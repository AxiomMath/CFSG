module

public import CFSG.Monster.B.TwoA.Unitary.CliqueMain
public import CFSG.LieType.Chevalley.C2E6FirstResidueForm
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.TwoA.Unitary.Clique

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
  CFSG.Monster.B.Classical.UnitarySix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Chevalley.C2E6Std (herm6 SU6 mem_SU6_iff_herm6)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open scoped LinearAlgebra.Projectivization MatrixGroups

theorem herm6_eq_herm (v w : Fin 6 → K) : herm6 v w = herm v w := rfl

@[expose] def su6Mat (h : SU6) : Matrix (Fin 6) (Fin 6) F4 :=
  ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)

theorem det_su6Mat (h : SU6) : (su6Mat h).det = 1 := h.1.2

theorem isIsometry_su6Mat (h : SU6) : IsIsometry (su6Mat h) :=
  fun x y => (mem_SU6_iff_herm6 _).1 h.2 x y

@[expose] noncomputable def toSU6 (g : SU frobeniusF4 6) : SU6 :=
  ⟨⟨((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4), det_of_mem g⟩,
    (mem_SU6_iff_herm6 _).2 fun v w => isIsometry_of_mem g v w⟩

@[expose] noncomputable def su6Equiv : SU6 ≃* SU frobeniusF4 6 where
  toFun h := mkSU (su6Mat h) (det_su6Mat h) (isIsometry_su6Mat h)
  invFun := toSU6
  left_inv _ := rfl
  right_inv _ := SU_ext rfl
  map_mul' _ _ := SU_ext rfl

theorem coe_su6Equiv (h : SU6) :
    (((su6Equiv h : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      su6Mat h := rfl

theorem pow_six_F4 : ∀ b : F4, b ≠ 0 → b ^ 6 = 1 := by decide

theorem map_su6Equiv_scalars :
    ((LinearFlag.scalars 6 K).subgroupOf SU6).map su6Equiv.toMonoidHom = scalars := by
  ext g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, LinearFlag.mem_scalars, mem_scalars]
  constructor
  · rintro ⟨c, -, hc⟩
    exact ⟨(c : K), hc⟩
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := det_of_mem g
      rw [ha, map_zero, Matrix.det_zero] at this
      exact zero_ne_one this
    let c : Kˣ := Units.mk0 (show K from a) ha0
    exact ⟨c, Units.ext (pow_six_F4 a ha0), ha⟩

theorem c2e6_projSU_equiv :
    (∀ v w : Fin 6 → K, herm6 v w = herm v w) ∧
    ∃ θ : SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6 ≃* ProjSU,
      ∀ (h : SU6) (g : SU frobeniusF4 6),
        ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = su6Mat h →
        θ (h : SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6) = (g : ProjSU) := by
  refine ⟨herm6_eq_herm, QuotientGroup.congr _ _ su6Equiv map_su6Equiv_scalars,
    fun h g hg => ?_⟩
  change ((su6Equiv h : SU frobeniusF4 6) : ProjSU) = _
  congr 1
  exact SU_ext hg.symm

theorem unitary_six_maximal_clique_unipotent_kernel :
    ((∀ v w : Fin 6 → K, herm6 v w = herm v w) ∧
      ∃ θ : SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6 ≃* ProjSU,
        ∀ (h : SU6) (g : SU frobeniusF4 6),
          ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = su6Mat h →
          θ (h : SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6) = (g : ProjSU)) ∧
    (∀ X : Submodule F4 V, IsTotIso X → Module.finrank F4 X ≤ 3) ∧
    (∀ S : Set IsoPt, Maximal isoGraph.IsClique S ↔
      ∃ W : Submodule F4 V, IsMaxIso W ∧ S = planePts W) ∧
    (∀ W : Submodule F4 V, IsMaxIso W → (planePts W).ncard = 21) ∧
    (∀ W W' : Submodule F4 V, IsMaxIso W → IsMaxIso W' →
      ∃ x : ProjSU, projAct x '' planePts W = planePts W') ∧
    (∀ W : Submodule F4 V, IsMaxIso W →
      ∃ (e : planePts W ≃ ℙ F4 (Fin 3 → F4)) (θ : (restrL W).range ≃* PSL(3, F4)),
        ∀ (σ : (restrL W).range) (p : planePts W),
          e ((σ : Equiv.Perm (planePts W)) p) = θ σ • e p) ∧
    Nat.card PSL(3, F4) = 20160 ∧
    (∀ W : Submodule F4 V, IsMaxIso W → Nat.card (restrL W).range = 20160) ∧
    (∀ W : Submodule F4 V, kerL W ≤ stabL W ∧
      ∀ x : stabL W, restrL W x = 1 ↔ (x : ProjSU) ∈ kerL W) ∧
    (∀ W : Submodule F4 V, IsMaxIso W →
      CFSG.IsElementaryAbelian 2 (kerL W) ∧ Nat.card (kerL W) = 2 ^ 9 ∧
        kerL W = Subgroup.closure (tPt '' planePts W)) ∧
    W0 = Submodule.span F4 (Set.range ![u 0, u 1, u 2]) ∧ IsMaxIso W0 ∧
    (∀ i : Fin 3, (hypEquiv (Sum.inl i) : ℕ) = i) ∧
    (∀ j : Fin 3, (hypEquiv (Sum.inr j) : ℕ) = 5 - j) ∧
    (∀ (C : Matrix (Fin 3) (Fin 3) F4) (d : Fin 3 ⊕ Fin 3),
      unipMat C *ᵥ u (hypEquiv d) = ∑ c, fromBlocks 1 C 0 1 c d • u (hypEquiv c)) ∧
    (∀ x : ProjSU, x ∈ kerL W0 ↔ ∃ C : Matrix (Fin 3) (Fin 3) F4, (C.map bar)ᵀ = C ∧
      ∃ g : SU frobeniusF4 6, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = unipMat C ∧
        (g : ProjSU) = x) ∧
    (∀ v ∈ W0, (∀ i : Fin 3, hypA v i = v (Fin.castLE (by norm_num) i)) ∧
      transvecMat v = unipMat (vecMulVec (hypA v) fun j => bar (hypA v j))) :=
  ⟨c2e6_projSU_equiv, maximal_clique_unipotent_kernel_graph⟩

end CFSG.Monster.B.TwoA.Unitary.Clique
