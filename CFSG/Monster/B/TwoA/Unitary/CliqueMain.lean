module

public import CFSG.Monster.B.TwoA.Unitary.CliqueLevi
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Monster.B.TwoA.Unitary.Clique

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
  CFSG.Monster.B.Classical.UnitarySix
open scoped LinearAlgebra.Projectivization MatrixGroups

theorem projAct_mk_inv (g : SU frobeniusF4 6) (p : IsoPt) :
    projAct ((g : ProjSU)⁻¹) p = g⁻¹ • p := by
  rw [← QuotientGroup.mk_inv, projAct_mk]

theorem kerL_smulSub (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    kerL (smulSub g X) = (kerL X).map (MulAut.conj (g : ProjSU)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro hx q hq
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, projAct_mk, projAct_mk_inv,
      hx _ ((smul_mem_planePts g X q).2 hq), inv_smul_smul]
  · intro hx p hp
    have hq : g⁻¹ • p ∈ planePts X := by
      rw [← smul_mem_planePts g, smul_inv_smul]
      exact hp
    have h := hx _ hq
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, projAct_mk, projAct_mk_inv,
      smul_inv_smul] at h
    calc projAct x p = g • (g⁻¹ • projAct x p) := (smul_inv_smul g _).symm
      _ = p := by rw [h, smul_inv_smul]

theorem natCard_kerL_smulSub (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    Nat.card (kerL (smulSub g X)) = Nat.card (kerL X) := by
  rw [kerL_smulSub]
  exact (Nat.card_congr ((kerL X).equivMapOfInjective _ (MulAut.conj _).injective).toEquiv).symm

theorem tPt_smul (g : SU frobeniusF4 6) (p : IsoPt) :
    tPt (g • p) = MulAut.conj (g : ProjSU) (tPt p) := by
  rw [← projAct_mk, tPt_projAct, MulAut.conj_apply]

theorem image_tPt_planePts_smulSub (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    tPt '' planePts (smulSub g X) =
      (MulAut.conj (g : ProjSU)).toMonoidHom '' (tPt '' planePts X) := by
  rw [planePts_smulSub, Set.image_image, Set.image_image]
  exact Set.image_congr fun p _ => tPt_smul g p

theorem IsMaxIso.kerL_eq_closure {W : Submodule F4 V} (hW : IsMaxIso W) :
    kerL W = Subgroup.closure (tPt '' planePts W) := by
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  rw [kerL_smulSub, kerL_W0_eq_closure, MonoidHom.map_closure, image_tPt_planePts_smulSub]

theorem IsMaxIso.natCard_kerL {W : Submodule F4 V} (hW : IsMaxIso W) :
    Nat.card (kerL W) = 2 ^ 9 := by
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  rw [natCard_kerL_smulSub, card_kerL_W0]

theorem IsMaxIso.kerL_comm {W : Submodule F4 V} (hW : IsMaxIso W) :
    ∀ x ∈ kerL W, ∀ y ∈ kerL W, x * y = y * x := by
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  rw [kerL_smulSub]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, kerL_W0_comm x hx y hy]

theorem IsMaxIso.kerL_sq {W : Submodule F4 V} (hW : IsMaxIso W) : ∀ x ∈ kerL W, x ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  rw [kerL_smulSub]
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pow, kerL_W0_sq x hx, map_one]

theorem IsMaxIso.isElementaryAbelian_kerL {W : Submodule F4 V} (hW : IsMaxIso W) :
    CFSG.IsElementaryAbelian 2 (kerL W) :=
  isElementaryAbelian_two_of _ hW.kerL_comm hW.kerL_sq

theorem exists_projAct_image_planePts {W W' : Submodule F4 V} (hW : IsMaxIso W)
    (hW' : IsMaxIso W') : ∃ x : ProjSU, projAct x '' planePts W = planePts W' := by
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  obtain ⟨g', rfl⟩ := hW'.exists_eq_smulSub
  refine ⟨((g' * g⁻¹ : SU frobeniusF4 6) : ProjSU), ?_⟩
  rw [Set.image_congr fun p _ => projAct_mk (g' * g⁻¹) p, ← planePts_smulSub, ← smulSub_mul,
    mul_assoc, inv_mul_cancel, mul_one]

theorem transvecMat_of_mem_W0 {v : V} (hv : v ∈ W0) :
    transvecMat v = unipMat (vecMulVec (hypA v) fun j => bar (hypA v j)) := by
  conv_lhs => rw [eq_lift3_of_mem_W0 hv]
  exact transvecMat_lift3 _

theorem mem_kerL_W0_iff' (x : ProjSU) :
    x ∈ kerL W0 ↔ ∃ C : Matrix (Fin 3) (Fin 3) F4, (C.map bar)ᵀ = C ∧
      ∃ g : SU frobeniusF4 6, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = unipMat C ∧
        (g : ProjSU) = x := by
  rw [mem_kerL_W0_iff]
  constructor
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, hC, unipSU C hC, rfl, rfl⟩
  · rintro ⟨C, hC, g, hg, rfl⟩
    exact ⟨C, hC, by congr 1; exact SU_ext hg⟩

theorem maximal_clique_unipotent_kernel_graph :
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
  ⟨fun _ hX => hX.finrank_le, maximal_isClique_iff, fun _ hW => hW.ncard_planePts,
    fun _ _ hW hW' => exists_projAct_image_planePts hW hW',
    fun _ hW => exists_levi_mulEquiv hW, natCard_PSL3, fun _ hW => natCard_range_restrL hW,
    fun W => ⟨kerL_le_stabL W, restrL_eq_one_iff W⟩,
    fun _ hW => ⟨hW.isElementaryAbelian_kerL, hW.natCard_kerL, hW.kerL_eq_closure⟩,
    rfl, isMaxIso_W0, fun _ => rfl, fun _ => rfl,
    fun C d => by rw [mulVec_u_hypEquiv, hyp_unipMat], mem_kerL_W0_iff',
    fun _ hv => ⟨fun _ => rfl, transvecMat_of_mem_W0 hv⟩⟩

end CFSG.Monster.B.TwoA.Unitary.Clique
