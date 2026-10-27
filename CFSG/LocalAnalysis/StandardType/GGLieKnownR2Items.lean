module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Transport

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open
open scoped commutatorElement

variable {U X : Type} [Group U] [Group X] [Finite X] {ψ : U →* X}

theorem pCoreOf_range_inf_normalizer_sup_eq_range (hker : ψ.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card ψ.ker)) {Rr Q J : Subgroup U} (hRr : IsPGroup 2 Rr) (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (Rr : Set U))
    (hNQ : Subgroup.normalizer (Rr : Set U) ≤ Subgroup.normalizer (Q : Set U))
    (hgen : Q ⊔ J = ⊤) :
    pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)) ⊔ J.map ψ =
      ψ.range := by
  rw [← map_normalizer_eq_range_inf_normalizer_map hker hodd hRr]
  apply le_antisymm
  · exact sup_le ((GGRootNorm.pCoreOf_le _).trans (Subgroup.map_le_range _ _))
      (Subgroup.map_le_range _ _)
  · rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup]
    refine sup_le_sup_right ?_ _
    refine GGRootNorm.le_pCoreOf_of_normalized (Subgroup.map_mono hQN) (hQ.map ψ) ?_
    rintro _ ⟨m, hm, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨m * q * m⁻¹, (Subgroup.mem_normalizer_iff.1 (hNQ hm) q).1 hq, by simp⟩

theorem item_four_of_pCore_le (hker : ψ.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card ψ.ker))
    {Rr Q : Subgroup U} (hRr : IsPGroup 2 Rr)
    (hC2 : pCoreOf 2 (Subgroup.normalizer (Rr : Set U)) ≤ Q) (hcomm : ⁅Q, Q⁆ ≤ Rr)
    (hcent : Q ≤ Subgroup.centralizer (Rr : Set U)) :
    ⁅pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)),
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X))⁆ ≤
        Rr.map ψ ∧
      pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)) ≤
        Subgroup.centralizer ((Rr.map ψ : Subgroup X) : Set X) := by
  have hkerN : ψ.ker ≤ Subgroup.normalizer (Rr : Set U) :=
    hker.trans (Subgroup.center_le_normalizer (Rr : Set U))
  rw [← map_normalizer_eq_range_inf_normalizer_map hker hodd hRr,
    ← map_pCoreOf_eq_of_odd_central_ker hker hodd hkerN]
  have hle : (pCoreOf 2 (Subgroup.normalizer (Rr : Set U))).map ψ ≤ Q.map ψ :=
    Subgroup.map_mono hC2
  refine ⟨?_, hle.trans ?_⟩
  · exact (Subgroup.commutator_le_map_commutator hle hle).trans (Subgroup.map_mono hcomm)
  · rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hcent hq) r hr]

end CFSG.StandardType.LieKnownR2
