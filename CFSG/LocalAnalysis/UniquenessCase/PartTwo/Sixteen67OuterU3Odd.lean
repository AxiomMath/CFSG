module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67OuterSO3Order
public import CFSG.GH74.KGroups.L3EpsUniGraph
public import CFSG.GH74.Generic.Context
import CFSG.GH74.KGroups.L3EpsUniInv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Blueprint (LieModel)
open CFSG.GH74.KGroups.L3Eps.Uni CFSG.LocalAnalysis.ComponentInitial

theorem orderOf_le_of_outer_involution_psu_odd {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hp2 : p ≠ 2) (hq : p ^ f % 3 = 1) (hU : LieModel J .PSU 3 p f) {α : MulAut J}
    (hα : α ^ 2 = 1) (hαout : α ∉ (MulAut.conj : J →* MulAut J).range) {y : J} (hy : α y = y) :
    orderOf y ≤ p ^ f + 1 := by
  obtain ⟨hp, hf, F, _, _, hFcard, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hU
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (p ^ f) := hpodd.pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := hp.odd_iff.1 hpodd
    have h3 : 3 ≤ p ^ f := by
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨θ, hθ⟩ := exists_cover_of_equiv h e₀
  have hσ : α * α = 1 := by rw [← pow_two, hα]
  rcases involution_type h hp2 h5 hθ hσ with ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · obtain ⟨z, hz⟩ := exists_conj_of_typeI h hθ hAu hAA hrel
    exact (hαout ⟨z, hz⟩).elim
  · have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hodd
    obtain ⟨D⟩ := exists_realData h h2 hAu hAA
    haveI : Finite h.fixedField := Subtype.finite
    have hk2 : (2 : h.fixedField) ≠ 0 :=
      CFSG.GH74.Generic.S45.Uni.two_ne_zero_fixedField h h2
    have hk : ringChar h.fixedField ≠ 2 := ringChar_ne_two_of_two_ne_zero hk2
    obtain ⟨g, hgθ, hg⟩ := exists_fixed_rep h hθ hφ hrel hy
    obtain ⟨X, hX⟩ := D.exists_Phi_of_fixed hφ hg
    have hρX : (θ.comp D.Phi) X = y := by
      show θ (D.Phi X) = y
      rw [hX, hgθ]
    have hXiso : (X : GL (Fin 3) h.fixedField) ∈ D.Iso := (Subgroup.mem_inf.1 X.2).1
    have hXisom : (X : GL (Fin 3) h.fixedField) ∈
        CFSG.ComponentClassification.CatalogueBGraphForm.isometryGroup 3 h.fixedField D.G := by
      simpa only [RealData.Iso] using hXiso
    have hXdetker : (X : GL (Fin 3) h.fixedField) ∈
        (Matrix.GeneralLinearGroup.det :
          GL (Fin 3) h.fixedField →* h.fixedFieldˣ).ker := (Subgroup.mem_inf.1 X.2).2
    have hXdet : ((X : GL (Fin 3) h.fixedField) :
        Matrix (Fin 3) (Fin 3) h.fixedField).det = 1 := by
      have h1 := MonoidHom.mem_ker.1 hXdetker
      have h2' := congrArg (fun u : h.fixedFieldˣ => (u : h.fixedField)) h1
      simpa using h2'
    have hbound := orderOf_le_card_add_one_of_isometry_three hk D.hGs hXisom hXdet
    calc orderOf y = orderOf ((θ.comp D.Phi) X) := by rw [hρX]
      _ = orderOf (X : ↥D.Iso1) := orderOf_injective (θ.comp D.Phi) (D.injective_theta_Phi hθ) X
      _ = orderOf (X : GL (Fin 3) h.fixedField) := (Subgroup.orderOf_coe X).symm
      _ ≤ Nat.card h.fixedField + 1 := hbound
      _ = p ^ f + 1 := by rw [h.card_fixedField]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
