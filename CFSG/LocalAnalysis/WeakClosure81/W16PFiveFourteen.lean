module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveThirteen
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteenD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

section Certified


theorem Hyp167.false_of_le_pCoreOf (hI : NamedInputs15 G) (hS : Std15 G) (h152 : Thm152 G)
    (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H) : False := by
  have hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T ≠ ⊥ :=
    Hyp167.inf_conj_eSub_ne_bot hI hS h152 h1 hX hVO
  have hIA : conjClosure V X ≤ conjSubgroup M g :=
    Hyp167.I_le_conjSubgroup_M h1 hS hX hVO hBE
  by_cases hle : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) ≤
      E3.mQuot V (U ⊔ V₀)
  · exact Hyp167.false_of_mQuot_A_le h1 hS h152 hX hVO hIA hle
  · have hn : 1 ≤ E3.mQuot V (U ⊔ V₀) := Cex16.one_le_n h152 hX.cex
    have hmA : E3.mQuot V (U ⊔ V₀) <
        E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) := not_le.1 hle
    have h2mA : 2 ≤ E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) := by omega
    have hAab : IsElemAbelian 2 (conjSubgroup V g) :=
      E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
    have hD2 : 2 < ((conjSubgroup V g) ⊓ kerMOf M X).relIndex (conjSubgroup V g) := by
      have hpow := E3.relIndex_eq_two_pow hAab.isPGroup
        ((conjSubgroup V g) ⊓ kerMOf M X)
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) :=
            Nat.pow_le_pow_right (by norm_num) h2mA
        _ = ((conjSubgroup V g) ⊓ kerMOf M X).relIndex (conjSubgroup V g) := hpow.symm
    have hA_le_X : conjSubgroup V g ≤ X :=
      hX.A_le_T.trans (hX.sylow.le.trans inf_le_left)
    have hXM : ¬ X ≤ M := hX.mem.2.2.not_le_M
    obtain ⟨Y, hYX, hYmin⟩ := exists_isMinimalNotLE (B := M) hA_le_X hXM
    obtain ⟨-, k, hmA_le_k, h12⟩ :=
      Hyp167.setting12Two_of_min hI.thmB hS hX hAab le_rfl hD2 hYmin hYX
    have hquad := Hyp167.quad_of_le_conjSubgroup_M hX hIA
    have hk : k ≤ E3.mQuot V (U ⊔ V₀) :=
      Hyp167.le_n_of_quad hI.mult hS h152 h1 hX hVO hAab le_rfl hYmin.1 hYX hYmin.2.1 h12 hquad
    omega

theorem IsMinFam16.not_le_pCoreOf (hI : NamedInputs15 G) (hS : Std15 G) (h152 : Thm152 G)
    (h1 : W16One G) (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) : ¬ V ≤ pCoreOf 2 H := by
  intro hVO
  obtain ⟨g, X, T, hX⟩ := IsMinFam16.exists_hyp167 h1 hS h hH
  exact Hyp167.false_of_le_pCoreOf hI hS h152 h1 hX hVO

theorem w16Fourteen_of_named_inputs (hI : NamedInputs15 G) :
    Std15 G → Thm152 G → W16One G → ∀ ⦃M V₀ V U S H : Subgroup G⦄, Cex16 M V₀ V U S →
      IsMinFam16 M U S H → ¬ V ≤ pCoreOf 2 H :=
  fun hS h152 h1 _ _ _ _ _ _ h hH => IsMinFam16.not_le_pCoreOf hI hS h152 h1 h hH

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
