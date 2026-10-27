module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.GroupTheory.SylowCentralCoprimeQuotient
import CFSG.GroupTheory.WeirSylow.SigmaThree
import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.GroupTheory CFSG.Open Subgroup

theorem sp6SylowWreath_holds :
    Sp6SylowWreath := by
  intro Y _ _ f h P
  have hZ : ¬ 3 ∣ Nat.card (center Y) := Theorem82.not_three_dvd_card_center_of_isLie811 h
  obtain ⟨-, -, -, -, hm⟩ := h
  obtain ⟨K, _, _, _, -, hK3, ⟨e⟩⟩ :=
    Theorem82.ModelUnpack.exists_model_of_lieModel_psp (by decide) hm
  let := Fintype.ofFinite K
  have hK : ¬ 3 ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨Q⟩ : Nonempty (Sylow 3 (StatedSp 3 K)) := inferInstance
  let P₁ : Sylow 3 (Y ⧸ center Y) := P.mapSurjective (QuotientGroup.mk'_surjective _)
  let Q₁ : Sylow 3 (StatedProj (StatedSp 3 K)) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
  obtain ⟨φ₁⟩ := nonempty_mulEquiv_map_mk_of_isPGroup hZ P.isPGroup'
  obtain ⟨φ₂⟩ := nonempty_mulEquiv_map_mk_of_isPGroup
    (Theorem82.ModelUnpack.not_dvd_card_scalars_statedSp (by norm_num) Nat.prime_three
      (by norm_num)) Q.isPGroup'
  obtain ⟨φ₃⟩ := WeirSylow.nonempty_sylow_mulEquiv_sylow_of_mulEquiv e.symm P₁ Q₁
  obtain ⟨ψ⟩ := WeirSylow.sylow_Sp (by decide : Odd 3) K hK 3 Q
  obtain ⟨ω⟩ := WeirSylow.sigmaModelEquivWreath
    (a := padicValNat 3 (Fintype.card K ^ orderOf (Fintype.card K : ZMod 3) - 1))
    (WeirSylow.sp_three_div_orderOf_eq_three hK)
  exact ⟨_, WeirSylow.one_le_padicValNat_three_pow_orderOf_sub_one hK Fintype.one_lt_card,
    ⟨(((φ₁.trans φ₃).trans φ₂.symm).trans ψ).trans ω⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
