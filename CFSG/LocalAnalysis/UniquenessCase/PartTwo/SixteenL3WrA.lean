module

public import CFSG.Quasithin.Background.HL3WrA3
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod3A
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13

section Model

private theorem s16b_card_T0 : Nat.card T0 = 2 ^ 7 := by
  unfold T0
  rw [card_map_prod_sup_tau, card_U3]
  norm_num

private theorem s16b_relIndex_T0 : ¬ 2 ∣ (T0.subgroupOf norm).index := by
  have hXc : Nat.card norm = 2 ^ 7 * 441 := by rw [card_norm]; norm_num
  have h1 := Subgroup.relIndex_mul_card (H := T0) (K := norm)
  rw [inf_eq_left.mpr T0_le_norm, s16b_card_T0, hXc] at h1
  have h3 : T0.relIndex norm = 441 := by
    have hpos : 0 < 2 ^ 7 := by positivity
    nlinarith [h1]
  show ¬ 2 ∣ T0.relIndex norm
  rw [h3]
  decide

private theorem s16b_not_mem_aSet_three_norm (A : Subgroup (MulAut WMod)) :
    A ∉ E3.aSet 3 norm := by
  intro hA
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  have hAp : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  obtain ⟨m, -, hm⟩ := CFSG.Quasithin.H13.S127.Mod.exists_conj_le T0_le_norm
    (IsPGroup.of_card s16b_card_T0) s16b_relIndex_T0 hA.1 hAp
  have hle : A.map (MulAut.congr m).toMonoidHom ≤ T0 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hm a ha
  have h3 := CFSG.Quasithin.H13.S127.Mod.aSet_map_congr hA m hle
  rw [aSet_three_T0_eq_empty] at h3
  exact h3

private theorem s16b_aParam_le_two {X : Subgroup (MulAut WMod)} (hX : X ≤ norm) :
    E3.aParam X ≤ 2 := by
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  unfold E3.aParam
  split_ifs with hev
  · by_cases hne : {k : ℕ | 0 < k ∧ (E3.aSet k X).Nonempty}.Nonempty
    · refine csSup_le hne ?_
      rintro k ⟨-, A, hAk⟩
      by_contra hlt
      exact s16b_not_mem_aSet_three_norm A
        (E3.aSet_mono hX (E3.aSet_anti (by omega : 3 ≤ k) X hAk))
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, csSup_empty]
      exact Nat.zero_le _
  · exact Nat.zero_le _

private theorem s16b_two_le_aParam {X : Subgroup (MulAut WMod)} (hX : img ≤ X) :
    2 ≤ E3.aParam X := by
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  exact E3.le_aParam_of_mem_aSet (by norm_num)
    (A1_mem_aSet ((Subgroup.map_le_range _ _).trans hX))

end Model

section Finite

theorem L3Wreath_aParam_eq_two {V : Type*} [CommGroup V] {H M : Subgroup (MulAut V)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) : E3.aParam M = 2 := by
  obtain ⟨e, he⟩ := exists_model hreal
  have h1 : img ≤ M.map (congrHom e) := he ▸ Subgroup.map_mono hHM
  have h2 : M.map (congrHom e) ≤ L3Wr.norm := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut WMod)) :
          Set (MulAut WMod)) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    have h4 := (Subgroup.map_mono (f := congrHom e) hMN).trans (le_of_eq h3)
    have h5 := congrArg (fun K : Subgroup (MulAut WMod) => Subgroup.normalizer
      (K : Set (MulAut WMod))) he
    exact h4.trans (le_of_eq h5)
  rw [← aParam_map_congrHom e M]
  exact le_antisymm (s16b_aParam_le_two h2) (s16b_two_le_aParam h1)

variable {G : Type} [Group G] [Finite G]

end Finite

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
