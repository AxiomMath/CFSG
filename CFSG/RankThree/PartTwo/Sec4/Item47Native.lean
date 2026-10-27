module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.SmallOddCore.McLAut
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem card_outer_J2 : Nat.card (Outer NativeSporadic.J2) ≤ 2 := by
  obtain ⟨-, -, -, -, -, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_outer_J3 : Nat.card (Outer NativeSporadic.J3) ≤ 2 :=
  CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.j3_outer_card_le
    CFSG.Sporadic.Schreier.j3PermEquiv

theorem card_outer_McL : Nat.card (Outer NativeSporadic.McL) ≤ 2 :=
  CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.mcl_outer_card_le
    CFSG.Sporadic.Schreier.mclPermEquiv

theorem card_outer_HS : Nat.card (Outer NativeSporadic.HS) ≤ 2 :=
  CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
    CFSG.Sporadic.Schreier.hsPermEquiv

theorem card_outer_Ru : Nat.card (Outer NativeSporadic.Ru) ≤ 2 :=
  CFSG.Sporadic.Schreier.outer_card_le_of_equiv
    (by rw [CFSG.Sporadic.RuSchreier.card_outer_ruP]; norm_num)
    CFSG.Sporadic.RuSchreier.ruEquivP

theorem card_outer_carrier_le_two {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M23 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨ s = .McL ∨ s = .HS ∨
      s = .He ∨ s = .Ru) :
    Nat.card (Outer (NativeSporadic.Carrier s)) ≤ 2 := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CFSG.Sporadic.Schreier.at_m11_schreier.1
  · exact CFSG.ComponentClassification.M12Cover.card_outer.le
  · exact CFSG.Sporadic.Schreier.at_m23_schreier.1
  · exact CFSG.Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num)
  · exact card_outer_J2
  · exact card_outer_J3
  · exact card_outer_McL
  · exact card_outer_HS
  · exact CFSG.Sporadic.Schreier.AT_He_Schreier.1
  · exact card_outer_Ru

theorem card_mulAut_carrier_le_two_mul {s : TauCeti.SporadicName} (hs : s = .M22 ∨ s = .M24) :
    Nat.card (MulAut (NativeSporadic.Carrier s)) ≤ 2 * Nat.card (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl
  · exact CFSG.Sporadic.Schreier.m22_mulAut_card
  · exact CFSG.Sporadic.Schreier.m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))

theorem center_carrier_M22_M24 {s : TauCeti.SporadicName} (hs : s = .M22 ∨ s = .M24) :
    Subgroup.center (NativeSporadic.Carrier s) = ⊥ := by
  rcases hs with rfl | rfl
  · exact CFSG.Sporadic.Schreier.m22_center_eq_bot'
  · exact CFSG.Sporadic.Schreier.m24_center_eq_bot'

theorem center_eq_bot_of_isSimpleGroup_of_not_prime {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hY : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Y :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hY (Group.is_simple_iff_prime_card.mp inferInstance)

theorem center_carrier_eq_bot_of_cover {s : TauCeti.SporadicName} (hs : s ∈ sporadicCovers46) :
    Subgroup.center (NativeSporadic.Carrier s) = ⊥ := by
  simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact CFSG.Sporadic.Schreier.m22_center_eq_bot'
  · have := CFSG.Sporadic.J3.fam_j3_simplicity.2.2
    change Subgroup.center NativeSporadic.J3 = ⊥
    exact center_eq_bot_of_isSimpleGroup_of_not_prime
      (by rw [CFSG.Sporadic.J3.card_J3]; norm_num)
  · have := CFSG.Sporadic.McL.fam_mcl_simplicity.2.2
    change Subgroup.center NativeSporadic.McL = ⊥
    exact center_eq_bot_of_isSimpleGroup_of_not_prime
      (by rw [CFSG.Sporadic.McL.card_McL]; norm_num)
  · have := CFSG.Sporadic.ON.fam_on_simplicity.2.2
    change Subgroup.center NativeSporadic.ON = ⊥
    exact center_eq_bot_of_isSimpleGroup_of_not_prime
      (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)

theorem card_outer_tits (X : Type) [Group X] (f : ℕ) (h : ReeTitsModel X .Tits 2 f) :
    Nat.card (Outer X) = 2 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 f h
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact CFSG.Sporadic.Schreier.Tits.card_outer_titsD

end CFSG.RankThree.PartTwo.Sec4
