module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.UC2TenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc2_17_37_uniqueMax (D : Data G) (h869 : F08.R869 D) (hSyl : UCK.U3Syl)
    {V₀ V L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n)
    (h17_36a : R17_36aAt D V₀ V) :
    UniqueMax D.M (L ⊔ D.T) := by
  have hnt : ¬ F08.Thin8 L := not_thin_of_isSU3 hSyl c.shape
  have hU0 : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uniqueMax_conjClosure_of_not_thin h869 c.mem_calC hnt
  rw [← h17_36a L n c] at hU0
  exact UC22.uc22p22u_uniqueMax_mono D le_sup_left
    (sup_le c.mem_calC.1.le D.sylowM.le) hU0

theorem seventeen_thirtyseven
    (D : Data G) {V₀ V : Subgroup G}
    (h17_35 : R17_35At D V₀ V) (h17_36a : R17_36aAt D V₀ V)
    (h17_36b : R17_36bAt D V₀ V) (h898 : F08.R898 D)
    (h109 : Inputs1719.UC2_10_9 D) (h869 : F08.R869 D) (hSyl : UCK.U3Syl) :
    R17_37At D V₀ V := by
  intro L n c
  by_contra hpow
  have hV0 : V₀ ≠ ⊥ :=
    uc2_17_35_v0_ne_bot_of_ne_two D c h17_35 fun h2 => hpow ⟨1, h2.trans (by norm_num)⟩
  have hLN : D.M ≤ Subgroup.normalizer (L : Set G) := uc2_17_36a_normal c h17_36a
  have hUL : UniqueMax D.M (L ⊔ D.T) := uc2_17_37_uniqueMax D h869 hSyl c h17_36a
  obtain ⟨s, hsodd, hs1, hsdvd⟩ := s13_exists_odd_divisor hpow
  obtain ⟨r, hr, hrdvd⟩ := s13_exists_prime_dvd hs1
  have hrdvdn : r ∣ 2 ^ n - 1 :=
    hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hsdvd)
  have hTL : D.T ≤ Subgroup.normalizer (L : Set G) := D.sylowM.le.trans hLN
  have hT2 : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1
  have hTsylM : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hSylLT : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ D.T) L := by
    rw [inf_comm]
    exact CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hTsylM c.mem_calC.1.le hLN
  obtain ⟨X, hXL, hXcard, hXT⟩ :=
    Inputs1719.exists_prime_order_le_normalizer_of_isSU3_bar2 hTL hT2 hSylLT c.shape
      hsodd hsdvd hr hrdvd
  have hXN : Subgroup.normalizer (X : Set G) ≤ D.M :=
    h17_36b L n c r hr hrdvdn X hXcard hXL
  have hXU : X ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    h898 L c.mem_calC n c.shape s hsodd hsdvd r hr hrdvd X hXL hXcard hXN
  exact hV0
    (v0_eq_bot_of_uc2_10_9_of_normal h109 c.hyp125 c.mem_calC hLN hUL hsodd hr hrdvd hXL hXT
      hXcard (inU_iff_mem_uniqueSet.mpr hXU))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
