module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneCardinality
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLSixSevenComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneSection15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLSixSevenFixers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoCommon
public import CFSG.Quasithin.Vol2.Ch10SecQ9H46
public import CFSG.RankThree.PartOne.S11b.Sec109SixFiveArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s168e3_ln_fix_order_seven_of_natural
    {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hN : BinaryNaturalSL H (⊤ : Subgroup W) ⊥ n 1) :
    ∀ x : W, x ≠ 1 → ∃ b ∈ H, orderOf b = 7 ∧ b x = x := by
  classical
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hN
  have hπinj : Function.Injective π :=
    hπ.injective_of_faithful (FFModel.nat_faithful _)
  obtain ⟨f, -, hfk, hfe⟩ := FFC.exists_natMap hπ
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hfk u).mp hu))
  intro x _
  obtain ⟨B, hBord, hBx, -⟩ := s168e3_ln_fix_seven_two hn
    (Multiplicative.toAdd (f ⟨x, trivial⟩)) 0
  let γ : ↥(StatedSL n (ZMod 2)) := ⟨B, FFC.mem_statedSL_zmod B⟩
  have hγord : orderOf γ = 7 := by
    calc orderOf γ = orderOf B := (Subgroup.orderOf_coe γ).symm
         _ = 7 := hBord
  have hModel : natAct (StatedSL n (ZMod 2)) γ (f ⟨x, trivial⟩) =
      f ⟨x, trivial⟩ := by
    simpa only [natAct, γ, ofAdd_toAdd] using congrArg Multiplicative.ofAdd hBx
  have hfix : ((π γ : ↥H) : MulAut W) x = x := by
    have hf := (hfe γ ⟨x, trivial⟩ trivial).trans hModel
    exact congrArg Subtype.val (hfinj hf)
  refine ⟨((π γ : ↥H) : MulAut W), (π γ).2, ?_, hfix⟩
  rw [Subgroup.orderOf_coe, orderOf_injective π hπinj γ]
  exact hγord

theorem s168e3_concl163F_of_naturalSL_six_seven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) n 1) :
    Concl163F D V₀ V hV L := by
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn7 : n ≤ 7 := by rcases hn with rfl | rfl <;> norm_num
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_sl_six_seven_component_at_three c hcomp hn hSL
  have hLn : IsLn ↥(lBar V₀ V hV L) n 1 := s16k_isLn_of_isSLn hn3 hSL
  obtain ⟨-, θ, -, hmap, -⟩ :=
    s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := hN
  have hR' := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
    (I := wTil V₀ V hV L) le_rfl hR
  rw [hmap] at hR'
  have hNstar : BinaryNaturalSL (lStar D.M V₀ V hV L)
      (wStar D.M V₀ V hV L) ⊥ n 1 :=
    ⟨K, hKf, hKfin, hKcard, hR'⟩
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inl ⟨n, hn3, hLn, hNstar⟩
  have hEmbedCard : Nat.card ↥(Mbar D.M V₀ V hV) ∣
      Nat.card (MulAut ↥(lBar V₀ V hV L)) :=
    s168e3_card_mbar_dvd_card_mulAut_of_natural c hs hperf
  have hClass : StatedClassicalModel ↥(lBar V₀ V hV L) .PSL n 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hLn (by decide)
  have hOrd := CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
    ↥(lBar V₀ V hV L) n 2 1 hClass
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(lBar V₀ V hV L)) ∣ 2 := by
    have h := hOrd.2.2.2.2 hn3
    simpa using h
  have hAut : Nat.card (MulAut ↥(lBar V₀ V hV L)) ∣
      2 * Nat.card ↥(lBar V₀ V hV L) :=
    CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F.card_mulAut_dvd_of_outer hOut
  have hAcard : Nat.card ↥(Mbar D.M V₀ V hV) ∣
      2 * Nat.card ↥(lBar V₀ V hV L) :=
    hEmbedCard.trans hAut
  have hOrder : Nat.card ↥(lBar V₀ V hV L) =
      2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
    have h := hOrd.1
    simpa using h
  have hBcard : Nat.card ↥(lBar V₀ V hV L) = 20158709760 ∨
      Nat.card ↥(lBar V₀ V hV L) = 163849992929280 := by
    rcases hn with h6 | h7
    · left
      have hc6 : StatedClassicalModel ↥(lBar V₀ V hV L) .PSL 6 2 1 := h6 ▸ hClass
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hc6]
      decide
    · right
      have hc7 : StatedClassicalModel ↥(lBar V₀ V hV L) .PSL 7 2 1 := h7 ▸ hClass
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hc7]
      decide
  have hsig : D.sig ⊆ ({3, 7} : Set ℕ) := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    have hpA : p ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      have h := s168e3_two_pow_dvd_card c hp
      rwa [c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV] at h
    have hcop : Nat.Coprime (p ^ 2) 2 :=
      Nat.Coprime.pow_left 2 ((Nat.coprime_primes hpp Nat.prime_two).2 hp2)
    have hpB : p ^ 2 ∣ Nat.card ↥(lBar V₀ V hV L) :=
      hcop.dvd_of_dvd_mul_left (hpA.trans hAcard)
    by_cases hp3 : p = 3
    · rw [hp3]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · have hp5 : 5 ≤ p := by
        by_contra h
        have hp2le : 2 ≤ p := hpp.two_le
        have hle : p ≤ 4 := by omega
        have hp4 : p = 2 ∨ p = 3 ∨ p = 4 := by omega
        rcases hp4 with rfl | rfl | rfl
        · exact hp2 rfl
        · exact hp3 rfl
        · norm_num at hpp
      rw [hOrder] at hpB
      have hp7 := (CFSG.RankThree.PartOne.Sec109.eq_seven_of_sq_dvd hn3 hn7 hpp hp5 hpB).1
      rw [hp7]
      exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hcube : ¬ 7 ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    intro h
    have h' : 7 ^ 3 ∣ 2 * Nat.card ↥(lBar V₀ V hV L) := h.trans hAcard
    rcases hBcard with hc | hc <;> rw [hc] at h' <;> norm_num at h'
  have hdiv7 : 7 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rcases hBcard with hc | hc <;> rw [hc] <;> norm_num
  have htop : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have hNtop : BinaryNaturalSL (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ n 1 := by
    simpa only [htop] using hNstar
  have hfixStar : ∀ x : vStar D.M V₀ V hV L, x ≠ 1 →
      ∃ b ∈ lStar D.M V₀ V hV L, orderOf b = 7 ∧ b x = x :=
    s168e3_ln_fix_order_seven_of_natural hn hNtop
  have hfixTil : ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ b ∈ Mbar D.M V₀ V hV, orderOf b = 7 ∧ b x = x :=
    s168e3_pointFix_of_star c hs Nat.prime_seven (by norm_num) hdiv7 hfixStar
  have hKernel : S168e3Kernel (Mbar D.M V₀ V hV) 7 :=
    s168e3_kernel_of_cube Nat.prime_seven (Mbar D.M V₀ V hV) hcube hfixTil
  have h7not : 7 ∉ D.sig := fun h7 =>
    s168e3_false_of_kernel c Nat.prime_seven h7 hKernel
  obtain ⟨p, hp⟩ := c.std.hx.sig_nonempty
  have h3 : 3 ∈ D.sig := by
    rcases hsig hp with hp3 | hp7
    · exact hp3 ▸ hp
    · exact absurd (hp7 ▸ hp) h7not
  have hnot : ¬ s15ExcList ↥(lBar V₀ V hV L) := by
    intro hexc
    have hle := s15ExcList_card_le hexc
    rcases hBcard with hc | hc <;> rw [hc] at hle <;> omega
  exact s168e3_concl163F_of_natural_perfect c hcomp hs hperf hnot h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
