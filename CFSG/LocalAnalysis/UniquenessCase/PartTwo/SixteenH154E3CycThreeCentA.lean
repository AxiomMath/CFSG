module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FixLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycThreeCentA_isPGroup_two_of_le {V U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hUV : U ≤ V) : IsPGroup 2 U := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using hV.2 g.1 (hUV g.2))⟩

private theorem s16h_e3_CycThreeCentA_wConj_le_v (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) : X ≤ V := by
  obtain ⟨m, hm, rfl⟩ := hX
  have hW : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hVm : conjSubgroup V m = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (h.hyp125.pairFacts.le_normalizer hm)
  exact (Subgroup.map_mono hW).trans (le_of_eq hVm)

private theorem s16h_e3_CycThreeCentA_orderOf_eq_three_of_mem_barSub
    {V₀ V E : Subgroup G} (hV : IsElemAbelian 2 V) (hEab : IsElemAbelian 3 E)
    {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ barSub V₀ V hV E) (hφ1 : φ ≠ 1) :
    orderOf φ = 3 := by
  have h3 : φ ^ 3 = 1 := (s16h_barSub_isElemAbelian hV hEab).2 φ hφ
  have hdvd : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hφ1
  · exact h

theorem s16h_e3_CycThreeCentA_three_dvd_cElt
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs3 : s15 D.M V₀ V hV L = 3)
    (hpσ : p ∉ D.sig) (h3 : D.sig = {3})
    (hn76 : ¬ (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6))
    (hct : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, 3 ∣ Nat.card ↥(F11.CElt D.M V₀ u) := by
  have h3mem : 3 ∈ D.sig := by rw [h3]; exact Set.mem_singleton 3
  have hp3 : CFSG.Open.pRank 3 D.M = 3 := s16h_pRank_eq_three D S hr3 h3mem
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEM, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) D.M
  have hE27 : Nat.card ↥E = 3 ^ 3 := by rw [hEcard, hp3]
  intro X hX Y hY hXY u hu
  obtain ⟨φ, hφE, hφ1, hfix⟩ :=
    s16h_e3_CycThreeCentAA_exists_bar_fix D S hr3 hσ hV h hc hp hLp hχ hs3 hpσ h3 hn76 hct
      hEM hEab hE27 X hX Y hY hXY u hu
  have hXV : X ≤ V := s16h_e3_CycThreeCentA_wConj_le_v D h.hyp151 hV hX
  have hYV : Y ≤ V := s16h_e3_CycThreeCentA_wConj_le_v D h.hyp151 hV hY
  have huV : u ∈ V := (sup_le hXV hYV) hu
  have hφ : φ ∈ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hEM hφE
  have hord : orderOf φ = 3 :=
    s16h_e3_CycThreeCentA_orderOf_eq_three_of_mem_barSub hV hEab hφE hφ1
  exact Sixteen21.dvd_card_cElt_of_mem_mbar hV hφ hord huV (hfix huV)

theorem s16h_e3_CycThreeCent_exists_three_fix
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs3 : s15 D.M V₀ V hV L = 3)
    (hpσ : p ∉ D.sig) (h3 : D.sig = {3})
    (hn76 : ¬ (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6))
    (hct : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, ∃ φ ∈ Mbar D.M V₀ V hV, orderOf φ = 3 ∧
        ∀ (huV : u ∈ V), φ (mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have h3mem : 3 ∈ D.sig := by rw [h3]; exact Set.mem_singleton 3
  have hp3 : CFSG.Open.pRank 3 D.M = 3 := s16h_pRank_eq_three D S hr3 h3mem
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) D.M
  have hE27 : Nat.card E = 3 ^ 3 := by rw [hEcard, hp3]
  obtain ⟨Eb, hEbM, -, hEbcard⟩ :=
    s16h_e3_bar_rank_ge D h.hyp151.hyp125 (q := 3) (k := 3) hct ⟨E, hEM, hE, hE27⟩
  have h3Eb : 3 ∣ Nat.card ↥Eb := by rw [hEbcard]; norm_num
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Eb) 3 h3Eb
  refine fun X hX Y hY hXY u hu => ?_
  have hXleV : X ≤ V := s16h_e3_CycThreeCentA_wConj_le_v D h.hyp151 hV hX
  have hYleV : Y ≤ V := s16h_e3_CycThreeCentA_wConj_le_v D h.hyp151 hV hY
  have huV : u ∈ V := (sup_le hXleV hYleV) hu
  by_cases hu0 : u ∈ V₀
  · refine ⟨(y₀ : MulAut (Vtil V₀ V hV)), hEbM y₀.2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, hy₀]
    · intro huV'
      have h1 : mkTil V₀ V hV (IntMod.mk hV ⟨u, huV'⟩) = 1 := by
        rw [← map_one (mkTil V₀ V hV)]
        exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2
          ((mem_modNull V₀ V hV _).2 hu0)
      rw [h1, map_one]
  · have hdvd := s16h_e3_CycThreeCentA_three_dvd_cElt D S hr3 hσ hV h hc hp hLp hχ hs3
      hpσ h3 hn76 hct X hX Y hY hXY u hu
    have hH : F11.Hyp11 D V₀ V := Hyp125.hyp11 S.h127 h.hyp151.hyp125
    have hV0p : IsPGroup 2 V₀ :=
      s16h_e3_CycThreeCentA_isPGroup_two_of_le h.hyp151.hyp125.pairFacts.elemAbelian₀ le_rfl
    have h4 : Nat.card V₀ ≤ 4 := by
      rw [card_eq_two_pow_mSub hV0p]
      have hsmall : mSub V₀ ≤ 2 := h.hyp16.small
      interval_cases mSub V₀ <;> norm_num
    obtain ⟨n, -, hn⟩ := r113_holds D V₀ V hH h4 u huV hu0
    have hcard : Nat.card ↥(F11.CElt D.M V₀ u) =
        (D.M ⊓ centralizer ({u} : Set G)).relIndex (F11.CElt D.M V₀ u) *
          Nat.card ↥((D.M ⊓ centralizer ({u} : Set G)) ⊓ F11.CElt D.M V₀ u) :=
      (Subgroup.relIndex_mul_card _ _).symm
    rw [hcard, hn] at hdvd
    have hcop : Nat.Coprime 3 (2 ^ n) :=
      Nat.prime_two.coprime_pow_of_not_dvd (by norm_num)
    have h3card : 3 ∣
        Nat.card ↥((D.M ⊓ centralizer ({u} : Set G)) ⊓ F11.CElt D.M V₀ u) :=
      hcop.dvd_of_dvd_mul_left hdvd
    have h3cent : 3 ∣ Nat.card ↥(D.M ⊓ centralizer ({u} : Set G)) :=
      h3card.trans (Subgroup.card_dvd_of_le inf_le_left)
    obtain ⟨y, hyord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(D.M ⊓ centralizer ({u} : Set G))) 3 h3cent
    set x : G := (y : G) with hx
    have hxM : x ∈ D.M := (Subgroup.mem_inf.mp y.2).1
    have hxC : x ∈ centralizer ({u} : Set G) := (Subgroup.mem_inf.mp y.2).2
    have hxord : orderOf x = 3 := by
      rw [hx, Subgroup.orderOf_coe, hyord]
    have hxu : x * u * x⁻¹ = u := by
      have hcomm : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hxs : x ∈ stabTil V₀ V := hMs hxM
    refine ⟨actTil V₀ V hV ⟨x, hxs⟩, actTil_mem_barSub V₀ V hV hxM hxs, ?_, ?_⟩
    · have hpow : actTil V₀ V hV ⟨x, hxs⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have hsub : (⟨x, hxs⟩ : ↥(stabTil V₀ V)) ^ 3 = 1 := by
          have hord : orderOf (⟨x, hxs⟩ : ↥(stabTil V₀ V)) = 3 := by
            rw [← Subgroup.orderOf_coe, hxord]
          simpa [hord] using pow_orderOf_eq_one (⟨x, hxs⟩ : ↥(stabTil V₀ V))
        rw [hsub, map_one]
      have hne : actTil V₀ V hV ⟨x, hxs⟩ ≠ 1 := by
        intro h1
        have hxCt : x ∈ F11.CTilde D.M V₀ V :=
          (mem_cTilde_iff hV h.hyp151.hyp125.pairFacts.le_normalizer).2 ⟨hxM, hxs, h1⟩
        exact hct (hxord ▸ Subgroup.orderOf_dvd_natCard _ hxCt)
      have hdvd3 : orderOf (actTil V₀ V hV ⟨x, hxs⟩) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one hpow
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hne
      · exact h
    · intro huV'
      have hstep : actStab V₀ V hV ⟨x, hxs⟩ (IntMod.mk hV ⟨u, huV'⟩) =
          IntMod.mk hV ⟨u, huV'⟩ := by
        apply IntMod.val_injective
        rw [actStab_apply_val]
        exact hxu
      rw [actTil_mk, hstep]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
