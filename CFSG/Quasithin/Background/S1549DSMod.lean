module

public import CFSG.Quasithin.Background.FFC6B
public import CFSG.Quasithin.Background.FFC6H
public import CFSG.Quasithin.Background.FFC2Ident
public import CFSG.Quasithin.Background.InternalSecB5
public import CFSG.Quasithin.Background.C1PackS15348
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.QuasithinUnique CFSG.Quasithin.B5 CFSG.Open CFSG.LieType.BorelTits

theorem sl3_card_ne {q N : ℕ} (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≠ N := by
  intro h
  have hq : q ≤ 4 := by
    by_contra hq
    push Not at hq
    have h1 : 5 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 5 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 5 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    rcases hN with rfl | rfl | rfl <;> norm_num at h4
  interval_cases q <;> rcases hN with rfl | rfl | rfl <;> norm_num at h

theorem sp4_card_ne' {q N : ℕ} (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) :
    q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) ≠ N := by
  intro h
  have hq : q ≤ 2 := by
    by_contra hq
    push Not at hq
    have h1 : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have h2 : 3 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 3 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    rcases hN with rfl | rfl | rfl <;> norm_num at h4
  interval_cases q <;> rcases hN with rfl | rfl | rfl <;> norm_num at h

section Excl

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V} {N : ℕ}

theorem not_sl3_list (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) (hc : Nat.card ↥L = N) {n : ℕ}
    (h : BinaryNaturalSL L U Z 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc, card_statedSL_three1527d] at h1
  exact sl3_card_ne hN h1.symm

theorem not_sp4_list (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) (hc : Nat.card ↥L = N) {n : ℕ}
    (h : BinaryNaturalSp4 L U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp] at h1
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h1
  exact sp4_card_ne' hN (q := Nat.card F) (by simpa using h1.symm)

theorem not_sl_two_list (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) (hc : Nat.card ↥L = N) {d : ℕ}
    (hd : d = 4 ∨ d = 5) {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)) →* ↥L}
    (hπ : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2))).RealizesVia L U Z π) : False := by
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc] at h1
  rcases hd with rfl | rfl
  · rw [card_statedSL_four_zmod1527d] at h1
    omega
  · rw [card_statedSL_five_zmod1527d] at h1
    omega

theorem not_extSq_list (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) (hc : Nat.card ↥L = N) {d : ℕ}
    (hd : d = 4 ∨ d = 5) (h : SLExteriorTwo L U Z d) : False := by
  obtain ⟨π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)) :=
    (Nat.card_congr (FFC.equivOfRealizes (FFC.extSq_faithful (by omega)) hπ).toEquiv).symm
  rw [hc] at hcard
  rcases hd with rfl | rfl
  · rw [card_statedSL_four_zmod1527d] at hcard
    omega
  · rw [card_statedSL_five_zmod1527d] at hcard
    omega

end Excl

section B51

variable {V : Type} [CommGroup V] [Finite V]

theorem list_irrPlus (hB51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hB : B51Hyp G L) {N : ℕ} (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) (hc : Nat.card ↥L = N) :
    commV L ∈ IrrPlus L ⊤ := by
  obtain ⟨hp1, -⟩ := hB51 V hV G L hB
  rcases hp1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  · exact hi.1
  · exfalso
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, hreal, -, -⟩ := hii
    have h1 := card_eq_of_nat_realizes1527d (hreal 0)
    rw [hc, card_statedSL_three1527d] at h1
    exact sl3_card_ne hN h1.symm
  · exfalso
    obtain ⟨hn, π, U₁, U₂, -, hreal, -⟩ := hiii.2
    exact not_sl_two_list hN hc hn hreal
  · exfalso
    obtain ⟨-, n, hn, k, hk, -, hdir⟩ := hiv
    obtain ⟨I, π, -, -, -, hreal⟩ := hdir
    exact not_sl_two_list hN hc hn (hreal ⟨0, hk⟩)

end B51

section Sec

variable {V : Type} [CommGroup V] [Finite V]

theorem section_q_one (hB42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1) {X K T Ab : Subgroup (MulAut V)}
    (h : B51Hyp X K) (hU : commV K ∈ IrrPlus K ⊤) (hT : IsSylowTwoOf T X)
    (hAb : IsFFStarOffender X Ab) (hAbT : Ab ≤ T) {C : Subgroup V} (hC : C = fixV K ⊓ commV K)
    {N : ℕ} (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) (hc : Nat.card ↥K = N) :
    (1 : WithTop ℚ) ≤ qOf (autSec (K ⊔ T) (commV K) C) := by
  obtain ⟨B, hBA, hB, hconcl⟩ := FFC.B59.b42_offender hB42 hV h hU hT hAb hAbT hC
  have hb4 := b4Hyp_section' hV h hU hT.1 hT.2.1 hC
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV h hU hT hC
  have hLG := le_G h
  have hLU : K ≤ stabSub (commV K) := hLG.trans hGU
  have hLC : K ≤ stabSub C := hLG.trans hGC
  have hcL' : Nat.card ↥(autSec K (commV K) C) = N := by
    rw [← hc]
    exact (Nat.card_congr (secEquiv K hLU hLC hfL).toEquiv).symm
  have hq1 : ∀ {G' : Subgroup (MulAut (Sec (commV K) C))}, qOf G' = ((1 : ℚ) : WithTop ℚ) →
      (1 : WithTop ℚ) ≤ qOf G' := fun hq => by rw [hq]; exact le_of_eq (by simp)
  rcases hconcl with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact hq1 c1.2.2.2
  · exfalso
    obtain ⟨-, ⟨n, hn⟩, -⟩ := c2
    exact not_sl3_list hN hcL' hn
  · exfalso
    obtain ⟨⟨n, hn, h1⟩, -⟩ := c3
    by_cases hn1 : n = 1
    · subst hn1
      obtain ⟨⟨e6⟩, hL, -⟩ := FFC.ident_sp4 hb4 hn
      obtain ⟨f⟩ := FFC.commutator_equiv_alternating (by norm_num : 5 ≤ 6) e6
      have h2 : Nat.card ↥(autSec K (commV K) C) = Nat.card ↥(alternatingGroup (Fin 6)) := by
        rw [Nat.card_congr (MulEquiv.subgroupCongr hL).toEquiv, Nat.card_congr f.toEquiv]
      rw [hcL', card_alternatingGroup1527d 6 (by norm_num)] at h2
      norm_num [Nat.factorial] at h2
      rcases hN with rfl | rfl | rfl <;> omega
    · have hJL := h1 (by have := one_le_of_binaryNaturalSp4 hn; omega)
      rw [hJL] at hn
      exact not_sp4_list hN hcL' hn
  · exact hq1 c4.2
  · exact hq1 c5.2
  · exact hq1 c6.2.2.2.1
  · exact hq1 c7.2.2.2.2.1
  · exact hq1 c8.2.2.1
  · exfalso
    obtain ⟨-, n, hn4, hn, -⟩ := c9
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hn
    exact not_sl_two_list hN hcL' hn4 hπ
  · obtain ⟨hext, hrest⟩ := c10
    rcases hrest with hi | hii
    · exact hq1 hi.2.2.2
    · exfalso
      exact not_extSq_list hN hcL' (Or.inl rfl) hext
  · exact hq1 c11.2.2.2.1

end Sec

section Transfer

variable {V : Type} [CommGroup V] [Finite V]

theorem no_strong_of_section_q (hV : ∀ v : V, v ^ 2 = 1) {X K T A : Subgroup (MulAut V)}
    (h : B51Hyp X K) (hirr : commV K ∈ IrrPlus K ⊤) (hT : IsSylowTwoOf T X)
    (hA : IsFFStarOffender X A) (hAT : A ≤ T) {C : Subgroup V} (hC : C = fixV K ⊓ commV K)
    (hq : (1 : WithTop ℚ) ≤ qOf (autSec (K ⊔ T) (commV K) C)) : 1 ≤ rAV A := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hUC, hlt', hGU, hGC, hfL, hfM⟩ := secConfig hV h hirr hT hC
  have hAG : A ≤ X := hA.1
  have hAle : A ≤ K ⊔ T := hAT.trans le_sup_right
  have hAU : A ≤ stabSub (commV K) := hAG.trans hGU
  have hAC : A ≤ stabSub C := hAG.trans hGC
  have hfA : A ⊓ centSec (commV K) C = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [← hfM]
    exact inf_le_inf_right _ hAle
  have hr := FFC.B59.rAV_autSec_le hV hUC hAU hAC hfA hA.2.1 hA.2.2.1
  have hne : autSec A (commV K) C ≠ ⊥ := by
    intro hbot
    have hcard := card_autSec_mul (A := A) hAU hAC
    rw [hfA, Subgroup.card_bot, mul_one, hbot, Subgroup.card_bot] at hcard
    exact hA.2.1 (Subgroup.card_eq_one.1 hcard.symm)
  have hA2 : IsA2 (autSec (K ⊔ T) (commV K) C) (autSec A (commV K) C) :=
    ⟨autSec_mono hAle _ _, hne, isElemAbelian2_autSec _ _ hA.2.2.1⟩
  have hS2 := sq_eq_one_sec hV (commV K) C
  have hstrong : IsStrongFFModule (autSec (K ⊔ T) (commV K) C) :=
    (isStrongFFModule_iff hS2).2 ⟨_, hA2, lt_of_le_of_lt hr hlt⟩
  exact not_isStrongFFModule_of_one_le_qOf hS2 hq hstrong

end Transfer

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem list_no_strong (hB51 : AsB51) (hB42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    {X L S A : Subgroup (MulAut V)}
    (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hLq : CFSG.IsQuasisimple ↥L) (hLs : SQTKGroup ↥L)
    {N : ℕ} (hN : N = 1080 ∨ N = 2520 ∨ N = 6048) (hLc : Nat.card ↥L = N)
    (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S) (hO2 : pCoreOf 2 X = ⊥)
    (hLJ : L ≤ ffJ X) (hA : IsStrongFFStarOffender X A) : False := by
  classical
  have hXn : X ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    exact ⟨fun hl => hLn x hx l hl, fun h => by
      have := hLn x⁻¹ (X.inv_mem hx) _ h
      simpa [mul_assoc] using this⟩
  have hX2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L := fun x hx =>
    C1Pack153.exists_pow_mem_of_mem_sup_two hS.2.1 (fun s hs => hXn (hS.1 hs)) (hXLS hx)
  set G₁ := ffJ X with hG₁
  have hG₁X : G₁ ≤ X := B6.ffJ_le X
  have hLo := B1Red.isQuasisimple_to_open hLq
  have hG₁n : ∀ y ∈ G₁, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun y hy l hl => hLn y (hG₁X hy) l hl
  have hG₁2 : ∀ y ∈ G₁, ∃ e : ℕ, y ^ 2 ^ e ∈ L := fun y hy => hX2 y (hG₁X hy)
  have hO2G₁ : pCoreOf 2 G₁ = ⊥ := by
    refine le_bot_iff.mp ?_
    have h1 : pCoreOf 2 G₁ ≤ pCoreOf 2 X := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hRX : pCoreOf 2 G₁ ≤ X := (pCoreOf_le 2 G₁).trans hG₁X
      refine le_pCoreOf_of_le_normalizer 2 hRX ?_ (pCoreOf_isPGroup 2 G₁)
      intro x hx
      have h1 : conjSub x G₁ = G₁ := B6.conjSub_eq_self (B6.le_normalizer_ffJ X hx)
      have h2 : conjSub x (pCoreOf 2 G₁) = pCoreOf 2 G₁ := by
        rw [← pCoreOf_conjSub, h1]
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        rw [← h2]
        exact mul_mem_conjSub hr
      · intro hr
        rw [← h2] at hr
        have := mem_conjSub.mp hr
        simpa [mul_assoc] using this
    rwa [hO2] at h1
  have hFstar : quasithinGenFitting G₁ = L :=
    InternalSec.quasithinGenFitting_eq_of_two_pow hLJ hG₁n hLo hG₁2 hO2G₁
  have hB : B51Hyp G₁ L := by
    refine ⟨?_, hLq, hLs, hLJ, hO2G₁, (InternalSec.ffJ_ffJ X).symm⟩
    have hZL : centerOf G₁ ≤ L := (FFC.centerOf_le_genFitting G₁).trans hFstar.le
    rw [hFstar, sup_eq_left.mpr hZL]
  have hirr := list_irrPlus hB51 hV hB hN hLc
  have hAoff := hA.1
  have hAG₁ : A ≤ G₁ := B6.le_ffJ hAoff
  have hA' : IsFFStarOffender G₁ A := ⟨hAG₁, hAoff.2⟩
  obtain ⟨T, hT, hAT⟩ := FFC.B59.exists_isSylowTwoOf_ge hAG₁ hAoff.2.2.1.isPGroup
  obtain ⟨C, hC⟩ : ∃ C : Subgroup V, C = fixV L ⊓ commV L := ⟨_, rfl⟩
  have hq1 := section_q_one hB42 hV hB hirr hT hA' hAT hC hN hLc
  exact absurd hA.2 (not_lt.2 (no_strong_of_section_q hV hB hirr hT hA' hAT hC hq1))

end Main

end S1549D

end CFSG.Quasithin
