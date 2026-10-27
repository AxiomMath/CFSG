module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6A_rank_two_of_bad
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp7 : p = 7) (hm : rk ↥(wTil V₀ V hV L) = 6)
    (hbad : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∀ q ∈ D.sig, 2 ≤ CFSG.pRank q ↥(autSub (Mbar D.M V₀ V hV ⊓
      normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)) (wTil V₀ V hV L)) := by
  intro q hq
  by_contra hcon
  have hqprime : q.Prime := (D.sig_prime q hq).1
  have hq2 : q ≠ 2 := (D.sig_prime q hq).2
  have hle : CFSG.pRank q ↥(autSub (Mbar D.M V₀ V hV ⊓
      normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)) (wTil V₀ V hV L)) ≤ 1 := by
    omega
  have h3 : 3 ≤ CFSG.Open.pRank q D.M := S.hx.three_le q hq
  have h3' : 3 ≤ CFSG.pRank q ↥D.M := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := D.M)]
    exact h3
  obtain ⟨E, hEM, hEab, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) hqprime (M := D.M) (k := 3) h3'
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hEst : E ≤ stabTil V₀ V := hEM.trans hMstab
  let Ub : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L
  let lB : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV ⊓ normalizer (lB : Set _)
  have hleOpen : CFSG.Open.pRank q (autSub A Ub) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := autSub A Ub)]
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hle
  let Eb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV E
  have hEb_leA : Eb ≤ A := by
    refine le_inf (barSub_mono V₀ V hV hEM) ?_
    exact s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 (by omega)
      (hqprime.odd_of_ne_two hq2) hEM hEab
  have hEb_ab : IsElemAbelian q Eb := s16h_barSub_isElemAbelian hV hEab
  have hEb_stab : Eb ≤ stabSub Ub := by
    intro g hg
    have hgn : g ∈ normalizer (lB : Set (MulAut (Vtil V₀ V hV))) := (mem_inf.1 (hEb_leA hg)).2
    exact StabLat.mem_stabSub_commSub (X := lB) (Y := ⊤) (g := g)
      (by intro u; simp) hgn
  let Q : Subgroup (MulAut (Vtil V₀ V hV)) := Eb ⊓ centSub Ub
  have hQ : Q ≤ barSub V₀ V hV E := fun x hx => hx.1
  have hcardEb := card_autSub_mul (A := Eb) (U := Ub) hEb_stab
  have hcardE := s16c7_card_mul_card_preBarSub (V₀ := V₀) (V := V) (E := E) hV hEst
    (Q := Q) hQ
  have hpre : preBarSub E V₀ V hV Q = E ⊓ preBarSub D.M V₀ V hV (centSub Ub) := by
    ext g
    rw [mem_preBarSub E V₀ V hV Q, Subgroup.mem_inf,
      mem_preBarSub D.M V₀ V hV (centSub Ub)]
    constructor
    · rintro ⟨hgE, hgs, hgQ⟩
      exact ⟨hgE, hEM hgE, hgs, hgQ.2⟩
    · rintro ⟨hgE, -, hgs, hgc⟩
      exact ⟨hgE, hgs, ⟨actTil_mem_barSub V₀ V hV hgE hgs, hgc⟩⟩
  rw [hpre] at hcardE
  have hmul : Nat.card E = Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV (centSub Ub)) *
      Nat.card (autSub Eb Ub) := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Q)) ?_
    calc Nat.card E * Nat.card ↥Q
        = Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV (centSub Ub)) * Nat.card Eb := hcardE
      _ = Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV (centSub Ub)) *
            (Nat.card (autSub Eb Ub) * Nat.card ↥Q) := by rw [← hcardEb]
      _ = (Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV (centSub Ub)) *
            Nat.card (autSub Eb Ub)) * Nat.card ↥Q := by ring
  have hEbA1_ab : IsElemAbelian q (autSub Eb Ub) := by
    have h1 : IsElemAbelian q (Eb.subgroupOf (stabSub Ub)) := hEb_ab.subgroupOf (stabSub Ub)
    have h2 : IsElemAbelian q ((Eb.subgroupOf (stabSub Ub)).map (resHom Ub)) :=
      h1.map (resHom Ub)
    exact h2
  have hEbA1_le : autSub Eb Ub ≤ autSub A Ub := autSub_mono hEb_leA Ub
  have hrank_le : CFSG.Open.pRank q (autSub Eb Ub) ≤ 1 := by
    exact (CFSG.SectionRank.pRank_mono (p := q) hqprime.one_lt hEbA1_le).trans hleOpen
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEbA1_ab.isPGroup
  have hnle : n ≤ 1 := (CFSG.SectionRank.le_pRank (p := q) hqprime.one_lt (le_refl _)
    hEbA1_ab hn).trans hrank_le
  have hcardAuto_le : Nat.card (autSub Eb Ub) ≤ q := by
    rw [hn]
    calc q ^ n ≤ q ^ 1 := Nat.pow_le_pow_right hqprime.pos hnle
      _ = q := pow_one q
  have hXcard : q ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV (centSub Ub)) := by
    rw [hEcard] at hmul
    have hle1 : q ^ 3 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV (centSub Ub)) * q := by
      rw [hmul]
      exact Nat.mul_le_mul_left _ hcardAuto_le
    have h2 : q ^ 2 * q ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV (centSub Ub)) * q := by
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hle1
    exact Nat.le_of_mul_le_mul_right h2 hqprime.pos
  exact hbad (s16h_uniqueMax_of_card_le D S.h61 S.h127 h hq h3 hEab hXcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
