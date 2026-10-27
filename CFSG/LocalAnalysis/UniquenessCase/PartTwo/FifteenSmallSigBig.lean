module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourRankSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeI
import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Big

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

theorem s15Small_dvd_of_rs_two (D : Data G) (hAut : RAutRank153) (hAbs : RAbsIrr153)
    (hSimple : RSimple153) (h127 : R127 D) (h1111 : R1111_153 D) (h1217 : R1217 D)
    {V₀ V L K₀ : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) {q : ℕ} (hq : q ∈ D.sig) :
    q ∣ Nat.card ↥(barSub V₀ V hV K₀) := by
  by_contra hqK
  have hqprime : q.Prime := (D.sig_prime q hq).1
  have hq2 : q ≠ 2 := (D.sig_prime q hq).2
  have hqodd : Odd q := hqprime.odd_of_ne_two hq2
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have hrk : 1 ≤ CFSG.Open.pRank q (Mbar D.M V₀ V hV) := by
    have h1 := h1111 V₀ V hH11 q hq
    have h2 := s15_Three_pRank_MBar11 hV hMs q
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    omega
  obtain ⟨y, hyM, hyord⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hqprime hrk
  have hyq : y ^ q = 1 := hyord ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyord
    exact hqprime.ne_one hyord.symm
  have hcard : Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV K₀).map (MulAut.conj φ).toMonoidHom} ≤ 2 :=
    (s15GapFour_ncard_conj_le (Mbar D.M V₀ V hV) (barSub V₀ V hV K₀)
      (barSub V₀ V hV L)).trans (le_of_eq hrs)
  have hZ : Subgroup.center ↥(barSub V₀ V hV K₀) = ⊥ := (hSimple _ _ _ _ hperf).2
  have hcen : ∀ x ∈ Mbar D.M V₀ V hV,
      x * y * x⁻¹ ∈ centralizer (barSub V₀ V hV K₀ : Set (MulAut (Vtil V₀ V hV))) := by
    intro x hx
    have hxy : x * y * x⁻¹ ∈ Mbar D.M V₀ V hV :=
      (Mbar D.M V₀ V hV).mul_mem ((Mbar D.M V₀ V hV).mul_mem hx hyM)
        ((Mbar D.M V₀ V hV).inv_mem hx)
    have hxq : (x * y * x⁻¹) ^ q = 1 := by rw [conj_pow, hyq]; simp
    have hnorm : x * y * x⁻¹ ∈ normalizer (barSub V₀ V hV K₀ : Set (MulAut (Vtil V₀ V hV))) :=
      s15GapFour_mem_normalizer_of_odd (Mbar D.M V₀ V hV) (barSub V₀ V hV K₀) hcard hxy hqodd hxq
    exact s15GapFour_centralizes_of_normalizes hAut hL2 hZ hnorm hqprime hqK hxq
  exact hy1 (s15GapFour_eq_one_of_centralizes hAbs D h1217 h hV hshape hperf hyM hcen)

theorem s15Small_sig_big (hAut : RAutRank153) (hAbs : RAbsIrr153) (hSimple : RSimple153)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1111 : R1111_153 D) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hsmall : mSub V₀ ≤ 2)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) (hne : D.sig.Nonempty) (h3 : 3 ∉ D.sig) :
    ∃ p : ℕ, ((p = 5 ∧ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5) ∨
        (p = 7 ∧ IsL3 ↥(barSub V₀ V hV K₀) 1)) ∧
      D.sig = {p} ∧ CFSG.Open.pRank p D.M = 3 := by
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have hcard4 : Nat.card V₀ ≤ 4 := by
    rw [card_eq_two_pow_mSub hpf.elemAbelian₀.isPGroup]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hsmall
      _ = 4 := by norm_num
  have hdvd := fun q hq => s15Small_dvd_of_rs_two D hAut hAbs hSimple h127 h1111 h1217 h hV hshape
    hperf hL2 hrs (q := q) hq
  have hle3 := fun q hq => s15GapFour_pRank_le_three_of_small hAut hAbs hSimple D h61 h127 h1217
    h hV hshape hperf hL2 hrs hcard4 (q := q) hq
  have hq2 : ∀ r ∈ D.sig, r ≠ 2 := fun r hr => (D.sig_prime r hr).2
  have hq3 : ∀ r ∈ D.sig, r ≠ 3 := fun r hr h3' => h3 (h3' ▸ hr)
  have hrk3 : ∀ r ∈ D.sig, CFSG.Open.pRank r D.M = 3 := by
    intro r hr
    have := (h1111 V₀ V hH11 r hr).2
    have := hle3 r hr
    omega
  obtain ⟨q, hq⟩ := hne
  rcases hL2 with hL3' | hA5'
  · have hr7 : ∀ r ∈ D.sig, r = 7 := by
      intro r hr
      have hd := hdvd r hr
      rw [WeakClosure81.card_eq_of_isL3 hL3'] at hd
      rcases s15_Three_prime_dvd_168 (D.sig_prime r hr).1 hd with h | h | h
      · exact absurd h (hq2 r hr)
      · exact absurd h (hq3 r hr)
      · exact h
    refine ⟨7, Or.inr ⟨rfl, hL3'⟩, ?_, ?_⟩
    · ext r
      simp only [Set.mem_singleton_iff]
      exact ⟨hr7 r, fun hr => by rw [hr]; exact (hr7 q hq) ▸ hq⟩
    · exact hrk3 7 ((hr7 q hq) ▸ hq)
  · have hr5 : ∀ r ∈ D.sig, r = 5 := by
      intro r hr
      have hd := hdvd r hr
      rw [s15_Three_card_alt_five hA5'] at hd
      rcases s15_Three_prime_dvd_60 (D.sig_prime r hr).1 hd with h | h | h
      · exact absurd h (hq2 r hr)
      · exact absurd h (hq3 r hr)
      · exact h
    refine ⟨5, Or.inl ⟨rfl, hA5'⟩, ?_, ?_⟩
    · ext r
      simp only [Set.mem_singleton_iff]
      exact ⟨hr5 r, fun hr => by rw [hr]; exact (hr5 q hq) ▸ hq⟩
    · exact hrk3 5 ((hr5 q hq) ▸ hq)

end Big

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
