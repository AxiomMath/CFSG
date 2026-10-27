module

public import CFSG.Quasithin.Background.F918M2
public import CFSG.Quasithin.Background.F918M3
public import CFSG.Quasithin.Background.F918M4
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.D2Offenders

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {V : Type} [CommGroup V] [Finite V]

theorem d29_further (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)} {I I' : Subgroup V}
    (hS : TwoSummands G I I') (hi : 2 < rk I) (hAG : A ≤ G) (hAe : IsElemAbelian2 A)
    {a : MulAut V} (haA : a ∈ A) (haI : a ∉ stabSub I) {c : V} (hcI : c ∈ I) (hc1 : c ≠ 1)
    (hBc : ∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x = x ∨ b x = x * c)
    (hrkB : rk ↥(A ⊓ stabSub I) + 1 = rk I)
    (hfull : ∀ t : MulAut ↥I, IsTransvectionWith t (⟨c, hcI⟩ : ↥I) →
      t ∈ autSub (A ⊓ stabSub I) I) :
    pCoreOf 2 G ≠ ⊥ ∨ ∃ A₀ : Subgroup (MulAut V), IsA2 G A₀ ∧ commSeries A₀ 2 = ⊥ ∧ rAV A₀ ≤ 1 := by
  set N : Subgroup (MulAut V) := G ⊓ stabSub I with hN
  set J : Subgroup V := Subgroup.closure {x | ∃ n ∈ N, n c = x} with hJ
  have haG : a ∈ G := hAG haA
  have hNst : N ≤ stabSub I := inf_le_right
  have hJI : J ≤ I := by
    rw [hJ, Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    exact (hNst hn c).mpr hcI
  have hcJ : c ∈ J := Subgroup.subset_closure ⟨1, N.one_mem, rfl⟩
  have hJN : ∀ n ∈ N, ∀ x ∈ J, n x ∈ J := by
    intro n hn x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨n * m, N.mul_mem hn hm, rfl⟩
    | one => rw [map_one]; exact J.one_mem
    | mul y z _ _ hy hz => rw [map_mul]; exact J.mul_mem hy hz
    | inv y _ hy => rw [map_inv]; exact J.inv_mem hy
  by_cases hJeq : J = I
  ·
    have hBN : A ⊓ stabSub I ≤ N := inf_le_inf_right _ hAG
    have hfull' : ∀ t : MulAut ↥I, IsTransvectionWith t (⟨c, hcI⟩ : ↥I) → t ∈ autSub N I :=
      fun t ht => autSub_mono hBN I (hfull t ht)
    have htop : autSub N I = ⊤ :=
      autSub_eq_top_of_transvections hV hNst hcI hc1 hfull' hJeq
    by_cases hker : G ⊓ centSub I = ⊥
    · right
      exact d29_further_diag hV hS hi hAG hAe haA haI hcI hc1 hBc hrkB hfull hJeq hker
    · right
      exact d29_further_kernel hV hS hi haG haI htop hker
  · left
    exact d29_further_small hV hS hAG hAe haA haI hcI hc1 hBc hfull J hJI hcJ hJeq hJN

theorem d29_five (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)}
    (hA : A ∈ kRPlusLe G 3 2) {I I' : Subgroup V} (hS : TwoSummands G I I') (hi : 2 ≤ rk I)
    (hB : A ⊓ stabSub I < A) :
    (∃ (c : V) (hc : c ∈ I), c ≠ 1 ∧
        (∀ t : MulAut ↥I, t ∈ autSub (A ⊓ stabSub I) I ↔
          IsTransvectionWith t (⟨c, hc⟩ : ↥I)) ∧
        (2 < rk I → pCoreOf 2 G ≠ ⊥ ∨ qOf G < (rAV A : WithTop ℚ))) ∨
    (rk I - rk ↥(I ⊓ fixV (A ⊓ stabSub I)) = rk I - 2 ∧ rk I - 2 = rk ↥(A ⊓ stabSub I) ∧
        (2 < rk I → rAV (A ⊓ stabSub I) = rAV A ∧ rAV A = 2 ∧ A ∉ QhatStar G)) := by
  have hAG : A ≤ G := hA.1.1.1.le
  have hAe : IsElemAbelian2 A := hA.1.1.1.isElemAbelian2
  obtain ⟨a, haA, haI⟩ : ∃ a ∈ A, a ∉ stabSub I := by
    by_contra h
    push Not at h
    exact absurd hB (not_lt_of_ge fun g hg => ⟨hg, h g hg⟩)
  rcases d29_shape hV hA (hS.mono hAG) hi hB with
    ⟨c, hc, hc1, hBc, hCI, hrkB, hr1, hfull⟩ | ⟨hrk, hm, hcase⟩
  · left
    refine ⟨c, hc, hc1, fun t => ⟨fun ht => ?_, hfull t⟩, fun h2 => ?_⟩
    · obtain ⟨⟨b, hb⟩, hbA, rfl⟩ := mem_autSub.mp ht
      refine ⟨hc1 ∘ fun h => congrArg Subtype.val h, fun x => ?_⟩
      rcases hBc b hbA x x.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rcases d29_further hV hS h2 hAG hAe haA haI hc hc1 hBc hrkB hfull with hp | ⟨A₀, hA₀, hq, hr⟩
      · exact Or.inl hp
      · right
        have h1 : qOf G ≤ ((1 : ℚ) : WithTop ℚ) :=
          qOf_le_iff.mpr ⟨A₀, hA₀, (isQuadratic_iff_commSeries_two A₀).mpr hq, hr⟩
        exact lt_of_le_of_lt h1 (WithTop.coe_lt_coe.mpr hr1)
  · right
    refine ⟨?_, ?_, fun h2 => ?_⟩
    · omega
    · omega
    · obtain ⟨hr, hr2⟩ := hcase h2
      refine ⟨hr, hr2, fun hQ => ?_⟩
      obtain ⟨r, hqr, -, hAk, hmin⟩ := QhatStar_spec hQ
      have hBne : A ⊓ stabSub I ≠ ⊥ := by
        intro h
        have : rk ↥(A ⊓ stabSub I) = 0 := by rw [h, rk_bot]
        omega
      have hA2 : IsA2 G A := hA.1.1.1
      have hBA : A ⊓ stabSub I ≤ A := inf_le_left
      have hmem : A ⊓ stabSub I ∈ kRle G 3 r := by
        refine ⟨⟨hA2.mono hBA hBne, ?_⟩, le_bot_iff.mp (hAk.2 ▸ commSeries_mono hBA 3)⟩
        rw [hr]
        exact hAk.1.2.le
      have := hmin _ hmem hBA
      exact absurd this (ne_of_lt hB)

theorem d29_six (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)} {I I' : Subgroup V}
    (hS : TwoSummands G I I') (hi : 2 < rk I) (hO2 : pCoreOf 2 G = ⊥) :
    ∀ A ∈ QhatStar G, A ≤ stabSub I := by
  intro A hQ
  by_contra hAI
  obtain ⟨r, hqr, hr2, hAk, hmin⟩ := QhatStar_spec hQ
  have hA2 : IsA2 G A := hAk.1.1
  have hAr : rAV A = r := hAk.1.2
  have hcub : commSeries A 3 = ⊥ := hAk.2
  have hplus : A ∈ RPlus G :=
    D2_3_2 hA2 hcub (by rw [hAr]; exact hqr.symm)
  have hmemA : A ∈ kRPlusLe G 3 2 :=
    ⟨⟨⟨hA2, by rw [hAr]; exact hr2⟩, hcub⟩, hplus⟩
  have hB : A ⊓ stabSub I < A := by
    refine lt_of_le_of_ne inf_le_left fun h => hAI ?_
    intro g hg
    have : g ∈ A ⊓ stabSub I := by rw [h]; exact hg
    exact this.2
  rcases d29_five hV hmemA hS hi.le hB with
    ⟨c, hc, hc1, hfull, hfurther⟩ | ⟨-, -, hcase⟩
  · rcases hfurther hi with hp | hq
    · exact hp hO2
    · have h1 : qhatOf G ≤ qOf G := qhatOf_le_qOf G
      rw [hqr] at h1
      rw [hAr] at hq
      exact lt_irrefl _ (lt_of_le_of_lt h1 hq)
  · obtain ⟨-, -, hQA⟩ := hcase hi
    exact hQA hQ

end CFSG.Quasithin
