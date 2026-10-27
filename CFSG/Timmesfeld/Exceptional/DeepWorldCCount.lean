module

public import CFSG.Timmesfeld.Exceptional.DeepWorldCBasic

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

theorem ncard_mul_le_ncard_mul {α β : Type*} [Finite α] [Finite β] {s : Set α} {t : Set β}
    (r : α → β → Prop) {m n : ℕ} (hm : ∀ a ∈ s, m ≤ {b | b ∈ t ∧ r a b}.ncard)
    (hn : ∀ b ∈ t, {a | a ∈ s ∧ r a b}.ncard ≤ n) : s.ncard * m ≤ t.ncard * n := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [Set.ncard_eq_toFinset_card' s, Set.ncard_eq_toFinset_card' t]
  refine Finset.card_mul_le_card_mul r (fun a ha => ?_) (fun b hb => ?_)
  · have h := hm a (Set.mem_toFinset.1 ha)
    rw [Set.ncard_eq_toFinset_card'] at h
    convert h using 2
    ext b
    simp [Finset.mem_bipartiteAbove]
  · have h := hn b (Set.mem_toFinset.1 hb)
    rw [Set.ncard_eq_toFinset_card'] at h
    convert h using 2
    ext a
    simp [Finset.mem_bipartiteBelow]

variable {G : Type*} [Group G] {D : Set G}

theorem ncard_diff_pair_eq {α : Type*} [Finite α] {s : Set α} {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) (hs : s.ncard = 10) : (s \ {a, b}).ncard = 8 := by
  have hsub : ({a, b} : Set α) ⊆ s := by
    rintro x (rfl | rfl)
    exacts [ha, hb]
  rw [Set.ncard_sdiff hsub, Set.ncard_pair hab, hs]

namespace FiveLineSetting

variable (S : FiveLineSetting G D)
include S

theorem eighty_le {p : G} (hp : p ∈ D) : 80 ≤ (nbhd D p 2 \ nbhd D p 1).ncard := by
  have := S.finite
  have h := ncard_mul_le_ncard_mul (s := collinearSet D p) (t := nbhd D p 2 \ nbhd D p 1)
    (fun x u => u ∈ collinearSet D x) (m := 8) (n := 1) (fun x hx => ?_) (fun u hu => ?_)
  · rw [S.ten p hp] at h
    omega
  ·
    have hpx : p ∈ collinearSet D x := mem_collinearSet_symm hp hx
    have hpxx : p * x ∈ collinearSet D x := mul_mem_collinearSet_right S.root hp hx
    have hne : p ≠ p * x := fun e => S.root.ne_one hx.1 (by
      have := congrArg (p⁻¹ * ·) e
      simpa using this.symm)
    rw [← ncard_diff_pair_eq hpx hpxx hne (S.ten x hx.1)]
    refine Set.ncard_le_ncard (fun v hv => ?_) (Set.toFinite _)
    obtain ⟨hv, hv'⟩ := hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hv'
    exact ⟨S.mem_two hp hx hv hv'.1 hv'.2, hv⟩
  ·
    refine (Set.ncard_le_one (Set.toFinite _)).2 fun x hx y hy => ?_
    have hu1 := hu.2
    have huD := nbhd_subset hp 2 hu.1
    rw [S.eq_sq_of_commute hp huD hu1 hx.1.1 hx.1.2.1.symm hx.2.2.1,
      S.eq_sq_of_commute hp huD hu1 hy.1.1 hy.1.2.1.symm hy.2.2.1]

theorem eight_mul_two_le {p : G} (hp : p ∈ D)
    (hfar : ∀ w, w ∈ nbhd D p 3 → w ∉ nbhd D p 2 → ∃ a ∈ collinearSet D w, a ∉ nbhd D p 3) :
    (nbhd D p 2 \ nbhd D p 1).ncard * 8 ≤ (nbhd D p 3 \ nbhd D p 2).ncard := by
  have := S.finite
  have h := ncard_mul_le_ncard_mul (s := nbhd D p 2 \ nbhd D p 1)
    (t := nbhd D p 3 \ nbhd D p 2) (fun u w => w ∈ collinearSet D u) (m := 8) (n := 1)
    (fun u hu => ?_) (fun w hw => ?_)
  · simpa using h
  · obtain ⟨hu2, hu1⟩ := hu
    have huD := nbhd_subset hp 2 hu2
    have h4 := S.orderOf_eq_four_of_mem_two hp hu2 hu1
    have h4' : orderOf (p * u) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
    obtain ⟨hxD, hpx, hux, -⟩ := sq_mem_of_orderOf_eq_four S.root hp huD h4'
    set x := (p * u) ^ 2
    have hxu : x ≠ u := fun e => hu1 ((mem_nbhd_one_iff hp).2 ⟨huD, e ▸ hpx.symm⟩)
    have hx : x ∈ collinearSet D u := (S.mem_collinearSet_iff huD).2 ⟨hxD, hux, hxu⟩
    have hux' : u * x ∈ collinearSet D u := mul_mem_collinearSet S.root huD hx
    have hne : x ≠ u * x := fun e => S.root.ne_one huD (by
      have := congrArg (· * x⁻¹) e
      simpa using this.symm)
    rw [← ncard_diff_pair_eq hx hux' hne (S.ten u huD)]
    refine Set.ncard_le_ncard (fun v hv => ?_) (Set.toFinite _)
    obtain ⟨hv, hv'⟩ := hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hv'
    exact ⟨S.mem_three hp hu2 hu1 hv hv'.1 hv'.2, hv⟩
  · obtain ⟨hw3, hw2⟩ := hw
    have hwD := nbhd_subset hp 3 hw3
    obtain ⟨a, ha, ha3⟩ := hfar w hw3 hw2
    refine (Set.ncard_le_one (Set.toFinite _)).2 fun u hu v hv => ?_
    exact S.eq_of_mem_two_of_far hp hw3 hw2 ha ha3
      (mem_collinearSet_symm (nbhd_subset hp 2 hv.1.1) hv.2) hv.1.1
      (mem_collinearSet_symm (nbhd_subset hp 2 hu.1.1) hu.2) hu.1.1

theorem eight_mul_three_le {p : G} (hp : p ∈ D)
    (hfar : ∀ w, w ∈ nbhd D p 3 → w ∉ nbhd D p 2 → ∃ a ∈ collinearSet D w, a ∉ nbhd D p 3) :
    (nbhd D p 3 \ nbhd D p 2).ncard * 8 ≤ (nbhd D p 4 \ nbhd D p 3).ncard * 2 := by
  have := S.finite
  refine ncard_mul_le_ncard_mul (fun w a => a ∈ collinearSet D w) (fun w hw => ?_)
    (fun a ha => ?_)
  · obtain ⟨hw3, hw2⟩ := hw
    have hwD := nbhd_subset hp 3 hw3
    obtain ⟨a, ha, ha3⟩ := hfar w hw3 hw2
    obtain ⟨-, u, hu2, hwu⟩ := (mem_nbhd_succ_iff hp).1 hw3
    have huD := nbhd_subset hp 2 hu2
    have huw : u ≠ w := fun e => hw2 (e ▸ hu2)
    have hu : u ∈ collinearSet D w := (S.mem_collinearSet_iff hwD).2 ⟨huD, hwu, huw⟩
    have huniq : ∀ u' ∈ collinearSet D w, u' ∈ nbhd D p 2 → u' = u := fun u' hu' hu'2 =>
      S.eq_of_mem_two_of_far hp hw3 hw2 ha ha3 hu hu2 hu' hu'2
    have hwu' : w * u ∈ collinearSet D w := mul_mem_collinearSet S.root hwD hu
    have hne : u ≠ w * u := fun e => S.root.ne_one hwD (by
      have := congrArg (· * u⁻¹) e
      simpa using this.symm)
    rw [← ncard_diff_pair_eq hu hwu' hne (S.ten w hwD)]
    refine Set.ncard_le_ncard (fun v hv => ?_) (Set.toFinite _)
    obtain ⟨hv, hv'⟩ := hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hv'
    exact ⟨S.mem_four hp hw3 hw2 huniq hv hv'.1 hv'.2, hv⟩
  · obtain ⟨ha4, ha3⟩ := ha
    have haD := nbhd_subset hp 4 ha4
    by_contra hlt
    push Not at hlt
    obtain ⟨w₀, w₁, w₂, h₀, h₁, h₂, h01, h02, h12⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 hlt
    have hy : ∀ w ∈ {w | w ∈ nbhd D p 3 \ nbhd D p 2 ∧ a ∈ collinearSet D w},
        w ∈ collinearSet D a := fun w hw => mem_collinearSet_symm (nbhd_subset hp 3 hw.1.1) hw.2
    refine S.noThreeNear p hp a haD ha3
      (S.threeNear_of_three hp haD ha3 (y := ![w₀, w₁, w₂]) (fun i => ?_) (fun i => ?_)
        (fun i j hij => ?_))
    · fin_cases i
      exacts [hy _ h₀, hy _ h₁, hy _ h₂]
    · fin_cases i
      exacts [h₀.1.1, h₁.1.1, h₂.1.1]
    · fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem le_ncard_four {p : G} (hp : p ∈ D)
    (hfar : ∀ w, w ∈ nbhd D p 3 → w ∉ nbhd D p 2 → ∃ a ∈ collinearSet D w, a ∉ nbhd D p 3) :
    2560 ≤ (nbhd D p 4 \ nbhd D p 3).ncard := by
  have h2 := S.eighty_le hp
  have h3 := S.eight_mul_two_le hp hfar
  have h4 := S.eight_mul_three_le hp hfar
  omega

end FiveLineSetting

end CFSG.Timmesfeld.Moufang.Deep
