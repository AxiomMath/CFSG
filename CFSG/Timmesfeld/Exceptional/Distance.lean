module

public import CFSG.Timmesfeld.Exceptional.KdStructure

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def nbhd (D : Set G) (c : G) : ℕ → Set G
  | 0 => {c}
  | k + 1 => nbhd D c k ∪ {d | d ∈ D ∧ ∃ e ∈ nbhd D c k, Commute d e}

variable {c d e : G} {k : ℕ}

theorem nbhd_zero : nbhd D c 0 = {c} := rfl

theorem mem_nbhd_self (k : ℕ) : c ∈ nbhd D c k := by
  induction k with
  | zero => exact rfl
  | succ k ih => exact Or.inl ih

theorem nbhd_subset (hc : c ∈ D) (k : ℕ) : nbhd D c k ⊆ D := by
  induction k with
  | zero =>
    intro d hd
    rw [nbhd_zero, Set.mem_singleton_iff] at hd
    exact hd ▸ hc
  | succ k ih =>
    rintro d (hd | ⟨hd, -⟩)
    exacts [ih hd, hd]

theorem nbhd_mono : Monotone (nbhd D c) :=
  monotone_nat_of_le_succ fun _ _ hd => Or.inl hd

theorem mem_nbhd_succ_of_commute (hd : d ∈ D) (he : e ∈ nbhd D c k) (hde : Commute d e) :
    d ∈ nbhd D c (k + 1) :=
  Or.inr ⟨hd, e, he, hde⟩

theorem mem_nbhd_succ_iff (hc : c ∈ D) :
    d ∈ nbhd D c (k + 1) ↔ d ∈ D ∧ ∃ e ∈ nbhd D c k, Commute d e := by
  refine ⟨fun hd => ?_, fun hd => Or.inr hd⟩
  rcases hd with hd | hd
  · exact ⟨nbhd_subset hc k hd, d, hd, Commute.refl d⟩
  · exact hd

theorem mem_nbhd_one_iff (hc : c ∈ D) : d ∈ nbhd D c 1 ↔ d ∈ D ∧ Commute d c := by
  rw [mem_nbhd_succ_iff hc]
  simp only [nbhd_zero, Set.mem_singleton_iff, exists_eq_left]

theorem mem_nbhd_add_two_of_orderOf_eq_four (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ nbhd D c k) (he' : e ∈ D) (h4 : orderOf (d * e) = 4) : d ∈ nbhd D c (k + 2) := by
  obtain ⟨hw, hdw, hew, -⟩ := sq_mem_of_orderOf_eq_four hD hd he' h4
  exact mem_nbhd_succ_of_commute hd (mem_nbhd_succ_of_commute hw he hew.symm) hdw

theorem mem_nbhd_two_iff (hD : IsRootInvolutionSet D) (hNL : NoLevi D) (hc : c ∈ D) :
    d ∈ nbhd D c 2 ↔ d ∈ D ∧ (Commute d c ∨ orderOf (d * c) = 4) := by
  constructor
  · intro hd
    obtain ⟨hdD, e, he, hde⟩ := (mem_nbhd_succ_iff hc).1 hd
    obtain ⟨heD, hec⟩ := (mem_nbhd_one_iff hc).1 he
    refine ⟨hdD, ?_⟩
    by_cases hdc : Commute d c
    · exact .inl hdc
    · exact .inr (hNL.orderOf_eq_four hD heD hdD hc hde.symm hec hdc)
  · rintro ⟨hdD, hdc | h4⟩
    · exact nbhd_mono (by norm_num) ((mem_nbhd_one_iff hc).2 ⟨hdD, hdc⟩)
    · exact mem_nbhd_add_two_of_orderOf_eq_four hD hdD (mem_nbhd_self 0) hc h4

theorem not_mem_nbhd_two_iff (hD : IsRootInvolutionSet D) (hNL : NoLevi D) (hc : c ∈ D)
    (hd : d ∈ D) : d ∉ nbhd D c 2 ↔ ¬ Commute d c ∧ Odd (orderOf (d * c)) := by
  rw [mem_nbhd_two_iff hD hNL hc]
  constructor
  · intro h
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hd hc with h1 | h1 | ⟨h1, h2⟩
    · exact absurd ⟨hd, .inl h1⟩ h
    · exact absurd ⟨hd, .inr h1⟩ h
    · exact ⟨h2, h1⟩
  · rintro ⟨hdc, hodd⟩ ⟨-, h1 | h1⟩
    · exact hdc h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)

theorem totallyOpposite_iff_not_mem_nbhd_three (hD : IsRootInvolutionSet D) (hNL : NoLevi D)
    (hc : c ∈ D) (hd : d ∈ D) : TotallyOpposite D d c ↔ d ∉ nbhd D c 3 := by
  rw [mem_nbhd_succ_iff hc]
  constructor
  · rintro hTO ⟨-, e, he, hde⟩
    have heD := nbhd_subset hc 2 he
    exact (not_mem_nbhd_two_iff hD hNL hc heD).2 (hTO e heD hde) he
  · intro h x hx hdx
    exact (not_mem_nbhd_two_iff hD hNL hc hx).1 fun hx2 => h ⟨hd, x, hx2, hdx⟩

theorem exists_special_of_mem_nbhd_three (hD : IsRootInvolutionSet D) (hNL : NoLevi D)
    (hNP : NoPolar D) (hc : c ∈ D) (h3 : d ∈ nbhd D c 3) (h2 : d ∉ nbhd D c 2) :
    ∃ x ∈ D, Commute d x ∧ d * x ∈ D ∧ orderOf (x * c) = 4 := by
  obtain ⟨hd, e, he, hde⟩ := (mem_nbhd_succ_iff hc).1 h3
  obtain ⟨heD, hec | h4⟩ := (mem_nbhd_two_iff hD hNL hc).1 he
  · exact absurd (mem_nbhd_succ_of_commute hd ((mem_nbhd_one_iff hc).2 ⟨heD, hec⟩) hde) h2
  · refine ⟨e, heD, hde, hNP d hd e heD hde fun hed => h2 (hed ▸ he), h4⟩

theorem orderOf_eq_three_of_mem_nbhd_three (hD : IsRootInvolutionSet D) (hNL : NoLevi D)
    (hNP : NoPolar D) (hP1 : ExcP1 D) (hc : c ∈ D) (h3 : d ∈ nbhd D c 3)
    (h2 : d ∉ nbhd D c 2) : orderOf (d * c) = 3 := by
  obtain ⟨x, hx, hdx, hdxD, h4⟩ := exists_special_of_mem_nbhd_three hD hNL hNP hc h3 h2
  have hd := nbhd_subset hc 3 h3
  obtain ⟨hdc, hodd⟩ := (not_mem_nbhd_two_iff hD hNL hc hd).1 h2
  exact hP1 d hd c hc hdc hodd x hx hdx hdxD h4

theorem NoLevi.sq_eq_of_commute (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNL : NoLevi D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) {y w z : G} (hy : y ∈ D) (hw : w ∈ D) (hz : z ∈ D)
    (hzy : Commute z y) (hzw : Commute z w) (hyw : ¬ Commute y w) : (y * w) ^ 2 = z := by
  have hyz : y ≠ z := by
    rintro rfl
    exact hyw hzw
  have hwz : w ≠ z := by
    rintro rfl
    exact hyw hzy.symm
  rcases NoLevi.centralizer_cases hD hconj hNL hNP hPl hz hy hw hzy hzw hyz hwz with
    h | h | ⟨-, h⟩
  · exact absurd (h ▸ Commute.refl y) hyw
  · exact absurd (h ▸ hzy.symm.mul_right (Commute.refl y)) hyw
  · exact h

theorem exists_mem_nbhd (hconn : Closure.CommConnected D) (hc : c ∈ D) (hd : d ∈ D) :
    ∃ k, d ∈ nbhd D c k := by
  refine hconn {x | ∃ k, x ∈ nbhd D c k} (fun x ⟨k, hk⟩ => nbhd_subset hc k hk)
    ⟨c, 0, mem_nbhd_self 0⟩ ?_ hd
  rintro x ⟨k, hk⟩ y hy hxy
  exact ⟨k + 1, mem_nbhd_succ_of_commute hy hk hxy.symm⟩

end CFSG.Timmesfeld.Moufang
