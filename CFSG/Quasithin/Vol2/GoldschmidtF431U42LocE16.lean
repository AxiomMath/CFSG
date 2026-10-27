module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocV

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

@[expose] def commIdx (i j : ℕ) : Bool :=
  comp (Tl.getD i []) (Tl.getD j []) == comp (Tl.getD j []) (Tl.getD i [])

@[expose] def isInvT (i : ℕ) : Bool :=
  comp (Tl.getD i []) (Tl.getD i []) == idL && Tl.getD i [] != idL

@[expose] def cSet (i : ℕ) : Finset ℕ := (Finset.range 64).filter fun j => commIdx i j = true

@[expose] def chkE16 : Bool := (List.range 64).all fun i =>
  !(isInvT i && !fixL0 (Tl.getD i [])) ||
    ((cSet i).card == 16 && (List.range 64).any fun j =>
      commIdx i j && comp (Tl.getD j []) (Tl.getD j []) != idL)

theorem chkE16_true : chkE16 = true := by decide +kernel

theorem eq_Vsub_of_elemAbelian {E : Subgroup Y} (hET : E ≤ T)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    (hcard : Nat.card Vsub ≤ Nat.card E) : E = Vsub := by
  by_contra hne
  have hex : ∃ e ∈ E, e ∉ Vsub := by
    by_contra hall
    refine hne (Subgroup.eq_of_le_of_card_ge (fun e he => ?_) hcard)
    by_contra h
    exact hall ⟨e, he, h⟩
  obtain ⟨e, heE, heV⟩ := hex
  obtain ⟨i, hi, hrepe⟩ := (mem_T_iff e).1 (hET heE)
  have hinv : isInvT i = true := by
    have h1 : comp (Tl.getD i []) (Tl.getD i []) = idL := by
      have := repL_mul hrepe hrepe
      rw [← Subgroup.coe_mul, hsq e heE] at this
      exact repL_unique this (repL_one 45)
    have h2 : Tl.getD i [] ≠ idL := by
      intro h
      apply heV
      have : e = 1 := Subtype.ext (eq_of_repL hrepe (by rw [h]; exact repL_one 45))
      rw [this]
      exact Vsub.one_mem
    simp only [isInvT, h1, beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq, h2,
      not_false_eq_true]
  have hnf : fixL0 (Tl.getD i []) = false := by
    by_contra h
    exact heV (mem_Vsub_of_fix (hET heE) ((fixL0_iff hrepe).1 (by simpa using h)))
  have h16 := chkE16_true
  simp only [chkE16, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at h16
  have hspec := h16 i hi
  rcases hspec with h1 | ⟨hc16, j0, hj0, hcj0, hsq0⟩
  · simp only [hinv, hnf, Bool.not_false, Bool.and_self] at h1
    exact absurd h1 (by decide)
  · have hmemE : ∀ g : E, ∃ j < 64, RepL (Tl.getD j []) ((g : Y) : P45) :=
      fun g => (mem_T_iff g).1 (hET g.2)
    choose! Φ hΦ using hmemE
    have hΦS : ∀ g : E, Φ g ∈ cSet i := by
      intro g
      have hj := (hΦ g).1
      have hr := (hΦ g).2
      simp only [cSet, Finset.mem_filter, Finset.mem_range, commIdx, beq_iff_eq]
      refine ⟨hj, ?_⟩
      have hg : (e : P45) * ((g : Y) : P45) = ((g : Y) : P45) * (e : P45) :=
        congrArg Subtype.val (hcomm e heE g g.2)
      have e1 := repL_mul hrepe hr
      have e2 := repL_mul hr hrepe
      rw [hg] at e1
      exact repL_unique e1 e2
    have hΦinj : Function.Injective Φ := by
      intro g g' h
      have h1 := (hΦ g).2
      have h2 := (hΦ g').2
      rw [h] at h1
      exact Subtype.ext (Subtype.ext (eq_of_repL h1 h2))
    have : Fintype E := Fintype.ofFinite E
    have himg : Finset.univ.image Φ = cSet i := by
      refine Finset.eq_of_subset_of_card_le (fun j hj => ?_) ?_
      · obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hj
        exact hΦS g
      · rw [Finset.card_image_of_injective _ hΦinj, hc16, Finset.card_univ,
          ← Nat.card_eq_fintype_card]
        exact (card_Vsub_ge).trans hcard
    have hj0S : j0 ∈ cSet i := by
      simp only [cSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj0, hcj0⟩
    rw [← himg] at hj0S
    obtain ⟨g, -, hg⟩ := Finset.mem_image.1 hj0S
    have hr := (hΦ g).2
    rw [hg] at hr
    have hsqg := hsq g g.2
    have := repL_mul hr hr
    rw [← Subgroup.coe_mul, hsqg] at this
    exact hsq0 (repL_unique this (repL_one 45))

end CFSG.Quasithin.H13.F431.U42
