module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainE6

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem nmh_eq_zero_of_neg_eq_self {x : ZMod 3} (h : x = -x) : x = 0 := by
  revert h; revert x; decide

private theorem nmh_fixed_iff {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} {v : Coords 8} :
    spMat σ s *ᵥ v = v ↔ ∀ j, v (σ j) = s j * v j := by
  constructor
  · intro hv j
    have h := congrFun hv (σ j)
    rw [spMat_mulVec] at h
    simpa using h.symm
  · intro hv
    funext i
    simp only [spMat_mulVec]
    rw [← hv (σ.symm i), Equiv.apply_symm_apply]

theorem nmh_involution_data {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hs : IsSign s) (h2 : spMat σ s * spMat σ s = 1) :
    (∀ j, σ (σ j) = j) ∧ ∀ j, s (σ j) * s j = 1 := by
  have hs' : IsSign fun j => s (σ j) * s j := IsSign.mul (fun j => hs (σ j)) hs
  have h' : spMat (σ * σ) (fun j => s (σ j) * s j) = spMat 1 (fun _ => 1) := by
    rw [← spMat_mul, h2, spMat_one]
  obtain ⟨hσ2, hsign⟩ := nm_spMat_inj hs' (fun _ => Or.inl rfl) h'
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := DFunLike.congr_fun hσ2 j
    simpa [Equiv.Perm.mul_apply] using this
  · exact congrFun hsign j

theorem nmh_diagonal_eq_spMat (d : Fin 8 → ZMod 3) :
    Matrix.diagonal d = spMat (1 : Equiv.Perm (Fin 8)) d := by
  ext i j
  by_cases h : i = j
  · subst h; simp [spMat_apply, Matrix.diagonal_apply_eq]
  · simp [spMat_apply, Matrix.diagonal_apply, h]

private theorem nmh_spMat_eq_perm_mul_diagonal (σ : Equiv.Perm (Fin 8))
    (s : Fin 8 → ZMod 3) :
    spMat σ s = spMat σ (fun _ => 1) * Matrix.diagonal s := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [spMat_apply, spMat_apply]
    by_cases h : i = σ j <;> simp [h]
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

private theorem nmh_spMat_one_eq_permMatrix (σ : Equiv.Perm (Fin 8)) :
    spMat σ (fun _ => 1) = Equiv.Perm.permMatrix (ZMod 3) σ.symm := by
  ext i j
  rw [spMat_apply]
  change (if i = σ j then (1 : ZMod 3) else 0)
    = ((σ.symm).toPEquiv.toMatrix) i j
  have h : ((σ.symm).toPEquiv.toMatrix : Matrix (Fin 8) (Fin 8) (ZMod 3)) i =
      Pi.single (σ.symm i) (1 : ZMod 3) := PEquiv.toMatrix_toPEquiv_apply σ.symm i
  rw [congrFun h j, Pi.single_apply]
  by_cases hij : i = σ j
  · subst hij
    rw [if_pos rfl, if_pos (Equiv.symm_apply_apply σ j).symm]
  · have hne : j ≠ σ.symm i := fun hh => hij (by rw [← Equiv.apply_symm_apply σ i, hh])
    rw [if_neg hij, if_neg hne]

theorem nmh_det_spMat (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3) :
    (spMat σ s).det = (Equiv.Perm.sign σ : ZMod 3) * ∏ j, s j := by
  conv_lhs => rw [nmh_spMat_eq_perm_mul_diagonal]
  rw [Matrix.det_mul, nmh_spMat_one_eq_permMatrix, Matrix.det_permutation,
    Equiv.Perm.sign_symm, Matrix.det_diagonal]

@[expose] def nmhPF (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3) : Finset (Fin 8) :=
  Finset.univ.filter fun j => σ j = j ∧ s j = 1

@[expose] def nmhAF (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3) : Finset (Fin 8) :=
  Finset.univ.filter fun j => σ j = j ∧ s j = -1

@[expose] def nmhCF (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3) : Finset (Fin 8) :=
  Finset.univ.filter fun j => σ j ≠ j ∧ j < σ j

private abbrev nmhIdx (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3) : Type :=
  {j : Fin 8 // σ j = j ∧ s j = 1} ⊕ {j : Fin 8 // σ j ≠ j ∧ j < σ j}

private def nmhIdxVal {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} : nmhIdx σ s → Fin 8
  | Sum.inl x => x.1
  | Sum.inr x => x.1

private noncomputable def nmhExtend (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3)
    (hσ : ∀ j, σ (σ j) = j) (f : nmhIdx σ s → ZMod 3) : Coords 8 :=
  fun j =>
    if hfix : σ j = j then
      if hs1 : s j = 1 then f (Sum.inl ⟨j, hfix, hs1⟩) else 0
    else
      if hlt : j < σ j then f (Sum.inr ⟨j, hfix, hlt⟩)
      else
        s (σ j) * f (Sum.inr ⟨σ j, by rw [hσ]; exact fun h => hfix h.symm, by
          rw [hσ]; exact lt_of_le_of_ne (le_of_not_gt hlt) fun h => hfix h⟩)

private theorem nmhExtend_fixed_pos {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hσ : ∀ j, σ (σ j) = j) (f : nmhIdx σ s → ZMod 3) {j : Fin 8} (hfix : σ j = j)
    (hs1 : s j = 1) :
    nmhExtend σ s hσ f j = f (Sum.inl ⟨j, hfix, hs1⟩) := by
  simp only [nmhExtend, dif_pos hfix, dif_pos hs1]

private theorem nmhExtend_fixed_neg {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hσ : ∀ j, σ (σ j) = j) (f : nmhIdx σ s → ZMod 3) {j : Fin 8} (hfix : σ j = j)
    (hs1 : s j ≠ 1) :
    nmhExtend σ s hσ f j = 0 := by
  simp only [nmhExtend, dif_pos hfix, dif_neg hs1]

private theorem nmhExtend_lt {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hσ : ∀ j, σ (σ j) = j) (f : nmhIdx σ s → ZMod 3) {j : Fin 8} (hfix : σ j ≠ j)
    (hlt : j < σ j) :
    nmhExtend σ s hσ f j = f (Sum.inr ⟨j, hfix, hlt⟩) := by
  simp only [nmhExtend, dif_neg hfix, dif_pos hlt]

private theorem nmhExtend_gt {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hσ : ∀ j, σ (σ j) = j) (f : nmhIdx σ s → ZMod 3) {j : Fin 8} (hfix : σ j ≠ j)
    (hlt : ¬ j < σ j) :
    nmhExtend σ s hσ f j
      = s (σ j) * f (Sum.inr ⟨σ j, by rw [hσ]; exact fun h => hfix h.symm, by
          rw [hσ]; exact lt_of_le_of_ne (le_of_not_gt hlt) fun h => hfix h⟩) := by
  simp only [nmhExtend, dif_neg hfix, dif_neg hlt]

private theorem nmhExtend_rel {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hσ : ∀ j, σ (σ j) = j) (hsign : ∀ j, s (σ j) * s j = 1)
    (f : nmhIdx σ s → ZMod 3) (j : Fin 8) :
    nmhExtend σ s hσ f (σ j) = s j * nmhExtend σ s hσ f j := by
  by_cases hfix : σ j = j
  · have hfixσ : σ (σ j) = σ j := (hσ j).trans hfix.symm
    have hsj : s (σ j) = s j := congrArg s hfix
    by_cases hs1 : s j = 1
    · have hs1σ : s (σ j) = 1 := hsj.trans hs1
      rw [hs1, one_mul]
      rw [nmhExtend_fixed_pos hσ f hfixσ hs1σ, nmhExtend_fixed_pos hσ f hfix hs1]
      exact congrArg f (congrArg Sum.inl (Subtype.ext hfix))
    · have hsneg : s j = -1 := by
        rcases hs j with h | h
        · exact absurd h hs1
        · exact h
      have hs1σ : s (σ j) ≠ 1 := by rw [hsj]; exact hs1
      rw [nmhExtend_fixed_neg hσ f hfixσ hs1σ, nmhExtend_fixed_neg hσ f hfix hs1,
        hsneg, mul_zero]
  · rcases lt_or_gt_of_ne hfix with hgt | hlt
    · have hfix' : σ (σ j) ≠ σ j := fun h => hfix (by rw [← h]; exact hσ j)
      have hlt' : σ j < σ (σ j) := by rw [hσ]; exact hgt
      have hsj : s j * s (σ j) = 1 := by rw [mul_comm]; exact hsign j
      rw [nmhExtend_gt hσ f hfix (not_lt.mpr (le_of_lt hgt)),
        nmhExtend_lt hσ f hfix' hlt', ← mul_assoc, hsj, one_mul]
    · have hfix' : σ (σ j) ≠ σ j := fun h => hfix (by rw [← h]; exact hσ j)
      have hnlt' : ¬ σ j < σ (σ j) := by rw [hσ]; exact not_lt.mpr (le_of_lt hlt)
      rw [nmhExtend_lt hσ f hfix hlt, nmhExtend_gt hσ f hfix' hnlt']
      simp only [hσ]

theorem nmhFixCount_spMat {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hσ : ∀ j, σ (σ j) = j) (hsign : ∀ j, s (σ j) * s j = 1) (hs : IsSign s) :
    nmFixCount (spMat σ s) = 3 ^ ((nmhPF σ s).card + (nmhCF σ s).card) := by
  have hcardIdx : Fintype.card (nmhIdx σ s)
      = (nmhPF σ s).card + (nmhCF σ s).card := by
    simp only [nmhIdx, nmhPF, nmhCF]
    rw [Fintype.card_sum, Fintype.card_subtype, Fintype.card_subtype]
  let R : {v : Coords 8 // spMat σ s *ᵥ v = v} → (nmhIdx σ s → ZMod 3) :=
    fun v r => v.1 (nmhIdxVal r)
  have hR : Function.Injective R := by
    intro v w hvw
    apply Subtype.ext
    funext j
    have hv := nmh_fixed_iff.mp v.2
    have hw := nmh_fixed_iff.mp w.2
    by_cases hfix : σ j = j
    · by_cases hs1 : s j = 1
      · exact congrFun hvw (Sum.inl ⟨j, hfix, hs1⟩)
      · have hsneg : s j = -1 := by
          rcases hs j with h | h
          · exact absurd h hs1
          · exact h
        have hvj : v.1 j = 0 := by
          have h := hv j
          rw [hfix, hsneg] at h
          exact nmh_eq_zero_of_neg_eq_self (h.trans (neg_one_mul (v.1 j)))
        have hwj : w.1 j = 0 := by
          have h := hw j
          rw [hfix, hsneg] at h
          exact nmh_eq_zero_of_neg_eq_self (h.trans (neg_one_mul (w.1 j)))
        rw [hvj, hwj]
    · rcases lt_or_gt_of_ne hfix with hgt | hlt
      · have hfix' : σ (σ j) ≠ σ j := fun h => hfix (by rw [← h]; exact hσ j)
        have hlt' : σ j < σ (σ j) := by rw [hσ]; exact hgt
        have hvj := hv (σ j); have hwj := hw (σ j)
        rw [hσ] at hvj hwj
        have h' : v.1 (σ j) = w.1 (σ j) := congrFun hvw (Sum.inr ⟨σ j, hfix', hlt'⟩)
        rw [hvj, hwj, h']
      · exact congrFun hvw (Sum.inr ⟨j, hfix, hlt⟩)
  have hLfix : ∀ f : nmhIdx σ s → ZMod 3, spMat σ s *ᵥ nmhExtend σ s hσ f
      = nmhExtend σ s hσ f := by
    intro f
    rw [nmh_fixed_iff]
    intro j
    exact nmhExtend_rel hs hσ hsign f j
  let L : (nmhIdx σ s → ZMod 3) → {v : Coords 8 // spMat σ s *ᵥ v = v} :=
    fun f => ⟨nmhExtend σ s hσ f, hLfix f⟩
  have hL : Function.Injective L := by
    intro f g hfg
    funext r
    rcases r with h | h
    · rcases h with ⟨j, hfix, hs1⟩
      rw [← nmhExtend_fixed_pos hσ f hfix hs1, ← nmhExtend_fixed_pos hσ g hfix hs1]
      exact congrFun (Subtype.ext_iff.mp hfg) j
    · rcases h with ⟨j, hfix, hlt⟩
      rw [← nmhExtend_lt hσ f hfix hlt, ← nmhExtend_lt hσ g hfix hlt]
      exact congrFun (Subtype.ext_iff.mp hfg) j
  have hle1 : Fintype.card {v : Coords 8 // spMat σ s *ᵥ v = v}
      ≤ Fintype.card (nmhIdx σ s → ZMod 3) := Fintype.card_le_of_injective R hR
  have hle2 : Fintype.card (nmhIdx σ s → ZMod 3)
      ≤ Fintype.card {v : Coords 8 // spMat σ s *ᵥ v = v} :=
    Fintype.card_le_of_injective L hL
  rw [Fintype.card_fun, ZMod.card, hcardIdx] at hle1 hle2
  have hEq : Fintype.card {v : Coords 8 // spMat σ s *ᵥ v = v}
      = 3 ^ ((nmhPF σ s).card + (nmhCF σ s).card) := le_antisymm hle1 hle2
  rw [nmFixCount, Nat.card_eq_fintype_card]
  exact hEq

private theorem nmhProdFixed {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hσ : ∀ j, σ (σ j) = j) (hsign : ∀ j, s (σ j) * s j = 1) :
    (∏ j, s j) = ∏ j ∈ Finset.univ.filter (fun j => σ j = j), s j := by
  rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
    (p := fun j => σ j = j)]
  have hnf : (∏ j ∈ Finset.univ.filter (fun j => ¬ σ j = j), s j) = 1 := by
    apply Finset.prod_involution (g := fun a _ => σ a)
    · intro a _
      rw [mul_comm (s a) (s (σ a)), hsign a]
    · intro a ha _
      exact (Finset.mem_filter.mp ha).2
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      exact (Finset.mem_filter.mp ha).2 (by rw [hσ] at h; exact h.symm)
    · intro a _
      exact hσ a
  rw [hnf, mul_one]

private theorem nmhProdFixedNeg (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3)
    (hs : IsSign s) :
    (∏ j ∈ Finset.univ.filter (fun j => σ j = j), s j)
      = (-1) ^ (nmhAF σ s).card := by
  have hpt : ∀ j ∈ Finset.univ.filter (fun j => σ j = j),
      s j = if s j = -1 then (-1 : ZMod 3) else 1 := by
    intro j _
    rcases hs j with h | h <;> rw [h] <;> decide
  rw [Finset.prod_congr rfl hpt]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  rw [Finset.filter_filter]
  rfl

theorem nmhCardFixed_eq (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3)
    (hs : IsSign s) :
    (Finset.univ.filter (fun j => σ j = j)).card
      = (nmhPF σ s).card + (nmhAF σ s).card := by
  have hset : Finset.univ.filter (fun j => σ j = j) = nmhPF σ s ∪ nmhAF σ s := by
    ext j
    simp only [nmhPF, nmhAF, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hj
      rcases hs j with h | h
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, h⟩
    · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
  have hdisj : Disjoint (nmhPF σ s) (nmhAF σ s) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [nmhPF, nmhAF, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
    rw [hj1.2] at hj2
    exact absurd hj2.2 (by decide)
  rw [hset, Finset.card_union_of_disjoint hdisj]

private theorem nmhEvenFixed (σ : Equiv.Perm (Fin 8)) (hσ2 : σ * σ = 1) :
    Even (Finset.univ.filter (fun j => σ j = j)).card := by
  have hsupp : (Finset.univ.filter (fun j => σ j ≠ j)).card
      = (Equiv.Perm.support σ).card := by
    congr 1
  have h2 : 2 ∣ (Equiv.Perm.support σ).card :=
    Equiv.Perm.two_dvd_card_support (by simpa [pow_two] using hσ2)
  have hsum : (Finset.univ.filter (fun j => σ j = j)).card
      + (Finset.univ.filter (fun j => σ j ≠ j)).card = 8 := by
    rw [Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun j => σ j = j)]
    simp
  rw [hsupp] at hsum
  obtain ⟨k, hk⟩ := h2
  exact ⟨4 - k, by omega⟩

private theorem nmhEvenAF {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hσ : ∀ j, σ (σ j) = j) (hsign : ∀ j, s (σ j) * s j = 1)
    (hpu : ∏ j, s j = 1) : Even (nmhAF σ s).card := by
  have hprod := nmhProdFixed hσ hsign
  have h1 := nmhProdFixedNeg σ s hs
  have hpow : (-1 : ZMod 3) ^ (nmhAF σ s).card = 1 := by
    rw [← h1, ← hprod, hpu]
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hpow

theorem nmhEvenPF {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hσ : ∀ j, σ (σ j) = j) (hσ2 : σ * σ = 1) (hsign : ∀ j, s (σ j) * s j = 1)
    (hpu : ∏ j, s j = 1) : Even (nmhPF σ s).card := by
  have hcard := nmhCardFixed_eq σ s hs
  have hfixed := nmhEvenFixed σ hσ2
  have haf := nmhEvenAF hs hσ hsign hpu
  rw [hcard] at hfixed
  obtain ⟨k, hk⟩ := hfixed
  obtain ⟨l, hl⟩ := haf
  exact ⟨k - l, by omega⟩

end CFSG.StandardType.FrameRoute.FS81

end
