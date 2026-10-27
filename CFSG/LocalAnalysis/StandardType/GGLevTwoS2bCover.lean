module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bPhi
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bAux

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem levTwoS2b_rRefl_apply (n : ℕ) (_hn : 1 ≤ n) {β v : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanB n) β) {k₀ : ℤ}
    (hk : (k₀ : ℚ) * form (isFiniteType_cartanB n) (toRat β) (toRat β) =
      2 * form (isFiniteType_cartanB n) (toRat β) (toRat v)) :
    weylAction (isFiniteType_cartanB n) (rRefl (isFiniteType_cartanB n) β) v = v - k₀ • β := by
  obtain ⟨k, hk', hact⟩ := weylAction_rRefl (isFiniteType_cartanB n) hβ v
  have hβ0 : β ≠ 0 := by
    obtain ⟨w, i, rfl⟩ := hβ
    exact weylAction_single_ne_zero (isFiniteType_cartanB n) w i
  have hf : form (isFiniteType_cartanB n) (toRat β) (toRat β) ≠ 0 :=
    (form_pos (isFiniteType_cartanB n) (fun h => hβ0 (toRat_injective (by simpa using h)))).ne'
  have hk_eq : (k : ℚ) = k₀ := by
    have hzero : ((k : ℚ) - k₀) * form (isFiniteType_cartanB n) (toRat β) (toRat β) = 0 := by
      linarith
    rcases mul_eq_zero.mp hzero with h | h
    · linarith
    · exact absurd h hf
  rw [show k = k₀ from Int.cast_injective hk_eq] at hact
  exact hact

theorem levTwoS2b_dot_add_single (n : ℕ) {a b : Fin n} (hab : a ≠ b) (s t : ℤ) :
    ∑ k : Fin n, ((Pi.single a s + Pi.single b t : Fin n → ℤ) k : ℚ) *
        ((Pi.single a s : Fin n → ℤ) k : ℚ) = (s : ℚ) * (s : ℚ) := by
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [levTwoS2b_dot_single_self n a s, levTwoS2b_dot_single_ne n (Ne.symm hab) t s]
  ring

theorem levTwoS2b_rRefl_pair (n : ℕ) (hn : 1 ≤ n) {a b : Fin n} (hab : a ≠ b) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t)))
        (levTwoS2b_ofCoord n (Pi.single a s)) =
      levTwoS2b_ofCoord n (Pi.single b (-t)) := by
  have hβ : IsRt (isFiniteType_cartanB n)
      (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t)) :=
    levTwoS2b_isRt_ofCoord_long n hab hs ht
  have hlong : levTwoS2b_isLong n (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t)) :=
    levTwoS2b_isLong_ofCoord_long n hab hs ht
  have hform : (1 : ℚ) * form (isFiniteType_cartanB n)
        (toRat (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t)))
        (toRat (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t))) =
      2 * form (isFiniteType_cartanB n)
        (toRat (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t)))
        (toRat (levTwoS2b_ofCoord n (Pi.single a s))) := by
    rw [one_mul, levTwoS2b_form_self_long n hn hlong, levTwoS2b_form_coord_kappa n hn,
      levTwoS2b_coord_ofCoord, levTwoS2b_coord_ofCoord, levTwoS2b_dot_add_single n hab s t]
    have hss : (s : ℚ) * (s : ℚ) = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [hss]
    ring
  rw [levTwoS2b_rRefl_apply n hn hβ hform, Nat.cast_one, one_zsmul, ← levTwoS2b_ofCoord_sub]
  congr 1
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  by_cases hka : k = a
  · subst hka
    simp [hab]
  · by_cases hkb : k = b
    · subst hkb
      simp [hka]
    · simp [hka, hkb]

theorem levTwoS2b_rRefl_pair' (n : ℕ) (hn : 1 ≤ n) {a c : Fin n} (hac : a ≠ c) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single a s + Pi.single c t)))
        (levTwoS2b_ofCoord n (Pi.single c t)) =
      levTwoS2b_ofCoord n (Pi.single a (-s)) := by
  have hβ : IsRt (isFiniteType_cartanB n)
      (levTwoS2b_ofCoord n (Pi.single a s + Pi.single c t)) :=
    levTwoS2b_isRt_ofCoord_long n hac hs ht
  have hlong : levTwoS2b_isLong n (levTwoS2b_ofCoord n (Pi.single a s + Pi.single c t)) :=
    levTwoS2b_isLong_ofCoord_long n hac hs ht
  have hform : (1 : ℚ) * form (isFiniteType_cartanB n)
        (toRat (levTwoS2b_ofCoord n (Pi.single a s + Pi.single c t)))
        (toRat (levTwoS2b_ofCoord n (Pi.single a s + Pi.single c t))) =
      2 * form (isFiniteType_cartanB n)
        (toRat (levTwoS2b_ofCoord n (Pi.single a s + Pi.single c t)))
        (toRat (levTwoS2b_ofCoord n (Pi.single c t))) := by
    rw [one_mul, levTwoS2b_form_self_long n hn hlong, levTwoS2b_form_coord_kappa n hn,
      levTwoS2b_coord_ofCoord, levTwoS2b_coord_ofCoord]
    rw [show (Pi.single a s + Pi.single c t : Fin n → ℤ) = Pi.single c t + Pi.single a s from
      by abel]
    rw [levTwoS2b_dot_add_single n (Ne.symm hac) t s]
    have htt : (t : ℚ) * (t : ℚ) = 1 := by rcases ht with rfl | rfl <;> norm_num
    rw [htt]
    ring
  rw [levTwoS2b_rRefl_apply n hn hβ hform, Nat.cast_one, one_zsmul, ← levTwoS2b_ofCoord_sub]
  congr 1
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  by_cases hkc : k = c
  · subst hkc
    by_cases hka : k = a <;> simp [hka]
  · by_cases hka : k = a
    · subst hka
      simp [hkc]
    · simp [hka, hkc]

theorem levTwoS2b_rRefl_sub (n : ℕ) (hn : 1 ≤ n) {a b : Fin n} (hab : a ≠ b) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b s)))
        (levTwoS2b_ofCoord n (Pi.single a s)) =
      levTwoS2b_ofCoord n (Pi.single b s) := by
  have ht : (-s : ℤ) = 1 ∨ (-s : ℤ) = -1 := by rcases hs with h | h <;> simp [h]
  have h := levTwoS2b_rRefl_pair n hn hab hs ht
  rw [neg_neg] at h
  convert h using 2
  rw [sub_eq_add_neg, Pi.single_neg]

theorem levTwoS2b_rRefl_add (n : ℕ) (hn : 1 ≤ n) {a b : Fin n} (hab : a ≠ b) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b s)))
        (levTwoS2b_ofCoord n (Pi.single a s)) =
      levTwoS2b_ofCoord n (Pi.single b (-s)) :=
  levTwoS2b_rRefl_pair n hn hab hs hs

theorem levTwoS2b_short_mem_cl (n : ℕ) (hn : 2 ≤ n) {s t : Fin n → ℤ}
    (hss : levTwoS2b_isShort n s) (hst : levTwoS2b_isShort n t) :
    Cl (isFiniteType_cartanB n) (levTwoS2b_allLong n ∪ {s}) t := by
  classical
  have : Nontrivial (Fin n) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega⟩
  obtain ⟨a, σ, hσ, hcs⟩ := hss
  obtain ⟨b, τ, hτ, hct⟩ := hst
  set S : Set (Fin n → ℤ) := levTwoS2b_allLong n ∪ {s} with hSdef
  have hsS : s ∈ S := Or.inr (by simp)
  have hsbase : Cl (isFiniteType_cartanB n) S s := Cl.base hsS
  have hs_eq : s = levTwoS2b_ofCoord n (Pi.single a σ) := by
    apply levTwoS2b_coord_injective n
    rw [levTwoS2b_coord_ofCoord, hcs]
  have ht_eq : t = levTwoS2b_ofCoord n (Pi.single b τ) := by
    apply levTwoS2b_coord_injective n
    rw [levTwoS2b_coord_ofCoord, hct]
  subst hs_eq
  subst ht_eq
  rcases eq_or_ne a b with rfl | hab
  ·
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
    · exact hsbase
    ·
      obtain ⟨c, hc⟩ := exists_ne a
      have h1 : levTwoS2b_ofCoord n (Pi.single a (1 : ℤ) + Pi.single c 1) ∈
          levTwoS2b_allLong n :=
        ⟨levTwoS2b_isRt_ofCoord_long n (Ne.symm hc) (Or.inl rfl) (Or.inl rfl),
          levTwoS2b_isLong_ofCoord_long n (Ne.symm hc) (Or.inl rfl) (Or.inl rfl)⟩
      have h2 : levTwoS2b_ofCoord n (Pi.single a (1 : ℤ) + Pi.single c (-1)) ∈
          levTwoS2b_allLong n :=
        ⟨levTwoS2b_isRt_ofCoord_long n (Ne.symm hc) (Or.inl rfl) (Or.inr rfl),
          levTwoS2b_isLong_ofCoord_long n (Ne.symm hc) (Or.inl rfl) (Or.inr rfl)⟩
      have step1 : Cl (isFiniteType_cartanB n) S
          (levTwoS2b_ofCoord n (Pi.single c (-1))) := by
        have hcl := Cl.refl (Cl.base (Or.inl h1)) hsbase
        rwa [levTwoS2b_rRefl_pair n (by omega) (Ne.symm hc) (Or.inl rfl) (Or.inl rfl)] at hcl
      have step2 : Cl (isFiniteType_cartanB n) S
          (levTwoS2b_ofCoord n (Pi.single a (-1))) := by
        have hcl := Cl.refl (Cl.base (Or.inl h2)) step1
        rwa [levTwoS2b_rRefl_pair' n (by omega) (Ne.symm hc) (Or.inl rfl) (Or.inr rfl)] at hcl
      simpa using step2
    ·
      obtain ⟨c, hc⟩ := exists_ne a
      have h1 : levTwoS2b_ofCoord n (Pi.single a (-1 : ℤ) + Pi.single c 1) ∈
          levTwoS2b_allLong n :=
        ⟨levTwoS2b_isRt_ofCoord_long n (Ne.symm hc) (Or.inr rfl) (Or.inl rfl),
          levTwoS2b_isLong_ofCoord_long n (Ne.symm hc) (Or.inr rfl) (Or.inl rfl)⟩
      have h2 : levTwoS2b_ofCoord n (Pi.single a (-1 : ℤ) + Pi.single c (-1)) ∈
          levTwoS2b_allLong n :=
        ⟨levTwoS2b_isRt_ofCoord_long n (Ne.symm hc) (Or.inr rfl) (Or.inr rfl),
          levTwoS2b_isLong_ofCoord_long n (Ne.symm hc) (Or.inr rfl) (Or.inr rfl)⟩
      have step1 : Cl (isFiniteType_cartanB n) S
          (levTwoS2b_ofCoord n (Pi.single c (-1))) := by
        have hcl := Cl.refl (Cl.base (Or.inl h1)) hsbase
        rwa [levTwoS2b_rRefl_pair n (by omega) (Ne.symm hc) (Or.inr rfl) (Or.inl rfl)] at hcl
      have step2 : Cl (isFiniteType_cartanB n) S
          (levTwoS2b_ofCoord n (Pi.single a (1))) := by
        have hcl := Cl.refl (Cl.base (Or.inl h2)) step1
        rwa [levTwoS2b_rRefl_pair' n (by omega) (Ne.symm hc) (Or.inr rfl) (Or.inr rfl)] at hcl
      simpa using step2
    · exact hsbase
  ·
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
    ·
      have h1 : levTwoS2b_ofCoord n (Pi.single a (1 : ℤ) - Pi.single b 1) ∈
          levTwoS2b_allLong n :=
        ⟨levTwoS2b_isRt_ofCoord_sub n hab, levTwoS2b_isLong_ofCoord_sub n hab⟩
      have hcl := Cl.refl (Cl.base (Or.inl h1)) hsbase
      rwa [levTwoS2b_rRefl_sub n (by omega) hab (Or.inl rfl)] at hcl
    ·
      have h1 : levTwoS2b_ofCoord n (Pi.single a (1 : ℤ) + Pi.single b 1) ∈
          levTwoS2b_allLong n :=
        ⟨levTwoS2b_isRt_ofCoord_long n hab (Or.inl rfl) (Or.inl rfl),
          levTwoS2b_isLong_ofCoord_long n hab (Or.inl rfl) (Or.inl rfl)⟩
      have hcl := Cl.refl (Cl.base (Or.inl h1)) hsbase
      rwa [levTwoS2b_rRefl_add n (by omega) hab (Or.inl rfl)] at hcl
    ·
      have h1 : levTwoS2b_ofCoord n (Pi.single a (-1 : ℤ) + Pi.single b (-1)) ∈
          levTwoS2b_allLong n :=
        ⟨levTwoS2b_isRt_ofCoord_long n hab (Or.inr rfl) (Or.inr rfl),
          levTwoS2b_isLong_ofCoord_long n hab (Or.inr rfl) (Or.inr rfl)⟩
      have hcl := Cl.refl (Cl.base (Or.inl h1)) hsbase
      rwa [levTwoS2b_rRefl_add n (by omega) hab (Or.inr rfl)] at hcl
    ·
      have h1 : levTwoS2b_ofCoord n (Pi.single a (-1 : ℤ) - Pi.single b (-1)) ∈
          levTwoS2b_allLong n :=
        ⟨levTwoS2b_isRt_ofCoord_sub' n hab (Or.inr rfl),
          levTwoS2b_isLong_ofCoord_sub' n hab (Or.inr rfl)⟩
      have hcl := Cl.refl (Cl.base (Or.inl h1)) hsbase
      rwa [levTwoS2b_rRefl_sub n (by omega) hab (Or.inr rfl)] at hcl

theorem levTwoS2b_tcRoot_allLong (n : ℕ) (hn : 2 ≤ n) :
    TCRoot (isFiniteType_cartanB n) (levTwoS2b_allLong n) := by
  intro S hS
  classical
  by_cases hshort : ∃ s ∈ S, levTwoS2b_isShort n s
  · obtain ⟨s, hsS, hss⟩ := hshort
    refine ⟨{s}, ?_, by simp, ?_⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_singleton] at hx
      subst hx
      exact hsS
    · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_singleton] at hx
        subst hx
        exact hsS
      · intro x hxS
        rcases levTwoS2b_isShort_or_isLong n (hS x hxS) with hxs | hxl
        · simpa [Finset.coe_singleton] using levTwoS2b_short_mem_cl n hn hss hxs
        · exact Cl.base (Or.inl ⟨hS x hxS, hxl⟩)
  · refine ⟨∅, by simp, by simp, ?_⟩
    apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
    · simp
    · intro x hxS
      rcases levTwoS2b_isShort_or_isLong n (hS x hxS) with hxs | hxl
      · exact absurd ⟨x, hxS, hxs⟩ hshort
      · exact Cl.base (Or.inl ⟨hS x hxS, hxl⟩)

end CFSG.StandardType.LevTwo
