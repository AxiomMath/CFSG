module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainInvolCount
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private theorem nmh_spMat_one_eq_nmSgn (s : Fin 8 → ZMod 3) (hs : IsSign s) :
    spMat (1 : Equiv.Perm (Fin 8)) s
      = nmSgn (Finset.univ.filter fun j => s j = -1) := by
  rw [← nmh_diagonal_eq_spMat, nmSgn]
  congr 1
  funext i
  by_cases h : i ∈ Finset.univ.filter (fun j => s j = -1)
  · rw [if_pos h]; exact (Finset.mem_filter.mp h).2
  · rw [if_neg h]
    rcases hs i with hh | hh
    · exact hh
    · exact absurd (by simpa using hh) h

private theorem nmh_exists_y_diag {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hE : spMat (1 : Equiv.Perm (Fin 8)) s ∉ nmE6)
    (hpf : (nmhPF (1 : Equiv.Perm (Fin 8)) s).card = 2) :
    ∃ y ∈ evenAll0 7, y * y = 1 ∧ y * spMat 1 s = spMat 1 s * y ∧ y.det = -1 ∧
      ∀ v : Coords 8, spMat (1 : Equiv.Perm (Fin 8)) s *ᵥ v = -v → y *ᵥ v = v := by
  classical
  set A : Finset (Fin 8) := Finset.univ.filter (fun j => s j = -1) with hA
  have hMeq : spMat (1 : Equiv.Perm (Fin 8)) s = nmSgn A := nmh_spMat_one_eq_nmSgn s hs
  have hAF : nmhAF (1 : Equiv.Perm (Fin 8)) s = A := by
    ext j; simp [nmhAF, hA, and_comm]
  have hfixall : Finset.univ.filter (fun j => (1 : Equiv.Perm (Fin 8)) j = j)
      = Finset.univ := by ext j; simp
  have hAcard : A.card = 6 := by
    have hcard := nmhCardFixed_eq (1 : Equiv.Perm (Fin 8)) s hs
    rw [hfixall, Finset.card_univ, Fintype.card_fin, hAF] at hcard
    omega
  have h0A : (0 : Fin 8) ∈ A := by
    by_contra h0
    exact hE ⟨A, h0, hAcard, hMeq⟩
  have hs0 : s 0 = -1 := (Finset.mem_filter.mp h0A).2
  have h0pf : 0 ∉ nmhPF (1 : Equiv.Perm (Fin 8)) s := by
    intro h
    have h1 : s 0 = 1 := by simpa [nmhPF] using h
    rw [h1] at hs0
    exact absurd hs0 (by decide)
  obtain ⟨p', q', hpq, hpf_eq⟩ := Finset.card_eq_two.mp hpf
  have hp'mem : p' ∈ nmhPF (1 : Equiv.Perm (Fin 8)) s := by rw [hpf_eq]; simp
  have hq'mem : q' ∈ nmhPF (1 : Equiv.Perm (Fin 8)) s := by rw [hpf_eq]; simp
  have hsp : s p' = 1 := by simpa [nmhPF] using hp'mem
  have hsq : s q' = 1 := by simpa [nmhPF] using hq'mem
  have hp'0 : p' ≠ 0 := fun h => h0pf (h ▸ hp'mem)
  have hq'0 : q' ≠ 0 := fun h => h0pf (h ▸ hq'mem)
  have hp'A : p' ∉ A := by
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsp]; decide
  have hq'A : q' ∉ A := by
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsq]; decide
  have hsj : ∀ m, s (Equiv.swap p' q' m) = s m := by
    intro m
    by_cases hmp : m = p'
    · subst hmp; rw [Equiv.swap_apply_left, hsq, hsp]
    · by_cases hmq : m = q'
      · subst hmq; rw [Equiv.swap_apply_right, hsp, hsq]
      · rw [Equiv.swap_apply_of_ne_of_ne hmp hmq]
  refine ⟨spMat (Equiv.swap p' q') (fun _ => 1), ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Equiv.swap p' q', fun _ => 1, fun _ => Or.inl rfl,
      ⟨Equiv.swap_apply_of_ne_of_ne (Ne.symm hp'0) (Ne.symm hq'0), by simp⟩, rfl⟩
  · exact spMat_mul_self _ _ (Equiv.swap_mul_self p' q') (by intro m; simp)
  · rw [spMat_mul, spMat_mul]
    simp only [Pi.one_apply, mul_one, one_mul]
    congr 1
    funext m
    exact (hsj m).symm
  · rw [nmh_det_spMat, Equiv.Perm.sign_swap hpq]
    decide
  · intro v hv
    funext i
    have hvi : ∀ k, k ∉ A → v k = 0 := by
      intro k hk
      have h := congrFun hv k
      simp only [hMeq, nmSgn_mulVec, if_neg hk] at h
      exact nmh_eq_zero_of_neg_eq_self h
    rw [spMat_mulVec]
    simp only [Pi.one_apply, one_mul, Equiv.symm_swap]
    by_cases hip : i = p'
    · rw [hip]
      rw [Equiv.swap_apply_left, hvi q' hq'A, hvi p' hp'A]
    · by_cases hiq : i = q'
      · rw [hiq]
        rw [Equiv.swap_apply_right, hvi p' hp'A, hvi q' hq'A]
      · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]

private theorem nmh_neg_mul_neg {s₀ x : ZMod 3} (h : s₀ = 1 ∨ s₀ = -1) :
    -s₀ * -(s₀ * x) = x := by
  rcases h with h | h
  · rw [h, one_mul]
    rw [show (-1 : ZMod 3) * -x = -(1 * -x) from neg_mul 1 (-x), one_mul]
    exact neg_neg x
  · rw [h]
    rw [show (-(-1) : ZMod 3) = 1 from neg_neg 1, one_mul]
    rw [show (-1 : ZMod 3) * x = -(1 * x) from neg_mul 1 x, one_mul]
    exact neg_neg x

private theorem nmh_exists_y_cycle {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hs : IsSign s) (hσ0 : σ 0 = 0) (hσ : ∀ j, σ (σ j) = j)
    (hsign : ∀ j, s (σ j) * s j = 1) (hcf : (nmhCF σ s).card = 2) :
    ∃ y ∈ evenAll0 7, y * y = 1 ∧ y * spMat σ s = spMat σ s * y ∧ y.det = -1 ∧
      ∀ v : Coords 8, spMat σ s *ᵥ v = -v → y *ᵥ v = v := by
  classical
  obtain ⟨a, b, hab, hcf_eq⟩ := Finset.card_eq_two.mp hcf
  have hamem : a ∈ nmhCF σ s := by rw [hcf_eq]; simp
  have hlt : a < σ a := (Finset.mem_filter.mp hamem).2.2
  have hne : σ a ≠ a := (Finset.mem_filter.mp hamem).2.1
  have ha0 : a ≠ 0 := by
    intro h; subst h; exact hne hσ0
  have hsa0 : σ a ≠ 0 := by
    intro h
    have : a = 0 := by rw [← hσ a, h, hσ0]
    exact ha0 this
  have hsa : s (σ a) = s a := by
    rcases hs a with h1 | h1 <;> rcases hs (σ a) with h2 | h2
    · rw [h2, h1]
    · exact absurd (hsign a) (by rw [h1, h2]; decide)
    · exact absurd (hsign a) (by rw [h1, h2]; decide)
    · rw [h2, h1]
  have hpair : ∀ m, (Equiv.swap a (σ a) m = a ∨ Equiv.swap a (σ a) m = σ a) ↔
      (m = a ∨ m = σ a) := by
    intro m
    by_cases hma : m = a
    · subst hma; simp [Equiv.swap_apply_left]
    · by_cases hms : m = σ a
      · subst hms; simp [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hma hms]
  let u : Fin 8 → ZMod 3 := fun m => if m = a ∨ m = σ a then -s a else 1
  have hsu : IsSign u := by
    intro m
    dsimp only [u]
    split_ifs
    · rcases hs a with h | h <;> rw [h] <;> decide
    · exact Or.inl rfl
  have hprod_u : (∏ m, u m) = 1 := by
    have hset : Finset.univ.filter (fun m : Fin 8 => m = a ∨ m = σ a) = {a, σ a} := by
      ext m; simp [eq_comm, or_comm]
    dsimp only [u]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [hset, Finset.card_pair_eq_two_iff.mpr (Ne.symm hne)]
    rcases hs a with h | h <;> rw [h] <;> decide
  have hu_self : ∀ m, u (Equiv.swap a (σ a) m) * u m = 1 := by
    intro m
    by_cases hm : m = a ∨ m = σ a
    · have hm' := (hpair m).mpr hm
      dsimp only [u]
      rw [if_pos hm', if_pos hm]
      rcases hs a with h | h <;> rw [h] <;> decide
    · have hm' : ¬ (Equiv.swap a (σ a) m = a ∨ Equiv.swap a (σ a) m = σ a) :=
        fun h => hm ((hpair m).mp h)
      dsimp only [u]
      rw [if_neg hm', if_neg hm, one_mul]
  have hτσ : Equiv.swap a (σ a) * σ = σ * Equiv.swap a (σ a) := by
    ext m
    by_cases hm : m = a ∨ m = σ a
    · rcases hm with h | h
      · subst h; simp [Equiv.Perm.mul_apply, hσ]
      · subst h; simp [Equiv.Perm.mul_apply, hσ]
    · have hmτ : Equiv.swap a (σ a) m = m := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => hm (Or.inl h)
        · exact fun h => hm (Or.inr h)
      have hσm : ¬ (σ m = a ∨ σ m = σ a) := by
        rintro (h | h)
        · exact hm (Or.inr (by rw [← hσ m, h]))
        · exact hm (Or.inl (by rw [← hσ m, h, hσ a]))
      have hσmτ : Equiv.swap a (σ a) (σ m) = σ m := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => hσm (Or.inl h)
        · exact fun h => hσm (Or.inr h)
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hmτ, hσmτ]
  have huσ : ∀ m, u (σ m) * s m = s (Equiv.swap a (σ a) m) * u m := by
    intro m
    by_cases hm : m = a ∨ m = σ a
    · rcases hm with h | h
      · rw [h]
        rw [Equiv.swap_apply_left]
        dsimp only [u]
        rw [if_pos (Or.inr rfl), if_pos (Or.inl rfl), hsa]
        ring
      · rw [h]
        rw [hσ a, Equiv.swap_apply_right]
        dsimp only [u]
        rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl), hsa]
        ring
    · have hσm : ¬ (σ m = a ∨ σ m = σ a) := by
        rintro (h | h)
        · exact hm (Or.inr (by rw [← hσ m, h]))
        · exact hm (Or.inl (by rw [← hσ m, h, hσ a]))
      have hmτ : Equiv.swap a (σ a) m = m := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => hm (Or.inl h)
        · exact fun h => hm (Or.inr h)
      dsimp only [u]
      rw [if_neg hσm, if_neg hm, one_mul, mul_one, hmτ]
  refine ⟨spMat (Equiv.swap a (σ a)) u, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Equiv.swap a (σ a), u, hsu,
      ⟨Equiv.swap_apply_of_ne_of_ne (Ne.symm ha0) (Ne.symm hsa0), hprod_u⟩, rfl⟩
  · exact spMat_mul_self _ _ (Equiv.swap_mul_self a (σ a)) hu_self
  · rw [spMat_mul, spMat_mul, hτσ]
    congr 1
    funext m
    exact huσ m
  · rw [nmh_det_spMat, Equiv.Perm.sign_swap (Ne.symm hne), hprod_u]
    decide
  · intro v hv
    funext m
    have hvm : ∀ k, v (σ k) = -(s k * v k) := by
      intro k
      have h := congrFun hv (σ k)
      rw [spMat_mulVec] at h
      simp only [Equiv.symm_apply_apply, Pi.neg_apply] at h
      rw [h]
      exact (neg_neg (v (σ k))).symm
    rw [spMat_mulVec, Equiv.symm_swap]
    dsimp only [u]
    by_cases hm : m = a ∨ m = σ a
    · rcases hm with h | h
      · rw [h]
        rw [Equiv.swap_apply_left, if_pos (Or.inr rfl)]
        rw [hvm a]
        exact nmh_neg_mul_neg (hs a)
      · rw [h]
        rw [Equiv.swap_apply_right, if_pos (Or.inl rfl)]
        rw [hvm a]
        exact neg_mul (s a) (v a)
    · have hm' : ¬ (Equiv.swap a (σ a) m = a ∨ Equiv.swap a (σ a) m = σ a) :=
        fun h => hm ((hpair m).mp h)
      have hmτ : Equiv.swap a (σ a) m = m := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => hm (Or.inl h)
        · exact fun h => hm (Or.inr h)
      rw [hmτ, if_neg hm, one_mul]

theorem nm_klein {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ evenAll0 7) (h2 : M * M = 1)
    (h9 : nmFixCount M = 9) (hE : M ∉ nmE6) :
    ∃ y ∈ evenAll0 7, y * y = 1 ∧ y * M = M * y ∧ y.det = -1 ∧
      ∀ v : Coords 8, M *ᵥ v = -v → y *ᵥ v = v := by
  obtain ⟨σ, s, hs, ⟨hσ0, hpu⟩, rfl⟩ := hM
  obtain ⟨hσapp, hsign⟩ := nmh_involution_data hs h2
  have hσ2 : σ * σ = 1 := by
    apply Equiv.ext; intro j; exact hσapp j
  have hcount := nmhFixCount_spMat hσapp hsign hs
  have hpc : (nmhPF σ s).card + (nmhCF σ s).card = 2 := by
    have h3 : 3 ^ ((nmhPF σ s).card + (nmhCF σ s).card) = 3 ^ 2 := by
      rw [← hcount, h9]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  have hevenPF := nmhEvenPF hs hσapp hσ2 hsign hpu
  have hp02 : (nmhPF σ s).card = 0 ∨ (nmhPF σ s).card = 2 := by
    obtain ⟨k, hk⟩ := hevenPF
    omega
  rcases hp02 with hp0 | hp2
  · have hcf : (nmhCF σ s).card = 2 := by omega
    exact nmh_exists_y_cycle hs hσ0 hσapp hsign hcf
  · have hc0 : (nmhCF σ s).card = 0 := by omega
    have hσ1 : σ = 1 := by
      ext j
      by_contra hne
      have hne' : σ j ≠ j := fun h => hne (by rw [h, Equiv.Perm.one_apply])
      rcases lt_or_gt_of_ne hne' with hgt | hlt
      · have hfix' : σ (σ j) ≠ σ j := fun h => hne' (h.symm.trans (hσapp j))
        have hlt' : σ j < σ (σ j) := by rw [hσapp]; exact hgt
        have hmem : σ j ∈ nmhCF σ s := by
          simp only [nmhCF, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hfix', hlt'⟩
        have := Finset.card_pos.mpr ⟨σ j, hmem⟩
        omega
      · have hmem : j ∈ nmhCF σ s := by
          simp only [nmhCF, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hne', hlt⟩
        have := Finset.card_pos.mpr ⟨j, hmem⟩
        omega
    subst hσ1
    exact nmh_exists_y_diag hs hE hp2

end CFSG.StandardType.FrameRoute.FS81

end
