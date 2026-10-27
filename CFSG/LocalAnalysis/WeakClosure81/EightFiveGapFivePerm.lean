module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFivePermA
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFivePermB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm Subgroup

theorem gap5Perm_exists_commuting_conj {n : ℕ} (hn : 4 ≤ n) {τ : Perm (Fin n)} (hτ : τ * τ = 1)
    (hs : Perm.sign τ = -1) :
    ∃ c ∈ alternatingGroup (Fin n), c * τ * c⁻¹ ≠ τ ∧
      τ * (c * τ * c⁻¹) = (c * τ * c⁻¹) * τ := by
  obtain ⟨j, hoddj, hj⟩ := w85g_exists_odd_card_support hτ hs
  rcases eq_or_ne j 1 with hj1 | hjne
  · have hcard2 : τ.support.card = 2 := by rw [hj, hj1, mul_one]
    obtain ⟨a, b, hab, rfl⟩ := Equiv.Perm.card_support_eq_two.mp hcard2
    exact w85g_exists_commuting_conj_swap hab (by simpa using hn)
  · have h4 : 4 ≤ τ.support.card := by
      obtain ⟨k, hk⟩ := hoddj
      rw [hj]
      omega
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hta, htb, htc, htd⟩ :=
      w85g_exists_two_pairs hτ h4
    exact w85g_exists_commuting_conj_four hτ hs hab hac had hbc hbd hcd hta htb htc htd

theorem gap5Perm_exists_conj_orderOf_eq_six {n : ℕ} (hn : 7 ≤ n) {τ : Perm (Fin n)}
    (hτ : τ * τ = 1) (hs : Perm.sign τ = -1) (hns : ∀ i j : Fin n, i ≠ j → τ ≠ swap i j) :
    ∃ σ : Perm (Fin n), orderOf (τ * (σ * τ * σ⁻¹)) = 6 := by
  obtain ⟨j, hoddj, hj⟩ := w85g_exists_odd_card_support hτ hs
  have hj3 : 3 ≤ j := by
    by_contra h
    have hj1 : j = 1 := by
      obtain ⟨k, hk⟩ := hoddj
      omega
    have hcard2 : τ.support.card = 2 := by rw [hj, hj1, mul_one]
    obtain ⟨a, b, hab, rfl⟩ := Equiv.Perm.card_support_eq_two.mp hcard2
    exact hns a b hab rfl
  by_cases hfix : ∃ x, τ x = x
  ·
    obtain ⟨x, hx⟩ := hfix
    have h6 : 6 ≤ τ.support.card := by rw [hj]; omega
    obtain ⟨p, hτp⟩ := w85g_exists_fixed_embedding hτ h6 hx
    exact w85g_orderOf_six_fixed hτ p.injective hτp
  ·
    have hsupp : τ.support = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro x
      rw [Equiv.Perm.mem_support]
      intro hx
      exact hfix ⟨x, hx⟩
    have hcard : τ.support.card = n := by
      rw [hsupp, Finset.card_univ, Fintype.card_fin]
    have h10 : 10 ≤ τ.support.card := by
      obtain ⟨k, hk⟩ := hoddj
      omega
    obtain ⟨p, hτp⟩ := w85g_exists_free_embedding hτ h10
    exact w85g_orderOf_six_free hτ p.injective hτp

theorem gap5Perm_not_odd_index_four_five {n : ℕ} (hn : n = 4 ∨ n = 5) {τ : Perm (Fin n)}
    (hτ : τ * τ = 1) (hs : Perm.sign τ = -1) :
    ¬ Odd (Subgroup.centralizer ({τ} : Set (Perm (Fin n)))).index := by
  rcases hn with rfl | rfl
  · have htransposition : τ.IsSwap :=
      w85g_isSwap_of_sign_neg_one_card_le_five (by norm_num) hτ hs
    intro hodd
    have hcard : Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin 4)))) = 4 := by
      rw [w85g_nat_card_centralizer_isSwap htransposition]
      decide
    have hperm : Nat.card (Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_fin]
      decide
    have hci := Subgroup.card_mul_index (Subgroup.centralizer ({τ} : Set (Perm (Fin 4))))
    rw [hcard, hperm] at hci
    obtain ⟨k, hk⟩ := hodd
    omega
  · have htransposition : τ.IsSwap :=
      w85g_isSwap_of_sign_neg_one_card_le_five (by norm_num) hτ hs
    intro hodd
    have hcard : Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin 5)))) = 12 := by
      rw [w85g_nat_card_centralizer_isSwap htransposition]
      decide
    have hperm : Nat.card (Perm (Fin 5)) = 120 := by
      rw [Nat.card_perm, Nat.card_fin]
      decide
    have hci := Subgroup.card_mul_index (Subgroup.centralizer ({τ} : Set (Perm (Fin 5))))
    rw [hcard, hperm] at hci
    obtain ⟨k, hk⟩ := hodd
    omega

theorem gap5Perm_card_le_six_of_klein_dichotomy {α : Type} [Fintype α] [DecidableEq α]
    {x y : Perm α} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hne : x ≠ y)
    (hdich : ∀ i j : α, i ≠ j →
      (x * swap i j = swap i j * x ∧ y * swap i j = swap i j * y) ∨
      (x * swap i j ≠ swap i j * x ∧ y * swap i j ≠ swap i j * y ∧
        x * y * swap i j ≠ swap i j * (x * y))) :
    Fintype.card α ≤ 6 := by
  classical
  have hstep1 : ∀ b : α, x b = b ∨ y b = b ∨ x (y b) = b := by
    intro b
    by_contra h
    rw [not_or, not_or] at h
    obtain ⟨hxb, hyb, hxyb⟩ := h
    have hbne : b ≠ x b := fun hh => hxb hh.symm
    have hxx : x (x b) = b := by
      have := congrArg (fun z : Perm α => z b) hx
      simpa [Equiv.Perm.mul_apply] using this
    have hcomm : x * swap b (x b) = swap b (x b) * x :=
      (w85g_mul_swap_commute_iff hbne).mpr (Or.inr ⟨rfl, hxx⟩)
    rcases hdich b (x b) hbne with ⟨_, hys⟩ | ⟨hxs, _⟩
    · rcases (w85g_mul_swap_commute_iff hbne).mp hys with ⟨hy1, _⟩ | ⟨hy1, _⟩
      · exact hyb hy1
      · exact hxyb (by rw [hy1, hxx])
    · exact hxs hcomm
  have hstep2 : ¬ ∃ a, x a = a ∧ y a = a := by
    rintro ⟨a, hxa, hya⟩
    have hxne1 : x ≠ 1 := hx1
    obtain ⟨b, hxb⟩ : ∃ b, x b ≠ b := by
      by_contra h
      push Not at h
      exact hxne1 (Equiv.ext h)
    have hab : a ≠ b := fun hh => hxb (by rw [← hh]; exact hxa)
    have hcontr : x * swap a b = swap a b * x := by
      rcases hstep1 b with h1 | h1 | h1
      · exact absurd h1 hxb
      · have hcomm : y * swap a b = swap a b * y :=
          (w85g_mul_swap_commute_iff hab).mpr (Or.inl ⟨hya, h1⟩)
        rcases hdich a b hab with ⟨hxs, _⟩ | ⟨_, hys, _⟩
        · exact hxs
        · exact absurd hcomm hys
      · have haz : (x * y) a = a := by simp [Equiv.Perm.mul_apply, hya, hxa]
        have hbz : (x * y) b = b := by simp [Equiv.Perm.mul_apply, h1]
        have hcomm : (x * y) * swap a b = swap a b * (x * y) :=
          (w85g_mul_swap_commute_iff hab).mpr (Or.inl ⟨haz, hbz⟩)
        rcases hdich a b hab with ⟨hxs, _⟩ | ⟨_, _, hxys⟩
        · exact hxs
        · exact absurd hcomm hxys
    rcases (w85g_mul_swap_commute_iff hab).mp hcontr with ⟨hxa', hxb'⟩ | ⟨hxa', hxb'⟩
    · exact hxb hxb'
    · exact hab (by rw [← hxa', hxa])
  have hstep3x : ∀ b b', x b = b → x b' = b' → b ≠ b' → b' = y b := by
    intro b b' hb hb' hne
    have hcomm : x * swap b b' = swap b b' * x :=
      (w85g_mul_swap_commute_iff hne).mpr (Or.inl ⟨hb, hb'⟩)
    rcases hdich b b' hne with ⟨_, hys⟩ | ⟨hxs, _⟩
    · rcases (w85g_mul_swap_commute_iff hne).mp hys with ⟨hy1, _⟩ | ⟨hy1, _⟩
      · exact absurd ⟨b, hb, hy1⟩ hstep2
      · exact hy1.symm
    · exact absurd hcomm hxs
  have hstep3y : ∀ b b', y b = b → y b' = b' → b ≠ b' → b' = x b := by
    intro b b' hb hb' hne
    have hcomm : y * swap b b' = swap b b' * y :=
      (w85g_mul_swap_commute_iff hne).mpr (Or.inl ⟨hb, hb'⟩)
    rcases hdich b b' hne with ⟨hxs, _⟩ | ⟨_, hys, _⟩
    · rcases (w85g_mul_swap_commute_iff hne).mp hxs with ⟨hx1, _⟩ | ⟨hx1, _⟩
      · exact absurd ⟨b, hx1, hb⟩ hstep2
      · exact hx1.symm
    · exact absurd hcomm hys
  have hstep3xy : ∀ b b', x (y b) = b → x (y b') = b' → b ≠ b' → b' = x b := by
    intro b b' hb hb' hne
    have hcomm : (x * y) * swap b b' = swap b b' * (x * y) :=
      (w85g_mul_swap_commute_iff hne).mpr
        (Or.inl ⟨by simpa [Equiv.Perm.mul_apply] using hb,
          by simpa [Equiv.Perm.mul_apply] using hb'⟩)
    rcases hdich b b' hne with ⟨hxs, _⟩ | ⟨_, _, hxys⟩
    · rcases (w85g_mul_swap_commute_iff hne).mp hxs with ⟨hxb, _⟩ | ⟨hxb, _⟩
      · have hyb : y b = b := by
          have : x (y b) = x b := by rw [hb, hxb]
          exact x.injective this
        exact absurd ⟨b, hxb, hyb⟩ hstep2
      · exact hxb.symm
    · exact absurd hcomm hxys
  have hFx : (Finset.univ.filter (fun b => x b = b)).card ≤ 2 := by
    by_cases hne : (Finset.univ.filter (fun b => x b = b)).Nonempty
    · obtain ⟨b, hb⟩ := hne
      have hb' : x b = b := by simpa using hb
      have hsub : Finset.univ.filter (fun b => x b = b) ⊆ {b, y b} := by
        intro b' hb''
        have hxb' : x b' = b' := by simpa using hb''
        by_cases hbb : b' = b
        · simp [hbb]
        · have hne' : b ≠ b' := fun hh => hbb hh.symm
          have := hstep3x b b' hb' hxb' hne'
          simp [this]
      calc (Finset.univ.filter (fun b => x b = b)).card ≤ ({b, y b} : Finset α).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  have hFy : (Finset.univ.filter (fun b => y b = b)).card ≤ 2 := by
    by_cases hne : (Finset.univ.filter (fun b => y b = b)).Nonempty
    · obtain ⟨b, hb⟩ := hne
      have hb' : y b = b := by simpa using hb
      have hsub : Finset.univ.filter (fun b => y b = b) ⊆ {b, x b} := by
        intro b' hb''
        have hyb' : y b' = b' := by simpa using hb''
        by_cases hbb : b' = b
        · simp [hbb]
        · have hne' : b ≠ b' := fun hh => hbb hh.symm
          have := hstep3y b b' hb' hyb' hne'
          simp [this]
      calc (Finset.univ.filter (fun b => y b = b)).card ≤ ({b, x b} : Finset α).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  have hFxy : (Finset.univ.filter (fun b => x (y b) = b)).card ≤ 2 := by
    by_cases hne : (Finset.univ.filter (fun b => x (y b) = b)).Nonempty
    · obtain ⟨b, hb⟩ := hne
      have hb' : x (y b) = b := by simpa using hb
      have hsub : Finset.univ.filter (fun b => x (y b) = b) ⊆ {b, x b} := by
        intro b' hb''
        have hxb' : x (y b') = b' := by simpa using hb''
        by_cases hbb : b' = b
        · simp [hbb]
        · have hne' : b ≠ b' := fun hh => hbb hh.symm
          have := hstep3xy b b' hb' hxb' hne'
          simp [this]
      calc (Finset.univ.filter (fun b => x (y b) = b)).card ≤ ({b, x b} : Finset α).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  have hcover : (Finset.univ : Finset α) ⊆
      (Finset.univ.filter (fun b => x b = b)) ∪
        (Finset.univ.filter (fun b => y b = b)) ∪
        (Finset.univ.filter (fun b => x (y b) = b)) := by
    intro b _
    rcases hstep1 b with h1 | h1 | h1
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl (by simpa using h1))))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr (by simpa using h1))))
    · exact Finset.mem_union.mpr (Or.inr (by simpa using h1))
  calc Fintype.card α = (Finset.univ : Finset α).card := by rw [Finset.card_univ]
    _ ≤ ((Finset.univ.filter (fun b => x b = b)) ∪
          (Finset.univ.filter (fun b => y b = b)) ∪
          (Finset.univ.filter (fun b => x (y b) = b))).card := Finset.card_le_card hcover
    _ ≤ ((Finset.univ.filter (fun b => x b = b)) ∪
          (Finset.univ.filter (fun b => y b = b))).card +
          (Finset.univ.filter (fun b => x (y b) = b)).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.filter (fun b => x b = b)).card +
          (Finset.univ.filter (fun b => y b = b)).card) +
          (Finset.univ.filter (fun b => x (y b) = b)).card := by
        have := Finset.card_union_le (Finset.univ.filter (fun b => x b = b))
          (Finset.univ.filter (fun b => y b = b))
        omega
    _ ≤ 6 := by omega

end CFSG.LocalAnalysis.WeakClosure81

end
