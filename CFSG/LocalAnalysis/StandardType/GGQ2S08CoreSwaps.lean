module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType

private lemma ggQ2s08k5_eq_swap_of_apply_ne {m : ℕ} {x : Equiv.Perm (Fin m)} (hx : x.IsSwap)
    {u : Fin m} (hu : x u ≠ u) : x = Equiv.swap u (x u) := by
  obtain ⟨p, q, hpq, rfl⟩ := hx
  have hupq : u = p ∨ u = q := (Equiv.swap_apply_ne_self_iff.mp hu).2
  rcases hupq with h | h
  · subst h
    simp
  · subst h
    rw [Equiv.swap_comm]
    simp

private lemma ggQ2s08k5_not_commute_of_moves {m : ℕ} {x y : Equiv.Perm (Fin m)}
    (hx : x.IsSwap) (hy : y.IsSwap) (hxy : x ≠ y) {u : Fin m} (hxu : x u ≠ u)
    (hyu : y u ≠ u) : x * y ≠ y * x := by
  have hx' : x = Equiv.swap u (x u) := ggQ2s08k5_eq_swap_of_apply_ne hx hxu
  have hy' : y = Equiv.swap u (y u) := ggQ2s08k5_eq_swap_of_apply_ne hy hyu
  have hvu : u ≠ x u := fun h => hxu h.symm
  have hwu : u ≠ y u := fun h => hyu h.symm
  have hvw : x u ≠ y u := by
    intro h
    exact hxy (by rw [hx', hy', h])
  intro h
  rw [hx', hy'] at h
  have key := congrArg (fun f : Equiv.Perm (Fin m) => f (x u)) h
  have hlhs : (Equiv.swap u (x u) * Equiv.swap u (y u)) (x u) = u := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxu hvw, Equiv.swap_apply_right]
  have hrhs : (Equiv.swap u (y u) * Equiv.swap u (x u)) (x u) = y u := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  rw [hlhs, hrhs] at key
  exact hwu key

private lemma ggQ2s08k5_common_of_pow_three {m : ℕ} {x y : Equiv.Perm (Fin m)}
    (hx : x.IsSwap) (hy : y.IsSwap) (hxy : x ≠ y) (h3 : (x * y) ^ 3 = 1) :
    ∃ u, x u ≠ u ∧ y u ≠ u := by
  by_contra h
  have hd : x.Disjoint y := by
    intro u
    by_cases hu : x u = u
    · exact Or.inl hu
    · right
      by_contra hyu
      exact h ⟨u, hu, hyu⟩
  have hx2 : orderOf x = 2 := hx.orderOf
  have hy2 : orderOf y = 2 := hy.orderOf
  have horder : orderOf (x * y) = 2 := by
    rw [hd.orderOf, hx2, hy2, Nat.lcm_self]
  have hdiv : orderOf (x * y) ∣ 3 := (orderOf_dvd_iff_pow_eq_one).mpr h3
  rw [horder] at hdiv
  exact absurd hdiv (by norm_num)

private lemma ggQ2s08k5_isThreeCycle_of_common {m : ℕ} {x y : Equiv.Perm (Fin m)}
    (hx : x.IsSwap) (hy : y.IsSwap) (hxy : x ≠ y) {u : Fin m} (hxu : x u ≠ u)
    (hyu : y u ≠ u) : (x * y).IsThreeCycle := by
  have hx' : x = Equiv.swap u (x u) := ggQ2s08k5_eq_swap_of_apply_ne hx hxu
  have hy' : y = Equiv.swap u (y u) := ggQ2s08k5_eq_swap_of_apply_ne hy hyu
  have hvu : u ≠ x u := fun h => hxu h.symm
  have hwu : u ≠ y u := fun h => hyu h.symm
  have hvw : x u ≠ y u := by
    intro h
    exact hxy (by rw [hx', hy', h])
  rw [hx', hy']
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hvu hwu hvw

private lemma ggQ2s08k5_moves_left_or_right {m : ℕ} {p q : Fin m} (hpq : p ≠ q)
    {x : Equiv.Perm (Fin m)} (hx : x.IsSwap) (hne : Equiv.swap p q ≠ x)
    (h3 : (Equiv.swap p q * x) ^ 3 = 1) : (x p ≠ p) ∨ (x q ≠ q) := by
  obtain ⟨u, hzu, hxu⟩ :=
    ggQ2s08k5_common_of_pow_three (Equiv.Perm.swap_isSwap_iff.mpr hpq) hx hne h3
  have hu : u = p ∨ u = q := (Equiv.swap_apply_ne_self_iff.mp hzu).2
  rcases hu with h | h
  · left
    rwa [← h]
  · right
    rwa [← h]

private def ggQ2s08k5_Good {m ℓ : ℕ} (τ : Fin ℓ → Equiv.Perm (Fin m)) (n : ℕ)
    (a : ℕ → Fin m) : Prop :=
  (∀ i j, i ≤ n → j ≤ n → a i = a j → i = j) ∧
  (∀ i, i < n → ∀ (h : i < ℓ), τ ⟨i, h⟩ = Equiv.swap (a i) (a (i + 1)))

private theorem ggQ2s08k5_swap_path_aux {m : ℕ} (hm : 0 < m) (ℓ : ℕ)
    (τ : Fin ℓ → Equiv.Perm (Fin m)) (hsw : ∀ i, (τ i).IsSwap)
    (hne : ∀ i j, i ≠ j → τ i ≠ τ j)
    (hadj : ∀ i j : Fin ℓ, (i : ℕ) + 1 = j → (τ i * τ j) ^ 3 = 1)
    (hcomm : ∀ i j : Fin ℓ, (i : ℕ) + 2 ≤ j → τ i * τ j = τ j * τ i) :
    ∃ a : Fin (ℓ + 1) → Fin m, Function.Injective a ∧
      ∀ i : Fin ℓ, τ i = Equiv.swap (a i.castSucc) (a i.succ) := by
  have key : ∀ n, n ≤ ℓ → ∃ a : ℕ → Fin m, ggQ2s08k5_Good τ n a := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨fun _ => ⟨0, hm⟩, ?_, ?_⟩
      · intro i j hi hj _
        omega
      · intro i hi h
        omega
    | succ n ih =>
      intro hn
      obtain ⟨a, Hinj, Hrel⟩ := ih (by omega)
      rcases n with _ | _ | k
      ·
        obtain ⟨p, q, hpq, hτ⟩ := hsw ⟨0, by omega⟩
        refine ⟨fun i => if i = 0 then p else if i = 1 then q else a i, ?_, ?_⟩
        · intro i j hi hj hij
          have hi' : i = 0 ∨ i = 1 := by omega
          have hj' : j = 0 ∨ j = 1 := by omega
          rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
          · rfl
          · change p = q at hij
            exact absurd hij hpq
          · change q = p at hij
            exact absurd hij.symm hpq
          · rfl
        · intro i hi h
          have hi' : i = 0 := by omega
          subst hi'
          simpa using hτ
      ·
        have hτ0 : τ ⟨0, by omega⟩ = Equiv.swap (a 0) (a 1) := Hrel 0 (by omega) (by omega)
        have hne01 : τ ⟨0, by omega⟩ ≠ τ ⟨1, by omega⟩ :=
          hne ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
        have h3 : (τ ⟨0, by omega⟩ * τ ⟨1, by omega⟩) ^ 3 = 1 :=
          hadj ⟨0, by omega⟩ ⟨1, by omega⟩ rfl
        obtain ⟨u, hu0, hu1⟩ := ggQ2s08k5_common_of_pow_three (hsw ⟨0, by omega⟩)
          (hsw ⟨1, by omega⟩) hne01 h3
        rw [hτ0] at hu0
        have hu : u = a 0 ∨ u = a 1 := (Equiv.swap_apply_ne_self_iff.mp hu0).2
        have ha01 : a 0 ≠ a 1 := by
          intro h
          exact (by omega : (0 : ℕ) ≠ 1) (Hinj 0 1 (by omega) (by omega) h)
        by_cases hq : τ ⟨1, by omega⟩ (a 1) ≠ a 1
        · have ha0v : a 0 ≠ τ ⟨1, by omega⟩ (a 1) := by
            intro h
            have hτ1 : τ ⟨1, by omega⟩ = Equiv.swap (a 1) (τ ⟨1, by omega⟩ (a 1)) :=
              ggQ2s08k5_eq_swap_of_apply_ne (hsw ⟨1, by omega⟩) hq
            apply hne01
            rw [hτ0, hτ1, h]
            exact Equiv.swap_comm _ _
          have ha1v : a 1 ≠ τ ⟨1, by omega⟩ (a 1) := fun h => hq h.symm
          refine ⟨fun i => if i = 0 then a 0 else if i = 1 then a 1
            else if i = 2 then τ ⟨1, by omega⟩ (a 1) else a i, ?_, ?_⟩
          · intro i j hi hj hij
            have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
            have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
            rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
            all_goals first
              | rfl
              | (change a 0 = a 1 at hij; exact absurd hij ha01)
              | (change a 1 = a 0 at hij; exact absurd hij.symm ha01)
              | (change a 0 = τ ⟨1, by omega⟩ (a 1) at hij; exact absurd hij ha0v)
              | (change τ ⟨1, by omega⟩ (a 1) = a 0 at hij;
                  exact absurd hij.symm ha0v)
              | (change a 1 = τ ⟨1, by omega⟩ (a 1) at hij; exact absurd hij ha1v)
              | (change τ ⟨1, by omega⟩ (a 1) = a 1 at hij;
                  exact absurd hij.symm ha1v)
          · intro i hi h
            have hi' : i = 0 ∨ i = 1 := by omega
            rcases hi' with rfl | rfl
            · simpa using hτ0
            · have hτ1 : τ ⟨1, by omega⟩ = Equiv.swap (a 1) (τ ⟨1, by omega⟩ (a 1)) :=
                ggQ2s08k5_eq_swap_of_apply_ne (hsw ⟨1, by omega⟩) hq
              simpa using hτ1
        · have hp : τ ⟨1, by omega⟩ (a 0) ≠ a 0 := by
            rcases hu with h | h
            · rwa [h] at hu1
            · rw [h] at hu1
              exact absurd hu1 hq
          have hτ1 : τ ⟨1, by omega⟩ = Equiv.swap (a 0) (τ ⟨1, by omega⟩ (a 0)) :=
            ggQ2s08k5_eq_swap_of_apply_ne (hsw ⟨1, by omega⟩) hp
          have ha1v : a 1 ≠ τ ⟨1, by omega⟩ (a 0) := by
            intro h
            apply hne01
            rw [hτ0, hτ1, h]
          refine ⟨fun i => if i = 0 then a 1 else if i = 1 then a 0
            else if i = 2 then τ ⟨1, by omega⟩ (a 0) else a i, ?_, ?_⟩
          · intro i j hi hj hij
            have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
            have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
            rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
            all_goals first
              | rfl
              | (change a 1 = a 0 at hij; exact absurd hij.symm ha01)
              | (change a 0 = a 1 at hij; exact absurd hij ha01)
              | (change a 1 = τ ⟨1, by omega⟩ (a 0) at hij; exact absurd hij ha1v)
              | (change τ ⟨1, by omega⟩ (a 0) = a 1 at hij;
                  exact absurd hij.symm ha1v)
              | (change a 0 = τ ⟨1, by omega⟩ (a 0) at hij;
                  exact absurd hij.symm hp)
              | (change τ ⟨1, by omega⟩ (a 0) = a 0 at hij; exact absurd hij hp)
          · intro i hi h
            have hi' : i = 0 ∨ i = 1 := by omega
            rcases hi' with rfl | rfl
            · rw [hτ0]
              exact Equiv.swap_comm _ _
            · simpa using hτ1
      ·
        have hrel_k1 : τ ⟨k + 1, by omega⟩ = Equiv.swap (a (k + 1)) (a (k + 2)) :=
          Hrel (k + 1) (by omega) (by omega)
        have hrel_k : τ ⟨k, by omega⟩ = Equiv.swap (a k) (a (k + 1)) :=
          Hrel k (by omega) (by omega)
        have hak : a k ≠ a (k + 1) := by
          intro h
          exact (by omega : k ≠ k + 1) (Hinj k (k + 1) (by omega) (by omega) h)
        have hne_k1 : τ ⟨k + 1, by omega⟩ ≠ τ ⟨k + 2, by omega⟩ :=
          hne ⟨k + 1, by omega⟩ ⟨k + 2, by omega⟩ (by simp)
        have h3 : (τ ⟨k + 1, by omega⟩ * τ ⟨k + 2, by omega⟩) ^ 3 = 1 :=
          hadj ⟨k + 1, by omega⟩ ⟨k + 2, by omega⟩ rfl
        obtain ⟨u, hu_k1, hu_k2⟩ := ggQ2s08k5_common_of_pow_three (hsw ⟨k + 1, by omega⟩)
          (hsw ⟨k + 2, by omega⟩) hne_k1 h3
        rw [hrel_k1] at hu_k1
        have hu : u = a (k + 1) ∨ u = a (k + 2) :=
          (Equiv.swap_apply_ne_self_iff.mp hu_k1).2
        have hcomm_k : τ ⟨k, by omega⟩ * τ ⟨k + 2, by omega⟩ =
            τ ⟨k + 2, by omega⟩ * τ ⟨k, by omega⟩ :=
          hcomm ⟨k, by omega⟩ ⟨k + 2, by omega⟩ (by simp)
        have hτk_moves : τ ⟨k, by omega⟩ (a (k + 1)) ≠ a (k + 1) := by
          rw [hrel_k, Equiv.swap_apply_right]
          exact hak
        have hnext_fixes : τ ⟨k + 2, by omega⟩ (a (k + 1)) = a (k + 1) := by
          by_contra hfix
          have hnc := ggQ2s08k5_not_commute_of_moves (hsw ⟨k, by omega⟩)
            (hsw ⟨k + 2, by omega⟩)
            (hne ⟨k, by omega⟩ ⟨k + 2, by omega⟩ (by simp)) hτk_moves hfix
          exact hnc hcomm_k
        have huy : u = a (k + 2) := by
          rcases hu with h | h
          · exact absurd (by rw [h]; exact hnext_fixes) hu_k2
          · exact h
        have hnext_moves : τ ⟨k + 2, by omega⟩ (a (k + 2)) ≠ a (k + 2) := by
          rwa [huy] at hu_k2
        have hw_eq : τ ⟨k + 2, by omega⟩ =
            Equiv.swap (a (k + 2)) (τ ⟨k + 2, by omega⟩ (a (k + 2))) :=
          ggQ2s08k5_eq_swap_of_apply_ne (hsw ⟨k + 2, by omega⟩) hnext_moves
        have hv_ne_last : τ ⟨k + 2, by omega⟩ (a (k + 2)) ≠ a (k + 2) := hnext_moves
        have hv_ne_x : τ ⟨k + 2, by omega⟩ (a (k + 2)) ≠ a (k + 1) := by
          intro h
          apply hne_k1
          rw [hrel_k1, hw_eq, h]
          exact Equiv.swap_comm _ _
        have hv_ne_prev : ∀ i, i ≤ k → τ ⟨k + 2, by omega⟩ (a (k + 2)) ≠ a i := by
          intro i hi hvi
          have hcomm_i : τ ⟨i, by omega⟩ * τ ⟨k + 2, by omega⟩ =
              τ ⟨k + 2, by omega⟩ * τ ⟨i, by omega⟩ :=
            hcomm ⟨i, by omega⟩ ⟨k + 2, by omega⟩ (by simp; omega)
          have hτi_moves : τ ⟨i, by omega⟩ (a i) ≠ a i := by
            rw [Hrel i (by omega) (by omega), Equiv.swap_apply_left]
            exact fun h => (by omega : i + 1 ≠ i) (Hinj (i + 1) i (by omega) (by omega) h)
          have hnext_moves_i : τ ⟨k + 2, by omega⟩ (a i) ≠ a i := by
            rw [hw_eq]
            rw [show a i = τ ⟨k + 2, by omega⟩ (a (k + 2)) from hvi.symm]
            rw [Equiv.swap_apply_right]
            exact fun h => (by omega : k + 2 ≠ i)
              (Hinj (k + 2) i (by omega) (by omega) (h.trans hvi))
          exact (ggQ2s08k5_not_commute_of_moves (hsw ⟨i, by omega⟩)
            (hsw ⟨k + 2, by omega⟩)
            (hne ⟨i, by omega⟩ ⟨k + 2, by omega⟩ (by simp; omega)) hτi_moves
            hnext_moves_i) hcomm_i
        have hv_ne : ∀ i, i ≤ k + 2 → τ ⟨k + 2, by omega⟩ (a (k + 2)) ≠ a i := by
          intro i hi
          rcases (by omega : i = k + 2 ∨ i = k + 1 ∨ i ≤ k) with h | h | h
          · rw [h]
            exact hv_ne_last
          · rw [h]
            exact hv_ne_x
          · exact hv_ne_prev i h
        refine ⟨Function.update a (k + 3)
          (τ ⟨k + 2, by omega⟩ (a (k + 2))), ?_, ?_⟩
        · intro i j hi hj hij
          by_cases hi3 : i = k + 3
          · subst hi3
            rw [Function.update_self] at hij
            by_cases hj3 : j = k + 3
            · subst hj3
              rfl
            · rw [Function.update_of_ne (by omega : j ≠ k + 3) _ a] at hij
              exact absurd hij (hv_ne j (by omega))
          · rw [Function.update_of_ne (by omega : i ≠ k + 3) _ a] at hij
            by_cases hj3 : j = k + 3
            · subst hj3
              rw [Function.update_self] at hij
              exact absurd hij.symm (hv_ne i (by omega))
            · rw [Function.update_of_ne (by omega : j ≠ k + 3) _ a] at hij
              exact Hinj i j (by omega) (by omega) hij
        · intro i hi h
          by_cases hi2 : i = k + 2
          · subst hi2
            have h1 : Function.update a (k + 3)
                (τ ⟨k + 2, by omega⟩ (a (k + 2))) (k + 2) = a (k + 2) :=
              Function.update_of_ne (by omega) _ a
            have h2 : Function.update a (k + 3)
                (τ ⟨k + 2, by omega⟩ (a (k + 2))) (k + 3) =
                τ ⟨k + 2, by omega⟩ (a (k + 2)) := Function.update_self _ _ a
            rw [h1, h2]
            simpa using hw_eq
          · have h1 : Function.update a (k + 3)
                (τ ⟨k + 2, by omega⟩ (a (k + 2))) i = a i :=
              Function.update_of_ne (by omega) _ a
            have h2 : Function.update a (k + 3)
                (τ ⟨k + 2, by omega⟩ (a (k + 2))) (i + 1) = a (i + 1) :=
              Function.update_of_ne (by omega) _ a
            rw [Hrel i (by omega) h, h1, h2]
  obtain ⟨a, Hinj, Hrel⟩ := key ℓ (le_refl ℓ)
  refine ⟨fun i => a i, ?_, ?_⟩
  · intro i j hij
    exact Fin.ext (Hinj i.val j.val (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)
      hij)
  · intro i
    simpa using Hrel i.val i.isLt i.isLt

theorem ggQ2s08core_no_four {m : ℕ} {a b : Equiv.Perm (Fin m)} (ha : a.IsSwap) (hb : b.IsSwap)
    (hab : a ≠ b) (h4 : (a * b) ^ 4 = 1) : a * b = b * a := by
  obtain ⟨p, q, hpq, rfl⟩ := ha
  obtain ⟨r, s, hrs, rfl⟩ := hb
  by_cases hc : ∃ u, Equiv.swap p q u ≠ u ∧ Equiv.swap r s u ≠ u
  · obtain ⟨u, hu1, hu2⟩ := hc
    have ht := ggQ2s08k5_isThreeCycle_of_common (Equiv.Perm.swap_isSwap_iff.mpr hpq)
      (Equiv.Perm.swap_isSwap_iff.mpr hrs) hab hu1 hu2
    have hdiv : orderOf (Equiv.swap p q * Equiv.swap r s) ∣ 4 :=
      (orderOf_dvd_iff_pow_eq_one).mpr h4
    rw [ht.orderOf] at hdiv
    exact absurd hdiv (by norm_num)
  · have hd : Equiv.Perm.Disjoint (Equiv.swap p q) (Equiv.swap r s) := by
      intro u
      by_cases hu : Equiv.swap p q u = u
      · exact Or.inl hu
      · right
        by_contra hcon
        exact hc ⟨u, hu, hcon⟩
    exact hd.commute.eq

theorem ggQ2s08core_no_fork {m : ℕ} {z a b c : Equiv.Perm (Fin m)} (hz : z.IsSwap) (ha : a.IsSwap)
    (hb : b.IsSwap) (hc : c.IsSwap) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h3a : (z * a) ^ 3 = 1) (h3b : (z * b) ^ 3 = 1)
    (h3c : (z * c) ^ 3 = 1) (hab' : a * b = b * a) (hac' : a * c = c * a) (hbc' : b * c = c * b) :
    False := by
  obtain ⟨p, q, hpq, rfl⟩ := hz
  obtain ⟨A1, A2, hA12, rfl⟩ := ha
  obtain ⟨B1, B2, hB12, rfl⟩ := hb
  obtain ⟨C1, C2, hC12, rfl⟩ := hc
  have hAs := ggQ2s08k5_moves_left_or_right hpq (Equiv.Perm.swap_isSwap_iff.mpr hA12) hza h3a
  have hBs := ggQ2s08k5_moves_left_or_right hpq (Equiv.Perm.swap_isSwap_iff.mpr hB12) hzb h3b
  have hCs := ggQ2s08k5_moves_left_or_right hpq (Equiv.Perm.swap_isSwap_iff.mpr hC12) hzc h3c
  have hABp : ¬ (Equiv.swap A1 A2 p ≠ p ∧ Equiv.swap B1 B2 p ≠ p) := by
    rintro ⟨h1, h2⟩
    exact (ggQ2s08k5_not_commute_of_moves (Equiv.Perm.swap_isSwap_iff.mpr hA12)
      (Equiv.Perm.swap_isSwap_iff.mpr hB12) hab h1 h2) hab'
  have hABq : ¬ (Equiv.swap A1 A2 q ≠ q ∧ Equiv.swap B1 B2 q ≠ q) := by
    rintro ⟨h1, h2⟩
    exact (ggQ2s08k5_not_commute_of_moves (Equiv.Perm.swap_isSwap_iff.mpr hA12)
      (Equiv.Perm.swap_isSwap_iff.mpr hB12) hab h1 h2) hab'
  have hACp : ¬ (Equiv.swap A1 A2 p ≠ p ∧ Equiv.swap C1 C2 p ≠ p) := by
    rintro ⟨h1, h2⟩
    exact (ggQ2s08k5_not_commute_of_moves (Equiv.Perm.swap_isSwap_iff.mpr hA12)
      (Equiv.Perm.swap_isSwap_iff.mpr hC12) hac h1 h2) hac'
  have hACq : ¬ (Equiv.swap A1 A2 q ≠ q ∧ Equiv.swap C1 C2 q ≠ q) := by
    rintro ⟨h1, h2⟩
    exact (ggQ2s08k5_not_commute_of_moves (Equiv.Perm.swap_isSwap_iff.mpr hA12)
      (Equiv.Perm.swap_isSwap_iff.mpr hC12) hac h1 h2) hac'
  have hBCp : ¬ (Equiv.swap B1 B2 p ≠ p ∧ Equiv.swap C1 C2 p ≠ p) := by
    rintro ⟨h1, h2⟩
    exact (ggQ2s08k5_not_commute_of_moves (Equiv.Perm.swap_isSwap_iff.mpr hB12)
      (Equiv.Perm.swap_isSwap_iff.mpr hC12) hbc h1 h2) hbc'
  have hBCq : ¬ (Equiv.swap B1 B2 q ≠ q ∧ Equiv.swap C1 C2 q ≠ q) := by
    rintro ⟨h1, h2⟩
    exact (ggQ2s08k5_not_commute_of_moves (Equiv.Perm.swap_isSwap_iff.mpr hB12)
      (Equiv.Perm.swap_isSwap_iff.mpr hC12) hbc h1 h2) hbc'
  by_cases hpa : Equiv.swap A1 A2 p ≠ p
  · by_cases hpb : Equiv.swap B1 B2 p ≠ p
    · exact hABp ⟨hpa, hpb⟩
    · by_cases hpc : Equiv.swap C1 C2 p ≠ p
      · exact hACp ⟨hpa, hpc⟩
      · have hqb : Equiv.swap B1 B2 q ≠ q := by
          rcases hBs with h | h
          · exact absurd h hpb
          · exact h
        have hqc : Equiv.swap C1 C2 q ≠ q := by
          rcases hCs with h | h
          · exact absurd h hpc
          · exact h
        exact hBCq ⟨hqb, hqc⟩
  · have hqa : Equiv.swap A1 A2 q ≠ q := by
      rcases hAs with h | h
      · exact absurd h hpa
      · exact h
    by_cases hpb : Equiv.swap B1 B2 p ≠ p
    · by_cases hpc : Equiv.swap C1 C2 p ≠ p
      · exact hBCp ⟨hpb, hpc⟩
      · have hqc : Equiv.swap C1 C2 q ≠ q := by
          rcases hCs with h | h
          · exact absurd h hpc
          · exact h
        exact hACq ⟨hqa, hqc⟩
    · have hqb : Equiv.swap B1 B2 q ≠ q := by
        rcases hBs with h | h
        · exact absurd h hpb
        · exact h
      exact hABq ⟨hqa, hqb⟩

theorem ggQ2s08k5_swap_path_nonempty {m ℓ : ℕ} (hm : 0 < m) (τ : Fin ℓ → Equiv.Perm (Fin m))
    (hsw : ∀ i, (τ i).IsSwap)
    (hne : ∀ i j, i ≠ j → τ i ≠ τ j)
    (hadj : ∀ i j : Fin ℓ, (i : ℕ) + 1 = j → (τ i * τ j) ^ 3 = 1)
    (hcomm : ∀ i j : Fin ℓ, (i : ℕ) + 2 ≤ j → τ i * τ j = τ j * τ i) :
    ∃ a : Fin (ℓ + 1) → Fin m, Function.Injective a ∧
      ∀ i : Fin ℓ, τ i = Equiv.swap (a i.castSucc) (a i.succ) :=
  ggQ2s08k5_swap_path_aux hm ℓ τ hsw hne hadj hcomm

theorem ggQ2s08core_swap_path {m ℓ : ℕ} (hℓ : 0 < ℓ) (τ : Fin ℓ → Equiv.Perm (Fin m))
    (hsw : ∀ i, (τ i).IsSwap)
    (hne : ∀ i j, i ≠ j → τ i ≠ τ j)
    (hadj : ∀ i j : Fin ℓ, (i : ℕ) + 1 = j → (τ i * τ j) ^ 3 = 1)
    (hcomm : ∀ i j : Fin ℓ, (i : ℕ) + 2 ≤ j → τ i * τ j = τ j * τ i) :
    ∃ a : Fin (ℓ + 1) → Fin m, Function.Injective a ∧
      ∀ i : Fin ℓ, τ i = Equiv.swap (a i.castSucc) (a i.succ) := by
  obtain ⟨x, _, -, -⟩ := hsw ⟨0, hℓ⟩
  exact ggQ2s08k5_swap_path_nonempty (Fin.pos x) τ hsw hne hadj hcomm

end CFSG.StandardType

end
