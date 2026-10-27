module

public import CFSG.Quasithin.EmptyFaithful.S153QDef

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4A

variable {W : Type} [CommGroup W] {z : MulAut W}

theorem isPt_iff {o : Subgroup W} : IsPt z o ↔ Nat.card ↥o = 4 ∧ ∀ w ∈ o, z w ∈ o := Iff.rfl

theorem z_cube_apply (hz3 : z ^ 3 = 1) (w : W) : z (z (z w)) = w := by
  have h := congrArg (fun g : MulAut W => g w) hz3
  simpa [pow_succ, MulAut.mul_apply] using h

theorem z_ne_one {w : W} (hw : w ≠ 1) : z w ≠ 1 := fun h => hw (z.injective (h.trans (map_one z).symm))

theorem three_dvd_of_zpow (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {x : W} (hx : x ≠ 1) {j : ℕ}
    (h : (z ^ j) x = x) : 3 ∣ j := by
  have hj : z ^ j = z ^ (j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hz3, one_pow, one_mul]
  rw [hj] at h
  have hlt : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : j % 3
  · omega
  · exact absurd (hfpf x (by simpa using h)) hx
  · have h2 : z (z x) = x := by simpa [pow_succ, MulAut.mul_apply] using h
    have h3 : z x = x := by
      have h4 := z_cube_apply hz3 x
      rw [h2] at h4
      exact h4
    exact absurd (hfpf x h3) hx

theorem pt_mem_cases (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {o : Subgroup W} (ho : IsPt z o) {w : W}
    (hw : w ∈ o) (hw1 : w ≠ 1) : ∀ x ∈ o, x = 1 ∨ x = w ∨ x = z w ∨ x = z (z w) := by
  classical
  obtain ⟨hcard, hz⟩ := isPt_iff.1 ho
  have hzw1 : z w ≠ 1 := z_ne_one hw1
  have hzzw1 : z (z w) ≠ 1 := z_ne_one hzw1
  have h12 : w ≠ z w := fun h => hw1 (hfpf w h.symm)
  have h23 : z w ≠ z (z w) := fun h => h12 (z.injective h)
  have h13 : w ≠ z (z w) := fun h => h12 (by
    have h4 := z_cube_apply hz3 w
    rw [← h] at h4
    exact h4.symm)
  have hS : ({1, w, z w, z (z w)} : Finset W).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h23]
    · simp [h12, h13]
    · simp [Ne.symm hw1, Ne.symm hzw1, Ne.symm hzzw1]
  have hsub : (({1, w, z w, z (z w)} : Finset W) : Set W) ⊆ (o : Set W) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact o.one_mem
    · exact hw
    · exact hz _ hw
    · exact hz _ (hz _ hw)
  have hoc : (o : Set W).ncard = 4 := by rw [← hcard, ← Nat.card_coe_set_eq]; rfl
  have hfin : (o : Set W).Finite :=
    Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero (show Nat.card ↥o ≠ 0 by omega))
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset, hS, hoc]) hfin
  intro x hx
  have hx' : x ∈ (({1, w, z w, z (z w)} : Finset W) : Set W) := heq ▸ hx
  simpa using hx'

theorem pt_exists_ne_one {o : Subgroup W} (h : IsPt z o) : ∃ w ∈ o, w ≠ 1 := by
  by_contra hcon
  have hbot : o = ⊥ := (Subgroup.eq_bot_iff_forall o).2 fun w hw => by
    by_contra hw1
    exact hcon ⟨w, hw, hw1⟩
  have h1 := (isPt_iff.1 h).1
  rw [hbot, Subgroup.card_bot] at h1
  omega

theorem pt_le_of_mem (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {o₁ o₂ : Subgroup W} (h₁ : IsPt z o₁)
    (h₂ : IsPt z o₂) {w : W} (hw₁ : w ∈ o₁) (hw₂ : w ∈ o₂) (hw1 : w ≠ 1) : o₁ ≤ o₂ := by
  intro x hx
  have h₂' := (isPt_iff.1 h₂).2
  rcases pt_mem_cases hz3 hfpf h₁ hw₁ hw1 x hx with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hw₂
  · exact h₂' _ hw₂
  · exact h₂' _ (h₂' _ hw₂)

theorem pt_inf_eq_bot (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {o₁ o₂ : Subgroup W} (h₁ : IsPt z o₁)
    (h₂ : IsPt z o₂) (hne : o₁ ≠ o₂) : o₁ ⊓ o₂ = ⊥ := by
  by_contra hbot
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  exact hne (le_antisymm (pt_le_of_mem hz3 hfpf h₁ h₂ hw.1 hw.2 hw1')
    (pt_le_of_mem hz3 hfpf h₂ h₁ hw.2 hw.1 hw1'))

theorem card_mul_le_card_sup [Finite W] {H K : Subgroup W} (h : H ⊓ K = ⊥) :
    Nat.card H * Nat.card K ≤ Nat.card ↥(H ⊔ K) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun ab : H × K => (⟨ab.1.1 * ab.2.1, mul_mem (Subgroup.mem_sup_left ab.1.2)
      (Subgroup.mem_sup_right ab.2.2)⟩ : ↥(H ⊔ K))) ?_
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
  simp only [Subtype.mk.injEq] at hab
  have h1 : a * a'⁻¹ ∈ H ⊓ K := by
    refine Subgroup.mem_inf.2 ⟨mul_mem ha (inv_mem ha'), ?_⟩
    have : a * a'⁻¹ = b' * b⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, hab, mul_comm]
    rw [this]
    exact mul_mem hb' (inv_mem hb)
  rw [h, Subgroup.mem_bot, mul_inv_eq_one] at h1
  subst h1
  have h2 : b = b' := mul_left_cancel hab
  subst h2
  rfl

theorem card_mod_three [Finite W] (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {U : Subgroup W}
    (hU : ∀ x ∈ U, z x ∈ U) : Nat.card U % 3 = 1 := by
  classical
  have : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun u => ⟨z u, hU u u.2⟩
  have h3 : ∀ u : U, f (f (f u)) = u := fun u => Subtype.ext (z_cube_apply hz3 (u : W))
  have hf : f ^ 3 ^ 1 = 1 := by
    show f^[3 ^ 1] = id
    funext u
    exact h3 u
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · exact Subtype.ext (map_one z)
    · rintro ⟨u, hu⟩
      have hu' : z u = u := congrArg Subtype.val hu
      exact Subtype.ext (Subtype.ext (hfpf u hu'))
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

theorem fix_of_stable (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {g : MulAut W} (hgz : g * z = z * g)
    {c : Subgroup W} (hc : IsPt z c) (hgc : ∀ x ∈ c, g x ∈ c) {m : ℕ} (hm : ¬ 3 ∣ m) (hgm : g ^ m = 1) :
    ∀ x ∈ c, g x = x := by
  intro x hx
  by_cases hx1 : x = 1
  · subst hx1
    exact map_one g
  have hgx1 : g x ≠ 1 := fun h => hx1 (g.injective (h.trans (map_one g).symm))
  have hcom : ∀ n : ℕ, g * z ^ n = z ^ n * g := fun n => (Commute.pow_right (show Commute g z from hgz) n).eq
  have key : ∀ a : ℕ, g x = (z ^ a) x → ∀ j : ℕ, (g ^ j) x = (z ^ (a * j)) x := by
    intro a ha j
    induction j with
    | zero => simp
    | succ j ih =>
      calc (g ^ (j + 1)) x = (g * g ^ j) x := by rw [pow_succ']
        _ = g ((g ^ j) x) := rfl
        _ = g ((z ^ (a * j)) x) := by rw [ih]
        _ = (g * z ^ (a * j)) x := rfl
        _ = (z ^ (a * j) * g) x := by rw [hcom]
        _ = (z ^ (a * j)) (g x) := rfl
        _ = (z ^ (a * j)) ((z ^ a) x) := by rw [ha]
        _ = (z ^ (a * j) * z ^ a) x := rfl
        _ = (z ^ (a * (j + 1))) x := by rw [← pow_add, mul_add, mul_one]
  rcases pt_mem_cases hz3 hfpf hc hx hx1 (g x) (hgc x hx) with h | h | h | h
  · exact absurd h hgx1
  · exact h
  · exfalso
    have h1 := key 1 (by simpa using h) m
    rw [hgm] at h1
    have h3 := three_dvd_of_zpow hz3 hfpf hx1 (j := 1 * m) (by simpa using h1.symm)
    omega
  · exfalso
    have h1 := key 2 (by simpa [pow_succ, MulAut.mul_apply] using h) m
    rw [hgm] at h1
    have h3 := three_dvd_of_zpow hz3 hfpf hx1 (j := 2 * m) (by simpa using h1.symm)
    omega

end Q4A

end S153Q

end CFSG.Quasithin
