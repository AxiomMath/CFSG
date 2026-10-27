module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.RankThree.PartOne.FIS.PermFacts

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.BenderSuzuki

namespace WreathClass

open Equiv SemidirectProduct

variable {f m : ℕ}

theorem mul_left_apply (a b : L2Wreath f m) (p : Fin m) :
    (a * b).left p = a.left p * b.left (a.right⁻¹ p) := rfl

theorem inl_conj_left (y : Fin m → PSL2Model f) (c : L2Wreath f m) (p : Fin m) :
    (inl y * c * (inl y)⁻¹).left p = y p * c.left p * (y (c.right⁻¹ p))⁻¹ := by
  simp [mul_left_apply]

theorem inl_conj_right (y : Fin m → PSL2Model f) (c : L2Wreath f m) :
    (inl y * c * (inl y)⁻¹).right = c.right := by
  simp

theorem inr_conj_left (σ : Perm (Fin m)) (c : L2Wreath f m) (p : Fin m) :
    (inr σ * c * (inr σ)⁻¹).left p = c.left (σ⁻¹ p) := by
  simp [mul_left_apply]

theorem inr_conj_right (σ : Perm (Fin m)) (c : L2Wreath f m) :
    (inr σ * c * (inr σ)⁻¹).right = σ * c.right * σ⁻¹ := by
  simp

theorem exists_conj_ne (hf : 2 ≤ f) {t : PSL2Model f} (ht : t ≠ 1) (u : PSL2Model f) :
    ∃ a : PSL2Model f, a * t * a⁻¹ ≠ u := by
  by_contra h
  push Not at h
  apply ht
  have hc : t ∈ Subgroup.center (PSL2Model f) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := h g
    have h2 := h 1
    simp only [one_mul, inv_one, mul_one] at h2
    rw [← h2] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  rw [center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hc
  exact hc

theorem exists_mul_self_ne_one (hf : 2 ≤ f) : ∃ a : PSL2Model f, a * a ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨t, -, ht1⟩ := WreathEndgame.exists_involution hf
  apply ht1
  have hc : t ∈ Subgroup.center (PSL2Model f) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g⁻¹ = g := inv_eq_of_mul_eq_one_right (h g)
    have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right (h t)
    have hgt : (g * t)⁻¹ = g * t := inv_eq_of_mul_eq_one_right (h (g * t))
    calc g * t = (g * t)⁻¹ := hgt.symm
      _ = t * g := by rw [mul_inv_rev, hg, ht]
  rw [center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hc
  exact hc

theorem mul_self_eq_one_of_mem {G : Type*} [Group G] {C : Set G} (hC : IsOddTransp C) {c : G}
    (hc : c ∈ C) : c * c = 1 := by
  have h := pow_orderOf_eq_one c
  rwa [hC.1 c hc, pow_two] at h

theorem left_mul_left_eq_one {c : L2Wreath f m} (h : c * c = 1) (p : Fin m) :
    c.left p * c.left (c.right⁻¹ p) = 1 := by
  have := congrArg (fun z => z.left p) h
  simpa [mul_left_apply] using this

theorem not_dvd_two_or_odd_of_right {P : L2Wreath f m} (h : orderOf P.right = 2) (hP : P * P ≠ 1) :
    ¬ (orderOf P ∣ 2 ∨ Odd (orderOf P)) := by
  have h2 : 2 ∣ orderOf P := by
    have h1 := orderOf_map_dvd (SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) P
    change orderOf P.right ∣ orderOf P at h1
    rwa [h] at h1
  rintro (h' | ⟨q, hq⟩)
  · apply hP
    have hord : orderOf P = 2 := Nat.dvd_antisymm h' h2
    have h1 := pow_orderOf_eq_one P
    rwa [hord, pow_two] at h1
  · obtain ⟨s, hs⟩ := h2
    omega

theorem orderOf_swap_mul_swap {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) : orderOf (swap i j * swap k l) = 2 := by
  have hd : (swap i j).Disjoint (swap k l) :=
    (WreathEndgame.swapDisjoint_iff hij hkl).2 ⟨hik, hil, hjk, hjl⟩
  have hsq : (swap i j * swap k l) ^ 2 = 1 := by
    rw [hd.commute.mul_pow]
    simp [pow_two]
  have hne : swap i j * swap k l ≠ 1 := by
    intro h
    have h1 := congrArg (fun σ : Perm (Fin m) => σ i) h
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hik hil, swap_apply_left,
      Perm.one_apply] at h1
    exact hij h1.symm
  exact orderOf_eq_prime hsq hne

theorem exists_conj_over_swap {c : L2Wreath f m} {i j k l : Fin m} (hr : c.right = swap i j)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (a : PSL2Model f) :
    ∃ g : L2Wreath f m, (g * c * g⁻¹).right = swap k l ∧
      (g * c * g⁻¹).left i = a * c.left k * a⁻¹ ∧ (g * c * g⁻¹).left j = c.left l := by
  set σ : Perm (Fin m) := swap i k * swap j l with hσ
  have hσi : σ i = k := by
    rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne hij hil, swap_apply_left]
  have hσj : σ j = l := by
    rw [hσ, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hil.symm hkl.symm]
  have hσi' : σ⁻¹ i = k := by
    rw [hσ, mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hjk.symm hkl]
  have hσj' : σ⁻¹ j = l := by
    rw [hσ, mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply,
      swap_apply_of_ne_of_ne hij.symm hjk, swap_apply_left]
  have hr₁ : (inr σ * c * (inr σ)⁻¹).right = swap k l := by
    rw [inr_conj_right, hr, ← swap_apply_apply, hσi, hσj]
  have hg : inl (Pi.mulSingle i a : Fin m → PSL2Model f) * inr σ * c *
      (inl (Pi.mulSingle i a : Fin m → PSL2Model f) * inr σ)⁻¹ =
      inl (Pi.mulSingle i a : Fin m → PSL2Model f) * (inr σ * c * (inr σ)⁻¹) *
        (inl (Pi.mulSingle i a : Fin m → PSL2Model f))⁻¹ := by
    group
  refine ⟨inl (Pi.mulSingle i a : Fin m → PSL2Model f) * inr σ, ?_, ?_, ?_⟩
  · rw [hg, inl_conj_right, hr₁]
  · rw [hg, inl_conj_left, hr₁, swap_inv, swap_apply_of_ne_of_ne hik hil, inr_conj_left, hσi',
      Pi.mulSingle_eq_same]
  · rw [hg, inl_conj_left, hr₁, swap_inv, swap_apply_of_ne_of_ne hjk hjl, inr_conj_left, hσj',
      Pi.mulSingle_eq_of_ne hij.symm, inv_one, mul_one, one_mul]

theorem left_eq_one_of_normalized (hf : 2 ≤ f) (hm : 4 ≤ m) {C : Set (L2Wreath f m)}
    (hC : IsOddTransp C) (hconj : ∀ c ∈ C, ∀ g : L2Wreath f m, g * c * g⁻¹ ∈ C)
    {c : L2Wreath f m} (hc : c ∈ C) {i j : Fin m} (hij : i ≠ j) (hr : c.right = swap i j)
    (hi : c.left i = 1) (hj : c.left j = 1) {k : Fin m} (hki : k ≠ i) (hkj : k ≠ j) :
    c.left k = 1 := by
  by_contra ht
  obtain ⟨l, hli, hlj, hlk⟩ := CFSG.RankThree.PartOne.FIS.PermFacts.exists_fourth hm i j k
  obtain ⟨a, ha⟩ := exists_conj_ne hf ht (c.left l)⁻¹
  have hik : i ≠ k := hki.symm
  have hjk : j ≠ k := hkj.symm
  have hil : i ≠ l := hli.symm
  have hjl : j ≠ l := hlj.symm
  have hkl : k ≠ l := hlk.symm
  obtain ⟨g, hgr, hgi, hgj⟩ := exists_conj_over_swap hr hij hik hil hjk hjl hkl a
  have hcinv : c.right⁻¹ = swap i j := by rw [hr, swap_inv]
  have hPr : (c * (g * c * g⁻¹)).right = swap i j * swap k l := by
    rw [mul_right, hr, hgr]
  have hPi : (c * (g * c * g⁻¹)).left i = c.left l := by
    rw [mul_left_apply, hcinv, swap_apply_left, hi, one_mul, hgj]
  have hPj : (c * (g * c * g⁻¹)).left j = a * c.left k * a⁻¹ := by
    rw [mul_left_apply, hcinv, swap_apply_right, hj, one_mul, hgi]
  have hPinv : (c * (g * c * g⁻¹)).right⁻¹ i = j := by
    rw [hPr, mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hjk hjl]
  have hPP : ((c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹))).left i =
      c.left l * (a * c.left k * a⁻¹) := by
    rw [mul_left_apply, hPinv, hPi, hPj]
  have hord : orderOf (c * (g * c * g⁻¹)).right = 2 := by
    rw [hPr]
    exact orderOf_swap_mul_swap hij hkl hik hil hjk hjl
  refine not_dvd_two_or_odd_of_right hord (fun h => ha (eq_inv_of_mul_eq_one_right ?_))
    (hC.2 c hc _ (hconj c hc g))
  rw [← hPP, h]
  rfl

theorem mem_swapSet_of_isSwap_right {f m : ℕ} (hf : 2 ≤ f) (hm : 5 ≤ m)
    {C : Set (CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f m)}
    (hC : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp C)
    (hconj : ∀ c ∈ C, ∀ g : CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f m, g * c * g⁻¹ ∈ C)
    {c : CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f m} (hc : c ∈ C) (hsw : c.right.IsSwap) :
    c ∈ WreathEndgame.swapSet f m := by
  obtain ⟨i, j, hij, hr⟩ := hsw
  have hcc : c * c = 1 := mul_self_eq_one_of_mem hC hc
  have hinv : c.right⁻¹ = swap i j := by rw [hr, swap_inv]
  have hij1 : c.left i * c.left j = 1 := by
    have h := left_mul_left_eq_one hcc i
    rwa [hinv, swap_apply_left] at h
  set y₀ : Fin m → PSL2Model f := Pi.mulSingle j (c.left i) with hy₀
  have hc₁ : inl y₀ * c * (inl y₀)⁻¹ ∈ C := hconj c hc _
  set c₁ : L2Wreath f m := inl y₀ * c * (inl y₀)⁻¹ with hc₁def
  have hr₁ : c₁.right = swap i j := by rw [hc₁def, inl_conj_right, hr]
  have hl₁i : c₁.left i = 1 := by
    rw [hc₁def, inl_conj_left, hinv, swap_apply_left, hy₀, Pi.mulSingle_eq_of_ne hij,
      Pi.mulSingle_eq_same, one_mul, mul_inv_cancel]
  have hl₁j : c₁.left j = 1 := by
    rw [hc₁def, inl_conj_left, hinv, swap_apply_right, hy₀, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne hij, inv_one, mul_one, hij1]
  have hl₁k : ∀ k, k ≠ i → k ≠ j → c₁.left k = c.left k := by
    intro k hki hkj
    rw [hc₁def, inl_conj_left, hinv, swap_apply_of_ne_of_ne hki hkj, hy₀,
      Pi.mulSingle_eq_of_ne hkj, inv_one, mul_one, one_mul]
  refine ⟨i, j, hij, hr, fun k hki hkj => ?_, eq_inv_of_mul_eq_one_right hij1⟩
  have h1 := left_eq_one_of_normalized hf (by omega) hC hconj hc₁ hij hr₁ hl₁i hl₁j hki hkj
  rwa [hl₁k k hki hkj] at h1

theorem sq_eq_one_of_cycleType {σ : Perm (Fin 6)} (h : σ.cycleType = Multiset.replicate 3 2) :
    σ * σ = 1 := by
  have h1 := Perm.lcm_cycleType σ
  rw [h] at h1
  have h2 : orderOf σ = 2 := by
    rw [← h1]
    decide
  have h3 := pow_orderOf_eq_one σ
  rwa [h2, pow_two] at h3

theorem ne_self_of_cycleType {σ : Perm (Fin 6)} (h : σ.cycleType = Multiset.replicate 3 2)
    (p : Fin 6) : σ p ≠ p := by
  have hs := Perm.sum_cycleType σ
  rw [h] at hs
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hs]
    simp
  have hp : p ∈ σ.support := by
    rw [hsupp]
    exact Finset.mem_univ p
  exact Perm.mem_support.1 hp

theorem pow_left_of_right_eq_one {P : L2Wreath f m} (hP : P.right = 1) (n : ℕ) (r : Fin m) :
    (P ^ n).left r = P.left r ^ n := by
  have h : P = inl P.left := by
    have := inl_left_mul_inr_right P
    rw [hP, map_one, mul_one] at this
    exact this.symm
  have h2 : P ^ n = inl (P.left ^ n) := by
    rw [map_pow, ← h]
  rw [h2, left_inl, Pi.pow_apply]

theorem left_mul_conj_inl {c : L2Wreath f m} (hcc : c * c = 1) (hσ : c.right * c.right = 1)
    (y : Fin m → PSL2Model f) (r : Fin m) :
    (c * (inl y * c * (inl y)⁻¹)).left r =
      c.left r * y (c.right r) * (c.left r)⁻¹ * (y r)⁻¹ := by
  have hσinv : c.right⁻¹ = c.right := inv_eq_of_mul_eq_one_right hσ
  have h1 := left_mul_left_eq_one hcc r
  rw [hσinv] at h1
  have h2 : c.left (c.right r) = (c.left r)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : c.right (c.right r) = r := by
    rw [← Perm.mul_apply, hσ]
    rfl
  rw [mul_left_apply, inl_conj_left, hσinv, h3, h2]
  group

theorem not_dvd_two_or_odd_of_base {P : L2Wreath f m} (hP : P.right = 1) {r s : Fin m}
    {x x' a b : PSL2Model f} (hr : P.left r = x * a * x⁻¹) (hs : P.left s = x' * b * x'⁻¹)
    (ha : a * a ≠ 1) (hb : b * b = 1) (hb1 : b ≠ 1) : ¬ (orderOf P ∣ 2 ∨ Odd (orderOf P)) := by
  rintro (h | ⟨k, hk⟩)
  · have h1 : (P ^ 2).left r = 1 := by rw [orderOf_dvd_iff_pow_eq_one.1 h]; rfl
    rw [pow_left_of_right_eq_one hP, hr, conj_pow, conj_eq_one_iff] at h1
    exact ha (by rwa [pow_two] at h1)
  · have h1 : (P ^ orderOf P).left s = 1 := by rw [pow_orderOf_eq_one]; rfl
    rw [pow_left_of_right_eq_one hP, hs, conj_pow, conj_eq_one_iff, hk] at h1
    have h2 : b ^ (2 * k + 1) = b := by
      rw [pow_succ, pow_mul, pow_two, hb, one_pow, one_mul]
    exact hb1 (h2 ▸ h1)

theorem not_triple_right {f : ℕ} (hf : 2 ≤ f)
    {C : Set (CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f 6)}
    (hC : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp C)
    (hconj : ∀ c ∈ C, ∀ g : CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f 6, g * c * g⁻¹ ∈ C)
    {c : CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f 6} (hc : c ∈ C) :
    c.right.cycleType ≠ Multiset.replicate 3 2 := by
  intro hcyc
  have hσσ : c.right * c.right = 1 := sq_eq_one_of_cycleType hcyc
  have hfix : ∀ p, c.right p ≠ p := ne_self_of_cycleType hcyc
  have hσσ' : ∀ p, c.right (c.right p) = p := fun p => by
    rw [← Perm.mul_apply, hσσ]
    rfl
  have hcc : c * c = 1 := mul_self_eq_one_of_mem hC hc
  obtain ⟨a, ha⟩ := exists_mul_self_ne_one hf
  obtain ⟨b, hb, hb1⟩ := WreathEndgame.exists_involution hf
  obtain ⟨u, v, hvu, hvσ⟩ : ∃ u v : Fin 6, v ≠ u ∧ v ≠ c.right u := by
    obtain ⟨v, hv1, hv2⟩ :=
      (by decide : ∀ u w : Fin 6, ∃ v : Fin 6, v ≠ u ∧ v ≠ w) 0 (c.right 0)
    exact ⟨0, v, hv1, hv2⟩
  have hσv : c.right v ≠ u := fun h => hvσ (by rw [← h, hσσ'])
  obtain ⟨y, hyu, hyv, hyσu, hyσv⟩ : ∃ y : Fin 6 → PSL2Model f, y u = a ∧ y v = b ∧
      y (c.right u) = 1 ∧ y (c.right v) = 1 := by
    refine ⟨Pi.mulSingle u a * Pi.mulSingle v b, ?_, ?_, ?_, ?_⟩
    · rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hvu.symm, mul_one]
    · rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hvu, one_mul]
    · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (hfix u), Pi.mulSingle_eq_of_ne hvσ.symm, one_mul]
    · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hσv, Pi.mulSingle_eq_of_ne (hfix v), one_mul]
  have hPu := left_mul_conj_inl hcc hσσ y (c.right u)
  have hPv := left_mul_conj_inl hcc hσσ y (c.right v)
  rw [hσσ', hyu, hyσu, inv_one, mul_one] at hPu
  rw [hσσ', hyv, hyσv, inv_one, mul_one] at hPv
  have hPr : (c * (inl y * c * (inl y)⁻¹)).right = 1 := by
    rw [mul_right, inl_conj_right, hσσ]
  exact not_dvd_two_or_odd_of_base hPr hPu hPv ha hb hb1 (hC.2 c hc _ (hconj c hc _))

end WreathClass

end CFSG.OddTranspositions.PartThree

end
