module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.WreathBase
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Timmesfeld.Bridge.Asc72WAct
import CFSG.Timmesfeld.Bridge.Asc72WreathConn

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.BenderSuzuki

namespace WreathEndgame

open Equiv SemidirectProduct

variable {f m k n : ℕ}

section Perm

variable {α : Type*} [DecidableEq α]

theorem swap_fixes_iff {a b p : α} (hab : a ≠ b) : swap a b p = p ↔ p ≠ a ∧ p ≠ b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [swap_apply_left] at h
      exact hab h.symm
    · rintro rfl
      rw [swap_apply_right] at h
      exact hab h
  · rintro ⟨h1, h2⟩
    exact swap_apply_of_ne_of_ne h1 h2

theorem swapDisjoint_iff {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l) :
    (swap i j).Disjoint (swap k l) ↔ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l := by
  constructor
  · intro h
    have hi : i ≠ k ∧ i ≠ l := by
      rcases h i with h' | h'
      · exact absurd ((swap_fixes_iff hij).1 h').1 (by simp)
      · exact (swap_fixes_iff hkl).1 h'
    have hj : j ≠ k ∧ j ≠ l := by
      rcases h j with h' | h'
      · exact absurd ((swap_fixes_iff hij).1 h').2 (by simp)
      · exact (swap_fixes_iff hkl).1 h'
    exact ⟨hi.1, hi.2, hj.1, hj.2⟩
  · rintro ⟨h1, h2, h3, h4⟩ x
    by_cases hxi : x = i
    · exact Or.inr ((swap_fixes_iff hkl).2 ⟨hxi ▸ h1, hxi ▸ h2⟩)
    by_cases hxj : x = j
    · exact Or.inr ((swap_fixes_iff hkl).2 ⟨hxj ▸ h3, hxj ▸ h4⟩)
    · exact Or.inl ((swap_fixes_iff hij).2 ⟨hxi, hxj⟩)

theorem swap_commute_cases [Fintype α] {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l)
    (h : Commute (swap i j) (swap k l)) :
    swap i j = swap k l ∨ (swap i j).Disjoint (swap k l) := by
  have hs := Perm.mem_support_iff_of_commute h
  rw [Perm.support_swap hkl] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  by_cases hfix : swap i j k = k
  · right
    have hl : swap i j l = l := by
      rcases (hs l).2 (Or.inr rfl) with h' | h'
      · exact absurd ((swap i j).injective (h'.trans hfix.symm)) hkl.symm
      · exact h'
    intro x
    by_cases hxk : x = k
    · exact Or.inl (hxk ▸ hfix)
    by_cases hxl : x = l
    · exact Or.inl (hxl ▸ hl)
    · exact Or.inr (swap_apply_of_ne_of_ne hxk hxl)
  · left
    have hkl' : swap i j k = l := by
      rcases (hs k).2 (Or.inl rfl) with h' | h'
      · exact absurd h' hfix
      · exact h'
    by_cases hki : k = i
    · subst hki
      rw [swap_apply_left] at hkl'
      subst hkl'
      rfl
    · by_cases hkj : k = j
      · subst hkj
        rw [swap_apply_right] at hkl'
        subst hkl'
        exact swap_comm _ _
      · exact absurd (swap_apply_of_ne_of_ne hki hkj) hfix

theorem swap_eq_swap_cases {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l) (h : swap i j = swap k l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hi : swap k l i ≠ i := by
    rw [← h, swap_apply_left]
    exact hij.symm
  have hi' : i = k ∨ i = l := by
    by_contra hcon
    push Not at hcon
    exact hi (swap_apply_of_ne_of_ne hcon.1 hcon.2)
  rcases hi' with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have := congrArg (fun σ => σ i) h
    simp only [swap_apply_left] at this
    exact this
  · right
    refine ⟨rfl, ?_⟩
    have := congrArg (fun σ => σ i) h
    simp only [swap_apply_left, swap_apply_right] at this
    exact this

omit [DecidableEq α] in
theorem disjoint_conj_of_commute {σ τ γ : Perm α} (h : σ.Disjoint τ) (hc : Commute γ τ) :
    (γ * σ * γ⁻¹).Disjoint τ := by
  intro p
  have hp : γ (γ⁻¹ p) = p := Equiv.apply_symm_apply γ p
  rcases h (γ⁻¹ p) with h1 | h1
  · left
    rw [Perm.mul_apply, Perm.mul_apply, h1, hp]
  · right
    have h2 : γ (τ (γ⁻¹ p)) = τ (γ (γ⁻¹ p)) := congrArg (fun w => w (γ⁻¹ p)) hc.eq
    rw [h1, hp] at h2
    exact h2.symm

end Perm

@[expose] def swapSet (f m : ℕ) : Set (L2Wreath f m) :=
  {x | ∃ i j : Fin m, i ≠ j ∧ x.right = swap i j ∧
    (∀ l, l ≠ i → l ≠ j → x.left l = 1) ∧ x.left j = (x.left i)⁻¹}

@[expose] def disjSwaps (f m : ℕ) (τ : Perm (Fin m)) : Set (L2Wreath f m) :=
  {x | x ∈ swapSet f m ∧ x.right.Disjoint τ}

@[expose] def sameSwaps (f m : ℕ) (τ : Perm (Fin m)) : Set (L2Wreath f m) :=
  {x | x ∈ swapSet f m ∧ x.right = τ}

@[expose] noncomputable def swp (a : PSL2Model f) (i j : Fin m) : L2Wreath f m :=
  ⟨Pi.mulSingle i a * Pi.mulSingle j a⁻¹, swap i j⟩

@[simp] theorem swp_right (a : PSL2Model f) (i j : Fin m) : (swp a i j).right = swap i j := rfl

theorem swp_left_fst {a : PSL2Model f} {i j : Fin m} (hij : i ≠ j) : (swp a i j).left i = a := by
  simp [swp, Pi.mulSingle_eq_of_ne hij]

theorem swp_left_snd {a : PSL2Model f} {i j : Fin m} (hij : i ≠ j) :
    (swp a i j).left j = a⁻¹ := by
  simp [swp, Pi.mulSingle_eq_of_ne hij.symm]

theorem swp_left_of_ne {a : PSL2Model f} {i j l : Fin m} (hli : l ≠ i) (hlj : l ≠ j) :
    (swp a i j).left l = 1 := by
  simp [swp, Pi.mulSingle_eq_of_ne hli, Pi.mulSingle_eq_of_ne hlj]

theorem swp_mem {a : PSL2Model f} {i j : Fin m} (hij : i ≠ j) : swp a i j ∈ swapSet f m :=
  ⟨i, j, hij, rfl, fun _ hli hlj => swp_left_of_ne hli hlj, by
    rw [swp_left_fst hij, swp_left_snd hij]⟩

theorem eq_swp {x : L2Wreath f m} {i j : Fin m} (hij : i ≠ j) (hx : x.right = swap i j)
    (h1 : ∀ l, l ≠ i → l ≠ j → x.left l = 1) (h2 : x.left j = (x.left i)⁻¹) :
    x = swp (x.left i) i j := by
  refine SemidirectProduct.ext (funext fun l => ?_) hx
  by_cases hli : l = i
  · subst hli
    exact (swp_left_fst hij).symm
  by_cases hlj : l = j
  · subst hlj
    rw [h2, swp_left_snd hij]
  · rw [h1 l hli hlj, swp_left_of_ne hli hlj]

theorem eq_swp_of_right_eq {x : L2Wreath f m} (hx : x ∈ swapSet f m) {i j : Fin m} (hij : i ≠ j)
    (hr : x.right = swap i j) : x = swp (x.left i) i j := by
  obtain ⟨u, v, huv, hxr, h1, h2⟩ := hx
  rw [hxr] at hr
  rcases swap_eq_swap_cases huv hij hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact eq_swp huv hxr h1 h2
  · exact eq_swp hij (hxr.trans (swap_comm _ _)) (fun l hl1 hl2 => h1 l hl2 hl1)
      (by rw [h2, inv_inv])

theorem swp_one_eq_inr (i j : Fin m) : swp (1 : PSL2Model f) i j = inr (swap i j) := by
  refine SemidirectProduct.ext (funext fun l => ?_) rfl
  simp [swp]

theorem inr_swap_mem_swapSet {i j : Fin m} (hij : i ≠ j) :
    (inr (swap i j) : L2Wreath f m) ∈ swapSet f m := by
  rw [← swp_one_eq_inr]
  exact swp_mem hij

theorem two_le_of_mem_swapSet {x : L2Wreath f m} (hx : x ∈ swapSet f m) : 2 ≤ m := by
  obtain ⟨i, j, hij, -⟩ := hx
  by_contra h
  apply hij
  have := i.isLt
  have := j.isLt
  exact Fin.ext (by omega)

theorem isConj_of_mem_swapSet {a b : Fin m} (hab : a ≠ b) {x : L2Wreath f m}
    (hx : x ∈ swapSet f m) : IsConj (inr (swap a b)) x :=
  (WreathConn.isConj_inr_swap_iff hab x).2 hx

theorem mem_swapSet_of_isConj {a b : Fin m} (hab : a ≠ b) {x : L2Wreath f m}
    (hx : IsConj (inr (swap a b)) x) : x ∈ swapSet f m :=
  (WreathConn.isConj_inr_swap_iff hab x).1 hx

theorem conj_mem_swapSet (g : L2Wreath f m) {x : L2Wreath f m} (hx : x ∈ swapSet f m) :
    g * x * g⁻¹ ∈ swapSet f m := by
  obtain ⟨i, j, hij, -⟩ := id hx
  exact mem_swapSet_of_isConj hij
    ((isConj_of_mem_swapSet hij hx).trans (isConj_iff.2 ⟨g, rfl⟩))

theorem commute_of_disjoint_right {x y : L2Wreath f m} (hx : x ∈ swapSet f m)
    (hy : y ∈ swapSet f m) (h : x.right.Disjoint y.right) : Commute x y := by
  obtain ⟨i, j, hij, hxr, hxl, -⟩ := hx
  obtain ⟨k, l, hkl, hyr, hyl, -⟩ := hy
  rw [hxr, hyr] at h
  obtain ⟨h1, h2, h3, h4⟩ := (swapDisjoint_iff hij hkl).1 h
  exact WreathConn.commute_of_disjoint hxr hxl hyr hyl h1 h2 h3 h4

section Class

variable {G : Type*} [Group G] {D : Set G}

theorem isConj_map_iff {H : Type*} [Group H] (Φ : G ≃* H) {a b : G} :
    IsConj (Φ a) (Φ b) ↔ IsConj a b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨Φ.symm c, Φ.injective ?_⟩
    simpa using hc
  · exact fun h => Φ.toMonoidHom.map_isConj h

theorem mem_D_iff_mem_swapSet (hS : Setup G D) (hm : 2 ≤ m) (Φ : G ≃* L2Wreath f m)
    (hΦ : ∀ u ∈ D, Φ u ∈ swapSet f m) (u : G) : u ∈ D ↔ Φ u ∈ swapSet f m := by
  refine ⟨hΦ u, fun hu => ?_⟩
  obtain ⟨u₀, hu₀⟩ := hS.nonempty
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h1 := isConj_of_mem_swapSet h01 (hΦ u₀ hu₀)
  have h2 := isConj_of_mem_swapSet h01 hu
  have h3 : IsConj u₀ u := (isConj_map_iff Φ).1 (h1.symm.trans h2)
  rw [hS.eq_setOf_isConj hu₀]
  exact h3

theorem exists_mem_D_right_eq (hS : Setup G D) (hm : 2 ≤ m) (Φ : G ≃* L2Wreath f m)
    (hΦ : ∀ u ∈ D, Φ u ∈ swapSet f m) {a b : Fin m} (hab : a ≠ b) :
    ∃ u ∈ D, (Φ u).right = swap a b := by
  refine ⟨Φ.symm (inr (swap a b)), ?_, by simp⟩
  rw [mem_D_iff_mem_swapSet hS hm Φ hΦ, MulEquiv.apply_symm_apply]
  exact inr_swap_mem_swapSet hab

theorem reach_invariant {P : G → Prop}
    (hP : ∀ b c, b ∈ D → c ∈ D → Commute b c → P b → P c) {x y : G} (h : Reach D x y) :
    P x → P y := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hx => hP _ _ hbc.1 hbc.2.1 hbc.2.2 (ih hx)

theorem false_of_invariant (hS : Setup G D) (hconn : ¬ Disconnected D)
    (hm : 2 ≤ m) (Φ : G ≃* L2Wreath f m) (hΦ : ∀ u ∈ D, Φ u ∈ swapSet f m)
    (Z : Perm (Fin m) → Prop)
    (hZ : ∀ i j k l : Fin m, i ≠ j → k ≠ l → swap i j * swap k l = swap k l * swap i j →
      Z (swap i j) → Z (swap k l))
    {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) (h1 : Z (swap a b)) (h2 : ¬ Z (swap c d)) :
    False := by
  obtain ⟨u, hu, hur⟩ := exists_mem_D_right_eq hS hm Φ hΦ hab
  obtain ⟨v, hv, hvr⟩ := exists_mem_D_right_eq hS hm Φ hΦ hcd
  have hreach : Reach D u v := by
    by_contra hr
    exact hconn ⟨u, hu, v, hv, hr⟩
  have key := reach_invariant (P := fun w => Z (Φ w).right) ?_ hreach (by simpa [hur] using h1)
  · exact h2 (by simpa [hvr] using key)
  · intro b' c' hb hc hbc hZb
    obtain ⟨i, j, hij, hbr, -⟩ := hΦ b' hb
    obtain ⟨k, l, hkl, hcr, -⟩ := hΦ c' hc
    have hcomm : (Φ b').right * (Φ c').right = (Φ c').right * (Φ b').right := by
      have := congrArg (fun w => (Φ w).right) hbc.eq
      simpa using this
    rw [hbr, hcr] at hcomm
    rw [hbr] at hZb
    rw [hcr]
    exact hZ i j k l hij hkl hcomm hZb

theorem three_cases : ∀ i j k l : Fin 3, i ≠ j → k ≠ l →
    swap i j * swap k l = swap k l * swap i j →
    swap i j = swap 0 1 → swap k l = swap 0 1 := by decide

theorem four_cases : ∀ i j k l : Fin 4, i ≠ j → k ≠ l →
    swap i j * swap k l = swap k l * swap i j →
    (swap i j = swap 0 1 ∨ swap i j = swap 2 3) →
    (swap k l = swap 0 1 ∨ swap k l = swap 2 3) := by decide

theorem false_of_three_four (hS : Setup G D) (hconn : ¬ Disconnected D) (hm : m = 3 ∨ m = 4)
    (Φ : G ≃* L2Wreath f m) (hΦ : ∀ u ∈ D, Φ u ∈ swapSet f m) : False := by
  rcases hm with rfl | rfl
  · exact false_of_invariant hS hconn (by norm_num) Φ hΦ (fun σ => σ = swap 0 1)
      three_cases (a := 0) (b := 1) (c := 0) (d := 2) (by decide) (by decide) rfl (by decide)
  · exact false_of_invariant hS hconn (by norm_num) Φ hΦ
      (fun σ => σ = swap 0 1 ∨ σ = swap 2 3)
      four_cases (a := 0) (b := 1) (c := 0) (d := 2) (by decide) (by decide) (Or.inl rfl)
      (by decide)

end Class

theorem mul_self_eq_one_of_pow_four (hf : 2 ≤ f) {l : PSL2Model f} (h : l ^ 4 = 1) :
    l * l = 1 := by
  have hB : IsBenderGroup (PSL2Model f) := .isPSL2 f hf (MulEquiv.refl _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (show orderOf l ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one h)
  have hp : IsPGroup 2 (Subgroup.zpowers l) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hlQ : l ∈ (Q : Subgroup (PSL2Model f)) := hQ (Subgroup.mem_zpowers l)
  exact IsBenderGroup.mul_self_eq_one_of_commute hB Q hlQ
    (fun y hy => IsBenderGroup.commute_of_psl2 hf (MulEquiv.refl _) Q l hlQ y hy)

theorem exists_involution (hf : 2 ≤ f) : ∃ t : PSL2Model f, t * t = 1 ∧ t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.closure {t : PSL2Model f | t * t = 1} ≤ ⊥ := by
    rw [Subgroup.closure_le]
    intro t ht
    exact Subgroup.mem_bot.2 (hcon t ht)
  rw [WreathConn.closure_mul_self_eq_one_eq_top hf] at hle
  have := psl2Model_nontrivial hf
  obtain ⟨x, hx⟩ := exists_ne (1 : PSL2Model f)
  exact hx (Subgroup.mem_bot.1 (hle (Subgroup.mem_top x)))

theorem pair_mul_self_eq_one {t : PSL2Model f} (ht : t * t = 1) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) :
    (Pi.mulSingle i₀ t * Pi.mulSingle i₁ t : Fin n → PSL2Model f) *
      (Pi.mulSingle i₀ t * Pi.mulSingle i₁ t) = 1 := by
  have hc : Commute (Pi.mulSingle i₁ t : Fin n → PSL2Model f) (Pi.mulSingle i₀ t) :=
    Pi.mulSingle_commute (f := fun _ : Fin n => PSL2Model f) hi.symm t t
  have h1 : (Pi.mulSingle i₀ t : Fin n → PSL2Model f) * Pi.mulSingle i₀ t = 1 := by
    rw [← Pi.mulSingle_mul, ht, Pi.mulSingle_one]
  have h2 : (Pi.mulSingle i₁ t : Fin n → PSL2Model f) * Pi.mulSingle i₁ t = 1 := by
    rw [← Pi.mulSingle_mul, ht, Pi.mulSingle_one]
  calc (Pi.mulSingle i₀ t * Pi.mulSingle i₁ t : Fin n → PSL2Model f) *
        (Pi.mulSingle i₀ t * Pi.mulSingle i₁ t)
      = Pi.mulSingle i₀ t * Pi.mulSingle i₀ t * (Pi.mulSingle i₁ t * Pi.mulSingle i₁ t) :=
        hc.mul_mul_mul_comm _ _
    _ = 1 := by rw [h1, h2, mul_one]

theorem exists_orderOf_four (hf : 2 ≤ f) (hn : 2 ≤ n) :
    ∃ w : L2Wreath f n, orderOf w = 4 := by
  obtain ⟨t, ht, ht1⟩ := exists_involution hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let w : L2Wreath f n := ⟨Pi.mulSingle i₀ t, swap i₀ i₁⟩
  let u : Fin n → PSL2Model f := Pi.mulSingle i₀ t * Pi.mulSingle i₁ t
  have hww : w * w = inl u := by
    refine SemidirectProduct.ext ?_ (by simp [w])
    simp only [mul_left, left_inl]
    show Pi.mulSingle i₀ t * (permAct (Fin n) (PSL2Model f) (swap i₀ i₁)) (Pi.mulSingle i₀ t) = u
    rw [WreathAct.permAct_mulSingle, swap_apply_left]
  have hu1 : u ≠ 1 := by
    intro h
    have := congrFun h i₀
    simp only [u, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi, mul_one,
      Pi.one_apply] at this
    exact ht1 this
  refine ⟨w, ?_⟩
  have h4 : orderOf w = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1)
      (by rw [pow_one, pow_two, hww]; exact fun h => hu1 (inl_injective (by rwa [map_one])))
      (by
        rw [show w ^ 2 ^ (1 + 1) = (w * w) * (w * w) by
          rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two], hww, ← map_mul,
          pair_mul_self_eq_one ht hi, map_one])
  simpa using h4

theorem base_mul_self_eq_one (hf : 2 ≤ f) {y : L2Wreath f n} (hy1 : y.right = 1)
    (h : y * y * (y * y) = 1) : y * y = 1 := by
  have hyl : y = inl y.left := by
    have := inl_left_mul_inr_right y
    rw [hy1, map_one, mul_one] at this
    exact this.symm
  have hbase : ∀ l, y.left l * y.left l = 1 := by
    intro l
    apply mul_self_eq_one_of_pow_four hf
    rw [hyl] at h
    have h2 := congrFun (congrArg SemidirectProduct.left h) l
    simp only [mul_left, mul_right, left_inl, right_inl, mul_one, map_one, MulAut.one_apply,
      Pi.mul_apply, one_left, Pi.one_apply] at h2
    calc y.left l ^ 4 = y.left l * y.left l * (y.left l * y.left l) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h2
  rw [hyl]
  refine SemidirectProduct.ext ?_ (by simp)
  funext l
  simp only [mul_left, left_inl, right_inl, map_one, MulAut.one_apply, Pi.mul_apply, one_left,
    Pi.one_apply]
  exact hbase l

theorem exists_base_sq_eq {d x : L2Wreath f 2} (hd : d ∈ swapSet f 2) (hdd : d * d = 1)
    (hx : Commute x d) : ∃ y : L2Wreath f 2, y.right = 1 ∧ y * y = x * x := by
  have hperm : ∀ σ : Perm (Fin 2), σ = 1 ∨ σ = swap 0 1 := by decide
  have hdr : d.right = swap 0 1 := by
    obtain ⟨i, j, hij, hr, -⟩ := hd
    have : ∀ i j : Fin 2, i ≠ j → swap i j = swap 0 1 := by decide
    rw [hr]
    exact this i j hij
  rcases hperm x.right with h | h
  · exact ⟨x, h, rfl⟩
  · refine ⟨x * d, ?_, ?_⟩
    · rw [mul_right, h, hdr, swap_mul_self]
    · calc x * d * (x * d) = x * (d * x) * d := by group
        _ = x * (x * d) * d := by rw [hx.eq.symm]
        _ = x * x * (d * d) := by group
        _ = x * x := by rw [hdd, mul_one]

theorem orderOf_ne_four_of_commute_swap (hf : 2 ≤ f) {d x : L2Wreath f 2}
    (hd : d ∈ swapSet f 2) (hdd : d * d = 1) (hx : Commute x d) : orderOf x ≠ 4 := by
  intro h4
  obtain ⟨y, hy1, hyy⟩ := exists_base_sq_eq hd hdd hx
  have hx4 : x * x * (x * x) = 1 := by
    have : x ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one x
    calc x * x * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hyy1 : y * y = 1 := base_mul_self_eq_one hf hy1 (by rw [hyy]; exact hx4)
  have hxx : x ^ 2 = 1 := by rw [pow_two, ← hyy]; exact hyy1
  have := orderOf_dvd_of_pow_eq_one hxx
  rw [h4] at this
  omega

section Halpha

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_d_of_mem_Halpha (hC : HypothesisC D) {y : G} (hy : y ∈ Halpha D hC.alpha) :
    Commute y hC.d :=
  Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_d hC hy)

theorem false_of_two (hC : HypothesisC D) {f n : ℕ} (hH : TenHyp hC f n) {f' : ℕ}
    (hf' : 2 ≤ f') (Φ : G ≃* L2Wreath f' 2) (hΦ : ∀ u ∈ D, Φ u ∈ swapSet f' 2) : False := by
  obtain ⟨e⟩ := hH.iso
  obtain ⟨w, hw⟩ := exists_orderOf_four hH.two_le (by have := hH.five_le; omega : 2 ≤ n)
  obtain ⟨q, hq⟩ := e.surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have h4 : 4 ∣ orderOf x := by
    have := orderOf_map_dvd (e.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha)))) x
    simpa [hq, hw] using this
  have hne : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hy : orderOf (x ^ (orderOf x / 4)) = 4 := orderOf_pow_orderOf_div hne h4
  set y : Halpha D hC.alpha := x ^ (orderOf x / 4) with hydef
  have hcomm : Commute (y : G) hC.d := commute_d_of_mem_Halpha hC y.2
  have hdd : hC.d * hC.d = 1 := by
    have h2 := hC.setup.oddT.1 hC.d hC.hd
    have := pow_orderOf_eq_one hC.d
    rwa [h2, pow_two] at this
  refine orderOf_ne_four_of_commute_swap hf' (hΦ hC.d hC.hd) (by rw [← map_mul, hdd, map_one])
    (hcomm.map Φ) ?_
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]

end Halpha

section Embedding

variable (f) in
theorem wreathExt_compat (ε : Fin k ↪ Fin m) (g : Perm (Fin k)) :
    (Function.ExtendByOne.hom (PSL2Model f) ε).comp
        (permAct (Fin k) (PSL2Model f) g).toMonoidHom =
      (permAct (Fin m) (PSL2Model f) (Equiv.Perm.viaEmbeddingHom ε g)).toMonoidHom.comp
        (Function.ExtendByOne.hom (PSL2Model f) ε) := by
  ext h p
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Function.ExtendByOne.hom_apply]
  show Function.extend ε (fun a => h (g⁻¹ a)) 1 p =
    Function.extend ε h 1 ((Equiv.Perm.viaEmbeddingHom ε g)⁻¹ p)
  rw [← map_inv]
  by_cases hp : ∃ a, ε a = p
  · obtain ⟨a, rfl⟩ := hp
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply, ε.injective.extend_apply,
      ε.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hp, Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ (by simpa using hp),
      Function.extend_apply' _ _ _ hp]

variable (f) in
@[expose] noncomputable def wreathExt (ε : Fin k ↪ Fin m) : L2Wreath f k →* L2Wreath f m :=
  SemidirectProduct.map (Function.ExtendByOne.hom (PSL2Model f) ε)
    (Equiv.Perm.viaEmbeddingHom ε) (wreathExt_compat f ε)

theorem wreathExt_left (ε : Fin k ↪ Fin m) (x : L2Wreath f k) :
    (wreathExt f ε x).left = Function.extend ε x.left 1 := rfl

theorem wreathExt_right (ε : Fin k ↪ Fin m) (x : L2Wreath f k) :
    (wreathExt f ε x).right = x.right.viaEmbedding ε := rfl

theorem wreathExt_injective (ε : Fin k ↪ Fin m) : Function.Injective (wreathExt f ε) := by
  intro x y hxy
  refine SemidirectProduct.ext ?_ ?_
  · funext a
    have := congrFun (congrArg SemidirectProduct.left hxy) (ε a)
    rwa [wreathExt_left, wreathExt_left, ε.injective.extend_apply, ε.injective.extend_apply] at this
  · exact Equiv.Perm.viaEmbeddingHom_injective ε (congrArg SemidirectProduct.right hxy)

theorem wreathExt_swp (ε : Fin k ↪ Fin m) (a : PSL2Model f) (p q : Fin k) :
    wreathExt f ε (swp a p q) = swp a (ε p) (ε q) := by
  refine SemidirectProduct.ext ?_ ?_
  · funext u
    rw [wreathExt_left]
    by_cases hu : ∃ r, ε r = u
    · obtain ⟨r, rfl⟩ := hu
      rw [ε.injective.extend_apply]
      simp [swp, Pi.mulSingle_apply, ε.injective.eq_iff]
    · rw [Function.extend_apply' _ _ _ hu]
      have h1 : u ≠ ε p := fun h => hu ⟨p, h.symm⟩
      have h2 : u ≠ ε q := fun h => hu ⟨q, h.symm⟩
      simp [swp, Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h2]
  · refine Equiv.ext fun u => ?_
    rw [wreathExt_right, swp_right, swp_right]
    by_cases hu : ∃ r, ε r = u
    · obtain ⟨r, rfl⟩ := hu
      rw [Equiv.Perm.viaEmbedding_apply, ε.injective.swap_apply]
    · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ (by simpa using hu)]
      have h1 : u ≠ ε p := fun h => hu ⟨p, h.symm⟩
      have h2 : u ≠ ε q := fun h => hu ⟨q, h.symm⟩
      exact (swap_apply_of_ne_of_ne h1 h2).symm

theorem exists_embedding_range {i j : Fin (k + 2)} (hij : i ≠ j) :
    ∃ ε : Fin k ↪ Fin (k + 2), ∀ p, p ∈ Set.range ε ↔ p ≠ i ∧ p ≠ j := by
  classical
  have hcard : Fintype.card {p : Fin (k + 2) // p ≠ i ∧ p ≠ j} = k := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun p : Fin (k + 2) => p ≠ i ∧ p ≠ j) =
        ({i, j} : Finset (Fin (k + 2)))ᶜ := by
      ext p
      simp
    rw [this, Finset.card_compl, Finset.card_pair hij, Fintype.card_fin]
    omega
  let e : Fin k ≃ {p : Fin (k + 2) // p ≠ i ∧ p ≠ j} := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype _), fun p => ?_⟩
  constructor
  · rintro ⟨a, rfl⟩
    exact (e a).2
  · intro hp
    obtain ⟨a, ha⟩ := e.surjective ⟨p, hp⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩

theorem image_wreathExt_swapSet (ε : Fin k ↪ Fin m) {i₀ j₀ : Fin m} (hij : i₀ ≠ j₀)
    (hε : ∀ p, p ∈ Set.range ε ↔ p ≠ i₀ ∧ p ≠ j₀) :
    wreathExt f ε '' swapSet f k = disjSwaps f m (swap i₀ j₀) := by
  ext x
  constructor
  · rintro ⟨x', ⟨p, q, hpq, hr, h1, h2⟩, rfl⟩
    have hx' := eq_swp hpq hr h1 h2
    rw [hx', wreathExt_swp]
    refine ⟨swp_mem (ε.injective.ne hpq), ?_⟩
    rw [swp_right]
    have hp := (hε (ε p)).1 ⟨p, rfl⟩
    have hq := (hε (ε q)).1 ⟨q, rfl⟩
    exact (swapDisjoint_iff (ε.injective.ne hpq) hij).2 ⟨hp.1, hp.2, hq.1, hq.2⟩
  · rintro ⟨hxS, hxd⟩
    obtain ⟨u, v, huv, hr, h1, h2⟩ := hxS
    rw [hr] at hxd
    obtain ⟨hu1, hu2, hv1, hv2⟩ := (swapDisjoint_iff huv hij).1 hxd
    obtain ⟨p, rfl⟩ := (hε u).2 ⟨hu1, hu2⟩
    obtain ⟨q, rfl⟩ := (hε v).2 ⟨hv1, hv2⟩
    have hpq : p ≠ q := fun h => huv (h ▸ rfl)
    refine ⟨swp (x.left (ε p)) p q, swp_mem hpq, ?_⟩
    rw [wreathExt_swp]
    exact (eq_swp huv hr h1 h2).symm

end Embedding

theorem finite_l2Wreath (f m : ℕ) : Finite (L2Wreath f m) := WreathAct.finite_wreath

attribute [local instance] finite_l2Wreath

theorem exists_isMinimalNormal_le {W : Type*} [Group W] [Finite W] {K : Subgroup W}
    (hK : K.Normal) (hK0 : K ≠ ⊥) : ∃ N ≤ K, Asc72.IsMinimalNormal N := by
  obtain ⟨N, hNK, hNmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun N : Subgroup W => N.Normal ∧ N ≠ ⊥) K ⟨hK, hK0⟩
  refine ⟨N, hNK, hNmin.prop.1, hNmin.prop.2, fun N' hN' hN'N => ?_⟩
  by_cases hN1 : N' = ⊥
  · exact Or.inl hN1
  · exact Or.inr (le_antisymm hN'N (hNmin.2 ⟨hN', hN1⟩ hN'N))

theorem normal_closure_swapSet (hk : 2 ≤ k) : (Subgroup.closure (swapSet f k)).Normal := by
  have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hsub : Group.conjugatesOfSet (swapSet f k) ⊆ swapSet f k := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    exact mem_swapSet_of_isConj h01 ((isConj_of_mem_swapSet h01 ha).trans hax)
  have hnc : Subgroup.closure (swapSet f k) = Subgroup.normalClosure (swapSet f k) :=
    le_antisymm ((Subgroup.closure_le _).2 Subgroup.subset_normalClosure)
      (Subgroup.closure_mono hsub)
  rw [hnc]
  exact Subgroup.normalClosure_normal

theorem closure_swapSet_ne_bot (hk : 2 ≤ k) : Subgroup.closure (swapSet f k) ≠ ⊥ := by
  have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  intro h
  have hmem : (inr (swap (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩) : L2Wreath f k) ∈
      Subgroup.closure (swapSet f k) := Subgroup.subset_closure (inr_swap_mem_swapSet h01)
  rw [h, Subgroup.mem_bot] at hmem
  have := congrArg SemidirectProduct.right hmem
  simp only [right_inr, one_right] at this
  exact h01 (swap_eq_one_iff.1 this)

theorem inr_mem_closure_swapSet (σ : Perm (Fin k)) :
    (inr σ : L2Wreath f k) ∈ Subgroup.closure (swapSet f k) := by
  have hσ : σ ∈ Subgroup.closure {τ : Perm (Fin k) | τ.IsSwap} := by
    rw [Perm.closure_isSwap]
    trivial
  have hle : Subgroup.closure {τ : Perm (Fin k) | τ.IsSwap} ≤
      (Subgroup.closure (swapSet f k)).comap inr := by
    rw [Subgroup.closure_le]
    rintro τ ⟨x, y, hxy, rfl⟩
    exact Subgroup.subset_closure (inr_swap_mem_swapSet hxy)
  exact hle hσ

theorem closure_swapSet_eq_top (hf : 2 ≤ f) (hk : 2 ≤ k) :
    Subgroup.closure (swapSet f k) = ⊤ := by
  obtain ⟨N, hNK, hN⟩ := exists_isMinimalNormal_le (normal_closure_swapSet hk)
    (closure_swapSet_ne_bot hk)
  have hNB : N = l2WreathBase f k := eq_l2WreathBase_of_isMinimalNormal hf hk hN
  have hbase : l2WreathBase f k ≤ Subgroup.closure (swapSet f k) := hNB ▸ hNK
  refine eq_top_iff.2 fun w _ => ?_
  rw [← inl_left_mul_inr_right w]
  exact Subgroup.mul_mem _ (hbase ⟨w.left, rfl⟩) (inr_mem_closure_swapSet _)

theorem ncard_sameSwaps_le {i₀ j₀ : Fin m} (hij : i₀ ≠ j₀) :
    (sameSwaps f m (swap i₀ j₀)).ncard ≤ Nat.card (PSL2Model f) := by
  rw [← Set.ncard_univ]
  refine Set.ncard_le_ncard_of_injOn (fun x => x.left i₀) (fun _ _ => Set.mem_univ _) ?_
    Set.finite_univ
  intro x hx x' hx' h
  calc x = swp (x.left i₀) i₀ j₀ := eq_swp_of_right_eq hx.1 hij hx.2
    _ = swp (x'.left i₀) i₀ j₀ := by rw [show x.left i₀ = x'.left i₀ from h]
    _ = x' := (eq_swp_of_right_eq hx'.1 hij hx'.2).symm

theorem card_lt_ncard_swapSet (hk : 3 ≤ k) :
    Nat.card (PSL2Model f) < (swapSet f k).ncard := by
  let p : Fin k := ⟨0, by omega⟩
  let q : Fin k := ⟨1, by omega⟩
  let r : Fin k := ⟨2, by omega⟩
  have hpq : p ≠ q := by simp [p, q, Fin.ext_iff]
  have hpr : p ≠ r := by simp [p, r, Fin.ext_iff]
  have hqr : q ≠ r := by simp [q, r, Fin.ext_iff]
  let T : Set (L2Wreath f k) := Set.range fun a : PSL2Model f => swp a p q
  have hTinj : Function.Injective fun a : PSL2Model f => swp a p q := by
    intro a b hab
    have := congrArg (fun w => w.left p) hab
    simpa [swp_left_fst hpq] using this
  have hT : T.ncard = Nat.card (PSL2Model f) := by
    show (Set.range fun a : PSL2Model f => swp a p q).ncard = _
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hTinj, Set.ncard_univ]
  have hnot : swp (1 : PSL2Model f) p r ∉ T := by
    rintro ⟨a, ha⟩
    have := congrArg SemidirectProduct.right ha
    simp only [swp_right] at this
    rcases swap_eq_swap_cases hpq hpr this with ⟨-, h⟩ | ⟨h, -⟩
    · exact hqr h
    · exact hpr h
  have hsub : insert (swp (1 : PSL2Model f) p r) T ⊆ swapSet f k := by
    rintro x (rfl | ⟨a, rfl⟩)
    · exact swp_mem hpr
    · exact swp_mem hpq
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hnot (Set.toFinite _), hT] at this
  omega

section CommSet

variable {d : L2Wreath f m} {i₀ j₀ : Fin m}

theorem commSet_subset_union (hij : i₀ ≠ j₀) (hdr : d.right = swap i₀ j₀) {x : L2Wreath f m}
    (hx : x ∈ commSet (swapSet f m) d) :
    x ∈ disjSwaps f m (swap i₀ j₀) ∨ x ∈ sameSwaps f m (swap i₀ j₀) := by
  obtain ⟨hxS, hxc, -⟩ := hx
  obtain ⟨u, v, huv, hxr, -⟩ := id hxS
  have hc : Commute x.right d.right := hxc.map SemidirectProduct.rightHom
  rw [hxr, hdr] at hc
  rcases swap_commute_cases huv hij hc with h | h
  · exact Or.inr ⟨hxS, hxr.trans h⟩
  · exact Or.inl ⟨hxS, hxr ▸ h⟩

theorem disjSwaps_subset_commSet (hij : i₀ ≠ j₀) (hd : d ∈ swapSet f m)
    (hdr : d.right = swap i₀ j₀) : disjSwaps f m (swap i₀ j₀) ⊆ commSet (swapSet f m) d := by
  rintro x ⟨hxS, hxd⟩
  refine ⟨hxS, commute_of_disjoint_right hxS hd (hdr ▸ hxd), ?_⟩
  rintro rfl
  rw [hdr] at hxd
  exact hij (swap_eq_one_iff.1 (Perm.disjoint_refl_iff.1 hxd))

theorem commute_of_mem_closure_commSet {G' : Type*} [Group G'] {D' : Set G'} {d' g : G'}
    (hg : g ∈ Subgroup.closure (commSet D' d')) : Commute g d' := by
  have hle : Subgroup.closure (commSet D' d') ≤ Subgroup.centralizer {d'} := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hz.2.1.eq.symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hg) d' rfl).symm

theorem commute_right_of_mem_closure_commSet (hdr : d.right = swap i₀ j₀) {g : L2Wreath f m}
    (hg : g ∈ Subgroup.closure (commSet (swapSet f m) d)) : Commute g.right (swap i₀ j₀) := by
  have h : Commute g.right d.right :=
    (commute_of_mem_closure_commSet hg).map SemidirectProduct.rightHom
  rwa [hdr] at h

theorem conj_mem_disjSwaps {g x : L2Wreath f m} {τ : Perm (Fin m)} (hg : Commute g.right τ)
    (hx : x ∈ disjSwaps f m τ) : g * x * g⁻¹ ∈ disjSwaps f m τ := by
  refine ⟨conj_mem_swapSet g hx.1, ?_⟩
  simpa only [mul_right, inv_right] using disjoint_conj_of_commute hx.2 hg

theorem conj_mem_sameSwaps {g x : L2Wreath f m} {τ : Perm (Fin m)} (hg : Commute g.right τ)
    (hx : x ∈ sameSwaps f m τ) : g * x * g⁻¹ ∈ sameSwaps f m τ := by
  refine ⟨conj_mem_swapSet g hx.1, ?_⟩
  have h : (g * x * g⁻¹).right = g.right * τ * g.right⁻¹ := by
    simp only [mul_right, inv_right, hx.2]
  rw [h, hg.eq, mul_inv_cancel_right]

theorem exists_conj_mem_closure_commSet (hf : 2 ≤ f) (hk : 2 ≤ k) (ε : Fin k ↪ Fin m)
    (hij : i₀ ≠ j₀) (hε : ∀ p, p ∈ Set.range ε ↔ p ≠ i₀ ∧ p ≠ j₀) (hd : d ∈ swapSet f m)
    (hdr : d.right = swap i₀ j₀) {e y : L2Wreath f m} (he : e ∈ disjSwaps f m (swap i₀ j₀))
    (hy : y ∈ disjSwaps f m (swap i₀ j₀)) :
    ∃ g ∈ Subgroup.closure (commSet (swapSet f m) d), y = g * e * g⁻¹ := by
  have himg : wreathExt f ε '' swapSet f k = disjSwaps f m (swap i₀ j₀) :=
    image_wreathExt_swapSet ε hij hε
  rw [← himg] at he hy
  obtain ⟨e', he', rfl⟩ := he
  obtain ⟨y', hy', rfl⟩ := hy
  have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨c, hc⟩ := isConj_iff.1
    ((isConj_of_mem_swapSet h01 he').symm.trans (isConj_of_mem_swapSet h01 hy'))
  refine ⟨wreathExt f ε c, ?_, ?_⟩
  · have hmem : wreathExt f ε c ∈ Subgroup.closure (wreathExt f ε '' swapSet f k) := by
      rw [← MonoidHom.map_closure, closure_swapSet_eq_top hf hk]
      exact ⟨c, Subgroup.mem_top c, rfl⟩
    refine Subgroup.closure_mono ?_ hmem
    rw [himg]
    exact disjSwaps_subset_commSet hij hd hdr
  · rw [← hc, map_mul, map_mul, map_inv]

theorem orbitIn_disjSwaps (hf : 2 ≤ f) (hk : 2 ≤ k) (ε : Fin k ↪ Fin m) (hij : i₀ ≠ j₀)
    (hε : ∀ p, p ∈ Set.range ε ↔ p ≠ i₀ ∧ p ≠ j₀) (hd : d ∈ swapSet f m)
    (hdr : d.right = swap i₀ j₀) {e : L2Wreath f m} (he : e ∈ disjSwaps f m (swap i₀ j₀)) :
    orbitIn (swapSet f m) d e = disjSwaps f m (swap i₀ j₀) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_disjSwaps (commute_right_of_mem_closure_commSet hdr hg) he
  · intro y hy
    obtain ⟨g, hg, hyg⟩ := exists_conj_mem_closure_commSet hf hk ε hij hε hd hdr he hy
    exact ⟨g, hg, hyg⟩

theorem eq_disjSwaps_of_isMaxOrbit (hf : 2 ≤ f) (hk : 3 ≤ k) (ε : Fin k ↪ Fin m)
    (hij : i₀ ≠ j₀) (hε : ∀ p, p ∈ Set.range ε ↔ p ≠ i₀ ∧ p ≠ j₀) (hd : d ∈ swapSet f m)
    (hdr : d.right = swap i₀ j₀) {E : Set (L2Wreath f m)}
    (hE : IsMaxOrbit (swapSet f m) d E) : E = disjSwaps f m (swap i₀ j₀) := by
  have himg := image_wreathExt_swapSet (f := f) ε hij hε
  have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨e₀, he₀⟩ : (disjSwaps f m (swap i₀ j₀)).Nonempty := by
    rw [← himg]
    exact ⟨_, ⟨_, inr_swap_mem_swapSet h01, rfl⟩⟩
  obtain ⟨e, heA, hEe, hmax⟩ := hE
  have hXcard : (disjSwaps f m (swap i₀ j₀)).ncard = (swapSet f k).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ (wreathExt_injective ε)]
  have hlt := card_lt_ncard_swapSet (f := f) hk
  have hXle : (disjSwaps f m (swap i₀ j₀)).ncard ≤ E.ncard := by
    have := hmax e₀ (disjSwaps_subset_commSet hij hd hdr he₀)
    rwa [orbitIn_disjSwaps hf (by omega) ε hij hε hd hdr he₀] at this
  rcases commSet_subset_union hij hdr heA with hXe | hYe
  · rw [hEe, orbitIn_disjSwaps hf (by omega) ε hij hε hd hdr hXe]
  · exfalso
    have hEsub : E ⊆ sameSwaps f m (swap i₀ j₀) := by
      rw [hEe]
      rintro _ ⟨g, hg, rfl⟩
      exact conj_mem_sameSwaps (commute_right_of_mem_closure_commSet hdr hg) hYe
    have h1 := Set.ncard_le_ncard hEsub (Set.toFinite _)
    have h2 := ncard_sameSwaps_le (f := f) (m := m) hij
    omega

theorem closure_disjSwaps_eq_range (hf : 2 ≤ f) (hk : 2 ≤ k) (ε : Fin k ↪ Fin m)
    (hij : i₀ ≠ j₀) (hε : ∀ p, p ∈ Set.range ε ↔ p ≠ i₀ ∧ p ≠ j₀) :
    Subgroup.closure (disjSwaps f m (swap i₀ j₀)) = (wreathExt f ε).range := by
  rw [← image_wreathExt_swapSet ε hij hε, ← MonoidHom.map_closure, closure_swapSet_eq_top hf hk,
    ← MonoidHom.range_eq_map]

theorem closure_maxOrbit_equiv (hf : 2 ≤ f) (hk : 3 ≤ k) {d : L2Wreath f (k + 2)}
    (hd : d ∈ swapSet f (k + 2)) {E : Set (L2Wreath f (k + 2))}
    (hE : IsMaxOrbit (swapSet f (k + 2)) d E) :
    Nonempty (Subgroup.closure E ≃* L2Wreath f k) := by
  obtain ⟨i₀, j₀, hij, hdr, -⟩ := id hd
  obtain ⟨ε, hε⟩ := exists_embedding_range (k := k) hij
  rw [eq_disjSwaps_of_isMaxOrbit hf hk ε hij hε hd hdr hE,
    closure_disjSwaps_eq_range hf (by omega) ε hij hε]
  exact ⟨(MonoidHom.ofInjective (wreathExt_injective ε)).symm⟩

end CommSet

section Transport

variable {G G' : Type*} [Group G] [Group G'] {D : Set G}

theorem closure_image_mulEquiv (Φ : G ≃* G') (S : Set G) :
    Subgroup.closure (Φ '' S) = (Subgroup.closure S).map Φ.toMonoidHom :=
  (MonoidHom.map_closure Φ.toMonoidHom S).symm

theorem commSet_map (Φ : G ≃* G') {D' : Set G'} (hD : ∀ u, u ∈ D ↔ Φ u ∈ D') (d : G) :
    commSet D' (Φ d) = Φ '' commSet D d := by
  ext y
  constructor
  · rintro ⟨hy, hc, hne⟩
    obtain ⟨x, rfl⟩ := Φ.surjective y
    refine ⟨x, ⟨(hD x).2 hy, ?_, fun h => hne (h ▸ rfl)⟩, rfl⟩
    simpa using hc.map Φ.symm
  · rintro ⟨x, ⟨hx, hc, hne⟩, rfl⟩
    exact ⟨(hD x).1 hx, hc.map Φ, fun h => hne (Φ.injective h)⟩

theorem orbitIn_map (Φ : G ≃* G') {D' : Set G'} (hD : ∀ u, u ∈ D ↔ Φ u ∈ D') (d e : G) :
    orbitIn D' (Φ d) (Φ e) = Φ '' orbitIn D d e := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [commSet_map Φ hD d, closure_image_mulEquiv] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨x * e * x⁻¹, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨Φ x, ?_, by simp⟩
    rw [commSet_map Φ hD d, closure_image_mulEquiv]
    exact ⟨x, hx, rfl⟩

theorem isMaxOrbit_map (Φ : G ≃* G') {D' : Set G'} (hD : ∀ u, u ∈ D ↔ Φ u ∈ D') {d : G}
    {E : Set G} (h : IsMaxOrbit D d E) : IsMaxOrbit D' (Φ d) (Φ '' E) := by
  obtain ⟨e, he, hEe, hmax⟩ := h
  refine ⟨Φ e, ?_, ?_, ?_⟩
  · rw [commSet_map Φ hD d]
    exact ⟨e, he, rfl⟩
  · rw [hEe, orbitIn_map Φ hD]
  · intro e' he'
    rw [commSet_map Φ hD d] at he'
    obtain ⟨x, hx, rfl⟩ := he'
    rw [orbitIn_map Φ hD, Set.ncard_image_of_injective _ Φ.injective,
      Set.ncard_image_of_injective _ Φ.injective]
    exact hmax x hx

end Transport

theorem center_eq_bot_of_equiv {H : Type*} [Group H] (hf : 2 ≤ f) (e : H ≃* L2Wreath f k) :
    Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply e.injective
  rw [map_one]
  have hz' : e z ∈ Subgroup.center (L2Wreath f k) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  have hcent : e z ∈ Subgroup.centralizer (l2WreathBase f k : Set (L2Wreath f k)) :=
    fun b _ => Subgroup.mem_center_iff.1 hz' b
  rw [centralizer_l2WreathBase hf] at hcent
  exact Subgroup.mem_bot.1 hcent

theorem halpha_equiv {G : Type} [Group G] [Finite G] {D : Set G} (hC : HypothesisC D)
    (hf : 2 ≤ f) (hk : 3 ≤ k) (Φ : G ≃* L2Wreath f (k + 2))
    (hD : ∀ u, u ∈ D ↔ Φ u ∈ swapSet f (k + 2)) :
    Nonempty (Halpha D hC.alpha ≃* L2Wreath f k) := by
  obtain ⟨eE⟩ := closure_maxOrbit_equiv hf hk ((hD hC.d).1 hC.hd) (isMaxOrbit_map Φ hD hC.hE)
  have hmap : (Halpha D hC.alpha).map Φ.toMonoidHom = Subgroup.closure (Φ '' hC.E) := by
    rw [Halpha, hC.DalphaStar_alpha, MonoidHom.map_closure]
    rfl
  exact ⟨((Subgroup.equivMapOfInjective _ Φ.toMonoidHom Φ.injective).trans
    (MulEquiv.subgroupCongr hmap)).trans eE⟩

end WreathEndgame

theorem tenWreathEndgame_holds :
    ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (f n : ℕ),
      TenHyp hC f n →
      ∀ (f' m : ℕ) (Φ : G ≃* L2Wreath f' m), 2 ≤ f' →
        (∀ u ∈ D, ∃ i j : Fin m, i ≠ j ∧ (Φ u).right = Equiv.swap i j ∧
          (∀ k, k ≠ i → k ≠ j → (Φ u).left k = 1) ∧ (Φ u).left j = ((Φ u).left i)⁻¹) →
        f' = f ∧ m = n + 2 := by
  intro G _ _ D hC f n hH f' m Φ hf' hΦ
  have hS := hC.setup
  have hΦ' : ∀ u ∈ D, Φ u ∈ WreathEndgame.swapSet f' m := hΦ
  have hm2 : 2 ≤ m := WreathEndgame.two_le_of_mem_swapSet (hΦ' hC.d hC.hd)
  rcases (by omega : m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m) with rfl | rfl | rfl | h5
  · exact (WreathEndgame.false_of_two hC hH hf' Φ hΦ').elim
  · exact (WreathEndgame.false_of_three_four hS hC.conn (Or.inl rfl) Φ hΦ').elim
  · exact (WreathEndgame.false_of_three_four hS hC.conn (Or.inr rfl) Φ hΦ').elim
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨eH⟩ := WreathEndgame.halpha_equiv hC hf' (by omega) Φ
    (WreathEndgame.mem_D_iff_mem_swapSet hS hm2 Φ hΦ')
  obtain ⟨e⟩ := hH.iso
  let eFull : L2Wreath f n ≃* L2Wreath f' k :=
    e.symm.trans ((QuotientGroup.quotientMulEquivOfEq
      (WreathEndgame.center_eq_bot_of_equiv hf' eH)).trans (QuotientGroup.quotientBot.trans eH))
  obtain ⟨h1, h2⟩ := l2Wreath_params_eq hH.two_le hf' (by have := hH.five_le; omega)
    (by omega) eFull
  exact ⟨h1.symm, by omega⟩

end CFSG.OddTranspositions.PartThree

end
