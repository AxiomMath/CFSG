module

public import CFSG.Walter.Ree.Thompson3.Invol

public section

namespace CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3]

@[expose] def bSet (σ : k ≃+* k) : Set (ThompsonN k σ) := {n | n.α = 0 ∧ n.γ = 0}

theorem bSet_mul {σ : k ≃+* k} {n m : ThompsonN k σ} (hn : n ∈ bSet σ) (hm : m ∈ bSet σ) :
    n * m ∈ bSet σ := by
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨hm1, hm2⟩ := hm
  refine ⟨?_, ?_⟩ <;> simp [ThompsonN.mul_def, thompsonMul, hn1, hn2, hm1, hm2]

theorem bSet_inv {σ : k ≃+* k} {n : ThompsonN k σ} (hn : n ∈ bSet σ) : n⁻¹ ∈ bSet σ := by
  obtain ⟨hn1, hn2⟩ := hn
  refine ⟨?_, ?_⟩ <;> simp [ThompsonN.inv_def, hn1, hn2]

theorem one_mem_bSet (σ : k ≃+* k) : (1 : ThompsonN k σ) ∈ bSet σ := ⟨rfl, rfl⟩

theorem torus_mem_bSet (σ : k ≃+* k) (t : kˣ) : ThompsonN.torus σ t ∈ bSet σ := ⟨rfl, rfl⟩

omit [CharP k 3] in
theorem pp0_mem_bSet (σ : k ≃+* k) (z : k) : pp σ 0 z 0 ∈ bSet σ := ⟨rfl, rfl⟩

theorem J_mem_bSet (σ : k ≃+* k) : ThompsonN.J σ ∈ bSet σ := torus_mem_bSet σ _

theorem eq_torus_mul_pp0 {σ : k ≃+* k} {n : ThompsonN k σ} (hn : n ∈ bSet σ) :
    n = ThompsonN.torus σ n.κ * pp σ 0 n.β 0 := by
  obtain ⟨h1, h2⟩ := hn
  ext <;> simp [ThompsonN.mul_def, thompsonMul, pp, h1, h2]

theorem pp0_mul_pp0 (σ : k ≃+* k) (z z' : k) : pp σ 0 z 0 * pp σ 0 z' 0 = pp σ 0 (z + z') 0 := by
  simp only [pp]
  rw [ThompsonN.mul_P]
  simp

theorem bSet_comm_J {σ : k ≃+* k} {n : ThompsonN k σ} (hn : n ∈ bSet σ) :
    n * ThompsonN.J σ = ThompsonN.J σ * n := by
  obtain ⟨h1, h2⟩ := hn
  ext <;> simp [ThompsonN.mul_def, thompsonMul, ThompsonN.J, h1, h2, mul_comm]

omit [CharP k 3] in
theorem card_bSet [Finite k] (σ : k ≃+* k) :
    (bSet σ).ncard = (Nat.card k - 1) * Nat.card k := by
  have : bSet σ = Set.range (fun v : kˣ × k => (⟨v.1, 0, v.2, 0⟩ : ThompsonN k σ)) := by
    ext n
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(n.κ, n.β), by ext <;> simp [h1, h2]⟩
    · rintro ⟨v, rfl⟩; exact ⟨rfl, rfl⟩
  rw [this, Set.ncard_range_of_injective, Nat.card_prod, Nat.card_units]
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [ThompsonN.mk.injEq] at h
  rw [h.1, h.2.2.1]

instance instFiniteThompsonN [Finite k] (σ : k ≃+* k) : Finite (ThompsonN k σ) :=
  Finite.of_equiv _ (ThompsonN.equivProd σ).symm

namespace RType

variable [Finite k] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

section H

variable {a : ℕ} (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h69 : Eq69 R)
include ha haσ h69

omit [Finite k] in
theorem K_pp0_K (z : k) (hz : z ≠ 0) :
    R.K * R.ι (pp σ 0 z 0) * R.K = R.ι (pp σ 0 (-z⁻¹) 0 * ThompsonN.torus σ (Units.mk0 z hz ^ a)) *
      R.K * R.ι (pp σ 0 (-z⁻¹) 0) := by
  have hx : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz)
  have h := h69 a ha haσ (-z⁻¹) hx
  have e1 : -(-z⁻¹)⁻¹ = z := by rw [inv_neg, inv_inv, neg_neg]
  have e2 : (Units.mk0 (-z⁻¹) hx)⁻¹ ^ a = Units.mk0 z hz ^ a := by
    have : (Units.mk0 (-z⁻¹) hx)⁻¹ = -Units.mk0 z hz := Units.ext (by simp)
    rw [this, Even.neg_pow ha]
  rw [e1, e2] at h
  rw [map_mul, ← h]

omit [Finite k] in
theorem K_b_K {b : ThompsonN k σ} (hb : b ∈ bSet σ) :
    (∃ b' ∈ bSet σ, R.K * R.ι b * R.K = R.ι b') ∨
      ∃ b' ∈ bSet σ, ∃ z : k, R.K * R.ι b * R.K = R.ι b' * R.K * R.ι (pp σ 0 z 0) := by
  rw [eq_torus_mul_pp0 hb, map_mul]
  have e : R.K * (R.ι (ThompsonN.torus σ b.κ) * R.ι (pp σ 0 b.β 0)) * R.K =
      R.ι (ThompsonN.torus σ b.κ⁻¹) * (R.K * R.ι (pp σ 0 b.β 0) * R.K) := by
    rw [← mul_assoc, R.K_mul_torus]; group
  rw [e]
  by_cases hβ : b.β = 0
  · left
    refine ⟨ThompsonN.torus σ b.κ⁻¹, torus_mem_bSet σ _, ?_⟩
    rw [hβ, show pp σ 0 0 0 = 1 from rfl, map_one, mul_one, R.K_mul_K, mul_one]
  · right
    refine ⟨ThompsonN.torus σ b.κ⁻¹ * (pp σ 0 (-b.β⁻¹) 0 *
      ThompsonN.torus σ (Units.mk0 b.β hβ ^ a)), bSet_mul (torus_mem_bSet σ _)
        (bSet_mul (pp0_mem_bSet σ _) (torus_mem_bSet σ _)), -b.β⁻¹, ?_⟩
    rw [R.K_pp0_K ha haσ h69 b.β hβ]
    simp only [map_mul, mul_assoc]

@[expose] def hSet : Set G :=
  {g | (∃ b ∈ bSet σ, g = R.ι b) ∨ ∃ b ∈ bSet σ, ∃ z : k, g = R.ι b * R.K * R.ι (pp σ 0 z 0)}

omit [Finite k] ha haσ h69 in
theorem K_mul_b {b : ThompsonN k σ} (hb : b ∈ bSet σ) :
    R.K * R.ι b = R.ι (ThompsonN.torus σ b.κ⁻¹) * R.K * R.ι (pp σ 0 b.β 0) := by
  conv_lhs => rw [eq_torus_mul_pp0 hb, map_mul, ← mul_assoc, R.K_mul_torus]

omit [Finite k] in
theorem hSet_mul {g h : G} (hg : g ∈ R.hSet) (hh : h ∈ R.hSet) : g * h ∈ R.hSet := by
  rcases hg with ⟨b₁, hb₁, rfl⟩ | ⟨b₁, hb₁, z₁, rfl⟩ <;>
    rcases hh with ⟨b₂, hb₂, rfl⟩ | ⟨b₂, hb₂, z₂, rfl⟩
  · exact Or.inl ⟨b₁ * b₂, bSet_mul hb₁ hb₂, by rw [map_mul]⟩
  · exact Or.inr ⟨b₁ * b₂, bSet_mul hb₁ hb₂, z₂, by rw [map_mul]; group⟩
  ·
    set b₃ := pp σ 0 z₁ 0 * b₂
    have hb₃ : b₃ ∈ bSet σ := bSet_mul (pp0_mem_bSet σ _) hb₂
    refine Or.inr ⟨b₁ * ThompsonN.torus σ b₃.κ⁻¹, bSet_mul hb₁ (torus_mem_bSet σ _), b₃.β, ?_⟩
    have := R.K_mul_b hb₃
    have e : R.ι b₃ = R.ι (pp σ 0 z₁ 0) * R.ι b₂ := map_mul _ _ _
    rw [e] at this
    rw [map_mul]
    calc R.ι b₁ * R.K * R.ι (pp σ 0 z₁ 0) * R.ι b₂ =
        R.ι b₁ * (R.K * (R.ι (pp σ 0 z₁ 0) * R.ι b₂)) := by group
      _ = _ := by rw [this]; group
  · set b₃ := pp σ 0 z₁ 0 * b₂
    have hb₃ : b₃ ∈ bSet σ := bSet_mul (pp0_mem_bSet σ _) hb₂
    have e : R.ι b₁ * R.K * R.ι (pp σ 0 z₁ 0) * (R.ι b₂ * R.K * R.ι (pp σ 0 z₂ 0)) =
        R.ι b₁ * (R.K * R.ι b₃ * R.K) * R.ι (pp σ 0 z₂ 0) := by
      rw [show b₃ = pp σ 0 z₁ 0 * b₂ from rfl, map_mul]; group
    rw [e]
    rcases R.K_b_K ha haσ h69 hb₃ with ⟨b', hb', h'⟩ | ⟨b', hb', z, h'⟩
    · refine Or.inl ⟨b₁ * b' * pp σ 0 z₂ 0, bSet_mul (bSet_mul hb₁ hb') (pp0_mem_bSet σ _), ?_⟩
      rw [h']
      simp only [map_mul]
    · refine Or.inr ⟨b₁ * b', bSet_mul hb₁ hb', z + z₂, ?_⟩
      rw [h', ← pp0_mul_pp0]
      simp only [map_mul, mul_assoc]

omit [Finite k] ha haσ h69 in
theorem hSet_inv {g : G} (hg : g ∈ R.hSet) : g⁻¹ ∈ R.hSet := by
  rcases hg with ⟨b, hb, rfl⟩ | ⟨b, hb, z, rfl⟩
  · exact Or.inl ⟨b⁻¹, bSet_inv hb, by rw [map_inv]⟩
  ·
    have hb' := bSet_inv hb
    refine Or.inr ⟨(pp σ 0 z 0)⁻¹ * ThompsonN.torus σ (b⁻¹).κ⁻¹,
      bSet_mul (bSet_inv (pp0_mem_bSet σ _)) (torus_mem_bSet σ _), (b⁻¹).β, ?_⟩
    have := R.K_mul_b hb'
    rw [map_mul, map_inv]
    calc (R.ι b * R.K * R.ι (pp σ 0 z 0))⁻¹ =
          (R.ι (pp σ 0 z 0))⁻¹ * R.K⁻¹ * (R.ι b)⁻¹ := by group
      _ = (R.ι (pp σ 0 z 0))⁻¹ * (R.K * R.ι b⁻¹) := by rw [R.K_inv_eq, map_inv, mul_assoc]
      _ = _ := by rw [this]; group

@[expose] def hSub : Subgroup G where
  carrier := R.hSet
  mul_mem' := R.hSet_mul ha haσ h69
  one_mem' := Or.inl ⟨1, one_mem_bSet σ, by rw [map_one]⟩
  inv_mem' := R.hSet_inv

omit [Finite k] in
theorem mem_hSub_iff (g : G) : g ∈ R.hSub ha haσ h69 ↔ g ∈ R.hSet := Iff.rfl

omit [Finite k] in
theorem ι_mem_hSub {b : ThompsonN k σ} (hb : b ∈ bSet σ) : R.ι b ∈ R.hSub ha haσ h69 :=
  Or.inl ⟨b, hb, rfl⟩

omit [Finite k] in
theorem K_mem_hSub : R.K ∈ R.hSub ha haσ h69 :=
  Or.inr ⟨1, one_mem_bSet σ, 0, by rw [map_one, one_mul, show pp σ 0 0 0 = 1 from rfl, map_one,
    mul_one]⟩

omit [Finite k] in
theorem Jg_mem_hSub : R.Jg ∈ R.hSub ha haσ h69 := R.ι_mem_hSub ha haσ h69 (J_mem_bSet σ)

omit [Finite k] ha haσ h69 in
theorem hSet_comm_J {g : G} (hg : g ∈ R.hSet) : g * R.Jg = R.Jg * g := by
  have hbJ : ∀ b ∈ bSet σ, R.ι b * R.Jg = R.Jg * R.ι b := fun b hb => by
    rw [Jg, ← map_mul, ← map_mul, bSet_comm_J hb]
  rcases hg with ⟨b, hb, rfl⟩ | ⟨b, hb, z, rfl⟩
  · exact hbJ b hb
  · have h1 := hbJ b hb
    have h2 := hbJ _ (pp0_mem_bSet σ z)
    have h3 := R.Jg_mul_K
    calc R.ι b * R.K * R.ι (pp σ 0 z 0) * R.Jg = R.ι b * R.K * (R.ι (pp σ 0 z 0) * R.Jg) := by
          group
      _ = R.ι b * (R.K * R.Jg) * R.ι (pp σ 0 z 0) := by rw [h2]; group
      _ = (R.ι b * R.Jg) * R.K * R.ι (pp σ 0 z 0) := by rw [← h3]; group
      _ = _ := by rw [h1]; group

theorem card_hSub :
    (Nat.card k - 1) * Nat.card k + (Nat.card k - 1) * Nat.card k * Nat.card k ≤
    Nat.card (R.hSub ha haσ h69) := by
  classical
  let f : bSet σ ⊕ (bSet σ × k) → G := fun x => match x with
    | Sum.inl b => R.ι b
    | Sum.inr (b, z) => R.ι b * R.K * R.ι (pp σ 0 z 0)
  have hf : Function.Injective f := by
    rintro (⟨b, hb⟩ | ⟨⟨b, hb⟩, z⟩) (⟨b', hb'⟩ | ⟨⟨b', hb'⟩, z'⟩) h <;> simp only [f] at h
    · have := R.ι_injective h; subst this; rfl
    · exact absurd (h ▸ R.ι_mem b) (R.pres_not_mem b' (0, z', 0))
    · exact absurd (h.symm ▸ R.ι_mem b') (R.pres_not_mem b (0, z, 0))
    · obtain ⟨h1, h2⟩ := R.pres_unique (v := (0, z, 0)) (v' := (0, z', 0)) h
      simp only [Prod.mk.injEq, true_and, and_true] at h2
      subst h1; subst h2; rfl
  have hrange : ∀ x, f x ∈ R.hSub ha haσ h69 := by
    rintro (⟨b, hb⟩ | ⟨⟨b, hb⟩, z⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨b, hb, z, rfl⟩
  let f' : bSet σ ⊕ (bSet σ × k) → R.hSub ha haσ h69 := fun x => ⟨f x, hrange x⟩
  have hf' : Function.Injective f' := fun x y h => hf (congrArg Subtype.val h)
  have h1 := Nat.card_le_card_of_injective f' hf'
  rw [Nat.card_sum, Nat.card_prod, Nat.card_coe_set_eq, card_bSet] at h1
  exact h1

end H

theorem fix_comm_J_eq
    {ω : Option (k × k × k)} (hω : R.act ω R.Jg ≠ ω) :
    ∃ s₀ : G, ∀ y : G, R.act ω y = ω → y * R.Jg = R.Jg * y → y = 1 ∨ y = s₀ := by
  obtain ⟨s₀, hs₀, hs₀1, hs₀a, hs₀b⟩ := R.exists_invol_fixes_two (Ne.symm hω)
  refine ⟨s₀, fun y hy hyJ => ?_⟩
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  · right
    have hyy := R.sq_eq_one_of_fix_comm_J hω hy hyJ
    have hyJ' : R.act (R.act ω R.Jg) y = R.act ω R.Jg := by
      rw [← act_mul, ← hyJ, act_mul, hy]
    exact R.invol_unique (Ne.symm hω) hyy hy1 hy hyJ' hs₀ hs₀1 hs₀a hs₀b

theorem card_orbit_ge
    (H : Subgroup G) (hH : ∀ h ∈ H, h * R.Jg = R.Jg * h)
    {ω : Option (k × k × k)} (hω : R.act ω R.Jg ≠ ω) :
    Nat.card H ≤ 2 * ((fun h => R.act ω h) '' (H : Set G)).ncard := by
  classical
  obtain ⟨s₀, hs₀⟩ := R.fix_comm_J_eq hω
  have hfin : (H : Set G).Finite := Set.toFinite _
  let s : Finset G := hfin.toFinset
  have key := Finset.card_le_mul_card_image (s := s) (f := fun h => R.act ω h) 2 (by
    intro b hb
    obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_image.mp hb
    have hh₀H : h₀ ∈ H := by simpa [s] using hh₀
    calc (s.filter fun x => R.act ω x = R.act ω h₀).card ≤ ({h₀, s₀ * h₀} : Finset G).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, s, Set.Finite.mem_toFinset, SetLike.mem_coe] at hx
          obtain ⟨hxH, hxe⟩ := hx
          have hfix : R.act ω (x * h₀⁻¹) = ω := by rw [act_mul, hxe, act_act_inv]
          rcases hs₀ _ hfix (hH _ (H.mul_mem hxH (H.inv_mem hh₀H))) with h1 | h1
          · simp [mul_inv_eq_one.mp h1]
          · simp [mul_inv_eq_iff_eq_mul.mp h1]
      _ ≤ 2 := Finset.card_le_two)
  have e1 : s.card = Nat.card H := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  have e2 : (s.image fun h => R.act ω h).card = ((fun h => R.act ω h) '' (H : Set G)).ncard := by
    rw [← Set.ncard_coe_finset, Finset.coe_image, Set.Finite.coe_toFinset]
  rw [← e1, ← e2]
  exact key

theorem orderOf_Jg : orderOf R.Jg = 2 := by
  apply orderOf_eq_prime
  · rw [sq]; exact R.Jg_mul_Jg
  · intro h
    have := congrArg (fun z => R.act (some (1, 0, 0)) z) h
    simp only [act_J, act_one, Option.some.injEq, Prod.mk.injEq] at this
    exact two_ne_zero' (by linear_combination -this.1)

theorem K_not_conj_JK
    {x : G} (hx : x * R.Jg = R.Jg * x) : x⁻¹ * R.K * x ≠ R.Jg * R.K := by
  intro hxK
  set h := R.hyp
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.isConj_J R.orderOf_Jg)
  have hcomm : ∀ y : G, y * R.Jg = R.Jg * y → (c * y * c⁻¹) * h.J = h.J * (c * y * c⁻¹) := by
    intro y hy
    rw [← hc]
    calc c * y * c⁻¹ * (c * R.Jg * c⁻¹) = c * (y * R.Jg) * c⁻¹ := by group
      _ = c * (R.Jg * y) * c⁻¹ := by rw [hy]
      _ = _ := by group
  have hL : ∀ y : G, y * h.J = h.J * y → y ∈ h.L ∨ h.J * y ∈ h.L := by
    intro y hy
    obtain ⟨z, hz | hz⟩ := h.centralizer hy
    · exact Or.inl (hz ▸ h.κ_mem z)
    · right; rw [hz, ← mul_assoc, h.J_mul_J, one_mul]; exact h.κ_mem z
  have hconjL : ∀ y : G, y * h.J = h.J * y → ∀ l ∈ h.L, y⁻¹ * l * y ∈ h.L := by
    intro y hy l hl
    rcases hL y hy with hyL | hyL
    · exact h.L.mul_mem (h.L.mul_mem (h.L.inv_mem hyL) hl) hyL
    · have e : y⁻¹ * l * y = (h.J * y)⁻¹ * l * (h.J * y) := by
        have hlJ := h.comm_L hl
        rw [mul_inv_rev, h.J_inv]
        calc y⁻¹ * l * y = y⁻¹ * (l * (h.J * h.J)) * y := by rw [h.J_mul_J, mul_one]
          _ = y⁻¹ * (h.J * l * h.J) * y := by
              rw [show y⁻¹ * (l * (h.J * h.J)) * y = y⁻¹ * (l * h.J) * h.J * y by group, hlJ]
              group
          _ = _ := by group
      rw [e]
      exact h.L.mul_mem (h.L.mul_mem (h.L.inv_mem hyL) hl) hyL
  set K' := c * R.K * c⁻¹
  set x' := c * x * c⁻¹
  have hK'J : K' * h.J = h.J * K' := hcomm _ R.Jg_mul_K.symm
  have hx'J : x' * h.J = h.J * x' := hcomm _ hx
  have hrel : x'⁻¹ * K' * x' = h.J * K' := by
    rw [← hc]
    calc x'⁻¹ * K' * x' = c * (x⁻¹ * R.K * x) * c⁻¹ := by simp only [K', x']; group
      _ = c * (R.Jg * R.K) * c⁻¹ := by rw [hxK]
      _ = _ := by simp only [K']; group
  apply h.J_not_mem
  rcases hL K' hK'J with hK'L | hK'L
  ·
    have h1 := hconjL x' hx'J K' hK'L
    rw [hrel] at h1
    have : h.J = h.J * K' * K'⁻¹ := by group
    rw [this]
    exact h.L.mul_mem h1 (h.L.inv_mem hK'L)
  ·
    have h1 := hconjL x' hx'J _ hK'L
    have e : x'⁻¹ * (h.J * K') * x' = K' := by
      calc x'⁻¹ * (h.J * K') * x' = (x'⁻¹ * h.J * x') * (x'⁻¹ * K' * x') := by group
        _ = h.J * (h.J * K') := by
            rw [hrel]; congr 1
            calc x'⁻¹ * h.J * x' = x'⁻¹ * (h.J * x') := by group
              _ = x'⁻¹ * (x' * h.J) := by rw [hx'J]
              _ = h.J := by group
        _ = K' := by rw [← mul_assoc, h.J_mul_J, one_mul]
    rw [e] at h1
    have : h.J = h.J * K' * K'⁻¹ := by group
    rw [this]
    exact h.L.mul_mem hK'L (h.L.inv_mem h1)

end RType

end CFSG.Walter.Ree.T2
