module

public import CFSG.Quasithin.EmptyFaithful.S152YA
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.S152Y

open Matrix

section Abstract

variable {K X : Type} [Group K] [Group X]

@[expose] def NatCoord (ρ : K →* MulAut X) (α : K →* SL3) (β : X →* Multiplicative Vec3) : Prop :=
  ∀ (k : K) (x : X), Multiplicative.toAdd (β (ρ k x)) = mulV (α k) (Multiplicative.toAdd (β x))

@[expose] def stabV (ρ : K →* MulAut X) (V : Subgroup X) : Subgroup K where
  carrier := {k | ∀ x, ρ k x ∈ V ↔ x ∈ V}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    rw [map_mul, MulAut.mul_apply, ha, hb]
  inv_mem' := by
    intro a ha x
    have := ha (ρ a⁻¹ x)
    rw [show ρ a (ρ a⁻¹ x) = x by rw [← MulAut.mul_apply, ← map_mul]; simp] at this
    exact this.symm

open Classical in
@[expose] noncomputable def coordSet [Fintype X] (β : X →* Multiplicative Vec3) (V : Subgroup X) : Finset Vec3 :=
  (Finset.univ.filter (fun x : X => x ∈ V)).image (fun x => Multiplicative.toAdd (β x))

theorem mem_coordSet [Fintype X] {β : X →* Multiplicative Vec3} {V : Subgroup X} {p : Vec3} :
    p ∈ coordSet β V ↔ ∃ v ∈ V, Multiplicative.toAdd (β v) = p := by
  classical
  unfold coordSet
  simp

theorem coordSet_mem_planes [Fintype X] {β : X →* Multiplicative Vec3} {V : Subgroup X}
    (hV : Nat.card V = 4) (hinj : ∀ v ∈ V, β v = 1 → v = 1) : coordSet β V ∈ Planes := by
  classical
  refine mem_planes_of _ (Finset.mem_univ _) ?_ ?_ ?_
  · have h1 : (coordSet β V).card = (Finset.univ.filter (fun x : X => x ∈ V)).card := by
      unfold coordSet
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      have hx' : x ∈ V := (Finset.mem_filter.mp hx).2
      have hy' : y ∈ V := (Finset.mem_filter.mp hy).2
      have h2 : β (x * y⁻¹) = 1 := by
        have : β x = β y := Multiplicative.toAdd.injective hxy
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.mpr this
      have := hinj _ (V.mul_mem hx' (V.inv_mem hy')) h2
      exact mul_inv_eq_one.mp this
    rw [h1, ← Fintype.card_subtype]
    rw [← Nat.card_eq_fintype_card]
    exact hV
  · exact mem_coordSet.mpr ⟨1, V.one_mem, by simp⟩
  · intro a ha b hb
    obtain ⟨v, hv, rfl⟩ := mem_coordSet.mp ha
    obtain ⟨w, hw, rfl⟩ := mem_coordSet.mp hb
    exact mem_coordSet.mpr ⟨v * w, V.mul_mem hv hw, by simp⟩

structure VData (ρ : K →* MulAut X) (V : Subgroup X) (S : Subgroup K) (y : K) : Prop where
  card : Nat.card V = 4
  S_le : S ≤ stabV ρ V
  y_mem : y ∈ stabV ρ V
  y_fpf : ∀ v ∈ V, ρ y v = v → v = 1

theorem coordSet_card [Fintype X] {β : X →* Multiplicative Vec3} {V : Subgroup X}
    (hV : Nat.card V = 4) (hinj : ∀ v ∈ V, β v = 1 → v = 1) : (coordSet β V).card = 4 :=
  planes_card_four _ (coordSet_mem_planes hV hinj)

theorem parabolic [Fintype X] {ρ : K →* MulAut X} {α : K →* SL3} {β : X →* Multiplicative Vec3}
    (hβ : NatCoord ρ α β) {V : Subgroup X} {S : Subgroup K} {y : K} (hV : VData ρ V S y)
    (hinj : ∀ v ∈ V, β v = 1 → v = 1) (hS8 : Nat.card (S.map α) = 8) :
    ∀ g : SL3, (coordSet β V).image (mulV g) = coordSet β V → ∃ h ∈ stabV ρ V, α h = g := by
  classical
  set A := coordSet β V with hA
  have hAP : A ∈ Planes := coordSet_mem_planes hV.card hinj
  set H := stabV ρ V with hH
  have hle : H.map α ≤ stabSub A := by
    rintro _ ⟨h, hh, rfl⟩
    show A.image (mulV (α h)) = A
    apply image_eq_of_subset
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_coordSet.mp ha
    rw [← hβ h v]
    exact mem_coordSet.mpr ⟨ρ h v, (hh v).mpr hv, rfl⟩
  have h8 : 8 ∣ Nat.card (H.map α) := by
    rw [← hS8]
    exact Subgroup.card_dvd_of_le (Subgroup.map_mono hV.S_le)
  have hyH : α y ∈ H.map α := ⟨y, hV.y_mem, rfl⟩
  have hstab : A.image (mulV (α y)) = A := hle hyH
  have hfpf : ∀ a ∈ A, a ≠ 0 → mulV (α y) a ≠ a := by
    intro a ha ha0 h
    obtain ⟨v, hv, rfl⟩ := mem_coordSet.mp ha
    have h1 : β (ρ y v) = β v := Multiplicative.toAdd.injective (by rw [hβ y v]; exact h)
    have h2 : ρ y v = v := by
      have := hinj (ρ y v * v⁻¹) (V.mul_mem ((hV.y_mem v).mpr hv) (V.inv_mem hv)) (by
        rw [map_mul, map_inv, h1]; exact mul_inv_cancel _)
      exact mul_inv_eq_one.mp this
    have h3 := hV.y_fpf v hv h2
    subst h3
    exact ha0 (by simp)
  have hcube : α y ^ 3 = 1 := cube_one A hAP (α y) (Finset.mem_univ _) hstab hfpf
  have hne : α y ≠ 1 := by
    intro h1
    obtain ⟨a, ha, ha0⟩ := Finset.exists_mem_ne (show 1 < A.card by rw [coordSet_card hV.card hinj]; norm_num) 0
    exact hfpf a ha ha0 (by rw [h1, mulV_one])
  have hord : orderOf (α y) = 3 := orderOf_eq_prime hcube hne
  have h3 : 3 ∣ Nat.card (H.map α) := by
    have := orderOf_dvd_natCard (⟨α y, hyH⟩ : H.map α)
    rwa [Subgroup.orderOf_mk, hord] at this
  have h24 : 24 ∣ Nat.card (H.map α) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3
  have hpos : 0 < Nat.card (H.map α) := Nat.card_pos
  have hle24 : Nat.card (H.map α) ≤ 24 := by
    have := Subgroup.card_le_of_le hle
    rwa [natCard_stabSub hAP] at this
  have hcard : Nat.card (H.map α) = 24 := by
    obtain ⟨m, hm⟩ := h24
    omega
  have heq : H.map α = stabSub A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_stabSub hAP, hcard])
  intro g hg
  have : g ∈ stabSub A := hg
  rw [← heq] at this
  obtain ⟨h, hh, rfl⟩ := this
  exact ⟨h, hh, rfl⟩

@[expose] def orbitSet (ρ : K →* MulAut X) (V : Subgroup X) : Set X := {x | ∃ (k : K) (v : X), v ∈ V ∧ x = ρ k v}

theorem NatCoord.mul {ρ : K →* MulAut X} {α : K →* SL3} {β₀ β₁ : X →* Multiplicative Vec3}
    (h₀ : NatCoord ρ α β₀) (h₁ : NatCoord ρ α β₁) : NatCoord ρ α (β₀ * β₁) := by
  intro k x
  show Multiplicative.toAdd (β₀ (ρ k x) * β₁ (ρ k x)) = mulV (α k) (Multiplicative.toAdd (β₀ x * β₁ x))
  rw [toAdd_mul, toAdd_mul, h₀ k x, h₁ k x, mulV_add]

theorem NatCoord.kills {ρ : K →* MulAut X} {α : K →* SL3} {c : X →* Multiplicative Vec3}
    (hc : NatCoord ρ α c) {V : Subgroup X} (hV : ∀ v ∈ V, c v = 1) :
    Subgroup.closure (orbitSet ρ V) ≤ c.ker := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, v, hv, rfl⟩
  show c (ρ k v) = 1
  have h1 := hc k v
  rw [hV v hv] at h1
  have : Multiplicative.toAdd (c (ρ k v)) = 0 := by rw [h1]; simp [mulV]
  exact Multiplicative.toAdd.injective (by simpa using this)

theorem card_vec3 : Nat.card Vec3 = 8 := by
  rw [Nat.card_eq_fintype_card]
  simp

theorem card_le_of_joint [Finite X] {c c' : X →* Multiplicative Vec3}
    (hjoint : ∀ x, c x = 1 → c' x = 1 → x = 1) {U : Subgroup X} (hU : U ≤ c.ker) : Nat.card U ≤ 8 := by
  have hinj : Function.Injective (fun x : U => Multiplicative.toAdd (c' x)) := by
    intro x y hxy
    have h1 : c' ((x : X) * (y : X)⁻¹) = 1 := by
      have : c' x = c' y := Multiplicative.toAdd.injective hxy
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr this
    have h2 : c ((x : X) * (y : X)⁻¹) = 1 := hU (U.mul_mem x.2 (U.inv_mem y.2))
    have := hjoint _ h2 h1
    exact Subtype.ext (mul_inv_eq_one.mp this)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [card_vec3] at this

theorem eq_or_eq_or_eq_or_eq_of_card_four' {V : Type*} [Finite V] (hV : Nat.card V = 4)
    {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (w : V) : w = a ∨ w = b ∨ w = c ∨ w = d := by
  classical
  by_contra hw
  push Not at hw
  have hcard : (({a, b, c, d, w} : Finset V)).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair]
    · exact hw.2.2.2.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hcd, fun h => hw.2.2.1 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hbc, hbd, fun h => hw.2.1 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac, had, fun h => hw.1 h.symm⟩
  have : Fintype V := Fintype.ofFinite V
  have hle := Finset.card_le_univ ({a, b, c, d, w} : Finset V)
  rw [hcard, ← Nat.card_eq_fintype_card, hV] at hle
  omega

theorem vec3_add_self (a : Vec3) : a + a = 0 := by
  ext i
  have : ∀ x : ZMod 2, x + x = 0 := by decide
  exact this (a i)

theorem mul_self_eq_one_vec (z : Multiplicative Vec3) : z * z = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul]
  exact vec3_add_self _

theorem inj_of_not_all [Finite X] {ρ : K →* MulAut X} {α : K →* SL3} {c : X →* Multiplicative Vec3}
    (hc : NatCoord ρ α c) (hsq : ∀ x : X, x * x = 1) {V : Subgroup X} {S : Subgroup K} {y : K}
    (hV : VData ρ V S y) (hw : ∃ w ∈ V, c w ≠ 1) : ∀ v ∈ V, c v = 1 → v = 1 := by
  classical
  intro v hv hcv
  by_contra hv1
  obtain ⟨w, hwV, hw⟩ := hw
  have hv'V : ρ y v ∈ V := (hV.y_mem v).mpr hv
  have hcv' : c (ρ y v) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [hc y v, hcv]
    simp [mulV_zero]
  have hv'v : ρ y v ≠ v := fun h => hv1 (hV.y_fpf v hv h)
  have hv'1 : ρ y v ≠ 1 := fun h => hv1 ((ρ y).injective (h.trans (map_one (ρ y)).symm))
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v)
  have hv''V : v * ρ y v ∈ V := V.mul_mem hv hv'V
  have hv''1 : v * ρ y v ≠ 1 := by
    intro h
    apply hv'v
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hvinv]
  have hv''v : v * ρ y v ≠ v := by
    intro h
    exact hv'1 (mul_eq_left.mp h)
  have hv''v' : v * ρ y v ≠ ρ y v := by
    intro h
    exact hv1 (mul_eq_right.mp h)
  have hex := eq_or_eq_or_eq_or_eq_of_card_four' (V := ↥V) hV.card
    (a := (1 : ↥V)) (b := ⟨v, hv⟩) (c := ⟨ρ y v, hv'V⟩) (d := ⟨v * ρ y v, hv''V⟩)
    (fun h => hv1 (congrArg Subtype.val h).symm) (fun h => hv'1 (congrArg Subtype.val h).symm)
    (fun h => hv''1 (congrArg Subtype.val h).symm) (fun h => hv'v (congrArg Subtype.val h).symm)
    (fun h => hv''v (congrArg Subtype.val h).symm) (fun h => hv''v' (congrArg Subtype.val h).symm)
    ⟨w, hwV⟩
  apply hw
  rcases hex with h | h | h | h
  · have e : w = 1 := congrArg Subtype.val h
    rw [e]
    simp
  · have e : w = v := congrArg Subtype.val h
    rw [e]
    exact hcv
  · have e : w = ρ y v := congrArg Subtype.val h
    rw [e]
    exact hcv'
  · have e : w = v * ρ y v := congrArg Subtype.val h
    rw [e, map_mul, hcv, hcv']
    simp

theorem afl2 [Fintype X] {ρ : K →* MulAut X} {α : K →* SL3} {β₀ β₁ : X →* Multiplicative Vec3}
    (h₀ : NatCoord ρ α β₀) (h₁ : NatCoord ρ α β₁)
    (hjoint : ∀ x, β₀ x = 1 → β₁ x = 1 → x = 1) (hsq : ∀ x : X, x * x = 1)
    {V : Subgroup X} {S : Subgroup K} {y : K} (hV : VData ρ V S y) (hS8 : Nat.card (S.map α) = 8) :
    Nat.card (Subgroup.closure (orbitSet ρ V)) ≤ 8 := by
  classical
  have h₂ : NatCoord ρ α (β₀ * β₁) := h₀.mul h₁
  have key : (∀ v ∈ V, β₀ v = 1) ∨ (∀ v ∈ V, β₁ v = 1) ∨ (∀ v ∈ V, (β₀ * β₁) v = 1) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨w₀, hw₀V, hw₀⟩, ⟨w₁, hw₁V, hw₁⟩, ⟨w₂, hw₂V, hw₂⟩⟩ := hcon
    have hinj₀ := inj_of_not_all h₀ hsq hV ⟨w₀, hw₀V, hw₀⟩
    have hinj₁ := inj_of_not_all h₁ hsq hV ⟨w₁, hw₁V, hw₁⟩
    have hpar := parabolic h₀ hV hinj₀ hS8
    have hAP : coordSet β₀ V ∈ Planes := coordSet_mem_planes hV.card hinj₀
    have hb : ∀ v ∈ V, β₁ v = β₀ v := by
      intro v hv
      by_cases hv1 : v = 1
      · subst hv1
        simp
      · have ha : Multiplicative.toAdd (β₀ v) ∈ coordSet β₀ V := mem_coordSet.mpr ⟨v, hv, rfl⟩
        have ha0 : Multiplicative.toAdd (β₀ v) ≠ 0 := fun h =>
          hv1 (hinj₀ v hv (Multiplicative.toAdd.injective (by simpa using h)))
        have hfix : ∀ g : SL3, (coordSet β₀ V).image (mulV g) = coordSet β₀ V →
            mulV g (Multiplicative.toAdd (β₀ v)) = Multiplicative.toAdd (β₀ v) →
            mulV g (Multiplicative.toAdd (β₁ v)) = Multiplicative.toAdd (β₁ v) := by
          intro g hg hgv
          obtain ⟨h, hh, rfl⟩ := hpar g hg
          have hρ : ρ h v ∈ V := (hh v).mpr hv
          have h1 : ρ h v = v := by
            have : β₀ (ρ h v * v⁻¹) = 1 := by
              rw [map_mul, map_inv]
              apply mul_inv_eq_one.mpr
              apply Multiplicative.toAdd.injective
              rw [h₀ h v]
              exact hgv
            exact mul_inv_eq_one.mp (hinj₀ _ (V.mul_mem hρ (V.inv_mem hv)) this)
          have := h₁ h v
          rw [h1] at this
          exact this.symm
        rcases fix_lemma _ hAP _ ha ha0 _ hfix with h0 | h0
        · exfalso
          apply hv1
          exact hinj₁ v hv (Multiplicative.toAdd.injective (by simpa using h0))
        · exact Multiplicative.toAdd.injective h0
    apply hw₂
    show β₀ w₂ * β₁ w₂ = 1
    rw [hb w₂ hw₂V]
    exact mul_self_eq_one_vec _
  rcases key with hk | hk | hk
  · exact card_le_of_joint (c := β₀) (c' := β₁) hjoint (h₀.kills hk)
  · exact card_le_of_joint (c := β₁) (c' := β₀) (fun x h1 h0 => hjoint x h0 h1) (h₁.kills hk)
  · refine card_le_of_joint (c := β₀ * β₁) (c' := β₁) (fun x hc h1 => hjoint x ?_ h1) (h₂.kills hk)
    have : β₀ x * β₁ x = 1 := hc
    rw [h1, mul_one] at this
    exact this

theorem image_image_mulV (A : Finset Vec3) (g h : SL3) :
    (A.image (mulV h)).image (mulV g) = A.image (mulV (g * h)) := by
  rw [Finset.image_image]
  congr 1
  funext v
  exact (mulV_mul g h v).symm

theorem afl1 [Fintype X] {ρ : K →* MulAut X} {α : K →* SL3} {β : X →* Multiplicative Vec3}
    (hβ : NatCoord ρ α β) (hα : Function.Surjective α) (hsq : ∀ x : X, x * x = 1)
    (hker : ∀ a b c : X, β a = 1 → β b = 1 → β c = 1 → a = b ∨ a = c ∨ b = c)
    (hkerfix : ∀ (k : K) (x : X), β x = 1 → ρ k x = x)
    (htriv : ∀ k : K, α k = 1 → ρ k = 1)
    {V : Subgroup X} {S : Subgroup K} {y : K} (hV : VData ρ V S y) (hS8 : Nat.card (S.map α) = 8) :
    Nat.card (Subgroup.closure (orbitSet ρ V)) ≤ 8 := by
  classical
  have hinj : ∀ v ∈ V, β v = 1 → v = 1 := fun v hv hv1 => hV.y_fpf v hv (hkerfix y v hv1)
  have hAP : coordSet β V ∈ Planes := coordSet_mem_planes hV.card hinj
  have hpar := parabolic hβ hV hinj hS8
  set A := coordSet β V with hA
  let pl : K → Finset Vec3 := fun k => A.image (mulV (α k))
  let Vk : K → Set X := fun k => {x | ∃ v ∈ V, x = ρ k v}
  have hpl_mem : ∀ k, pl k ∈ Planes := fun k => planes_image A hAP (α k) (Finset.mem_univ _)
  have hpl_mul : ∀ m k, pl (m * k) = (pl k).image (mulV (α m)) := by
    intro m k
    simp only [pl, image_image_mulV, map_mul]
  have hpl_exists : ∀ B ∈ Planes, ∃ k : K, pl k = B := by
    intro B hB
    obtain ⟨g, hg⟩ := planes_trans A hAP B hB
    obtain ⟨k, rfl⟩ := hα g
    exact ⟨k, hg⟩
  have hcoord : ∀ k x, x ∈ Vk k → Multiplicative.toAdd (β x) ∈ pl k := by
    rintro k _ ⟨v, hv, rfl⟩
    rw [hβ k v]
    exact Finset.mem_image.mpr ⟨_, mem_coordSet.mpr ⟨v, hv, rfl⟩, rfl⟩
  have hexists : ∀ k p, p ∈ pl k → ∃ x ∈ Vk k, Multiplicative.toAdd (β x) = p := by
    intro k p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, hv, rfl⟩ := mem_coordSet.mp ha
    exact ⟨ρ k v, ⟨v, hv, rfl⟩, hβ k v⟩
  have hunique : ∀ k x x', x ∈ Vk k → x' ∈ Vk k → β x = β x' → x = x' := by
    rintro k _ _ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩ h
    have h1 : mulV (α k) (Multiplicative.toAdd (β v)) = mulV (α k) (Multiplicative.toAdd (β v')) := by
      rw [← hβ k v, ← hβ k v', h]
    have h2 : β v = β v' := Multiplicative.toAdd.injective (mulV_inj _ h1)
    have h3 : β (v * v'⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr h2
    have := hinj _ (V.mul_mem hv (V.inv_mem hv')) h3
    rw [mul_inv_eq_one.mp this]
  have hzero : ∀ k x, x ∈ Vk k → β x = 1 → x = 1 := by
    rintro k _ ⟨v, hv, rfl⟩ h
    have h1 : mulV (α k) (Multiplicative.toAdd (β v)) = 0 := by
      rw [← hβ k v, h]
      rfl
    have h2 : β v = 1 := by
      apply Multiplicative.toAdd.injective
      apply mulV_inj (α k)
      rw [h1]
      exact (mulV_zero (α k)).symm
    rw [hinj v hv h2]
    simp
  have hVk_eq : ∀ k k', pl k = pl k' → Vk k = Vk k' := by
    intro k k' hk
    have himg : A.image (mulV (α (k⁻¹ * k'))) = A := by
      have h1 : (pl k).image (mulV (α k⁻¹)) = A := by
        simp only [pl, image_image_mulV, ← map_mul, inv_mul_cancel]
        have : mulV (1 : SL3) = id := by funext v; simp [mulV_one]
        rw [map_one, this]
        simp
      have h2 : (pl k').image (mulV (α k⁻¹)) = A.image (mulV (α (k⁻¹ * k'))) := by
        simp only [pl, image_image_mulV, ← map_mul]
      rw [← h2, ← hk, h1]
    obtain ⟨h, hh, hhα⟩ := hpar _ himg
    have hz : α (h⁻¹ * (k⁻¹ * k')) = 1 := by rw [map_mul, map_inv, hhα]; simp
    have hρz := htriv _ hz
    have hρt : ρ (k⁻¹ * k') = ρ h := by
      have : k⁻¹ * k' = h * (h⁻¹ * (k⁻¹ * k')) := by group
      rw [this, map_mul, hρz, mul_one]
    have hρk' : ρ k' = ρ k * ρ h := by
      have : k' = k * (k⁻¹ * k') := by group
      rw [this, map_mul, hρt]
    have hρinv : ∀ v, ρ h (ρ h⁻¹ v) = v := by
      intro v
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨ρ h⁻¹ v, (((stabV ρ V).inv_mem hh) v).mpr hv, ?_⟩
      rw [hρk']
      show ρ k v = ρ k (ρ h (ρ h⁻¹ v))
      rw [hρinv]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨ρ h v, (hh v).mpr hv, ?_⟩
      rw [hρk']
      rfl
  have hp₀ : (![1, 0, 0] : Vec3) ≠ 0 := by decide
  have hbase : ∃ (k₁ k₂ : K) (x : X), pl k₁ ≠ pl k₂ ∧ x ∈ Vk k₁ ∧ x ∈ Vk k₂ ∧
      Multiplicative.toAdd (β x) = ![1, 0, 0] := by
    obtain ⟨B₁, hB₁, B₂, hB₂, B₃, hB₃, h12, h13, h23, hp1, hp2, hp3⟩ := three_planes _ hp₀
    obtain ⟨k₁, hk₁⟩ := hpl_exists B₁ hB₁
    obtain ⟨k₂, hk₂⟩ := hpl_exists B₂ hB₂
    obtain ⟨k₃, hk₃⟩ := hpl_exists B₃ hB₃
    obtain ⟨x₁, hx₁, hbx₁⟩ := hexists k₁ _ (hk₁ ▸ hp1)
    obtain ⟨x₂, hx₂, hbx₂⟩ := hexists k₂ _ (hk₂ ▸ hp2)
    obtain ⟨x₃, hx₃, hbx₃⟩ := hexists k₃ _ (hk₃ ▸ hp3)
    have hb12 : β (x₂ * x₁⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr (Multiplicative.toAdd.injective (hbx₂.trans hbx₁.symm))
    have hb13 : β (x₃ * x₁⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr (Multiplicative.toAdd.injective (hbx₃.trans hbx₁.symm))
    rcases hker _ _ 1 hb12 hb13 (map_one β) with h | h | h
    ·
      have : x₂ = x₃ := mul_right_cancel h
      exact ⟨k₂, k₃, x₂, by rw [hk₂, hk₃]; exact h23, hx₂, this ▸ hx₃, hbx₂⟩
    · have : x₂ = x₁ := mul_inv_eq_one.mp h
      exact ⟨k₁, k₂, x₁, by rw [hk₁, hk₂]; exact h12, hx₁, this ▸ hx₂, hbx₁⟩
    · have : x₃ = x₁ := mul_inv_eq_one.mp h
      exact ⟨k₁, k₃, x₁, by rw [hk₁, hk₃]; exact h13, hx₁, this ▸ hx₃, hbx₁⟩
  have hagree : ∀ k k' : K, pl k ≠ pl k' → ∀ x x' : X, x ∈ Vk k → x' ∈ Vk k' → β x = β x' →
      β x ≠ 1 → x = x' := by
    intro k k' hne x x' hx hx' hxx hx1
    obtain ⟨k₁, k₂, x₀, h12, hx₁, hx₂, hbx₀⟩ := hbase
    obtain ⟨g, hg1, hg2⟩ := planes_two_trans (pl k₁) (hpl_mem k₁) (pl k₂) (hpl_mem k₂) (pl k)
      (hpl_mem k) (pl k') (hpl_mem k') h12 hne
    obtain ⟨m, rfl⟩ := hα g
    have hVm1 : Vk (m * k₁) = Vk k := hVk_eq _ _ (by rw [hpl_mul]; exact hg1)
    have hVm2 : Vk (m * k₂) = Vk k' := hVk_eq _ _ (by rw [hpl_mul]; exact hg2)
    have hy₀1 : ρ m x₀ ∈ Vk k := by
      rw [← hVm1]
      obtain ⟨v, hv, hxv⟩ := hx₁
      exact ⟨v, hv, by rw [hxv, map_mul]; rfl⟩
    have hy₀2 : ρ m x₀ ∈ Vk k' := by
      rw [← hVm2]
      obtain ⟨v, hv, hxv⟩ := hx₂
      exact ⟨v, hv, by rw [hxv, map_mul]; rfl⟩
    have hq : Multiplicative.toAdd (β (ρ m x₀)) = mulV (α m) ![1, 0, 0] := by rw [hβ m x₀, hbx₀]
    have hq0 : Multiplicative.toAdd (β (ρ m x₀)) ≠ 0 := by
      rw [hq]
      intro h
      apply hp₀
      apply mulV_inj (α m)
      rw [h, mulV_zero]
    have hp0 : Multiplicative.toAdd (β x) ≠ 0 := fun h =>
      hx1 (Multiplicative.toAdd.injective (by simpa using h))
    have hpk : Multiplicative.toAdd (β x) ∈ pl k := hcoord k x hx
    have hpk' : Multiplicative.toAdd (β x) ∈ pl k' := by
      rw [hxx]
      exact hcoord k' x' hx'
    have hqk : Multiplicative.toAdd (β (ρ m x₀)) ∈ pl k := hcoord k _ hy₀1
    have hqk' : Multiplicative.toAdd (β (ρ m x₀)) ∈ pl k' := hcoord k' _ hy₀2
    obtain ⟨r, hr0, hmeet⟩ := planes_meet (pl k) (hpl_mem k) (pl k') (hpl_mem k') hne
    have hpr : Multiplicative.toAdd (β x) = r := by
      have : Multiplicative.toAdd (β x) ∈ pl k ∩ pl k' := Finset.mem_inter.mpr ⟨hpk, hpk'⟩
      rw [hmeet] at this
      rcases Finset.mem_insert.mp this with h | h
      · exact absurd h hp0
      · exact Finset.mem_singleton.mp h
    have hqr : Multiplicative.toAdd (β (ρ m x₀)) = r := by
      have : Multiplicative.toAdd (β (ρ m x₀)) ∈ pl k ∩ pl k' := Finset.mem_inter.mpr ⟨hqk, hqk'⟩
      rw [hmeet] at this
      rcases Finset.mem_insert.mp this with h | h
      · exact absurd h hq0
      · exact Finset.mem_singleton.mp h
    have hβx : β x = β (ρ m x₀) := Multiplicative.toAdd.injective (hpr.trans hqr.symm)
    have e1 : x = ρ m x₀ := hunique k x _ hx hy₀1 hβx
    have e2 : x' = ρ m x₀ := hunique k' x' _ hx' hy₀2 (hxx.symm.trans hβx)
    rw [e1, e2]
  have hU : ∀ x, x ∈ orbitSet ρ V ↔ ∃ k, x ∈ Vk k := by
    intro x
    constructor
    · rintro ⟨k, v, hv, rfl⟩
      exact ⟨k, v, hv, rfl⟩
    · rintro ⟨k, v, hv, rfl⟩
      exact ⟨k, v, hv, rfl⟩
  have hinjU : ∀ x ∈ orbitSet ρ V, ∀ x' ∈ orbitSet ρ V, β x = β x' → x = x' := by
    intro x hx x' hx' hxx
    obtain ⟨k, hk⟩ := (hU x).mp hx
    obtain ⟨k', hk'⟩ := (hU x').mp hx'
    by_cases h1 : β x = 1
    · have e1 := hzero k x hk h1
      have e2 := hzero k' x' hk' (hxx ▸ h1)
      rw [e1, e2]
    · by_cases hpk : pl k = pl k'
      · have : x' ∈ Vk k := by rw [hVk_eq k k' hpk]; exact hk'
        exact hunique k x x' hk this hxx
      · exact hagree k k' hpk x x' hk hk' hxx h1
  have hone : (1 : X) ∈ orbitSet ρ V := ⟨1, 1, V.one_mem, by simp⟩
  have hmulU : ∀ x ∈ orbitSet ρ V, ∀ x' ∈ orbitSet ρ V, x * x' ∈ orbitSet ρ V := by
    intro x hx x' hx'
    obtain ⟨k, hk⟩ := (hU x).mp hx
    obtain ⟨k', hk'⟩ := (hU x').mp hx'
    by_cases h1 : β x = 1
    · rw [hzero k x hk h1, one_mul]
      exact hx'
    by_cases h2 : β x' = 1
    · rw [hzero k' x' hk' h2, mul_one]
      exact hx
    by_cases h3 : β x = β x'
    · have : x = x' := hinjU x hx x' hx' h3
      rw [← this, hsq]
      exact hone
    · have hp0 : Multiplicative.toAdd (β x) ≠ 0 := fun h =>
        h1 (Multiplicative.toAdd.injective (by simpa using h))
      have hp'0 : Multiplicative.toAdd (β x') ≠ 0 := fun h =>
        h2 (Multiplicative.toAdd.injective (by simpa using h))
      have hpp' : Multiplicative.toAdd (β x) ≠ Multiplicative.toAdd (β x') := fun h =>
        h3 (Multiplicative.toAdd.injective h)
      obtain ⟨B, hB, hpB, hp'B⟩ := two_in_plane _ (Finset.mem_univ _) _ (Finset.mem_univ _) hp0 hp'0 hpp'
      obtain ⟨m, hm⟩ := hpl_exists B hB
      obtain ⟨z, hz, hzb⟩ := hexists m _ (hm ▸ hpB)
      obtain ⟨z', hz', hz'b⟩ := hexists m _ (hm ▸ hp'B)
      have hzx : z = x := hinjU z ((hU z).mpr ⟨m, hz⟩) x hx (Multiplicative.toAdd.injective hzb)
      have hzx' : z' = x' := hinjU z' ((hU z').mpr ⟨m, hz'⟩) x' hx' (Multiplicative.toAdd.injective hz'b)
      obtain ⟨v, hv, hzv⟩ := hz
      obtain ⟨v', hv', hzv'⟩ := hz'
      refine ⟨m, v * v', V.mul_mem hv hv', ?_⟩
      rw [← hzx, ← hzx', hzv, hzv', map_mul]
  have hclosure : ∀ x ∈ Subgroup.closure (orbitSet ρ V), x ∈ orbitSet ρ V := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact hone
    | mul x y _ _ hx hy => exact hmulU x hx y hy
    | inv x _ hx =>
      have : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x)
      rw [this]
      exact hx
  have hinjc : Function.Injective
      (fun x : Subgroup.closure (orbitSet ρ V) => Multiplicative.toAdd (β x)) := by
    intro x y hxy
    exact Subtype.ext (hinjU x (hclosure x x.2) y (hclosure y y.2) (Multiplicative.toAdd.injective hxy))
  have := Nat.card_le_card_of_injective _ hinjc
  rwa [card_vec3] at this

end Abstract

end CFSG.Quasithin.S152Y
