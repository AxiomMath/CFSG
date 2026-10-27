module

public import CFSG.Quasithin.Vol2.Ch3E213MG41C3
public import CFSG.Quasithin.Vol2.Ch3E213MG41B

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] def IsNorm (G₀ : Subgroup (antiSp k)) (F₀ : Subfield k) (x : Fin 4 → k) : Prop :=
  x ≠ 0 ∧ ∀ c, c ∈ Lam G₀ x ↔ c ∈ F₀

variable {G₀ : Subgroup (antiSp k)} {F₀ : Subfield k}

theorem IsNorm.ne_zero {x : Fin 4 → k} (h : IsNorm G₀ F₀ x) : x ≠ 0 :=
  h.1

theorem IsNorm.mem {x : Fin 4 → k} (h : IsNorm G₀ F₀ x) {c : k} (hc : c ∈ F₀) :
    trv x c ∈ G₀ :=
  (h.2 c).mpr hc

theorem IsNorm.mem_centres {x : Fin 4 → k} (h : IsNorm G₀ F₀ x) : x ∈ centres G₀ :=
  ⟨h.1, 1, one_ne_zero, (h.2 1).mpr F₀.one_mem⟩

theorem isNorm_smul {x : Fin 4 → k} (h : IsNorm G₀ F₀ x) {r : k} (hr : r ∈ F₀) (hr0 : r ≠ 0) :
    IsNorm G₀ F₀ (r • x) := by
  refine ⟨smul_ne_zero hr0 h.1, fun c => ?_⟩
  rw [mem_Lam_smul, h.2]
  constructor
  · intro hc
    have := F₀.mul_mem (F₀.inv_mem (F₀.pow_mem hr 2)) hc
    rwa [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hr0), one_mul] at this
  · intro hc
    exact F₀.mul_mem (F₀.pow_mem hr 2) hc

theorem isNorm_act {x : Fin 4 → k} (h : IsNorm G₀ F₀ x) {g : antiSp k} (hg : g ∈ G₀) :
    IsNorm G₀ F₀ (natAct g x) := by
  refine ⟨fun h0 => h.1 (act_injective g (by rw [h0, act_zero])), fun c => ?_⟩
  rw [mem_Lam_act hg, h.2]

theorem mem_of_sq_mem [Finite k] {μ : k} (h : μ ^ 2 ∈ F₀) : μ ∈ F₀ := by
  classical
  let _ := Fintype.ofFinite k
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card k = 2 ^ n := by
    obtain ⟨n, hp, hn⟩ := FiniteField.card k 2
    exact ⟨n, hn⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := k)
    omega
  have hμ : μ = (μ ^ 2) ^ 2 ^ (n - 1) := by
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), ← hn,
      FiniteField.pow_card]
  rw [hμ]
  exact F₀.pow_mem h _

theorem mem_of_isNorm_smul [Finite k] {x : Fin 4 → k} (h : IsNorm G₀ F₀ x) {μ : k}
    (h' : IsNorm G₀ F₀ (μ • x)) : μ ∈ F₀ := by
  have h1 : (1 : k) ∈ Lam G₀ (μ • x) := (h'.2 1).mpr F₀.one_mem
  rw [mem_Lam_smul, mul_one, h.2] at h1
  exact mem_of_sq_mem h1

theorem card_lam_of_isNorm {x : Fin 4 → k} (h : IsNorm G₀ F₀ x) :
    Nat.card (Lam G₀ x) = Nat.card F₀ :=
  Nat.card_congr (Equiv.subtypeEquivRight h.2)

theorem isNorm_of_pair [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) {x y : Fin 4 → k}
    (hx : IsNorm G₀ F₀ x) (hxy : spBil x y = 1) {b : k} (hb : b ≠ 0) (hbL : b ∈ Lam G₀ y) :
    IsNorm G₀ F₀ y := by
  have h4 : 4 ≤ Nat.card (Lam G₀ x) := by rw [card_lam_of_isNorm hx]; exact hF4
  obtain ⟨F₁, hx1, hy1⟩ := pair_lemma hk hxy ((hx.2 1).mpr F₀.one_mem) h4 hb hbL
  have hx0 : (Lam G₀ x : Set k) = F₀ := Set.ext fun c => hx.2 c
  refine ⟨fun h0 => ?_, fun c => ?_⟩
  · rw [h0] at hxy
    simp at hxy
  · have := congrArg (fun s : Set k => c ∈ s) (hy1.trans (hx1.symm.trans hx0))
    exact Iff.of_eq this

theorem isNorm_of_bil_ne_zero [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀)
    {x y : Fin 4 → k} (hx : IsNorm G₀ F₀ x) (hy : y ∈ centres G₀) (hxy : spBil x y ≠ 0) :
    IsNorm G₀ F₀ ((spBil x y)⁻¹ • y) := by
  obtain ⟨-, b, hb, hbL⟩ := hy
  refine isNorm_of_pair hk hF4 hx (b := spBil x y ^ 2 * b) ?_ ?_ ?_
  · rw [LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hxy]
  · exact mul_ne_zero (pow_ne_zero 2 hxy) hb
  · rw [mem_Lam_smul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hxy, one_pow, one_mul]
    exact hbL

theorem bil_mem_of_isNorm [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) {x y : Fin 4 → k}
    (hx : IsNorm G₀ F₀ x) (hy : IsNorm G₀ F₀ y) : spBil x y ∈ F₀ := by
  by_cases h0 : spBil x y = 0
  · rw [h0]
    exact F₀.zero_mem
  · have := mem_of_isNorm_smul hy (isNorm_of_bil_ne_zero hk hF4 hx hy.mem_centres h0)
    simpa using F₀.inv_mem this

theorem isNorm_trv {x y : Fin 4 → k} (hx : IsNorm G₀ F₀ x) (hy : IsNorm G₀ F₀ y) {c : k}
    (hc : c ∈ F₀) : IsNorm G₀ F₀ (y + (c * spBil y x) • x) := by
  rw [← act_trv]
  exact isNorm_act hy (hx.mem hc)

theorem isNorm_add [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) {x y : Fin 4 → k}
    (hx : IsNorm G₀ F₀ x) (hy : IsNorm G₀ F₀ y) (hxy : spBil x y ≠ 0) :
    IsNorm G₀ F₀ (x + y) := by
  have hyx : spBil y x ≠ 0 := by rwa [bil_symm]
  have hc : (spBil y x)⁻¹ ∈ F₀ := F₀.inv_mem (bil_mem_of_isNorm hk hF4 hy hx)
  have := isNorm_trv hx hy hc
  rwa [inv_mul_cancel₀ hyx, one_smul, add_comm] at this

theorem isNorm_orth_add [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) {a b z : Fin 4 → k}
    (ha : IsNorm G₀ F₀ a) (hb : IsNorm G₀ F₀ b) (hz : IsNorm G₀ F₀ z) (hab : spBil a b = 0)
    (haz : spBil a z ≠ 0) (hbz : spBil b z ≠ 0) (hne : spBil a z ≠ spBil b z) :
    IsNorm G₀ F₀ (a + b) := by
  have h1 := isNorm_add hk hF4 ha hz haz
  have h2 : IsNorm G₀ F₀ (a + z + b) := by
    apply isNorm_add hk hF4 h1 hb
    rw [LinearMap.BilinForm.add_left, hab, zero_add, bil_symm]
    exact hbz
  have h3 : IsNorm G₀ F₀ (a + z + b + z) := by
    apply isNorm_add hk hF4 h2 hz
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left, bil_self, add_zero]
    intro h0
    apply hne
    linear_combination h0 - spBil b z * (CharTwo.two_eq_zero : (2 : k) = 0)
  have : a + z + b + z = a + b := by
    rw [add_right_comm, add_assoc a z z, CharTwo.add_self_eq_zero, add_zero]
  rwa [this] at h3

section Plane

variable {x z u : Fin 4 → k}

theorem isNorm_move_z (hz : IsNorm G₀ F₀ z) (hxz : spBil x z = 1) (huz : spBil u z = 0)
    {α β c : k} (hc : c ∈ F₀) (h : IsNorm G₀ F₀ (α • x + β • z + u)) :
    IsNorm G₀ F₀ (α • x + (β + c * α) • z + u) := by
  have h1 := isNorm_trv hz h hc
  have hval : spBil (α • x + β • z + u) z = α := by
    simp [hxz, bil_self, huz]
  rw [hval] at h1
  convert h1 using 1
  module

theorem isNorm_move_x (hx : IsNorm G₀ F₀ x) (hxz : spBil x z = 1) (hux : spBil u x = 0)
    {α β c : k} (hc : c ∈ F₀) (h : IsNorm G₀ F₀ (α • x + β • z + u)) :
    IsNorm G₀ F₀ ((α + c * β) • x + β • z + u) := by
  have hzx : spBil z x = 1 := by rw [bil_symm, hxz]
  have h1 := isNorm_trv hx h hc
  have hval : spBil (α • x + β • z + u) x = β := by
    simp [hzx, bil_self, hux]
  rw [hval] at h1
  convert h1 using 1
  module

theorem isNorm_congr {α β α' β' : k} (h : IsNorm G₀ F₀ (α • x + β • z + u)) (hα : α = α')
    (hβ : β = β') : IsNorm G₀ F₀ (α' • x + β' • z + u) := by
  subst hα hβ
  exact h

variable (hx : IsNorm G₀ F₀ x) (hz : IsNorm G₀ F₀ z) (hxz : spBil x z = 1)
  (hux : spBil u x = 0) (huz : spBil u z = 0)
include hx hz hxz hux huz

theorem isNorm_to_hub {α β : k} (hα : α ∈ F₀) (hβ : β ∈ F₀) (h0 : α ≠ 0 ∨ β ≠ 0)
    (h : IsNorm G₀ F₀ (α • x + β • z + u)) : IsNorm G₀ F₀ ((1 : k) • x + (0 : k) • z + u) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have key : ∀ {a b : k}, a ∈ F₀ → b ∈ F₀ → a ≠ 0 → IsNorm G₀ F₀ (a • x + b • z + u) →
      IsNorm G₀ F₀ ((1 : k) • x + (0 : k) • z + u) := by
    intro a b ha hb ha0 hab
    have s1 := isNorm_move_z hz hxz huz (c := b / a) (F₀.div_mem hb ha) hab
    have s1' := isNorm_congr s1 rfl
      (show b + b / a * a = 0 by field_simp; linear_combination b * h2)
    have s2 := isNorm_move_z hz hxz huz (c := a⁻¹) (F₀.inv_mem ha) s1'
    have s2' := isNorm_congr s2 rfl
      (show (0 : k) + a⁻¹ * a = 1 by rw [inv_mul_cancel₀ ha0, zero_add])
    have s3 := isNorm_move_x hx hxz hux (c := a + 1) (F₀.add_mem ha F₀.one_mem) s2'
    have s3' := isNorm_congr s3 (show a + (a + 1) * 1 = 1 by linear_combination a * h2) rfl
    have s4 := isNorm_move_z hz hxz huz (c := 1) F₀.one_mem s3'
    exact isNorm_congr s4 rfl (show (1 : k) + 1 * 1 = 0 by linear_combination h2)
  by_cases hα0 : α = 0
  · have hβ0 : β ≠ 0 := h0.resolve_left (not_not.mpr hα0)
    have s0 := isNorm_move_x hx hxz hux (c := β⁻¹) (F₀.inv_mem hβ) h
    have s0' := isNorm_congr s0 (show α + β⁻¹ * β = 1 by
      rw [hα0, zero_add, inv_mul_cancel₀ hβ0]) rfl
    exact key F₀.one_mem hβ one_ne_zero s0'
  · exact key hα hβ hα0 h

theorem isNorm_from_hub {α β : k} (hα : α ∈ F₀) (hβ : β ∈ F₀) (h0 : α ≠ 0 ∨ β ≠ 0)
    (h : IsNorm G₀ F₀ ((1 : k) • x + (0 : k) • z + u)) : IsNorm G₀ F₀ (α • x + β • z + u) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have s1 := isNorm_move_z hz hxz huz (c := 1) F₀.one_mem h
  have s1' := isNorm_congr s1 rfl (show (0 : k) + 1 * 1 = 1 by ring)
  by_cases hα0 : α = 0
  · have hβ0 : β ≠ 0 := h0.resolve_left (not_not.mpr hα0)
    have t1 := isNorm_move_z hz hxz huz (c := β) hβ h
    have t1' := isNorm_congr t1 rfl (show (0 : k) + β * 1 = β by ring)
    have t2 := isNorm_move_x hx hxz hux (c := β⁻¹) (F₀.inv_mem hβ) t1'
    exact isNorm_congr t2 (show (1 : k) + β⁻¹ * β = α by
      rw [hα0, inv_mul_cancel₀ hβ0]; linear_combination h2) rfl
  · have s2 := isNorm_move_x hx hxz hux (c := α + 1) (F₀.add_mem hα F₀.one_mem) s1'
    have s2' := isNorm_congr s2 (show (1 : k) + (α + 1) * 1 = α by linear_combination h2) rfl
    have s3 := isNorm_move_z hz hxz huz (c := (β + 1) / α)
      (F₀.div_mem (F₀.add_mem hβ F₀.one_mem) hα) s2'
    exact isNorm_congr s3 rfl (show (1 : k) + (β + 1) / α * α = β by
      field_simp; linear_combination h2)

theorem isNorm_plane {α β α' β' : k} (hα : α ∈ F₀) (hβ : β ∈ F₀) (h0 : α ≠ 0 ∨ β ≠ 0)
    (hα' : α' ∈ F₀) (hβ' : β' ∈ F₀) (h0' : α' ≠ 0 ∨ β' ≠ 0)
    (h : IsNorm G₀ F₀ (α • x + β • z + u)) : IsNorm G₀ F₀ (α' • x + β' • z + u) :=
  isNorm_from_hub hx hz hxz hux huz hα' hβ' h0' (isNorm_to_hub hx hz hxz hux huz hα hβ h0 h)

end Plane

end CFSG.Quasithin.Ch3E213M.G41
