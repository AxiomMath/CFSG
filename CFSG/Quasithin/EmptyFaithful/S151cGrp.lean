module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

open DihedralGroup

theorem d3_inner_exists : ∀ u v : DihedralGroup 3, u ≠ 1 → u * u * u = 1 → v * v = 1 →
    v * u * v⁻¹ = u⁻¹ → ∃ g : DihedralGroup 3, g * r 1 * g⁻¹ = u ∧ g * sr 0 * g⁻¹ = v := by
  decide

theorem d3_normal_form : ∀ z : DihedralGroup 3, ∃ i a : ℕ, z = (r 1) ^ i * (sr 0) ^ a := by
  intro z
  have : ∀ z : DihedralGroup 3, ∃ i : Fin 3, ∃ a : Fin 2, z = (r 1) ^ (i : ℕ) * (sr 0) ^ (a : ℕ) := by
    decide
  obtain ⟨i, a, h⟩ := this z
  exact ⟨i, a, h⟩

theorem d3_center_trivial : ∀ x : DihedralGroup 3, (∀ y, y * x = x * y) → x = 1 := by
  decide

theorem exists_inner_of_normalizes_D3 {G : Type*} [Group G] {L : Subgroup G}
    (e : ↥L ≃* DihedralGroup 3) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l ∈ L, ∀ m ∈ L, x * m * x⁻¹ = l * m * l⁻¹ := by
  have hxm : ∀ m ∈ L, x * m * x⁻¹ ∈ L := fun m hm => (Subgroup.mem_normalizer_iff.mp hx m).mp hm
  let ψ : ↥L → ↥L := fun m => ⟨x * m * x⁻¹, hxm m m.2⟩
  have hψmul : ∀ a b : ↥L, ψ (a * b) = ψ a * ψ b := fun a b => Subtype.ext (by
    show x * (a * b : G) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹)
    group)
  have hψinj : Function.Injective ψ := fun a b hab => Subtype.ext (by
    have h := congrArg Subtype.val hab
    simp only [ψ, mul_left_inj, mul_right_inj] at h
    exact h)
  let φ : DihedralGroup 3 → DihedralGroup 3 := fun d => e (ψ (e.symm d))
  have hφmul : ∀ a b, φ (a * b) = φ a * φ b := fun a b => by
    simp only [φ, map_mul, hψmul]
  have hφone : φ 1 = 1 := by
    have : φ 1 * φ 1 = φ 1 := by rw [← hφmul, mul_one]
    exact mul_eq_left.mp this
  have hφinj : Function.Injective φ := fun a b hab => by
    have h1 := e.injective hab
    exact e.symm.injective (hψinj h1)
  have hu3 : φ (r 1) * φ (r 1) * φ (r 1) = 1 := by
    rw [← hφmul, ← hφmul]
    have : (r 1 : DihedralGroup 3) * r 1 * r 1 = 1 := by decide
    rw [this, hφone]
  have hu1 : φ (r 1) ≠ 1 := fun h => by
    have : φ (r 1) = φ 1 := by rw [h, hφone]
    exact absurd (hφinj this) (by decide)
  have hv2 : φ (sr 0) * φ (sr 0) = 1 := by
    rw [← hφmul]
    have : (sr 0 : DihedralGroup 3) * sr 0 = 1 := by decide
    rw [this, hφone]
  have hvu : φ (sr 0) * φ (r 1) * (φ (sr 0))⁻¹ = (φ (r 1))⁻¹ := by
    have hinv : ∀ a, (φ a)⁻¹ = φ a⁻¹ := fun a => by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← hφmul, mul_inv_cancel, hφone]
    rw [hinv, hinv, ← hφmul, ← hφmul]
    have : (sr 0 : DihedralGroup 3) * r 1 * (sr 0)⁻¹ = (r 1)⁻¹ := by decide
    rw [this]
  obtain ⟨g, hg1, hg2⟩ := d3_inner_exists _ _ hu1 hu3 hv2 hvu
  refine ⟨((e.symm g : ↥L) : G), (e.symm g).2, fun m hm => ?_⟩
  obtain ⟨i, a, hia⟩ := d3_normal_form (e ⟨m, hm⟩)
  have hφpow : ∀ (d : DihedralGroup 3) (n : ℕ), φ (d ^ n) = φ d ^ n := fun d n => by
    induction n with
    | zero => simp [hφone]
    | succ n ih => rw [pow_succ, hφmul, ih, pow_succ]
  have hφd : φ (e ⟨m, hm⟩) = g * e ⟨m, hm⟩ * g⁻¹ := by
    rw [hia, hφmul, hφpow, hφpow, ← hg1, ← hg2, conj_pow, conj_pow]
    group
  have h1 : e (ψ ⟨m, hm⟩) = g * e ⟨m, hm⟩ * g⁻¹ := by
    rw [← hφd]
    simp only [φ, MulEquiv.symm_apply_apply]
  have h2 : ψ ⟨m, hm⟩ = e.symm g * ⟨m, hm⟩ * (e.symm g)⁻¹ := by
    apply e.injective
    rw [h1]
    simp
  exact congrArg Subtype.val h2

theorem exists_mul_eq_of_normalizes_D3 {G : Type*} [Group G] {L : Subgroup G}
    (e : ↥L ≃* DihedralGroup 3) {N : Subgroup G} (hLN : L ≤ N)
    (hn : ∀ x ∈ N, x ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ N) :
    ∃ l ∈ L, ∃ d ∈ N, (∀ m ∈ L, d * m = m * d) ∧ x = l * d := by
  obtain ⟨l, hl, hlx⟩ := exists_inner_of_normalizes_D3 e (hn x hx)
  refine ⟨l, hl, l⁻¹ * x, N.mul_mem (N.inv_mem (hLN hl)) hx, fun m hm => ?_, by group⟩
  have := hlx m hm
  calc l⁻¹ * x * m = l⁻¹ * (x * m * x⁻¹) * x := by group
    _ = l⁻¹ * (l * m * l⁻¹) * x := by rw [this]
    _ = m * (l⁻¹ * x) := by group

theorem inf_centralizer_eq_bot_D3 {G : Type*} [Group G] {L : Subgroup G}
    (e : ↥L ≃* DihedralGroup 3) : L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have h1 : e ⟨x, hx.1⟩ = 1 := d3_center_trivial _ fun y => by
    have := Subgroup.mem_centralizer_iff.mp hx.2 ((e.symm y : ↥L) : G) (e.symm y).2
    have h2 : (e.symm y) * (⟨x, hx.1⟩ : ↥L) = (⟨x, hx.1⟩ : ↥L) * (e.symm y) := Subtype.ext this
    have := congrArg e h2
    simpa using this
  have : (⟨x, hx.1⟩ : ↥L) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

end CFSG.Quasithin
