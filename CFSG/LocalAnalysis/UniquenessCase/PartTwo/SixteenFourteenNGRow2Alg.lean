module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistAlg
public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private lemma s1614_ra_sq_eq_one_or_eq {M : Type*} [Group M] {a x : M} (ha : a * a = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨q, r, hr, hk⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ k = 2 * q + r :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  have h2 : a ^ (2 : ℤ) = 1 := by simpa [zpow_two, pow_two] using ha
  rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases hr with rfl | rfl
  · left; simp
  · right; simp

private lemma s1614_ra_fix_eq_one {Ω : Type*} [CommGroup Ω] (hΩ : ∀ x : Ω, x * x = 1)
    {g : MulAut Ω} (hg3' : ∀ v : Ω, g (g (g v)) = v) {X : Subgroup Ω}
    (hX : Nat.card ↥X = 4) (hgX : ∀ x ∈ X, g x ∈ X)
    (hgnt : ∃ x ∈ X, g x ≠ x) :
    ∀ x ∈ X, g x = x → x = 1 := by
  obtain ⟨x₀, hx₀, hgx₀⟩ := hgnt
  intro x hx hgx
  by_contra hx1
  have hx2 : x * x = 1 := hΩ x
  have hx₀1 : x₀ ≠ 1 := by
    intro h
    exact hgx₀ (by rw [h, map_one])
  have hx₀x : x₀ ≠ x := by
    intro h
    exact hgx₀ (by rw [h, hgx])
  have hx₀z : x₀ ∉ Subgroup.zpowers x := by
    intro h
    rcases s1614_ra_sq_eq_one_or_eq hx2 h with h1 | h1
    · exact hx₀1 h1
    · exact hx₀x h1
  have hzX : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.2 hx
  have hidx : ((Subgroup.zpowers x).subgroupOf X).index = 2 := by
    have h1 := ((Subgroup.zpowers x).subgroupOf X).index_mul_card
    have h2 : Nat.card ↥((Subgroup.zpowers x).subgroupOf X) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzX).toEquiv, Nat.card_zpowers]
      exact orderOf_eq_prime (by rwa [pow_two]) hx1
    rw [hX, h2] at h1
    omega
  have hnotA : (⟨g x₀, hgX x₀ hx₀⟩ : ↥X) ∉ (Subgroup.zpowers x).subgroupOf X := by
    intro h
    have hmem : g x₀ ∈ Subgroup.zpowers x := Subgroup.mem_subgroupOf.1 h
    rcases s1614_ra_sq_eq_one_or_eq hx2 hmem with h1 | h1
    · exact hx₀1 (g.injective (h1.trans (map_one g).symm))
    · exact hx₀x (g.injective (h1.trans hgx.symm))
  have hnotB : (⟨x₀, hx₀⟩ : ↥X)⁻¹ ∉ (Subgroup.zpowers x).subgroupOf X := by
    intro h
    have hmem : x₀⁻¹ ∈ Subgroup.zpowers x := Subgroup.mem_subgroupOf.1 h
    exact hx₀z (by simpa using (Subgroup.zpowers x).inv_mem hmem)
  have hmem : (⟨g x₀, hgX x₀ hx₀⟩ : ↥X) * (⟨x₀, hx₀⟩ : ↥X)⁻¹
      ∈ (Subgroup.zpowers x).subgroupOf X := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact ⟨fun h => absurd h hnotA, fun h => absurd h hnotB⟩
  have hmem' : g x₀ * x₀⁻¹ ∈ Subgroup.zpowers x := by
    simpa using (Subgroup.mem_subgroupOf.1 hmem)
  have hx_eq : g x₀ * x₀⁻¹ = x := by
    rcases s1614_ra_sq_eq_one_or_eq hx2 hmem' with h | h
    · exact absurd (mul_inv_eq_one.1 h) hgx₀
    · exact h
  have hgx₀_eq : g x₀ = x * x₀ := by
    calc g x₀ = g x₀ * x₀⁻¹ * x₀ := by group
      _ = x * x₀ := by rw [hx_eq]
  have hg2 : g (g x₀) = x₀ := by
    rw [hgx₀_eq, map_mul, hgx, hgx₀_eq, ← mul_assoc, hx2, one_mul]
  have h3 := hg3' x₀
  rw [hg2] at h3
  exact hgx₀ h3

theorem s1614_row2_fixed {Ω : Type} [CommGroup Ω] [Finite Ω] (hΩ : ∀ x : Ω, x * x = 1)
    {y g : MulAut Ω} (hy3 : y * y * y = 1) (hyfpf : ∀ x : Ω, y x = x → x = 1)
    (hg3 : g * g * g = 1) (hyg : y * g = g * y) {X : Subgroup Ω} (hX : Nat.card ↥X = 4)
    (hgX : X.map g.toMonoidHom = X) (hgnt : ∃ x ∈ X, g x ≠ x)
    (hXy : X ⊓ X.map y.toMonoidHom = ⊥) :
    ∃ R : Subgroup Ω, R ≤ X ⊔ X.map y.toMonoidHom ∧ rk ↥R = 2 ∧ ∀ r ∈ R, (y * g) r = r := by
  have hΩ2 : ∀ v : Ω, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hΩ v
  have hy3' : ∀ v : Ω, y (y (y v)) = v := fun v => by
    have h := congrArg (fun f : MulAut Ω => f v) hy3
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h
  have hg3' : ∀ v : Ω, g (g (g v)) = v := fun v => by
    have h := congrArg (fun f : MulAut Ω => f v) hg3
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h
  have hyg' : ∀ v : Ω, y (g v) = g (y v) := fun v => by
    have h := congrArg (fun f : MulAut Ω => f v) hyg
    simpa only [MulAut.mul_apply] using h
  have hyy : ∀ v : Ω, y (y v) = v * y v := fun v =>
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist.apply_apply_eq_of_fpf hΩ (f := y)
      hy3' hyfpf v
  have hgX' : ∀ x ∈ X, g x ∈ X := by
    intro x hx
    have h : g.toMonoidHom x ∈ X.map g.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rwa [hgX] at h
  have hgfpf : ∀ x ∈ X, g x = x → x = 1 :=
    s1614_ra_fix_eq_one hΩ hg3' hX hgX' hgnt
  have hgg : ∀ b ∈ X, g (g b) = b * g b := by
    intro b hb
    have hbX : g b ∈ X := hgX' b hb
    have hb2X : g (g b) ∈ X := hgX' (g b) hbX
    have hsX : b * g b * g (g b) ∈ X := X.mul_mem (X.mul_mem hb hbX) hb2X
    have hsfix : g (b * g b * g (g b)) = b * g b * g (g b) := by
      rw [map_mul, map_mul, hg3' b]
      ac_rfl
    have hs1 : b * g b * g (g b) = 1 := hgfpf _ hsX hsfix
    have h2 : g (g b) = (b * g b)⁻¹ := eq_inv_of_mul_eq_one_right hs1
    rw [h2, inv_eq_of_mul_eq_one_right (hΩ (b * g b))]
  have hggmul : ∀ b ∈ X, g (g b) * g b = b := by
    intro b hb
    rw [hgg b hb, mul_assoc, hΩ (g b), mul_one]
  let φ : ↥X →* Ω :=
    MonoidHom.mk' (fun b : ↥X => g (b : Ω) * y (b : Ω)) (by
      intro a b
      change g (↑a * ↑b) * y (↑a * ↑b) = (g ↑a * y ↑a) * (g ↑b * y ↑b)
      rw [map_mul g, map_mul y]
      ac_rfl)
  have hφker : ∀ b : ↥X, φ b = 1 → b = 1 := by
    intro b hb
    have hgy : g (b : Ω) = y (b : Ω) := by
      have h := eq_inv_of_mul_eq_one_left hb
      rwa [inv_eq_of_mul_eq_one_right (hΩ (y (b : Ω)))] at h
    have hmemX : g (b : Ω) ∈ X := hgX' b b.2
    have hmemY : g (b : Ω) ∈ X.map y.toMonoidHom := by
      rw [hgy]
      exact Subgroup.mem_map_of_mem y.toMonoidHom b.2
    have hbot : g (b : Ω) ∈ (⊥ : Subgroup Ω) := by
      rw [← hXy]
      exact Subgroup.mem_inf.2 ⟨hmemX, hmemY⟩
    have hg1 : g (b : Ω) = 1 := by simpa using hbot
    have hb1 : (b : Ω) = 1 := g.injective (by rw [hg1, map_one])
    exact Subtype.ext hb1
  have hφinj : Function.Injective φ := (injective_iff_map_eq_one φ).2 hφker
  have hcard : Nat.card ↥(φ.range) = 4 := by
    have h := Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    rw [← hX]
    exact h.symm
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨b, rfl⟩ := hr
    change g (b : Ω) * y (b : Ω) ∈ X ⊔ X.map y.toMonoidHom
    exact Subgroup.mul_mem_sup (hgX' b b.2)
      (Subgroup.mem_map_of_mem y.toMonoidHom b.2)
  · have h1 : 2 ^ rk ↥(φ.range) = 2 ^ 2 := by
      rw [← card_eq_two_pow hΩ2 φ.range, hcard]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h1
  · intro r hr
    obtain ⟨b, rfl⟩ := hr
    change (y * g) (g (b : Ω) * y (b : Ω)) = g (b : Ω) * y (b : Ω)
    rw [MulAut.mul_apply, map_mul g, map_mul y, ← hyg' b, hyy (g (b : Ω))]
    have hrearr : y (g (g (b : Ω))) * (g (b : Ω) * y (g (b : Ω))) =
        y (g (g (b : Ω))) * y (g (b : Ω)) * g (b : Ω) := by ac_rfl
    rw [hrearr, ← map_mul y, hggmul b b.2, mul_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
