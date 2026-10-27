module

public import CFSG.RankThree.PartOne.NF7J.LRoots3
public import CFSG.RankThree.PartOne.S12.Sec1322Reflect

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS
open scoped commutatorElement

structure Datum {G : Type} [Group G] [Finite G] (p : ℕ) (E : Subgroup G) where
  H : Subgroup (MulAut E)
  e : ↥H ≃* GL (Fin 3) (ZMod 2)
  ν : MulAut E
  hν : ∀ x : E, ν x = x⁻¹
  hD : ∀ t ∈ reflectionSet p E, ∃ a ∈ H, a * a = 1 ∧ a ≠ 1 ∧ t = ν * a
  hD' : ∀ a ∈ H, a * a = 1 → a ≠ 1 → ν * a ∈ reflectionSet p E
  hHW : H ≤ torusWeyl E

namespace Datum

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} (D : Datum p E)

theorem ν_sq : D.ν * D.ν = 1 := by
  ext x
  simp [MulAut.mul_apply, D.hν]

theorem ν_comm (g : MulAut E) : g * D.ν = D.ν * g := by
  ext x
  simp [MulAut.mul_apply, D.hν, map_inv]

theorem ν_mul_ν_mul (a : MulAut E) : D.ν * (D.ν * a) = a := by
  rw [← mul_assoc, D.ν_sq, one_mul]

theorem exists_lift {x : MulAut E} (hx : x ∈ D.H) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), conjAut E w hw = x :=
  Sec1322.exists_lift (D.hHW hx)

theorem νmul_sq {a : MulAut E} (ha : a * a = 1) : (D.ν * a) * (D.ν * a) = 1 := by
  calc (D.ν * a) * (D.ν * a) = D.ν * (a * D.ν) * a := by simp only [mul_assoc]
    _ = D.ν * (D.ν * a) * a := by rw [D.ν_comm a]
    _ = (D.ν * D.ν) * (a * a) := by simp only [mul_assoc]
    _ = 1 := by rw [D.ν_sq, ha, one_mul]

theorem νmul_νmul (a b : MulAut E) : (D.ν * a) * (D.ν * b) = a * b := by
  calc (D.ν * a) * (D.ν * b) = D.ν * (a * D.ν) * b := by simp only [mul_assoc]
    _ = D.ν * (D.ν * a) * b := by rw [D.ν_comm a]
    _ = (D.ν * D.ν) * a * b := by simp only [mul_assoc]
    _ = a * b := by rw [D.ν_sq, one_mul]

end Datum

section FrameDatum

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K) (D : Datum p E)

theorem RFrame.r₀_sq : F.r₀ * F.r₀ = 1 := by
  have := pow_orderOf_eq_one F.r₀
  rwa [F.r₀_ref.1.1, sq] at this

theorem RFrame.r₁_sq : F.r₁ * F.r₁ = 1 := by
  have := pow_orderOf_eq_one F.r₁
  rwa [F.r₁_ref.1.1, sq] at this

theorem a₁_mem : D.ν * F.r₀ ∈ D.H := by
  obtain ⟨a, ha, -, -, hr⟩ := D.hD F.r₀ F.r₀_ref
  rw [hr, D.ν_mul_ν_mul]
  exact ha

theorem a₂_mem : D.ν * F.r₁ ∈ D.H := by
  obtain ⟨a, ha, -, -, hr⟩ := D.hD F.r₁ F.r₁_ref
  rw [hr, D.ν_mul_ν_mul]
  exact ha

theorem a₁_sq : (D.ν * F.r₀) * (D.ν * F.r₀) = 1 := D.νmul_sq F.r₀_sq

theorem a₂_sq : (D.ν * F.r₁) * (D.ν * F.r₁) = 1 := D.νmul_sq F.r₁_sq

theorem rho_mem : F.r₀ * F.r₁ ∈ D.H := by
  rw [← D.νmul_νmul F.r₀ F.r₁]
  exact D.H.mul_mem (a₁_mem F D) (a₂_mem F D)

theorem rho_pow_four : (F.r₀ * F.r₁) ^ 4 = 1 := by
  have := pow_orderOf_eq_one (F.r₀ * F.r₁)
  rwa [F.ord] at this

theorem rho_sq_ne : (F.r₀ * F.r₁) * (F.r₀ * F.r₁) ≠ 1 := by
  intro h
  have h2 : (F.r₀ * F.r₁) ^ 2 = 1 := by rw [sq]; exact h
  have := orderOf_dvd_of_pow_eq_one h2
  rw [F.ord] at this
  omega

theorem zz_sq : ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) = 1 := by
  have := rho_pow_four F
  calc ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) = (F.r₀ * F.r₁) ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := this

theorem zz_mem : (F.r₀ * F.r₁) * (F.r₀ * F.r₁) ∈ D.H := D.H.mul_mem (rho_mem F D) (rho_mem F D)

theorem zp_mem_reflectionSet :
    D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) ∈ reflectionSet p E :=
  D.hD' _ (zz_mem F D) (zz_sq F) (rho_sq_ne F)

structure EFacts (G : Type) [Group G] (p : ℕ) (c : G) (E : Subgroup G) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  c_mem : c ∈ E
  c_ne : c ≠ 1
  c_pow : c ^ p = 1
  comm : ∀ x y : E, x * y = y * x

variable (X : EFacts G p c E)

@[expose] def EFacts.cE : E := ⟨c, X.c_mem⟩

include F in
theorem torusImage_fix_c {t : MulAut E} (ht : t ∈ torusImage E L) : t X.cE = X.cE := by
  obtain ⟨x, hxL, hxE, rfl⟩ := KF132.exists_conjAut_of_mem_torusImage ht
  apply Subtype.ext
  rw [Equivariance.coe_conjAut hxE]
  show x * c * x⁻¹ = c
  rw [← F.hcL x hxL]
  group

theorem rho_fix_c : (F.r₀ * F.r₁) X.cE = X.cE := by
  rw [MulAut.mul_apply, torusImage_fix_c F X F.r₁_L, torusImage_fix_c F X F.r₀_L]

theorem zz_fix_c : ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) X.cE = X.cE := by
  rw [MulAut.mul_apply, rho_fix_c F X, rho_fix_c F X]

theorem zp_c : (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) X.cE = X.cE⁻¹ := by
  rw [MulAut.mul_apply, zz_fix_c F X, D.hν]

include X in
theorem moved_zp : autMovedInG E (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) = Subgroup.zpowers c := by
  have : Fact p.Prime := ⟨X.prime⟩
  have hp2 : p ≠ 2 := by have := X.five_le; omega
  set zp := D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) with hzp
  have hrefl : IsAutReflection p E zp := (zp_mem_reflectionSet F D).1
  have hc2 : X.cE ^ 2 ∈ autMoved E zp := by
    have h1 : zp X.cE * X.cE⁻¹ ∈ autMoved E zp := Subgroup.subset_closure ⟨X.cE, rfl⟩
    rw [zp_c F D X] at h1
    have h2 := (autMoved E zp).inv_mem h1
    have e : (X.cE⁻¹ * X.cE⁻¹)⁻¹ = X.cE ^ 2 := by group
    rwa [e] at h2
  have hcmem : X.cE ∈ autMoved E zp := by
    have hpow : X.cE ^ p = 1 := Subtype.ext X.c_pow
    have h3 : X.cE = (X.cE ^ 2) ^ ((p + 1) / 2) := by
      have hodd : p % 2 = 1 := by
        rcases hp2' : (Nat.Prime.eq_two_or_odd X.prime) with h | h
        · exact absurd h hp2
        · exact h
      have : 2 * ((p + 1) / 2) = p + 1 := by omega
      rw [← pow_mul, this, pow_succ, hpow, one_mul]
    rw [h3]
    exact (autMoved E zp).pow_mem hc2 _
  have hle : Subgroup.zpowers c ≤ autMovedInG E zp := by
    rw [Subgroup.zpowers_le]
    exact ⟨X.cE, hcmem, rfl⟩
  have hordc : orderOf c = p := orderOf_eq_prime X.c_pow X.c_ne
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_moved hrefl, Nat.card_zpowers, hordc]

end FrameDatum

end CFSG.RankThree.PartOne.NF7J
