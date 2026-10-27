module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2

namespace CFSG
end CFSG
open CFSG

universe u

namespace CFSG.TBSScratch

open scoped commutatorElement IsMulCommutative

structure Baer (r : ℕ) (G : Type u) where
  val : G

instance {r : ℕ} {G : Type u} : CoeOut (Baer r G) G where
  coe x := x.val

@[simp] theorem Baer.ext_iff {r : ℕ} {G : Type u} {x y : Baer r G} :
    x = y ↔ x.val = y.val := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases x
    cases y
    simp at h
    simp [h]

def baerMul {r : ℕ} {G : Type u} [Group G] (x y : Baer r G) : Baer r G :=
  ⟨x.val * y.val * ⁅y.val, x.val⁆ ^ r⟩

def baerOne {r : ℕ} {G : Type u} [One G] : Baer r G := ⟨1⟩

def baerInv {r : ℕ} {G : Type u} [Inv G] (x : Baer r G) : Baer r G := ⟨x.val⁻¹⟩

instance {r : ℕ} {G : Type u} [Group G] : Mul (Baer r G) where
  mul := baerMul

instance {r : ℕ} {G : Type u} [One G] : One (Baer r G) where
  one := baerOne

instance {r : ℕ} {G : Type u} [Inv G] : Inv (Baer r G) where
  inv := baerInv

@[simp] theorem baer_coe_mul {r : ℕ} {G : Type u} [Group G] (x y : Baer r G) :
    ((x * y : Baer r G) : G) = (x : G) * (y : G) * ⁅(y : G), (x : G)⁆ ^ r := rfl

@[simp] theorem baer_coe_one {r : ℕ} {G : Type u} [One G] :
    ((1 : Baer r G) : G) = (1 : G) := rfl

@[simp] theorem baer_coe_inv {r : ℕ} {G : Type u} [Inv G] (x : Baer r G) :
    ((x⁻¹ : Baer r G) : G) = ((x : G)⁻¹ : G) := rfl

theorem commutator_mem_center_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.center G := by
  exact hcomm <|
    Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
      (show x ∈ (⊤ : Subgroup G) by trivial) (show y ∈ (⊤ : Subgroup G) by trivial)

theorem swap_mul_commutator_of_mem_center {G : Type u} [Group G] {x y : G}
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G) :
    y * x = x * y * ⁅y, x⁆ := by
  have hx : x * ⁅y, x⁆ = ⁅y, x⁆ * x := (Subgroup.mem_center_iff.mp hcomm) x
  have hy : y * ⁅y, x⁆ = ⁅y, x⁆ * y := (Subgroup.mem_center_iff.mp hcomm) y
  calc
    y * x = ⁅y, x⁆ * x * y := by
      simp [commutatorElement_def, mul_assoc]
    _ = x * ⁅y, x⁆ * y := by
      rw [← hx, mul_assoc]
    _ = x * (⁅y, x⁆ * y) := by
      simp [mul_assoc]
    _ = x * (y * ⁅y, x⁆) := by
      rw [← hy]
    _ = x * y * ⁅y, x⁆ := by
      simp [mul_assoc]

theorem commutator_mul_right_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hzcent : ⁅x, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm x z
  have hzy : y * ⁅x, z⁆ = ⁅x, z⁆ * y :=
    (Subgroup.mem_center_iff.mp hzcent y)
  calc
    ⁅x, y * z⁆ = ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ := by
      rw [commutator_mul_right]
    _ = ⁅x, y⁆ * (y * ⁅x, z⁆) * y⁻¹ := by simp [mul_assoc]
    _ = ⁅x, y⁆ * (⁅x, z⁆ * y) * y⁻¹ := by rw [hzy]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by simp [mul_assoc]

theorem commutator_mul_left_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hycent : ⁅y, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm y z
  have hxcent : ⁅x, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm x z
  have hxy : x * ⁅y, z⁆ = ⁅y, z⁆ * x :=
    (Subgroup.mem_center_iff.mp hycent x)
  have hyx : ⁅y, z⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ :=
    (Subgroup.mem_center_iff.mp hycent ⁅x, z⁆).symm
  calc
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
      rw [commutator_mul_left]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by
      rw [hxy]
      simp [mul_assoc]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hyx


theorem commutator_eq_one_of_right_mem_center {G : Type u} [Group G] {x z : G}
    (hz : z ∈ Subgroup.center G) :
    ⁅x, z⁆ = 1 := by
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz x))

theorem commutator_eq_one_of_left_mem_center {G : Type u} [Group G] {z x : G}
    (hz : z ∈ Subgroup.center G) :
    ⁅z, x⁆ = 1 := by
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz x).symm)

theorem commutator_right_baer_factor
    {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y * ⁅y, x⁆ ^ r⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  let c : G := ⁅y, x⁆
  have hc : c ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm y x
  have hcpow : c ^ r ∈ Subgroup.center G := (Subgroup.center G).pow_mem hc r
  calc
    ⁅z, x * y * c ^ r⁆ = ⁅z, x * y⁆ * ⁅z, c ^ r⁆ := by
      rw [commutator_mul_right_of_commutator_le_center hcomm]
    _ = ⁅z, x * y⁆ := by
      rw [commutator_eq_one_of_right_mem_center hcpow]
      simp
    _ = ⁅z, x⁆ * ⁅z, y⁆ := by
      rw [commutator_mul_right_of_commutator_le_center hcomm]

theorem commutator_left_baer_factor
    {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅y * z * ⁅z, y⁆ ^ r, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
  let c : G := ⁅z, y⁆
  have hc : c ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm z y
  have hcpow : c ^ r ∈ Subgroup.center G := (Subgroup.center G).pow_mem hc r
  calc
    ⁅y * z * c ^ r, x⁆ = ⁅y * z, x⁆ * ⁅c ^ r, x⁆ := by
      rw [commutator_mul_left_of_commutator_le_center hcomm]
    _ = ⁅y * z, x⁆ := by
      rw [commutator_eq_one_of_left_mem_center hcpow]
      simp
    _ = ⁅y, x⁆ * ⁅z, x⁆ := by
      rw [commutator_mul_left_of_commutator_le_center hcomm]

theorem center_three_mul_rotate {G : Type u} [Group G] {a b c : G}
    (ha : a ∈ Subgroup.center G) (hb : b ∈ Subgroup.center G)
    (hc : c ∈ Subgroup.center G) :
    a * (b * c) = c * (a * b) := by
  let aZ : Subgroup.center G := ⟨a, ha⟩
  let bZ : Subgroup.center G := ⟨b, hb⟩
  let cZ : Subgroup.center G := ⟨c, hc⟩
  have h : aZ * (bZ * cZ) = cZ * (aZ * bZ) := by
    simp [mul_assoc, mul_comm]
  exact congrArg Subtype.val h


def baerEquiv {G : Type u} {r : ℕ} : Baer r G ≃ G where
  toFun x := x.val
  invFun g := ⟨g⟩
  left_inv x := by cases x; rfl
  right_inv g := rfl

instance baerFinite {G : Type u} [Finite G] {r : ℕ} : Finite (Baer r G) :=
  Finite.of_equiv G (baerEquiv (G := G) (r := r)).symm

theorem smul_commutatorElement
    {A G : Type u} [Group A] [Group G] [MulDistribMulAction A G]
    (a : A) (x y : G) :
    a • ⁅x, y⁆ = ⁅a • x, a • y⁆ := by
  simp [commutatorElement_def]


theorem pow_two_mul_half_eq_self_of_pow_prime_eq_one
    {G : Type u} [Group G] {p r : ℕ}
    {c : G} (hc : c ^ p = 1) (hhalf : 2 * r = p + 1) :
    c ^ (2 * r) = c := by
  rw [hhalf, pow_succ, hc]
  simp


end CFSG.TBSScratch
