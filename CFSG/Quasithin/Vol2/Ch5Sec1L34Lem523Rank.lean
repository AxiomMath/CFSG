module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.Quasithin.Vol2.Ch10SecABasic
public import CFSG.Quasithin.Vol2.Ch10SecALift
public import CFSG.Quasithin.Vol2.Ch6Semilinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)
open scoped MatrixGroups

namespace S2A

variable {G : Type} [Group G]

@[expose] def commHom {X : Subgroup G} {d : G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hdX : d ∈ Subgroup.normalizer (X : Set G)) : ↥X →* ↥X where
  toFun x := ⟨(x : G) * d * (x : G)⁻¹ * d⁻¹, by
    have h1 : d * (x : G)⁻¹ * d⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hdX _).mp (X.inv_mem x.2)
    have := X.mul_mem x.2 h1
    simpa [mul_assoc] using this⟩
  map_one' := by ext; simp
  map_mul' x y := by
    apply Subtype.ext
    have hx : d * (x : G)⁻¹ * d⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hdX _).mp (X.inv_mem x.2)
    have hy : d * (y : G)⁻¹ * d⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hdX _).mp (X.inv_mem y.2)
    have h1 := hX _ y.2 _ hx
    simp only [Subgroup.coe_mul, mul_inv_rev]
    calc (x : G) * y * d * ((y : G)⁻¹ * (x : G)⁻¹) * d⁻¹ =
        (x : G) * (y * (d * (y : G)⁻¹ * d⁻¹)) * (d * (x : G)⁻¹ * d⁻¹) := by group
      _ = (x : G) * (d * (x : G)⁻¹ * d⁻¹) * (y * (d * (y : G)⁻¹ * d⁻¹)) := by
        rw [mul_assoc (x : G), hX _ (X.mul_mem y.2 hy) _ hx, ← mul_assoc]
      _ = (x : G) * d * (x : G)⁻¹ * d⁻¹ * ((y : G) * d * (y : G)⁻¹ * d⁻¹) := by group

theorem commHom_apply {X : Subgroup G} {d : G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hdX : d ∈ Subgroup.normalizer (X : Set G)) (x : ↥X) :
    ((commHom hX hdX x : ↥X) : G) = (x : G) * d * (x : G)⁻¹ * d⁻¹ := rfl

theorem commHom_eq_one_iff {X : Subgroup G} {d : G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hdX : d ∈ Subgroup.normalizer (X : Set G)) (x : ↥X) :
    commHom hX hdX x = 1 ↔ (x : G) ∈ Subgroup.centralizer ({d} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [Set.mem_singleton_iff.mp hy]
    have h1 := congrArg Subtype.val h
    rw [commHom_apply] at h1
    have h2 : (x : G) * d = d * x := by
      have := congrArg (· * (d * x)) h1
      simpa [mul_assoc] using this
    exact h2.symm
  · intro h
    apply Subtype.ext
    rw [commHom_apply]
    have h1 := h d rfl
    simp only [OneMemClass.coe_one]
    rw [← h1]
    group

theorem relIndex_centralizer_le [Finite G] {X Y : Subgroup G} {d : G}
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hdX : d ∈ Subgroup.normalizer (X : Set G))
    (hY : ∀ x ∈ X, x * d * x⁻¹ * d⁻¹ ∈ Y) :
    (Subgroup.centralizer ({d} : Set G)).relIndex X ≤ Nat.card Y := by
  set φ := commHom hX hdX with hφ
  have hker : φ.ker = (Subgroup.centralizer ({d} : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, commHom_eq_one_iff]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hmap : φ.range.map X.subtype ≤ Y := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact hY x x.2
  calc Nat.card φ.range = Nat.card (φ.range.map X.subtype) :=
        (Subgroup.card_map_of_injective X.subtype_injective).symm
    _ ≤ Nat.card Y := Subgroup.card_le_of_le hmap

end S2A

end CFSG.Quasithin.H13
