module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.H13.I1277

theorem relIndex_ne_zero_of_finite {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_le_card_of_fiber {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    {α : Type*} [Finite α] (φ : H → α) (hφ : ∀ x y : H, φ x = φ y ↔ (x : G)⁻¹ * (y : G) ∈ K) :
    K.relIndex H ≤ Nat.card α := by
  classical
  let ψ : H ⧸ K.subgroupOf H → α := Quotient.lift φ fun a b hab =>
    (hφ a b).mpr (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab))
  have hinj : Function.Injective ψ := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : φ a = φ b := hpq
    exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ((hφ a b).mp h1))
  exact Nat.card_le_card_of_injective ψ hinj

theorem le_relIndex_of_fiber {G : Type*} [Group G] [Finite G] {H K : Subgroup G} {ι : Type*}
    [Finite ι] (f : ι → H) (hf : ∀ i j, (f i : G)⁻¹ * (f j : G) ∈ K → i = j) :
    Nat.card ι ≤ K.relIndex H := by
  classical
  have hinj : Function.Injective
      (fun i => (QuotientGroup.mk (f i) : H ⧸ K.subgroupOf H)) := by
    intro i j hij
    exact hf i j (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hij))
  exact Nat.card_le_card_of_injective _ hinj

theorem relIndex_mul_relIndex_lt {G : Type*} [Group G] [Finite G] {H B U : Subgroup G} {z : G}
    (hBH : B ≤ H) (hzU : z ∈ U) (hz1 : z ≠ 1) (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hC : H ⊓ Subgroup.centralizer ({z} : Set G) ≤ B) :
    B.relIndex H * (Subgroup.centralizer ({z} : Set G)).relIndex B < Nat.card U := by
  classical
  set X : Subgroup G := H ⊓ Subgroup.centralizer ({z} : Set G) with hX
  have hXB : X ≤ B := hC
  have htower : X.relIndex B * B.relIndex H = X.relIndex H :=
    Subgroup.relIndex_mul_relIndex X B H hXB hBH
  have hCX : (Subgroup.centralizer ({z} : Set G)).relIndex B = X.relIndex B := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, hX, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hBH x.2, hx⟩, fun hx => hx.2⟩
  have hbound : X.relIndex H < Nat.card U := by
    let φ : H → {u : U // u ≠ 1} := fun x =>
      ⟨⟨(x : G) * z * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hHU x.2) z).mp hzU⟩, by
        intro h
        apply hz1
        have h' : (x : G) * z * (x : G)⁻¹ = 1 := congrArg Subtype.val h
        calc z = (x : G)⁻¹ * ((x : G) * z * (x : G)⁻¹) * (x : G) := by group
          _ = 1 := by rw [h']; group⟩
    have hφ : ∀ x y : H, φ x = φ y ↔ (x : G)⁻¹ * (y : G) ∈ X := by
      intro x y
      have hc : ((x : G)⁻¹ * (y : G)) ∈ H := H.mul_mem (H.inv_mem x.2) y.2
      have hiff : (x : G) * z * (x : G)⁻¹ = (y : G) * z * (y : G)⁻¹ ↔
          ((x : G)⁻¹ * (y : G)) * z = z * ((x : G)⁻¹ * (y : G)) := by
        constructor
        · intro h
          have hcc : ((x : G)⁻¹ * (y : G)) * z * ((x : G)⁻¹ * (y : G))⁻¹ = z := by
            calc ((x : G)⁻¹ * (y : G)) * z * ((x : G)⁻¹ * (y : G))⁻¹
                = (x : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (x : G) := by group
              _ = (x : G)⁻¹ * ((x : G) * z * (x : G)⁻¹) * (x : G) := by rw [h]
              _ = z := by group
          exact (mul_inv_eq_iff_eq_mul).mp hcc
        · intro h
          set c : G := (x : G)⁻¹ * (y : G) with hcdef
          have hy : (y : G) = (x : G) * c := by rw [hcdef]; group
          have hcc : c * z * c⁻¹ = z := (mul_inv_eq_iff_eq_mul).mpr h
          rw [hy]
          calc (x : G) * z * (x : G)⁻¹ = (x : G) * (c * z * c⁻¹) * (x : G)⁻¹ := by rw [hcc]
            _ = (x : G) * c * z * ((x : G) * c)⁻¹ := by group
      have hmemX : ((x : G)⁻¹ * (y : G)) ∈ X ↔
          ((x : G)⁻¹ * (y : G)) * z = z * ((x : G)⁻¹ * (y : G)) := by
        constructor
        · intro hm
          exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hm).2
        · intro hm
          exact Subgroup.mem_inf.mpr ⟨hc, Subgroup.mem_centralizer_singleton_iff.mpr hm⟩
      rw [hmemX, ← hiff]
      constructor
      · intro h
        exact congrArg (fun p : {u : U // u ≠ 1} => ((p : U) : G)) h
      · intro h
        exact Subtype.ext (Subtype.ext h)
    have hcard := relIndex_le_card_of_fiber φ hφ
    have hlt : Nat.card {u : U // u ≠ 1} < Nat.card U :=
      Finite.card_subtype_lt (p := fun u : U => u ≠ 1) (x := 1) (by simp)
    exact lt_of_le_of_lt hcard hlt
  rw [hCX, mul_comm, htower]
  exact hbound

end CFSG.Quasithin.H13.I1277
