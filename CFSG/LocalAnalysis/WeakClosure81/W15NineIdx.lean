module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_mul_centMod {V₀ V W' Δ : Subgroup G} {y : G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV₀ : V₀ ≤ V) (hW' : W' ≤ V)
    (hgen : V ≤ W' ⊔ V₀) (hyV : y ∈ normalizer (V : Set G))
    (hyV₀ : y ∈ normalizer (V₀ : Set G)) (hΔ : Δ ≤ V)
    (hΔcard : Nat.card Δ ≤ 2) (hcomm : ∀ w ∈ W', y * w * y⁻¹ * w⁻¹ ∈ Δ) :
    Nat.card V ≤ 2 * Nat.card (centMod V₀ V y) := by
  have hmem : ∀ v : V, y * (v : G) * y⁻¹ * (v : G)⁻¹ ∈ V := fun v =>
    V.mul_mem ((Subgroup.mem_normalizer_iff.1 hyV v).1 v.2) (V.inv_mem v.2)
  have hcom : ∀ a b : V, (a : G) * b = b * a := fun a b => hVab _ a.2 _ b.2
  let φ : V →* V := MonoidHom.mk' (fun v => ⟨y * (v : G) * y⁻¹ * (v : G)⁻¹, hmem v⟩) (by
    intro a b
    apply Subtype.ext
    show y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹ =
      (y * (a : G) * y⁻¹ * (a : G)⁻¹) * (y * (b : G) * y⁻¹ * (b : G)⁻¹)
    have hc : (a : G)⁻¹ * (y * (b : G) * y⁻¹ * (b : G)⁻¹) =
        (y * (b : G) * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ := by
      have := hVab _ (V.inv_mem a.2) _ (hmem b)
      exact this
    calc y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹
        = (y * (a : G) * y⁻¹) * ((y * (b : G) * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (y * (a : G) * y⁻¹) * ((a : G)⁻¹ * (y * (b : G) * y⁻¹ * (b : G)⁻¹)) := by rw [hc]
      _ = _ := by group)
  haveI hN : (V₀.subgroupOf V).Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ = n := by
      apply Subtype.ext
      show (g : G) * n * (g : G)⁻¹ = n
      rw [mul_inv_eq_iff_eq_mul]
      exact hcom g n
    rwa [h1]⟩
  let θ : V →* V ⧸ V₀.subgroupOf V := (QuotientGroup.mk' (V₀.subgroupOf V)).comp φ
  have hker_iff : ∀ v : V, v ∈ θ.ker ↔ y * (v : G) * y⁻¹ * (v : G)⁻¹ ∈ V₀ := fun v =>
    (MonoidHom.mem_ker).trans ((QuotientGroup.eq_one_iff (φ v)).trans Subgroup.mem_subgroupOf)
  have hker : Nat.card θ.ker = Nat.card (centMod V₀ V y) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, (hker_iff x.1).1 x.2⟩
        invFun := fun z => ⟨⟨z.1, z.2.1⟩, (hker_iff ⟨z.1, z.2.1⟩).2 z.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  have hrange : Nat.card θ.range ≤ 2 := by
    have hle : θ.range ≤ (Δ.subgroupOf V).map (QuotientGroup.mk' (V₀.subgroupOf V)) := by
      rintro _ ⟨v, rfl⟩
      have htop : (⊤ : Subgroup V) ≤ ((Δ.subgroupOf V).map
          (QuotientGroup.mk' (V₀.subgroupOf V))).comap θ := by
        rw [← Subgroup.subgroupOf_eq_top.2 hgen, Subgroup.subgroupOf_sup hW' hV₀]
        refine sup_le (fun w hw => ?_) (fun v hv => ?_)
        · refine Subgroup.mem_map.2 ⟨φ w, Subgroup.mem_subgroupOf.2 (hcomm _ hw), rfl⟩
        · have : θ v = 1 := (hker_iff v).2 (V₀.mul_mem
            ((Subgroup.mem_normalizer_iff.1 hyV₀ v).1 hv) (V₀.inv_mem hv))
          rw [Subgroup.mem_comap, this]
          exact Subgroup.one_mem _
      exact htop (Subgroup.mem_top v)
    haveI : Finite (Δ.subgroupOf V) := inferInstance
    calc Nat.card θ.range ≤ Nat.card ((Δ.subgroupOf V).map (QuotientGroup.mk' (V₀.subgroupOf V))) :=
          Subgroup.card_le_of_le hle
      _ ≤ Nat.card (Δ.subgroupOf V) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
      _ = Nat.card Δ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΔ).toEquiv
      _ ≤ 2 := hΔcard
  calc Nat.card V = Nat.card θ.ker * Nat.card θ.range := (Subgroup.card_ker_mul_card_range θ).symm
    _ ≤ Nat.card (centMod V₀ V y) * 2 := by
        rw [hker]
        exact Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card (centMod V₀ V y) := Nat.mul_comm _ _

end CFSG.LocalAnalysis.WeakClosure81
