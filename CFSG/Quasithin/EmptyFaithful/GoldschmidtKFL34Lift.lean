module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.Quasithin.SBd19F

open Subgroup

variable {K : Type} [Group K]

theorem commutator_mem_center_of_comm {g d : K}
    (h : (d : K ⧸ center K) * (g : K ⧸ center K) = (g : K ⧸ center K) * d) :
    d * g * d⁻¹ * g⁻¹ ∈ center K := by
  apply (QuotientGroup.eq_one_iff _).mp
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, h]
  group

@[expose] def zetaHom (g : K) (U₀ : Subgroup (K ⧸ center K))
    (hc : ∀ s ∈ U₀, s * (g : K ⧸ center K) = (g : K ⧸ center K) * s) :
    U₀.comap (QuotientGroup.mk' (center K)) →* center K where
  toFun d := ⟨(d : K) * g * (d : K)⁻¹ * g⁻¹, commutator_mem_center_of_comm (hc _ d.2)⟩
  map_one' := by
    apply Subtype.ext
    change (1 : K) * g * (1 : K)⁻¹ * g⁻¹ = 1
    group
  map_mul' d d' := by
    apply Subtype.ext
    have hd' : (d' : K) * g * (d' : K)⁻¹ * g⁻¹ ∈ center K :=
      commutator_mem_center_of_comm (hc _ d'.2)
    have hcomm := fun y : K => mem_center_iff.mp hd' y
    change (d : K) * (d' : K) * g * ((d : K) * (d' : K))⁻¹ * g⁻¹ =
      ((d : K) * g * (d : K)⁻¹ * g⁻¹) * ((d' : K) * g * (d' : K)⁻¹ * g⁻¹)
    calc (d : K) * (d' : K) * g * ((d : K) * (d' : K))⁻¹ * g⁻¹
        = (d : K) * ((d' : K) * g * (d' : K)⁻¹ * g⁻¹) * (g * (d : K)⁻¹ * g⁻¹) := by group
      _ = ((d' : K) * g * (d' : K)⁻¹ * g⁻¹) * (d : K) * (g * (d : K)⁻¹ * g⁻¹) := by
          rw [← hcomm (d : K)]
      _ = ((d : K) * g * (d : K)⁻¹ * g⁻¹) * ((d' : K) * g * (d' : K)⁻¹ * g⁻¹) := by
          rw [hcomm ((d : K) * g * (d : K)⁻¹ * g⁻¹)]
          group

theorem zetaHom_eq_one_of_mem (g : K) {U₀ Z₀ : Subgroup (K ⧸ center K)}
    (hc : ∀ s ∈ U₀, s * (g : K ⧸ center K) = (g : K ⧸ center K) * s)
    (hZ : ∀ z ∈ Z₀, ∃ a ∈ U₀, ∃ b ∈ U₀, z = a * b * a⁻¹ * b⁻¹)
    (d : U₀.comap (QuotientGroup.mk' (center K)))
    (hd : QuotientGroup.mk' (center K) (d : K) ∈ Z₀) : zetaHom g U₀ hc d = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := hZ _ hd
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center K) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center K) b
  let A : U₀.comap (QuotientGroup.mk' (center K)) := ⟨a', ha⟩
  let B : U₀.comap (QuotientGroup.mk' (center K)) := ⟨b', hb⟩
  have hπ : QuotientGroup.mk' (center K) ((A * B * A⁻¹ * B⁻¹ : U₀.comap
      (QuotientGroup.mk' (center K))) : K) = QuotientGroup.mk' (center K) (d : K) := by
    rw [hab]
    simp [A, B]
  have hz : (((A * B * A⁻¹ * B⁻¹)⁻¹ * d : U₀.comap (QuotientGroup.mk' (center K))) : K) ∈
      center K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center K) ((((A * B * A⁻¹ * B⁻¹)⁻¹ * d : U₀.comap
      (QuotientGroup.mk' (center K))) : K)) = 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    have := hπ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at this
    rw [this, inv_mul_cancel]
  have hζz : zetaHom g U₀ hc ((A * B * A⁻¹ * B⁻¹)⁻¹ * d) = 1 := by
    apply Subtype.ext
    change (((A * B * A⁻¹ * B⁻¹)⁻¹ * d : U₀.comap (QuotientGroup.mk' (center K))) : K) * g *
      (((A * B * A⁻¹ * B⁻¹)⁻¹ * d : U₀.comap (QuotientGroup.mk' (center K))) : K)⁻¹ * g⁻¹ = 1
    rw [← mem_center_iff.mp hz g]
    group
  have hζ0 : zetaHom g U₀ hc (A * B * A⁻¹ * B⁻¹) = 1 := by
    apply Subtype.ext
    have hcomm := mem_center_iff.mp (zetaHom g U₀ hc B).2 (zetaHom g U₀ hc A : K)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [hcomm]
    group
  calc zetaHom g U₀ hc d
      = zetaHom g U₀ hc ((A * B * A⁻¹ * B⁻¹) * ((A * B * A⁻¹ * B⁻¹)⁻¹ * d)) := by
        rw [mul_inv_cancel_left]
    _ = 1 := by rw [map_mul, hζ0, hζz, one_mul]

theorem exists_fixed_lift_not_mem [Finite K] (g : K) {U₀ Z₀ : Subgroup (K ⧸ center K)}
    (hc : ∀ s ∈ U₀, s * (g : K ⧸ center K) = (g : K ⧸ center K) * s)
    (hsq : ∀ s ∈ U₀, s * s ∈ Z₀)
    (hZ : ∀ z ∈ Z₀, ∃ a ∈ U₀, ∃ b ∈ U₀, z = a * b * a⁻¹ * b⁻¹)
    (hΩ : Nat.card {z : center K // z * z = 1} ≤ 4)
    (hcard : 4 * Nat.card Z₀ < Nat.card U₀) :
    ∃ d : K, (d : K ⧸ center K) ∈ U₀ ∧ (d : K ⧸ center K) ∉ Z₀ ∧ d * g = g * d := by
  classical
  let H : Subgroup K := U₀.comap (QuotientGroup.mk' (center K))
  let ζ := zetaHom g U₀ hc
  have hsqζ : ∀ d : H, ζ d * ζ d = 1 := fun d => by
    rw [← map_mul]
    exact zetaHom_eq_one_of_mem g hc hZ (d * d) (by
      simpa only [Subgroup.coe_mul, map_mul] using hsq _ d.2)
  have hlift : ∀ s : U₀, ∃ d : H, QuotientGroup.mk' (center K) (d : K) = s := fun s => by
    obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective (center K) s.1
    exact ⟨⟨d, by simp only [H, Subgroup.mem_comap, hd]; exact s.2⟩, hd⟩
  choose lift hlift using hlift
  let F : U₀ → {z : center K // z * z = 1} := fun s => ⟨ζ (lift s), hsqζ _⟩
  have : Fintype U₀ := Fintype.ofFinite _
  have : Fintype {z : center K // z * z = 1} := Fintype.ofFinite _
  obtain ⟨w, -, hw⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (Finset.univ : Finset U₀)) (t := (Finset.univ : Finset {z : center K // z * z = 1}))
    (f := F) (n := Nat.card Z₀) (fun _ _ => Finset.mem_univ _) (by
      rw [Finset.card_univ, Finset.card_univ, ← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hΩ) hcard)
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ Finset.filter (fun x => F x = w) Finset.univ := by
    apply Finset.card_pos.mp
    exact lt_of_le_of_lt (Nat.zero_le _) hw
  obtain ⟨s, hs, hsZ⟩ : ∃ s ∈ Finset.filter (fun x => F x = w) Finset.univ,
      (s : K ⧸ center K) * (s₀ : K ⧸ center K)⁻¹ ∉ Z₀ := by
    by_contra hcon
    push Not at hcon
    let φ : {x // x ∈ Finset.filter (fun x => F x = w) Finset.univ} → Z₀ := fun x =>
      ⟨(x.1 : K ⧸ center K) * (s₀ : K ⧸ center K)⁻¹, hcon x.1 x.2⟩
    have hφ : Function.Injective φ := fun x y hxy => by
      have h1 := congrArg Subtype.val hxy
      have h2 : (x.1 : K ⧸ center K) = (y.1 : K ⧸ center K) := mul_right_cancel h1
      exact Subtype.ext (Subtype.ext h2)
    have := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
    omega
  have hF : F s = F s₀ := by
    rw [(Finset.mem_filter.mp hs).2, (Finset.mem_filter.mp hs₀).2]
  have hζ : ζ (lift s) = ζ (lift s₀) := congrArg (fun z => (z.1 : center K)) hF
  have hπd : (((lift s : K) * (lift s₀ : K)⁻¹ : K) : K ⧸ center K) =
      (s : K ⧸ center K) * (s₀ : K ⧸ center K)⁻¹ := by
    have h := congrArg₂ (fun x y : K ⧸ center K => x * y⁻¹) (hlift s) (hlift s₀)
    exact h
  refine ⟨(lift s : K) * (lift s₀ : K)⁻¹, ?_, ?_, ?_⟩
  · rw [hπd]
    exact U₀.mul_mem s.2 (U₀.inv_mem s₀.2)
  · rw [hπd]
    exact hsZ
  · have h1 : ζ (lift s * (lift s₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, hζ, mul_inv_cancel]
    have h2 := congrArg Subtype.val h1
    change (lift s : K) * (lift s₀ : K)⁻¹ * g * ((lift s : K) * (lift s₀ : K)⁻¹)⁻¹ * g⁻¹ = 1 at h2
    have h3 := mul_inv_eq_one.mp h2
    exact (mul_inv_eq_iff_eq_mul.mp h3)

end CFSG.Quasithin.SBd19F
