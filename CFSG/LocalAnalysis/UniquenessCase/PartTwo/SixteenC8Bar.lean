module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Sp6P
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixModelTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)

theorem c8_le_pullSub_range_of_normal {H' : Type} [Group H'] {H : Subgroup H'}
    (ψ : ↥H ≃* ↥(StatedSp 3 (ZMod 2))) {X : Subgroup H'}
    (hX : X ≤ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)))
    (hXn : ∀ g ∈ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)), ∀ x ∈ X,
      g * x * g⁻¹ ∈ X)
    (h3 : ¬ 3 ∣ Nat.card X) : X ≤ pullSub ψ (tauSym 3).range := by
  have hXH : X ≤ H := hX.trans (pullSub_le ψ _)
  let Y : Subgroup (StatedSp 3 (ZMod 2)) := (X.subgroupOf H).map ψ.toMonoidHom
  have hXY : X = pullSub ψ Y := eq_pullSub_of_le ψ hXH
  have hYP : Y ≤ stabilizer 3 (ZMod 2) (lagrangianZero 3) := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : (x : H') ∈ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) :=
      hX (Subgroup.mem_subgroupOf.1 hx)
    simpa using (mem_pullSub.1 hx').2
  have hYn : ∀ g ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3), ∀ y ∈ Y,
      g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hgs : ((ψ.symm g : ↥H) : H') ∈
        pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) :=
      mem_pullSub.2 ⟨(ψ.symm g).2, by rw [MulEquiv.apply_symm_apply]; exact hg⟩
    refine Subgroup.mem_map.2 ⟨(ψ.symm g : ↥H) * x * (ψ.symm g : ↥H)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hXn _ hgs _ (Subgroup.mem_subgroupOf.1 hx)
    · show ψ ((ψ.symm g) * x * (ψ.symm g)⁻¹) = g * ψ x * g⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hcard : Nat.card Y = Nat.card X := by
    rw [hXY, card_pullSub ψ Y]
  have h3Y : ¬ 3 ∣ Nat.card Y := by
    rw [hcard]
    exact h3
  have hYle : Y ≤ (tauSym 3).range := c8_le_range_tauSym_of_normal hYP hYn h3Y
  rw [hXY]
  exact pullSub_mono ψ hYle

theorem c8_mem_pullSub_range_of_commutator_mem {H' : Type} [Group H'] {H : Subgroup H'}
    (ψ : ↥H ≃* ↥(StatedSp 3 (ZMod 2))) {s : H'}
    (hs : s ∈ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)))
    (h : ∀ p ∈ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)),
      s * p * s⁻¹ * p⁻¹ ∈ pullSub ψ (tauSym 3).range) :
    s ∈ pullSub ψ (tauSym 3).range := by
  obtain ⟨hsH, hsP⟩ := mem_pullSub.1 hs
  have key : ∀ p ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3),
      ψ ⟨s, hsH⟩ * p * (ψ ⟨s, hsH⟩)⁻¹ * p⁻¹ ∈ (tauSym 3).range := by
    intro p hp
    have hp' : ((ψ.symm p : ↥H) : H') ∈
        pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) :=
      mem_pullSub.2 ⟨(ψ.symm p).2, by rw [MulEquiv.apply_symm_apply]; exact hp⟩
    obtain ⟨hm, hR⟩ := mem_pullSub.1 (h _ hp')
    have hthis : ψ ⟨s * ((ψ.symm p : ↥H) : H') * s⁻¹ * ((ψ.symm p : ↥H) : H')⁻¹, hm⟩
        = ψ ⟨s, hsH⟩ * p * (ψ ⟨s, hsH⟩)⁻¹ * p⁻¹ := by
      have hsub : (⟨s * ((ψ.symm p : ↥H) : H') * s⁻¹ *
            ((ψ.symm p : ↥H) : H')⁻¹, hm⟩ : ↥H)
          = ⟨s, hsH⟩ * ψ.symm p * ⟨s, hsH⟩⁻¹ * (ψ.symm p)⁻¹ := Subtype.ext rfl
      rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    rw [← hthis]
    exact hR
  exact mem_pullSub.2 ⟨hsH, c8_mem_range_tauSym_of_commutator_mem hsP key⟩

variable {G : Type} [Group G] [Finite G]

theorem c8_card_barSub_dvd (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (X : Subgroup G) :
    Nat.card (barSub V₀ V hV X) ∣ Nat.card X := by
  have h1 : Nat.card (barSub V₀ V hV X) ∣ Nat.card (X.subgroupOf (stabTil V₀ V)) :=
    Subgroup.card_map_dvd (X.subgroupOf (stabTil V₀ V)) (actTil V₀ V hV)
  have h2 : Nat.card (X.subgroupOf (stabTil V₀ V)) = Nat.card ↥(X ⊓ stabTil V₀ V) := by
    rw [← Subgroup.inf_subgroupOf_right X (stabTil V₀ V)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h2] at h1
  exact h1.trans (Subgroup.card_dvd_of_le inf_le_left)

theorem c8_conj_mem_barSub (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {X Y : Subgroup G}
    (hYX : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X) :
    ∀ g ∈ barSub V₀ V hV Y, ∀ x ∈ barSub V₀ V hV X, g * x * g⁻¹ ∈ barSub V₀ V hV X := by
  intro g hg x hx
  obtain ⟨a, haY, rfl⟩ := (mem_barSub V₀ V hV Y g).1 hg
  obtain ⟨b, hbX, rfl⟩ := (mem_barSub V₀ V hV X x).1 hx
  refine (mem_barSub V₀ V hV X _).2 ⟨a * b * a⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  show (a : G) * (b : G) * (a : G)⁻¹ ∈ X
  exact hYX _ haY _ hbX

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
