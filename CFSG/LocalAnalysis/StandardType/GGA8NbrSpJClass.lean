module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpComp

public section

namespace CFSG.StandardType

namespace CoordSp

open Multiplicative CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped commutatorElement

@[expose] def SpCompShape {G : Type} [Group G] {F : Type} [Field F] {n p : ℕ}
    (ψ : StatedSp n F →* G) (A₀ : StatedSp n F) (β : Fin n → ZMod p) (L₁ : Subgroup G) : Prop :=
  (L₁ = ((blockSp (F := F) (spClass β 0)).range).map (frameConj ψ A₀) ∧
      1 ≤ (spClass β 0).card) ∨
    (∃ c : ZMod p, c ≠ 0 ∧
      L₁ = ((classHom (F := F) (spClass β c)).range).map (frameConj ψ A₀) ∧
        2 ≤ (spClass β c).card)

theorem comp_of_aligned_shape {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    [CharP F 2] {n p : ℕ} [Fact p.Prime] {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ}
    {hζ : ζ ^ p = 1} (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hψ : Function.Injective ψ)
    (hζo : orderOf ζ = p) {β : Fin n → ZMod p} (hal : SpAligned β) {L₁ : Subgroup G}
    (hb1 : frameHom ψ A₀ hζ (ofAdd β) ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ hζ (ofAdd β)})) :
    SpCompShape ψ A₀ β L₁ := by
  classical
  unfold SpCompShape
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (frameHom ψ A₀ hζ) := frameHom_injective ψ A₀ hζ hψ hζo
  have hβ0 : β ≠ 0 := fun h => hb1 (by rw [h, ofAdd_zero, map_one])
  have h4 : 4 ≤ Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h2 := Nat.le_of_dvd (by omega) hpF
    have h3 := hp.two_le
    omega
  have hb : frameHom ψ A₀ hζ (ofAdd β) = frameConj ψ A₀ (torusElt ζ β) := rfl
  rw [hb, centralizer_eq_map hψ A₀ ζ β] at hcomp
  have hφinj : Function.Injective (frameConj ψ A₀) := frameConj_injective hψ A₀
  have hmemC₀ : ∀ u, u ∈ Subgroup.centralizer ({torusElt ζ β} : Set (StatedSp n F)) ↔
      WtPres β (mat n F u) := fun u =>
    Subgroup.mem_centralizer_singleton_iff.trans (commute_torusElt_iff hζ hζo β u)
  set φ := frameConj ψ A₀ with hφdef
  set C₀ := Subgroup.centralizer ({torusElt ζ β} : Set (StatedSp n F)) with hC₀
  set KZ := suppGroup (n := n) (K := F) (planeSet (spClass β 0)) with hKZ
  set KC : ZMod p → Subgroup (StatedSp n F) := fun c => (classHom (F := F) (spClass β c)).range
    with hKC
  have hKZC : KZ ≤ C₀ := fun M hM => (hmemC₀ M).mpr (wtPres_of_mem_zeroBlock hM)
  have hKCC : ∀ c, KC c ≤ C₀ := by
    rintro c _ ⟨A, rfl⟩
    exact (hmemC₀ _).mpr (wtPres_classHom β c A)
  have hcommY : ∀ u ∈ C₀, u * torusElt ζ β = torusElt ζ β * u := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp hu
  have hKZn : ((KZ.map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_suppGroup hζ hζo (planeSet_zero_union β) (hcommY u hu) hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ c, c ≠ 0 → (((KC c).map φ).subgroupOf (C₀.map φ)).Normal := by
    intro c hc
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC c))]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_range_classHom hp2 hζ hζo hal hc (hcommY u hu) hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hq := hcomp.2.2
  by_cases hZ : L₁ ≤ KZ.map φ
  ·
    left
    have hrange : KZ.map φ = (φ.comp (blockSp (F := F) (spClass β 0))).range := by
      rw [MonoidHom.range_comp, range_blockSp]
    have hZ1 : 1 ≤ (spClass β 0).card := by
      by_contra h0
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      rw [hrange] at hZ
      obtain ⟨X, rfl⟩ := hZ hx
      obtain ⟨Z, rfl⟩ := hZ hy
      rw [← map_mul, ← map_mul, statedSp_comm_of_eq_zero (by omega) X Z]
    have hQ : CFSG.IsQuasisimple (StatedSp (spClass β 0).card F) :=
      CFSG.LieType.Universal.Symplectic.isQuasisimple _ F hZ1 (Or.inl (Or.inr h4))
    have hL₁ : L₁ = KZ.map φ := by
      have hc' :=
        CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hZ (Subgroup.map_mono hKZC)
      rw [hrange] at hc' ⊢
      exact CoordSL.eq_of_isComponentOf_range hQ _ hc'
    refine ⟨?_, hZ1⟩
    rw [hL₁, hKZ, range_blockSp (spClass β 0)]
  · by_cases hCex : ∃ c, c ≠ 0 ∧ L₁ ≤ (KC c).map φ
    ·
      right
      obtain ⟨c, hc, hLc⟩ := hCex
      have hrange : (KC c).map φ = (φ.comp (classHom (F := F) (spClass β c))).range :=
        (MonoidHom.range_comp _ _).symm
      rw [hrange] at hLc
      have hS2 : 2 ≤ (spClass β c).card := by
        by_contra h1
        refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
        obtain ⟨X, rfl⟩ := hLc hx
        obtain ⟨Z, rfl⟩ := hLc hy
        rw [← map_mul, ← map_mul, CoordSL.specialLinear_comm_of_le_one (by omega) X Z]
      have hQ : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (spClass β c).card) F) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple _ F hS2
          (Or.inr (by omega)) (Or.inr LinSemisimple.natCard_ne_three)
      have hL₁ : L₁ = (KC c).map φ := by
        have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hLc
          (by rw [← hrange]; exact Subgroup.map_mono (hKCC c))
        rw [hrange]
        exact CoordSL.eq_of_isComponentOf_range hQ _ hc'
      have hS : (spClass β c).Nonempty := Finset.card_pos.mp (by omega)
      refine ⟨c, hc, ?_, hS2⟩
      exact hL₁
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅L₁, KZ.map φ⁆ = ⊥ :=
        (CoordSL.le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono hKZC)
          hKZn).resolve_left hZ
      have hCb : ∀ c, c ≠ 0 → ⁅L₁, (KC c).map φ⁆ = ⊥ := fun c hc =>
        (CoordSL.le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono (hKCC c))
          (hKCn c hc)).resolve_left (hCex c hc)
      have hcommN : ∀ {N : Subgroup G}, ⁅L₁, N⁆ = ⊥ → ∀ x ∈ L₁, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hlift : ∀ w, φ w ∈ L₁ → (∀ M ∈ KZ, w * M = M * w) ∧
          ∀ c, c ≠ 0 → ∀ M ∈ KC c, w * M = M * w := by
        intro w hw
        refine ⟨fun M hM => hφinj ?_, fun c hc M hM => hφinj ?_⟩
        · rw [map_mul, map_mul]
          exact hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ hM)
        · rw [map_mul, map_mul]
          exact hcommN (hCb c hc) _ hw _ (Subgroup.mem_map_of_mem φ hM)
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hcomp.1 hx
      obtain ⟨v, hv, rfl⟩ := hcomp.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks hp2 hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hlift u hx).1 (hlift v hy).1 (hlift u hx).2 (hlift v hy).2]

end CoordSp

end CFSG.StandardType

end
