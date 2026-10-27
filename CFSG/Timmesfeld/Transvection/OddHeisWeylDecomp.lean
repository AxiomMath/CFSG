module

public import CFSG.Timmesfeld.Transvection.OddHeisFrameBasics

import CFSG.Timmesfeld.Transvection.OddLocal
import CFSG.Timmesfeld.Transvection.OddNormalize
import CFSG.Timmesfeld.Transvection.OddPairsFrame
import CFSG.Timmesfeld.Transvection.OddResidueOrder
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.Transvection.OddResidueBlock

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres CFSG.LocalAnalysis.UniquenessCase
open scoped commutatorElement

private lemma eq_conj_of_commute_mul {G : Type*} [Group G] {y u x X : G}
    (hX : X = y * u * y * x * (y * u * y)⁻¹) (h : Commute y X) :
    y * x * y⁻¹ = u⁻¹ * X * u := by
  subst hX
  have h3 : y⁻¹ * (y * u * y * x * (y * u * y)⁻¹) * y =
      y * u * y * x * (y * u * y)⁻¹ := by
    calc y⁻¹ * (y * u * y * x * (y * u * y)⁻¹) * y
        = y⁻¹ * ((y * u * y * x * (y * u * y)⁻¹) * y) := by group
      _ = y⁻¹ * (y * (y * u * y * x * (y * u * y)⁻¹)) := by rw [← h.eq]
      _ = y * u * y * x * (y * u * y)⁻¹ := by group
  have h2 : y * u * y * x * (y * u * y)⁻¹ = u * (y * x * y⁻¹) * u⁻¹ := by
    rw [← h3]
    group
  calc y * x * y⁻¹ = u⁻¹ * (u * (y * x * y⁻¹) * u⁻¹) * u := by group
    _ = u⁻¹ * (y * u * y * x * (y * u * y)⁻¹) * u := by rw [h2]

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H] {Δ : Set (Subgroup H)}
  {P Q : Fin (2 * r / 2) → Subgroup H} (hm : 4 ≤ 2 * r)

private lemma mem_crossShortRootGroup_prev_last
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q) (c : F) :
    R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c ∈
        shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
          (Q (cLastIdx r hr)) (P (cLastIdx r hr)) ∧
      R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) ∈
        shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
          (Q (cPrevIdx r hr)) (P (cPrevIdx r hr)) := by
  have hik : cPrevIdx r hr ≠ cLastIdx r hr := cPrevIdx_ne_cLastIdx hr
  have hidx_lr : idx (Sum.inl (cPrevIdx r hr) : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) ≠
      idx (Sum.inr (cLastIdx r hr)) := by simpa using hik
  have hidx_rl : idx (Sum.inl (cLastIdx r hr) : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) ≠
      idx (Sum.inr (cPrevIdx r hr)) := by simpa using hik.symm
  constructor
  · simpa using (hR.short (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) hidx_lr
      (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)).2 ⟨c, rfl⟩
  · simpa using (hR.short (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) hidx_rl
      (R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹))).2 ⟨-c⁻¹, rfl⟩


private lemma residueGroup_le_normalizer_pointGroup
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q (cLastIdx r hr))
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ) :
    residueGroup Δ P Q (cPrevIdx r hr) ≤ Subgroup.normalizer
      (↑(((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
            (Q (cPrevIdx r hr)) (P (cPrevIdx r hr)) ⊔
          shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
            (P (cPrevIdx r hr)) (Q (cPrevIdx r hr)) ⊔ P (cLastIdx r hr))) : Subgroup H)) := by
  have hik : cPrevIdx r hr ≠ cLastIdx r hr := cPrevIdx_ne_cLastIdx hr
  have hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P (cLastIdx r hr) :=
    (hR.map_su3Top_su3Bot_of_comp hFn hr hm hθc).1
  have hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q (cLastIdx r hr) :=
    (hR.map_su3Top_su3Bot_of_comp hFn hr hm hθc).2
  exact hF.residueGroup_le_normalizer_map_heis_sup (k := cLastIdx r hr) h hML hq hns hFn
    hcard hθr hθo hθt hθb hθmem (i := cPrevIdx r hr) hik

private lemma mem_heisRootGroup_conj_mul
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q (cLastIdx r hr))
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {x W ws : H}
    (hW : W = R.toHom hFn (even_two_mul r) hm
      (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr)))
    (hDx : (W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹ ∈
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) :
    W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹ ∈
        (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ∧
      W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹ ∈ Subgroup.normalizer
        (↑(((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
          (shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
              (Q (cPrevIdx r hr)) (P (cPrevIdx r hr)) ⊔
            shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
              (P (cPrevIdx r hr)) (Q (cPrevIdx r hr)) ⊔ P (cLastIdx r hr))) : Subgroup H)) := by
  obtain ⟨A, hA_mem, hA⟩ := hDx
  have hxhat_eq : W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹ =
      W * θ A * W⁻¹ := by
    rw [← hA]
  have hθr' : (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).range =
      residueGroup Δ P Q (cPrevIdx r hr) :=
    (hF.su3_residue_oddPrevLift hFn hr hm h.cls.root hns hR hθr hθc hθmem).1
  have hxhatBP : W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹ ∈
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
        (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) := by
    rw [hxhat_eq, hW, ← oddPrevLift_apply (hFn := hFn) (hr := hr)
      (Ψ₀ := R.toHom hFn (even_two_mul r) hm) (θ := θ) A]
    exact Subgroup.mem_map_of_mem _ hA_mem
  have hxhat_res : W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹ ∈
      residueGroup Δ P Q (cPrevIdx r hr) := by
    rw [← hθr']
    exact Subgroup.map_le_range _ _ hxhatBP
  exact ⟨hxhatBP, (residueGroup_le_normalizer_pointGroup hFn hr hm h hML hq hF hns hcard
    hR hθr hθo hθc hθmem) hxhat_res⟩

private lemma commutator_mem_pointGroup
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q (cLastIdx r hr))
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {c : F} {x : H} (hx : x ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) :
    ⁅R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c, x⁆ ∈
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ⊔
        (shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
            (Q (cLastIdx r hr)) (P (cLastIdx r hr)) ⊔
          shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
            (P (cLastIdx r hr)) (Q (cLastIdx r hr)) ⊔ P (cPrevIdx r hr))) := by
  have hik : cPrevIdx r hr ≠ cLastIdx r hr := cPrevIdx_ne_cLastIdx hr
  have hΔ : IsRootClass Δ := h.cls.root
  obtain ⟨hθr', hnsP, hθmem', -⟩ :=
    hF.su3_residue_oddPrevLift hFn hr hm hΔ hns hR hθr hθc hθmem
  obtain ⟨hθo', hθt', hθb'⟩ :=
    hF.oddPrevLift_normalized hFn hr hm hΔ hns hR hθr hθo hθc hθmem
  have hyY : R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c ∈
      shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
        (Q (cLastIdx r hr)) (P (cLastIdx r hr)) :=
    (mem_crossShortRootGroup_prev_last hr hR c).1
  have hyUP : R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c ∈
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ⊔
        (shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
            (Q (cLastIdx r hr)) (P (cLastIdx r hr)) ⊔
          shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
            (P (cLastIdx r hr)) (Q (cLastIdx r hr)) ⊔ P (cPrevIdx r hr))) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_sup_left hyY))
  have hxres : x ∈ residueGroup Δ P Q (cLastIdx r hr) := by
    rw [← hθr]
    exact Subgroup.map_le_range θ _ hx
  exact hF.commutatorElement_mem_map_heis_sup (k := cPrevIdx r hr) (i := cLastIdx r hr)
    h hML hq hnsP hFn hcard hθr' hθo' hθt' hθb' hθmem' hik.symm
    (x := R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c) (b := x) hyUP hxres

private lemma commuting_heisRootGroup_crossShortRootGroup
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q (cLastIdx r hr))
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ) :
    Commuting
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
        (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ))
      (shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
        (Q (cLastIdx r hr)) (P (cLastIdx r hr))) := by
  have hik : cPrevIdx r hr ≠ cLastIdx r hr := cPrevIdx_ne_cLastIdx hr
  have hΔ : IsRootClass Δ := h.cls.root
  obtain ⟨hθr', hnsP, hθmem', -⟩ :=
    hF.su3_residue_oddPrevLift hFn hr hm hΔ hns hR hθr hθc hθmem
  obtain ⟨hθo', hθt', hθb'⟩ :=
    hF.oddPrevLift_normalized hFn hr hm hΔ hns hR hθr hθo hθc hθmem
  exact (IsFrame.commuting_map_heis_shortRootGroup (k := cPrevIdx r hr) h hML hq
    hF.toIsFrame hFn hcard hθr' hθt' hθb' (i := cLastIdx r hr) hik.symm).1

private lemma weylDecompositionData
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q (cLastIdx r hr))
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {c : F} {x W ws : H}
    (hW : W = R.toHom hFn (even_two_mul r) hm
      (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr)))
    (hx : x ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hDx : (W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹ ∈
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) :
    R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c ∈
        shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
          (Q (cLastIdx r hr)) (P (cLastIdx r hr)) ∧
      R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) ∈
        shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
          (Q (cPrevIdx r hr)) (P (cPrevIdx r hr)) ∧
      W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹ ∈
        (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ∧
      W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹ ∈ Subgroup.normalizer
        (↑(((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
          (shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
              (Q (cPrevIdx r hr)) (P (cPrevIdx r hr)) ⊔
            shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
              (P (cPrevIdx r hr)) (Q (cPrevIdx r hr)) ⊔ P (cLastIdx r hr))) : Subgroup H)) ∧
      ⁅R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c, x⁆ ∈
        ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
            (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ⊔
          (shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
              (Q (cLastIdx r hr)) (P (cLastIdx r hr)) ⊔
            shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
              (P (cLastIdx r hr)) (Q (cLastIdx r hr)) ⊔ P (cPrevIdx r hr))) ∧
      Commuting
        ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ))
        (shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
          (Q (cLastIdx r hr)) (P (cLastIdx r hr))) := by
  obtain ⟨hyY, huY⟩ := mem_crossShortRootGroup_prev_last hr hR c
  obtain ⟨hxhatBP, hxhatN⟩ := mem_heisRootGroup_conj_mul hFn hr hm h hML hq hF hns hcard hR
    hθr hθo hθc hθmem hW hDx
  exact ⟨hyY, huY, hxhatBP, hxhatN, commutator_mem_pointGroup hFn hr hm h hML hq hF hns
    hcard hR hθr hθo hθc hθmem hx, commuting_heisRootGroup_crossShortRootGroup hFn hr hm h
    hML hq hF hns hcard hR hθr hθo hθc hθmem⟩

private lemma exists_eq_mul_of_mem_shortRootGroup {G : Type*} [Group G]
    {W ws x y u xhat : G} {BP UL UP Y Y' : Subgroup G} {K : Type*} {z : K → G}
    (hws : ws = y * u * y)
    (hxhat : xhat = W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹)
    (hxhatBP : xhat ∈ BP) (hBPUP : BP ≤ UP)
    (hxhatN : xhat ∈ Subgroup.normalizer (UL : Set G))
    (hxUL : x ∈ UL) (huUL : u ∈ UL) (hyY : y ∈ Y)
    (hBY : Commuting BP Y) (hcommUP : ⁅y, x⁆ ∈ UP)
    (hmeet : UP ⊓ UL ≤ Y') (hY : ∀ a, a ∈ Y' ↔ ∃ w, z w = a) :
    ∃ w, ⁅y, x⁆ = W * ((W⁻¹ * ws) * x * (W⁻¹ * ws)⁻¹) * W⁻¹ * z w := by
  have hyB : Commute y xhat := (hBY xhat hxhatBP y hyY).symm
  have hxhatUP : xhat ∈ UP := hBPUP hxhatBP
  let a : G := xhat⁻¹ * ⁅y, x⁆
  have haUP : a ∈ UP := by
    show xhat⁻¹ * ⁅y, x⁆ ∈ UP
    exact UP.mul_mem (UP.inv_mem hxhatUP) hcommUP
  have hxuinv : xhat⁻¹ * u⁻¹ * xhat ∈ UL := by
    have hxhatinv : xhat⁻¹ ∈ Subgroup.normalizer (UL : Set G) :=
      (Subgroup.normalizer (UL : Set G)).inv_mem hxhatN
    simpa using (Subgroup.mem_normalizer_iff.1 hxhatinv u⁻¹).1 (UL.inv_mem huUL)
  have hxhat_form : xhat = y * u * y * x * (y * u * y)⁻¹ := by
    rw [hxhat, hws]
    group
  have hconj : y * x * y⁻¹ = u⁻¹ * xhat * u := eq_conj_of_commute_mul hxhat_form hyB
  have ha_eq : a = xhat⁻¹ * u⁻¹ * xhat * u * x⁻¹ := by
    show xhat⁻¹ * ⁅y, x⁆ = xhat⁻¹ * u⁻¹ * xhat * u * x⁻¹
    rw [commutatorElement_def, hconj]
    group
  have haUL : a ∈ UL := by
    rw [ha_eq]
    exact UL.mul_mem (UL.mul_mem hxuinv huUL) (UL.inv_mem hxUL)
  have haY : a ∈ Y' := hmeet ⟨haUP, haUL⟩
  obtain ⟨w, hw⟩ := (hY a).1 haY
  refine ⟨w, ?_⟩
  have hmain : ⁅y, x⁆ = xhat * a := by
    show ⁅y, x⁆ = xhat * (xhat⁻¹ * ⁅y, x⁆)
    group
  rw [hmain, hw, hxhat]

theorem IsMaxFrame.commutatorElement_ξ_eq_mul
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q (cLastIdx r hr))
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    (hmeet :
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
            (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) ⊔
          (shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
              (Q (cLastIdx r hr)) (P (cLastIdx r hr)) ⊔
            shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
              (P (cLastIdx r hr)) (Q (cLastIdx r hr)) ⊔ P (cPrevIdx r hr))) ⊓
        ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
          (shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
              (Q (cPrevIdx r hr)) (P (cPrevIdx r hr)) ⊔
            shortRootGroup Δ (P (cLastIdx r hr)) (Q (cLastIdx r hr))
              (P (cPrevIdx r hr)) (Q (cPrevIdx r hr)) ⊔ P (cLastIdx r hr))) ≤
      shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
        (P (cLastIdx r hr)) (Q (cLastIdx r hr)))
    {c : F} {x : H} (hx : x ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hDx :
      ((R.toHom hFn (even_two_mul r) hm
            (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (cPrevIdx r hr)))⁻¹ *
          (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
            R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
            R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) * x *
        ((R.toHom hFn (even_two_mul r) hm
            (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (cPrevIdx r hr)))⁻¹ *
          (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
            R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
            R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c))⁻¹ ∈
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) :
    ∃ w : F, ⁅R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c, x⁆ =
      R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)) *
        (((R.toHom hFn (even_two_mul r) hm
              (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
                (cPrevIdx r hr)))⁻¹ *
            (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
              R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
              R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) * x *
          ((R.toHom hFn (even_two_mul r) hm
              (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
                (cPrevIdx r hr)))⁻¹ *
            (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
              R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
              R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c))⁻¹) *
        (R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) w := by
  have hik : cPrevIdx r hr ≠ cLastIdx r hr := cPrevIdx_ne_cLastIdx hr
  obtain ⟨hyY, huY, hxhatBP, hxhatN, hcommUP, hcommBP⟩ :=
    weylDecompositionData hFn hr hm h hML hq hF hns hcard hR hθr hθo hθc hθmem rfl hx hDx
  have hY : ∀ a, a ∈ shortRootGroup Δ (P (cPrevIdx r hr)) (Q (cPrevIdx r hr))
      (P (cLastIdx r hr)) (Q (cLastIdx r hr)) ↔
      ∃ w, R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) w = a := by
    intro a
    simpa using (hR.short (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
      (by simpa using hik) a)
  exact exists_eq_mul_of_mem_shortRootGroup rfl rfl hxhatBP le_sup_left hxhatN
    (Subgroup.mem_sup_left hx)
    (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_sup_left huY)))
    hyY hcommBP hcommUP hmeet hY

end CFSG.Timmesfeld.Transvection
