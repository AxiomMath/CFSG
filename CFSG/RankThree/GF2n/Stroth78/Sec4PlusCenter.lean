module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs
public import CFSG.RankThree.GF2n.Stroth78.Sec3Two

import CFSG.RankThree.GF2n.Stroth78.Sec3One
import CFSG.LargeExtraspecial.OrthoF2PairsCases
import CFSG.LargeExtraspecial.S12Five
import CFSG.LargeExtraspecial.AS35QCoLin
import CFSG.LinearAlgebra.F2PlaneMaps

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

section Linear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem apply_eq_self_of_commute_of_orderOf_mul_eq_four
    (hq : q.polarBilin.Nondegenerate) {α β c : V ≃ₗ[ZMod 2] V}
    (hα : CFSG.LargeExtraspecial.IsTypeA q α 2) (hβ : CFSG.LargeExtraspecial.IsTypeA q β 2)
    (h4 : orderOf (α * β) = 4) (hcα : c * α = α * c) (hcβ : c * β = β * c)
    (hodd : Odd (orderOf c)) : ∀ w ∈ commSpace α, c w = w := by
  have hstab : ∀ w ∈ commSpace α, c w ∈ commSpace α := by
    intro w hw
    obtain ⟨v, hv⟩ := mem_commSpace.mp hw
    refine mem_commSpace.mpr ⟨c v, ?_⟩
    have h1 : c (α v) = α (c v) := by
      have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hcα
      simpa using this
    rw [← h1, ← map_sub, hv]
  obtain ⟨-, hne, a, ha, b, hb, hab⟩ :=
    (CFSG.LargeExtraspecial.orderOf_mul_eq_four_iff_of_isTypeA hq hα hβ).mp h4
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨huA, huB⟩ := Submodule.mem_inf.mp hu
  have hβO := CFSG.LargeExtraspecial.OrthoF2.mem_orthogonalGroup_of_isTypeA hβ
  have hβu : β u = u :=
    (CFSG.LargeExtraspecial.OrthoF2.mem_orthogonal_commSpace_iff hq hβO).mp huB
  have hcu : c u = u := by
    by_contra hcu
    have hβcu : β (c u) = c u := by
      have h1 : c (β u) = β (c u) := by
        have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f u) hcβ
        simpa using this
      rw [← h1, hβu]
    have hcu0 : c u ≠ 0 := fun h => hu0 (c.injective (by rw [h, map_zero]))
    have hfix : ∀ w ∈ commSpace α, β w = w :=
      CFSG.LargeExtraspecial.s12_fix_of_fix_pair hα.2.2.2.1 huA (hstab u huA) hu0 hcu0
        (Ne.symm hcu) hβu hβcu
    apply hab
    have hmem : a ∈ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) :=
      (CFSG.LargeExtraspecial.OrthoF2.mem_orthogonal_commSpace_iff hq hβO).mpr (hfix a ha)
    exact (CFSG.LargeExtraspecial.OrthoF2.mem_orthogonal_iff_polar.mp hmem) b hb
  exact CFSG.LinearAlgebra.apply_eq_self_of_odd_of_apply_eq hα.2.2.2.1 hstab hodd huA hu0 hcu

end Linear

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem rhoLin_mul_self_eq_one_of_forall_commSpace (S : Setting z E F) {D : Set (Hbar z)}
    {ζ : Hbar z} (hζ : ζ ∈ Subgroup.closure D) (hcomm : ∀ d ∈ D, d * ζ = ζ * d)
    (hfix : ∀ d ∈ D, ∀ w ∈ commSpace (rhoLin S d), rhoLin S ζ w = w) :
    rhoLin S ζ * rhoLin S ζ = 1 := by
  let c := rhoLin S ζ
  let K : Subgroup (Hbar z) :=
    { carrier := {g | ∀ u : Additive (QbarOf S), rhoLin S g (c u - u) = c u - u}
      mul_mem' := by
        intro g h hg hh u
        rw [rhoLin_mul, LinearEquiv.mul_apply, hh u, hg u]
      one_mem' := by
        intro u
        simp [rhoLin]
      inv_mem' := by
        intro g hg u
        calc rhoLin S g⁻¹ (c u - u) = rhoLin S g⁻¹ (rhoLin S g (c u - u)) := by rw [hg u]
          _ = c u - u := by
            rw [← LinearEquiv.mul_apply, ← rhoLin_mul, inv_mul_cancel]
            simp [rhoLin] }
  have hD : D ⊆ K := by
    intro d hd u
    have hdc : rhoLin S d (c u) = c (rhoLin S d u) := by
      have := congrArg (fun g => rhoLin S g u) (hcomm d hd)
      simpa [rhoLin_mul, LinearEquiv.mul_apply] using this
    have h2 : c (rhoLin S d u - u) = rhoLin S d u - u := hfix d hd _ (sub_mem_commSpace _ _)
    have h1 : rhoLin S d (c u - u) - (c u - u) = c (rhoLin S d u - u) - (rhoLin S d u - u) := by
      simp only [map_sub, hdc]
      abel
    rw [h2, sub_self] at h1
    exact sub_eq_zero.mp h1
  have hζK : ζ ∈ K := (Subgroup.closure_le K).mpr hD hζ
  refine LinearEquiv.ext fun u => ?_
  have h : c (c u - u) = c u - u := hζK u
  rw [map_sub] at h
  show c (c u) = u
  have h2 : c (c u) = (c u - u) + c u := sub_eq_iff_eq_add.mp h
  rw [h2, sub_eq_add_neg, CFSG.LargeExtraspecial.OrthoF2.vec_neg u, add_assoc, add_comm u (c u),
    ← add_assoc, CFSG.LargeExtraspecial.OrthoF2.vec_add_self, zero_add]

theorem centerIn_Xsub_eq_bot_of_threeFourPlus (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) :
    centerIn (Xsub S a) = ⊥ := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hq : (qS S).polarBilin.Nondegenerate := by
    letI := modAbF S
    exact q_nondegenerate S
  obtain ⟨-, -, -, hclass⟩ := stroth78_31 S h h217
  rcases Subgroup.bot_or_exists_ne_one (centerIn (Xsub S a)) with hbot | ⟨ζ, hζ, hζ1⟩
  · exact hbot
  exfalso
  have hζX : ζ ∈ Xsub S a := hζ.1
  have hζc : ∀ x ∈ Xsub S a, x * ζ = ζ * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hζ.2 x hx
  have hcard := card_centerIn_Xsub S h h217
  have hodd : Odd (orderOf ζ) := by
    have hdvd0 : orderOf ζ ∣ Nat.card (centerIn (Xsub S a)) := by
      have := Subgroup.orderOf_dvd_natCard (centerIn (Xsub S a)) hζ
      simpa using this
    have hdvd3 : orderOf ζ ∣ 3 := by
      rcases hcard with h1 | h3
      · rw [h1] at hdvd0
        exact hdvd0.trans (one_dvd 3)
      · rw [h3] at hdvd0
        exact hdvd0
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hζ1
    · rw [h3]
      decide
  have hoddc : Odd (orderOf (rhoLin S ζ)) := by rw [orderOf_rhoLin]; exact hodd
  obtain ⟨α₀, hα₀, β₀, hβ₀, h4⟩ := h34
  have hα₀D : IsA2Hbar S α₀ := Eset_subset_A2set S a hα₀
  have hβ₀D : IsA2Hbar S β₀ := Eset_subset_A2set S a hβ₀
  have hAα : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S α₀) 2 :=
    isTypeA_rhoBar_of_isA2Hbar S hα₀D
  have hAβ : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S β₀) 2 :=
    isTypeA_rhoBar_of_isA2Hbar S hβ₀D
  have h4' : orderOf (rhoLin S α₀ * rhoLin S β₀) = 4 := by
    rw [← rhoLin_mul, orderOf_rhoLin]
    exact h4
  have hcomm : ∀ x ∈ Xsub S a, rhoLin S ζ * rhoLin S x = rhoLin S x * rhoLin S ζ := by
    intro x hx
    rw [← rhoLin_mul, ← rhoLin_mul, hζc x hx]
  have hall : ∀ w ∈ commSpace (rhoLin S α₀), rhoLin S ζ w = w :=
    apply_eq_self_of_commute_of_orderOf_mul_eq_four hq hAα hAβ h4'
      (hcomm α₀ (subset_Xsub S a hα₀)) (hcomm β₀ (subset_Xsub S a hβ₀)) hoddc
  have hallE : ∀ α' ∈ Eset S a, ∀ w ∈ commSpace (rhoLin S α'), rhoLin S ζ w = w := by
    intro α' hα' w hw
    obtain ⟨x, hx, rfl⟩ := (hclass α₀ hα₀ α').mp hα'
    rw [rhoLin_conj, CFSG.LargeExtraspecial.AS35QCo.commSpace_conj, Submodule.mem_map] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [LinearEquiv.coe_coe, ← LinearEquiv.mul_apply, hcomm x hx, LinearEquiv.mul_apply,
      hall y hy]
  have hsq : rhoLin S ζ * rhoLin S ζ = 1 :=
    rhoLin_mul_self_eq_one_of_forall_commSpace S (D := Eset S a) hζX
      (fun d hd => hζc d (subset_Xsub S a hd)) hallE
  have hord : orderOf (rhoLin S ζ) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have h1ord : orderOf (rhoLin S ζ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h2
    · exact h1
    · rw [h2] at hoddc
      exact absurd hoddc (by decide)
  rw [orderOf_rhoLin] at h1ord
  exact hζ1 (orderOf_eq_one_iff.mp h1ord)

theorem center_Xsub_eq_bot_of_threeFourPlus (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) :
    Subgroup.center ↥(Xsub S a) = ⊥ := by
  have hZ := centerIn_Xsub_eq_bot_of_threeFourPlus S h h217 h34
  rw [eq_bot_iff]
  intro ζ hζ
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hmem : (ζ : Hbar z) ∈ centerIn (Xsub S a) := by
    refine ⟨ζ.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hζ ⟨x, hx⟩)
  rw [hZ, Subgroup.mem_bot] at hmem
  simpa using hmem

end CFSG.RankThree.GF2n.Stroth78
