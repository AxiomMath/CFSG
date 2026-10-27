module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar

import CFSG.LargeExtraspecial.AS35QCoLin
import CFSG.LargeExtraspecial.OrthoF2NormalizerThree
import CFSG.LargeExtraspecial.OrthoF2PairsCases
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

noncomputable abbrev rhoGL (S : Setting z E F) :
    Hbar z →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) :=
  (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup (qS S))).comp (rhoBar S)

@[simp] theorem rhoGL_apply (S : Setting z E F) (x : Hbar z) :
    rhoGL S x = rhoLin S x := rfl

theorem rhoGL_injective (S : Setting z E F) : Function.Injective (rhoGL S) := by
  intro x y hxy
  exact rhoBar_injective S (Subtype.ext hxy)

theorem rhoLin_pow_three_eq_one (S : Setting z E F) {x : Hbar z} (hx : orderOf x = 3) :
    (rhoLin S x) ^ 3 = 1 := by
  rw [show (3 : ℕ) = orderOf (rhoLin S x) by rw [orderOf_rhoLin, hx]]
  exact pow_orderOf_eq_one _

theorem rhoLin_conj_eq_or_eq_inv (S : Setting z E F) {ω ℓ : Hbar z}
    (hrel : ℓ * ω * ℓ⁻¹ = ω ∨ ℓ * ω * ℓ⁻¹ = ω⁻¹) :
    rhoLin S ℓ * rhoLin S ω * (rhoLin S ℓ)⁻¹ = rhoLin S ω ∨
      rhoLin S ℓ * rhoLin S ω * (rhoLin S ℓ)⁻¹ = (rhoLin S ω)⁻¹ := by
  rcases hrel with hrel | hrel
  · left
    calc rhoLin S ℓ * rhoLin S ω * (rhoLin S ℓ)⁻¹
        = rhoLin S (ℓ * ω * ℓ⁻¹) := (rhoLin_conj S ℓ ω).symm
      _ = rhoLin S ω := by rw [hrel]
  · right
    calc rhoLin S ℓ * rhoLin S ω * (rhoLin S ℓ)⁻¹
        = rhoLin S (ℓ * ω * ℓ⁻¹) := (rhoLin_conj S ℓ ω).symm
      _ = rhoLin S ω⁻¹ := by rw [hrel]
      _ = (rhoLin S ω)⁻¹ := rhoLin_inv S ω

theorem rhoLin_apply_eq_of_mem_fixSpace_of_normalizes (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {ω : Hbar z} (hω3 : orderOf ω = 3)
    (haω : aVec S h.mem_Q ∈ commSpace (rhoLin S ω))
    (hnorm : ∀ ℓ ∈ Lbar S a, ℓ * ω * ℓ⁻¹ = ω ∨ ℓ * ω * ℓ⁻¹ = ω⁻¹)
    {ℓ : Hbar z} (hℓ : ℓ ∈ Lbar S a) {v : Additive (QbarOf S)}
    (hv : v ∈ fixSpace (rhoLin S ω)) : rhoLin S ℓ v = v := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hωq : ∀ u, qS S (rhoLin S ω u) = qS S u :=
    fun u => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S ω).2 u
  have hUa : ∀ u ∈ fixSpace (rhoLin S ω),
      QuadraticMap.polar (qS S) u (aVec S h.mem_Q) = 0 := by
    intro u hu
    have horth := CFSG.LargeExtraspecial.AS35QCo.fixSpace_eq_orthogonal
      (q := qS S) (V := Additive (QbarOf S)) (hq := by letI := modAbF S; exact q_nondegenerate S)
      (g := rhoLin S ω) hωq
    have hu' := horth ▸ hu
    have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hu') (aVec S h.mem_Q) haω
    rwa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] at h0
  have haU : aVec S h.mem_Q ∉ fixSpace (rhoLin S ω) := by
    have hbot : commSpace (rhoLin S ω) ⊓ fixSpace (rhoLin S ω) = ⊥ :=
      CFSG.LargeExtraspecial.OrthoF2.commSpace_inf_fixSpace_eq_bot_of_pow_three
        (rhoLin_pow_three_eq_one S hω3)
    intro hmem
    have hmem' : aVec S h.mem_Q ∈ commSpace (rhoLin S ω) ⊓ fixSpace (rhoLin S ω) :=
      Submodule.mem_inf.mpr ⟨haω, hmem⟩
    rw [hbot, Submodule.mem_bot] at hmem'
    have hne : aVec S h.mem_Q ≠ 0 := by
      simpa [aVec] using aV_ne_zero S h.mem_Q h.not_mem_ZQ
    exact hne hmem'
  have hinv : ∀ ℓ ∈ Lbar S a, ∀ u ∈ fixSpace (rhoLin S ω),
      rhoLin S ℓ u ∈ fixSpace (rhoLin S ω) := by
    intro ℓ hℓ u hu
    have hconj := rhoLin_conj_eq_or_eq_inv S (hnorm ℓ hℓ)
    have hmaps : (fixSpace (rhoLin S ω)).map
        (rhoLin S ℓ : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S)) =
        fixSpace (rhoLin S ω) := by
      rw [← CFSG.LargeExtraspecial.AS35QCo.fixSpace_conj]
      rcases hconj with hconj | hconj
      · rw [hconj]
      · rw [hconj, CFSG.LargeExtraspecial.AS35QCo.fixSpace_inv]
    have hmem : rhoLin S ℓ u ∈ (fixSpace (rhoLin S ω)).map
        (rhoLin S ℓ : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S)) :=
      Submodule.mem_map_of_mem hu
    rwa [hmaps] at hmem
  have hres := rhoBar_apply_eq_of_invariant S h.mem_Q h.isConj h.mem_Qa hUa haU hinv ℓ hℓ v hv
  simpa [rhoLin] using hres

theorem card_Lbar_le_four_of_normalizes (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {ω : Hbar z} (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace (rhoLin S ω)) = 4)
    (haω : aVec S h.mem_Q ∈ commSpace (rhoLin S ω))
    (hnorm : ∀ ℓ ∈ Lbar S a, ℓ * ω * ℓ⁻¹ = ω ∨ ℓ * ω * ℓ⁻¹ = ω⁻¹) :
    Nat.card (Lbar S a) ≤ 4 := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hφinj : Function.Injective (rhoGL S) := rhoGL_injective S
  have hω3' : orderOf (rhoLin S ω) = 3 := by rw [orderOf_rhoLin, hω3]
  have hωq : ∀ v, qS S (rhoLin S ω v) = qS S v :=
    fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S ω).2 v
  have hPq : ∀ p ∈ (Lbar S a).map (rhoGL S), ∀ v, qS S (p v) = qS S v := by
    intro p hp v
    obtain ⟨ℓ, -, rfl⟩ := Subgroup.mem_map.mp hp
    simpa [rhoGL_apply] using
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S ℓ).2 v
  have hnormP : ∀ p ∈ (Lbar S a).map (rhoGL S),
      p * rhoLin S ω * p⁻¹ = rhoLin S ω ∨
        p * rhoLin S ω * p⁻¹ = (rhoLin S ω)⁻¹ := by
    intro p hp
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hp
    simpa [rhoGL_apply] using rhoLin_conj_eq_or_eq_inv S (hnorm ℓ hℓ)
  have htriv : ∀ p ∈ (Lbar S a).map (rhoGL S), ∀ v ∈ fixSpace (rhoLin S ω), p v = v := by
    intro p hp v hv
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hp
    simpa [rhoGL_apply] using
      rhoLin_apply_eq_of_mem_fixSpace_of_normalizes S h hω3 haω hnorm hℓ hv
  have hfix : ∀ p ∈ (Lbar S a).map (rhoGL S), p (aVec S h.mem_Q) = aVec S h.mem_Q := by
    intro p hp
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hp
    simpa [rhoGL_apply] using rhoBar_apply_aVec_of_mem_Lbar S h.mem_Q h.isConj hℓ
  have hmain : Nat.card ((Lbar S a).map (rhoGL S)) ≤ 4 :=
    CFSG.LargeExtraspecial.card_le_four_of_normalizes_of_apply_eq
      (V := Additive (QbarOf S)) (q := qS S) (hq := by letI := modAbF S; exact q_nondegenerate S)
      (ω := rhoLin S ω) (P := (Lbar S a).map (rhoGL S)) (c := aVec S h.mem_Q)
      hωq hω3' h4 hPq hnormP htriv haω
      (by simpa [aVec] using aV_ne_zero S h.mem_Q h.not_mem_ZQ)
      (by simpa [aVec] using qS_aVec_eq_zero S h.mem_Q h.isConj) hfix
  rwa [Subgroup.card_map_of_injective (f := rhoGL S) hφinj] at hmain

theorem exists_mem_Lbar_conj_ne (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {ω : Hbar z} (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace (rhoLin S ω)) = 4)
    (haω : aVec S h.mem_Q ∈ commSpace (rhoLin S ω)) :
    ∃ ℓ ∈ Lbar S a, ℓ * ω * ℓ⁻¹ ≠ ω ∧ ℓ * ω * ℓ⁻¹ ≠ ω⁻¹ := by
  by_contra hc
  push Not at hc
  have hnorm : ∀ ℓ ∈ Lbar S a, ℓ * ω * ℓ⁻¹ = ω ∨ ℓ * ω * ℓ⁻¹ = ω⁻¹ := by
    intro ℓ hℓ
    rcases eq_or_ne (ℓ * ω * ℓ⁻¹) ω with h | h
    · exact Or.inl h
    · exact Or.inr (hc ℓ hℓ h)
  exact (not_le_of_gt h.four_lt_card_Lbar)
    (card_Lbar_le_four_of_normalizes S h hω3 h4 haω hnorm)

theorem exists_mem_Lbar_conj_ne_of_mem_Rbar (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {r e : Hbar z} (hr : r ∈ Rbar S a) (hr1 : r ≠ 1)
    (he : e ∈ Eset S a) (h3 : orderOf (r * e) = 3) :
    ∃ ℓ ∈ Lbar S a, ℓ * (r * e) * ℓ⁻¹ ≠ r * e ∧ ℓ * (r * e) * ℓ⁻¹ ≠ (r * e)⁻¹ := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hrA2 : r ∈ A2set S :=
    Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hr hr1)
  have heA2 : e ∈ A2set S := Eset_subset_A2set S a he
  have htypeR : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S r) 2 :=
    isTypeA_rhoBar_of_isA2Hbar S hrA2
  have htypeE : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S e) 2 :=
    isTypeA_rhoBar_of_isA2Hbar S heA2
  have h3lin : orderOf (rhoLin S r * rhoLin S e) = 3 := by
    rw [← rhoLin_mul, orderOf_rhoLin, h3]
  have hmul := CFSG.LargeExtraspecial.commSpace_mul_of_orderOf_eq_three
    (q := qS S) (hq := by letI := modAbF S; exact q_nondegenerate S) htypeR htypeE h3lin
  have h4 : finrank (ZMod 2) (commSpace (rhoLin S (r * e))) = 4 := by
    rw [rhoLin_mul]
    exact hmul.2.2.1
  have haR : aVec S h.mem_Q ∈ commSpace (rhoLin S r) :=
    aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj
      h.not_mem_ZQ h.mem_Qa h.centerIn_Qa_not_le_Q hr hr1
  have haω : aVec S h.mem_Q ∈ commSpace (rhoLin S (r * e)) := by
    rw [rhoLin_mul, hmul.2.1]
    exact Submodule.mem_sup_left haR
  exact exists_mem_Lbar_conj_ne S h h3 h4 haω

end CFSG.RankThree.GF2n.Stroth78
