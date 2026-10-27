module

public import CFSG.RankThree.GF2n.Stroth78.Sec3SevenFix
public import CFSG.LargeExtraspecial.OrthoF2Fixed

import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
public import CFSG.RankThree.GF2n.Stroth78.Sec3LbarBound

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem rhoLin_apply_eq_of_mem_fixSpaceOf (S : Setting z E F) {a : G}
    {v : Additive (QbarOf S)}
    (hv : v ∈ CFSG.LargeExtraspecial.fixSpaceOf ((Lbar S a).map (rhoGL S)))
    {ℓ : Hbar z} (hℓ : ℓ ∈ Lbar S a) : rhoLin S ℓ v = v := by
  have hmemA : rhoGL S ℓ ∈ (Lbar S a).map (rhoGL S) :=
    Subgroup.mem_map.mpr ⟨ℓ, hℓ, rfl⟩
  have h := (CFSG.LargeExtraspecial.mem_fixSpaceOf.mp hv) (rhoGL S ℓ) hmemA
  simpa [rhoGL_apply] using h

theorem Sec3Hyp.aVec_mem_fixSpaceOf {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) :
    aVec S h.mem_Q ∈
      CFSG.LargeExtraspecial.fixSpaceOf ((Lbar S a).map (rhoGL S)) := by
  rw [CFSG.LargeExtraspecial.mem_fixSpaceOf]
  intro f hf
  obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hf
  rw [rhoGL_apply]
  exact rhoBar_apply_aVec_of_mem_Lbar S h.mem_Q h.isConj hℓ

theorem ofMul_mkQbar_mul_of_mem_ZQ (S : Setting z E F) (r : ↥(Q z)) {e : G}
    (heQ : e ∈ Q z) (heZ : e ∈ ZQ z) :
    Additive.ofMul (mkQbar S (r * ⟨e, heQ⟩)) = Additive.ofMul (mkQbar S r) := by
  have heclass : Additive.ofMul (mkQbar S ⟨e, heQ⟩) = 0 :=
    aV_eq_zero_of_mem_ZQ S heQ heZ
  have hmul : (mkQbar S (r * ⟨e, heQ⟩) : QbarOf S) =
      mkQbar S r * mkQbar S ⟨e, heQ⟩ := map_mul (mkQbar S) r ⟨e, heQ⟩
  calc
    Additive.ofMul (mkQbar S (r * ⟨e, heQ⟩))
        = Additive.ofMul (mkQbar S r) + Additive.ofMul (mkQbar S ⟨e, heQ⟩) := by
          rw [hmul, ofMul_mul]
    _ = Additive.ofMul (mkQbar S r) := by rw [heclass, add_zero]

theorem Sec3Hyp.exists_preimage_of_fix {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {v : Additive (QbarOf S)}
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ v = v) (hq : qS S v = 0)
    (hspan : v ∉ (ZMod 2) ∙ aVec S h.mem_Q) :
    ∃ r : ↥(Q z), v = Additive.ofMul (mkQbar S r) ∧
      (∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
        Additive.ofMul (mkQbar S r)) ∧
      qS S (Additive.ofMul (mkQbar S r)) = 0 ∧
      Additive.ofMul (mkQbar S r) ∉ (ZMod 2) ∙ aVec S h.mem_Q := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)) (Additive.toMul v)
  have hvr : v = Additive.ofMul (mkQbar S r) := by
    have h := congrArg Additive.ofMul hr.symm
    simpa [mkQbar] using h
  refine ⟨r, hvr, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    simpa [hvr] using hfix ℓ hℓ
  · simpa [hvr] using hq
  · intro hm
    exact hspan (hvr ▸ hm)

theorem Sec3Hyp.exists_mem_Tset_of_fix {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (r : ↥(Q z))
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r))
    (hq : qS S (Additive.ofMul (mkQbar S r)) = 0)
    (hspan : Additive.ofMul (mkQbar S r) ∉ (ZMod 2) ∙ aVec S h.mem_Q) :
    ∃ (g : G) (t : ↥(H z)),
      g ∈ QaOf (a * z) ∧ g * a * g⁻¹ = z ∧
      (t : G) = g * (r : G) * g⁻¹ ∧
      (QuotientGroup.mk t : Hbar z) ∈ Tset S a := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  obtain ⟨g, hgQaz, hga⟩ :=
    exists_conj_eq_z_of_mem_QaOf_mul_z S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
  have hgz : g * z * g⁻¹ = a :=
    conj_z_eq_of_conj_a_eq S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga
  have hB : QuadraticMap.polar (qS S) (Additive.ofMul (mkQbar S r))
      (aVec S h.mem_Q) = 0 :=
    Sec3Hyp.polar_aVec_eq_zero_of_fix h hfix
  have hrCa : (r : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    have hcomm : (r : G) * a = a * (r : G) :=
      (polar_q_eq_zero_iff S r ⟨a, h.mem_Q⟩).mp hB
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hcomm.symm
  have htL0 : g * (r : G) * g⁻¹ ∈ L0 S a := by
    have hmem : g * (r : G) * g⁻¹ ∈ (Q z ⊓ Subgroup.centralizer ({a} : Set G)).map
        (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨(r : G), Subgroup.mem_inf.mpr ⟨r.2, hrCa⟩,
        by simp [MulAut.conj_apply]⟩
    rwa [map_conj_CQ_eq_L0 S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga] at hmem
  have htmem : g * (r : G) * g⁻¹ ∈ H z := (Subgroup.mem_inf.mp htL0).2
  let t : ↥(H z) := ⟨g * (r : G) * g⁻¹, htmem⟩
  have ht : (t : G) = g * (r : G) * g⁻¹ := rfl
  have hβT : (QuotientGroup.mk t : Hbar z) ∈ Tset S a :=
    Sec3Hyp.mem_Tset_of_fix h hgQaz hga r hfix t ht hq hspan
  exact ⟨g, t, hgQaz, hga, ht, hβT⟩

theorem Sec3Hyp.exists_smul_preimage_of_fix {S : Setting z E F} {a g : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hgQaz : g ∈ QaOf (a * z)) (hga : g * a * g⁻¹ = z)
    (r : ↥(Q z))
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r))
    (t : ↥(H z)) (ht : (t : G) = g * (r : G) * g⁻¹)
    (hq : qS S (Additive.ofMul (mkQbar S r)) = 0)
    (hspan : Additive.ofMul (mkQbar S r) ∉ (ZMod 2) ∙ aVec S h.mem_Q) :
    ∃ (s : ↥(H z)) (r' : ↥(Q z)) (t' : ↥(H z)),
      (QuotientGroup.mk s : Hbar z) ∈ Tset S a ∧
      Additive.ofMul (mkQbar S r') = Additive.ofMul (mkQbar S r) ∧
      (t' : G) = g * (r' : G) * g⁻¹ ∧
      (QuotientGroup.mk t' : Hbar z) = (QuotientGroup.mk t) * (QuotientGroup.mk s) := by
  have hgz : g * z * g⁻¹ = a :=
    conj_z_eq_of_conj_a_eq S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga
  obtain ⟨α, hα1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hαR : (α : Hbar z) ∈ Rbar S a := α.2
  have hα1' : (α : Hbar z) ≠ 1 := fun h1 => hα1 (Subtype.ext h1)
  have hαT : (α : Hbar z) ∈ Tset S a := h.mem_Tset_of_mem_Rbar hαR hα1'
  obtain ⟨s, hsZ, -, -, hsα⟩ :=
    exists_mem_centerIn_inf_H_of_mem_Rbar S hαR hα1'
  have hsmap : (s : G) ∈ (ZQ z).map (MulAut.conj g).toMonoidHom := by
    have h := hsZ
    rwa [centerIn_QaOf_eq_map_conj S hgz] at h
  obtain ⟨e, heZQ, heconj⟩ := Subgroup.mem_map.mp hsmap
  have heQ : e ∈ Q z := (Subgroup.mem_inf.mp heZQ).1
  let r' : ↥(Q z) := r * ⟨e, heQ⟩
  have hr'class : Additive.ofMul (mkQbar S r') = Additive.ofMul (mkQbar S r) :=
    ofMul_mkQbar_mul_of_mem_ZQ S r heQ heZQ
  let t' : ↥(H z) := t * s
  have heconj' : g * e * g⁻¹ = (s : G) := by
    simpa [MulAut.conj_apply] using heconj
  have ht' : (t' : G) = g * (r' : G) * g⁻¹ := by
    change (t : G) * (s : G) = g * (r' : G) * g⁻¹
    rw [ht, ← heconj']
    change (g * (r : G) * g⁻¹) * (g * e * g⁻¹) = g * ((r : G) * e) * g⁻¹
    group
  have hmul : (QuotientGroup.mk t' : Hbar z) =
      (QuotientGroup.mk t) * (QuotientGroup.mk s) := by
    rw [show t' = t * s from rfl, QuotientGroup.mk_mul]
  have hαT' : (QuotientGroup.mk s : Hbar z) ∈ Tset S a := by
    simpa [hsα] using hαT
  exact ⟨s, r', t', hαT', hr'class, ht', hmul⟩

theorem Sec3Hyp.eq_zero_or_eq_aVec_of_fix {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hT : ∀ α ∈ Tset S a, ∀ β ∈ Tset S a, α * β ∉ Tset S a)
    {v : Additive (QbarOf S)} (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ v = v)
    (hq : qS S v = 0) : v = 0 ∨ v = aVec S h.mem_Q := by
  by_cases hv0 : v = 0
  · exact Or.inl hv0
  by_cases hva : v = aVec S h.mem_Q
  · exact Or.inr hva
  have hspan : v ∉ (ZMod 2) ∙ aVec S h.mem_Q := by
    intro hm
    rcases CFSG.LargeExtraspecial.OrthoF2.mem_span_singleton_iff.mp hm with h0 | ha
    · exact hv0 h0
    · exact hva ha
  obtain ⟨r, -, hfixr, hqr, hspanr⟩ :=
    Sec3Hyp.exists_preimage_of_fix h hfix hq hspan
  obtain ⟨g, t, hgQaz, hga, ht, hβT⟩ :=
    Sec3Hyp.exists_mem_Tset_of_fix h r hfixr hqr hspanr
  obtain ⟨s, r', t', hαT, hr'class, ht', hmul⟩ :=
    Sec3Hyp.exists_smul_preimage_of_fix h hgQaz hga r hfixr t ht hqr hspanr
  have hfixr' : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r')) =
      Additive.ofMul (mkQbar S r') := by
    intro ℓ hℓ
    rw [hr'class]
    exact hfixr ℓ hℓ
  have hqr' : qS S (Additive.ofMul (mkQbar S r')) = 0 := by
    rw [hr'class]
    exact hqr
  have hspanr' : Additive.ofMul (mkQbar S r') ∉ (ZMod 2) ∙ aVec S h.mem_Q := by
    intro hm
    apply hspanr
    rwa [hr'class] at hm
  have hβ'T : (QuotientGroup.mk t' : Hbar z) ∈ Tset S a :=
    Sec3Hyp.mem_Tset_of_fix h hgQaz hga r' hfixr' t' ht' hqr' hspanr'
  rw [hmul] at hβ'T
  exact absurd hβ'T ((hT (QuotientGroup.mk t) hβT (QuotientGroup.mk s) hαT))

theorem Sec3Hyp.not_forall_Lbar_fix_commSpace {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hT : ∀ α ∈ Tset S a, ∀ β ∈ Tset S a, α * β ∉ Tset S a)
    {α : Hbar z} (hα : IsA2Hbar S α) :
    ¬ ∀ ℓ ∈ Lbar S a, ∀ v ∈ commSpace (rhoLin S α), rhoLin S ℓ v = v := by
  intro hall
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  have htype : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S α) 2 := by
    simpa [rhoLin] using isTypeA_rhoBar_of_isA2Hbar S hα
  have hle : commSpace (rhoLin S α) ≤ (ZMod 2) ∙ aVec S h.mem_Q := by
    intro v hv
    have hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ v = v := fun ℓ hℓ => hall ℓ hℓ v hv
    have hq : qS S v = 0 := htype.2.2.2.2 v hv
    exact CFSG.LargeExtraspecial.OrthoF2.mem_span_singleton_iff.mpr
      (Sec3Hyp.eq_zero_or_eq_aVec_of_fix h hT hfix hq)
  have hdim2 : finrank (ZMod 2) (commSpace (rhoLin S α)) = 2 := htype.2.2.2.1
  have hdim1 : finrank (ZMod 2) ((ZMod 2) ∙ aVec S h.mem_Q) = 1 :=
    finrank_span_singleton (aV_ne_zero S h.mem_Q h.not_mem_ZQ)
  have hle1 : finrank (ZMod 2) (commSpace (rhoLin S α)) ≤ 1 := by
    calc
      finrank (ZMod 2) (commSpace (rhoLin S α)) ≤
          finrank (ZMod 2) ((ZMod 2) ∙ aVec S h.mem_Q) := Submodule.finrank_mono hle
      _ = 1 := hdim1
  omega

end CFSG.RankThree.GF2n.Stroth78
