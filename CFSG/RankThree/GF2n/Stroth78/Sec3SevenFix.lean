module

public import CFSG.LargeExtraspecial.OrthoF2Radical

import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem rhoLin_mk_eq_conjQbar (S : Setting z E F) (t : ↥(H z)) :
    rhoLin S (QuotientGroup.mk t) = conjQbar S t := by
  rw [rhoLin]
  exact rhoBar_coe_eq_conjQbar S t

theorem mem_Lbar_of_mem_L0 (S : Setting z E F) {a : G} {ℓ : ↥(H z)}
    (hℓ : (ℓ : G) ∈ L0 S a) : (QuotientGroup.mk ℓ : Hbar z) ∈ Lbar S a := by
  rw [← map_L0_eq_Lbar S a]
  exact Subgroup.mem_map.mpr ⟨ℓ, Subgroup.mem_subgroupOf.mpr hℓ, rfl⟩

theorem Sec3Hyp.polar_aVec_eq_zero_of_fix {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {v : Additive (QbarOf S)}
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ v = v) :
    QuadraticMap.polar (qS S) v (aVec S h.mem_Q) = 0 := by
  obtain ⟨α, hα1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hαR : (α : Hbar z) ∈ Rbar S a := α.2
  have hα1' : (α : Hbar z) ≠ 1 := fun h => hα1 (Subtype.ext h)
  have hαL : (α : Hbar z) ∈ Lbar S a := Rbar_le_Lbar S a hαR
  have hfixα : rhoLin S (α : Hbar z) v = v := hfix α hαL
  have hfixa : rhoLin S (α : Hbar z) (aVec S h.mem_Q) = aVec S h.mem_Q :=
    rhoBar_apply_aVec_of_mem_Lbar S h.mem_Q h.isConj hαL
  have hmem := aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ
    h.mem_Qa h.centerIn_Qa_not_le_Q hαR hα1'
  rw [mem_commSpace] at hmem
  obtain ⟨w0, hw0⟩ := hmem
  have hO : rhoLin S (α : Hbar z) ∈ TauCeti.QuadraticMap.orthogonalGroup (qS S) :=
    (rhoBar S α).2
  have hstep : QuadraticMap.polar (qS S) v
      (rhoLin S (α : Hbar z) w0 - w0) = 0 := by
    rw [QuadraticMap.polar_sub_right,
      ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO v w0, hfixα, sub_self]
  rwa [hw0] at hstep

theorem commutator_mem_ZQ_of_fix (S : Setting z E F) (ℓ : ↥(H z)) (r : ↥(Q z))
    (hfix : rhoLin S (QuotientGroup.mk ℓ) (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r)) : ⁅(r : G), (ℓ : G)⁆ ∈ ZQ z := by
  have hclass := additive_commutator_eq_sub S ℓ.2 r.2
  have hρ : rhoLin S (QuotientGroup.mk ℓ) = conjQbar S ℓ :=
    rhoLin_mk_eq_conjQbar S ℓ
  have hzero : Additive.ofMul (mkQbar S
      ⟨⁅(r : G), (ℓ : G)⁆, commutator_mem_Q_of_mem_H ℓ.2 r.2⟩) = 0 := by
    rw [hclass]
    change conjQbar S ℓ (Additive.ofMul (mkQbar S r)) -
      Additive.ofMul (mkQbar S r) = 0
    rw [hρ] at hfix
    rw [hfix, sub_self]
  have h1 : (mkQbar S ⟨⁅(r : G), (ℓ : G)⁆, commutator_mem_Q_of_mem_H ℓ.2 r.2⟩ :
      QbarOf S) = 1 := by
    have := congrArg Additive.toMul hzero
    simpa using this
  rw [← MonoidHom.mem_ker] at h1
  rw [show (mkQbar S).ker = (ZQ z).subgroupOf (Q z) from QuotientGroup.ker_mk' _] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem Sec3Hyp.commutator_mem_ZQ_of_mem_L0 {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {r : ↥(Q z)}
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r))
    {ℓ : G} (hℓ : ℓ ∈ L0 S a) : ⁅ℓ, (r : G)⁆ ∈ ZQ z := by
  have hℓH : ℓ ∈ H z := (Subgroup.mem_inf.mp hℓ).2
  let ℓH : ↥(H z) := ⟨ℓ, hℓH⟩
  have hbar : (QuotientGroup.mk ℓH : Hbar z) ∈ Lbar S a :=
    mem_Lbar_of_mem_L0 S (ℓ := ℓH) (by simpa [ℓH] using hℓ)
  have hcomm : ⁅(r : G), ℓ⁆ ∈ ZQ z :=
    commutator_mem_ZQ_of_fix S ℓH r (hfix (QuotientGroup.mk ℓH) hbar)
  have h' : ⁅ℓ, (r : G)⁆ = ⁅(r : G), ℓ⁆⁻¹ := by rw [commutatorElement_inv]
  rw [h']
  exact (ZQ z).inv_mem hcomm

theorem rhoLin_mk_apply_of_conj_eq_mul (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (d : ↥(H z)) (r : ↥(Q z)) (hd : (d : G) * (r : G) * (d : G)⁻¹ = (r : G) * a) :
    rhoLin S (QuotientGroup.mk d) (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r) + aVec S haQ := by
  have hd' : conjAutQ S d r = ⟨(r : G) * a, (Q z).mul_mem r.2 haQ⟩ := by
    apply Subtype.ext
    rw [conjAutQ_apply]
    exact hd
  have hρ : rhoLin S (QuotientGroup.mk d) = conjQbar S d :=
    rhoLin_mk_eq_conjQbar S d
  have hprod : (mkQbar S ⟨(r : G) * a, (Q z).mul_mem r.2 haQ⟩ : QbarOf S) =
      mkQbar S r * mkQbar S ⟨a, haQ⟩ := by
    rw [← map_mul]
    congr 1
  calc
    rhoLin S (QuotientGroup.mk d) (Additive.ofMul (mkQbar S r))
        = conjQbar S d (Additive.ofMul (mkQbar S r)) := by rw [hρ]
    _ = Additive.ofMul (mkQbar S (conjAutQ S d r)) := by
          simpa only [mkQbar, QuotientGroup.mk'_apply] using conjQbar_apply_mk S d r
    _ = Additive.ofMul (mkQbar S ⟨(r : G) * a, (Q z).mul_mem r.2 haQ⟩) := by rw [hd']
    _ = Additive.ofMul (mkQbar S r) + aVec S haQ := by
          rw [hprod, ofMul_mul]

theorem commutator_conj_mem_sup_zpowers_ZQ (S : Setting z E F) {a g r x : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (hgQaz : g ∈ QaOf (a * z)) (hga : g * a * g⁻¹ = z)
    (hrCa : r ∈ Subgroup.centralizer ({a} : Set G))
    (hfix : ∀ ℓ ∈ L0 S a, ⁅ℓ, r⁆ ∈ ZQ z)
    (hx : x ∈ Q z ⊓ Subgroup.centralizer ({a} : Set G)) :
    ⁅x, g * r * g⁻¹⁆ ∈ Subgroup.zpowers a ⊔ ZQ z := by
  have hgz : g * z * g⁻¹ = a :=
    conj_z_eq_of_conj_a_eq S haQ hconj haZ hgQaz hga
  have hxmap : x ∈ (L0 S a).map (MulAut.conj g).toMonoidHom := by
    rw [show L0 S a = QaOf a ⊓ H z from rfl,
      map_conj_L0_eq_CQ S haQ hconj haZ hgQaz hga]
    exact hx
  obtain ⟨ℓ, hℓ, hℓx⟩ := Subgroup.mem_map.mp hxmap
  have hℓx' : g * ℓ * g⁻¹ = x := by simpa [MulAut.conj_apply] using hℓx
  have hℓQa : ℓ ∈ QaOf a := (Subgroup.mem_inf.mp hℓ).1
  have hinv : r * ℓ⁻¹ * r⁻¹ ∈ QaOf a :=
    fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hrCa ((QaOf a).inv_mem hℓQa)
  have hcommQa : ⁅ℓ, r⁆ ∈ QaOf a := by
    rw [commutatorElement_def, show ℓ * r * ℓ⁻¹ * r⁻¹ = ℓ * (r * ℓ⁻¹ * r⁻¹) by group]
    exact (QaOf a).mul_mem hℓQa hinv
  have hcommZ : ⁅ℓ, r⁆ ∈ ZQ z := hfix ℓ hℓ
  have hcommIn : g * ⁅ℓ, r⁆ * g⁻¹ ∈ Q z ⊓ centerIn (QaOf a) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hcommQa
      rwa [map_conj_QaOf_eq_Q hga] at h
    · have h' : g * ⁅ℓ, r⁆ * g⁻¹ ∈ (ZQ z).map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨⁅ℓ, r⁆, hcommZ, by
          change (MulAut.conj g) ⁅ℓ, r⁆ = g * ⁅ℓ, r⁆ * g⁻¹
          rw [MulAut.conj_apply]⟩
      rwa [← centerIn_QaOf_eq_map_conj S hgz] at h'
  have hzaZ : z ∉ centerIn (QaOf a) :=
    z_not_mem_centerIn_Qa S haQ hconj haZ hza
  have hsup := centerIn_QaOf_inf_Q_le_sup_zpowers_ZQ S haQ hzaZ hcommIn
  have hxt : ⁅x, g * r * g⁻¹⁆ = g * ⁅ℓ, r⁆ * g⁻¹ := by
    rw [← hℓx', commutatorElement_def, commutatorElement_def]
    group
  rwa [hxt]

theorem Sec3Hyp.rhoLin_sub_mem_span_of_fix {S : Setting z E F} {a g : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hgQaz : g ∈ QaOf (a * z)) (hga : g * a * g⁻¹ = z)
    (r : ↥(Q z))
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r))
    (t : ↥(H z)) (ht : (t : G) = g * (r : G) * g⁻¹)
    (hrCa : (r : G) ∈ Subgroup.centralizer ({a} : Set G))
    {x : Additive (QbarOf S)}
    (hx : QuadraticMap.polar (qS S) x (aVec S h.mem_Q) = 0) :
    rhoLin S (QuotientGroup.mk t) x - x ∈ (ZMod 2) ∙ aVec S h.mem_Q := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  obtain ⟨y, hyC, hyv⟩ := (mem_QaInterImage_iff S).mp
    (mem_QaInterImage_CQ_of_polar_aVec_eq_zero S h.mem_Q hx)
  have hyQ : (y : G) ∈ Q z := y.2
  have hyCa : (y : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.mem_inf.mp hyC).2
  have hcommZ : ∀ ℓ ∈ L0 S a, ⁅ℓ, (r : G)⁆ ∈ ZQ z :=
    fun ℓ hℓ => Sec3Hyp.commutator_mem_ZQ_of_mem_L0 h hfix hℓ
  have hcomm := commutator_conj_mem_sup_zpowers_ZQ S h.mem_Q h.isConj h.not_mem_ZQ
    h.mem_Qa hgQaz hga hrCa hcommZ (x := (y : G))
    (Subgroup.mem_inf.mpr ⟨hyQ, hyCa⟩)
  have hcomm' : ⁅(y : G), (t : G)⁆ ∈ Subgroup.zpowers a ⊔ ZQ z := by
    simpa [← ht] using hcomm
  have hclass : Additive.ofMul (mkQbar S
      ⟨⁅(y : G), (t : G)⁆, commutator_mem_Q_of_mem_H t.2 y.2⟩) ∈
      (ZMod 2) ∙ aVec S h.mem_Q :=
    mkQbar_mem_span_of_mem_sup_zpowers_ZQ S h.mem_Q h.isConj hcomm'
      (commutator_mem_Q_of_mem_H t.2 y.2)
  have hxy : x = Additive.ofMul (mkQbar S y) := by
    simpa using (congrArg Additive.ofMul hyv).symm
  have hdiff : rhoLin S (QuotientGroup.mk t) x - x =
      Additive.ofMul (mkQbar S
        ⟨⁅(y : G), (t : G)⁆, commutator_mem_Q_of_mem_H t.2 y.2⟩) := by
    rw [rhoLin_mk_eq_conjQbar S t, hxy]
    exact (additive_commutator_eq_sub S t.2 y.2).symm
  rwa [hdiff]

theorem Sec3Hyp.rhoLin_mem_pointRadical_of_fix {S : Setting z E F} {a g : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hgQaz : g ∈ QaOf (a * z)) (hga : g * a * g⁻¹ = z)
    (r : ↥(Q z))
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r))
    (t : ↥(H z)) (ht : (t : G) = g * (r : G) * g⁻¹)
    (hrCa : (r : G) ∈ Subgroup.centralizer ({a} : Set G)) :
    (QuotientGroup.mk t : Hbar z) ∈ Lbar S a ∧
      rhoLin S (QuotientGroup.mk t) ∈
        CFSG.LargeExtraspecial.pointRadical (qS S) (aVec S h.mem_Q) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  have hgz : g * z * g⁻¹ = a :=
    conj_z_eq_of_conj_a_eq S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga
  have htL0 : (t : G) ∈ L0 S a := by
    have hmem : (t : G) ∈ (Q z ⊓ Subgroup.centralizer ({a} : Set G)).map
        (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨(r : G), Subgroup.mem_inf.mpr ⟨r.2, hrCa⟩, ?_⟩
      simpa [MulAut.conj_apply, ht]
    rwa [map_conj_CQ_eq_L0 S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga] at hmem
  have hmemLbar : (QuotientGroup.mk t : Hbar z) ∈ Lbar S a :=
    mem_Lbar_of_mem_L0 S htL0
  have hfixa : rhoLin S (QuotientGroup.mk t) (aVec S h.mem_Q) = aVec S h.mem_Q :=
    rhoBar_apply_aVec_of_mem_Lbar S h.mem_Q h.isConj hmemLbar
  have hO : rhoLin S (QuotientGroup.mk t) ∈
      TauCeti.QuadraticMap.orthogonalGroup (qS S) := (rhoBar S (QuotientGroup.mk t)).2
  refine ⟨hmemLbar, (CFSG.LargeExtraspecial.mem_pointRadical).mpr ⟨hO, hfixa, ?_, ?_⟩⟩
  · intro x hx
    have hx' : QuadraticMap.polar (qS S) x (aVec S h.mem_Q) = 0 := by
      rwa [QuadraticMap.polar_comm] at hx
    exact Sec3Hyp.rhoLin_sub_mem_span_of_fix h hgQaz hga r hfix t ht hrCa hx'
  · intro v
    rw [QuadraticMap.polar_sub_right,
      ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO (aVec S h.mem_Q) v,
      hfixa, sub_self]

theorem Sec3Hyp.mk_ne_one_of_fix {S : Setting z E F} {a g : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hgQaz : g ∈ QaOf (a * z)) (hga : g * a * g⁻¹ = z)
    (r : ↥(Q z))
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r))
    (t : ↥(H z)) (ht : (t : G) = g * (r : G) * g⁻¹)
    (hspan : Additive.ofMul (mkQbar S r) ∉ (ZMod 2) ∙ aVec S h.mem_Q) :
    (QuotientGroup.mk t : Hbar z) ≠ 1 := by
  intro ht1
  have htQ : (t : G) ∈ Q z :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff t).mp ht1)
  have htmap : (t : G) ∈ (QaOf a).map (MulAut.conj g).toMonoidHom := by
    rw [map_conj_QaOf_eq_Q hga]
    exact htQ
  obtain ⟨y, hyQa, hy⟩ := Subgroup.mem_map.mp htmap
  have hyr : y = (r : G) := by
    apply (MulAut.conj g).injective
    simpa [MulAut.conj_apply, ht] using hy
  have hrQa : (r : G) ∈ QaOf a := hyr ▸ hyQa
  obtain ⟨l, hl, hsub⟩ := exists_lbar_apply_sub_eq S h.mem_Q h.isConj h.mem_Qa
    r.2 hrQa (by simpa [aVec] using hspan)
  have hsub' : rhoLin S l (Additive.ofMul (mkQbar S r)) -
      Additive.ofMul (mkQbar S r) = Additive.ofMul (mkQbar S ⟨a, h.mem_Q⟩) := by
    simpa [aVec] using hsub
  have hzero : aVec S h.mem_Q = 0 := by
    have hzero' : Additive.ofMul (mkQbar S ⟨a, h.mem_Q⟩) = 0 := by
      rw [← hsub', hfix l hl, sub_self]
    simpa [aVec] using hzero'
  exact aV_ne_zero S h.mem_Q h.not_mem_ZQ hzero

theorem Sec3Hyp.exists_commutator_of_qS_ne_zero {S : Setting z E F} {a g : G} {w : ℕ}
    (h : Sec3Hyp S a w) (r : ↥(Q z))
    (t : ↥(H z)) (ht : (t : G) = g * (r : G) * g⁻¹)
    (hr2 : (r : G) ^ 2 = 1) {u : Additive (QbarOf S)}
    (hu : u ∈ commSpace (rhoLin S (QuotientGroup.mk t)))
    (hua : QuadraticMap.polar (qS S) u (aVec S h.mem_Q) = 0) (hq1 : qS S u = 1) :
    ∃ (c : G) (hcQ : c ∈ Q z) (hcCa : c ∈ Subgroup.centralizer ({a} : Set G)),
      c ^ 2 = z ∧ u = Additive.ofMul (mkQbar S ⟨c, hcQ⟩) ∧
        c * (t : G) * c⁻¹ = (t : G) * z := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  rw [rhoLin_mk_eq_conjQbar S t] at hu
  obtain ⟨y, hyv⟩ := (mem_commSpace_conjQbar_iff S t.2).mp hu
  let c : G := ⁅(y : G), (t : G)⁆
  have hcQ : c ∈ Q z := commutator_mem_Q_of_mem_H t.2 y.2
  have hu_c : u = Additive.ofMul (mkQbar S ⟨c, hcQ⟩) := by
    simpa [c] using hyv
  have hq1c : qS S (Additive.ofMul (mkQbar S ⟨c, hcQ⟩)) = 1 := by
    rw [← hu_c]
    exact hq1
  have hc2ne : c ^ 2 ≠ 1 := by
    intro hc1
    have h0 := (q_eq_zero_iff S ⟨c, hcQ⟩).mpr hc1
    exact one_ne_zero (hq1c.symm.trans h0)
  have hc2z : c ^ 2 = z := by
    rcases eq_one_or_z_of_mem_zpowers S (sq_mem_zpowers_of_mem_Q S hcQ) with h1 | h1
    · exact absurd h1 hc2ne
    · exact h1
  have hcCa : c ∈ Subgroup.centralizer ({a} : Set G) := by
    have hpolar : QuadraticMap.polar (qS S)
        (Additive.ofMul (mkQbar S ⟨c, hcQ⟩)) (aVec S h.mem_Q) = 0 := by
      rw [← hu_c]
      exact hua
    have hcomm : c * a = a * c :=
      (polar_q_eq_zero_iff S ⟨c, hcQ⟩ ⟨a, h.mem_Q⟩).mp hpolar
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hcomm.symm
  have ht2 : (t : G) ^ 2 = 1 := by
    rw [ht, conj_pow, hr2]
    group
  have hconjct : c * (t : G) * c⁻¹ = (t : G) * z :=
    conj_s_eq_mul_z_of_commutator S (s := (t : G)) (q := (y : G)) ht2
      (by simpa [c] using hc2z)
  exact ⟨c, hcQ, hcCa, hc2z, hu_c, hconjct⟩

theorem Sec3Hyp.exists_mem_L0_conj_eq_mul {S : Setting z E F} {a g : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hgQaz : g ∈ QaOf (a * z)) (hga : g * a * g⁻¹ = z)
    (r : ↥(Q z)) (t : ↥(H z)) (ht : (t : G) = g * (r : G) * g⁻¹)
    {c : G} (hcQ : c ∈ Q z) (hcCa : c ∈ Subgroup.centralizer ({a} : Set G))
    (hconjct : c * (t : G) * c⁻¹ = (t : G) * z) :
    ∃ d : ↥(H z), (d : G) ∈ L0 S a ∧
      (d : G) * (r : G) * (d : G)⁻¹ = (r : G) * a := by
  have hcmap : c ∈ (L0 S a).map (MulAut.conj g).toMonoidHom := by
    rw [show L0 S a = QaOf a ⊓ H z from rfl,
      map_conj_L0_eq_CQ S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga]
    exact Subgroup.mem_inf.mpr ⟨hcQ, hcCa⟩
  obtain ⟨d, hdL0, hdg⟩ := Subgroup.mem_map.mp hcmap
  have hdH : d ∈ H z := (Subgroup.mem_inf.mp hdL0).2
  let dH : ↥(H z) := ⟨d, hdH⟩
  have hd_eq : d = g⁻¹ * c * g := by
    calc
      d = g⁻¹ * (g * d * g⁻¹) * g := by group
      _ = g⁻¹ * c * g := by rw [show g * d * g⁻¹ = c by simpa [MulAut.conj_apply] using hdg]
  have hdr : d * (r : G) * d⁻¹ = (r : G) * a := by
    rw [hd_eq]
    calc
      (g⁻¹ * c * g) * (r : G) * (g⁻¹ * c * g)⁻¹
          = g⁻¹ * (c * (g * (r : G) * g⁻¹) * c⁻¹) * g := by group
      _ = g⁻¹ * (c * (t : G) * c⁻¹) * g := by rw [← ht]
      _ = g⁻¹ * ((t : G) * z) * g := by rw [hconjct]
      _ = (g⁻¹ * (t : G) * g) * (g⁻¹ * z * g) := by group
      _ = (r : G) * a := by
            have h1 : g⁻¹ * (t : G) * g = (r : G) := by rw [ht]; group
            have h2 : g⁻¹ * z * g = a := by
              calc
                g⁻¹ * z * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [← hga]
                _ = a := by group
            rw [h1, h2]
  exact ⟨dH, hdL0, hdr⟩

theorem Sec3Hyp.qS_eq_zero_of_mem_commSpace_of_fix {S : Setting z E F} {a g : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hgQaz : g ∈ QaOf (a * z)) (hga : g * a * g⁻¹ = z)
    (r : ↥(Q z))
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r))
    (t : ↥(H z)) (ht : (t : G) = g * (r : G) * g⁻¹)
    (hr2 : (r : G) ^ 2 = 1) {u : Additive (QbarOf S)}
    (hu : u ∈ commSpace (rhoLin S (QuotientGroup.mk t)))
    (hua : QuadraticMap.polar (qS S) u (aVec S h.mem_Q) = 0) :
    qS S u = 0 := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  by_contra hq0
  have hq1 : qS S u = 1 := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (qS S u) with h1 | h1
    · exact absurd h1 hq0
    · exact h1
  obtain ⟨c, hcQ, hcCa, -, -, hconjct⟩ :=
    Sec3Hyp.exists_commutator_of_qS_ne_zero h r t ht hr2 hu hua hq1
  obtain ⟨dH, hdL0, hdr⟩ :=
    Sec3Hyp.exists_mem_L0_conj_eq_mul h hgQaz hga r t ht hcQ hcCa hconjct
  have hdbar : (QuotientGroup.mk dH : Hbar z) ∈ Lbar S a :=
    mem_Lbar_of_mem_L0 S hdL0
  have hdapply := rhoLin_mk_apply_of_conj_eq_mul S h.mem_Q dH r hdr
  have hfixd := hfix (QuotientGroup.mk dH) hdbar
  have hzero : aVec S h.mem_Q = 0 := by
    have h1 : Additive.ofMul (mkQbar S r) + aVec S h.mem_Q =
        Additive.ofMul (mkQbar S r) := by
      rw [← hdapply]
      exact hfixd
    have h1' : Additive.ofMul (mkQbar S r) + aVec S h.mem_Q =
        Additive.ofMul (mkQbar S r) + 0 := by simpa using h1
    exact add_left_cancel h1'
  exact aV_ne_zero S h.mem_Q h.not_mem_ZQ hzero

theorem Sec3Hyp.mem_Tset_of_fix {S : Setting z E F} {a g : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hgQaz : g ∈ QaOf (a * z)) (hga : g * a * g⁻¹ = z)
    (r : ↥(Q z))
    (hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (Additive.ofMul (mkQbar S r)) =
      Additive.ofMul (mkQbar S r))
    (t : ↥(H z)) (ht : (t : G) = g * (r : G) * g⁻¹)
    (hq : qS S (Additive.ofMul (mkQbar S r)) = 0)
    (hspan : Additive.ofMul (mkQbar S r) ∉ (ZMod 2) ∙ aVec S h.mem_Q) :
    (QuotientGroup.mk t : Hbar z) ∈ Tset S a := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
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
  have h4 := Sec3Hyp.rhoLin_mem_pointRadical_of_fix h hgQaz hga r hfix t ht hrCa
  have hmemLbar : (QuotientGroup.mk t : Hbar z) ∈ Lbar S a := h4.1
  have hβne : (QuotientGroup.mk t : Hbar z) ≠ 1 :=
    Sec3Hyp.mk_ne_one_of_fix h hgQaz hga r hfix t ht hspan
  have ha0 : aVec S h.mem_Q ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  have haq : qS S (aVec S h.mem_Q) = 0 := qS_aVec_eq_zero S h.mem_Q h.isConj
  obtain ⟨u, huPolar, hlin⟩ :=
    (CFSG.LargeExtraspecial.mem_pointRadical_iff (q_nondegenerate S) ha0 haq).mp h4.2
  have hu_not_span : u ∉ (ZMod 2) ∙ aVec S h.mem_Q := by
    intro hu
    apply hβne
    apply rhoLin_injective S
    rw [hlin, (CFSG.LargeExtraspecial.eichler_eq_one_iff (q_nondegenerate S) ha0 haq
      huPolar).mpr hu]
    simp [rhoLin]
  have hcommu : u ∈ commSpace (rhoLin S (QuotientGroup.mk t)) := by
    have hcomm_eq := (CFSG.LargeExtraspecial.eichler_type_of_not_mem_span
      (q_nondegenerate S) ha0 haq huPolar hu_not_span).1
    rw [hlin, hcomm_eq]
    exact Submodule.subset_span (by simp)
  have hr2 : (r : G) ^ 2 = 1 := (q_eq_zero_iff S r).mp hq
  have hua : QuadraticMap.polar (qS S) u (aVec S h.mem_Q) = 0 := by
    simpa [QuadraticMap.polar_comm] using huPolar
  have huq : qS S u = 0 :=
    Sec3Hyp.qS_eq_zero_of_mem_commSpace_of_fix h hgQaz hga r hfix t ht hr2 hcommu hua
  have htype : CFSG.LargeExtraspecial.IsTypeA (qS S)
      (rhoLin S (QuotientGroup.mk t)) 2 := by
    have := (CFSG.LargeExtraspecial.eichler_type_of_not_mem_span
      (q_nondegenerate S) ha0 haq huPolar hu_not_span).2.1 huq
    rwa [← hlin] at this
  exact ⟨hmemLbar, hβne, isA2Hbar_of_isTypeA_rhoBar S (by simpa [rhoLin] using htype)⟩

end CFSG.RankThree.GF2n.Stroth78
