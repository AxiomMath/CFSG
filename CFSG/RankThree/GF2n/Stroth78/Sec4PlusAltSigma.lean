module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltXhat
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusZQFour

import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
import CFSG.RankThree.GF2n.Stroth78.Sec2Eleven
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse
import CFSG.Permutation.AlternatingAutomorphism.Conjugation
import CFSG.CGT.A8S.TopPerm
import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem conj_mem_ZQ_of_mem_H (S : Setting z E F) {h u : G} (hh : h ∈ H z) (hu : u ∈ ZQ z) :
    h * u * h⁻¹ ∈ ZQ z := by
  have e := conjAutZQ_apply S ⟨h, hh⟩ ⟨u, hu⟩
  rw [← e]
  exact (conjAutZQ S ⟨h, hh⟩ ⟨u, hu⟩).2

theorem mem_centerIn_QaOf_iff_conj (S : Setting z E F) {a g : G} (hga : g * a * g⁻¹ = z)
    {x : G} : x ∈ centerIn (QaOf a) ↔ g * x * g⁻¹ ∈ ZQ z := by
  have hgz' : g⁻¹ * z * g⁻¹⁻¹ = a := by
    rw [inv_inv, ← hga]
    group
  rw [centerIn_QaOf_eq_map_of_conj_eq S hgz', Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem exists_commutator_eq_a (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ : Nat.card ↥(ZQ z) = 4) :
    ∃ q s : G, q ∈ Q z ∧ q ∈ Subgroup.centralizer ({a} : Set G) ∧ s ∈ centerIn (QaOf a) ∧
      ∃ hsH : s ∈ H z, (QuotientGroup.mk (⟨s, hsH⟩ : ↥(H z)) : Hbar z) ∈ Rbar S a ∧
        ⁅q, s⁆ = a := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  obtain ⟨α, hα1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hαR : (α : Hbar z) ∈ Rbar S a := α.2
  have hα1' : (α : Hbar z) ≠ 1 := fun h1 => hα1 (Subtype.ext h1)
  obtain ⟨s, hsZ, hsH, -, hsα⟩ := exists_mem_centerIn_inf_H_of_mem_Rbar S hαR hα1'
  have hmem := aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
    h.centerIn_Qa_not_le_Q hαR hα1'
  have hσ : (rhoBar S (α : Hbar z) : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) =
      conjQbar S ⟨(s : G), hsH⟩ := by
    rw [← hsα, rhoBar_apply_mk, rho_apply_mk]
  rw [hσ] at hmem
  obtain ⟨q, hq⟩ := (mem_commSpace_conjQbar_iff S hsH).mp hmem
  have hsub := additive_commutator_eq_sub S hsH q.2
  have hu0 : conjQbar S ⟨(s : G), hsH⟩ (Additive.ofMul (mkQbar S ⟨(q : G), q.2⟩)) -
      Additive.ofMul (mkQbar S ⟨(q : G), q.2⟩) = aVec S h.mem_Q := by
    rw [← hsub, ← hq]
  have hO : conjQbar S ⟨(s : G), hsH⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup (qS S) :=
    conjQbar_mem_orthogonal S ⟨(s : G), hsH⟩
  have hqσ : qS S (conjQbar S ⟨(s : G), hsH⟩ (Additive.ofMul (mkQbar S ⟨(q : G), q.2⟩))) =
      qS S (Additive.ofMul (mkQbar S ⟨(q : G), q.2⟩)) :=
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO) _
  have hσu : conjQbar S ⟨(s : G), hsH⟩ (Additive.ofMul (mkQbar S ⟨(q : G), q.2⟩)) =
      aVec S h.mem_Q + Additive.ofMul (mkQbar S ⟨(q : G), q.2⟩) := by
    rw [← hu0]
    abel
  have hpol : QuadraticMap.polar (qS S) (aVec S h.mem_Q)
      (Additive.ofMul (mkQbar S ⟨(q : G), q.2⟩)) = 0 := by
    have h1 := QuadraticMap.map_add (qS S) (aVec S h.mem_Q)
      (Additive.ofMul (mkQbar S ⟨(q : G), q.2⟩))
    rw [← hσu, hqσ, qS_aVec_eq_zero S h.mem_Q h.isConj, zero_add] at h1
    exact (add_eq_left.mp h1.symm)
  have hqa : (a : G) * (q : G) = (q : G) * a :=
    (polar_q_eq_zero_iff S ⟨a, h.mem_Q⟩ ⟨(q : G), q.2⟩).mp hpol
  have hqC : (q : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hqa.symm
  obtain ⟨g, hgQaz, hga⟩ :=
    exists_conj_eq_z_of_mem_QaOf_mul_z S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
  have hq'H : g * (q : G) * g⁻¹ ∈ H z := by
    have hgz' : g⁻¹ * z * g⁻¹⁻¹ = a := by
      rw [inv_inv, ← hga]
      group
    have := (mem_centralizer_QaOf_iff S hgz').mp hqC
    simpa using this
  have hs'Z : g * (s : G) * g⁻¹ ∈ ZQ z := (mem_centerIn_QaOf_iff_conj S hga).mp hsZ
  have hc'Z : g * ⁅(q : G), (s : G)⁆ * g⁻¹ ∈ ZQ z := by
    have e : g * ⁅(q : G), (s : G)⁆ * g⁻¹ = ⁅g * (q : G) * g⁻¹, g * (s : G) * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, commutatorElement_def]
    exact (ZQ z).mul_mem (conj_mem_ZQ_of_mem_H S hq'H hs'Z) ((ZQ z).inv_mem hs'Z)
  have hcZa : ⁅(q : G), (s : G)⁆ ∈ centerIn (QaOf a) :=
    (mem_centerIn_QaOf_iff_conj S hga).mpr hc'Z
  have hcQ : ⁅(q : G), (s : G)⁆ ∈ Q z := commutator_mem_Q_of_mem_H hsH q.2
  have hmem : ⁅(q : G), (s : G)⁆ ∈ centerIn (QaOf a) ⊓ Q z := ⟨hcZa, hcQ⟩
  rw [centerIn_QaOf_inf_Q_eq_zpowers_of_card_ZQ_eq_four S h hZ] at hmem
  have ha1 : a ≠ 1 := fun ha => h.not_mem_ZQ (ha ▸ (ZQ z).one_mem)
  have ha2 : a ^ 2 = 1 := by
    have := a_mul_self_eq_one S h.isConj
    rwa [← pow_two] at this
  have hao : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hcl : aVec S h.mem_Q = Additive.ofMul (mkQbar S ⟨⁅(q : G), (s : G)⁆, hcQ⟩) := hq
  have hceq : ⁅(q : G), (s : G)⁆ = a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rcases zpow_eq_one_or_self_of_orderOf_eq_two hao k with h1 | h1
    · exfalso
      have h0 : ⁅(q : G), (s : G)⁆ = 1 := by rw [← hk, h1]
      have hone : (⟨⁅(q : G), (s : G)⁆, hcQ⟩ : ↥(Q z)) = 1 := Subtype.ext h0
      rw [hone] at hcl
      exact aV_ne_zero S h.mem_Q h.not_mem_ZQ (by simpa using hcl)
    · rw [← hk, h1]
  exact ⟨q, s, q.2, hqC, hsZ, hsH, by rw [hsα]; exact hαR, hceq⟩

theorem conj_eq_of_mem_XsubHat_of_mem_ZQ (S : Setting z E F) (a : G)
    (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u) {x u : G} (hx : x ∈ XsubHat S a)
    (hu : u ∈ ZQ z) : x * u * x⁻¹ = u := by
  obtain ⟨hxH, hxX⟩ := (mem_XsubHat_iff S a).mp hx
  have h1 := rhoZ_mk S ⟨x, hxH⟩ ⟨u, hu⟩
  rw [hX1 _ hxX ⟨u, hu⟩] at h1
  exact h1.symm

theorem a_mem_FsubH (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ : Nat.card ↥(ZQ z) = 4) : a ∈ FsubH S a := by
  obtain ⟨q, s, hqQ, -, -, hsH, hsR, hqs⟩ := exists_commutator_eq_a S h hZ
  have hsX : s ∈ XsubHat S a := (mem_XsubHat_iff S a).mpr ⟨hsH, h.Rbar_le_Xsub hsR⟩
  have hmem : ⁅q, s⁆ ∈ FsubH S a := Subgroup.commutator_mem_commutator hqQ hsX
  rwa [hqs] at hmem

theorem exists_mem_L0_not_mem_XsubHat (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ : Nat.card ↥(ZQ z) = 4) (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u) :
    ∃ r ∈ L0 S a, r ∉ XsubHat S a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨q, s, hqQ, hqC, hsZ, hsH, -, hqs⟩ := exists_commutator_eq_a S h hZ
  obtain ⟨g, hgQaz, hga⟩ :=
    exists_conj_eq_z_of_mem_QaOf_mul_z S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
  have hgz : g * z * g⁻¹ = a := conj_z_eq_of_conj_a_eq S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga
  have hq'H : g * q * g⁻¹ ∈ H z := by
    have hgz' : g⁻¹ * z * g⁻¹⁻¹ = a := by
      rw [inv_inv, ← hga]
      group
    have := (mem_centralizer_QaOf_iff S hgz').mp hqC
    simpa using this
  have hq'Qa : g * q * g⁻¹ ∈ QaOf a := by
    rw [QaOf_eq_map_of_conj_eq S hgz]
    exact ⟨q, hqQ, by simp [MulAut.conj_apply]⟩
  have hq'X : g * q * g⁻¹ ∈ XsubHat S a := hcon _ ⟨hq'Qa, hq'H⟩
  have hs'Z : g * s * g⁻¹ ∈ ZQ z := (mem_centerIn_QaOf_iff_conj S hga).mp hsZ
  have h1 := conj_eq_of_mem_XsubHat_of_mem_ZQ S a hX1 hq'X hs'Z
  have h2 : ⁅g * q * g⁻¹, g * s * g⁻¹⁆ = 1 := by
    rw [commutatorElement_def, h1]
    group
  have h3 : ⁅q, s⁆ = 1 := by
    have e : g * ⁅q, s⁆ * g⁻¹ = ⁅g * q * g⁻¹, g * s * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h2] at e
    calc ⁅q, s⁆ = g⁻¹ * (g * ⁅q, s⁆ * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  have ha1 : a ≠ 1 := fun ha => h.not_mem_ZQ (ha ▸ (ZQ z).one_mem)
  exact ha1 (hqs.symm.trans h3)

private theorem conjNormal_perm_bijective :
    Function.Bijective
      (MulAut.conjNormal : Equiv.Perm (Fin 8) →* MulAut (alternatingGroup (Fin 8))) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    rw [Subgroup.mem_bot]
    refine CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating (by simp) ?_
    intro g hg
    have h1 := congrArg
      (fun f : MulAut (alternatingGroup (Fin 8)) => (f ⟨g, hg⟩ : Equiv.Perm (Fin 8))) hσ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc σ * g = (σ * g * σ⁻¹) * σ := by group
      _ = g * σ := by rw [h1]
  · intro f
    obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
      (by omega : 8 = 5 ∨ 7 ≤ 8) f
    refine ⟨σ, MulEquiv.ext fun g => Subtype.ext ?_⟩
    simp only [MulAut.conjNormal_apply]
    exact (hσ g).symm

theorem exists_mulEquiv_perm_eight (S : Setting z E F) (a : G)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8))
    (hC : Subgroup.centralizer (Xsub S a : Set (Hbar z)) = ⊥)
    (hne : ∃ r : Hbar z, r ∉ Xsub S a) :
    ∃ ι : Hbar z ≃* Equiv.Perm (Fin 8), ∀ x : ↥(Xsub S a),
      ι (x : Hbar z) = ((e x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) := by
  classical
  haveI := Xsub_normal S a
  let cE : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective MulAut.conjNormal conjNormal_perm_bijective
  let φ : Hbar z →* Equiv.Perm (Fin 8) :=
    (cE.symm.toMonoidHom).comp
      (((MulAut.congr e).toMonoidHom).comp (MulAut.conjNormal : Hbar z →* MulAut ↥(Xsub S a)))
  have hφx : ∀ x : ↥(Xsub S a),
      φ (x : Hbar z) = ((e x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) := by
    intro x
    have hcE : cE ((e x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        MulAut.congr e (MulAut.conjNormal (x : Hbar z)) := by
      refine MulEquiv.ext fun y => Subtype.ext ?_
      have key : (MulAut.congr e (MulAut.conjNormal (x : Hbar z)) y :
          alternatingGroup (Fin 8)) = e x * y * (e x)⁻¹ := by
        have h1 : (MulAut.conjNormal (x : Hbar z) : MulAut ↥(Xsub S a)) (e.symm y) =
            x * e.symm y * x⁻¹ := Subtype.ext (by simp [MulAut.conjNormal_apply])
        show e ((MulAut.conjNormal (x : Hbar z) : MulAut ↥(Xsub S a)) (e.symm y)) = _
        rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [key]
      exact MulAut.conjNormal_apply _ _
    exact cE.symm_apply_eq.mpr hcE.symm
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    rw [Subgroup.mem_bot]
    have h1 : MulAut.congr e (MulAut.conjNormal h) = 1 := by
      have : cE.symm (MulAut.congr e (MulAut.conjNormal h)) = 1 := hh
      exact (MulEquiv.map_eq_one_iff cE.symm).mp this
    have h2 : (MulAut.conjNormal h : MulAut ↥(Xsub S a)) = 1 :=
      (MulEquiv.map_eq_one_iff (MulAut.congr e)).mp h1
    have h3 : h ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := congrArg (fun f : MulAut ↥(Xsub S a) => ((f ⟨x, hx⟩ : ↥(Xsub S a)) : Hbar z)) h2
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc x * h = (h * x * h⁻¹) * h := by rw [this]
        _ = h * x := by group
    rw [hC] at h3
    exact h3
  have hX : Nat.card ↥(Xsub S a) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hidx : (Xsub S a).index ≠ 1 := by
    intro h1
    obtain ⟨r, hr⟩ := hne
    apply hr
    rw [Subgroup.index_eq_one.mp h1]
    trivial
  have hidx0 : (Xsub S a).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard1 : 2 * 20160 ≤ Nat.card (Hbar z) := by
    have h1 := Subgroup.card_mul_index (Xsub S a)
    rw [hX] at h1
    omega
  have hcard : Nat.card (Equiv.Perm (Fin 8)) ≤ Nat.card (Hbar z) := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
    omega
  exact ⟨MulEquiv.ofBijective φ (hφinj.bijective_of_nat_card_le hcard), fun x => hφx x⟩

theorem exists_mem_Lbar_inf_Xsub_cycleType_two_two (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hw : w = 4) (hLle : Nat.card ↥(Lbar S a) ≤ 16)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8)) (ι : Hbar z ≃* Equiv.Perm (Fin 8))
    (hι : ∀ x : ↥(Xsub S a), ι (x : Hbar z) = ((e x : alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8)))
    {r : Hbar z} (hrL : r ∈ Lbar S a) (hrX : r ∉ Xsub S a) :
    ∃ t : Hbar z, t ∈ Lbar S a ∧ t ∈ Xsub S a ∧ (ι t).cycleType = {2, 2} := by
  classical
  haveI := Xsub_normal S a
  have hL16 : Nat.card ↥(Lbar S a) = 16 := by
    have h1 := h.two_pow_le_card_Lbar
    rw [hw] at h1
    omega
  have hX : Nat.card ↥(Xsub S a) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hH : Nat.card (Hbar z) = 40320 := by
    rw [Nat.card_congr ι.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hidx : (Xsub S a).index = 2 := by
    have h1 := Subgroup.card_mul_index (Xsub S a)
    rw [hX, hH] at h1
    omega
  have hrel : (Xsub S a).relIndex (Lbar S a) = 2 := by
    have hd : (Xsub S a).relIndex (Lbar S a) ∣ 2 := by
      rw [← hidx]
      exact Subgroup.relIndex_dvd_index_of_normal _ _
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact absurd (Subgroup.relIndex_eq_one.1 h1 hrL) hrX
    · exact h1
  have hT8 : Nat.card ↥(Xsub S a ⊓ Lbar S a) = 8 := by
    have h1 := Subgroup.relIndex_mul_card (Xsub S a) (Lbar S a)
    rw [hrel, hL16] at h1
    omega
  by_contra hcon
  push Not at hcon
  have hnofix : ∀ t : Hbar z, t ∈ Lbar S a → t ∈ Xsub S a → t ≠ 1 → ∀ i, ι t i ≠ i := by
    intro t htL htX ht1 i
    have ht2 : (ι t) ^ 2 = 1 := by
      rw [← map_pow, sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj htL, map_one]
    have ht1' : ι t ≠ 1 := fun h1 => ht1 (ι.injective (by rw [h1, map_one]))
    obtain ⟨k, hk, hk1, hk4⟩ := CFSG.CGT.A8S.Perm8.cycleType_eq_replicate ht2 ht1'
    have hsign : Equiv.Perm.sign (ι t) = 1 := by
      have := hι ⟨t, htX⟩
      rw [show ι t = ((e ⟨t, htX⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) from this]
      exact Equiv.Perm.mem_alternatingGroup.mp (e ⟨t, htX⟩).2
    have hke := CFSG.CGT.A8S.Perm8.even_of_sign_eq_one hk hsign
    have hk24 : k = 2 ∨ k = 4 := by
      obtain ⟨m, hm⟩ := hke
      omega
    rcases hk24 with rfl | rfl
    · exact absurd (by rw [hk]; rfl) (hcon t htL htX)
    · have hsum := Equiv.Perm.sum_cycleType (ι t)
      rw [hk, Multiset.sum_replicate] at hsum
      have hcard : (ι t).support.card = 8 := by simpa using hsum.symm
      have hfull : (ι t).support = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
      have hi : i ∈ (ι t).support := by rw [hfull]; exact Finset.mem_univ i
      exact Equiv.Perm.mem_support.mp hi
  let f : ↥(Xsub S a ⊓ Lbar S a) → Fin 8 := fun t => (ι (t : Hbar z)) 0
  have hfinj : Function.Injective f := by
    intro t₁ t₂ h12
    have hmem : (t₁ : Hbar z)⁻¹ * (t₂ : Hbar z) ∈ Xsub S a ⊓ Lbar S a :=
      (Xsub S a ⊓ Lbar S a).mul_mem ((Xsub S a ⊓ Lbar S a).inv_mem t₁.2) t₂.2
    have h0 : (ι ((t₁ : Hbar z)⁻¹ * (t₂ : Hbar z))) 0 = 0 := by
      have h12' : (ι (t₂ : Hbar z)) 0 = (ι (t₁ : Hbar z)) 0 := h12.symm
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, h12']
      simp
    by_contra hne
    have hne' : (t₁ : Hbar z)⁻¹ * (t₂ : Hbar z) ≠ 1 := by
      intro h1
      exact hne (Subtype.ext (inv_mul_eq_one.mp h1))
    exact hnofix _ hmem.2 hmem.1 hne' 0 h0
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card, Fintype.card_fin, hT8])
  obtain ⟨t₀, ht₀⟩ := hfbij.2 ((ι r) 0)
  have hιr : ι r = ι (t₀ : Hbar z) := by
    refine Equiv.ext fun j => ?_
    obtain ⟨t, rfl⟩ := hfbij.2 j
    have hrt : r * (t : Hbar z) = (t : Hbar z) * r :=
      commute_of_mem_Lbar S h.mem_Q h.isConj hrL t.2.2
    have ht₀t : (t₀ : Hbar z) * (t : Hbar z) = (t : Hbar z) * (t₀ : Hbar z) :=
      commute_of_mem_Lbar S h.mem_Q h.isConj t₀.2.2 t.2.2
    have h1 : (ι r) ((ι (t : Hbar z)) 0) = (ι (t : Hbar z)) ((ι r) 0) := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, hrt, map_mul, Equiv.Perm.mul_apply]
    have h2 : (ι (t₀ : Hbar z)) ((ι (t : Hbar z)) 0) =
        (ι (t : Hbar z)) ((ι (t₀ : Hbar z)) 0) := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, ht₀t, map_mul, Equiv.Perm.mul_apply]
    calc (ι r) (f t) = (ι (t : Hbar z)) ((ι r) 0) := h1
      _ = (ι (t : Hbar z)) (f t₀) := by rw [ht₀]
      _ = (ι (t₀ : Hbar z)) (f t) := h2.symm
  exact hrX (ι.injective hιr ▸ t₀.2.1)

end CFSG.RankThree.GF2n.Stroth78
