module

public import CFSG.LargeExtraspecial.A2ModPLOrbits
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltIndexTwo

import CFSG.RankThree.GF2n.Stroth78.Sec3SevenFix
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.GroupTheory.IndexMapNormal
import CFSG.CGT.A8S.OddInvolutionIndex

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.LargeExtraspecial.A2Mod (A2Action IsPointMaps transvectionSet)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem relIndex_centralizer_H_eq (S : Setting z E F) (y : G) :
    (H z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (H z) =
      (Q z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (Q z) *
        (((H z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (H z)).map
          (QuotientGroup.mk' ((Q z).subgroupOf (H z)))).index := by
  haveI := instNormalQH z
  have h := CFSG.GroupTheory.index_eq_relIndex_mul_index_map ((Q z).subgroupOf (H z))
    ((H z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (H z))
  have hrel : ((Q z).subgroupOf (H z) ⊓
      (H z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (H z)).relIndex
        ((Q z).subgroupOf (H z)) =
      (Q z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (Q z) := by
    have hinf : (Q z).subgroupOf (H z) ⊓
        (H z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (H z) =
        (Q z ⊓ (H z ⊓ Subgroup.centralizer ({y} : Set G))).subgroupOf (H z) := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [hinf, Subgroup.relIndex_subgroupOf (Q_le_H S), ← inf_assoc,
      inf_eq_left.mpr (Q_le_H S)]
  rw [hrel] at h
  exact h

theorem four_dvd_relIndex_Q_of_four_le_natCard_commSpace (S : Setting z E F) {y : G}
    (hy : y ∈ H z)
    (h4 : 4 ≤ Nat.card ↥(commSpace (rhoLin S (QuotientGroup.mk (⟨y, hy⟩ : ↥(H z)) : Hbar z)))) :
    4 ∣ (Q z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (Q z) := by
  classical
  set t : ↥(H z) := ⟨y, hy⟩ with ht
  rw [rhoLin_mk_eq_conjQbar] at h4
  let D : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S) :=
    (conjQbar S t : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S)) - 1
  let Φ : ↥(Q z) →* Multiplicative (Additive (QbarOf S)) :=
    { toFun := fun q => Multiplicative.ofAdd (D (Additive.ofMul (mkQbar S q)))
      map_one' := by simp
      map_mul' := fun q q' => by
        rw [map_mul, ofMul_mul, map_add, ofAdd_add] }
  have hker : (Q z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (Q z) ≤ Φ.ker := by
    intro q hq
    rw [Subgroup.mem_subgroupOf] at hq
    rw [MonoidHom.mem_ker]
    have hcomm : (q : G) * y = y * (q : G) := Subgroup.mem_centralizer_singleton_iff.mp hq.2
    have hconj : conjAutQ S t q = q := Subtype.ext (by
      rw [conjAutQ_apply]
      show y * (q : G) * y⁻¹ = (q : G)
      rw [← hcomm, mul_inv_cancel_right])
    have h0 : D (Additive.ofMul (mkQbar S q)) = 0 := by
      show conjQbar S t (Additive.ofMul (mkQbar S q)) - Additive.ofMul (mkQbar S q) = 0
      rw [mkQbar, QuotientGroup.mk'_apply, conjQbar_apply_mk, hconj, sub_self]
    show Multiplicative.ofAdd (D (Additive.ofMul (mkQbar S q))) = 1
    rw [h0]
    rfl
  have hidx : Φ.ker.index = Nat.card Φ.range := Subgroup.index_ker Φ
  have hmem : ∀ w : ↥(commSpace (conjQbar S t)),
      Multiplicative.ofAdd (w : Additive (QbarOf S)) ∈ Φ.range := by
    intro w
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp w.2
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)) (Additive.toMul c)
    refine ⟨q, ?_⟩
    show Multiplicative.ofAdd (D (Additive.ofMul (mkQbar S q))) = _
    rw [mkQbar, hq, ofMul_toMul]
    exact congrArg Multiplicative.ofAdd hc
  have hcard : 4 ≤ Nat.card Φ.range := by
    refine h4.trans (Nat.card_le_card_of_injective (fun w => ⟨_, hmem w⟩) ?_)
    intro w w' hww
    have h1 : Multiplicative.ofAdd (w : Additive (QbarOf S)) =
        Multiplicative.ofAdd (w' : Additive (QbarOf S)) := Subtype.mk.inj hww
    exact Subtype.ext (Multiplicative.ofAdd.injective h1)
  obtain ⟨n, hn⟩ := (Q_isPGroup S).index Φ.ker
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    rw [hidx] at hn
    rw [hn] at hcard
    interval_cases n <;> omega
  have hdvd : 4 ∣ Φ.ker.index := by
    rw [hn]
    exact (pow_dvd_pow 2 hn2 : 2 ^ 2 ∣ 2 ^ n)
  exact hdvd.trans (Subgroup.index_dvd_of_le hker)

theorem four_dvd_relIndex_H_of_mem_Xsub (S : Setting z E F) (a : G)
    {Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(Xsub S a)}
    (hΨs : Function.Surjective Ψ)
    {ρX : ↥(Xsub S a) →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))}
    (hρX : ∀ x, ρX x = rhoLin S (x : Hbar z))
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (QbarOf S)}
    (hP : IsPointMaps (ρX.comp Ψ) (qS S) P Pd) {y : G} (hy : y ∈ H z)
    (hyX : (QuotientGroup.mk (⟨y, hy⟩ : ↥(H z)) : Hbar z) ∈ Xsub S a)
    (hy1 : (QuotientGroup.mk (⟨y, hy⟩ : ↥(H z)) : Hbar z) ≠ 1) :
    4 ∣ (H z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (H z) := by
  haveI : Finite (Additive (QbarOf S)) := inferInstance
  obtain ⟨g, hg⟩ := hΨs ⟨_, hyX⟩
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hy1
    have h1 := congrArg Subtype.val hg
    rw [map_one] at h1
    exact h1.symm
  have h4 := hP.four_le_natCard_commSpace hg1
  have hρ : ((ρX.comp Ψ) g) = rhoLin S (QuotientGroup.mk (⟨y, hy⟩ : ↥(H z))) := by
    rw [MonoidHom.comp_apply, hρX, hg]
  rw [hρ] at h4
  rw [relIndex_centralizer_H_eq S y]
  exact Dvd.dvd.mul_right (four_dvd_relIndex_Q_of_four_le_natCard_commSpace S hy h4) _

theorem four_dvd_relIndex_H_of_not_mem_Xsub (S : Setting z E F) (a : G)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8)) (ι : Hbar z ≃* Equiv.Perm (Fin 8))
    (hι : ∀ x : ↥(Xsub S a),
      ι (x : Hbar z) = ((e x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)))
    {y : G} (hy : y ∈ H z) (hy2 : y ^ 2 = 1)
    (hyX : (QuotientGroup.mk (⟨y, hy⟩ : ↥(H z)) : Hbar z) ∉ Xsub S a) :
    4 ∣ (H z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (H z) := by
  set x : Hbar z := QuotientGroup.mk (⟨y, hy⟩ : ↥(H z)) with hx
  have hx2 : x ^ 2 = 1 := by
    have h1 : (⟨y, hy⟩ : ↥(H z)) ^ 2 = 1 := Subtype.ext (by simpa using hy2)
    rw [hx, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have hix2 : (ι x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  have hsign : Equiv.Perm.sign (ι x) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (ι x)) with h1 | h1
    · exfalso
      have hmem : ι x ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.mpr h1
      apply hyX
      have h2 : ι ((e.symm ⟨ι x, hmem⟩ : ↥(Xsub S a)) : Hbar z) = ι x := by
        rw [hι, MulEquiv.apply_symm_apply]
      have h3 := ι.injective h2
      rw [← h3]
      exact (e.symm ⟨ι x, hmem⟩).2
    · exact h1
  have h4 := CFSG.GroupTheory.four_dvd_index_centralizer_of_sign_eq_neg_one hix2 hsign
  have hcomap : Subgroup.comap ι.toMonoidHom
      (Subgroup.centralizer ({ι x} : Set (Equiv.Perm (Fin 8)))) =
      Subgroup.centralizer ({x} : Set (Hbar z)) := by
    ext h
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      ← map_mul, ι.injective.eq_iff]
  have h5 : (Subgroup.centralizer ({x} : Set (Hbar z))).index =
      (Subgroup.centralizer ({ι x} : Set (Equiv.Perm (Fin 8)))).index := by
    rw [← hcomap]
    exact Subgroup.index_comap_of_surjective
      (Subgroup.centralizer ({ι x} : Set (Equiv.Perm (Fin 8)))) (f := ι.toMonoidHom) ι.surjective
  have hle : ((H z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (H z)).map
      (QuotientGroup.mk' ((Q z).subgroupOf (H z))) ≤
        Subgroup.centralizer ({x} : Set (Hbar z)) := by
    rintro _ ⟨h', hh', rfl⟩
    have hh'' : (h' : G) ∈ H z ⊓ Subgroup.centralizer ({y} : Set G) := hh'
    rw [Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply, hx, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hh''.2)
  rw [relIndex_centralizer_H_eq S y]
  exact Dvd.dvd.mul_left (by rw [← h5] at h4; exact h4.trans (Subgroup.index_dvd_of_le hle)) _

theorem exists_mem_Xsub_apply_aVec_eq (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hw : w = 4)
    {Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(Xsub S a)}
    (hΨs : Function.Surjective Ψ)
    {ρX : ↥(Xsub S a) →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))}
    (hρX : ∀ x, ρX x = rhoLin S (x : Hbar z))
    (hA : A2Action (transvectionSet 4 (ZMod 2)) (qS S) (ρX.comp Ψ))
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (QbarOf S)}
    (hP : IsPointMaps (ρX.comp Ψ) (qS S) P Pd)
    (htop : LinearMap.range P ⊔ LinearMap.range Pd = ⊤)
    (hC : Subgroup.centralizer (Xsub S a : Set (Hbar z)) = ⊥)
    (hX2 : (Xsub S a).index = 2) {r : Hbar z} (hrX : r ∉ Xsub S a)
    (hr : rhoLin S r (aVec S h.mem_Q) = aVec S h.mem_Q)
    {y : G} (hyQ : y ∈ Q z) (hyZ : y ∉ ZQ z) (hy2 : y ^ 2 = 1)
    (hy4 : ¬ 4 ∣ (H z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (H z)) :
    ∃ x ∈ Xsub S a, rhoLin S x (aVec S h.mem_Q) = Additive.ofMul (mkQbar S ⟨y, hyQ⟩) := by
  classical
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  have hdim : finrank (ZMod 2) (Additive (QbarOf S)) < 16 := by
    rw [finrank_QbarOf_eq_two_mul S h.card_F, hw]
    norm_num
  have hpure : ∀ u : Additive (QbarOf S), u ≠ 0 →
      (u ∈ LinearMap.range P ∨ u ∈ LinearMap.range Pd) → ∀ ℓ : Hbar z,
        rhoLin S ℓ u = u → ℓ ∈ Xsub S a := by
    intro u hu hu' ℓ hℓ
    let ρH : Hbar z →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) :=
      (Subgroup.subtype _).comp (rhoBar S)
    let Ψ' : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* Hbar z :=
      (Xsub S a).subtype.comp Ψ
    have hρeq : ρH.comp Ψ' = ρX.comp Ψ := MonoidHom.ext fun g => (hρX (Ψ g)).symm
    have hP' : IsPointMaps (ρH.comp Ψ') (qS S) P Pd := by
      rw [hρeq]
      exact hP
    have hrange : Ψ'.range = Xsub S a := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hΨs, ← MonoidHom.range_eq_map]
      exact Subgroup.range_subtype _
    have hC' : Subgroup.centralizer (Ψ'.range : Set (Hbar z)) = ⊥ := by
      rw [hrange]
      exact hC
    have hnorm : ∀ g, ∃ g', ℓ * Ψ' g * ℓ⁻¹ = Ψ' g' := by
      intro g
      have hmem : ℓ * ((Ψ g : ↥(Xsub S a)) : Hbar z) * ℓ⁻¹ ∈ Xsub S a :=
        (Xsub_normal S a).conj_mem _ (Ψ g).2 ℓ
      obtain ⟨g', hg'⟩ := hΨs ⟨_, hmem⟩
      exact ⟨g', by simpa [Ψ'] using (congrArg Subtype.val hg').symm⟩
    have := hP'.mem_range_of_apply_eq hC' hnorm hu hu' hℓ
    rwa [hrange] at this
  have ha0 : aVec S h.mem_Q ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  have hy0 : Additive.ofMul (mkQbar S ⟨y, hyQ⟩) ≠ 0 := aV_ne_zero S hyQ hyZ
  have hasing : qS S (aVec S h.mem_Q) = 0 := qS_aVec_eq_zero S h.mem_Q h.isConj
  have hysing : qS S (Additive.ofMul (mkQbar S ⟨y, hyQ⟩)) = 0 :=
    (q_eq_zero_iff S ⟨y, hyQ⟩).mpr hy2
  have hapure : ¬ (aVec S h.mem_Q ∈ LinearMap.range P ∨ aVec S h.mem_Q ∈ LinearMap.range Pd) :=
    fun hp => hrX (hpure _ ha0 hp r hr)
  have hypure : ¬ (Additive.ofMul (mkQbar S ⟨y, hyQ⟩) ∈ LinearMap.range P ∨
      Additive.ofMul (mkQbar S ⟨y, hyQ⟩) ∈ LinearMap.range Pd) := by
    intro hp
    apply hy4
    rw [relIndex_centralizer_H_eq S y]
    have hA2 : 2 ∣ (Q z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (Q z) := by
      obtain ⟨n, hn⟩ := (Q_isPGroup S).index
        ((Q z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (Q z))
      have hn0 : n ≠ 0 := by
        rintro rfl
        have h1 : (Q z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (Q z) = 1 := by
          simpa using hn
        have h2 := Subgroup.relIndex_eq_one.mp h1
        apply hyZ
        refine Subgroup.mem_inf.mpr ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (h2 hq)).2
      show 2 ∣ ((Q z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (Q z)).index
      rw [hn]
      exact dvd_pow_self 2 hn0
    have hB2 : 2 ∣ (((H z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (H z)).map
        (QuotientGroup.mk' ((Q z).subgroupOf (H z)))).index := by
      have hle : ((H z ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf (H z)).map
          (QuotientGroup.mk' ((Q z).subgroupOf (H z))) ≤ Xsub S a := by
        rintro _ ⟨h', hh', rfl⟩
        have hh'' : (h' : G) ∈ H z ⊓ Subgroup.centralizer ({y} : Set G) := hh'
        have hcomm : (h' : G) * y = y * (h' : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp hh''.2
        refine hpure _ hy0 hp _ ?_
        rw [QuotientGroup.mk'_apply, rhoLin_mk_eq_conjQbar]
        show conjQbar S h' (Additive.ofMul (QuotientGroup.mk ⟨y, hyQ⟩)) =
          Additive.ofMul (QuotientGroup.mk ⟨y, hyQ⟩)
        rw [conjQbar_apply_mk]
        congr 2
        exact Subtype.ext (by
          rw [conjAutQ_apply]
          show (h' : G) * y * (h' : G)⁻¹ = y
          rw [hcomm, mul_inv_cancel_right])
      have h1 := Subgroup.index_dvd_of_le hle
      rwa [hX2] at h1
    simpa using mul_dvd_mul hA2 hB2
  have hmema : aVec S h.mem_Q ∈ LinearMap.range P ⊔ LinearMap.range Pd := by
    rw [htop]
    trivial
  have hmemy : Additive.ofMul (mkQbar S ⟨y, hyQ⟩) ∈ LinearMap.range P ⊔ LinearMap.range Pd := by
    rw [htop]
    trivial
  obtain ⟨g, hg⟩ := hP.exists_apply_eq_of_singular_of_not_mem_range hA hdim hmemy hmema hysing
    hasing (fun h1 => hypure (Or.inl h1)) (fun h1 => hypure (Or.inr h1))
    (fun h1 => hapure (Or.inl h1)) (fun h1 => hapure (Or.inr h1))
  refine ⟨((Ψ g : ↥(Xsub S a)) : Hbar z), (Ψ g).2, ?_⟩
  rw [← hρX]
  exact hg

theorem isConj_a_mul_z (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w) :
    IsConj a (a * z) := by
  obtain ⟨q, hq, hqa⟩ : ∃ q ∈ Q z, q * a ≠ a * q := by
    by_contra hcon
    push Not at hcon
    exact h.not_mem_ZQ (Subgroup.mem_inf.mpr ⟨h.mem_Q, Subgroup.mem_centralizer_iff.mpr hcon⟩)
  have hc : ⁅q, a⁆ ∈ Subgroup.zpowers z := by
    rw [← Q_deriv_eq S]
    exact Subgroup.commutator_mem_commutator hq h.mem_Q
  have hcz : ⁅q, a⁆ = z := by
    rcases eq_one_or_z_of_mem_zpowers S hc with h1 | h1
    · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1) hqa
    · exact h1
  have hza : a * z = z * a :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (z_mem_ZQ S)).2 a h.mem_Q
  refine isConj_iff.mpr ⟨q, ?_⟩
  rw [hza, ← hcz, commutatorElement_def]
  group

theorem isConj_z_of_apply_aVec_eq (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ : Nat.card ↥(ZQ z) = 4) (hFinf : FsubH S a ⊓ ZQ z = Subgroup.zpowers z)
    {y : G} (hyQ : y ∈ Q z) (hyF : y ∈ FsubH S a) {x : Hbar z} (hx : x ∈ Xsub S a)
    (hxy : rhoLin S x (aVec S h.mem_Q) = Additive.ofMul (mkQbar S ⟨y, hyQ⟩)) :
    IsConj z y := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
  have htH : (t : G) ∈ H z := t.2
  have hxy' : conjQbar S t (Additive.ofMul (QuotientGroup.mk ⟨a, h.mem_Q⟩)) =
      Additive.ofMul (QuotientGroup.mk ⟨y, hyQ⟩) := by
    rw [← rhoLin_mk_eq_conjQbar]
    exact hxy
  rw [conjQbar_apply_mk] at hxy'
  have h1 : (QuotientGroup.mk (conjAutQ S t ⟨a, h.mem_Q⟩) : QbarOf S) =
      QuotientGroup.mk ⟨y, hyQ⟩ := Additive.ofMul.injective hxy'
  have hu : ((conjAutQ S t ⟨a, h.mem_Q⟩)⁻¹ * ⟨y, hyQ⟩ : ↥(Q z)) ∈
      (ZQ z).subgroupOf (Q z) := QuotientGroup.eq.mp h1
  rw [Subgroup.mem_subgroupOf] at hu
  have hu' : ((t : G) * a * (t : G)⁻¹)⁻¹ * y ∈ ZQ z := by
    simpa [conjAutQ_apply] using hu
  have hat : (t : G) * a * (t : G)⁻¹ ∈ FsubH S a :=
    conj_mem_FsubH S a htH (a_mem_FsubH S h hZ)
  have huF : ((t : G) * a * (t : G)⁻¹)⁻¹ * y ∈ FsubH S a :=
    (FsubH S a).mul_mem ((FsubH S a).inv_mem hat) hyF
  have huz : ((t : G) * a * (t : G)⁻¹)⁻¹ * y ∈ Subgroup.zpowers z := by
    rw [← hFinf]
    exact ⟨huF, hu'⟩
  have hzc : (t : G) * z = z * (t : G) := Subgroup.mem_centralizer_singleton_iff.mp htH
  rcases eq_one_or_z_of_mem_zpowers S huz with h1 | h1
  · have hy : (t : G) * a * (t : G)⁻¹ = y := inv_mul_eq_one.mp h1
    exact h.isConj.trans (isConj_iff.mpr ⟨t, hy⟩)
  · have hy : y = (t : G) * a * (t : G)⁻¹ * z := inv_mul_eq_iff_eq_mul.mp h1
    have hconj : IsConj (a * z) y := isConj_iff.mpr ⟨t, by
      rw [hy]
      calc (t : G) * (a * z) * (t : G)⁻¹
          = ((t : G) * a * (t : G)⁻¹) * ((t : G) * z * (t : G)⁻¹) := by group
        _ = (t : G) * a * (t : G)⁻¹ * z := by
            rw [show (t : G) * z * (t : G)⁻¹ = z by rw [hzc]; group]⟩
    exact h.isConj.trans ((isConj_a_mul_z S h).trans hconj)

theorem sq_eq_one_of_mem_ZQ (S : Setting z E F) {u : G} (hu : u ∈ ZQ z) : u ^ 2 = 1 := by
  have hcomm : ∀ a ∈ E, ∀ w ∈ Subgroup.zpowers z, a * w = w * a := by
    intro a ha w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hza : z * a = a * z :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (E_le_ZQ S ha)).2 z (z_mem_Q S)
    exact (Commute.zpow_right (show Commute a z from hza.symm) k).eq
  rw [ZQ_eq S] at hu
  obtain ⟨e, he, w, hw, rfl⟩ := CFSG.CGT.T75H.exists_mul_of_mem_sup_of_comm hcomm hu
  have he2 : e ^ 2 = 1 := S.hyp.elemAbelian.2 e he
  have hw2 : w ^ 2 = 1 := by
    rcases eq_one_or_z_of_mem_zpowers S hw with h1 | h1
    · rw [h1]
      exact one_pow 2
    · rw [h1]
      simpa [S.hyp.orderOf_z] using pow_orderOf_eq_one z
  rw [(show Commute e w from hcomm e he w hw).mul_pow, he2, hw2, one_mul]

theorem relIndex_centralizer_le_two_of_mem_ZQ (S : Setting z E F)
    (hZ : Nat.card ↥(ZQ z) = 4) {b : G} (hbZ : b ∈ ZQ z) :
    (H z ⊓ Subgroup.centralizer ({b} : Set G)).relIndex (H z) ≤ 2 := by
  by_cases hbz : b ∈ Subgroup.zpowers z
  · have hle : H z ≤ Subgroup.centralizer ({b} : Set G) := by
      intro h hh
      rcases eq_one_or_z_of_mem_zpowers S hbz with hb | hb
      · rw [hb]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
      · rw [hb]
        exact hh
    rw [Subgroup.relIndex_eq_one.mpr (le_inf le_rfl hle)]
    norm_num
  · have hc : ∀ h : ↥(H z), b⁻¹ * ((h : G) * b * (h : G)⁻¹) ∈ Subgroup.zpowers z := fun h =>
      inv_mul_conj_mem_zpowers_of_card_ZQ_eq_four S hZ hbZ hbz h.2
    let ψ : ↥(H z) →* ↥(Subgroup.zpowers z) :=
      { toFun := fun h => ⟨b⁻¹ * ((h : G) * b * (h : G)⁻¹), hc h⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun h h' => by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc h')
          have hcomm : Commute (h : G) (z ^ k) :=
            Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp h.2) k
          have hzh : z ^ k * (h : G)⁻¹ = (h : G)⁻¹ * z ^ k := hcomm.inv_left.eq.symm
          have hb : (h' : G) * b * (h' : G)⁻¹ = b * z ^ k := by
            have : (h' : G) * b * (h' : G)⁻¹ = b * (b⁻¹ * ((h' : G) * b * (h' : G)⁻¹)) := by
              group
            rw [this, hk]
          apply Subtype.ext
          show b⁻¹ * (((h : G) * (h' : G)) * b * ((h : G) * (h' : G))⁻¹) =
            (b⁻¹ * ((h : G) * b * (h : G)⁻¹)) * (b⁻¹ * ((h' : G) * b * (h' : G)⁻¹))
          rw [hb]
          calc b⁻¹ * (((h : G) * (h' : G)) * b * ((h : G) * (h' : G))⁻¹)
              = b⁻¹ * ((h : G) * ((h' : G) * b * (h' : G)⁻¹) * (h : G)⁻¹) := by group
            _ = b⁻¹ * ((h : G) * (b * z ^ k) * (h : G)⁻¹) := by rw [hb]
            _ = b⁻¹ * ((h : G) * b * (z ^ k * (h : G)⁻¹)) := by group
            _ = b⁻¹ * ((h : G) * b * ((h : G)⁻¹ * z ^ k)) := by rw [hzh]
            _ = (b⁻¹ * ((h : G) * b * (h : G)⁻¹)) * (b⁻¹ * (b * z ^ k)) := by group }
    have hker : ψ.ker = (Subgroup.centralizer ({b} : Set G)).subgroupOf (H z) := by
      ext h
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h1
        have h2 : b⁻¹ * ((h : G) * b * (h : G)⁻¹) = 1 := congrArg Subtype.val h1
        have h3 : b = (h : G) * b * (h : G)⁻¹ := inv_mul_eq_one.mp h2
        calc (h : G) * b = (h : G) * b * (h : G)⁻¹ * (h : G) := by group
          _ = b * (h : G) := by rw [← h3]
      · intro h1
        apply Subtype.ext
        show b⁻¹ * ((h : G) * b * (h : G)⁻¹) = 1
        rw [h1]
        group
    have h1 : (H z ⊓ Subgroup.centralizer ({b} : Set G)).relIndex (H z) = ψ.ker.index := by
      unfold Subgroup.relIndex
      rw [Subgroup.inf_subgroupOf_left, hker]
    rw [h1, Subgroup.index_ker]
    calc Nat.card ψ.range ≤ Nat.card ↥(Subgroup.zpowers z) := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_zpowers, S.hyp.orderOf_z]

theorem false_of_isConj_mem_index_two (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hw : w = 4) (hZ : Nat.card ↥(ZQ z) = 4)
    (hweak : ∀ t ∈ ZQ z, IsConj z t → t = z)
    {Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(Xsub S a)}
    (hΨs : Function.Surjective Ψ)
    {ρX : ↥(Xsub S a) →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))}
    (hρX : ∀ x, ρX x = rhoLin S (x : Hbar z))
    (hA : A2Action (transvectionSet 4 (ZMod 2)) (qS S) (ρX.comp Ψ))
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (QbarOf S)}
    (hP : IsPointMaps (ρX.comp Ψ) (qS S) P Pd)
    (htop : LinearMap.range P ⊔ LinearMap.range Pd = ⊤)
    (hC : Subgroup.centralizer (Xsub S a : Set (Hbar z)) = ⊥)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8)) (ι : Hbar z ≃* Equiv.Perm (Fin 8))
    (hι : ∀ x : ↥(Xsub S a),
      ι (x : Hbar z) = ((e x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)))
    {r : G} (hr : r ∈ L0 S a) (hrX : r ∉ XsubHat S a)
    (hFinf : FsubH S a ⊓ ZQ z = Subgroup.zpowers z) (hFsup : FsubH S a ⊔ ZQ z = Q z)
    {b : G} (hbZ : b ∈ ZQ z) (hbz : b ∉ Subgroup.zpowers z)
    {H₁ : Subgroup G} (hH₁ : H₁ ≤ H z) (hbH₁ : b ∉ H₁)
    (hDH₁ : ⁅XsubHat S a, XsubHat S a⁆ ≤ H₁)
    {y : G} (hyb : IsConj b y) (hyH₁ : y ∈ H₁)
    (hy4 : ¬ 4 ∣ (H z ⊓ Subgroup.centralizer ({y} : Set G)).relIndex (H z)) : False := by
  have hyH : y ∈ H z := hH₁ hyH₁
  have hb2 : b ^ 2 = 1 := sq_eq_one_of_mem_ZQ S hbZ
  obtain ⟨c, hc⟩ := isConj_iff.mp hyb
  have hy2 : y ^ 2 = 1 := by
    rw [← hc, conj_pow, hb2]
    group
  have hzH₁ : z ∈ H₁ := hDH₁ (FsubH_le_commutator_XsubHat S a (z_mem_FsubH S a))
  have hzle : Subgroup.zpowers z ≤ H₁ := Subgroup.zpowers_le.mpr hzH₁
  have hbz' : b ≠ z := fun hbz1 => hbz (hbz1 ▸ Subgroup.mem_zpowers z)
  have hb1 : b ≠ 1 := fun hb1 => hbz (hb1 ▸ (Subgroup.zpowers z).one_mem)
  have hrH : r ∈ H z := (Subgroup.mem_inf.mp hr).2
  have hrXb : (QuotientGroup.mk (⟨r, hrH⟩ : ↥(H z)) : Hbar z) ∉ Xsub S a := fun hmem =>
    hrX ((mem_XsubHat_iff S a).mpr ⟨hrH, hmem⟩)
  have hX2 : (Xsub S a).index = 2 := index_Xsub_eq_two S a e ι
  by_cases hyQ : y ∈ Q z
  · by_cases hyZ : y ∈ ZQ z
    · by_cases hyz : y ∈ Subgroup.zpowers z
      · rcases eq_one_or_z_of_mem_zpowers S hyz with h1 | h1
        · rw [h1] at hyb
          exact hb1 (isConj_one_left.mp hyb)
        · rw [h1] at hyb
          exact hbz' (hweak b hbZ hyb.symm)
      · have hmem := inv_mul_mem_zpowers_of_mem_ZQ S hZ hbZ hbz hyZ hyz
        apply hbH₁
        have e1 : b = y * (b⁻¹ * y)⁻¹ := by group
        rw [e1]
        exact H₁.mul_mem hyH₁ (H₁.inv_mem (hzle hmem))
    ·
      have hyF : y ∈ FsubH S a := by
        rcases mem_FsubH_or_inv_mul_mem S a hZ hbZ hbz hFsup hyQ with h1 | h1
        · exact h1
        · exfalso
          apply hbH₁
          have e1 : b = y * (b⁻¹ * y)⁻¹ := by group
          rw [e1]
          exact H₁.mul_mem hyH₁ (H₁.inv_mem
            (hDH₁ (FsubH_le_commutator_XsubHat S a h1)))
      have hra : r * a = a * r :=
        Subgroup.mem_centralizer_iff.mp
          (Subgroup.mem_inf.mp (mem_centerIn_QaOf_of_isConj S h.isConj)).2 r
          (Subgroup.mem_inf.mp hr).1
      have hr' : rhoLin S (QuotientGroup.mk (⟨r, hrH⟩ : ↥(H z))) (aVec S h.mem_Q) =
          aVec S h.mem_Q := by
        rw [rhoLin_mk_eq_conjQbar]
        show conjQbar S ⟨r, hrH⟩ (Additive.ofMul (QuotientGroup.mk ⟨a, h.mem_Q⟩)) =
          Additive.ofMul (QuotientGroup.mk ⟨a, h.mem_Q⟩)
        rw [conjQbar_apply_mk]
        congr 2
        exact Subtype.ext (by
          rw [conjAutQ_apply]
          show r * a * r⁻¹ = a
          rw [hra, mul_inv_cancel_right])
      obtain ⟨x', hx'X, hx'⟩ := exists_mem_Xsub_apply_aVec_eq S h hw hΨs hρX hA hP htop hC hX2
        hrXb hr' hyQ hyZ hy2 hy4
      have hconj : IsConj z y := isConj_z_of_apply_aVec_eq S h hZ hFinf hyQ hyF hx'X hx'
      exact hbz' (hweak b hbZ (hconj.trans hyb.symm))
  · have hx1 : (QuotientGroup.mk (⟨y, hyH⟩ : ↥(H z)) : Hbar z) ≠ 1 := fun h1 =>
      hyQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
    by_cases hxX : (QuotientGroup.mk (⟨y, hyH⟩ : ↥(H z)) : Hbar z) ∈ Xsub S a
    · exact hy4 (four_dvd_relIndex_H_of_mem_Xsub S a hΨs hρX hP hyH hxX hx1)
    · exact hy4 (four_dvd_relIndex_H_of_not_mem_Xsub S a e ι hι hyH hy2 hxX)

end CFSG.RankThree.GF2n.Stroth78
