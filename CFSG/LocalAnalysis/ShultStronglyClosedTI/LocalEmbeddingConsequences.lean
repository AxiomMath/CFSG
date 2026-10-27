module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.ConjugateAction

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem pointClass_conjugate_mem_iff {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (g : G) :
    rightConjugateElem z g ∈ H ↔ g ∈ H := by
  constructor
  · intro hzg
    have hzright : z ∈ rightConjugate H g⁻¹ := by
      have hz := rightConjugateElem_mem_rightConjugate (g := g⁻¹) hzg
      simpa [rightConjugateElem, mul_assoc] using hz
    exact H.inv_mem_iff.mp ((h.unique_containment g⁻¹).mp hzright)
  · intro hg
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) h.distinguished_mem) hg

theorem point_centralizer_le {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) : Subgroup.centralizer ({z} : Set G) ≤ H := by
  intro g hg
  apply (pointClass_conjugate_mem_iff h g).mp
  have hfix : rightConjugateElem z g = z := by
    unfold rightConjugateElem
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc
      g⁻¹ * z * g = g⁻¹ * (z * g) := mul_assoc _ _ _
      _ = g⁻¹ * (g * z) := by rw [hcomm]
      _ = z := inv_mul_cancel_left g z
  exact hfix.symm ▸ h.distinguished_mem

theorem pointClass_inter_eq_subgroupClass {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    involutionPointClass z ∩ (H : Set G) =
      {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t} := by
  ext t
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, (pointClass_conjugate_mem_iff h g).mp hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, (pointClass_conjugate_mem_iff h g).mpr hg⟩

theorem point_normalizer_eq {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) : Subgroup.normalizer (H : Set G) = H := by
  apply le_antisymm
  · intro g hg
    apply H.inv_mem_iff.mp
    apply (h.unique_containment g⁻¹).mp
    have heq := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rw [rightConjugate, Subgroup.conjBy, inv_inv]
    have heq' : H.map (MulAut.conj g).toMonoidHom = H := by
      have hhom : (MulAut.conj g).toMonoidHom = (↑(MulAut.conj g) : G →* G) := by
        ext x
        rfl
      rw [hhom]
      exact heq
    rw [heq']
    exact h.distinguished_mem
  · exact H.le_normalizer

variable [Finite G]

theorem native_strong_embedding_of_order_conditions {M : Subgroup G}
    (h : fusionStronglyEmbedded M) : IsStronglyEmbedded M := by
  refine ⟨h.1, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 2
      (even_iff_two_dvd.mp h.2.1)
    have hxorder : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have hxI := orderOf_eq_prime_iff.mp hxorder
    exact ⟨x, x.property, hxI.2, hxI.1⟩
  · intro g hg x hxM hxconj hxI
    let I : Subgroup G := M ⊓ rightConjugate M g
    have hodd : Odd (Nat.card I) := by
      simpa only [I, rightConjugate, Subgroup.conjBy] using h.2.2 g hg
    let xI : I := ⟨x, hxM, hxconj⟩
    have hxorder : orderOf xI = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime_iff.mpr ⟨hxI.2, hxI.1⟩
    have hdiv : 2 ∣ Nat.card I := hxorder ▸ orderOf_dvd_natCard xI
    have hbad := hodd.of_dvd_nat hdiv
    norm_num at hbad


theorem no_central_involution_of_strong_embedding {M : Subgroup G}
    (hM : IsStronglyEmbedded M) {v : G} (hv : IsInvolution v)
    (hcenter : v ∈ Subgroup.center G) : False := by
  obtain ⟨w, hwM, hw⟩ := hM.exists_involution
  have hvM : v ∈ M := hM.centralizer_le hwM hw
    (Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_center_iff.mp hcenter) w).symm)
  have hcentralizer : Subgroup.centralizer ({v} : Set G) = ⊤ := by
    apply top_unique
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_center_iff.mp hcenter) g)
  exact hM.ne_top (top_unique (hcentralizer ▸ hM.centralizer_le hvM hv))

theorem local_hull_has_no_central_involution {H : Subgroup G} {z u : G}
    (h : InvolutionPointLocalEmbedding H z) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (humem : u ∈ localInvolutionPointHull z u) : False := by
  let L := localInvolutionPointHull z u
  let uL : L := ⟨u, humem⟩
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  have hcenter : uL ∈ Subgroup.center L := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (localInvolutionPointHull_le_centralizer z u a.property)
  exact no_central_involution_of_strong_embedding
    (native_strong_embedding_of_order_conditions (h.local_embedding u hu huz hescape)) (IsInvolution.subtype huI humem) hcenter

theorem involution_point_product_not_mem {H : Subgroup G} {z u : G}
    (h : InvolutionPointLocalEmbedding H z) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    u * z ∉ involutionPointClass z := by
  intro huzclass
  have hzz : z * z = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp h.distinguished_order).1
  have huzmem := mem_localInvolutionPointHull huzclass
    ((Commute.refl u).mul_left huz.symm)
  have hzmem := distinguished_mem_localInvolutionPointHull huz
  have humem : u ∈ localInvolutionPointHull z u := by
    simpa only [mul_assoc, hzz, mul_one] using
      (localInvolutionPointHull z u).mul_mem huzmem hzmem
  exact local_hull_has_no_central_involution h hu huz hescape humem

theorem central_rotation_of_even_involution_product {t s : G}
    (ht : orderOf t = 2) (hs : orderOf s = 2) (heven : Even (orderOf (t * s))) :
    ∃ v : G, orderOf v = 2 ∧ v ∈ Subgroup.zpowers (t * s) ∧
      Commute t v ∧ Commute s v := by
  let r := t * s
  let v := r ^ (orderOf r / 2)
  have hv : orderOf v = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos r)) heven.two_dvd
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have hsinv : s⁻¹ = s := inv_eq_self_of_orderOf_eq_two hs
  have htti : t * t = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht).1
  have htsemi : SemiconjBy t r r⁻¹ := by
    change t * (t * s) = (t * s)⁻¹ * t
    rw [mul_inv_rev, htinv, hsinv, ← mul_assoc, htti, one_mul,
      mul_assoc, htti, mul_one]
  have hssemi : SemiconjBy s r r⁻¹ := by
    change s * (t * s) = (t * s)⁻¹ * s
    simp only [mul_inv_rev, htinv, hsinv, mul_assoc]
  have hvinv : v⁻¹ = v := inv_eq_self_of_orderOf_eq_two hv
  refine ⟨v, hv, Subgroup.pow_mem _ (Subgroup.mem_zpowers r) _, ?_, ?_⟩
  · have hpow := htsemi.pow_right (orderOf r / 2)
    rw [inv_pow] at hpow
    change SemiconjBy t v v⁻¹ at hpow
    change t * v = v * t
    simpa only [hvinv] using hpow.eq
  · have hpow := hssemi.pow_right (orderOf r / 2)
    rw [inv_pow] at hpow
    change SemiconjBy s v v⁻¹ at hpow
    change s * v = v * s
    simpa only [hvinv] using hpow.eq

theorem pointClass_mem_of_even_product_order {H : Subgroup G} {z t : G}
    (h : InvolutionPointLocalEmbedding H z) (ht : t ∈ involutionPointClass z)
    (heven : Even (orderOf (t * z))) : t ∈ H := by
  obtain ⟨v, hv, hvpow, htv, hzv⟩ := central_rotation_of_even_involution_product
    (order_two_of_mem_pointClass h.distinguished_order ht) h.distinguished_order heven
  by_cases hcentralizer : Subgroup.centralizer ({v} : Set G) ≤ H
  · exact hcentralizer (Subgroup.mem_centralizer_singleton_iff.mpr htv)
  · have htL := mem_localInvolutionPointHull ht htv
    have hzL := distinguished_mem_localInvolutionPointHull hzv.symm
    have hrL := (localInvolutionPointHull z v).mul_mem htL hzL
    have hvL := (Subgroup.zpowers_le.mpr hrL) hvpow
    exact False.elim (local_hull_has_no_central_involution h hv hzv.symm hcentralizer hvL)

omit [Finite G] in
theorem inversion_eq_self_of_odd_order {r x : G} (hodd : Odd (orderOf r))
    (hinv : SemiconjBy r x x⁻¹) : x = x⁻¹ := by
  obtain ⟨k, hk⟩ := hodd
  have hsquare : Commute (r ^ 2) x := by
    change r ^ 2 * x = x * r ^ 2
    simpa only [pow_two, inv_inv] using (hinv.inv_right.mul_left hinv).eq
  have hlast : SemiconjBy (r ^ (2 * k + 1)) x x⁻¹ := by
    rw [pow_succ, pow_mul]
    have hcomm : r * (r ^ 2) ^ k = (r ^ 2) ^ k * r :=
      (Commute.self_pow r 2).pow_right k |>.eq
    rw [← hcomm]
    exact hinv.mul_left (hsquare.pow_left k).semiconjBy
  rw [← hk, pow_orderOf_eq_one] at hlast
  simpa only [one_mul, mul_one] using hlast.eq

theorem pointClass_factors_mem_of_product_centralizing {H : Subgroup G} {z t s : G}
    (h : InvolutionPointLocalEmbedding H z) (ht : t ∈ involutionPointClass z)
    (hs : s ∈ involutionPointClass z) (hne : t * s ≠ 1)
    (hcentral : Commute (t * s) z) : t ∈ H ∧ s ∈ H := by
  have htorder := order_two_of_mem_pointClass h.distinguished_order ht
  have hsorder := order_two_of_mem_pointClass h.distinguished_order hs
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two htorder
  have hsinv : s⁻¹ = s := inv_eq_self_of_orderOf_eq_two hsorder
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp htorder).1
  have hxH : t * s ∈ H := point_centralizer_le h
    (Subgroup.mem_centralizer_singleton_iff.mpr hcentral)
  have htH : t ∈ H := by
    by_contra htH
    have hxodd : Odd (orderOf (t * s)) := by
      apply Nat.not_even_iff_odd.mp
      intro heven
      obtain ⟨v, hv, hvpow, htv, hsv⟩ :=
        central_rotation_of_even_involution_product htorder hsorder heven
      have hzv : Commute z v := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hvpow
        exact hn ▸ hcentral.symm.zpow_right n
      have hescape : ¬ Subgroup.centralizer ({v} : Set G) ≤ H := by
        intro hle
        exact htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr htv))
      have htL := mem_localInvolutionPointHull ht htv
      have hsL := mem_localInvolutionPointHull hs hsv
      have hvL := (Subgroup.zpowers_le.mpr
        ((localInvolutionPointHull z v).mul_mem htL hsL)) hvpow
      exact local_hull_has_no_central_involution h hv hzv.symm hescape hvL
    have hxnotinv : t * s ≠ (t * s)⁻¹ := by
      intro hxinv
      have hxsquare : (t * s) ^ 2 = 1 := by
        rw [pow_two]
        calc
          (t * s) * (t * s) = (t * s)⁻¹ * (t * s) := by rw [← hxinv]
          _ = 1 := inv_mul_cancel _
      rcases (Nat.dvd_prime Nat.prime_two).mp
          (orderOf_dvd_iff_pow_eq_one.mpr hxsquare) with horder | horder
      · exact hne (orderOf_eq_one_iff.mp horder)
      · rw [horder] at hxodd
        norm_num at hxodd
    have htinverts : SemiconjBy t (t * s) (t * s)⁻¹ := by
      change t * (t * s) = (t * s)⁻¹ * t
      rw [mul_inv_rev, htinv, hsinv, ← mul_assoc, htt, one_mul,
        mul_assoc, htt, mul_one]
    have hrinverts : SemiconjBy (t * z) (t * s) (t * s)⁻¹ :=
      htinverts.mul_left hcentral.symm.semiconjBy
    have hreven : Even (orderOf (t * z)) := by
      apply Nat.not_odd_iff_even.mp
      intro hrodd
      exact hxnotinv (inversion_eq_self_of_odd_order hrodd hrinverts)
    exact htH (pointClass_mem_of_even_product_order h ht hreven)
  refine ⟨htH, ?_⟩
  have hprod := H.mul_mem htH hxH
  simpa only [← mul_assoc, htt, one_mul] using hprod

theorem involution_point_product_confinement {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    (∀ u : G, orderOf u = 2 → Commute u z →
      ¬ Subgroup.centralizer ({u} : Set G) ≤ H → u * z ∉ involutionPointClass z) ∧
    (∀ t ∈ involutionPointClass z, Even (orderOf (t * z)) → t ∈ H) ∧
    (∀ t ∈ involutionPointClass z, ∀ s ∈ involutionPointClass z,
      t * s ≠ 1 → Commute (t * s) z → t ∈ H ∧ s ∈ H) :=
  ⟨fun _ hu huz hescape => involution_point_product_not_mem h hu huz hescape,
    fun _ ht heven => pointClass_mem_of_even_product_order h ht heven,
    fun _ ht _ hs hne hcentral =>
      pointClass_factors_mem_of_product_centralizing h ht hs hne hcentral⟩

omit [Finite G] in
theorem pointClass_eq_conjAct_orbit (z : G) :
    involutionPointClass z = MulAction.orbit (ConjAct G) z := by
  ext t
  rw [ConjAct.mem_orbit_conjAct, isConj_comm, isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [rightConjugateElem, inv_inv]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [rightConjugateElem, inv_inv]⟩
theorem pointClass_card_mul_centralizer (z : G) :
    Nat.card (involutionPointClass z) *
      Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card G := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (ConjAct G) := Fintype.ofFinite _
  let : Fintype (MulAction.orbit (ConjAct G) z) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer (ConjAct G) z) := Fintype.ofFinite _
  have hcard := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) z
  have hstab : Nat.card (MulAction.stabilizer (ConjAct G) z) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    rw [Subgroup.centralizer_eq_comap_stabilizer z]
    let S := MulAction.stabilizer (ConjAct G) z
    let f : G →* ConjAct G := ConjAct.toConjAct.toMonoidHom
    have e : S.comap f ≃ S :=
      { toFun := fun a => ⟨f a, a.property⟩
        invFun := fun a => ⟨ConjAct.ofConjAct a, by
          change ConjAct.toConjAct (ConjAct.ofConjAct a.val) ∈ S
          simpa only [ConjAct.toConjAct_ofConjAct] using a.property⟩
        left_inv := fun a => Subtype.ext (ConjAct.ofConjAct_toConjAct a.val)
        right_inv := fun a => Subtype.ext (ConjAct.toConjAct_ofConjAct a.val) }
    exact Nat.card_congr e.symm
  simp only [← Nat.card_eq_fintype_card] at hcard
  rw [← pointClass_eq_conjAct_orbit z, hstab] at hcard
  exact hcard.trans (Nat.card_congr ConjAct.ofConjAct.toEquiv)
theorem pointClass_card_factorization {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    Nat.card (involutionPointClass z) = H.index *
      Nat.card {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t} := by
  let zH : H := ⟨z, h.distinguished_mem⟩
  have hclass : Nat.card (involutionPointClass zH) =
      Nat.card {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t} := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun t : involutionPointClass zH =>
      (⟨(t.val : G), ?_⟩ : {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t})) ?_
    · obtain ⟨g, hg⟩ := t.property
      refine ⟨g, g.property, ?_⟩
      exact congrArg Subtype.val hg
    · constructor
      · intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun a : {t : G | ∃ g : G, g ∈ H ∧
          rightConjugateElem z g = t} => (a : G)) hab
      · rintro ⟨t, ⟨g, hg, hgt⟩⟩
        let gH : H := ⟨g, hg⟩
        refine ⟨⟨rightConjugateElem zH gH, ⟨gH, rfl⟩⟩, ?_⟩
        exact Subtype.ext hgt
  have hcentralizer : Nat.card (Subgroup.centralizer ({zH} : Set H)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    have heq : (Subgroup.centralizer ({zH} : Set H)).map H.subtype =
        Subgroup.centralizer ({z} : Set G) := by
      ext g
      constructor
      · rintro ⟨gH, hgH, rfl⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hgH)
      · intro hg
        let gH : H := ⟨g, point_centralizer_le h hg⟩
        refine ⟨gH, ?_, rfl⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)
    rw [← heq, Subgroup.card_map_of_injective H.subtype_injective]
  have hsmall := pointClass_card_mul_centralizer zH
  rw [hclass, hcentralizer] at hsmall
  have hbig := pointClass_card_mul_centralizer z
  apply Nat.mul_right_cancel (Nat.card_pos (α := Subgroup.centralizer ({z} : Set G)))
  calc
    Nat.card (involutionPointClass z) * Nat.card (Subgroup.centralizer ({z} : Set G)) =
        Nat.card G := hbig
    _ = H.index * Nat.card H := H.index_mul_card.symm
    _ = (H.index * Nat.card {t : G | ∃ g : G, g ∈ H ∧
        rightConjugateElem z g = t}) * Nat.card (Subgroup.centralizer ({z} : Set G)) := by
          rw [mul_assoc, hsmall]
omit [Finite G] in
theorem point_fixed_coset_unique {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    ∀ omega : conjugateCosetSpace H,
      z • omega = omega ↔ omega = (QuotientGroup.mk 1 : conjugateCosetSpace H) := by
  intro omega
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective omega
  rw [fixed_coset_iff_mem_rightConjugate, h.unique_containment]
  rw [QuotientGroup.eq]
  simp only [mul_one]
omit [Finite G] in
theorem pointClass_fixed_coset_unique {H : Subgroup G} {z t : G}
    (h : InvolutionPointLocalEmbedding H z) (ht : t ∈ involutionPointClass z) :
    ∃! omega : conjugateCosetSpace H, t • omega = omega := by
  obtain ⟨g, rfl⟩ := ht
  let base : conjugateCosetSpace H := QuotientGroup.mk 1
  have hfix : z • base = base := (point_fixed_coset_unique h base).mpr rfl
  refine ⟨g⁻¹ • base, ?_, ?_⟩
  · change (g⁻¹ * z * g) • (g⁻¹ • base) = g⁻¹ • base
    simp only [mul_smul, smul_inv_smul, hfix]
  · intro omega homega
    have hfixed : z • (g • omega) = g • omega := by
      have hh := congrArg (fun w : conjugateCosetSpace H => g • w) homega
      simpa only [rightConjugateElem, ← mul_smul, mul_assoc,
        mul_inv_cancel_left] using hh
    have heq := (point_fixed_coset_unique h (g • omega)).mp hfixed
    have hh := congrArg (fun w : conjugateCosetSpace H => g⁻¹ • w) heq
    simpa only [inv_smul_smul] using hh

end CFSG.ShultStronglyClosedTI
