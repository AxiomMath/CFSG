module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem point_unique_containment_iff {H : Subgroup G} {z : G} (hz : z ∈ H) :
    (∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) ↔
    Subgroup.centralizer ({z} : Set G) ≤ H ∧
      involutionPointClass z ∩ (H : Set G) =
        {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t} := by
  constructor
  · intro huniq
    have hmem (g : G) : rightConjugateElem z g ∈ H ↔ g ∈ H := by
      constructor
      · intro hzg
        have hzright : z ∈ rightConjugate H g⁻¹ := by
          have hz' := rightConjugateElem_mem_rightConjugate (g := g⁻¹) hzg
          simpa [rightConjugateElem, mul_assoc] using hz'
        exact H.inv_mem_iff.mp ((huniq g⁻¹).mp hzright)
      · intro hg
        exact H.mul_mem (H.mul_mem (H.inv_mem hg) hz) hg
    refine ⟨?_, ?_⟩
    · intro g hg
      apply (hmem g).mp
      have hfix : rightConjugateElem z g = z := by
        unfold rightConjugateElem
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
        calc
          g⁻¹ * z * g = g⁻¹ * (z * g) := mul_assoc _ _ _
          _ = g⁻¹ * (g * z) := by rw [hcomm]
          _ = z := inv_mul_cancel_left g z
      exact hfix.symm ▸ hz
    · ext t
      constructor
      · rintro ⟨⟨g, rfl⟩, hzg⟩
        exact ⟨g, (hmem g).mp hzg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, rfl⟩, (hmem g).mpr hg⟩
  · rintro ⟨hcentral, hclass⟩ g
    constructor
    · intro hzright
      have hzg : rightConjugateElem z g⁻¹ ∈ H := by
        apply rightConjugateElem_mem_of_mem_rightConjugate (g := g⁻¹)
        simpa only [inv_inv] using hzright
      have hzgclass : rightConjugateElem z g⁻¹ ∈ involutionPointClass z ∩ (H : Set G) :=
        ⟨⟨g⁻¹, rfl⟩, hzg⟩
      rw [hclass] at hzgclass
      obtain ⟨a, ha, heq⟩ := hzgclass
      have hfix : rightConjugateElem z (a * g) = z := by
        calc
          rightConjugateElem z (a * g) =
              rightConjugateElem (rightConjugateElem z a) g := by
                simp [rightConjugateElem, mul_assoc]
          _ = rightConjugateElem (rightConjugateElem z g⁻¹) g := by rw [heq]
          _ = z := by simp [rightConjugateElem, mul_assoc]
      have hag : a * g ∈ Subgroup.centralizer ({z} : Set G) := by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hh := congrArg (fun t : G => (a * g) * t) hfix
        simpa only [rightConjugateElem, mul_assoc, mul_inv_cancel_left] using hh.symm
      have hh := H.mul_mem (H.inv_mem ha) (hcentral hag)
      simpa only [inv_mul_cancel_left] using hh
    · intro hg
      have hz' : rightConjugateElem z g⁻¹ ∈ H := by
        simpa only [rightConjugateElem, inv_inv] using
          H.mul_mem (H.mul_mem hg hz) (H.inv_mem hg)
      have hzright := rightConjugateElem_mem_rightConjugate (g := g) hz'
      simpa [rightConjugateElem, mul_assoc] using hzright
abbrev pointRightCosetSpace (H : Subgroup G) :=
  Quotient (QuotientGroup.rightRel H)

@[expose] def pointRightCosetMul (H : Subgroup G)
    (omega : pointRightCosetSpace H) (g : G) : pointRightCosetSpace H :=
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  e.symm (g⁻¹ • e omega)

theorem pointRightCosetMul_mk (H : Subgroup G) (x g : G) :
    pointRightCosetMul H (Quotient.mk (QuotientGroup.rightRel H) x) g = Quotient.mk (QuotientGroup.rightRel H) (x * g) := by
  change Quotient.mk (QuotientGroup.rightRel H) ((g⁻¹ * x⁻¹)⁻¹) = Quotient.mk (QuotientGroup.rightRel H) (x * g)
  simp only [mul_inv_rev, inv_inv]

theorem pointRightCosetMul_one (H : Subgroup G) (omega : pointRightCosetSpace H) :
    pointRightCosetMul H omega 1 = omega := by
  refine Quotient.inductionOn omega ?_
  intro x
  rw [pointRightCosetMul_mk, mul_one]

theorem pointRightCosetMul_mul (H : Subgroup G) (omega : pointRightCosetSpace H)
    (g k : G) :
    pointRightCosetMul H (pointRightCosetMul H omega g) k =
      pointRightCosetMul H omega (g * k) := by
  refine Quotient.inductionOn omega ?_
  intro x
  simp only [pointRightCosetMul_mk, mul_assoc]

variable [Finite G]
theorem involution_point_unique_containment_action {H : Subgroup G} {z : G}
    (hz : z ∈ H) (horder : orderOf z = 2) :
    ((∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) ↔
      Subgroup.centralizer ({z} : Set G) ≤ H ∧
        involutionPointClass z ∩ (H : Set G) =
          {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t}) ∧
    ((∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) →
      Subgroup.normalizer (H : Set G) = H ∧
      (∀ t ∈ involutionPointClass z, ∃! omega : pointRightCosetSpace H,
        pointRightCosetMul H omega t = omega) ∧
      (∀ omega : pointRightCosetSpace H,
        pointRightCosetMul H omega z = omega ↔ omega = Quotient.mk (QuotientGroup.rightRel H) 1) ∧
      Nat.card (involutionPointClass z) = H.index *
        Nat.card {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t}) := by
  refine ⟨point_unique_containment_iff hz, ?_⟩
  intro huniq
  have hnormalizer : Subgroup.normalizer (H : Set G) = H := by
    apply le_antisymm
    · intro g hg
      apply H.inv_mem_iff.mp
      apply (huniq g⁻¹).mp
      have heq := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      rw [rightConjugate, Subgroup.conjBy, inv_inv]
      have heq' : H.map (MulAut.conj g).toMonoidHom = H := by
        have hh : (MulAut.conj g).toMonoidHom = (↑(MulAut.conj g) : G →* G) := by
          ext x
          rfl
        rw [hh]
        exact heq
      rw [heq']
      exact hz
    · exact H.le_normalizer
  have hfixed : ∀ omega : conjugateCosetSpace H,
      z • omega = omega ↔ omega = (QuotientGroup.mk 1 : conjugateCosetSpace H) := by
    intro omega
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective omega
    rw [fixed_coset_iff_mem_rightConjugate, huniq, QuotientGroup.eq]
    simp only [mul_one]
  have hclassfix : ∀ t ∈ involutionPointClass z, ∃! omega : conjugateCosetSpace H,
      t • omega = omega := by
    intro t ht
    obtain ⟨g, rfl⟩ := ht
    let base : conjugateCosetSpace H := QuotientGroup.mk 1
    have hfix : z • base = base := (hfixed base).mpr rfl
    refine ⟨g⁻¹ • base, ?_, ?_⟩
    · change (g⁻¹ * z * g) • (g⁻¹ • base) = g⁻¹ • base
      simp only [mul_smul, smul_inv_smul, hfix]
    · intro omega homega
      have hf : z • (g • omega) = g • omega := by
        have hh := congrArg (fun w : conjugateCosetSpace H => g • w) homega
        simpa only [rightConjugateElem, ← mul_smul, mul_assoc,
          mul_inv_cancel_left] using hh
      have hh := congrArg (fun w : conjugateCosetSpace H => g⁻¹ • w) ((hfixed (g • omega)).mp hf)
      simpa only [inv_smul_smul] using hh
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  have hbase : e (Quotient.mk (QuotientGroup.rightRel H) 1) =
      (QuotientGroup.mk 1 : conjugateCosetSpace H) := by
    change QuotientGroup.mk (1 : G)⁻¹ = QuotientGroup.mk 1
    rw [inv_one]
  have hrightfix (t : G) (htorder : orderOf t = 2) (omega : pointRightCosetSpace H) :
      pointRightCosetMul H omega t = omega ↔ t • e omega = e omega := by
    change e.symm (t⁻¹ • e omega) = omega ↔ t • e omega = e omega
    rw [Equiv.symm_apply_eq, inv_eq_self_of_orderOf_eq_two htorder]
  have hrightclassfix : ∀ t ∈ involutionPointClass z,
      ∃! omega : pointRightCosetSpace H, pointRightCosetMul H omega t = omega := by
    intro t ht
    have htorder := order_two_of_mem_pointClass horder ht
    obtain ⟨omega, homega, huniqomega⟩ := hclassfix t ht
    refine ⟨e.symm omega, (hrightfix t htorder _).mpr ?_, ?_⟩
    · simpa only [e.apply_symm_apply] using homega
    · intro point hpoint
      apply e.injective
      simpa only [e.apply_symm_apply] using
        huniqomega (e point) ((hrightfix t htorder point).mp hpoint)
  have hrightbase : ∀ omega : pointRightCosetSpace H,
      pointRightCosetMul H omega z = omega ↔ omega = Quotient.mk (QuotientGroup.rightRel H) 1 := by
    intro omega
    rw [hrightfix z horder omega, hfixed]
    exact ⟨fun hpoint => e.injective (hpoint.trans hbase.symm),
      fun hpoint => hpoint ▸ hbase⟩
  refine ⟨hnormalizer, hrightclassfix, hrightbase, ?_⟩
  let zH : H := ⟨z, hz⟩
  have hclass : Nat.card (involutionPointClass zH) =
      Nat.card {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t} := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun t : involutionPointClass zH =>
      (⟨(t.val : G), ?_⟩ : {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t})) ?_
    · obtain ⟨g, hg⟩ := t.property
      exact ⟨g, g.property, congrArg Subtype.val hg⟩
    · constructor
      · intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun a : {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t} => (a : G)) hab
      · rintro ⟨t, ⟨g, hg, hgt⟩⟩
        let gH : H := ⟨g, hg⟩
        exact ⟨⟨rightConjugateElem zH gH, ⟨gH, rfl⟩⟩, Subtype.ext hgt⟩
  have hcentral := ((point_unique_containment_iff hz).mp huniq).1
  have hcentercard : Nat.card (Subgroup.centralizer ({zH} : Set H)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    have heq : (Subgroup.centralizer ({zH} : Set H)).map H.subtype =
        Subgroup.centralizer ({z} : Set G) := by
      ext g
      constructor
      · rintro ⟨gH, hgH, rfl⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hgH)
      · intro hg
        let gH : H := ⟨g, hcentral hg⟩
        exact ⟨gH, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)), rfl⟩
    rw [← heq, Subgroup.card_map_of_injective H.subtype_injective]
  have hsmall := pointClass_card_mul_centralizer zH
  rw [hclass, hcentercard] at hsmall
  apply Nat.mul_right_cancel (Nat.card_pos (α := Subgroup.centralizer ({z} : Set G)))
  calc
    Nat.card (involutionPointClass z) * Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card G :=
      pointClass_card_mul_centralizer z
    _ = H.index * Nat.card H := H.index_mul_card.symm
    _ = (H.index * Nat.card {t : G | ∃ g : G, g ∈ H ∧
        rightConjugateElem z g = t}) * Nat.card (Subgroup.centralizer ({z} : Set G)) := by
          rw [mul_assoc, hsmall]

theorem order_strong_embedding_of_native {Y : Type*} [Group Y] [Finite Y]
    {M : Subgroup Y} (hM : IsStronglyEmbedded M) : fusionStronglyEmbedded M := by
  refine ⟨hM.ne_top, hM.card_even, ?_⟩
  intro g hg
  let I : Subgroup Y := M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 (even_iff_two_dvd.mp heven)
  have hxorder : orderOf (x : Y) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hxI := orderOf_eq_prime_iff.mp hxorder
  have hxconj : (x : Y) ∈ rightConjugate M g := x.property.2
  exact hg (hM.mem_of_involution_mem_rightConjugate x.property.1 hxconj ⟨hxI.2, hxI.1⟩)
theorem local_datum_subgroup_inheritance {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (A : Subgroup G)
    (hzA : z ∈ A) (hescapeA : ¬ A ≤ H) :
    InvolutionPointLocalEmbedding (H.subgroupOf A) (⟨z, hzA⟩ : A) := by
  let zA : A := ⟨z, hzA⟩
  refine ⟨?_, h.distinguished_mem, ?_, ?_, ?_⟩
  · intro htop
    apply hescapeA
    intro a ha
    have hamem : (⟨a, ha⟩ : A) ∈ H.subgroupOf A := by rw [htop]; exact Subgroup.mem_top _
    exact hamem
  · exact (Subgroup.orderOf_coe zA).symm.trans h.distinguished_order
  · intro a
    have heq : zA ∈ rightConjugate (H.subgroupOf A) a ↔
        z ∈ rightConjugate H (a : G) := by
      rw [rightConjugate, Subgroup.conjBy, rightConjugate, Subgroup.conjBy]
      simp only [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
      rfl
    rw [heq, h.unique_containment]
    rfl
  · intro u hu huz hescape
    let v : G := u
    have huG : orderOf v = 2 := (Subgroup.orderOf_coe u).trans hu
    have huzG : Commute v z := by
      change v * z = z * v
      exact congrArg Subtype.val huz.eq
    have hescapeG : ¬ Subgroup.centralizer ({v} : Set G) ≤ H := by
      intro hle
      apply hescape
      intro a ha
      exact hle (Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ha)))
    let L := localInvolutionPointHull z v
    let V := localInvolutionPointHull zA u
    have hVL : V.map A.subtype ≤ L := by
      change (Subgroup.closure _).map A.subtype ≤ L
      rw [MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨a, ⟨ha, hac⟩, rfl⟩
      obtain ⟨g, hg⟩ := ha
      exact mem_localInvolutionPointHull
        ⟨g, congrArg Subtype.val hg⟩
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hac))
    let f : V →* L :=
      { toFun := fun a => ⟨a.val.val, hVL (Subgroup.mem_map_of_mem A.subtype a.property)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : L => (a : G)) hab
    have hzV : zA ∈ V := distinguished_mem_localInvolutionPointHull huz
    have hproper : (H.subgroupOf L).comap f ≠ ⊤ := by
      intro htop
      have hall : ∀ a : A, a ∈ Subgroup.centralizer ({u} : Set A) → a ∈ H.subgroupOf A := by
        intro a ha
        have hza : rightConjugateElem zA a ∈ V :=
          mem_localInvolutionPointHull ⟨a, rfl⟩ ?_
        · have hmem : (⟨rightConjugateElem zA a, hza⟩ : V) ∈ (H.subgroupOf L).comap f := by
            rw [htop]; exact Subgroup.mem_top _
          have hmemG : rightConjugateElem z (a : G) ∈ H := hmem
          exact (pointClass_conjugate_mem_iff h a).mp hmemG
        · have hau : Commute a u := Subgroup.mem_centralizer_singleton_iff.mp ha
          exact (hau.inv_left.mul_left huz.symm).mul_left hau
      exact hescape hall
    have hnative := (native_strong_embedding_of_order_conditions
      (h.local_embedding v huG huzG hescapeG)).comap_of_injective f hf hproper
      ⟨⟨zA, hzV⟩, h.distinguished_mem,
        IsInvolution.subtype (IsInvolution.subtype
          ⟨(orderOf_eq_prime_iff.mp h.distinguished_order).2,
            (orderOf_eq_prime_iff.mp h.distinguished_order).1⟩ hzA) hzV⟩
    have heq : (H.subgroupOf L).comap f = (H.subgroupOf A).subgroupOf V := by
      ext a
      rfl
    rw [heq] at hnative
    exact order_strong_embedding_of_native hnative

end CFSG.ShultStronglyClosedTI
