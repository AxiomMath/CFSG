module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma34Local
public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian

import CFSG.RankThree.GF2n.Parrott.Section4Lemma41
import CFSG.RankThree.GF2n.Parrott.SylowH
import CFSG.RankThree.GF2n.Parrott.QA45SylowFacts
import CFSG.GroupTheory.PCore.Transport
import CFSG.LocalAnalysis.UniquenessCase.UC6Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem lemma34_exists_isSylowOf_ge {P K : Subgroup G} (hPK : P ≤ K)
    (hP : IsPGroup 2 P) : ∃ T : Subgroup G, IsSylowOf 2 T K ∧ P ≤ T := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

private theorem lemma34_isPGroup_sup_J (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E) : IsPGroup 2 (J z ⊔ E : Subgroup G) := by
  have h1 := Subgroup.relIndex_mul_card E (J z ⊔ E)
  rw [inf_eq_left.mpr (le_sup_right : E ≤ J z ⊔ E), relIndex_sup_J_of_isParrottE h hE,
    hE.2.2.2.2.1] at h1
  exact IsPGroup.of_card (n := 14) (by rw [← h1]; norm_num)

section Perm

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem lemma34_mem_sup_J_iff_qH (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E) (x : ↥(H z)) :
    (x : G) ∈ J z ⊔ E ↔ qH D x ∈ imageQA45 D hE.1 := by
  have hJN := J_le_normalizer_of_isParrottE h hE
  constructor
  · intro hx
    obtain ⟨j, hj, e, he, hxe⟩ := lemma34_exists_mul_of_mem_sup hJN hx
    refine (mem_imageQA45_iff D hE.1 _).mpr ⟨e, he, ?_⟩
    have hjJ : qH D ⟨j, J_le_H hj⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj)
    have : x = ⟨j, J_le_H hj⟩ * ⟨e, hE.1 he⟩ := Subtype.ext hxe
    rw [this, map_mul, hjJ, one_mul]
  · intro hx
    obtain ⟨k, hk, hkx⟩ := (mem_imageQA45_iff D hE.1 _).mp hx
    have h1 : qH D (x * ⟨k, hE.1 hk⟩⁻¹) = 1 := by rw [map_mul, map_inv, hkx, mul_inv_cancel]
    have h2 : (x : G) * k⁻¹ ∈ J z := Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
    have h3 : (x : G) = ((x : G) * k⁻¹) * k := by group
    rw [h3]
    exact Subgroup.mul_mem_sup h2 hk

private theorem lemma34_qH_mem_normalizer (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E) {m : G} (hm : m ∈ Subgroup.normalizer (E : Set G) ⊓ H z) :
    qH D ⟨m, hm.2⟩ ∈ Subgroup.normalizer (imageQA45 D hE.1 : Set QA45.originalSubgroup) := by
  have hJn : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer J_le_H).mp (J_subgroupOf_normal z)
  have hmN : m ∈ Subgroup.normalizer ((J z ⊔ E : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup (J z) E ⟨hJn hm.2, hm.1⟩
  rw [Subgroup.mem_normalizer_iff]
  intro k
  obtain ⟨x, rfl⟩ := qH_surjective D k
  have e : qH D ⟨m, hm.2⟩ * qH D x * (qH D ⟨m, hm.2⟩)⁻¹ = qH D (⟨m, hm.2⟩ * x * ⟨m, hm.2⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [e, ← lemma34_mem_sup_J_iff_qH D h hE, ← lemma34_mem_sup_J_iff_qH D h hE]
  exact Subgroup.mem_normalizer_iff.mp hmN x

theorem lemma34_exists_qH_eq_of_mem_normalizer (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E)
    (hweak : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
      ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E)
    {a : QA45.originalSubgroup}
    (ha : a ∈ Subgroup.normalizer (imageQA45 D hE.1 : Set QA45.originalSubgroup)) :
    ∃ m : ↥(Subgroup.normalizer (E : Set G) ⊓ H z), qH D ⟨m, m.2.2⟩ = a := by
  obtain ⟨g, rfl⟩ := qH_surjective D a
  obtain ⟨T, hT, hPT⟩ := lemma34_exists_isSylowOf_ge (sup_le J_le_H hE.1)
    (lemma34_isPGroup_sup_J h hE)
  have hEJ : ∀ e ∈ E, (g : G) * e * (g : G)⁻¹ ∈ J z ⊔ E := by
    intro e he
    have heH : e ∈ H z := hE.1 he
    have h1 := (lemma34_mem_sup_J_iff_qH D h hE (g * ⟨e, heH⟩ * g⁻¹)).mpr (by
      have e1 : qH D (g * ⟨e, heH⟩ * g⁻¹) = qH D g * qH D ⟨e, heH⟩ * (qH D g)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [e1]
      exact (Subgroup.mem_normalizer_iff.mp ha _).mp
        ((mem_imageQA45_iff D hE.1 _).mpr ⟨e, he, rfl⟩))
    exact h1
  have hconj : CFSG.conjugate E (g : G)⁻¹ ≤ T := by
    rintro y ⟨e, he, rfl⟩
    have h1 := hPT (hEJ e he)
    simpa [MulAut.conj_apply] using h1
  have hEq := hweak T hT (le_trans le_sup_right hPT) (g : G)⁻¹ hconj
  have hgN : (g : G) ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [CFSG.conjugate] using hEq
  exact ⟨⟨g, hgN, g.2⟩, rfl⟩

end Perm

section PermFive

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup

theorem lemma34_exists_conj_sQA45 {E : Subgroup G} (hE : IsParrottE z E) :
    ∃ c : A45, ∀ s : A45, s ∈ sQA45 ↔ c⁻¹ * s * c ∈ imageQA45 D hE.1 := by
  have hEbar_ab : IsElemAbelian 2 (imageQA45 D hE.1) :=
    isElemAbelian_imageQA45 D hE.1 hE.2.2.2.1
  have hEbar_card : Nat.card (imageQA45 D hE.1) = 16 := by
    have h1 := card_eq_card_inf_J_mul_card_imageQA45 D hE.1
    generalize imageQA45 D hE.1 = Eb at h1 ⊢
    rw [hE.2.2.2.2.1, hE.2.2.2.2.2.1] at h1
    omega
  have hEbar_Q := imageQA45_le_Q D hE.1 hE.2.1
  obtain ⟨c, hc⟩ := (qa45_elemAbelian_sixteen).2 _ hEbar_ab hEbar_card hEbar_Q
  refine ⟨c, fun s => ?_⟩
  rw [← hc]
  constructor
  · rintro ⟨e, he, rfl⟩
    show c⁻¹ * (c * e * c⁻¹) * c ∈ _
    have : c⁻¹ * (c * e * c⁻¹) * c = e := by group
    rwa [this]
  · intro hs
    refine ⟨_, hs, ?_⟩
    show c * (c⁻¹ * s * c) * c⁻¹ = s
    group

include D

theorem exists_perm_five_of_isParrottE (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E)
    (hweak : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
      ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) :
    ∃ π : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) →* Equiv.Perm (Fin 5),
      Function.Surjective π ∧
        π.ker = (J z ⊔ E).subgroupOf (Subgroup.normalizer (E : Set G) ⊓ H z) := by
  classical
  obtain ⟨c, hS⟩ := lemma34_exists_conj_sQA45 D hE
  obtain ⟨hNorm, ⟨e⟩⟩ := qa45_normalizer_sQA45.2.2.1
  have := hNorm
  let φ : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) →* A45 :=
    (qH D).comp (Subgroup.inclusion inf_le_right)
  have hθ₀N : ∀ m : ↥(Subgroup.normalizer (E : Set G) ⊓ H z),
      (MulAut.conj c).toMonoidHom (φ m) ∈ Subgroup.normalizer (sQA45 : Set A45) := fun m =>
    (lemma34_mem_normalizer_conj_iff hS).mp (lemma34_qH_mem_normalizer D h hE m.2)
  let θ : ↥(Subgroup.normalizer (E : Set G) ⊓ H z) →* ↥(Subgroup.normalizer (sQA45 : Set A45)) :=
    ((MulAut.conj c).toMonoidHom.comp φ).codRestrict _ hθ₀N
  have hθs : Function.Surjective θ := by
    rintro ⟨s, hs⟩
    have ha : c⁻¹ * s * c ∈ Subgroup.normalizer (imageQA45 D hE.1 : Set A45) := by
      refine (lemma34_mem_normalizer_conj_iff hS).mpr ?_
      have : c * (c⁻¹ * s * c) * c⁻¹ = s := by group
      rwa [this]
    obtain ⟨m, hm⟩ := lemma34_exists_qH_eq_of_mem_normalizer D h hE hweak ha
    refine ⟨m, Subtype.ext ?_⟩
    show c * φ m * c⁻¹ = s
    have hφm : φ m = c⁻¹ * s * c := hm
    rw [hφm]
    group
  refine ⟨e.toMonoidHom.comp ((QuotientGroup.mk' (sQA45.subgroupOf _)).comp θ), ?_, ?_⟩
  · exact e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hθs)
  · ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show e (QuotientGroup.mk (θ m)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show c * φ m * c⁻¹ ∈ sQA45 ↔ _
    rw [hS]
    have : c⁻¹ * (c * φ m * c⁻¹) * c = φ m := by group
    rw [this]
    exact (lemma34_mem_sup_J_iff_qH D h hE ⟨m, m.2.2⟩).symm

omit D

end PermFive

section OddFive

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

include D

theorem odd_relIndex_of_isParrottE (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {E : Subgroup G} (hE : IsParrottE z E) :
    Odd ((Subgroup.normalizer (E : Set G) ⊓ H z).relIndex (Subgroup.normalizer (E : Set G))) := by
  classical
  have hMcard := lemma34_card_normalizer_inf_H hE
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (Subgroup.normalizer (E : Set G) ⊓ H z)
  have hfacM : (Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓ H z)).factorization 2 = 17 := by
    rw [hMcard, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]
    simp
  have hPcard : Nat.card P = 2 ^ 17 := by rw [hP.card_eq, hfacM]
  have hfacH : (Nat.card ↥(H z)).factorization 2 = 17 := by
    obtain ⟨S, hS⟩ := isSylow_sylowTwoH D h
    have h1 := S.card_eq_multiplicity
    have h2 : Nat.card (S : Subgroup ↥(H z)) = 2 ^ 17 := by
      rw [hS]
      exact card_sylowTwoH D h
    exact Nat.pow_right_injective le_rfl (h1.symm.trans h2)
  have hPH : IsSylowOf 2 P (H z) :=
    isSylowOf_of_card (hP.le.trans inf_le_right) (by rw [hPcard, hfacH])
  have hPtop : IsSylowOf 2 P ⊤ := isSylowOf_top_of_isSylowOf_H h hZ P hPH
  have hPN : IsSylowOf 2 P (Subgroup.normalizer (E : Set G)) :=
    hPtop.of_le (hP.le.trans inf_le_left) le_top
  rw [isSylowOf_iff] at hPN
  obtain ⟨-, -, hPN3⟩ := hPN
  have hdvd : (Subgroup.normalizer (E : Set G) ⊓ H z).relIndex (Subgroup.normalizer (E : Set G)) ∣
      P.relIndex (Subgroup.normalizer (E : Set G)) :=
    Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex P _ _ hP.le inf_le_left)
  rcases Nat.even_or_odd ((Subgroup.normalizer (E : Set G) ⊓ H z).relIndex
    (Subgroup.normalizer (E : Set G))) with he | ho
  · exact absurd ((even_iff_two_dvd.mp he).trans hdvd) hPN3
  · exact ho

omit D

end OddFive

section Five

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

include D

omit D

end Five

end CFSG.RankThree.GF2n.Parrott
