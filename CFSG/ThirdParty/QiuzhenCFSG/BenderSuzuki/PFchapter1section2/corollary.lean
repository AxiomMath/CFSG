module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_c

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section2

open PFchapter1section1 PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 2, Corollary to Proposition 2
-/

public theorem corollary_H_involution_mem_S
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t x : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q))
    (hxH : x ∈ H) (hxI : IsInvolution x) :
    x ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxQ : x ∈ Q :=
    involution_mem_Q_of_mem_H H D Q t hsec.hA.A1 x hxH hxI
  obtain ⟨P, hS_eq⟩ := hsec.S_sylow_in_Q
  have hnil : Group.IsNilpotent Q :=
    proposition_1_b H D Q K V W Q0 S Q1 t hsec
  haveI : Group.IsNilpotent Q := by
    simpa using hnil
  have hPnorm : (P : Subgroup Q).Normal :=
    Group.IsNilpotent.sylow_normal
      (show Group.IsNilpotent Q from inferInstance) 2 P
  haveI : Unique (Sylow 2 Q) := Sylow.unique_of_normal P hPnorm
  let xQ : Q := ⟨x, hxQ⟩
  have hxQ_order : orderOf xQ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      exact hxI.sq_eq_one
    · intro hxQ_one
      exact hxI.ne_one (Subtype.ext_iff.mp hxQ_one)
  let Z : Subgroup Q := Subgroup.zpowers xQ
  have hZcard : Nat.card Z = 2 := by
    dsimp [Z]
    rw [Nat.card_zpowers, hxQ_order]
  have hZp : IsPGroup 2 Z := by
    refine IsPGroup.of_card (p := 2) (G := Z) (n := 1) ?_
    norm_num [hZcard]
  obtain ⟨P', hZ_le_P'⟩ := IsPGroup.exists_le_sylow (G := Q) (p := 2) hZp
  have hP'_eq_P : (P' : Subgroup Q) = (P : Subgroup Q) := by
    exact congrArg (fun R : Sylow 2 Q => (R : Subgroup Q)) (Subsingleton.elim P' P)
  have hxP : xQ ∈ (P : Subgroup Q) := by
    have hxZ : xQ ∈ Z := Subgroup.mem_zpowers xQ
    have hxP' : xQ ∈ (P' : Subgroup Q) := hZ_le_P' hxZ
    simpa [hP'_eq_P] using hxP'
  rw [hS_eq]
  exact Subgroup.mem_map.mpr ⟨xQ, hxP, rfl⟩

private theorem corollary_S_involution_iff_H_involution
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t x : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    x ∈ S ∧ IsInvolution x ↔ x ∈ H ∧ IsInvolution x := by
  constructor
  · intro hx
    exact ⟨hsec.hA.A1.Q_le_H (hsec.S_le_Q hx.1), hx.2⟩
  · intro hx
    exact ⟨corollary_H_involution_mem_S H D Q K V W Q0 S Q1 t x hsec hx.1 hx.2,
      hx.2⟩

private theorem corollary_map_K_to_H_involutions_injective
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s) :
    Function.Injective
      (fun k : {x : G // x ∈ peterfalviKSet D t} =>
        (⟨rightConjugateElem s (k : G),
          ((PFchapter1section1.proposition_3 H D Q t hA1).2 s hsH hsI
              (rightConjugateElem s (k : G))).2
            ⟨k, k.property, rfl⟩⟩ :
          {x : G // x ∈ H ∧ IsInvolution x})) := by
  classical
  let Sset : Set G := {x : G | x ∈ H ∧ IsInvolution x}
  let phi : {x : G // x ∈ peterfalviKSet D t} → {x : G // x ∈ Sset} := fun k =>
    ⟨rightConjugateElem s (k : G), by
      simpa [Sset] using
        ((PFchapter1section1.proposition_3 H D Q t hA1).2 s hsH hsI
            (rightConjugateElem s (k : G))).2
          ⟨k, k.property, rfl⟩⟩
  have hphi_surj : Function.Surjective phi := by
    rintro ⟨y, hyS⟩
    rcases ((PFchapter1section1.proposition_3 H D Q t hA1).2 s hsH hsI y).1
        (by simpa [Sset] using hyS) with
      ⟨k, hkK, hk_eq⟩
    refine ⟨⟨k, hkK⟩, ?_⟩
    apply Subtype.ext
    simpa [phi, Sset] using hk_eq
  have hphi_inj : Function.Injective phi := by
    exact
      (hphi_surj.bijective_of_nat_card_le
        (by simpa [Sset] using le_of_eq (PFchapter1section1.proposition_3 H D Q t hA1).1)).1
  simpa [phi, Sset] using hphi_inj

public theorem corollary_K_regular_on_S_involutions
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    ConjugationRegularOn K {x : G | x ∈ S ∧ IsInvolution x} := by
  classical
  dsimp [ConjugationRegularOn]
  constructor
  · intro x hx a haK
    have hxH : x ∈ H ∧ IsInvolution x :=
      (corollary_S_involution_iff_H_involution H D Q K V W Q0 S Q1 t x hsec).1 hx
    have haKset : a ∈ peterfalviKSet D t := (hsec.K_def a).mp haK
    have hmemH :
        rightConjugateElem x a ∈ H ∧ IsInvolution (rightConjugateElem x a) :=
      ((PFchapter1section1.proposition_3 H D Q t hsec.hA.A1).2
        x hxH.1 hxH.2 (rightConjugateElem x a)).2
        ⟨a, haKset, rfl⟩
    exact
      (corollary_S_involution_iff_H_involution H D Q K V W Q0 S Q1 t
        (rightConjugateElem x a) hsec).2 hmemH
  · intro x hx y hy
    have hxH : x ∈ H ∧ IsInvolution x :=
      (corollary_S_involution_iff_H_involution H D Q K V W Q0 S Q1 t x hsec).1 hx
    have hyH : y ∈ H ∧ IsInvolution y :=
      (corollary_S_involution_iff_H_involution H D Q K V W Q0 S Q1 t y hsec).1 hy
    rcases
        ((PFchapter1section1.proposition_3 H D Q t hsec.hA.A1).2
          x hxH.1 hxH.2 y).1 hyH with
      ⟨k, hkKset, hk_eq⟩
    refine ⟨k, ⟨(hsec.K_def k).mpr hkKset, hk_eq.symm⟩, ?_⟩
    intro a ha
    rcases ha with ⟨haK, hy_eq_a⟩
    let kSet : {z : G // z ∈ peterfalviKSet D t} := ⟨k, hkKset⟩
    let aSet : {z : G // z ∈ peterfalviKSet D t} :=
      ⟨a, (hsec.K_def a).mp haK⟩
    have hinj :=
      corollary_map_K_to_H_involutions_injective H D Q t x
        hsec.hA.A1 hxH.1 hxH.2
    have himage : (⟨rightConjugateElem x (aSet : G),
          ((PFchapter1section1.proposition_3 H D Q t hsec.hA.A1).2 x hxH.1 hxH.2
              (rightConjugateElem x (aSet : G))).2
            ⟨aSet, aSet.property, rfl⟩⟩ :
          {z : G // z ∈ H ∧ IsInvolution z}) =
        (⟨rightConjugateElem x (kSet : G),
          ((PFchapter1section1.proposition_3 H D Q t hsec.hA.A1).2 x hxH.1 hxH.2
              (rightConjugateElem x (kSet : G))).2
            ⟨kSet, kSet.property, rfl⟩⟩ :
          {z : G // z ∈ H ∧ IsInvolution z}) := by
      apply Subtype.ext
      calc
        rightConjugateElem x (aSet : G) = y := hy_eq_a.symm
        _ = rightConjugateElem x (kSet : G) := hk_eq.symm
    have haSet_eq_kSet : aSet = kSet := hinj himage
    exact congrArg Subtype.val haSet_eq_kSet

private theorem corollary_S_hasPrimePowerOrder
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    ∃ n : ℕ, Nat.card S = 2 ^ n := by
  classical
  obtain ⟨P, hS_eq⟩ := hsec.S_sylow_in_Q
  have hP_two : ∃ n : ℕ, Nat.card (P : Subgroup Q) = 2 ^ n := by
    exact P.isPGroup'.exists_card_eq
  rcases hP_two with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hcard_map :
      Nat.card ((P : Subgroup Q).map Q.subtype) = Nat.card (P : Subgroup Q) :=
    Subgroup.card_map_of_injective
      (K := (P : Subgroup Q)) (f := Q.subtype) Q.subtype_injective
  rw [hS_eq, hcard_map, hn]

private theorem corollary_exists_rank_two_subgroup_le_Q
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (h2rank : TwoRankAtLeastTwo G) :
    ∃ A : Subgroup G, A ≤ Q ∧ Nat.card A = 4 ∧ ∀ x : A, x ^ 2 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀card, hE₀sq⟩ := TwoRankAtLeastTwo.exists_subgroup h2rank
  have hE₀p : IsPGroup 2 E₀ := by
    refine IsPGroup.of_card (p := 2) (G := E₀) (n := 2) ?_
    norm_num [hE₀card]
  obtain ⟨T, hE₀T⟩ := IsPGroup.exists_le_sylow (G := G) (p := 2) hE₀p
  obtain ⟨S, hSQ⟩ := PFchapter1section1.proposition_1_c H D Q t hA1
  obtain ⟨g, hgTS⟩ := MulAction.exists_smul_eq G T S
  let A : Subgroup G := E₀.map (MulAut.conj g).toMonoidHom
  have hA_le_S : A ≤ (S : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyE, rfl⟩
    have hyT : y ∈ (T : Subgroup G) := hE₀T hyE
    rw [← hgTS, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (T : Subgroup G) hyT
  have hAcard : Nat.card A = 4 := by
    have hcard_map :
        Nat.card A = Nat.card E₀ := by
      exact Subgroup.card_map_of_injective
        (K := E₀) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hcard_map, hE₀card]
  have hAsq : ∀ x : A, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    rcases Subgroup.mem_map.mp x.property with ⟨y, hyE, hyx⟩
    have hy2 : y ^ 2 = (1 : G) := by
      exact congrArg Subtype.val (hE₀sq ⟨y, hyE⟩)
    rw [← hyx]
    simpa [pow_two] using congrArg (fun z : G => (MulAut.conj g) z) hy2
  exact ⟨A, hA_le_S.trans hSQ, hAcard, hAsq⟩

private theorem corollary_exists_two_distinct_nontrivial_of_card_four
    {A : Type*} [Group A] [Finite A] (hcard : Nat.card A = 4) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hcardF : Fintype.card A = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have htwo_lt : 2 < Fintype.card A := by
    omega
  rcases Fintype.two_lt_card_iff.mp htwo_lt with ⟨a, b, c, hab, hac, hbc⟩
  by_cases ha : a = 1
  · by_cases hb : b = 1
    · exact False.elim (hab (ha.trans hb.symm))
    · by_cases hc : c = 1
      · exact False.elim (hac (ha.trans hc.symm))
      · exact ⟨b, c, hb, hc, hbc⟩
  · by_cases hb : b = 1
    · by_cases hc : c = 1
      · exact False.elim (hbc (hb.trans hc.symm))
      · exact ⟨a, c, ha, hc, hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

private theorem corollary_Q_normalized_by_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t k : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hkH : k ∈ H) :
    k ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hqQ
    let qH : H := ⟨q, hA1.Q_le_H hqQ⟩
    let kH : H := ⟨k, hkH⟩
    have hqSub : qH ∈ Q.subgroupOf H := by
      simpa [qH, Subgroup.mem_subgroupOf] using hqQ
    have hconj := hA1.Q_normal_in_H.conj_mem qH hqSub kH
    simpa [qH, kH, Subgroup.mem_subgroupOf] using hconj
  · intro hqQ
    have hkInvH : k⁻¹ ∈ H := H.inv_mem hkH
    let qH : H := ⟨k * q * k⁻¹, hA1.Q_le_H hqQ⟩
    let kInvH : H := ⟨k⁻¹, hkInvH⟩
    have hqSub : qH ∈ Q.subgroupOf H := by
      simpa [qH, Subgroup.mem_subgroupOf] using hqQ
    have hconj := hA1.Q_normal_in_H.conj_mem qH hqSub kInvH
    change ((k⁻¹ * (k * q * k⁻¹) * (k⁻¹)⁻¹ : G) ∈ Q) at hconj
    simpa [mul_assoc] using hconj


private theorem corollary_K_normalizes_S
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    K ≤ Subgroup.normalizer (S : Set G) := by
  classical
  obtain ⟨P, hS_eq⟩ := hsec.S_sylow_in_Q
  have hnil : Group.IsNilpotent Q :=
    proposition_1_b H D Q K V W Q0 S Q1 t hsec
  haveI : Group.IsNilpotent Q := by
    simpa using hnil
  have hPnorm : (P : Subgroup Q).Normal :=
    Group.IsNilpotent.sylow_normal
      (show Group.IsNilpotent Q from inferInstance) 2 P
  haveI : Unique (Sylow 2 Q) := Sylow.unique_of_normal P hPnorm
  haveI : (P : Subgroup Q).Characteristic := Sylow.characteristic_of_subsingleton P
  intro k hkK
  have hkH : k ∈ H := hsec.hA.A1.D_le_H (hsec.K_le_D hkK)
  have hkQ : k ∈ Subgroup.normalizer (Q : Set G) :=
    corollary_Q_normalized_by_H hsec.hA.A1 hkH
  let φ : Q ≃* Q :=
    { toFun := fun q =>
        ⟨k * (q : G) * k⁻¹,
          (Subgroup.mem_normalizer_iff.mp hkQ (q : G)).1 q.property⟩
      invFun := fun q =>
        ⟨k⁻¹ * (q : G) * k, by
          have hmem :=
            (Subgroup.mem_normalizer_iff.mp
              ((Subgroup.normalizer (Q : Set G)).inv_mem hkQ) (q : G)).1 q.property
          simpa using hmem⟩
      left_inv := by
        intro q
        apply Subtype.ext
        group
      right_inv := by
        intro q
        apply Subtype.ext
        group
      map_mul' := by
        intro q r
        apply Subtype.ext
        change k * ((q : G) * (r : G)) * k⁻¹ =
          (k * (q : G) * k⁻¹) * (k * (r : G) * k⁻¹)
        group }
  have hPmap : (P : Subgroup Q).map φ.toMonoidHom = (P : Subgroup Q) :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hsS
    rw [hS_eq] at hsS ⊢
    rcases Subgroup.mem_map.mp hsS with ⟨q, hqP, hq_eq⟩
    have hφqP : φ q ∈ (P : Subgroup Q) := by
      rw [← hPmap]
      exact Subgroup.mem_map.mpr ⟨q, hqP, rfl⟩
    refine Subgroup.mem_map.mpr ⟨φ q, hφqP, ?_⟩
    simpa [φ, hq_eq]
  · intro hsS
    rw [hS_eq] at hsS ⊢
    rcases Subgroup.mem_map.mp hsS with ⟨q, hqP, hq_eq⟩
    have hφqP : φ.symm q ∈ (P : Subgroup Q) := by
      have hPmap_symm : (P : Subgroup Q).map φ.symm.toMonoidHom = (P : Subgroup Q) :=
        Subgroup.characteristic_iff_map_eq.mp inferInstance φ.symm
      rw [← hPmap_symm]
      exact Subgroup.mem_map.mpr ⟨q, hqP, rfl⟩
    refine Subgroup.mem_map.mpr ⟨φ.symm q, hφqP, ?_⟩
    change k⁻¹ * (q : G) * k = s
    have hq_eq' : (q : G) = k * s * k⁻¹ := by
      simpa using hq_eq
    rw [hq_eq']
    change k⁻¹ * (k * s * k⁻¹) * k = s
    group

private theorem corollary_more_than_one_S_involution
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    ∃ x y : G, x ∈ S ∧ y ∈ S ∧ IsInvolution x ∧ IsInvolution y ∧ x ≠ y := by
  classical
  have h2rank : TwoRankAtLeastTwo G := by
    exact hsec.hA.A3
  obtain ⟨A, hAQ, hAcard, hAsq⟩ :=
    corollary_exists_rank_two_subgroup_le_Q H D Q t hsec.hA.A1 h2rank
  obtain ⟨a, b, ha_ne, hb_ne, hab⟩ :=
    corollary_exists_two_distinct_nontrivial_of_card_four hAcard
  let x : G := a
  let y : G := b
  have hxI : IsInvolution x := by
    constructor
    · intro hx_one
      exact ha_ne (Subtype.ext hx_one)
    · exact congrArg Subtype.val (hAsq a)
  have hyI : IsInvolution y := by
    constructor
    · intro hy_one
      exact hb_ne (Subtype.ext hy_one)
    · exact congrArg Subtype.val (hAsq b)
  have hxH : x ∈ H := hsec.hA.A1.Q_le_H (hAQ a.property)
  have hyH : y ∈ H := hsec.hA.A1.Q_le_H (hAQ b.property)
  have hxS : x ∈ S :=
    corollary_H_involution_mem_S H D Q K V W Q0 S Q1 t x hsec hxH hxI
  have hyS : y ∈ S :=
    corollary_H_involution_mem_S H D Q K V W Q0 S Q1 t y hsec hyH hyI
  exact ⟨x, y, hxS, hyS, hxI, hyI, fun hxy => hab (Subtype.ext hxy)⟩

public theorem corollary
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    IsMulCommutative S ∨ IsSuzukiTwoGroup S := by
  have hregular : ConjugationRegularOn K {x : G | x ∈ S ∧ IsInvolution x} :=
    corollary_K_regular_on_S_involutions H D Q K V W Q0 S Q1 t hsec
  have hS_two : ∃ n : ℕ, Nat.card S = 2 ^ n :=
    corollary_S_hasPrimePowerOrder H D Q K V W Q0 S Q1 t hsec
  have hK_cyclic : IsCyclic K :=
    (proposition_2 H D Q K V W Q0 S Q1 t hsec).1
  have hK_norm_S : K ≤ Subgroup.normalizer (S : Set G) :=
    corollary_K_normalizes_S H D Q K V W Q0 S Q1 t hsec
  have hmore_than_one_involution :
      ∃ x y : G, x ∈ S ∧ y ∈ S ∧ IsInvolution x ∧ IsInvolution y ∧ x ≠ y :=
    corollary_more_than_one_S_involution H D Q K V W Q0 S Q1 t hsec
  by_cases hcomm : IsMulCommutative S
  · exact Or.inl hcomm
  · right
    have involution_coe (x : S) (hx : IsInvolution x) :
        IsInvolution (x : G) := by
      constructor
      · intro hxone
        exact hx.ne_one (Subtype.ext hxone)
      · exact congrArg Subtype.val hx.sq_eq_one
    have involution_subtype (x : S) (hx : IsInvolution (x : G)) :
        IsInvolution x := by
      constructor
      · intro hxone
        exact hx.ne_one (congrArg Subtype.val hxone)
      · apply Subtype.ext
        exact hx.sq_eq_one
    refine ⟨?_, hcomm, ?_, ?_⟩
    · rcases hS_two with ⟨n, hn⟩
      exact ⟨n, by simpa using hn⟩
    · rcases hmore_than_one_involution with
        ⟨x, y, hxS, hyS, hxI, hyI, hxy⟩
      exact ⟨⟨x, hxS⟩, ⟨y, hyS⟩,
        involution_subtype ⟨x, hxS⟩ hxI,
        involution_subtype ⟨y, hyS⟩ hyI,
        fun h => hxy (congrArg Subtype.val h)⟩
    · letI : Subgroup.Normalizes K S := ⟨hK_norm_S⟩
      refine ⟨K, inferInstance, inferInstance, hK_cyclic, ?_, ?_⟩
      · rw [faithfulSMul_iff]
        intro k hkfix
        rcases hmore_than_one_involution with
          ⟨x, _y, hxS, _hyS, hxI, _hyI, _hxy⟩
        let xS : S := ⟨x, hxS⟩
        have hfixS : k • xS = xS := hkfix xS
        have hright :
            rightConjugateElem x ((k⁻¹ : K) : G) = x := by
          simpa [rightConjugateElem,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
              congrArg Subtype.val hfixS
        obtain ⟨a, ha, huniq⟩ :=
          hregular.2 x ⟨hxS, hxI⟩ x ⟨hxS, hxI⟩
        have hkinv_property :
            ((k⁻¹ : K) : G) ∈ K ∧
              x = rightConjugateElem x ((k⁻¹ : K) : G) :=
          ⟨(k⁻¹ : K).property, hright.symm⟩
        have hone_property :
            (1 : G) ∈ K ∧ x = rightConjugateElem x (1 : G) := by
          simp [rightConjugateElem]
        have hkinvG_one : ((k⁻¹ : K) : G) = (1 : G) :=
          (huniq _ hkinv_property).trans (huniq _ hone_property).symm
        have hkinv_one : k⁻¹ = (1 : K) := by
          apply Subtype.ext
          exact hkinvG_one
        simpa using congrArg Inv.inv hkinv_one
      · constructor
        · intro x hx k
          have hxI : IsInvolution (x : G) := involution_coe x hx
          have hmem :=
            hregular.1 (x : G) ⟨x.property, hxI⟩
              ((k⁻¹ : K) : G) (k⁻¹ : K).property
          apply involution_subtype
          simpa [rightConjugateElem,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hmem.2
        · intro x hx y hy
          have hxI : IsInvolution (x : G) := involution_coe x hx
          have hyI : IsInvolution (y : G) := involution_coe y hy
          obtain ⟨a, ha, huniq⟩ :=
            hregular.2 (x : G) ⟨x.property, hxI⟩
              (y : G) ⟨y.property, hyI⟩
          let k : K := ⟨a⁻¹, K.inv_mem ha.1⟩
          refine ⟨k, ?_, ?_⟩
          · apply Subtype.ext
            simpa [k, rightConjugateElem,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using ha.2
          · intro b hb
            apply Subtype.ext
            have hbG :
                (y : G) =
                  rightConjugateElem (x : G) ((b⁻¹ : K) : G) := by
              have hbval := congrArg Subtype.val hb
              simpa [rightConjugateElem,
                Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hbval
            have hb_inv_eq_a : ((b⁻¹ : K) : G) = a :=
              huniq _ ⟨(b⁻¹ : K).property, hbG⟩
            change (b : G) = a⁻¹
            simpa using congrArg Inv.inv hb_inv_eq_a

end PFchapter1section2
end CFSG.BenderSuzuki
