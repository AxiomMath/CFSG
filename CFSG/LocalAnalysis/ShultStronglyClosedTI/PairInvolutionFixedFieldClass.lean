module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation

public section

namespace CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem class_member_inheritance {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hcentral : InvolutionPointCentralSylow z)
    {Q : Subgroup G} (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {u : G}
    (hYH : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) {r : G}
    (hr : r ∈ Q ⊓ Subgroup.centralizer ({u} : Set G)) (hr1 : r ≠ 1)
    (hEclass : ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) \ {1} ⊆
      conjugacyWithin (Subgroup.centralizer ({u} : Set G)) r) :
    InvolutionPointLocalEmbedding (H.subgroupOf (Subgroup.centralizer ({u} : Set G)))
        (⟨r, hr.2⟩ : Subgroup.centralizer ({u} : Set G)) ∧
      InvolutionPointCentralSylow (⟨r, hr.2⟩ : Subgroup.centralizer ({u} : Set G)) ∧
      involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) =
        conjugacyWithin (Subgroup.centralizer ({u} : Set G)) r ∧
      Q ⊓ Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.closure (conjugacyWithin (Subgroup.centralizer ({u} : Set G)) r) := by
  let Y := Subgroup.centralizer ({u} : Set G)
  have hrQ : r ∈ (Q : Set G) \ {1} := ⟨hr.1, hr1⟩
  have hrc : r ∈ conjugacyWithin H z := hQclass ▸ hrQ
  obtain ⟨k, hk⟩ := hrc
  have hkr : rightConjugateElem z (k : G) = r := hk
  have hdatum : InvolutionPointLocalEmbedding H r := by
    have hl := local_point_datum_right_conjugate h (k : G)
    rwa [minimalLocalFailure_point_right_conjugate H k k.2, hkr] at hl
  have hcentr : InvolutionPointCentralSylow r := by
    have hc := minimalLocalFailure_central_sylow_right_conjugate hcentral (k : G)
    rwa [hkr] at hc
  obtain ⟨hlocal, hsylow⟩ := involution_point_subgroup_inheritance hdatum Y hr.2 hYH
  have hrD : r ∈ involutionPointClass z := point_subgroup_class h hQclass hrQ
  have hDr : involutionPointClass r = involutionPointClass z := pointClass_eq_of_mem hrD
  have hrY : r ∈ Y := hr.2
  have hDY : involutionPointClass z ∩ (Y : Set G) = conjugacyWithin Y r := by
    obtain ⟨S, hrS, hrcenter⟩ := hcentr
    ext s
    constructor
    · rintro ⟨hsD, hsY⟩
      obtain ⟨a, ha⟩ := subgroup_class_conjugate_mem_point hdatum S hrS hrcenter Y hrY
        (hDr.symm ▸ hsD) hsY
      have hs'D : (a : G)⁻¹ * s * a ∈ involutionPointClass z := conj_mem_pointClass hsD a
      have hs'Y : (a : G)⁻¹ * s * a ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem a.2) hsY) a.2
      have hs'Q : (a : G)⁻¹ * s * a ∈ (Q : Set G) \ {1} := by
        rw [← class_inter_point h hQclass]
        exact ⟨hs'D, ha⟩
      obtain ⟨y, hy⟩ := hEclass ⟨⟨hs'Q.1, hs'Y⟩, hs'Q.2⟩
      refine ⟨y * a⁻¹, ?_⟩
      calc
        ((y * a⁻¹ : Y) : G)⁻¹ * r * ((y * a⁻¹ : Y) : G) =
            (a : G) * ((y : G)⁻¹ * r * y) * (a : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        _ = s := by
          rw [hy]
          group
    · rintro ⟨y, rfl⟩
      refine ⟨conj_mem_pointClass hrD y, ?_⟩
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem y.2) hrY) y.2
  refine ⟨hlocal, hsylow hcentr, hDY, ?_⟩
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (hEclass ⟨hw, hw1⟩)

theorem fixed_set_eq_orbit {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {Q : Subgroup G} {e : ℕ} (hQcard : Nat.card Q = 2 ^ e) (he : 1 ≤ e)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {u : G} (huH : u ∈ H)
    (hu : orderOf u = 2) {r : G} (hrH : r ∈ H)
    (hDY : involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) =
      conjugacyWithin (Subgroup.centralizer ({u} : Set G)) r) :
    {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} := by
  let Y := Subgroup.centralizer ({u} : Set G)
  have hQH : Q ≤ H := point_subgroup_le h.distinguished_mem hQclass
  ext omega
  constructor
  · rintro ⟨y, hy, rfl⟩
    change rightCosetTranslate H (rightCosetTranslate H (rightCosetMk H 1) y) u =
      rightCosetTranslate H (rightCosetMk H 1) y
    rw [rightCosetTranslate_mul, Subgroup.mem_centralizer_singleton_iff.mp hy,
      ← rightCosetTranslate_mul, (translate_base_iff H u).mpr huH]
  · intro homega
    change rightCosetTranslate H omega u = omega at homega
    obtain ⟨g, rfl⟩ := exists_rightCosetMk omega
    have hwH : g * u * g⁻¹ ∈ H := (translate_mk_fixed_iff H g u).mp homega
    have hworder : orderOf (g * u * g⁻¹) = 2 := by
      simpa only [inv_inv] using (orderOf_conj_eq u g⁻¹).trans hu
    obtain ⟨v, hvQ, hv1, hvw⟩ := exists_nonidentity_commute hQcard he hworder
      (point_subgroup_normalized hQclass _ hwH)
    have hvcomm : v * (g * u * g⁻¹) = g * u * g⁻¹ * v :=
      Subgroup.mem_centralizer_singleton_iff.mp hvw
    let s : G := g⁻¹ * v * g
    have hsY : s ∈ Y := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc
        s * u = g⁻¹ * (v * (g * u * g⁻¹)) * g := by
          simp only [s]
          group
        _ = g⁻¹ * (g * u * g⁻¹ * v) * g := by rw [hvcomm]
        _ = u * s := by
          simp only [s]
          group
    have hsD : s ∈ involutionPointClass z :=
      conj_mem_pointClass (point_subgroup_class h hQclass ⟨hvQ, hv1⟩) g
    have hsr : s ∈ conjugacyWithin Y r := by
      rw [← hDY]
      exact ⟨hsD, hsY⟩
    obtain ⟨y, hy⟩ := hsr
    have hfixg : rightCosetTranslate H (rightCosetMk H g) s = rightCosetMk H g := by
      apply (translate_mk_fixed_iff H g s).mpr
      have hgs : g * s * g⁻¹ = v := by
        change g * (g⁻¹ * v * g) * g⁻¹ = v
        group
      rw [hgs]
      exact hQH hvQ
    have hfixy : rightCosetTranslate H (rightCosetMk H y) s = rightCosetMk H y := by
      apply (translate_mk_fixed_iff H y s).mpr
      have hys : (y : G) * s * (y : G)⁻¹ = r := by
        rw [← hy]
        group
      rw [hys]
      exact hrH
    refine ⟨y, y.2, ?_⟩
    rw [translate_base_mk]
    exact class_fixed_unique h hsD hfixy hfixg

theorem class_centralizer_card {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {Q : Subgroup G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {u : G}
    (horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega}) :
    Nat.card ↥(involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) =
      (Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) - 1) *
        Nat.card {omega : rightCosetSpace H // rightCosetTranslate H omega u = omega} := by
  classical
  let Y := Subgroup.centralizer ({u} : Set G)
  let D := involutionPointClass z ∩ (Y : Set G)
  let P := {omega : rightCosetSpace H // rightCosetTranslate H omega u = omega}
  let := Fintype.ofFinite P
  let R : P → D → Prop := fun omega s => rightCosetTranslate H omega.1 s = omega.1
  have hpair : Nat.card {p : P × D // R p.1 p.2} = Nat.card D := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun p => p.1.2) ⟨?_, ?_⟩
    · rintro ⟨⟨omega₁, s₁⟩, h₁⟩ ⟨⟨omega₂, s₂⟩, h₂⟩ hs
      change s₁ = s₂ at hs
      subst hs
      have heq : omega₁.1 = omega₂.1 := class_fixed_unique h s₁.2.1 h₁ h₂
      have heq' : omega₁ = omega₂ := Subtype.ext heq
      subst heq'
      rfl
    · intro s
      obtain ⟨omega, homega⟩ := class_fixed_exists h s.2.1
      have hsu : Commute (s : G) u :=
        Subgroup.mem_centralizer_singleton_iff.mp s.2.2
      exact ⟨⟨⟨⟨omega, class_fixed_of_commute h s.2.1 hsu homega⟩, s⟩, homega⟩, rfl⟩
  have hbase : Nat.card {s : D // rightCosetTranslate H (rightCosetMk H 1) s = rightCosetMk H 1} =
      Nat.card ↥(((Q ⊓ Y : Subgroup G) : Set G) \ {1}) := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun s => ⟨(s : G), ?_⟩) ⟨?_, ?_⟩
    · have hsH : ((s : D) : G) ∈ H := (translate_base_iff H _).mp s.2
      have hsQ : ((s : D) : G) ∈ (Q : Set G) \ {1} := by
        rw [← class_inter_point h hQclass]
        exact ⟨(s : D).2.1, hsH⟩
      exact ⟨⟨hsQ.1, (s : D).2.2⟩, hsQ.2⟩
    · intro s₁ s₂ hs
      have h' : ((s₁ : D) : G) = ((s₂ : D) : G) :=
        congrArg (fun x : ↥(((Q ⊓ Y : Subgroup G) : Set G) \ {1}) => (x : G)) hs
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨w, hw⟩
      have hwD : w ∈ involutionPointClass z ∩ (H : Set G) := by
        rw [class_inter_point h hQclass]
        exact ⟨hw.1.1, hw.2⟩
      exact ⟨⟨⟨w, hwD.1, hw.1.2⟩, (translate_base_iff H w).mpr hwD.2⟩, rfl⟩
  have hfiber : ∀ omega : P, Nat.card {s : D // R omega s} =
      Nat.card (Q ⊓ Y : Subgroup G) - 1 := by
    intro omega
    rw [← card_diff_one, ← hbase]
    have homega : omega.1 ∈ {omega : rightCosetSpace H | ∃ y ∈ Y,
        rightCosetTranslate H (rightCosetMk H 1) y = omega} := by
      rw [horbit]
      exact omega.2
    obtain ⟨y, hy, hyomega⟩ := homega
    apply Nat.card_congr
    have hconjD : ∀ (s : D) (a : G), a ∈ Y → a⁻¹ * (s : G) * a ∈ D := fun s a ha =>
      ⟨conj_mem_pointClass s.2.1 a, Y.mul_mem (Y.mul_mem (Y.inv_mem ha) s.2.2) ha⟩
    refine
      { toFun := fun s => ⟨⟨y * s * y⁻¹, by
            simpa only [inv_inv] using hconjD s.1 y⁻¹ (Y.inv_mem hy)⟩, ?_⟩
        invFun := fun s => ⟨⟨y⁻¹ * s * y, hconjD s.1 y hy⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hs := s.2
      change rightCosetTranslate H omega.1 s = omega.1 at hs
      change rightCosetTranslate H (rightCosetMk H 1) (y * s * y⁻¹) = rightCosetMk H 1
      rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hyomega, hs, ← hyomega,
        rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
    · have hs := s.2
      change rightCosetTranslate H (rightCosetMk H 1) s = rightCosetMk H 1 at hs
      change rightCosetTranslate H omega.1 (y⁻¹ * s * y) = omega.1
      rw [← hyomega, rightCosetTranslate_mul,
        show y * (y⁻¹ * ((s : D) : G) * y) = (s : D) * y by group,
        ← rightCosetTranslate_mul, hs]
    · intro s
      apply Subtype.ext
      apply Subtype.ext
      change y⁻¹ * (y * s * y⁻¹) * y = s
      group
    · intro s
      apply Subtype.ext
      apply Subtype.ext
      change y * (y⁻¹ * s * y) * y⁻¹ = s
      group
  calc
    Nat.card D = Nat.card {p : P × D // R p.1 p.2} := hpair.symm
    _ = Nat.card (Σ omega : P, {s : D // R omega s}) :=
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype R)
    _ = ∑ omega : P, Nat.card {s : D // R omega s} := Nat.card_sigma
    _ = ∑ _omega : P, (Nat.card (Q ⊓ Y : Subgroup G) - 1) :=
      Finset.sum_congr rfl fun omega _ => hfiber omega
    _ = (Nat.card (Q ⊓ Y : Subgroup G) - 1) * Nat.card P := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm]

end CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
