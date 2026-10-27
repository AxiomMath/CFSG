module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicFull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem conj_mem_rightPairFlipFiber {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
    {s b : G} (hs : s ∈ rightPairFlipFiber H z beta) (hb : b ∈ pairPointStabilizer H beta) :
    b⁻¹ * s * b ∈ rightPairFlipFiber H z beta := by
  have hbα : rightCosetTranslate H (rightCosetMk H 1) b = rightCosetMk H 1 :=
    (mem_rightCosetStabilizer_iff H _ _).mp hb.1
  have hbβ : rightCosetTranslate H beta b = beta :=
    (mem_rightCosetStabilizer_iff H _ _).mp hb.2
  have hbinv : rightCosetTranslate H (rightCosetMk H 1) b⁻¹ = rightCosetMk H 1 := by
    conv_lhs => rw [← hbα]
    rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  refine ⟨conj_mem_pointClass hs.1 b, ?_⟩
  rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hbinv, hs.2, hbβ]

variable [Finite G]

theorem proper_pair_torus_setup
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let Q := minimalLocalFailurePairActionPointHull H z
    IsElemAbelian 2 Q ∧ 4 ≤ Nat.card Q ∧ (Q : Set G) \ {1} = conjugacyWithin H z ∧ Q ≤ H ∧
      (∀ k ∈ H, ∀ v ∈ Q, k⁻¹ * v * k ∈ Q) ∧
      X ≤ B ∧ (X.subgroupOf B).Normal ∧ IsCyclic X ∧ Odd (Nat.card X) ∧
      Nat.card X = Nat.card (conjugacyWithin H z) ∧ Nat.card X = Nat.card Q - 1 ∧
      (∀ x ∈ X, rightConjugateElem x t = x⁻¹) ∧
      rightPairFlipFiber H z beta = (fun x => t * x) '' (X : Set G) ∧
      conjugacyWithin B t = (fun x => t * x) '' (X : Set G) ∧
      (∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
        ∃! x : X, (x : G)⁻¹ * a * x = b) := by
  intro B X Q
  obtain ⟨hQ, hcardQ, hQclass, -, -, -, -, hIB, hXI, -, hcyclic, hodd, hXcard, -, hset,
    hinv, -, -⟩ := CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨-, -, -, -, -, -, hfiberJ, hinvset, -, hfactor⟩ :=
    involution_point_pair_flip_zStar_factorization h.local_datum S hzS hzcenter beta hbeta t ht
  have htorder : orderOf t = 2 :=
    order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two htorder
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hXset : (X : Set G) = pairInvertedSet H beta t := hset
  have hXB : X ≤ B := hXI.trans hIB
  have hXQcard : Nat.card X = Nat.card Q - 1 := by
    rw [hXcard, ← hQclass, card_diff_one]
  have hfiber : rightPairFlipFiber H z beta = (fun x => t * x) '' (X : Set G) := by
    have hprod : (X : Set G) = (fun s => s * t) '' rightPairFlipFiber H z beta := by
      rw [hXset, hinvset]
      rfl
    ext s
    constructor
    · intro hs
      have hst : s * t ∈ (X : Set G) := by
        rw [hprod]
        exact ⟨s, hs, rfl⟩
      have hts : t * s ∈ (X : Set G) := by
        have hmem := X.inv_mem hst
        have heq : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, htinv, (inv_eq_of_mul_eq_one_right
          (mul_self_eq_one_of_orderOf_eq_two (order_two_of_mem_pointClass
            h.local_datum.distinguished_order hs.1)))]
        rwa [heq] at hmem
      refine ⟨t * s, hts, ?_⟩
      change t * (t * s) = s
      rw [← mul_assoc, htt, one_mul]
    · rintro ⟨x, hx, rfl⟩
      have hxinv : x⁻¹ ∈ (X : Set G) := X.inv_mem hx
      rw [hprod] at hxinv
      obtain ⟨s, hs, hseq⟩ := hxinv
      have htx : t * x = x⁻¹ * t := by
        have hconj := hinv x hx
        change t⁻¹ * x * t = x⁻¹ at hconj
        rw [htinv] at hconj
        calc t * x = (t * x * t) * t := by rw [mul_assoc, htt, mul_one]
          _ = x⁻¹ * t := by rw [hconj]
      change t * x ∈ rightPairFlipFiber H z beta
      rw [htx, ← hseq, mul_assoc, htt, mul_one]
      exact hs
  have hclassB : conjugacyWithin B t = (fun x => t * x) '' (X : Set G) := by
    rw [← hfiber]
    ext s
    constructor
    · rintro ⟨b, rfl⟩
      exact conj_mem_rightPairFlipFiber ht b.2
    · intro hs
      rw [hfiberJ] at hs
      obtain ⟨j, rfl⟩ := hs
      exact ⟨⟨j, (pairOddCore_le H beta t).1 j.2⟩, rfl⟩
  have hnormal : (X.subgroupOf B).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hb : ((g : G)⁻¹)⁻¹ = (g : G) := inv_inv _
    have hginv : (g : G)⁻¹ ∈ B := B.inv_mem g.2
    have h1 : ((g : G)⁻¹)⁻¹ * (t * n) * (g : G)⁻¹ ∈ (fun x => t * x) '' (X : Set G) := by
      rw [← hfiber]
      exact conj_mem_rightPairFlipFiber (hfiber ▸ ⟨n, hn, rfl⟩) hginv
    have h2 : ((g : G)⁻¹)⁻¹ * t * (g : G)⁻¹ ∈ (fun x => t * x) '' (X : Set G) := by
      rw [← hfiber]
      exact conj_mem_rightPairFlipFiber ht hginv
    obtain ⟨x₁, hx₁, hx₁eq⟩ := h1
    obtain ⟨x₂, hx₂, hx₂eq⟩ := h2
    rw [hb] at hx₁eq hx₂eq
    have hkey : (g : G) * (n : G) * (g : G)⁻¹ = x₂⁻¹ * x₁ := by
      have e1 : t * x₁ = (g : G) * (t * n) * (g : G)⁻¹ := hx₁eq
      have e2 : t * x₂ = (g : G) * t * (g : G)⁻¹ := hx₂eq
      calc (g : G) * (n : G) * (g : G)⁻¹ =
            ((g : G) * t * (g : G)⁻¹)⁻¹ * ((g : G) * (t * n) * (g : G)⁻¹) := by group
        _ = (t * x₂)⁻¹ * (t * x₁) := by rw [e1, e2]
        _ = x₂⁻¹ * x₁ := by group
    change (g : G) * (n : G) * (g : G)⁻¹ ∈ X
    rw [hkey]
    exact X.mul_mem (X.inv_mem hx₂) hx₁
  have horbit : ∀ a ∈ (Q : Set G) \ {1}, ∃ x : X, (x : G)⁻¹ * z * x = a := by
    intro a ha
    rw [hQclass] at ha
    obtain ⟨k, rfl⟩ := ha
    have hk : (k : G) ∈ (Subgroup.centralizer ({z} : Set G) : Set G) *
        pairInvertedSet H beta t := by
      rw [← hfactor]
      exact k.2
    obtain ⟨c, hc, x, hx, hkcx⟩ := Set.mem_mul.mp hk
    rw [← hXset] at hx
    refine ⟨⟨x, hx⟩, ?_⟩
    have hcz : c⁻¹ * z * c = z := by
      rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hc, inv_mul_cancel_left]
    change x⁻¹ * z * x = (k : G)⁻¹ * z * k
    rw [← hkcx]
    calc x⁻¹ * z * x = x⁻¹ * (c⁻¹ * z * c) * x := by rw [hcz]
      _ = (c * x)⁻¹ * z * (c * x) := by group
  let f : X → ((Q : Set G) \ {1} : Set G) := fun x =>
    ⟨(x : G)⁻¹ * z * x, by
      have hmem : (x : G)⁻¹ * z * x ∈ conjugacyWithin H z :=
        ⟨⟨x, pairPointStabilizer_le_point H beta (hXB x.2)⟩, rfl⟩
      rwa [← hQclass] at hmem⟩
  have hfsurj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx⟩ := horbit a ha
    exact ⟨x, Subtype.ext hx⟩
  have hfinj : Function.Injective f := by
    refine (hfsurj.bijective_of_nat_card_le ?_).1
    rw [card_diff_one, hXQcard]
  have hregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b := by
    intro a ha b hb
    obtain ⟨xa, hxa⟩ := horbit a ha
    obtain ⟨xb, hxb⟩ := horbit b hb
    refine ⟨xa⁻¹ * xb, ?_, ?_⟩
    · rw [← hxa, ← hxb]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro x hx
      have hfx : f (xa * x) = f xb := by
        apply Subtype.ext
        change ((xa * x : X) : G)⁻¹ * z * ((xa * x : X) : G) = (xb : G)⁻¹ * z * xb
        rw [hxb, ← hx, ← hxa]
        simp only [Subgroup.coe_mul]
        group
      have := hfinj hfx
      rw [← this]
      group
  exact ⟨hQ, hcardQ, hQclass, point_subgroup_le h.local_datum.distinguished_mem hQclass,
    point_subgroup_normalized hQclass, hXB, hnormal, hcyclic, hodd, hXcard, hXQcard, hinv,
    hfiber, hclassB, hregular⟩

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
