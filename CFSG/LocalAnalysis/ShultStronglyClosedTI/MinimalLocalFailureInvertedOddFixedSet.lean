module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureAmbientConjugation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullFull

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem even_card_of_fixedPointFree_involution {α : Type*} [Finite α] (s : Set α)
    (f : α → α) (hmaps : ∀ x ∈ s, f x ∈ s) (hinv : ∀ x ∈ s, f (f x) = x)
    (hfree : ∀ x ∈ s, f x ≠ x) : Even (Nat.card s) := by
  classical
  let : Fintype s := Fintype.ofFinite s
  let g : s → s := fun x => ⟨f x, hmaps x x.property⟩
  have hg : Function.Involutive g := fun x => Subtype.ext (hinv x x.property)
  let σ : Equiv.Perm s := hg.toPerm g
  have hσ : σ ^ 2 = 1 := by
    ext x
    simp [σ, sq, hg x]
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    intro hx
    exact hfree x x.property (congrArg Subtype.val hx)
  have hdvd := Equiv.Perm.two_dvd_card_support hσ
  rw [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card] at hdvd
  exact even_iff_two_dvd.mpr hdvd

theorem le_oddCore_map_of_normal_odd {N A : Subgroup G} (hAN : A ≤ N)
    (hnormal : (A.subgroupOf N).Normal) (hodd : Odd (Nat.card A)) :
    A ≤ (CFSG.oddCore N).map N.subtype := by
  have hcard : Nat.card (A.subgroupOf N) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hle : A.subgroupOf N ≤ CFSG.oddCore N :=
    le_sSup ⟨hnormal, hcard ▸ hodd⟩
  intro a ha
  exact Subgroup.mem_map.mpr ⟨⟨a, hAN ha⟩, hle ha, rfl⟩

theorem odd_card_oddCore_map [Finite G] (N : Subgroup G) :
    Odd (Nat.card ((CFSG.oddCore N).map N.subtype)) := by
  rw [Subgroup.card_map_of_injective N.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card N

theorem conj_mem_oddCore_map {N : Subgroup G} {r n : G} (hr : r ∈ (CFSG.oddCore N).map N.subtype)
    (hn : n ∈ N) : n * r * n⁻¹ ∈ (CFSG.oddCore N).map N.subtype := by
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
  refine Subgroup.mem_map.mpr ⟨⟨n, hn⟩ * r' * ⟨n, hn⟩⁻¹,
    (inferInstance : (CFSG.oddCore N).Normal).conj_mem r' hr' ⟨n, hn⟩, ?_⟩
  simp

theorem quotientRightRelEquiv_pointRightCosetMul (H : Subgroup G)
    (omega : pointRightCosetSpace H) (g : G) :
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H (pointRightCosetMul H omega g) =
      g⁻¹ • QuotientGroup.quotientRightRelEquivQuotientLeftRel H omega := by
  simp [pointRightCosetMul]

theorem odd_card_of_transitive_odd_subgroup [Finite G] (H J : Subgroup G)
    (hJodd : Odd (Nat.card J)) (s : Set (pointRightCosetSpace H)) (delta : pointRightCosetSpace H)
    (hdelta : delta ∈ s) (hpres : ∀ x ∈ s, ∀ j ∈ J, pointRightCosetMul H x j ∈ s)
    (htrans : ∀ x ∈ s, ∃ j ∈ J, pointRightCosetMul H delta j = x) :
    Odd (Nat.card s) := by
  classical
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  let : Fintype J := Fintype.ofFinite J
  have horbit : MulAction.orbit J (e delta) = e '' s := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨pointRightCosetMul H delta (j : G)⁻¹,
        hpres delta hdelta _ (J.inv_mem j.property), ?_⟩
      rw [quotientRightRelEquiv_pointRightCosetMul, inv_inv]
      rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, rfl⟩ := htrans x hx
      refine ⟨⟨j⁻¹, J.inv_mem hj⟩, ?_⟩
      rw [quotientRightRelEquiv_pointRightCosetMul]
      rfl
  have hcard : Nat.card (MulAction.orbit J (e delta)) = Nat.card s := by
    rw [horbit, Nat.card_image_of_injective e.injective]
  let : Fintype (MulAction.orbit J (e delta)) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer J (e delta)) := Fintype.ofFinite _
  have hmul := MulAction.card_orbit_mul_card_stabilizer_eq_card_group J (e delta)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    hcard] at hmul
  rw [← hmul] at hJodd
  exact (Nat.odd_mul.mp hJodd).1

variable [Finite G]

theorem pointClass_fixed_point_stabilizer {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (g : G) {gamma : pointRightCosetSpace H}
    (hgamma : pointRightCosetMul H gamma (rightConjugateElem z g) = gamma) :
    gamma = rightCosetMk H g ∧ rightCosetStabilizer H gamma = rightConjugate H g := by
  have huniq := ((involution_point_unique_containment_action h.distinguished_mem
    h.distinguished_order).2 h.unique_containment).2.1 (rightConjugateElem z g) ⟨g, rfl⟩
  have hbase := point_class_conjugate_fixed_rightCoset h g
  have heq : gamma = rightCosetMk H g := huniq.unique hgamma hbase
  exact ⟨heq, by rw [heq, rightCosetStabilizer_mk]⟩

theorem minimalLocalFailure_inverted_odd_subgroup_fixed_set_obstruction
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    {alpha beta : pointRightCosetSpace H} (hab : alpha ≠ beta)
    {t : G} (ht : t ∈ involutionPointClass z)
    (htab : pointRightCosetMul H alpha t = beta)
    {A : Subgroup G} (hAab : A ≤ rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H beta)
    (hAodd : Odd (Nat.card A)) (htA : t ∈ Subgroup.normalizer (A : Set G))
    (hAt : ⁅A, Subgroup.zpowers t⁆ ≠ ⊥)
    {gamma : pointRightCosetSpace H} (hgamma : pointRightCosetMul H gamma t = gamma) :
    let N := Subgroup.normalizer (A : Set G)
    let Δ := pointFixedSet H A
    let R := (CFSG.oddCore N).map N.subtype
    let L := Subgroup.closure (conjugacyWithin N t)
    let Gγ := rightCosetStabilizer H gamma
    N < ⊤ ∧ gamma ∉ Δ ∧ (∀ delta ∈ Δ, pointRightCosetMul H delta t ≠ delta) ∧
      Even (Nat.card Δ) ∧ twoRank L = 1 ∧
      (QuotientGroup.mk (⟨t, htA⟩ : N) : N ⧸ CFSG.oddCore N) ∈
        Subgroup.center (N ⧸ CFSG.oddCore N) ∧
      (N : Set G) = (N ⊓ Subgroup.centralizer ({t} : Set G) : Set G) * (R : Set G) ∧
      Gγ ⊓ N = N ⊓ Subgroup.centralizer ({t} : Set G) ∧
      conjugacyWithin Gγ t ∩ (N : Set G) = {t} ∧
      (2 < Nat.card Δ →
        ¬ ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
          ∃ x ∈ Subgroup.centralizer (A : Set G),
            pointRightCosetMul H a x = c ∧ pointRightCosetMul H b x = d) := by
  intro N Δ R L Gγ
  classical
  obtain ⟨hsimple, -⟩ := minimalLocalFailure_nonabelian_simple h
  obtain ⟨g, hg⟩ := ht
  have hg : rightConjugateElem z g = t := hg
  have htorder : orderOf t = 2 := by
    rw [← hg]
    exact order_two_of_mem_pointClass h.local_datum.distinguished_order ⟨g, rfl⟩
  have htsq : t * t = 1 := by
    rw [← sq]
    exact (orderOf_eq_prime_iff.mp htorder).1
  obtain ⟨-, hGγ⟩ := pointClass_fixed_point_stabilizer h.local_datum g
    (gamma := gamma) (by rw [hg]; exact hgamma)
  have huniq := ((involution_point_unique_containment_action h.local_datum.distinguished_mem
    h.local_datum.distinguished_order).2 h.local_datum.unique_containment).2.1 t ⟨g, hg⟩
  have hAalpha : alpha ∈ Δ :=
    (mem_pointFixedSet_iff H A alpha).mpr (hAab.trans inf_le_left)
  have htriple := properHull_minimal_failure_distinguished_triple_centralization h hcomm
    hsmallerR1
  have hagamma : alpha ≠ gamma := by
    intro heq
    apply hab
    rw [← htab, heq, hgamma]
  have hgammaΔ : gamma ∉ Δ := by
    intro hgam
    have hid := htriple t ⟨g, hg⟩ gamma alpha hgamma hagamma
    have hA3 : A ≤ (rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H alpha) ⊓
        rightCosetStabilizer H (pointRightCosetMul H alpha t) := by
      rw [htab]
      exact le_inf (le_inf ((mem_pointFixedSet_iff H A gamma).mp hgam)
        (hAab.trans inf_le_left)) (hAab.trans inf_le_right)
    rw [hid] at hA3
    exact hAt ((commutator_zpowers_eq_bot_iff A t).mpr (hA3.trans inf_le_right))
  have hfree : ∀ delta ∈ Δ, pointRightCosetMul H delta t ≠ delta := by
    intro delta hdelta hfix
    exact hgammaΔ (huniq.unique hgamma hfix ▸ hdelta)
  have hmapsΔ : ∀ delta ∈ Δ, pointRightCosetMul H delta t ∈ Δ :=
    fun delta hdelta => normalizer_preserves_pointFixedSet htA hdelta
  have heven : Even (Nat.card Δ) := by
    refine even_card_of_fixedPointFree_involution Δ (fun omega => pointRightCosetMul H omega t)
      hmapsΔ ?_ hfree
    intro omega _
    rw [pointRightCosetMul_mul, htsq]
    exact (mem_point_right_stabilizer_iff H omega 1).mp (Subgroup.one_mem _)
  have hAne : A ≠ ⊥ := by
    intro hbot
    apply hAt
    rw [hbot, Subgroup.commutator_bot_left]
  have hNproper : N < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hAnormal : A.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hAnormal.eq_bot_or_eq_top with hbot | htopA
    · exact hAne hbot
    · have hzA : z ∈ A := by rw [htopA]; trivial
      have hdvd := Subgroup.orderOf_dvd_natCard A hzA
      rw [h.local_datum.distinguished_order] at hdvd
      exact (Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr hdvd)
  have h' := minimalLocalFailure_ambient_right_conjugate h g
  rw [hg] at h'
  have hescape : ¬ N ≤ rightConjugate H g := by
    intro hle
    apply hgammaΔ
    rw [mem_pointFixedSet_iff, hGγ]
    exact Subgroup.le_normalizer.trans hle
  obtain ⟨-, -, hxor⟩ :=
    minimalLocalFailure_proper_local_hull_dichotomy h' hcomm hsmallerR1 hNproper htA hescape
  have hAR : A ≤ R :=
    le_oddCore_map_of_normal_odd Subgroup.le_normalizer Subgroup.normal_in_normalizer hAodd
  have htL : Subgroup.zpowers t ≤ L := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure ⟨1, by simp⟩
  have hnot2 : ¬ (2 ≤ twoRank L ∧ ⁅R, L⁆ = ⊥ ∧ R1Full L ∧
      (∃ _ : (⊤ : Subgroup L).Normal,
        CFSG.oddCore L < ⊤ ∧ Odd (⊤ : Subgroup L).index ∧
          fusionIsBenderGroup ((⊤ : Subgroup L) ⧸ (CFSG.oddCore L).subgroupOf ⊤)) ∧
      fusionIsBenderGroup (L ⧸ CFSG.oddCore L) ∧ ExplicitRankOneModel (L ⧸ CFSG.oddCore L)) := by
    rintro ⟨-, hRL, -⟩
    apply hAt
    exact le_bot_iff.mp ((Subgroup.commutator_mono hAR htL).trans hRL.le)
  obtain ⟨hrank, hcenter, hfactor, hpoint, hsingleton⟩ := hxor.or.resolve_right hnot2
  rw [← hGγ] at hpoint hsingleton
  refine ⟨hNproper, hgammaΔ, hfree, heven, hrank, hcenter, hfactor, hpoint, hsingleton, ?_⟩
  intro hthree htrans
  have hCN : Subgroup.centralizer (A : Set G) ≤ N :=
    Subgroup.centralizer_le_normalizer (A : Set G)
  have hCpres : ∀ x ∈ Δ, ∀ c ∈ Subgroup.centralizer (A : Set G),
      pointRightCosetMul H x c ∈ Δ :=
    fun x hx c hc => normalizer_preserves_pointFixedSet (hCN hc) hx
  have hcommR : ∀ c ∈ Subgroup.centralizer (A : Set G), c * t * c⁻¹ * t⁻¹ ∈ R := by
    intro c hc
    have hcz := Subgroup.mem_center_iff.mp hcenter (QuotientGroup.mk ⟨c, hCN hc⟩)
    have hker : (⟨c, hCN hc⟩ : N) * ⟨t, htA⟩ * (⟨c, hCN hc⟩ : N)⁻¹ * (⟨t, htA⟩ : N)⁻¹ ∈
        CFSG.oddCore N := by
      have h1 : (QuotientGroup.mk ((⟨c, hCN hc⟩ : N) * ⟨t, htA⟩ * (⟨c, hCN hc⟩ : N)⁻¹ *
          (⟨t, htA⟩ : N)⁻¹) : N ⧸ CFSG.oddCore N) = 1 := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcz]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_map.mpr ⟨_, hker, rfl⟩
  have hcommC : ∀ c ∈ Subgroup.centralizer (A : Set G),
      c * t * c⁻¹ * t⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
    intro c hc
    have htC : t * c⁻¹ * t⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro a ha
      have hta : t⁻¹ * a * t ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htA) a).mp ha
        simpa only [inv_inv] using this
      have hcinv := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hc) _ hta
      calc a * (t * c⁻¹ * t⁻¹) = t * ((t⁻¹ * a * t) * c⁻¹) * t⁻¹ := by group
        _ = t * (c⁻¹ * (t⁻¹ * a * t)) * t⁻¹ := by rw [hcinv]
        _ = t * c⁻¹ * t⁻¹ * a := by group
    have := Subgroup.mul_mem _ hc htC
    simpa only [mul_assoc] using this
  have hJodd : Odd (Nat.card (R ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) :=
    Odd.of_dvd_nat (odd_card_oddCore_map N) (Subgroup.card_dvd_of_le inf_le_left)
  have hJfix : ∀ j ∈ R ⊓ Subgroup.centralizer (A : Set G), ∀ x ∈ Δ,
      pointRightCosetMul H x j = x := by
    intro j hj delta hdelta
    by_contra hmove
    have hεΔ := hCpres delta hdelta j hj.2
    have hJtrans : ∀ x ∈ Δ, ∃ k ∈ R ⊓ Subgroup.centralizer (A : Set G),
        pointRightCosetMul H delta k = x := by
      intro x hx
      by_cases hxd : x = delta
      · exact ⟨1, Subgroup.one_mem _, by
          rw [hxd]; exact (mem_point_right_stabilizer_iff H delta 1).mp (Subgroup.one_mem _)⟩
      obtain ⟨c, hc, hcδ, hcε⟩ := htrans delta hdelta (pointRightCosetMul H delta j) hεΔ
        delta hdelta x hx (Ne.symm hmove) (Ne.symm hxd)
      have hcinvδ : pointRightCosetMul H delta c⁻¹ = delta := by
        calc pointRightCosetMul H delta c⁻¹
            = pointRightCosetMul H (pointRightCosetMul H delta c) c⁻¹ := by rw [hcδ]
          _ = delta := by
            rw [pointRightCosetMul_mul, mul_inv_cancel]
            exact (mem_point_right_stabilizer_iff H delta 1).mp (Subgroup.one_mem _)
      refine ⟨c⁻¹ * j * c, ⟨?_, ?_⟩, ?_⟩
      · have hmem := conj_mem_oddCore_map hj.1 (N.inv_mem (hCN hc))
        rw [inv_inv] at hmem
        exact hmem
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hj.2) hc
      · rw [← pointRightCosetMul_mul, ← pointRightCosetMul_mul, hcinvδ, hcε]
    have hodd := odd_card_of_transitive_odd_subgroup H _ hJodd Δ delta hdelta
      (fun x hx k hk => hCpres x hx k hk.2) hJtrans
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  set epsilon := pointRightCosetMul H alpha t with hepsilon
  have hεΔ : epsilon ∈ Δ := hmapsΔ alpha hAalpha
  have hεne : epsilon ≠ alpha := hfree alpha hAalpha
  obtain ⟨zeta, hzetaΔ, hzetaα, hzetaε⟩ : ∃ zeta ∈ Δ, zeta ≠ alpha ∧ zeta ≠ epsilon := by
    by_contra hnone
    push Not at hnone
    have hsub : Δ ⊆ {alpha, epsilon} := by
      intro x hx
      by_cases hxa : x = alpha
      · exact Or.inl hxa
      · exact Or.inr (hnone x hx hxa)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hpair : ({alpha, epsilon} : Set (pointRightCosetSpace H)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    rw [← Nat.card_coe_set_eq] at hle
    omega
  obtain ⟨c, hc, hcα, hcε⟩ := htrans alpha hAalpha epsilon hεΔ alpha hAalpha zeta hzetaΔ
    (Ne.symm hεne) (Ne.symm hzetaα)
  have hj : c * t * c⁻¹ * t⁻¹ ∈ R ⊓ Subgroup.centralizer (A : Set G) :=
    ⟨hcommR c hc, hcommC c hc⟩
  have hjα := hJfix _ hj alpha hAalpha
  have hct : c * t = (c * t * c⁻¹ * t⁻¹) * t * c := by group
  have hleft : pointRightCosetMul H alpha (c * t) = epsilon := by
    rw [← pointRightCosetMul_mul, hcα]
  have hright : pointRightCosetMul H alpha ((c * t * c⁻¹ * t⁻¹) * t * c) = zeta := by
    rw [← pointRightCosetMul_mul, ← pointRightCosetMul_mul, hjα, ← hepsilon, hcε]
  rw [← hct, hleft] at hright
  exact hzetaε hright.symm

theorem minimalLocalFailure_inverted_odd_subgroup_fixed_set_eq_pair
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    {alpha beta : pointRightCosetSpace H} (hab : alpha ≠ beta)
    {t : G} (ht : t ∈ involutionPointClass z)
    (htab : pointRightCosetMul H alpha t = beta)
    {A : Subgroup G} (hAab : A ≤ rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H beta)
    (hAodd : Odd (Nat.card A)) (htA : t ∈ Subgroup.normalizer (A : Set G))
    (hAt : ⁅A, Subgroup.zpowers t⁆ ≠ ⊥)
    (htrans : ∀ a ∈ pointFixedSet H A, ∀ b ∈ pointFixedSet H A, ∀ c ∈ pointFixedSet H A,
      ∀ d ∈ pointFixedSet H A, a ≠ b → c ≠ d →
        ∃ x ∈ Subgroup.centralizer (A : Set G),
          pointRightCosetMul H a x = c ∧ pointRightCosetMul H b x = d) :
    pointFixedSet H A = {alpha, beta} := by
  obtain ⟨g, hg⟩ := ht
  have hg : rightConjugateElem z g = t := hg
  let gamma := rightCosetMk H g
  have hgamma : pointRightCosetMul H gamma t = gamma := by
    rw [← hg]
    exact point_class_conjugate_fixed_rightCoset h.local_datum g
  have hall := minimalLocalFailure_inverted_odd_subgroup_fixed_set_obstruction h hcomm
    hsmallerR1 hab ⟨g, hg⟩ htab hAab hAodd htA hAt hgamma
  have hle : Nat.card (pointFixedSet H A) ≤ 2 := by
    by_contra hgt
    exact hall.2.2.2.2.2.2.2.2.2 (by omega) htrans
  have hα : alpha ∈ pointFixedSet H A :=
    (mem_pointFixedSet_iff H A alpha).mpr (hAab.trans inf_le_left)
  have hβ : beta ∈ pointFixedSet H A :=
    (mem_pointFixedSet_iff H A beta).mpr (hAab.trans inf_le_right)
  have hsub : ({alpha, beta} : Set (pointRightCosetSpace H)) ⊆ pointFixedSet H A := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hα
    · exact hβ
  have hpair : ({alpha, beta} : Set (pointRightCosetSpace H)).ncard = 2 :=
    Set.ncard_pair hab
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [hpair, ← Nat.card_coe_set_eq]
  exact hle

end CFSG.ShultStronglyClosedTI
