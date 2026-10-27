module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootQuotientClassesBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootTwoCoreStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairStabilizerInvolution
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses

open CFSG.Open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_relIndex_normalizer_coset {H Q B : Subgroup G} {u : G} (hBH : B ≤ H)
    (hQn : ∀ k ∈ H, ∀ v ∈ Q, k⁻¹ * v * k ∈ Q) (huH : u ∈ H)
    (htrans : ∀ x ∈ (fun y => u * y) '' (Q : Set G),
      ∃ n ∈ H ⊓ Subgroup.normalizer ((fun y => u * y) '' (Q : Set G)), n⁻¹ * u * n = x)
    (hCu : H ⊓ Subgroup.centralizer ({u} : Set G) ≤ Q ⊔ B) (hQB : Q ⊓ B = ⊥)
    (hBidx : B.relIndex H = Nat.card Q ^ 3) :
    Nat.card Q ∣ (H ⊓ Subgroup.normalizer ((fun y => u * y) '' (Q : Set G))).relIndex H := by
  set Δ := (fun y => u * y) '' (Q : Set G)
  set N := H ⊓ Subgroup.normalizer Δ
  set Cu := H ⊓ Subgroup.centralizer ({u} : Set G)
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_of_inv_conj_mem hQn
  have hCuN : Cu ≤ N := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨hg.1, (mem_normalizer_image_mul_left_iff (hHQ hg.1)).mpr ?_⟩
    rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hg.2, inv_mul_cancel_left,
      inv_mul_cancel]
    exact Q.one_mem
  have huN : u ∈ N :=
    hCuN (Subgroup.mem_inf.mpr ⟨huH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
  have hclass : conjugacyWithin N u = Δ := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact (Subgroup.mem_set_normalizer_iff''.mp (Subgroup.mem_inf.mp n.2).2 u).mp
        ⟨1, Q.one_mem, mul_one u⟩
    · intro hx
      obtain ⟨n, hn, hnx⟩ := htrans x hx
      exact ⟨⟨n, hn⟩, hnx⟩
  have hcardΔ : Nat.card Δ = Nat.card Q :=
    Nat.card_image_of_injective (mul_right_injective u) _
  have hNCu : N ⊓ Subgroup.centralizer ({u} : Set G) = Cu :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf hCuN inf_le_right)
  have horbit := FinalChain.card_conjugacyWithin_mul huN
  rw [hclass, hcardΔ, hNCu] at horbit
  have hr := Subgroup.relIndex_mul_card N H
  rw [inf_eq_left.mpr (inf_le_left : N ≤ H)] at hr
  have hb := Subgroup.relIndex_mul_card B H
  rw [inf_eq_left.mpr hBH, hBidx] at hb
  have hQBcard : Nat.card (Q ⊔ B : Subgroup G) = Nat.card Q * Nat.card B := by
    have h' := card_sup_mul_card_inf (fun b hb => hHQ (hBH hb) :
      B ≤ Subgroup.normalizer (Q : Set G))
    rw [sup_comm, inf_comm, hQB, Subgroup.card_bot, mul_one] at h'
    rw [h', mul_comm]
  obtain ⟨m, hm⟩ : Nat.card Cu ∣ Nat.card Q * Nat.card B :=
    hQBcard ▸ Subgroup.card_dvd_of_le hCu
  refine Dvd.intro m (Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos Nat.card_pos Nat.card_pos : 0 < Nat.card Q * Nat.card Cu) ?_).symm
  calc Nat.card Q * Nat.card Cu * N.relIndex H = N.relIndex H * Nat.card N := by
        rw [← horbit]; ring
    _ = Nat.card H := hr
    _ = Nat.card Q ^ 2 * (Nat.card Q * Nat.card B) := by rw [← hb]; ring
    _ = Nat.card Q ^ 2 * (Nat.card Cu * m) := by rw [hm]
    _ = Nat.card Q * Nat.card Cu * (Nat.card Q * m) := by ring

theorem exists_not_isConj_of_two_dvd_relIndex {H Q C : Subgroup G} (hCH : C ≤ H)
    (hCn : ∀ g ∈ H, ∀ x ∈ C, g * x * g⁻¹ ∈ C) {E : Type*} [Group E] (π : ↥C →* E)
    (hπ : Function.Surjective π) (hπeq : ∀ x y, π x = π y ↔ (x : G)⁻¹ * y ∈ Q)
    (hQn : ∀ k ∈ H, ∀ v ∈ Q, k⁻¹ * v * k ∈ Q) (u : ↥C) (hu2 : (u : G) ^ 2 = 1)
    (huQ : (u : G) ∉ Q)
    (heven : 2 ∣ (H ⊓ Subgroup.normalizer ((fun y => (u : G) * y) '' (Q : Set G))).relIndex H) :
    ∃ a b : E, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ IsConj a b := by
  have : Finite E := Finite.of_surjective π hπ
  set N := H ⊓ Subgroup.normalizer ((fun y => (u : G) * y) '' (Q : Set G))
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_of_inv_conj_mem hQn
  have hū : orderOf (π u) = 2 := orderOf_map_eq_two π hπeq hu2 huQ
  refine ⟨π u, ?_⟩
  by_contra hcon
  have hall : ∀ b : E, orderOf b = 2 → IsConj (π u) b := fun b hb => by
    by_contra hnc
    exact hcon ⟨b, hū, hb, hnc⟩
  have hset : conjugatesOf (π u) = {b : E | orderOf b = 2} := by
    ext b
    refine ⟨fun hb => ?_, hall b⟩
    obtain ⟨c, hc⟩ := (hb : IsConj (π u) b)
    exact (SemiconjBy.orderOf_eq _ hc).symm.trans hū
  have hodd : Odd (Nat.card (conjugatesOf (π u))) := by
    rw [hset]
    refine odd_card_orderOf_eq_two (even_iff_two_dvd.mpr ?_)
    rw [← hū]
    exact orderOf_dvd_natCard _
  have hcl : (Subgroup.centralizer ({π u} : Set E)).index = Nat.card (conjugatesOf (π u)) := by
    have h1 := conjugacy_class_card_mul_centralizer (π u)
    have h2 := Subgroup.card_mul_index (Subgroup.centralizer ({π u} : Set E))
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Subgroup.centralizer ({π u} : Set E)))
    rw [h2, ← h1, mul_comm]
  have hcomap : (Subgroup.centralizer ({π u} : Set E)).comap π = N.subgroupOf C := by
    ext c
    have hcH : (c : G) ∈ H := hCH c.2
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      ← map_mul, ← map_mul, hπeq, Subgroup.coe_mul, Subgroup.coe_mul,
      show ((c : G) * u)⁻¹ * (u * c) = (u : G)⁻¹ * ((c : G)⁻¹ * u * c) by group]
    exact ⟨fun hy => Subgroup.mem_inf.mpr
        ⟨hcH, (mem_normalizer_image_mul_left_iff (hHQ hcH)).mpr hy⟩,
      fun hcN => (mem_normalizer_image_mul_left_iff (hHQ hcH)).mp (Subgroup.mem_inf.mp hcN).2⟩
  have hoddC : Odd (N.relIndex C) := by
    rw [Subgroup.relIndex, ← hcomap, Subgroup.index_comap_of_surjective _ hπ, hcl]
    exact hodd
  have hHle : H ≤ C ⊔ N := by
    intro g hg
    obtain ⟨v, hv⟩ : ∃ v : C, (v : G) = g * u * g⁻¹ := ⟨⟨_, hCn g hg _ u.2⟩, rfl⟩
    have hv2 : (v : G) ^ 2 = 1 := by rw [hv, conj_pow, hu2, mul_one, mul_inv_cancel]
    have hvQ : (v : G) ∉ Q := by
      intro hvQ
      apply huQ
      have h' := hQn g hg _ hvQ
      rwa [hv, show g⁻¹ * (g * u * g⁻¹) * g = u by group] at h'
    obtain ⟨e, he⟩ := isConj_iff.mp (hall (π v) (orderOf_map_eq_two π hπeq hv2 hvQ))
    obtain ⟨c, rfl⟩ := hπ e
    rw [← map_inv, ← map_mul, ← map_mul, hπeq] at he
    have hcH : (c : G) ∈ H := hCH c.2
    have hnH : g⁻¹ * c ∈ H := H.mul_mem (H.inv_mem hg) hcH
    have hnN : g⁻¹ * (c : G) ∈ N := by
      refine Subgroup.mem_inf.mpr ⟨hnH, (mem_normalizer_image_mul_left_iff (hHQ hnH)).mpr ?_⟩
      have h' := hQn c hcH _ he
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hv,
        show (c : G)⁻¹ * ((c * u * (c : G)⁻¹)⁻¹ * (g * u * g⁻¹)) * c =
          (u : G)⁻¹ * ((g⁻¹ * c)⁻¹ * u * (g⁻¹ * c)) by group] at h'
    rw [show g = c * (g⁻¹ * c)⁻¹ by group]
    exact Subgroup.mul_mem_sup c.2 (N.inv_mem hnN)
  have hNC : N ≤ Subgroup.normalizer (C : Set G) := fun n hn =>
    le_normalizer_of_conj_mem hCn (Subgroup.mem_inf.mp hn).1
  have hsup : N ⊔ C = H :=
    le_antisymm (sup_le inf_le_left hCH) (hHle.trans (sup_comm C N).le)
  have hrel := relIndex_sup_eq_relIndex hNC
  rw [hsup] at hrel
  rw [hrel] at heven
  exact (Nat.not_even_iff_odd.mpr hoddC) (even_iff_two_dvd.mpr heven)

theorem minimalLocalFailure_linear_root_quotient_multiple_involution_classes_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t) :
    LinearChain.RootQuotientInvolutionClassesConclusion H z beta := by
  obtain ⟨-, -, hBidx, hNK, hQB, hJ, -, -, -, -, -, hinvJ, -⟩ := hker
  obtain ⟨-, ⟨e, he⟩, hQ4, hQclass, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  have hQn := PairInvolutionFixedField.point_subgroup_normalized hQclass
  have hBH := pairPointStabilizer_le_point H beta
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set B := pairPointStabilizer H beta
  have hcent : ∀ u ∈ B, orderOf u = 2 → u ∈ Subgroup.centralizer (Q : Set G) := by
    intro u huB hu
    have huJ := hinvJ u huB hu
    rw [hJ] at huJ
    exact (Subgroup.mem_inf.mp huJ).2
  have hdvd : ∀ u ∈ B, orderOf u = 2 →
      Nat.card Q ∣ (H ⊓ Subgroup.normalizer ((fun x => u * x) '' (Q : Set G))).relIndex H := by
    intro u huB hu
    have hQu : Q ≤ Subgroup.centralizer ({u} : Set G) := fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hcent u huB hu) v hv)
    obtain ⟨-, -, h2T, -⟩ := MixedClass.minimalLocalFailure_mixed_involution_class_closure h hcomm
      hsmallerR1 hbeta ht hproper huB hu
    rw [← hQdef, inf_eq_left.mpr hQu] at h2T
    have huΔ : u ∈ (fun x => u * x) '' (Q : Set G) := ⟨1, Q.one_mem, mul_one u⟩
    obtain ⟨hLu, -⟩ := proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta
      ht hproper hexcl huB hu
    refine card_dvd_relIndex_normalizer_coset hBH hQn (hBH huB) (fun x hx => ?_)
      (fun g hg => ?_) hQB hBidx
    · by_cases hxu : x = u
      · exact ⟨1, Subgroup.one_mem _, by rw [hxu, inv_one, one_mul, mul_one]⟩
      · obtain ⟨n, hn, hn1, -⟩ := h2T u huΔ x hx x hx u huΔ (Ne.symm hxu) hxu
        exact ⟨n, hn, hn1⟩
    · rw [← hNK]
      exact Subgroup.mem_inf.mpr ⟨FinalChain.centralizer_le_normalizer_of_localHull_eq hLu
        (Subgroup.mem_inf.mp hg).2, (Subgroup.mem_inf.mp hg).1⟩
  have h2q : 2 ∣ Nat.card Q := by
    rw [he]
    refine dvd_pow_self 2 fun he0 => ?_
    rw [he, he0, pow_zero] at hQ4
    omega
  unfold LinearChain.RootQuotientInvolutionClassesConclusion
  refine ⟨fun u huB hu =>
    dvd_two_pow_factorization he (relIndex_ne_zero_of_finite _ _) (hdvd u huB hu), ?_⟩
  obtain ⟨u, huB, hu⟩ := proper_pair_stabilizer_exists_involution h hcomm hbeta ht hproper
  have huC : u ∈ H ⊓ Subgroup.centralizer (Q : Set G) :=
    Subgroup.mem_inf.mpr ⟨hBH huB, hcent u huB hu⟩
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have huQ : u ∉ Q := by
    intro huQ
    have hu1 : u ∈ Q ⊓ B := Subgroup.mem_inf.mpr ⟨huQ, huB⟩
    rw [hQB, Subgroup.mem_bot] at hu1
    rw [hu1, orderOf_one] at hu
    omega
  have hQnC : (Q.subgroupOf (H ⊓ Subgroup.centralizer (Q : Set G))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        ← Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp g.2).2 _ hn, mul_inv_cancel_right]
      exact hn⟩
  refine ⟨hQnC, exists_not_isConj_of_two_dvd_relIndex inf_le_left
    (fun g hg x hx => conj_mem_inf_centralizer hQn hg hx)
    (QuotientGroup.mk' (Q.subgroupOf (H ⊓ Subgroup.centralizer (Q : Set G))))
    (QuotientGroup.mk'_surjective _) (fun x y => ?_) hQn ⟨u, huC⟩ hu2 huQ
    (h2q.trans (hdvd u huB hu))⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

end CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses
