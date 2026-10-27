module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsAlign
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairLinearOrSuzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOvergroupHull

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open Matrix CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ShultStronglyClosedTI.FixedPointModel CFSG.ShultStronglyClosedTI.OvergroupHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped LinearAlgebra.Projectivization

variable {G : Type} [Group G]

theorem mem_of_involution_count [Finite G] {L M Q : Subgroup G} (hQL : Q ≤ L) (hQM : Q ≤ M)
    (hQ : IsElemAbelian 2 Q)
    (hinv : Nat.card {x : L | x ∈ M.subgroupOf L ∧ orderOf x = 2} = Nat.card Q - 1)
    {x : G} (hxL : x ∈ L) (hxM : x ∈ M) (hx : orderOf x = 2) : x ∈ Q := by
  let I : Set L := {x : L | x ∈ M.subgroupOf L ∧ orderOf x = 2}
  let Q₁ : Set L := {y : L | (y : G) ∈ Q ∧ y ≠ 1}
  have hsub : Q₁ ⊆ I := by
    rintro y ⟨hyQ, hy1⟩
    refine ⟨hQM hyQ, ?_⟩
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hQ.2 _ hyQ) fun h => hy1 (Subtype.ext h)
  have hcard : Nat.card Q₁ = Nat.card Q - 1 := by
    rw [← card_diff_one Q]
    refine Nat.card_congr
      { toFun := fun y => ⟨((y : L) : G), y.2.1, fun h => y.2.2 (Subtype.ext h)⟩
        invFun := fun v => ⟨⟨v, hQL v.2.1⟩, v.2.1, fun h => v.2.2 (congrArg Subtype.val h)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have heq : Q₁ = I := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]
    exact hinv.le
  have hmem : (⟨x, hxL⟩ : L) ∈ I := ⟨hxM, by rw [Subgroup.orderOf_mk]; exact hx⟩
  rw [← heq] at hmem
  exact hmem.1

theorem not_succ_dvd_suzuki_order {q : ℕ} (hq : 4 ≤ q) :
    ¬ (q + 1) ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
  intro h
  have h' : ((q : ℤ) + 1) ∣ (q : ℤ) ^ 2 * ((q : ℤ) - 1) * ((q : ℤ) ^ 2 + 1) := by
    have := Int.natCast_dvd_natCast.mpr h
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at this
    exact this
  have h4 : ((q : ℤ) + 1) ∣ 4 := by
    have hid : (4 : ℤ) = ((q : ℤ) + 1) * ((q : ℤ) ^ 4 - 2 * (q : ℤ) ^ 3 + 3 * (q : ℤ) ^ 2 -
        4 * (q : ℤ) + 4) - (q : ℤ) ^ 2 * ((q : ℤ) - 1) * ((q : ℤ) ^ 2 + 1) := by ring
    rw [hid]
    exact dvd_sub (dvd_mul_right _ _) h'
  have := Int.le_of_dvd (by norm_num) h4
  omega

theorem card_psl2_of_card_two_pow {k : Type} [Field k] [Finite k] {e : ℕ}
    (hk : Nat.card k = 2 ^ e) :
    Nat.card (PSL2MatrixGroup k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  let : Fintype k := Fintype.ofFinite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := e) (by
    rw [← Nat.card_eq_fintype_card, hk])
  have hneg : (-1 : k) = 1 := CharTwo.neg_eq 1
  have h := huppert614_card_psl_mul_center (K := k)
  rwa [huppert614_card_center_of_neg_one_eq_one hneg, mul_one] at h

namespace UnitaryHullFrame

variable [Finite G] {H L : Subgroup G} {t : G} {Q : Subgroup G}
  (F : UnitaryHullFrame H t L (Nat.card Q))

omit [Finite G] in
theorem map_injective : Function.Injective (L.subtype.comp F.θ.toMonoidHom) :=
  Subtype.val_injective.comp F.θ.injective

theorem map_upperRootL (hQ : IsElemAbelian 2 Q) (hQH : Q ≤ H) (hQL : Q ≤ L)
    (hinv : Nat.card {x : L | x ∈ H.subgroupOf L ∧ orderOf x = 2} = Nat.card Q - 1) :
    (upperRootL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom) = Q := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    have hyH : (F.θ y : G) ∈ H := (F.mem_point y).mpr (upperRootL_smul_zero F.hJ F.hC hy)
    have hy2 : (F.θ y : G) * (F.θ y : G) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, upperRootL_mul_self F.hJ hy, map_one, Subgroup.coe_one]
    by_cases hy1 : (F.θ y : G) = 1
    · change (F.θ y : G) ∈ Q
      rw [hy1]
      exact Q.one_mem
    · exact mem_of_involution_count hQL hQH hQ hinv (F.θ y).2 hyH
        (orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1)
  · rw [Subgroup.card_map_of_injective F.map_injective, card_upperRootL F.hJ F.hC,
      card_unitaryCoverFixedField F.hfixed]
    exact F.hq.le

theorem map_lowerRootL (hQ : IsElemAbelian 2 Q) (hQH : Q ≤ H) (hQL : Q ≤ L)
    (hinv : Nat.card {x : L | x ∈ H.subgroupOf L ∧ orderOf x = 2} = Nat.card Q - 1)
    (htL : t ∈ L) (ht2 : t * t = 1) :
    (lowerRootL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom) = rightConjugate Q t := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    change (F.θ y : G) ∈ rightConjugate Q t
    have hyHt : (F.θ y : G) ∈ rightConjugate H t :=
      (F.mem_rightConjugate_iff htL ht2 y).mpr (lowerRootL_smul_two F.hJ F.hC hy)
    rw [mem_rightConjugate_iff_conj] at hyHt ⊢
    have hy2 : (F.θ y : G) * (F.θ y : G) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, lowerRootL_mul_self F.hJ hy, map_one, Subgroup.coe_one]
    have hconj2 : (t * (F.θ y : G) * t⁻¹) * (t * (F.θ y : G) * t⁻¹) = 1 := by
      rw [show (t * (F.θ y : G) * t⁻¹) * (t * (F.θ y : G) * t⁻¹) =
        t * ((F.θ y : G) * (F.θ y : G)) * t⁻¹ by group, hy2, mul_one, mul_inv_cancel]
    by_cases hy1 : t * (F.θ y : G) * t⁻¹ = 1
    · rw [hy1]
      exact Q.one_mem
    · exact mem_of_involution_count hQL hQH hQ hinv
        (L.mul_mem (L.mul_mem htL (F.θ y).2) (L.inv_mem htL)) hyHt
        (orderOf_eq_prime (by rw [pow_two]; exact hconj2) hy1)
  · have hcardQt : Nat.card (rightConjugate Q t) = Nat.card Q := by
      change Nat.card (Q.map (MulAut.conj t⁻¹).toMonoidHom) = Nat.card Q
      exact Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective
    rw [hcardQt, Subgroup.card_map_of_injective F.map_injective, card_lowerRootL F.hJ F.hC,
      card_unitaryCoverFixedField F.hfixed]
    exact F.hq.le

theorem map_sublineL_eq {K : Subgroup G}
    (hupper : (upperRootL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom) = Q)
    (hlower : (lowerRootL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom) = rightConjugate Q t)
    (hQK : Q ≤ K) (htK : t ∈ K)
    (hK : (∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = Nat.card Q ∧ Nonempty (K ≃* PSL2MatrixGroup k)) ∨
      (∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
        Nat.card k = Nat.card Q ∧ Nonempty (K ≃* CFSG.Blueprint.suzukiGroup m k))) :
    (sublineL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom) = K ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = Nat.card Q ∧ Nonempty (K ≃* PSL2MatrixGroup k) := by
  have hle : (sublineL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom) ≤ K := by
    rw [sublineL_eq_sup, Subgroup.map_sup, hupper, hlower]
    refine sup_le hQK fun x hx => ?_
    rw [mem_rightConjugate_iff_conj] at hx
    have hmem := K.mul_mem (K.mul_mem (K.inv_mem htK) (hQK hx)) htK
    rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at hmem
  have hq4 : 4 ≤ Nat.card Q := by
    rw [F.hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ F.f := Nat.pow_le_pow_right (by norm_num) F.hf
  have hcard : Nat.card ((sublineL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom)) =
      Nat.card Q * (Nat.card Q ^ 2 - 1) := by
    rw [Subgroup.card_map_of_injective F.map_injective,
      ← Nat.card_congr (sublineEquiv F.hJ F.hC).toEquiv,
      huppert614_card_specialLinearGroup,
      card_unitaryCoverFixedField F.hfixed]
    conv_rhs => rw [F.hq]
  rcases hK with ⟨k, _, _, hk, ⟨ψ⟩⟩ | ⟨m, k, _, _, hkm, hk, ⟨ψ⟩⟩
  · refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, k, inferInstance, inferInstance, hk, ⟨ψ⟩⟩
    rw [hcard, Nat.card_congr ψ.toEquiv, card_psl2_of_card_two_pow (hk.trans F.hq), hk]
  · exfalso
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard, Nat.card_congr ψ.toEquiv, CFSG.LieType.Ree.suzuki_order hkm, ← hkm, hk] at hdvd
    apply not_succ_dvd_suzuki_order hq4
    refine dvd_trans ⟨Nat.card Q * (Nat.card Q - 1), ?_⟩ hdvd
    have h1 : 1 ≤ Nat.card Q := by omega
    have h2 : 1 ≤ Nat.card Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring

end UnitaryHullFrame


structure UnitaryHullCoordinates (H : Subgroup G) (z : G) (beta : rightCosetSpace H) (t : G)
    (L : Subgroup G) extends
    UnitaryHullFrame H t L (Nat.card (minimalLocalFailurePairActionPointHull H z)) where
  upper : (upperRootL J C hJ).map (L.subtype.comp θ.toMonoidHom) =
    minimalLocalFailurePairActionPointHull H z
  lower : (lowerRootL J C hJ).map (L.subtype.comp θ.toMonoidHom) =
    rightConjugate (minimalLocalFailurePairActionPointHull H z) t
  subline : (sublineL J C hJ).map (L.subtype.comp θ.toMonoidHom) =
    minimalLocalFailureProperPairHull H z beta t

variable [Finite G]

theorem exists_unitaryHullCoordinates
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hY : Y < ⊤) (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y)
    (hdeg : Nat.card {ω : rightCosetSpace H |
        ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
        Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k)) ∧
      Nonempty (UnitaryHullCoordinates H z beta t
        (Subgroup.closure (involutionPointClass z ∩ (Y : Set G)))) := by
  obtain ⟨F⟩ := exists_unitaryHullFrame h hcomm hsmallerR1 hbeta ht hproper hY hKY hdeg
  set L := Subgroup.closure (involutionPointClass z ∩ (Y : Set G))
  have hL : L = Subgroup.closure (conjugacyWithin Y z) :=
    congrArg Subgroup.closure (overgroup_class_eq h hcomm hbeta ht hproper hKY)
  obtain ⟨-, hKL, hQL, -, -, -, -, -, -, hinvM, -⟩ :=
    overgroup_hull_structure h hcomm hsmallerR1 hbeta ht hproper hY hKY hL
  obtain ⟨hQH, hQK, -, hQ, -, -, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have htK : t ∈ minimalLocalFailureProperPairHull H z beta t :=
    minimalLocalFailureProperPair_flip_mem H z beta t
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two
    (order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1)
  have hupper := F.map_upperRootL hQ hQH hQL hinvM
  have hlower := F.map_lowerRootL hQ hQH hQL hinvM (hKL htK) ht2
  obtain ⟨-, -, -, hmodel, -⟩ :=
    ProperPairModel.minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1
      hbeta ht hproper
  have hK : (∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
        Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k)) ∨
      (∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
        Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
        Nonempty (minimalLocalFailureProperPairHull H z beta t ≃*
          CFSG.Blueprint.suzukiGroup m k)) := by
    rcases hmodel with ⟨-, -, -, -, k, _, _, hk, ψ, -⟩ | ⟨m, -, hQm, -, k, _, _, hk, ψ, -⟩
    · exact Or.inl ⟨k, inferInstance, inferInstance, hk, ⟨ψ⟩⟩
    · exact Or.inr ⟨m, k, inferInstance, inferInstance, hk, hk.trans hQm.symm, ⟨ψ⟩⟩
  obtain ⟨hsub, hlin⟩ := F.map_sublineL_eq hupper hlower hQK htK hK
  exact ⟨hlin, ⟨{ toUnitaryHullFrame := F, upper := hupper, lower := hlower, subline := hsub }⟩⟩

theorem exists_unitaryHullCoordinates_of_isUnitaryScalarQuotient
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hY : Y < ⊤) (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y)
    (hU : IsUnitaryScalarQuotient (Nat.card (minimalLocalFailurePairActionPointHull H z))
      (Subgroup.closure (involutionPointClass z ∩ (Y : Set G)))) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
        Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k)) ∧
      Nonempty (UnitaryHullCoordinates H z beta t
        (Subgroup.closure (involutionPointClass z ∩ (Y : Set G)))) := by
  obtain ⟨-, -, -, -, -, -, -, -, j, -, -, hΔ, -, -, -, huniq⟩ :=
    minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1 hbeta ht hproper hY
      hKY
  set L := Subgroup.closure (involutionPointClass z ∩ (Y : Set G))
  have hLY : L ≤ Y := (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hLgen : L = Subgroup.closure (involutionPointClass z ∩ (L : Set G)) := by
    refine le_antisymm (Subgroup.closure_mono fun x hx => ⟨hx.1, Subgroup.subset_closure hx⟩)
      (Subgroup.closure_mono (Set.inter_subset_inter_right _ hLY))
  obtain ⟨-, hj3⟩ := huniq L hLY hLgen hU
  subst hj3
  exact exists_unitaryHullCoordinates h hcomm hsmallerR1 hbeta ht hproper hY hKY hΔ

end CFSG.ShultStronglyClosedTI.UnitaryHulls
