module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Quasithin.Background.G2URoots
import CFSG.RankThree.PartTwo.Census.OddClassical.Main
import CFSG.LieType.Chevalley.ParabolicRadicalLevi
import CFSG.LieType.Chevalley.RootCharacterKernelProduct
import CFSG.LieType.Chevalley.OddRootPairSL2
import CFSG.Adapters.TauCetiExceptional.BridgeG2

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti
open scoped MatrixGroups

namespace Carrier

section Component

variable {M : Type} [Group M]

theorem commute_of_mem_normalizer_zpowers_of_sq {H : Type} [Group H] {t g : H} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set H)) :
    g * t = t * g := by
  have hmem := (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hsq : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
  have hcases : g * t * g⁻¹ = 1 ∨ g * t * g⁻¹ = t := by
    rw [← hk]
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, hsq, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
  rcases hcases with h | h
  · exfalso
    apply ht1
    have h' : g * t = g := by
      calc g * t = g * t * g⁻¹ * g := by group
        _ = g := by rw [h, one_mul]
    exact mul_eq_left.mp h'
  · calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h]

theorem not_isCharTwoType_of_involution_centralizer_component {C : Subgroup M} [Finite C]
    {d : M} (hdC : d ∈ C) (hd1 : d ≠ 1) (hd2 : d * d = 1) {S Q₁ Q₂ : Subgroup M}
    (hS : S = Q₁ ⊔ Q₂) (hSX : S ≤ C ⊓ Subgroup.centralizer {d})
    (hXS : C ⊓ Subgroup.centralizer {d} ≤ Subgroup.normalizer (S : Set M))
    (hQ : Q₂ ≤ Subgroup.centralizer (Q₁ : Set M)) {F : Type*} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F)
    (hodd : Odd (Nat.card F)) (e : Q₁ ≃* SL(2, F)) : ¬ IsCharTwoType C := by
  set d' : C := ⟨d, hdC⟩
  have hd1' : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hd2' : d' * d' = 1 := Subtype.ext hd2
  have hord : orderOf d' = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two, hd2']) hd1'
  set P : Subgroup C := Subgroup.zpowers d'
  set L : Subgroup C := Subgroup.normalizer (P : Set C)
  have hL : IsTwoLocal L := by
    refine ⟨P, ?_, ?_, rfl⟩
    · rwa [Ne, Subgroup.zpowers_eq_bot]
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hQ₁S : Q₁ ≤ S := hS ▸ le_sup_left
  have hSC : S ≤ C := hSX.trans inf_le_left
  have hLX : ∀ g ∈ L, (g : M) ∈ C ⊓ Subgroup.centralizer {d} := by
    intro g hg
    refine ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := commute_of_mem_normalizer_zpowers_of_sq hd1' hd2' hg
    exact congrArg Subtype.val h
  have hSL : S.subgroupOf C ≤ L := by
    intro k hk
    have hkX := hSX (Subgroup.mem_subgroupOf.mp hk)
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨n, rfl⟩
    have hc : k * d' = d' * k :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hkX.2)
    exact (Commute.zpow_left hc.symm n).eq
  have hSn : ∀ g ∈ L, ∀ k ∈ S.subgroupOf C, g * k * g⁻¹ ∈ S.subgroupOf C := by
    intro g hg k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hXS (hLX g hg)) k).mp hk
  have hQn : S ≤ Subgroup.normalizer (Q₁ : Set M) := by
    rw [hS]
    refine sup_le Subgroup.le_normalizer ?_
    exact hQ.trans (Subgroup.centralizer_le_normalizer _)
  have hJn : ∀ g ∈ S.subgroupOf C, ∀ j ∈ Q₁.subgroupOf C, g * j * g⁻¹ ∈ Q₁.subgroupOf C := by
    intro g hg j hj
    rw [Subgroup.mem_subgroupOf] at hg hj ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hQn hg) j).mp hj
  have hJK : Q₁.subgroupOf C ≤ S.subgroupOf C := Subgroup.subgroupOf_mono _ hQ₁S
  have eJ : (Q₁.subgroupOf C) ≃* SL(2, F) :=
    (Subgroup.subgroupOfEquivOfLe (hQ₁S.trans hSC)).trans e
  exact not_isCharTwoType_of_perfect_subnormal_subgroup hL hSL hSn hJK hJn
    (commutator_eq_self_of_mulEquiv_sl2 h4 eJ) (le_centralizer_of_mulEquiv_sl2 h4 hodd eJ)
    (not_isPGroup_two_of_mulEquiv_sl2 hodd eJ)

end Component

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def adjointQuotientG2Equiv (K : Type) [Field K] [Finite K] :
    AdjointQuotient .G2 K ≃* adjointGroup Tag.G2 K :=
  (QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
    QuotientGroup.quotientBot

@[expose] def signA (K : Type) [Field K] : Fin Tag.G2.rank → Kˣ :=
  ![-1, 1]

@[expose] def rootA : Fin Tag.G2.rank → ℤ :=
  ![0, 1]

@[expose] def rootB : Fin Tag.G2.rank → ℤ :=
  ![2, 3]

noncomputable abbrev rootPair (K : Type) [Field K] (γ : Fin Tag.G2.rank → ℤ) :
    Subgroup (ModGL Tag.G2 K) :=
  CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K γ ⊔
    CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (-γ)

omit [Finite K] in
theorem rootChar_signA (v : Fin Tag.G2.rank → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (signA K) v =
      (-1) ^ v ⟨0, by decide⟩ := by
  change ∏ i : Fin 2, (signA K) i ^ v i = _
  rw [Fin.prod_univ_two]
  change (-1 : Kˣ) ^ v ⟨0, by decide⟩ * (1 : Kˣ) ^ v ⟨1, by decide⟩ = _
  rw [one_zpow, mul_one]

omit [Finite K] in
theorem coords_of_mem_rootList {v : Fin Tag.G2.rank → ℤ} (hv : v ∈ CFSG.Quasithin.G2U.rootList) :
    (v ⟨0, by decide⟩ = 2 ∧ v ⟨1, by decide⟩ = 3) ∨ (v ⟨0, by decide⟩ = 1 ∧ v ⟨1, by decide⟩ = 3) ∨
      (v ⟨0, by decide⟩ = 1 ∧ v ⟨1, by decide⟩ = 2) ∨
      (v ⟨0, by decide⟩ = 1 ∧ v ⟨1, by decide⟩ = 1) ∨
      (v ⟨0, by decide⟩ = 0 ∧ v ⟨1, by decide⟩ = 1) ∨
      (v ⟨0, by decide⟩ = 1 ∧ v ⟨1, by decide⟩ = 0) ∨
      (v ⟨0, by decide⟩ = -1 ∧ v ⟨1, by decide⟩ = 0) ∨
      (v ⟨0, by decide⟩ = 0 ∧ v ⟨1, by decide⟩ = -1) ∨
      (v ⟨0, by decide⟩ = -1 ∧ v ⟨1, by decide⟩ = -1) ∨
      (v ⟨0, by decide⟩ = -1 ∧ v ⟨1, by decide⟩ = -2) ∨
      (v ⟨0, by decide⟩ = -1 ∧ v ⟨1, by decide⟩ = -3) ∨
      (v ⟨0, by decide⟩ = -2 ∧ v ⟨1, by decide⟩ = -3) := by
  simp only [CFSG.Quasithin.G2U.rootList, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

omit [Finite K] in
theorem rootCharKernel_signA (hK2 : ringChar K ≠ 2) :
    CFSG.LieType.Chevalley.rootCharKernel (signA K) = {rootA, -rootA, rootB, -rootB} := by
  have hneg : (-1 : Kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (congrArg Units.val h)
  have hodd : ∀ n : ℤ, n % 2 = 1 → (-1 : Kˣ) ^ n ≠ 1 := fun n hn h =>
    hneg (by rwa [(Int.odd_iff.mpr hn).neg_one_zpow] at h)
  have heven : ∀ n : ℤ, n % 2 = 0 → (-1 : Kˣ) ^ n = 1 := fun n hn =>
    (Int.even_iff.mpr hn).neg_one_zpow
  ext v
  simp only [CFSG.LieType.Chevalley.rootCharKernel, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, rootChar_signA, CFSG.Quasithin.G2U.isRoot_iff_mem_rootList]
  constructor
  · rintro ⟨hv, h1⟩
    simp only [CFSG.Quasithin.G2U.rootList, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | decide
      | exact absurd h1 (hodd _ (by decide))
  · rintro (rfl | rfl | rfl | rfl)
    all_goals exact ⟨by decide, heven _ (by decide)⟩

omit [Finite K] in
theorem rootSpan_signA (hK2 : ringChar K ≠ 2) :
    rootSpan Tag.G2 K (CFSG.LieType.Chevalley.rootCharKernel (signA K)) =
      rootPair K rootA ⊔ rootPair K rootB := by
  rw [rootCharKernel_signA hK2, rootSpan, iSup_insert, iSup_insert, iSup_insert, iSup_singleton,
    sup_assoc]

omit [Finite K] in
theorem rootSpan_le_toralCentralizer (a : Fin Tag.G2.rank → Kˣ) :
    rootSpan Tag.G2 K (CFSG.LieType.Chevalley.rootCharKernel a) ≤
      CFSG.LieType.Chevalley.toralCentralizer Tag.G2 K a :=
  le_trans le_sup_right (CFSG.LieType.Chevalley.toralRootGroup_le a)

omit [Finite K] in
theorem toralCentralizer_le_normalizer (a : Fin Tag.G2.rank → Kˣ) :
    CFSG.LieType.Chevalley.toralCentralizer Tag.G2 K a ≤ Subgroup.normalizer
      (rootSpan Tag.G2 K (CFSG.LieType.Chevalley.rootCharKernel a) : Set (ModGL Tag.G2 K)) := by
  rw [(CFSG.LieType.Chevalley.Chevalley_toral_centralizer_Bruhat_factors Tag.G2 K a).2.2.2]
  refine sup_le (sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
    fun _ hα => hα.1) Subgroup.le_normalizer) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨w, hw, rfl⟩
  have hS := (CFSG.LieType.Chevalley.canonical_weyl_root_transport Tag.G2 K).1 w
    (CFSG.LieType.Chevalley.rootCharKernel a) fun α hα => hα.1
  rw [CFSG.LieType.Chevalley.image_rootCharKernel hw] at hS
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg SetLike.coe hS
  rw [Subgroup.coe_map] at h
  exact h

omit [Finite K] in
theorem not_isRoot_add {γ δ : Fin Tag.G2.rank → ℤ} (hγ : γ = rootA ∨ γ = -rootA)
    (hδ : δ = rootB ∨ δ = -rootB) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot Tag.G2 (a • γ + b • δ) := by
  rw [CFSG.Quasithin.G2U.isRoot_iff_mem_rootList]
  intro hmem
  have hc := coords_of_mem_rootList hmem
  rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
  · have e0 : (a • rootA + b • rootB) ⟨0, by decide⟩ = a • (0 : ℤ) + b • (2 : ℤ) := rfl
    have e1 : (a • rootA + b • rootB) ⟨1, by decide⟩ = a • (1 : ℤ) + b • (3 : ℤ) := rfl
    rw [e0, e1] at hc
    simp only [nsmul_eq_mul] at hc
    omega
  · have e0 : (a • rootA + b • -rootB) ⟨0, by decide⟩ = a • (0 : ℤ) + b • (-2 : ℤ) := rfl
    have e1 : (a • rootA + b • -rootB) ⟨1, by decide⟩ = a • (1 : ℤ) + b • (-3 : ℤ) := rfl
    rw [e0, e1] at hc
    simp only [nsmul_eq_mul] at hc
    omega
  · have e0 : (a • -rootA + b • rootB) ⟨0, by decide⟩ = a • (0 : ℤ) + b • (2 : ℤ) := by
      change a • -(0 : ℤ) + b • (2 : ℤ) = _
      rw [neg_zero]
    have e1 : (a • -rootA + b • rootB) ⟨1, by decide⟩ = a • (-1 : ℤ) + b • (3 : ℤ) := rfl
    rw [e0, e1] at hc
    simp only [nsmul_eq_mul] at hc
    omega
  · have e0 : (a • -rootA + b • -rootB) ⟨0, by decide⟩ = a • (0 : ℤ) + b • (-2 : ℤ) := by
      change a • -(0 : ℤ) + b • (-2 : ℤ) = _
      rw [neg_zero]
    have e1 : (a • -rootA + b • -rootB) ⟨1, by decide⟩ = a • (-1 : ℤ) + b • (-3 : ℤ) := rfl
    rw [e0, e1] at hc
    simp only [nsmul_eq_mul] at hc
    omega

omit [Finite K] in
theorem rootPair_le_centralizer :
    rootPair K rootB ≤ Subgroup.centralizer (rootPair K rootA : Set (ModGL Tag.G2 K)) := by
  have hroot : ∀ γ : Fin Tag.G2.rank → ℤ, (γ = rootA ∨ γ = -rootA ∨ γ = rootB ∨
      γ = -rootB) → IsRoot Tag.G2 γ := by
    rintro γ (rfl | rfl | rfl | rfl) <;>
      exact CFSG.Quasithin.G2U.isRoot_iff_mem_rootList.mpr (by decide)
  have hcomm : ∀ γ δ : Fin Tag.G2.rank → ℤ, (γ = rootA ∨ γ = -rootA) →
      (δ = rootB ∨ δ = -rootB) →
      ∀ x ∈ CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K γ,
        ∀ y ∈ CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K δ, Commute x y := by
    intro γ δ hγ hδ
    have hγr := hroot γ (by rcases hγ with h | h <;> simp [h])
    have hδr := hroot δ (by rcases hδ with h | h <;> simp [h])
    refine CFSG.LieType.Chevalley.commute_of_forall_not_isRoot hγr hδr ?_ ?_
      (not_isRoot_add hγ hδ) K
    · rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;> decide
    · rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;> decide
  have hle : ∀ γ δ : Fin Tag.G2.rank → ℤ, (γ = rootA ∨ γ = -rootA) → (δ = rootB ∨ δ = -rootB) →
      CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K γ ≤ Subgroup.centralizer
        (CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K δ : Set (ModGL Tag.G2 K)) := by
    intro γ δ hγ hδ x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm γ δ hγ hδ x hx y hy).eq.symm
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (hle _ _ (Or.inl rfl) (Or.inl rfl)) (hle _ _ (Or.inr rfl) (Or.inl rfl))
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (hle _ _ (Or.inl rfl) (Or.inr rfl)) (hle _ _ (Or.inr rfl) (Or.inr rfl))

theorem not_isCharTwoType_adjointGroup_G2 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    ¬ IsCharTwoType (adjointGroup Tag.G2 K) := by
  have hK2 : ringChar K ≠ 2 := fun h => by
    have : Fintype K := Fintype.ofFinite K
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card] at this
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_iff.2 this)
  obtain ⟨B, hB, -⟩ :=
    (CFSG.LieType.Chevalley.G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).1
  obtain ⟨-, -, hdC, -⟩ :=
    (CFSG.LieType.Chevalley.G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).2 B hB
      (signA K)
  have hneg : (-1 : Kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (congrArg Units.val h)
  have hd1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .G2 (signA K) ≠
      1 := by
    intro h
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_one] at h
    have h0 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) ⟨0, by decide⟩
    exact hneg h0
  have hd2 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .G2 (signA K) *
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .G2 (signA K) = 1 := by
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_one]
    congr 1
    funext i
    fin_cases i
    · change (-1 : Kˣ) * (-1) = 1
      rw [neg_mul_neg, one_mul]
    · change (1 : Kˣ) * 1 = 1
      rw [one_mul]
  have hα : IsRoot Tag.G2 rootA := CFSG.Quasithin.G2U.isRoot_iff_mem_rootList.mpr (by decide)
  obtain ⟨-, ⟨eα⟩, -⟩ :=
    CFSG.LieType.Chevalley.odd_arbitrary_root_pair_SL2_p_components .G2 K hK2 hα
  exact not_isCharTwoType_of_involution_centralizer_component hdC hd1 hd2 (rootSpan_signA hK2)
    (rootSpan_le_toralCentralizer (signA K)) (toralCentralizer_le_normalizer (signA K))
    rootPair_le_centralizer h4 hodd eα.symm

theorem not_isCharTwoType_adjointQuotient_G2 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    ¬ IsCharTwoType (AdjointQuotient .G2 K) := fun h =>
  not_isCharTwoType_adjointGroup_G2 hodd h4 (isCharTwoType_of_mulEquiv (adjointQuotientG2Equiv K) h)

end G2

end Carrier

open Carrier

theorem excluded433_G2_odd (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p ≠ 2)
    (h3 : ¬ (q.p = 3 ∧ q.exponent = 1)) : Excluded433 (.lie ⟨.G2 q, hv⟩) := by
  intro G _ _ hG e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 (GaloisField q.p q.exponent) hK
  have hodd : Odd (Nat.card (GaloisField q.p q.exponent)) := by
    rw [hK, PrimePower.card_def]
    exact (q.prime_p.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hK]
    exact le_trans (by norm_num) (five_le_card_of_odd q hp2 h3)
  exact hG.false_of_not_isCharTwoType (e.trans b.symm)
    (not_isCharTwoType_adjointQuotient_G2 hodd h4)

theorem excluded433_G2_prime (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p ≠ 2)
    (hp3 : q.p ≠ 3) (_he : q.exponent = 1) : Excluded433 (.lie ⟨.G2 q, hv⟩) :=
  excluded433_G2_odd q hv hp2 fun h => hp3 h.1

end CFSG.RankThree.PartTwo.Census
