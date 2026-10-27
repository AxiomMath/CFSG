module

public import CFSG.RankThree.GF2n.Tim77Prop24Conj
public import CFSG.CGT.Timmesfeld75.Inputs214
public import CFSG.RankThree.GF2n.BenderStrongWC
import CFSG.CGT.Timmesfeld75.Core214Proof
import CFSG.CGT.Timmesfeld75.AschbacherNoPolarDischarge
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.Timmesfeld75.Config214
public import CFSG.CGT.Timmesfeld75.Sec25
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.CGT.Timmesfeld75.ZStarSmall
public import CFSG.Foundations
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.RankOne
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem isElemAbelian_subgroupOf {A : Subgroup G} (hA : Assembly.IsElemAbelian 2 A)
    (X : Subgroup G) : IsElemAbelian 2 (A.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hA X

theorem isElemAbelian_map' {H K : Type*} [Group H] [Group K] {T : Subgroup H}
    (hT : IsElemAbelian 2 T) (f : H →* K) : IsElemAbelian 2 (T.map f) :=
  CFSG.SectionRank.isElemAbelian_map hT _

variable [Finite G]

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

omit [Finite G] in
theorem M_le_X : M ≤ A ⊔ Ab :=
  S.hM ▸ sup_le (S.L_le.trans le_sup_left) (S.Lb_le.trans le_sup_right)

theorem normal_subgroupOf : (M.subgroupOf (A ⊔ Ab)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer S.M_le_X).mpr S.sup_le_normalizer_M

section Image

variable [(M.subgroupOf (A ⊔ Ab)).Normal]

local notation "πq" => QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))

omit S [Finite G] in
theorem mk_eq_one_iff (y : ↥(A ⊔ Ab)) : πq y = 1 ↔ (y : G) ∈ M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem exists_image_conj : ∃ x : ↥(A ⊔ Ab),
    (Ab.subgroupOf (A ⊔ Ab)).map πq = conjSubgroup (πq x) ((A.subgroupOf (A ⊔ Ab)).map πq) := by
  obtain ⟨x, hxX, hx⟩ := S.exists_conj_eq
  refine ⟨⟨x, hxX⟩, ?_⟩
  have hmem : ∀ z : G, z ∈ Ab ↔ x⁻¹ * z * x ∈ A := fun z => by rw [hx, mem_conjSubgroup]
  have hAbconj : Ab.subgroupOf (A ⊔ Ab) = conjSubgroup ⟨x, hxX⟩ (A.subgroupOf (A ⊔ Ab)) := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_conjSubgroup, Subgroup.mem_subgroupOf, hmem]
    rfl
  rw [hAbconj, map_conjSubgroup]

omit S [Finite G] in
theorem image_sup : (A.subgroupOf (A ⊔ Ab)).map πq ⊔ (Ab.subgroupOf (A ⊔ Ab)).map πq = ⊤ := by
  rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem mk_not_mem_image {b : G} (hb : b ∈ Ab) (hbL : b ∉ Lb) :
    πq ⟨b, le_sup_right (a := A) hb⟩ ∉ (A.subgroupOf (A ⊔ Ab)).map πq := by
  rintro ⟨a, ha, hab⟩
  have hm : (a : G)⁻¹ * b ∈ M := by
    have h1 := (QuotientGroup.eq.mp hab)
    rwa [Subgroup.mem_subgroupOf] at h1
  obtain ⟨l, hl, lb, hlb, hm'⟩ := S.exists_mul_of_mem_M hm
  have e : b * lb⁻¹ = (a : G) * l := by
    have : b = (a : G) * (l * lb) := by rw [← hm']; group
    rw [this]; group
  have h1 : b * lb⁻¹ ∈ A ⊓ Ab := Subgroup.mem_inf.mpr
    ⟨e ▸ A.mul_mem (Subgroup.mem_subgroupOf.mp ha) (S.L_le hl),
      Ab.mul_mem hb (Ab.inv_mem (S.Lb_le hlb))⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact hbL (h1 ▸ hlb)

theorem strongWC_image : StrongWC ((A.subgroupOf (A ⊔ Ab)).map πq) := by
  have hπs : Function.Surjective πq := QuotientGroup.mk'_surjective _
  refine ⟨isElemAbelian_map' (isElemAbelian_subgroupOf S.elem _) _, ?_⟩
  intro t' ht' ht'1 a' ha' g' hg'
  obtain ⟨t, ht, rfl⟩ := ht'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨g, rfl⟩ := hπs g'
  have e : (πq g)⁻¹ * πq a * πq g = πq (g⁻¹ * a * g) := by rw [map_mul, map_mul, map_inv]
  rw [e] at hg' ⊢
  rw [Subgroup.mem_centralizer_singleton_iff] at hg'
  have htA : (t : G) ∈ A := Subgroup.mem_subgroupOf.mp ht
  have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have htM : (t : G) ∉ M := fun h => ht'1 ((mk_eq_one_iff t).mpr h)
  have htL : (t : G) ∉ L := fun h => htM (S.L_le_M h)
  by_cases haM : (a : G) ∈ M
  · have h1 : πq (g⁻¹ * a * g) = 1 := by
      rw [map_mul, map_mul, map_inv, (mk_eq_one_iff a).mpr haM, mul_one, inv_mul_cancel]
    rw [h1]
    exact Subgroup.one_mem _
  · have haL : (a : G) ∉ L := fun h => haM (S.L_le_M h)
    have hcomm : (t : G) * ((g : G)⁻¹ * a * g) * (t : G)⁻¹ * ((g : G)⁻¹ * a * g)⁻¹ ∈ M := by
      have h2 : πq (t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hg', mul_inv_cancel_right,
          mul_inv_cancel]
      have := (mk_eq_one_iff _).mp h2
      simpa using this
    have hyA := S.conj_mem_of_commutator_mem (S.sup_le_normalizer_M g.2) htA htL haA haL hcomm
    exact ⟨g⁻¹ * a * g, Subgroup.mem_subgroupOf.mpr (by simpa using hyA), rfl⟩

theorem image_ne_bot : (A.subgroupOf (A ⊔ Ab)).map πq ≠ ⊥ := by
  obtain ⟨a₀, ha₀, ha₀L⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  intro h
  have : πq ⟨a₀, le_sup_left (b := Ab) ha₀⟩ ∈ (A.subgroupOf (A ⊔ Ab)).map πq :=
    ⟨⟨a₀, le_sup_left (b := Ab) ha₀⟩, ha₀, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact ha₀L (S.inf_M ▸ Subgroup.mem_inf.mpr ⟨ha₀, (mk_eq_one_iff _).mp this⟩)

theorem normalClosure_image :
    Subgroup.normalClosure
      (((A.subgroupOf (A ⊔ Ab)).map πq : Subgroup (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab))) :
        Set (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab))) = ⊤ := by
  obtain ⟨x, hx⟩ := S.exists_image_conj
  rw [eq_top_iff, ← image_sup, hx]
  exact sup_le Subgroup.le_normalClosure (conjSubgroup_le_normalClosure _ _)

theorem not_normal_image :
    ¬ ∀ g, conjSubgroup g ((A.subgroupOf (A ⊔ Ab)).map πq) =
      (A.subgroupOf (A ⊔ Ab)).map πq := by
  obtain ⟨x, hx⟩ := S.exists_image_conj
  obtain ⟨b₀, hb₀, hb₀L⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  intro h
  apply S.mk_not_mem_image hb₀ hb₀L
  rw [← h (πq x), ← hx]
  exact ⟨⟨b₀, _⟩, hb₀, rfl⟩

theorem exists_sup_conj_image : ∃ g,
    (A.subgroupOf (A ⊔ Ab)).map πq ⊔ conjSubgroup g ((A.subgroupOf (A ⊔ Ab)).map πq) = ⊤ := by
  obtain ⟨x, hx⟩ := S.exists_image_conj
  exact ⟨πq x, by rw [← hx]; exact image_sup⟩

theorem odd_orderOf_image {a b : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab)}
    (ha : a ∈ (A.subgroupOf (A ⊔ Ab)).map πq) (ha1 : a ≠ 1)
    (hb : b ∈ (Ab.subgroupOf (A ⊔ Ab)).map πq) (hb1 : b ≠ 1) : Odd (orderOf (a * b)) := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  have haL : (a : G) ∉ L := fun h => ha1 ((mk_eq_one_iff a).mpr (S.L_le_M h))
  have hbL : (b : G) ∉ Lb := fun h => hb1 ((mk_eq_one_iff b).mpr (S.Lb_le_M h))
  have h1 := S.odd_orderOf_mul (Subgroup.mem_subgroupOf.mp ha) haL
    (Subgroup.mem_subgroupOf.mp hb) hbL
  have h2 : orderOf (a * b) = orderOf ((a : G) * b) := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
  rw [← map_mul]
  exact Odd.of_dvd_nat (h2 ▸ h1) (orderOf_map_dvd _ (a * b))

theorem card_image_mul : Nat.card ((A.subgroupOf (A ⊔ Ab)).map πq) * Nat.card L = Nat.card A := by
  set φ := MonoidHom.comp πq (A.subgroupOf (A ⊔ Ab)).subtype with hφ
  have hrange : φ.range = (A.subgroupOf (A ⊔ Ab)).map πq := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card L := by
    refine Nat.card_congr
      { toFun := fun y => ⟨((y : ↥(A ⊔ Ab)) : G), ?_⟩
        invFun := fun l => ⟨⟨⟨l, le_sup_left (b := Ab) (S.L_le l.2)⟩, S.L_le l.2⟩, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun l => rfl }
    · have hy : πq ((y : ↥(A.subgroupOf (A ⊔ Ab))) : ↥(A ⊔ Ab)) = 1 := y.2
      rw [mk_eq_one_iff] at hy
      exact S.inf_M ▸ Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp y.1.2, hy⟩
    · show πq _ = 1
      rw [mk_eq_one_iff]
      exact S.L_le_M l.2
  have hdom : Nat.card ↥(A.subgroupOf (A ⊔ Ab)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, hker, hdom] at h1
  rw [mul_comm]
  exact h1

theorem relIndex_eq_card_image :
    L.relIndex A = Nat.card ((A.subgroupOf (A ⊔ Ab)).map πq) := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [inf_of_le_left S.L_le, ← S.card_image_mul] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

end Image

theorem exists_models (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∃ _ : (M.subgroupOf (A ⊔ Ab)).Normal,
      (∀ K : Subgroup (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab)), K.Normal → IsPGroup 2 K → K = ⊥) ∧
      ((∃ f : ℕ, 2 ≤ f ∧
          Nonempty (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* Sz a)) ∨
        (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧
          Nonempty (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* DihedralGroup n))) := by
  have hN := S.normal_subgroupOf
  refine ⟨hN, ?_⟩
  have hS := S.strongWC_image
  have hT0 := S.image_ne_bot
  have hK := S.normalClosure_image
  obtain ⟨b₀, hb₀, hb₀L⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  rcases lemma25_top aschbacherNoPolarInput_of_repo hS hK with hZ | hB
  · obtain ⟨n, hn, h3, ⟨e⟩⟩ := exists_dihedral_of_zStar hS.1
      (isElemAbelian_map' (isElemAbelian_subgroupOf S.elem_Ab _) _) image_sup hZ hT0
      (fun hle => S.mk_not_mem_image hb₀ hb₀L (hle ⟨⟨b₀, _⟩, hb₀, rfl⟩))
      fun a ha ha1 b hb hb1 => S.odd_orderOf_image ha ha1 hb hb1
    exact ⟨fun K _ hK2 => eq_bot_of_dihedral hn h3 e K hK2, Or.inr (Or.inr ⟨n, hn, h3, ⟨e.symm⟩⟩)⟩
  · obtain ⟨hO2, hmod⟩ := models_of_isBenderGroup hCen hU hS hT0 S.not_normal_image hK
      S.exists_sup_conj_image hB
    exact ⟨hO2, hmod.imp id Or.inl⟩

theorem tim77_2_4_one (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∃ _ : (M.subgroupOf (A ⊔ Ab)).Normal,
      (∀ K : Subgroup (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab)), K.Normal → IsPGroup 2 K → K = ⊥) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ L.relIndex A = 2 ^ f ∧
          Nonempty (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ L.relIndex A = 2 ^ (2 * a + 1) ∧
          Nonempty (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* Sz a)) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ L.relIndex A = 2 ∧
          Nonempty (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* DihedralGroup m))) := by
  obtain ⟨hN, hO2, hmod⟩ := S.exists_models hCen hU
  refine ⟨hN, hO2, ?_⟩
  have hS := S.strongWC_image
  have hT0 := S.image_ne_bot
  rw [S.relIndex_eq_card_image]
  rcases hmod with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ | ⟨m, hm, h3, ⟨e⟩⟩
  · exact Or.inl ⟨f, hf, card_eq_of_strongWC (.linear f hf e) hS hT0, ⟨e⟩⟩
  · have e' := e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)
    exact Or.inr (Or.inl ⟨a, ha, card_eq_of_strongWC (.suzuki a ha e') hS hT0, ⟨e⟩⟩)
  · exact Or.inr (Or.inr ⟨m, hm, h3,
      card_eq_two_of_dihedral hm e (isPGroup_of_strongWC hS) hT0, ⟨e⟩⟩)

end Prop24Setup

end CFSG.RankThree.GF2n.Tim77
