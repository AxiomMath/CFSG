module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofNorm
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)
open scoped Pointwise

namespace Proof1617

theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] {A C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (C ⊔ A : Subgroup G) * Nat.card (A ⊓ C : Subgroup G) =
      Nat.card A * Nat.card C := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hC
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h2, h3, h1, h4, Nat.card_congr e.toEquiv]
  ring

theorem card_eq_card_range_mul_card_ker {H M : Type*} [Group H] [Group M] (f : H →* M) :
    Nat.card H = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem card_comap_of_le_range {H M : Type*} [Group H] [Group M] (f : H →* M) {K : Subgroup M}
    (hK : K ≤ f.range) : Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  set g : K.comap f →* M := f.comp (K.comap f).subtype with hg
  have hrange : g.range = K := by
    ext m
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact hy
    · intro hm
      obtain ⟨y, rfl⟩ := hK hm
      exact ⟨⟨y, hm⟩, rfl⟩
  have hker : Nat.card g.ker = Nat.card f.ker := by
    have hle : f.ker ≤ K.comap f := fun y hy => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hy]
      exact K.one_mem
    have : g.ker = f.ker.subgroupOf (K.comap f) := by
      ext ⟨y, hy⟩
      simp [hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [card_eq_card_range_mul_card_ker g, hrange, hker]

variable {G : Type} [Group G] [Finite G]

theorem thetaQuotMulAut_eq_one_iff {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨y, hy⟩) = 1 ↔
      ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
  have : (aschbacherSolvableCore 3 ↥L).Normal := by
    have := Sec4.aschbacherSolvableCore_characteristic ↥L
    infer_instance
  constructor
  · intro h1 l hl
    have h2 := congrArg (fun σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) =>
      σ ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) h1
    simp only [Sec4.thetaQuotMulAut_mk, MulAut.one_apply] at h2
    rw [QuotientGroup.eq] at h2
    set m := L.normalizerMonoidHom ⟨y, hy⟩ ⟨l, hl⟩ with hm
    have hm' : (m : G) = y * l * y⁻¹ := Sec4.normalizerMonoidHom_apply_coe hy _
    have h3 : m * (⟨l, hl⟩ : ↥L)⁻¹ ∈ aschbacherSolvableCore 3 ↥L := by
      have h4 := Subgroup.Normal.conj_mem this _ h2 (⟨l, hl⟩ : ↥L)
      have h5 := (aschbacherSolvableCore 3 ↥L).inv_mem h4
      have heq : ((⟨l, hl⟩ : ↥L) * (m⁻¹ * ⟨l, hl⟩) * (⟨l, hl⟩ : ↥L)⁻¹)⁻¹ =
          m * (⟨l, hl⟩ : ↥L)⁻¹ := by group
      rwa [heq] at h5
    refine ⟨_, h3, ?_⟩
    simp [hm']
  · intro h1
    ext z
    induction z using QuotientGroup.induction_on with
    | H l =>
      rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply, QuotientGroup.eq]
      obtain ⟨t, ht, hte⟩ := h1 l l.2
      set m := L.normalizerMonoidHom ⟨y, hy⟩ l with hm
      have hm' : (m : G) = y * l * y⁻¹ := Sec4.normalizerMonoidHom_apply_coe hy _
      have htm : t = m * l⁻¹ := Subtype.ext (by simpa [hm'] using hte)
      rw [htm] at ht
      have h4 := Subgroup.Normal.conj_mem this _ ((aschbacherSolvableCore 3 ↥L).inv_mem ht) l⁻¹
      have heq : l⁻¹ * (m * l⁻¹)⁻¹ * l⁻¹⁻¹ = m⁻¹ * l := by group
      rwa [heq] at h4

end Proof1617

open Proof1617

variable {G : Type} [Group G] [Finite G]

end CFSG.RankThree.PartTwo.Sec16
