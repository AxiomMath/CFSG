module

import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec3.Sims321Action
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Late.Defs

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem Hyp1921.center_quot_eq_bot (h : Hyp1921 G A M N L) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  obtain ⟨φ⟩ := h.quotient_iso
  let e := φ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))
  have h1 := Subgroup.map_center_eq e
  rw [Sec3.Sims321.center_projectiveSL_eq_bot (n := 2)] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

theorem Hyp1921.mem_pCoreOf_of_commutator_mem (h : Hyp1921 G A M N L) {x : G} (hxL : x ∈ L)
    (hx : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    x ∈ CFSG.Open.pCoreOf 2 L := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hcen : π ⟨x, hxL⟩ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have h1 : (⟨x, hxL⟩ * l * ⟨x, hxL⟩⁻¹ * l⁻¹ : L) ∈ CFSG.pCore 2 ↥L :=
      (CFSG.mem_openPCoreOf_iff _).mp (hx l l.2)
    have h2 : π (⟨x, hxL⟩ * l * ⟨x, hxL⟩⁻¹ * l⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)).symm
  rw [h.center_quot_eq_bot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hcen
  exact (CFSG.mem_openPCoreOf_iff (⟨x, hxL⟩ : L)).mpr hcen

theorem Hyp1921.isElemAbelian_of_card_eq_nine (h : Hyp1921 G A M N L) {B : Subgroup G}
    (hBL : B ≤ L) (hB : Nat.card B = 9) : CFSG.Open.IsElemAbelian 3 B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.quotient_iso
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by simp [hB])
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : B →* projectiveSL 3 (GaloisField 2 2),
      ∀ x : B, Ψ x = KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)
        (e (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.inclusion hBL x))) :=
    ⟨(KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).toMonoidHom.comp
      (e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hBL))),
      fun x => rfl⟩
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hΨ] at hx
    have h1 : e (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.inclusion hBL x)) = 1 :=
      (MulEquiv.map_eq_one_iff (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))).mp hx
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.inclusion hBL x) = 1 :=
      (MulEquiv.map_eq_one_iff e).mp h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 : (x : G) ∈ CFSG.Open.pCoreOf 2 L :=
      (CFSG.mem_openPCoreOf_iff (Subgroup.inclusion hBL x)).mpr h2
    have h4 : B ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
      Subgroup.card_eq_one.mp (Sec20.card_inf_eq_one_of_isPGroup hB3
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L))
    have h5 : (x : G) ∈ B ⊓ CFSG.Open.pCoreOf 2 L := Subgroup.mem_inf.mpr ⟨x.2, h3⟩
    rw [h4, Subgroup.mem_bot] at h5
    exact Subtype.ext h5
  have hcard : Nat.card Ψ.range = 9 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, hB]
  have hEl : CFSG.Open.IsElemAbelian 3 Ψ.range :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (KFacts.L34.isElementaryAbelian_of_card_eq_nine KFacts.L34.card_galoisField_two_two hcard)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · show a * b = b * a
    apply hinj
    have hc : Ψ a * Ψ b = Ψ b * Ψ a :=
      congrArg Subtype.val (hEl.1.is_comm.comm ⟨Ψ a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
        ⟨Ψ b, MonoidHom.mem_range.mpr ⟨b, rfl⟩⟩)
    rw [map_mul, map_mul]
    exact hc
  · have hx' : (⟨x, hx⟩ : B) ^ 3 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact hEl.2 (Ψ ⟨x, hx⟩) (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
    simpa using congrArg Subtype.val hx'

theorem Hyp1921.exists_elemAbelian_card_nine (h : Hyp1921 G A M N L) :
    ∃ F : Subgroup G, F ≤ L ∧ CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.quotient_iso
  obtain ⟨F, hF⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  have hFL : F ≤ L := by
    obtain ⟨Q, rfl⟩ := hF
    exact Subgroup.map_subtype_le _
  have hcard : Nat.card F = 9 := by
    rw [hF.card_eq, Sec20.factorization_three_of_nonempty_quotient e] <;> norm_num
  exact ⟨F, hFL, h.isElemAbelian_of_card_eq_nine hFL hcard, hcard⟩

end CFSG.RankThree.PartTwo.Late
