module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
import CFSG.LocalAnalysis.UniquenessCase.UCKP1
import CFSG.LocalAnalysis.UniquenessCase.UCKPAutQuot
import CFSG.RankThree.GF2n.Stroth80.FieldAut
import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

@[expose] def U3ThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n →
    ∃ (N : Subgroup (MulAut X)) (_ : N.Normal),
      (MulAut.conj : X →* MulAut X).range ≤ N ∧ IsCyclic (MulAut X ⧸ N) ∧
      ∀ R : Subgroup (MulAut X), R ≤ N → IsElemAbelian 3 R → Nat.card R ≤ 3 ^ 2

theorem u3ThreeRank : U3ThreeRank := by
  classical
  intro X _ _ n hX
  have hn2 : 2 ≤ n := u3Range X n hX
  obtain ⟨-, K, _, _, hK, ⟨ψ⟩⟩ :=
    CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hX.2
  have hu : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : Finite K := hu.finite
  have hq : 2 < 2 ^ n :=
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hK3 : 3 ∣ Nat.card K - 1 := by
    have h4 : Nat.card K = 4 ^ n := by rw [hK, ← pow_mul, mul_comm, pow_mul]; norm_num
    have h41 : 4 ^ n % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  let e : X ⧸ center X ≃* unitaryPSU hu 3 :=
    ψ.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm
  haveI hNbar : (psuConj hu).range.Normal := (stdPinnedPSU3_stable (h := hu) hq).normal
  let ε : MulAut X →* MulAut (unitaryPSU hu 3) := (MulAut.congr e).toMonoidHom.comp autQuot
  have hεinj : Function.Injective ε :=
    (MulAut.congr e).injective.comp (autQuot_injective hX.1.1)
  let χ : MulAut X →* MulAut (unitaryPSU hu 3) ⧸ (psuConj hu).range :=
    (QuotientGroup.mk' (psuConj hu).range).comp ε
  refine ⟨χ.ker, inferInstance, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have h1 : ε (MulAut.conj x) = MulAut.conj (e (QuotientGroup.mk x)) := by
      show MulAut.congr e (autQuot (MulAut.conj x)) = _
      rw [autQuot_conj, congr_mulAutConj]
    rw [h1]
    exact mem_psuConj_range_of_isInnerAut (isInnerAut_conj _)
  ·
    haveI : IsCyclic (K ≃+* K) := CFSG.RankThree.GF2n.Stroth80.isCyclic_ringEquiv K
    have hcyc : IsCyclic (MulAut (unitaryPSU hu 3) ⧸ (psuConj hu).range) := by
      refine isCyclic_of_surjective ((QuotientGroup.mk' (psuConj hu).range).comp (psuField hu)) ?_
      intro y
      induction y using QuotientGroup.induction_on with
      | H α =>
        obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
        refine ⟨σ, ?_⟩
        have hA1 : (QuotientGroup.mk (psuConj hu A) : MulAut (unitaryPSU hu 3) ⧸ (psuConj hu).range)
            = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨A, rfl⟩
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, hA1, one_mul]
    haveI : IsCyclic χ.range := Subgroup.isCyclic χ.range
    exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange χ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange χ).symm.surjective
  ·
    intro R hR hRel
    have hB : IsElemAbelian 3 (R.map ε) := CFSG.Open.IsElemAbelian.map hRel ε
    have hBD : R.map ε ≤ (psuConj hu).range := by
      rintro _ ⟨r, hr, rfl⟩
      have h1 : χ r = 1 := hR hr
      rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hcomm := hB.1
    have h9 := card_le_nine_of_le_psuConj_range hK3 (R.map ε) hBD
      (fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : R.map ε) ⟨y, hy⟩)) hB.2
    rw [Subgroup.card_map_of_injective hεinj] at h9
    simpa using h9

end CFSG.LocalAnalysis.UniquenessCase.UCK
