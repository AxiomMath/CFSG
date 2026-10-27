module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieFinal
public import CFSG.RankThree.GF2n.Tim78P214
public import CFSG.GroupTheory.TISylowNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.RankTwoOddLie
open CFSG.ABGLocalTools
open CFSG.RankThree.GF2n.Tim78
open scoped MatrixGroups

theorem w10_4_9_nonabelian {Y : Type} [Group Y] [Finite Y] {Kb Tb : Subgroup Y}
    (hKbNorm : Kb.Normal) (hKbSimple : IsSimpleGroup ↥Kb)
    (hTb : IsElemAbelian 2 Tb) (h4 : 4 ≤ Nat.card Tb)
    (hfaith : Tb ⊓ centralizer (Kb : Set Y) = ⊥) :
    ∃ a b : ↥Kb, a * b ≠ b * a := by
  by_contra hnab
  have hcomm : ∀ a b : ↥Kb, a * b = b * a := by
    intro a b
    by_contra h
    exact hnab ⟨a, b, h⟩
  have : IsMulCommutative ↥Kb := ⟨⟨hcomm⟩⟩
  have : Kb.Normal := hKbNorm
  have hprime : Nat.Prime (Nat.card ↥Kb) := (Group.is_simple_iff_prime_card).mp hKbSimple
  have hcyc : IsCyclic ↥Kb := by
    have : Fact (Nat.card ↥Kb).Prime := ⟨hprime⟩
    exact isCyclic_of_prime_card rfl
  let φ : ↥Tb →* MulAut ↥Kb := (MulAut.conjNormal (H := Kb)).comp Tb.subtype
  have hφker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have hcent : (t : Y) ∈ centralizer (Kb : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have heval := congrArg (fun σ : MulAut ↥Kb => ((σ ⟨k, hk⟩ : ↥Kb) : Y)) ht
      simp only [φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at heval
      have heval' : (t : Y) * k * (t : Y)⁻¹ = k := by simpa using heval
      calc k * (t : Y) = ((t : Y) * k * (t : Y)⁻¹) * (t : Y) := by rw [heval']
        _ = (t : Y) * k := by group
    apply Subtype.ext
    have ht' : (t : Y) ∈ Tb ⊓ centralizer (Kb : Set Y) := ⟨t.2, hcent⟩
    rw [hfaith] at ht'
    exact Subgroup.mem_bot.mp ht'
  let ψ : ↥Tb →* (ZMod (Nat.card ↥Kb))ˣ :=
    (IsCyclic.mulAutMulEquiv ↥Kb).toMonoidHom.comp φ
  have hψker : ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have hφ : φ t = 1 := (IsCyclic.mulAutMulEquiv ↥Kb).injective (by simpa [ψ] using ht)
    have hmem : t ∈ φ.ker := MonoidHom.mem_ker.mpr hφ
    rw [hφker] at hmem
    exact hmem
  have : IsCyclic ((ZMod (Nat.card ↥Kb))ˣ) := ZMod.isCyclic_units_prime hprime
  have : IsCyclic ψ.range := Subgroup.isCyclic ψ.range
  have hexp : Monoid.exponent ψ.range ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
    intro x
    obtain ⟨t, ht⟩ := x.2
    have ht2 : t ^ 2 = 1 := Subtype.ext (by simpa using hTb.2 (t : Y) t.2)
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← ht, ← map_pow, ht2, map_one]
  have hcardA : Nat.card ψ.range ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact hexp
  have hle : Nat.card ψ.range ≤ 2 := Nat.le_of_dvd (by norm_num) hcardA
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hψker, Subgroup.card_bot, one_mul] at hcard
  omega

section W10


theorem w10_4_9_of (hI : CFSG.ComponentClassification.RankTwoOddLie.OddLieInputs)
    (hHRD : CFSG.ComponentClassification.RankTwoOddLie.ModelHighestRootData) : W10_4_9 := by
  intro Y _ _ Kb Tb hKbNorm hKbSimple hChev hTb h4 hfaith hsup hTI
  have hnonab := w10_4_9_nonabelian hKbNorm hKbSimple hTb h4 hfaith
  have : IsSimpleGroup ↥Kb := hKbSimple
  obtain ⟨hqs, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab
  have hB : CFSG.Open.IsQuasisimple ↥Kb :=
    ⟨Group.isPerfect_def.1 hqs.1, hqs.2.1⟩
  obtain ⟨q, hq, hq2, t, n, f, hadm, hmodel⟩ := hChev
  have hL : CFSG.Blueprint.OddLieType (↥Kb ⧸ center ↥Kb) := by
    refine ⟨t, n, q, f, hq, hq2, hadm, ?_⟩
    let e : ↥Kb ⧸ center ↥Kb ≃* ↥Kb :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hmodel
  have h46 : Hyp46 Kb Tb Tb := by
    refine ⟨hTb, h4, ?_, hfaith, le_sup_left, ?_, ?_, ?_⟩
    · exact Subgroup.le_normalizer_of_normal
    · refine (isSylowOf_iff).mpr ⟨le_rfl, hTb.isPGroup, ?_⟩
      simp
    · refine ⟨⊥, bot_le, ?_, by simp, ?_⟩
      · infer_instance
      · obtain ⟨k, hk⟩ := hTb.isPGroup.exists_card_eq
        exact ⟨k, by rw [Subgroup.relIndex_bot_left, hk]⟩
    · refine tightlyEmbedded_of_isTI ?_ ?_ (hTI.subgroupOf (Tb ⊔ Kb))
      · exact hTb.isPGroup.comap_subtype
      · intro hbot
        have hTbot : Tb = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le le_sup_left
        rw [hTbot, Subgroup.card_bot] at h4
        omega
  obtain ⟨-, p, f, hpFact, hp2, hf, hq5, ⟨e⟩, -, -⟩ :=
    h46.as76b_4_9_general hI hHRD hB hL
  have : Fact p.Prime := hpFact
  have hcardK : Nat.card ↥Kb = Nat.card (↥Kb ⧸ center ↥Kb) := by
    let e0 : ↥Kb ⧸ center ↥Kb ≃* ↥Kb :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact (Nat.card_congr e0.toEquiv).symm
  have hcardPSL : Nat.card ↥Kb = Nat.card (PSL(2, GaloisField p f)) := by
    rw [hcardK]
    exact Nat.card_congr e.toEquiv
  have hcardformula := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := p) (m := f)
    hp2 (by omega)
  rw [hcardPSL, hcardformula]
  have hsq : p ^ (2 * f) = (p ^ f) ^ 2 := by
    rw [mul_comm 2 f, pow_mul]
  rw [hsq]
  have hq5' : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 := by simpa using hq5
  rcases hq5' with h | h | h <;> rw [h] <;> norm_num

end W10

section W10holds


theorem w10_4_9_holds : W10_4_9 :=
  w10_4_9_of CFSG.ComponentClassification.RankTwoOddLie.oddLieInputs
    CFSG.ComponentClassification.RankTwoOddLie.modelHighestRootData

end W10holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
