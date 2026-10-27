module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofOuter
public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddG2
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerRoots
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofThree
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriThree
public import CFSG.RankThree.PartOne.KGD.D4T36Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
  (longElt coe_longElt rootB rootC rootD fixSubgroup_conj_mul_fieldActor_eq)
open CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux (fixEquivG2 longElt_mem_fix infCentralizerEquiv)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Support


namespace RonanD4OddThree

theorem pinnedX_pow_three {K : Type} [Field K] [CharP K 3]
    (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    pinnedX TwistTag.D4.tag K α c ^ 3 = 1 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hc : c + c + c = 0 := by linear_combination c * h3
  rw [pow_three', ← pinnedX_add, ← pinnedX_add, hc, pinnedX_zero]

theorem fixSub_conj_eq_centralizer_singleton {G : Type*} [Group G] (z : G) :
    Item426.fixSub (MulAut.conj z) = Subgroup.centralizer ({z} : Set G) := by
  ext x
  rw [Item426.mem_fixSub, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * z = z * x * z⁻¹ * z := by rw [hx]
      _ = z * x := by group
  · intro hx
    calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [hx]
      _ = x := by group

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem longElt_pow_three {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) (c : K) (hc : σ c = c) :
    longElt hf hK σ hσ hγ c hc ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_longElt, pinnedX_pow_three, Subgroup.coe_one]

theorem longElt_ne_one {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) {c : K} (hc : σ c = c) (hc0 : c ≠ 0) :
    longElt hf hK σ hσ hγ c hc ≠ 1 := by
  intro h
  apply hc0
  have h1 : pinnedX TwistTag.D4.tag K γ c = 1 := by
    have := congrArg Subtype.val h
    rw [coe_longElt] at this
    exact this
  exact pinnedX_injective TwistTag.D4.tag K γ (h1.trans (pinnedX_zero TwistTag.D4.tag K γ).symm)

theorem not_hasType424_autFix_fieldActor :
    ¬ KS11Lie2Proof.HasType424 ↥(Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
  intro h
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 σ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hfix : Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) := Subgroup.ext fun _ => Iff.rfl
  have h1 := h.of_mulEquiv (MulEquiv.subgroupCongr hfix)
  have h2 := h1.of_mulEquiv (fixEquivG2 hf hK σ hσ)
  have hk : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ]
    exact Nat.le_self_pow (by omega) 3
  exact RonanD4Odd.not_hasType424_g2 hk h2

theorem not_hasType424_autFix_classB {c : K} (hc : σ c = c) (hc0 : c ≠ 0) :
    ¬ KS11Lie2Proof.HasType424 ↥(Sec4.autFix (MulAut.conj
      (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) * fieldActor (t := TwistTag.D4) σ σ)) := by
  intro h
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 σ
  set z := longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc with hzdef
  set δ₀ := fieldActor (t := TwistTag.D4) σ σ with hδ₀
  have hz : z ∈ fixSubgroup δ₀ := longElt_mem_fix hf hK σ hσ (Or.inr (Or.inr rfl)) hc
  have heq : Sec4.autFix (MulAut.conj z * δ₀) = fixSubgroup δ₀ ⊓ Subgroup.centralizer {z} := by
    rw [← fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ hc hc0]
    exact Subgroup.ext fun _ => Iff.rfl
  set e := fixEquivG2 hf hK σ hσ with he
  have h1 := h.of_mulEquiv (MulEquiv.subgroupCongr heq)
  have h2 := h1.of_mulEquiv (infCentralizerEquiv (fixSubgroup δ₀) z hz e)
  have hz1 : (⟨z, hz⟩ : ↥(fixSubgroup δ₀)) ≠ 1 := fun h' =>
    longElt_ne_one hf hK σ hσ (Or.inr (Or.inr rfl)) hc hc0 (congrArg Subtype.val h')
  have hz3 : (⟨z, hz⟩ : ↥(fixSubgroup δ₀)) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact longElt_pow_three hf hK σ hσ (Or.inr (Or.inr rfl)) c hc
  have hz'1 : e ⟨z, hz⟩ ≠ 1 := fun h' => hz1 (e.injective (h'.trans (map_one e).symm))
  have hz'3 : e ⟨z, hz⟩ ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  refine KS11Lie3Proof.not_hasType424_fixSub_g2_three hz'1 hz'3 ?_
  rw [fixSub_conj_eq_centralizer_singleton]
  exact h2

end RonanD4OddThree

end Support

theorem noOuterType424D4Three_holds :
    NoOuterType424D4Three := by
  intro Z _ _ hZ α J hα3 hαout hJ hJT
  obtain ⟨X, _, ⟨q, hq, hp3, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item1118Res3Proof.exists_d4_model_pow f e
  rw [hp3] at hK hσ
  have hq1 : 1 ≤ q.exponent := q.exponent_pos
  haveI : CharP K 3 := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exc_charP_three_of_card K hK
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 σ
  set β := MulAut.congr E α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    fun h => hαout ((KFacts.isInnerAut_congr E α).mp h)
  have hHas : KS11Lie2Proof.HasType424 (Item426.fixSub α) :=
    KS11Lie2Proof.hasType424_of_mem hJ hJT
  have hfixα : Item426.fixSub α = Sec4.autFix α := by
    ext x
    rfl
  have hHasβ : KS11Lie2Proof.HasType424 (Sec4.autFix β) := by
    rw [hfixα] at hHas
    exact hHas.of_mulEquiv (Sec4.autFixCongrEquiv E α).symm
  exact CFSG.HardMathSupport.Dickson.DefCharOuter.Export.three_of_classes_gen hq1 hK σ hσ
    (fun γ => ¬ KS11Lie2Proof.HasType424 ↥(Sec4.autFix γ))
    (fun ε γ h hγ => h (RonanD4Odd.hasType424_autFix_conj ε γ hγ))
    (fun γ h hγ => h (RonanD4Odd.hasType424_autFix_inv γ hγ))
    (RonanD4OddThree.not_hasType424_autFix_fieldActor hq1 hK σ hσ)
    (fun {c} hc hc0 => RonanD4OddThree.not_hasType424_autFix_classB hq1 hK σ hσ hc hc0)
    β hβ3 hβout hHasβ

end CFSG.RankThree.PartTwo.Sec11
