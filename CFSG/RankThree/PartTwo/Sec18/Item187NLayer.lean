module

public import Certificates.Certificate43
public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
import CFSG.RankThree.Transfer.Yoshida
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofComp
import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Permutation.FiveTransitive.CoprimeAutomorphismDisplacement
import CFSG.RankThree.PartTwo.KFacts.KP10LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Cert43

variable {Y : Type*} [Group Y] [Finite Y]

theorem hasNormalPComplement_two_of_layer_eq_bot
    (h2 : CFSG.pCore 2 Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    (hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ 2)
    (hlayer : layer Y = ⊥) : CFSG.HasNormalPComplement 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := CFSG.GH74.GLS.oResidual 2 Y with hUdef
  have hU : ∀ u ∈ U, u ^ 2 = 1 → u = 1 := by
    intro u hu hu2
    have hcen : ∀ r : ℕ, r.Prime → u ∈ Subgroup.centralizer (CFSG.pCore r Y : Set Y) := by
      intro r hr
      have : Fact r.Prime := ⟨hr⟩
      by_cases hr2 : r = 2
      · subst hr2
        rw [h2, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
        rw [hh, one_mul, mul_one]
      by_cases hr3 : r = 3
      · subst hr3
        have hP1 : CFSG.pCore 3 Y = ⊥ := by
          rcases (CFSG.pCore_isPGroup (p := 3) (G := Y)).card_eq_or_dvd with h1 | h1
          · exact Subgroup.card_eq_one.mp h1
          · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card _)) h3
        rw [hP1, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
        rw [hh, one_mul, mul_one]
      have hr5 : 3 < r := by
        have := hr.two_le
        by_contra hle
        interval_cases r <;> simp_all
      have : (CFSG.pCore r Y).Normal := CFSG.pCore_normal
      obtain ⟨k, hk, φ, hφ⟩ := Sec16.Crit167.exists_rep hr2 (CFSG.pCore r Y) CFSG.pCore_isPGroup
        ((CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (hrank r hr hr5))
      refine hφ u ?_ ?_
      · have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
        exact Nat.Coprime.coprime_dvd_left h1
          ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
      · have hJ3 : ¬ 3 ∣ Nat.card φ.range := fun h =>
          h3 (h.trans (Subgroup.card_dvd_of_surjective (f := φ.rangeRestrict)
            φ.rangeRestrict_surjective))
        have hN := Sec16.Crit167.hasNormalPComplement_two_of_le_two hk φ.range hJ3
        have h1 := Sec16.Crit167.eq_one_of_mem_oResidual_of_hasNormalPComplement hN
          (Sec16.Crit167.rangeRestrict_mem_oResidual φ hu) (n := 1)
          (by rw [pow_one, ← map_pow, hu2, map_one])
        exact congrArg Subtype.val h1
    have hCF : Subgroup.centralizer (CFSG.fittingSubgroup Y : Set Y) ≤
        CFSG.fittingSubgroup Y := by
      have h := CFSG.centralizer_generalizedFitting_le Y
      rwa [CFSG.generalizedFitting.eq_sup, hlayer, sup_bot_eq] at h
    exact Sec16.Crit167.eq_one_of_mem_fittingSubgroup h2
      (hCF (Sec16.Crit167.mem_centralizer_fittingSubgroup hcen)) (n := 1)
      (by rw [pow_one]; exact hu2)
  have hUodd : Nat.Coprime 2 (Nat.card U) := KFacts.KP10.coprime_two_card_of_forall hU
  have : U.Normal := Sec16.Crit167.oResidual_two_normal
  exact ⟨U, this, hUodd, CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le U le_rfl⟩

theorem isSolvable_of_layer_eq_bot
    (h2 : CFSG.pCore 2 Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    (hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ 2)
    (hlayer : layer Y = ⊥) : Group.IsSolvable Y := by
  obtain ⟨U, hUn, hUodd, hq⟩ := hasNormalPComplement_two_of_layer_eq_bot h2 h3 hrank hlayer
  haveI : Group.IsSolvable U :=
    CFSG.Milestones.odd_order_solvable (Nat.coprime_two_left.mp hUodd)
  haveI := hq.isNilpotent
  haveI : Group.IsSolvable (Y ⧸ U) := inferInstance
  exact Group.isSolvable_of_ker_le_range U.subtype (QuotientGroup.mk' U)
    (by simp [QuotientGroup.ker_mk'])

theorem layer_ne_bot_of_not_isSolvable
    (h2 : CFSG.pCore 2 Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    (hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ 2)
    (hns : ¬ Group.IsSolvable Y) : layer Y ≠ ⊥ :=
  fun h => hns (isSolvable_of_layer_eq_bot h2 h3 hrank h)

end Cert43

section Layer

variable {Y : Type*} [Group Y] [Finite Y]

theorem two_dvd_card_layer (hl : layer Y ≠ ⊥) : 2 ∣ Nat.card (layer Y) := by
  have hex : ∃ K : Subgroup Y, IsComponent K := by
    by_contra hno
    apply hl
    have hE : {K : Subgroup Y | IsComponent K} = ∅ := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hK => hno ⟨K, hK⟩
    show sSup {K : Subgroup Y | IsComponent K} = ⊥
    rw [hE, sSup_empty]
  obtain ⟨K, hK⟩ := hex
  have hKnt : Nontrivial K := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    obtain ⟨a, b, hab⟩ := hK.1.2.2
    have : Subsingleton (K ⧸ Subgroup.center K) :=
      (QuotientGroup.mk'_surjective (Subgroup.center K)).subsingleton
    exact hab (Subsingleton.elim _ _)
  have hperf : Group.IsPerfect K := hK.1.1
  have hns : ¬ Group.IsSolvable K := fun hs => by
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial K
    rw [hperf.commutator_eq_top] at this
    exact lt_irrefl _ this
  have hev : Even (Nat.card K) := by
    by_contra h
    exact hns (CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.mp h))
  exact (even_iff_two_dvd.mp hev).trans (Subgroup.card_dvd_of_le (le_sSup hK))

theorem layer_inf_ne_bot_of_isSylowOf (hl : layer Y ≠ ⊥) {T : Subgroup Y}
    (hT : IsSylowOf 2 T ⊤) : layer Y ⊓ T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := CFSG.LocalCores.layer_characteristic (G := Y)
  haveI : (layer Y).Normal := inferInstance
  have hS : IsSylowOf 2 (T ⊓ layer Y) (layer Y) :=
    hT.inf_of_le_normalizer le_top (by simp [Subgroup.normalizer_eq_top])
  intro hbot
  have hrel := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
  rw [inf_comm, hbot, Subgroup.relIndex_bot_left] at hrel
  exact hrel (two_dvd_card_layer hl)

theorem fittingSubgroup_le_layer (h2 : CFSG.pCore 2 Y = ⊥) {T : Subgroup Y}
    (hT : IsPGroup 2 T) (hY : layer Y ⊔ T = ⊤) : fittingSubgroup Y ≤ layer Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := CFSG.LocalCores.layer_characteristic (G := Y)
  haveI : (layer Y).Normal := inferInstance
  have h1 : (layer Y ⊔ T).map (QuotientGroup.mk' (layer Y)) = ⊤ := by
    rw [hY, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
  have hq : IsPGroup 2 (Y ⧸ layer Y) := by
    have hp : IsPGroup 2 (T.map (QuotientGroup.mk' (layer Y))) := hT.map _
    rw [h1] at hp
    exact hp.of_equiv Subgroup.topEquiv
  intro f hf
  exact Sec16.Crit167.oResidual_two_le_of_isPGroup_quotient hq
    (Sec16.Comp167.fittingSubgroup_le_oResidual h2 hf)

theorem eq_one_of_forall_apply_eq_generalizedFitting (h3 : ¬ 3 ∣ Nat.card Y)
    (σ : MulAut Y) (hσ : σ ^ 3 = 1) (hfix : ∀ z ∈ generalizedFitting Y, σ z = z) :
    σ = 1 := by
  have hN : (generalizedFitting Y).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Y)).2
  refine FiveTransitive.CoprimeAutomorphismDisplacement.eq_one_of_quotient
    (generalizedFitting Y) σ 3 hσ ?_ hfix ?_
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
      h3 (h.trans (Subgroup.card_subgroup_dvd_card _))
  · intro x
    have hd : x⁻¹ * σ x ∈ generalizedFitting Y := by
      apply CFSG.centralizer_generalizedFitting_le Y
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 : x * f * x⁻¹ ∈ generalizedFitting Y := hN.conj_mem f hf x
      have h2 := hfix _ h1
      have e : σ x * f * (σ x)⁻¹ = x * f * x⁻¹ := by
        simpa [map_mul, map_inv, hfix f hf] using h2
      calc f * (x⁻¹ * σ x) = x⁻¹ * (x * f * x⁻¹) * σ x := by group
        _ = x⁻¹ * (σ x * f * (σ x)⁻¹) * σ x := by rw [e]
        _ = (x⁻¹ * σ x) * f := by group
    show (QuotientGroup.mk (σ x) : Y ⧸ generalizedFitting Y) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    simpa using (generalizedFitting Y).inv_mem hd

theorem eq_one_of_forall_apply_eq_layer (h2 : CFSG.pCore 2 Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    {T : Subgroup Y} (hT : IsPGroup 2 T) (hY : layer Y ⊔ T = ⊤)
    (σ : MulAut Y) (hσ : σ ^ 3 = 1) (hfix : ∀ z ∈ layer Y, σ z = z) : σ = 1 := by
  refine eq_one_of_forall_apply_eq_generalizedFitting h3 σ hσ fun z hz => ?_
  rw [CFSG.generalizedFitting.eq_sup] at hz
  have hle : fittingSubgroup Y ⊔ layer Y ≤ fixedSubgroupOf σ :=
    sup_le (fun f hf => (mem_fixedSubgroupOf σ f).mpr
      (hfix f (fittingSubgroup_le_layer h2 hT hY hf)))
      (fun f hf => (mem_fixedSubgroupOf σ f).mpr (hfix f hf))
  exact (mem_fixedSubgroupOf σ z).mp (hle hz)

theorem exists_component_not_fixed (h2 : CFSG.pCore 2 Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    {T : Subgroup Y} (hT : IsPGroup 2 T) (hY : layer Y ⊔ T = ⊤)
    (σ : MulAut Y) (hσ : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ K : Subgroup Y, IsComponent K ∧ ∃ z ∈ K, σ z ≠ z := by
  by_contra hno
  push Not at hno
  refine hσ1 (eq_one_of_forall_apply_eq_layer h2 h3 hT hY σ hσ fun z hz => ?_)
  have hle : layer Y ≤ fixedSubgroupOf σ :=
    sSup_le fun K hK z hz => (mem_fixedSubgroupOf σ z).mpr (hno K hK z hz)
  exact (mem_fixedSubgroupOf σ z).mp (hle hz)

end Layer

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
