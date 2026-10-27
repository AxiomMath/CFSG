module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XKDMisc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XKDOdd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XKDBender
import CFSG.Adapters.LieModelSimple
import CFSG.GroupTheory.PCoreSurjective
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

private theorem n924x_four_pow_mod_three (k : ℕ) : 4 ^ k % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]

private theorem n924x_odd_of_two_pow_mod_three {f : ℕ} (h : 2 ^ f % 3 = 2) : Odd f := by
  by_contra hodd
  have hf2 : 2 ∣ f := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨k, rfl⟩ := hf2
  have h2k : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  rw [h2k, n924x_four_pow_mod_three k] at h
  norm_num at h

theorem kFact913L2Even_holds : KFact913L2Even := by
  intro Q _ _ Lb Sb Xb n hLb hShape hSb hXL hXp hSX hn hL2
  let X : Subgroup ↥Lb := Xb.subgroupOf Lb
  have hL2' : IsL2 (Bar2 X) (2 * n) := by
    have hker : IsPGroup 2 (Subgroup.subgroupOfEquivOfLe hXL).symm.toMonoidHom.ker := by
      have hb : (Subgroup.subgroupOfEquivOfLe hXL).symm.toMonoidHom.ker = ⊥ :=
        MonoidHom.ker_eq_bot _ (Subgroup.subgroupOfEquivOfLe hXL).symm.injective
      rw [hb]
      exact IsPGroup.of_bot
    obtain ⟨eBar⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
      (p := 2) (Subgroup.subgroupOfEquivOfLe hXL).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXL).symm.surjective hker
    exact CFSG.Blueprint.LieModel.of_mulEquiv eBar hL2
  have hXp' : ⁅X, X⁆ = X := by
    refine (Subgroup.map_subtype_inj (H := Lb)).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXL, hXp]
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ Lb) Lb :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hSb le_top
      (Subgroup.normalizer_eq_top_iff.mpr hLb).ge
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 ((Sb ⊓ Lb).subgroupOf Lb) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff Lb]
    rw [Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simpa only [inf_assoc, inf_idem] using hTsyl
  have hTX : ((Sb ⊓ Lb).subgroupOf Lb) ≤ Subgroup.normalizer (X : Set ↥Lb) := by
    have h1 : (Sb ⊓ Lb) ≤ Subgroup.normalizer (Xb : Set Q) := inf_le_left.trans hSX
    have h2 : (Sb ⊓ Lb).subgroupOf Lb ≤
        (Subgroup.normalizer (Xb : Set Q)).subgroupOf Lb :=
      Subgroup.subgroupOf_mono Lb h1
    rwa [Subgroup.subgroupOf_normalizer_eq hXL] at h2
  have hXne : X ≠ ⊥ := by
    haveI : IsSimpleGroup (Bar2 X) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2'
    haveI : Nontrivial ↥X := (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot X).mp inferInstance
  have htop_of_bender (hB : CFSG.Open.fusionIsBenderGroup ↥Lb) : Xb = Lb := by
    have hXtop : X = ⊤ :=
      eq_top_of_normalized_by_sylow_of_bender hB hT hXne hXp' hTX
    exact le_antisymm hXL (Subgroup.subgroupOf_eq_top.mp hXtop)
  rcases hShape with ⟨hcyc, -⟩ | hJ1 | ⟨p, f, hp⟩ | ⟨p, f, hmod, hp⟩ | ⟨p, f, hmod, hp⟩
  · exact absurd hL2' (noL2Section_of_isCyclic hcyc X n hn)
  · exact absurd hL2' (noL2Section_of_isJ1 hJ1 X n hn)
  · by_cases hp2 : p = 2
    · subst hp2
      exact htop_of_bender (fusionIsBenderGroup_of_isL2_two hp)
    · exact absurd hL2' (noL2Section_psl2_odd hp2 hp X n hn)
  · by_cases hp2 : p = 2
    · subst hp2
      exact absurd hL2' (noL2Section_of_psl3_two_odd
        (n924x_odd_of_two_pow_mod_three hmod) hp X n hn)
    · exact absurd hL2' (noL2Section_psl3_odd hp2 hp X n hn)
  · by_cases hp2 : p = 2
    · subst hp2
      exact htop_of_bender (fusionIsBenderGroup_of_isU3_two hp)
    · exact absurd hL2' (noL2Section_psu3_odd hp2 hp X n hn)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
