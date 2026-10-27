module

public import CFSG.Quasithin.EmptyFaithful.S1421QA21Abs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeRankOne

public section

namespace CFSG.Quasithin.QA21

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

set_option linter.unusedSectionVars false

section Ree

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem solvable_le_reeFixedBorel (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hN : ∀ j : Fin F4.fixedOrbitCount, ¬ Group.IsSolvable ↥(reePosWeylGroup K a j))
    {A : Subgroup (ModGL F4.tag K)} (hAΓ : A ≤ F4.reeGamma K a)
    (hUA : F4.reeFixedPosUnipotent K a ≤ A) (hA : Group.IsSolvable ↥A) :
    A ≤ F4.reeFixedBorel K a := by
  have hle := (large_Ree_positive_root_overgroup_parabolic_containment hK hAΓ hUA).1
  have hJ : {k | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement k) ∈ A} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hk
    apply hN k
    have hNA : reePosWeylGroup K a k ≤ A :=
      sup_le hUA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hk))
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNA)
      (Subgroup.inclusion_injective hNA)
  rw [hJ, reeParabolic_empty] at hle
  exact hle

theorem not_isSolvable_reePosWeylGroup (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (j : Fin F4.fixedOrbitCount) : ¬ Group.IsSolvable ↥(reePosWeylGroup K a j) := by
  intro hs
  have hMs : Group.IsSolvable ↥(F4.reeLocalBlock K a j) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion
      (reeLocalBlock_le_reePosWeylGroup j)) (Subgroup.inclusion_injective _)
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hcases : j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
    rcases j with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases with rfl | rfl
  · rw [h0eq] at hMs
    obtain ⟨hsimple, x, y, hxy⟩ := isSimpleGroup_rankOneGroupOne ha hK
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.2 hMs x y)
  · rw [h1eq] at hMs
    obtain ⟨hsimple, x, y, hxy⟩ := isSimpleGroup_rankOneGroupTwo ha hK
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.2 hMs x y)

theorem borelAmbient_2f4 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    BorelAmbient (ModGL F4.tag K) (F4.reeGamma K a) (F4.reeFixedPosUnipotent K a)
      (F4.reeFixedBorel K a) (fun j : Fin 2 => F4.reeParabolic K a {f4Index j}) := by
  have hself := reeGamma_inf_normalizer_reeFixedPosUnipotent (t := F4) (K := K) (a := a)
  refine ⟨reeFixedPosUnipotent_le_reeGamma, ?_, hself.le,
    fun j => reeFixedBorel_le_reeParabolic F4 K a _,
    fun A hAC hUA hA => solvable_le_reeFixedBorel hK (not_isSolvable_reePosWeylGroup ha hK)
      hAC hUA hA⟩
  rw [← hself]
  exact inf_le_right

theorem borelPkg_2f4 {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 f) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup X, BorelPkg X U P := by
  obtain ⟨a, K, hF, hFin, hcp, φ, ha, hfa, hK, hφU, hres, -⟩ :=
    even_rank_two_residual_largeRee hX hU
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  exact ⟨_, (borelAmbient_2f4 ha hK').borelPkg φ hφU hres⟩

end Ree

end CFSG.Quasithin.QA21
