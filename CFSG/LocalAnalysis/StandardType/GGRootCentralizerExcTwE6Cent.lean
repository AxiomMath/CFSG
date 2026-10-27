module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic
public import CFSG.LieType.Chevalley.CLSEvenTrialityFourGroup

public section

namespace CFSG.StandardType

namespace RootCentExc

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem permLattice_single_three_E6 :
    permLattice TwistTag.E6.perm (Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1 :
      Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1 := by
  decide

theorem centTwoGen_stdRepC_zero [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    CentTwoGen (stdRepC (apply_apply_eq hK hσ) 0 : graphFixedRootGroup TwistTag.E6 K σ) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  set t := stdRepC (apply_apply_eq hK hσ) 0 with ht
  have hLC : su6Levi σ ≤ C₀ := su6Levi_le_graphFixedRootGroup σ
  set Qt := (tRadical σ).subgroupOf C₀ with hQt
  set Lt := (su6Levi σ).subgroupOf C₀ with hLt
  have hC : centralizer ({t} : Set C₀) = Qt ⊔ Lt :=
    centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ
  have hQ2 : IsPGroup 2 Qt := by
    obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
    obtain ⟨S, hS⟩ := hT.2.2.2.2.2.2.2.2.2.1
    refine S.isPGroup'.to_le ?_
    rw [hS]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hx).1,
      graphFixedRootGroup_le _ _ _ x.2⟩
  have : Finite K := finite_of_card hK
  have hsimple : IsSimpleGroup Lt := by
    have := isSimpleGroup_su6Levi (k := k) hf hk hK hσ
    let e : Lt ≃* su6Levi σ := subgroupOfEquivOfLe hLC
    have : Nontrivial Lt := e.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hx₄C : pinnedX TwistTag.E6.tag K (Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1) 1 ∈ C₀ :=
    pinnedX_one_mem_graphFixedRootGroup h2 σ (isRoot_single _ ⟨3, by decide⟩)
      (by rw [height_single]; exact one_pos) permLattice_single_three_E6
  have hx₄L : pinnedX TwistTag.E6.tag K (Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1) 1 ∈ su6Levi σ :=
    mem_inf.2 ⟨pinnedX_mem_subsystemGroup_setA (isRoot_single _ ⟨3, by decide⟩) (by decide) 1, hx₄C⟩
  set x₄ : C₀ := ⟨pinnedX TwistTag.E6.tag K (Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1) 1, hx₄C⟩ with hx₄
  have hx₄Lt : x₄ ∈ Lt := hx₄L
  have hx₄1 : x₄ ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    change pinnedX TwistTag.E6.tag K (Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1) 1 = 1 at h'
    rw [← pinnedX_zero TwistTag.E6.tag K (Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1)] at h'
    exact one_ne_zero (pinnedX_injective _ _ _ h')
  have hx₄2 : x₄ * x₄ = 1 := Subtype.ext (pinnedX_mul_self h2 _ 1)
  rw [CentTwoGen, hC]
  set M := ggOTwoPrime (Qt ⊔ Lt) with hM
  refine sup_le (OTwoGen.le_ggOTwoPrime_of_isPGroup le_sup_left hQ2) ?_
  have hnorm : (M.subgroupOf Lt).Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hl : (l : C₀) ∈ normalizer (M : Set C₀) :=
      ggMem_normalizer_oTwoPrime (le_normalizer (le_sup_right (a := Qt) l.2))
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.1 hl n).1 hn
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hx₄M : x₄ ∈ M :=
      subset_closure ⟨le_sup_right (a := Qt) hx₄Lt, 1, by rw [pow_one, pow_two, hx₄2]⟩
    have hmem : (⟨x₄, hx₄Lt⟩ : Lt) ∈ M.subgroupOf Lt := hx₄M
    rw [hbot, mem_bot] at hmem
    exact hx₄1 (congrArg Subtype.val hmem)
  · intro l hl
    have hmem : (⟨l, hl⟩ : Lt) ∈ M.subgroupOf Lt := by
      rw [htop]
      exact mem_top _
    exact hmem

theorem centTwoGen_pinnedX_highRoot [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {c : K}
    (hc : c ≠ 0) (hcσ : σ c = c)
    (hmem : pinnedX TwistTag.E6.tag K e6HighestRoot c ∈ graphFixedRootGroup TwistTag.E6 K σ) :
    CentTwoGen (⟨_, hmem⟩ : graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Finite K := finite_of_card hK
  obtain ⟨h, hh, -, hconj⟩ := exists_twistedE6_torus_conj_frame_prod σ
    (F := [e6HighestRoot]) (fun γ hγ => by
      rw [List.mem_singleton] at hγ
      subst hγ
      exact ⟨isRoot_e6HighestRoot, permLattice_e6HighestRoot⟩)
    (List.pairwise_singleton _ _) (fun _ => c) (fun γ _ => ⟨hc, hcσ⟩)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hconj
  have e : (⟨h, hh⟩ : graphFixedRootGroup TwistTag.E6 K σ) * ⟨_, hmem⟩ * ⟨h, hh⟩⁻¹ =
      stdRepC (apply_apply_eq hK hσ) 0 := Subtype.ext hconj
  have h1 := centTwoGen_stdRepC_zero (k := k) hf hk hK hσ
  rw [← e] at h1
  exact h1.of_conj

end RootCentExc

end CFSG.StandardType
