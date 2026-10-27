module

public import CFSG.Blueprint.ChevalleyStringsInputs
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.RootAut

private theorem ncard_eq_two_mul_posRoots
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hfin : Ψ.Finite) : Ψ.ncard = 2 * (posRoots Ψ).ncard := by
  classical
  have hu : Ψ = posRoots Ψ ∪ negRoots Ψ := by
    ext α
    constructor
    · intro hα
      exact (mem_posRoots_or_mem_negRoots hΨ hα).elim Or.inl Or.inr
    · rintro (h | h)
      · exact h.1
      · exact ((mem_negRoots_iff hΨ).1 h).1
  have hdisj : Disjoint (posRoots Ψ) (negRoots Ψ) :=
    Set.disjoint_left.2 fun α h1 h2 => not_mem_negRoots_of_mem_posRoots h1 h2
  have himg : negRoots Ψ = (fun α : Fin τ.rank → ℤ => -α) '' posRoots Ψ := by
    ext α
    constructor
    · intro h
      exact ⟨-α, h, by simp⟩
    · rintro ⟨β, hβ, rfl⟩
      change -(-β) ∈ posRoots Ψ
      rw [neg_neg]
      exact hβ
  have hfp : (posRoots Ψ).Finite := hfin.subset fun α hα => hα.1
  have hfn : (negRoots Ψ).Finite := by rw [himg]; exact hfp.image _
  conv_lhs => rw [hu]
  rw [Set.ncard_union_eq hdisj hfp hfn, himg, Set.ncard_image_of_injective _ neg_injective]
  ring

theorem compRank_eq_two_of_ncard_eq_six
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (h6 : Ψ.ncard = 6) : compRank Ψ = 2 := by
  classical
  have hfin : Ψ.Finite := Set.finite_of_ncard_pos (by omega)
  have hpos : (posRoots Ψ).ncard = 3 := by
    have := ncard_eq_two_mul_posRoots hΨ hfin
    omega
  have hfpos : (posRoots Ψ).Finite := hfin.subset fun α hα => hα.1
  have hΔsub : ((simpleRoots Ψ : Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) ⊆
      posRoots Ψ := fun β hβ => (mem_simpleRoots.1 hβ).2.1
  have hΔle : (simpleRoots Ψ).card ≤ 3 := by
    have h := Set.ncard_le_ncard hΔsub hfpos
    rwa [Set.ncard_coe_finset, hpos] at h
  have hge2 : 2 ≤ (simpleRoots Ψ).card := by
    by_contra hlt
    have hle1 : (simpleRoots Ψ).card ≤ 1 := by omega
    have hsub : posRoots Ψ ⊆
        ((simpleRoots Ψ : Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) := by
      intro α hα
      obtain ⟨c, hc, hαc⟩ := exists_nonneg_coords hΨ hα
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle1 with h0 | h1
      · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty] at hαc
        exact absurd hαc (hΨ.isRoot α hα.1).ne_zero
      · obtain ⟨β, hβ⟩ := Finset.card_eq_one.1 h1
        rw [hβ, Finset.sum_singleton] at hαc
        rcases (hΨ.isRoot α hα.1).eq_one_or_neg_one_of_eq_smul hαc with h | h
        · rw [h, one_smul] at hαc
          simp [hβ, hαc]
        · have := hc β (by simp [hβ])
          omega
    have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, hpos] at h
    omega
  have hne3 : (simpleRoots Ψ).card ≠ 3 := by
    intro h3
    have hΔeq : ((simpleRoots Ψ : Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) =
        posRoots Ψ :=
      Set.eq_of_subset_of_ncard_le hΔsub (by rw [hpos, Set.ncard_coe_finset]; omega) hfpos
    have hmemΔ : ∀ γ, γ ∈ posRoots Ψ → γ ∈ simpleRoots Ψ := fun γ hγ => by
      rw [← Finset.mem_coe, hΔeq]
      exact hγ
    have horth : ∀ β ∈ simpleRoots Ψ, ∀ γ ∈ simpleRoots Ψ, β ≠ γ → iform β γ = 0 := by
      intro β hβ γ hγ hne
      by_contra hne0
      have hlt : iform β γ < 0 := lt_of_le_of_ne (iform_simpleRoots_nonpos hΨ hβ hγ hne) hne0
      have hβh := simpleRoots_height_pos hβ
      have hγh := simpleRoots_height_pos hγ
      have hroot : IsRoot τ (β + γ) := by
        refine isRoot_add_of_iform_neg (simpleRoots_isRoot hβ) (simpleRoots_isRoot hγ) ?_ hlt
        intro h
        have := congrArg height h
        rw [height_neg] at this
        omega
      have hmem : β + γ ∈ posRoots Ψ :=
        ⟨hΨ.add_mem β (simpleRoots_subset hβ) γ (simpleRoots_subset hγ) hroot, by
          rw [height_add]
          omega⟩
      exact (mem_simpleRoots.1 (hmemΔ _ hmem)).2.2 β (mem_simpleRoots.1 hβ).2.1 γ
        (mem_simpleRoots.1 hγ).2.1 rfl
    obtain ⟨β₀, hβ₀⟩ : (simpleRoots Ψ).Nonempty := Finset.card_pos.1 (by omega)
    have hSΨ : ({β₀, -β₀} : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
      intro x hx
      rcases hx with rfl | rfl
      · exact simpleRoots_subset hβ₀
      · exact hΨ.neg_mem _ (simpleRoots_subset hβ₀)
    have hort : ∀ α ∈ ({β₀, -β₀} : Set (Fin τ.rank → ℤ)), ∀ β ∈ Ψ,
        β ∉ ({β₀, -β₀} : Set (Fin τ.rank → ℤ)) → iform α β = 0 := by
      intro α hα β hβ hβS
      have hβ₀β : iform β₀ β = 0 := by
        rcases mem_posRoots_or_mem_negRoots hΨ hβ with hp | hn
        · exact horth β₀ hβ₀ β (hmemΔ β hp) fun h => hβS (Or.inl h.symm)
        · have hn' : -β ∈ posRoots Ψ := hn
          have h0 := horth β₀ hβ₀ (-β) (hmemΔ _ hn') fun h =>
            hβS (Or.inr (show β = -β₀ by rw [h, neg_neg]))
          have h1 : iform β₀ (-β) = -iform β₀ β := by
            rw [← neg_one_smul ℤ β, iform_smul_right]
            ring
          omega
      rcases hα with rfl | rfl
      · exact hβ₀β
      · have h1 : iform (-β₀) β = -iform β₀ β := by
          rw [← neg_one_smul ℤ β₀, iform_smul_left]
          ring
        omega
    rcases hΨ.irreducible _ hSΨ hort with hE | hE
    · exact absurd hE (Set.nonempty_iff_ne_empty.1 ⟨β₀, Set.mem_insert _ _⟩)
    · have h2 : ({β₀, -β₀} : Set (Fin τ.rank → ℤ)).ncard ≤ 2 :=
        calc _ ≤ ({-β₀} : Set (Fin τ.rank → ℤ)).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      rw [hE, h6] at h2
      omega
  rw [compRank_eq_card hΨ]
  omega

end CFSG.StandardType.LangRat
