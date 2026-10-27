module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGLatOrth
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsLift
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction

section InvolutionsE8


private theorem ggInvE8_pinnedX_mem_rootGroup (n f : ℕ) {β : Fin (Tag.rank .E8) → ℤ}
    (hβ : IsRoot .E8 β) :
    (⟨pinnedX .E8 (GaloisField 2 f) β 1, pinnedX_mem_adjointGroup _ _⟩ : (ggU .E8 n f).K) ∈
      (ggU .E8 n f).D.rootGroup β := by
  have h2 : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have hs : ((rootOperatorFamily .E8).pinnedFamilySign β : GaloisField 2 f) = 1 := by
    rcases (rootOperatorFamily .E8).pinnedFamilySign_eq β with h | h <;> rw [h]
    · exact Int.cast_one
    · rw [Int.cast_neg, Int.cast_one]
      linear_combination -h2
  have hmem : (⟨pinnedX .E8 (GaloisField 2 f) β 1, pinnedX_mem_adjointGroup _ _⟩ :
      adjointGroup .E8 (GaloisField 2 f)) ∈
      rootGroup (rootOperatorFamily .E8) (GaloisField 2 f) β := by
    rw [rootGroup_of_isRoot hβ, RootOperatorFamily.mem_rootSubgroup]
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change ((rootOperatorFamily .E8).eltUnit (GaloisField 2 f) ⟨β, hβ⟩ 1 :
        ModGL .E8 (GaloisField 2 f)) = pinnedX .E8 (GaloisField 2 f) β 1
    rw [(rootOperatorFamily .E8).pinnedX_eq_eltUnit (GaloisField 2 f) hβ 1, hs, mul_one]
  exact hmem

private theorem ggInvE8_ofFn_highRoot :
    List.ofFn (highRoot .E8) = ([2, 3, 4, 6, 5, 4, 3, 2] : List ℤ) := by
  decide +kernel

private theorem ggInvE8_ofFn_y :
    oddDerivE8YFrame.map List.ofFn =
      ([[2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1]] : List (List ℤ)) := by
  decide +kernel

private theorem ggInvE8_ofFn_z :
    oddDerivE8ZFrame.map List.ofFn =
      ([[2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1],
        [1, 2, 2, 4, 4, 3, 2, 1]] : List (List ℤ)) := by
  decide +kernel

private theorem ggInvE8_ofFn_u :
    oddDerivE8UFrame.map List.ofFn =
      ([[2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 3, 4, 3, 2, 1, 1], [1, 2, 2, 3, 3, 3, 2, 1],
        [1, 2, 2, 4, 3, 2, 2, 1]] : List (List ℤ)) := by
  decide +kernel

private theorem ggInvE8_prod_mem (n f : ℕ) (F : List (Fin (Tag.rank .E8) → ℤ))
    (L : List (List ℤ)) (hL : L ∈ asClassList .E8) (hmap : F.map List.ofFn = L) :
    (F.map fun σ => (⟨pinnedX .E8 (GaloisField 2 f) σ 1,
        pinnedX_mem_adjointGroup _ _⟩ : (ggU .E8 n f).K)).prod ∈
      ⨆ β ∈ ({β : Fin ((ggU .E8 n f).D.rank) → ℤ | List.ofFn β ∈ L} : Set _),
        (ggU .E8 n f).D.rootGroup β := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
  have hσL : List.ofFn σ ∈ L := by
    have hmem : List.ofFn σ ∈ F.map List.ofFn := List.mem_map.2 ⟨σ, hσ, rfl⟩
    rwa [hmap] at hmem
  have hσZ : σ ∈ ({β : Fin ((ggU .E8 n f).D.rank) → ℤ | List.ofFn β ∈ L} : Set _) := hσL
  have hroot : IsRoot .E8 σ :=
    mem_rootFinset.1 ((mem_roots_E8 n f σ).1
      (ggASClass_subset_roots .E8 n f (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        ({β : Fin ((ggU .E8 n f).D.rank) → ℤ | List.ofFn β ∈ L}) ⟨L, hL, rfl⟩ hσZ))
  exact Subgroup.mem_iSup_of_mem σ
    (Subgroup.mem_iSup_of_mem hσZ (ggInvE8_pinnedX_mem_rootGroup n f hroot))

theorem ggExcKGInvolutions_E8 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .E8 n f).K →* G) (hset : GGKnownSetting .E8 n f ψ) :
    ∀ s ∈ ψ.range, orderOf s = 2 →
      ∃ g ∈ ψ.range, ∃ Z : Set (Fin (ggU .E8 n f).D.rank → ℤ), ggASClass .E8 n f Z ∧
        g * s * g⁻¹ ∈ ⨆ β ∈ Z, ((ggU .E8 n f).D.rootGroup β).map ψ := by
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hf : 1 ≤ f := hadm.2.1
  haveI : NeZero f := ⟨by omega⟩
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    refine hker.trans ?_
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).le
  have hrep : ∀ r ∈ innerRepsE8 (GaloisField 2 f),
      ∃ Z : Set (Fin (ggU .E8 n f).D.rank → ℤ), ggASClass .E8 n f Z ∧
        ∃ r' ∈ ⨆ β ∈ Z, (ggU .E8 n f).D.rootGroup β,
          (MonoidHom.id (ggU .E8 n f).K r') = r := by
    intro r hr
    rw [innerRepsE8] at hr
    rcases hr with rfl | rfl | rfl | rfl
    ·
      refine ⟨{β : Fin ((ggU .E8 n f).D.rank) → ℤ |
          List.ofFn β ∈ ([[2, 3, 4, 6, 5, 4, 3, 2]] : List (List ℤ))},
        ⟨[[2, 3, 4, 6, 5, 4, 3, 2]], by decide, rfl⟩, _, ?_, rfl⟩
      have hZmem : (highRoot .E8) ∈
          ({β : Fin ((ggU .E8 n f).D.rank) → ℤ |
            List.ofFn β ∈ ([[2, 3, 4, 6, 5, 4, 3, 2]] : List (List ℤ))} : Set _) := by
        show List.ofFn (highRoot .E8) ∈ ([[2, 3, 4, 6, 5, 4, 3, 2]] : List (List ℤ))
        rw [ggInvE8_ofFn_highRoot]
        simp
      have hroot : IsRoot .E8 (highRoot .E8) :=
        mem_rootFinset.1 ((mem_roots_E8 n f (highRoot .E8)).1
          (ggASClass_subset_roots .E8 n f (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            ({β : Fin ((ggU .E8 n f).D.rank) → ℤ |
              List.ofFn β ∈ ([[2, 3, 4, 6, 5, 4, 3, 2]] : List (List ℤ))})
            ⟨[[2, 3, 4, 6, 5, 4, 3, 2]], by decide, rfl⟩ hZmem))
      exact Subgroup.mem_iSup_of_mem (highRoot .E8)
        (Subgroup.mem_iSup_of_mem hZmem (ggInvE8_pinnedX_mem_rootGroup n f hroot))
    ·
      refine ⟨{β : Fin ((ggU .E8 n f).D.rank) → ℤ |
          List.ofFn β ∈ ([[2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1]] :
            List (List ℤ))},
        ⟨[[2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1]], by decide, rfl⟩, _, ?_, rfl⟩
      have heq : (oddDerivE8YFrame.map fun σ =>
            (⟨pinnedX .E8 (GaloisField 2 f) σ 1,
              pinnedX_mem_adjointGroup _ _⟩ : (ggU .E8 n f).K)).prod =
          (⟨(oddDerivE8YFrame.map fun σ => pinnedX .E8 (GaloisField 2 f) σ 1).prod,
            list_prod_map_pinnedX_mem_adjointGroup _⟩ : (ggU .E8 n f).K) := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_list_prod, List.map_map]
        rfl
      rw [← heq]
      exact ggInvE8_prod_mem n f oddDerivE8YFrame
        ([[2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1]] : List (List ℤ))
        (by decide) ggInvE8_ofFn_y
    ·
      refine ⟨{β : Fin ((ggU .E8 n f).D.rank) → ℤ |
          List.ofFn β ∈ ([[2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1],
            [1, 2, 2, 4, 4, 3, 2, 1]] : List (List ℤ))},
        ⟨[[2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1],
          [1, 2, 2, 4, 4, 3, 2, 1]], by decide, rfl⟩, _, ?_, rfl⟩
      have heq : (oddDerivE8ZFrame.map fun σ =>
            (⟨pinnedX .E8 (GaloisField 2 f) σ 1,
              pinnedX_mem_adjointGroup _ _⟩ : (ggU .E8 n f).K)).prod =
          (⟨(oddDerivE8ZFrame.map fun σ => pinnedX .E8 (GaloisField 2 f) σ 1).prod,
            list_prod_map_pinnedX_mem_adjointGroup _⟩ : (ggU .E8 n f).K) := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_list_prod, List.map_map]
        rfl
      rw [← heq]
      exact ggInvE8_prod_mem n f oddDerivE8ZFrame
        ([[2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1],
          [1, 2, 2, 4, 4, 3, 2, 1]] : List (List ℤ))
        (by decide) ggInvE8_ofFn_z
    ·
      refine ⟨{β : Fin ((ggU .E8 n f).D.rank) → ℤ |
          List.ofFn β ∈ ([[2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 3, 4, 3, 2, 1, 1],
            [1, 2, 2, 3, 3, 3, 2, 1], [1, 2, 2, 4, 3, 2, 2, 1]] : List (List ℤ))},
        ⟨[[2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 3, 4, 3, 2, 1, 1], [1, 2, 2, 3, 3, 3, 2, 1],
          [1, 2, 2, 4, 3, 2, 2, 1]], by decide, rfl⟩, _, ?_, rfl⟩
      have heq : (oddDerivE8UFrame.map fun σ =>
            (⟨pinnedX .E8 (GaloisField 2 f) σ 1,
              pinnedX_mem_adjointGroup _ _⟩ : (ggU .E8 n f).K)).prod =
          (⟨(oddDerivE8UFrame.map fun σ => pinnedX .E8 (GaloisField 2 f) σ 1).prod,
            list_prod_map_pinnedX_mem_adjointGroup _⟩ : (ggU .E8 n f).K) := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_list_prod, List.map_map]
        rfl
      rw [← heq]
      exact ggInvE8_prod_mem n f oddDerivE8UFrame
        ([[2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 3, 4, 3, 2, 1, 1], [1, 2, 2, 3, 3, 3, 2, 1],
          [1, 2, 2, 4, 3, 2, 2, 1]] : List (List ℤ))
        (by decide) ggInvE8_ofFn_u
  have hclass : ∀ y : (ggU .E8 n f).K, orderOf y = 2 →
      ∃ a : (ggU .E8 n f).K, a * y * a⁻¹ ∈ innerRepsE8 (GaloisField 2 f) := by
    intro y hy
    obtain ⟨hy2, hy1⟩ := (orderOf_eq_prime_iff (p := 2)).1 hy
    obtain ⟨g, hg⟩ := classListE8_exists_conj_mem_innerRepsE8 (K := GaloisField 2 f) hy2 hy1
    exact ⟨g, hg⟩
  intro s hs hs2
  exact ggExcKGInvolutions_of_factor .E8 n f ψ
    (MonoidHom.id (ggU .E8 n f).K) ψ hinj (fun a => ⟨a, rfl⟩)
    (fun _ => rfl) (innerRepsE8 (GaloisField 2 f)) hrep hclass hs hs2

end InvolutionsE8

end CFSG.StandardType
