module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGLatOrth
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsLift
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE7
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverCentral
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
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
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.SeitzReduction
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

section InvolutionsE7


private theorem ggInvE7_isogeny_xm_pinnedX {f : ℕ}
    (γ : Fin (Tag.rank .E7) → ℤ) (hγ : IsRoot .E7 γ) :
    e7Isogeny (GaloisField 2 f) (e7Data_valid.xm (GaloisField 2 f) γ 1) =
      (⟨pinnedX .E7 (GaloisField 2 f) γ 1,
        pinnedX_mem_adjointGroup γ 1⟩ : adjointGroup .E7 (GaloisField 2 f)) := by
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  rw [e7Isogeny_xm]
  rw [xPar_of_isRoot (F := rootOperatorFamily .E7) hγ]
  apply Subtype.ext
  simp only [RootOperatorFamily.coe_eltElement, Subtype.coe_mk]
  rw [RootOperatorFamily.pinnedX_eq_eltUnit (F := rootOperatorFamily .E7)
    (GaloisField 2 f) hγ 1]
  have h1 : (e7Eps γ : GaloisField 2 f) * 1 = 1 := by
    rcases e7Eps_eq_one_or γ with h | h
    · rw [h, Int.cast_one, one_mul]
    · rw [h, Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_mul]
  have h2 : ((rootOperatorFamily .E7).pinnedFamilySign γ : GaloisField 2 f) * 1 = 1 := by
    rcases (rootOperatorFamily .E7).pinnedFamilySign_eq γ with h | h
    · rw [h, Int.cast_one, one_mul]
    · rw [h, Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_mul]
  rw [h1, h2]

private theorem ggInvE7_frame_mem_of_check {L : List (List ℤ)}
    {F : List (Fin (Tag.rank .E7) → ℤ)}
    (h : (F.map (fun σ => List.ofFn σ)).all (fun ℓ => decide (ℓ ∈ L)) = true) :
    ∀ σ ∈ F, List.ofFn σ ∈ L := by
  intro σ hσ
  exact of_decide_eq_true (List.all_eq_true.mp h (List.ofFn σ) (List.mem_map_of_mem hσ))

private theorem ggInvE7_lift_frame {n f : ℕ}
    (L : List (List ℤ)) (hL : L ∈ asClassList .E7)
    (F : List (Fin (Tag.rank .E7) → ℤ))
    (hF : ∀ σ ∈ F, List.ofFn σ ∈ L) :
    ∃ Z : Set (Fin (ggU .E7 n f).D.rank → ℤ),
      ggASClass .E7 n f Z ∧
      ∃ r' ∈ ⨆ β ∈ Z, (ggU .E7 n f).D.rootGroup β,
        e7Isogeny (GaloisField 2 f) r' =
          (⟨(F.map fun σ => pinnedX .E7 (GaloisField 2 f) σ 1).prod,
            list_prod_map_pinnedX_mem_adjointGroup F⟩ : adjointGroup .E7 (GaloisField 2 f)) := by
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  haveI : Finite (GaloisField 2 f) := inferInstance
  have hroot : ∀ σ ∈ F, IsRoot .E7 σ := by
    intro σ hσ
    have hZ : σ ∈ ({β : Fin (ggU .E7 n f).D.rank → ℤ | List.ofFn β ∈ L}) := hF σ hσ
    have hmem := ggASClass_subset_roots .E7 n f (Or.inr (Or.inr (Or.inl rfl)))
      ({β : Fin (ggU .E7 n f).D.rank → ℤ | List.ofFn β ∈ L}) ⟨L, hL, rfl⟩ hZ
    exact mem_rootFinset.1 ((mem_roots_E7 n f σ).1 hmem)
  refine ⟨{β | List.ofFn β ∈ L}, ⟨L, hL, rfl⟩,
    (F.map fun σ => e7Data_valid.xm (GaloisField 2 f) σ 1).prod, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
      (l := F.map fun σ => e7Data_valid.xm (GaloisField 2 f) σ 1)
    intro g hg
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
    exact Subgroup.mem_iSup_of_mem σ (Subgroup.mem_iSup_of_mem (hF σ hσ)
      (e7Data_valid.xm_mem_rootGroup (GaloisField 2 f) σ 1))
  · rw [map_list_prod]
    have hcongr : List.map (e7Isogeny (GaloisField 2 f))
          (List.map (fun σ => e7Data_valid.xm (GaloisField 2 f) σ 1) F)
        = List.map (fun σ => (⟨pinnedX .E7 (GaloisField 2 f) σ 1,
            pinnedX_mem_adjointGroup σ 1⟩ : adjointGroup .E7 (GaloisField 2 f))) F := by
      rw [List.map_map]
      apply List.map_congr_left
      intro σ hσ
      exact ggInvE7_isogeny_xm_pinnedX σ (hroot σ hσ)
    rw [hcongr]
    apply Subtype.ext
    rw [Subgroup.val_list_prod]
    rw [List.map_map]
    rfl

theorem ggExcKGInvolutions_E7 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .E7 n f).K →* G) (hset : GGKnownSetting .E7 n f ψ) :
    ∀ s ∈ ψ.range, orderOf s = 2 →
      ∃ g ∈ ψ.range, ∃ Z : Set (Fin (ggU .E7 n f).D.rank → ℤ), ggASClass .E7 n f Z ∧
        g * s * g⁻¹ ∈ ⨆ β ∈ Z, ((ggU .E7 n f).D.rootGroup β).map ψ := by
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hf : 1 ≤ f := hadm.2.1
  haveI : NeZero f := ⟨by omega⟩
  haveI : Finite (GaloisField 2 f) := inferInstance
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  let K := GaloisField 2 f
  let φ : (ggU .E7 n f).K →* adjointGroup .E7 K := e7Isogeny K
  let χ : adjointGroup .E7 K →* G := ψ.comp (e7Equiv (K := K)).symm.toMonoidHom
  have hcenter : Subgroup.center (ggU .E7 n f).K = ⊥ := by
    change Subgroup.center (↥(e7Data_valid.minGroup K)) = ⊥
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center (K := K)]
    rw [MonoidHom.ker_eq_bot_iff]
    exact e7Isogeny_injective (K := K)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : x ∈ Subgroup.center (ggU .E7 n f).K := hker hx
    rw [hcenter, Subgroup.mem_bot] at hx'
    exact hx'
  have hχ : Function.Injective χ := by
    intro a b hab
    have hab' : ψ ((e7Equiv (K := K)).symm a) = ψ ((e7Equiv (K := K)).symm b) := hab
    exact (e7Equiv (K := K)).symm.injective (hψinj hab')
  have hψ : ∀ u, χ (φ u) = ψ u := by
    intro u
    change ψ ((e7Equiv (K := K)).symm (e7Isogeny K u)) = ψ u
    have h : e7Isogeny K u = e7Equiv (K := K) u :=
      (MulEquiv.ofBijective_apply (e7Isogeny K) _ u).symm
    rw [h]
    exact congrArg ψ (MulEquiv.symm_apply_apply (e7Equiv (K := K)) u)
  have hclass : ∀ y : adjointGroup .E7 K, orderOf y = 2 →
      ∃ a : adjointGroup .E7 K, a * y * a⁻¹ ∈ innerRepsE7 K := by
    intro y hy
    have hy2 : y ^ 2 = 1 := by
      have hpow : y ^ orderOf y = 1 := pow_orderOf_eq_one y
      rwa [hy] at hpow
    have hy1 : y ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hy
      omega
    exact exists_conj_mem_innerRepsE7 (K := K) hy2 hy1
  have hrep : ∀ r ∈ innerRepsE7 K,
      ∃ Z : Set (Fin (ggU .E7 n f).D.rank → ℤ), ggASClass .E7 n f Z ∧
        ∃ r' ∈ ⨆ β ∈ Z, (ggU .E7 n f).D.rootGroup β, φ r' = r := by
    intro r hr
    simp only [innerRepsE7, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨Z, hZ, r', hmem, heq⟩ := ggInvE7_lift_frame (n := n) (f := f)
        ([[2, 2, 3, 4, 3, 2, 1]] : List (List ℤ)) (by decide)
        [highRoot .E7] (ggInvE7_frame_mem_of_check (by decide +kernel))
      refine ⟨Z, hZ, r', hmem, ?_⟩
      rw [show φ r' = e7Isogeny (GaloisField 2 f) r' from rfl]
      rw [heq]
      apply Subtype.ext
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rfl
    · obtain ⟨Z, hZ, r', hmem, heq⟩ := ggInvE7_lift_frame (n := n) (f := f)
        ([[1, 1, 2, 3, 3, 2, 1], [1, 2, 2, 3, 2, 2, 1]] : List (List ℤ)) (by decide)
        oddDerivE7YFrame (ggInvE7_frame_mem_of_check (by decide +kernel))
      exact ⟨Z, hZ, r', hmem, heq⟩
    · obtain ⟨Z, hZ, r', hmem, heq⟩ := ggInvE7_lift_frame (n := n) (f := f)
        ([[1, 2, 2, 3, 2, 1, 0], [1, 1, 2, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1]] : List (List ℤ))
        (by decide) oddDerivE7ZFrame (ggInvE7_frame_mem_of_check (by decide +kernel))
      exact ⟨Z, hZ, r', hmem, heq⟩
    · obtain ⟨Z, hZ, r', hmem, heq⟩ := ggInvE7_lift_frame (n := n) (f := f)
        ([[1, 1, 1, 2, 2, 1, 1], [1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 2, 1]] : List (List ℤ))
        (by decide) oddDerivE7UFrame (ggInvE7_frame_mem_of_check (by decide +kernel))
      exact ⟨Z, hZ, r', hmem, heq⟩
    · obtain ⟨Z, hZ, r', hmem, heq⟩ := ggInvE7_lift_frame (n := n) (f := f)
        ([[1, 2, 2, 3, 2, 1, 0], [0, 1, 1, 2, 2, 2, 1], [1, 1, 2, 2, 1, 1, 1],
          [1, 1, 1, 2, 2, 1, 1]] : List (List ℤ)) (by decide)
        oddDerivE7VFrame (ggInvE7_frame_mem_of_check (by decide +kernel))
      exact ⟨Z, hZ, r', hmem, heq⟩
  intro s hs hs2
  exact ggExcKGInvolutions_of_factor .E7 n f ψ φ χ hχ (e7Isogeny_surjective K) hψ
    (innerRepsE7 K) hrep hclass hs hs2

end InvolutionsE7

end CFSG.StandardType
