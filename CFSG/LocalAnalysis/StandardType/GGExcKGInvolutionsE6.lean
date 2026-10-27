module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGLatOrth
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsLift
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFrameOn
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE6
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.SeitzReduction

section InvolutionsE6


private theorem ggInvE6_isogeny_xm_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    e6Isogeny K (e6Data_valid.xm K γ 1) =
      ⟨pinnedX .E6 K γ 1, pinnedX_mem_adjointGroup γ 1⟩ := by
  apply Subtype.ext
  exact E6Pilot.coe_e6Isogeny_xm hγ 1

private theorem ggInvE6_frame_prod_mem (K : Type) [Field K] [Finite K]
    (F : List (Fin (Tag.rank .E6) → ℤ)) (L : List (List ℤ))
    (hF : ∀ σ ∈ F, List.ofFn σ ∈ L) :
    (F.map fun σ => e6Data_valid.xm K σ 1).prod ∈
      ⨆ β ∈ ({β : Fin (Tag.rank .E6) → ℤ | List.ofFn β ∈ L}),
        e6Data_valid.rootGroup K β := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.mem_iSup_of_mem σ
    (Subgroup.mem_iSup_of_mem (hF σ hσ) (e6Data_valid.xm_mem_rootGroup K σ 1))

private theorem ggInvE6_isogeny_frame_prod (K : Type) [Field K] [Finite K] [CharP K 2]
    (F : List (Fin (Tag.rank .E6) → ℤ))
    (hroot : ∀ σ ∈ F, IsRoot .E6 σ) :
    e6Isogeny K ((F.map fun σ => e6Data_valid.xm K σ 1).prod) =
      ⟨(F.map fun σ => pinnedX .E6 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup F⟩ := by
  apply Subtype.ext
  rw [map_list_prod, Subgroup.val_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun σ hσ => E6Pilot.coe_e6Isogeny_xm (hroot σ hσ) 1

theorem ggExcKGInvolutions_E6 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .E6 n f).K →* G) (hset : GGKnownSetting .E6 n f ψ) :
    ∀ s ∈ ψ.range, orderOf s = 2 →
      ∃ g ∈ ψ.range, ∃ Z : Set (Fin (ggU .E6 n f).D.rank → ℤ), ggASClass .E6 n f Z ∧
        g * s * g⁻¹ ∈ ⨆ β ∈ Z, ((ggU .E6 n f).D.rootGroup β).map ψ := by
  intro s hs hs2
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hf : 1 ≤ f := hadm.2.1
  haveI : NeZero f := ⟨by omega⟩
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  obtain ⟨χ, hχinj, _, hψ⟩ :=
    NoOffE6Three.exists_injective_factor_E6_comp ψ hker hcent
  have hφsurj : Function.Surjective (e6Isogeny (GaloisField 2 f)) :=
    e6Isogeny_surjective (GaloisField 2 f)
  refine ggExcKGInvolutions_of_factor .E6 n f ψ (e6Isogeny (GaloisField 2 f)) χ hχinj
    hφsurj hψ (innerRepsE6 (GaloisField 2 f)) ?_ ?_ hs hs2
  ·
    intro r hr
    simp only [innerRepsE6, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    ·
      refine ⟨{β : Fin (ggU .E6 n f).D.rank → ℤ | List.ofFn β ∈ [[1, 2, 2, 3, 2, 1]]},
        ⟨[[1, 2, 2, 3, 2, 1]], by decide +kernel, rfl⟩,
        e6Data_valid.xm (GaloisField 2 f) (highRoot .E6) 1, ?_, ?_⟩
      · refine Subgroup.mem_iSup_of_mem (highRoot .E6) (Subgroup.mem_iSup_of_mem ?_
          (e6Data_valid.xm_mem_rootGroup (GaloisField 2 f) (highRoot .E6) 1))
        show List.ofFn (highRoot .E6) ∈ [[1, 2, 2, 3, 2, 1]]
        decide +kernel
      · exact ggInvE6_isogeny_xm_one (isRoot_highRoot .E6)
    ·
      have hmemY : ∀ σ ∈ oddDerivE6YFrame,
          List.ofFn σ ∈ [[1, 1, 2, 2, 1, 1], [1, 1, 1, 2, 2, 1]] := by
        intro σ hσ
        rw [oddDerivE6YFrame] at hσ
        rcases List.mem_cons.mp hσ with h | h
        · subst h; decide +kernel
        rcases List.mem_cons.mp h with h | h
        · subst h; decide +kernel
        exact (List.not_mem_nil (a := σ) h).elim
      have hZY : ggASClass .E6 n f
          {β : Fin (ggU .E6 n f).D.rank → ℤ |
            List.ofFn β ∈ [[1, 1, 2, 2, 1, 1], [1, 1, 1, 2, 2, 1]]} :=
        ⟨[[1, 1, 2, 2, 1, 1], [1, 1, 1, 2, 2, 1]], by decide +kernel, rfl⟩
      have hrootY : ∀ σ ∈ oddDerivE6YFrame, IsRoot .E6 σ := by
        intro σ hσ
        exact mem_rootFinset.mp ((mem_roots_E6 n f σ).mp
          (ggASClass_subset_roots .E6 n f (Or.inr (Or.inl rfl)) _ hZY (hmemY σ hσ)))
      refine ⟨_, hZY,
        (oddDerivE6YFrame.map fun σ => e6Data_valid.xm (GaloisField 2 f) σ 1).prod, ?_, ?_⟩
      · exact ggInvE6_frame_prod_mem (GaloisField 2 f) oddDerivE6YFrame
          [[1, 1, 2, 2, 1, 1], [1, 1, 1, 2, 2, 1]] hmemY
      · exact ggInvE6_isogeny_frame_prod (GaloisField 2 f) oddDerivE6YFrame hrootY
    ·
      have hmemZ : ∀ σ ∈ oddDerivE6ZFrame,
          List.ofFn σ ∈ [[0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1], [1, 1, 2, 2, 1, 0]] := by
        intro σ hσ
        rw [oddDerivE6ZFrame] at hσ
        rcases List.mem_cons.mp hσ with h | h
        · subst h; decide +kernel
        rcases List.mem_cons.mp h with h | h
        · subst h; decide +kernel
        rcases List.mem_cons.mp h with h | h
        · subst h; decide +kernel
        exact (List.not_mem_nil (a := σ) h).elim
      have hZZ : ggASClass .E6 n f
          {β : Fin (ggU .E6 n f).D.rank → ℤ |
            List.ofFn β ∈ [[0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1], [1, 1, 2, 2, 1, 0]]} :=
        ⟨[[0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1], [1, 1, 2, 2, 1, 0]], by decide +kernel, rfl⟩
      have hrootZ : ∀ σ ∈ oddDerivE6ZFrame, IsRoot .E6 σ := by
        intro σ hσ
        exact mem_rootFinset.mp ((mem_roots_E6 n f σ).mp
          (ggASClass_subset_roots .E6 n f (Or.inr (Or.inl rfl)) _ hZZ (hmemZ σ hσ)))
      refine ⟨_, hZZ,
        (oddDerivE6ZFrame.map fun σ => e6Data_valid.xm (GaloisField 2 f) σ 1).prod, ?_, ?_⟩
      · exact ggInvE6_frame_prod_mem (GaloisField 2 f) oddDerivE6ZFrame
          [[0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1], [1, 1, 2, 2, 1, 0]] hmemZ
      · exact ggInvE6_isogeny_frame_prod (GaloisField 2 f) oddDerivE6ZFrame hrootZ
  ·
    intro y hy
    have hy2 : y ^ 2 = 1 := by simpa [hy] using pow_orderOf_eq_one y
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hy
      omega
    exact exists_conj_mem_innerRepsE6 hy2 hy1

end InvolutionsE6

end CFSG.StandardType
