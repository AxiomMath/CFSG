module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpULie
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParQuotA
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParQuotB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

variable {G Q : Type} [Group G] [Group Q]

private lemma spUCitedParQuot_conjSubgroup_map (π : G →* Q) (K : Subgroup G) (g : G) :
    (conjSubgroup K g).map π = conjSubgroup (K.map π) (π g) := by
  have hhom : (MulAut.conj ((π g)⁻¹)).toMonoidHom.comp π
      = π.comp (MulAut.conj (g⁻¹)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply]
  unfold conjSubgroup
  simp only [Subgroup.map_map]
  rw [hhom]

theorem spUCited_rootParabolic_map [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : ¬ 2 ∣ Nat.card π.ker)
    {R Sy X₂ Pα : Subgroup G} {e : ℕ} (hR : IsPGroup 2 R) (hPα : π.ker ≤ Pα)
    (h : RootParabolic R Sy X₂ Pα e)
    (hinv : ∀ α : MulAut Q, Subgroup.map α.toMonoidHom (Sy.map π) = Sy.map π →
      Subgroup.map α.toMonoidHom (R.map π) = R.map π →
      Subgroup.map α.toMonoidHom (Pα.map π) = Pα.map π) :
    RootParabolic (R.map π) (Sy.map π) (X₂.map π) (Pα.map π) e := by
  have hmem := h.mem
  simp only [rootGroupsIn, Set.mem_setOf_eq] at hmem
  obtain ⟨⟨g, hg⟩, hX₂le⟩ := hmem
  have hX₂ : IsPGroup 2 X₂ := by
    rw [hg]
    exact hR.map (MulAut.conj (g⁻¹)).toMonoidHom
  have hkerNG : π.ker ≤ Subgroup.normalizer (X₂ : Set G) :=
    hker.trans (Subgroup.center_le_normalizer (X₂ : Set G))
  have hmap : (Sy ⊓ Subgroup.normalizer (X₂ : Set G)).map π
      = Sy.map π ⊓ Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q) := by
    rw [spUCited_map_inf_of_ker_le π (A := Sy)
          (B := Subgroup.normalizer (X₂ : Set G)) hkerNG,
        spUCited_normalizer_map_of_ker π hπ hker hodd hX₂]
  have hindex_eq :
      (Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q)).relIndex (Sy.map π)
        = (Subgroup.normalizer (X₂ : Set G)).relIndex Sy := by
    have hcomap : (((Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q) ⊓
          Sy.map π).subgroupOf (Sy.map π)).comap (π.subgroupMap Sy))
        = (Sy ⊓ Subgroup.normalizer (X₂ : Set G)).subgroupOf Sy := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
        have hx' : (x : G) ∈ (Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q)).comap π :=
          hx.1
        rw [spUCited_comap_normalizer_map π hπ hker hodd hX₂] at hx'
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨x.2, hx'⟩)
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
        have hxNQ : (π.subgroupMap Sy x : Q)
            ∈ Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q) := by
          have hx' : (x : G) ∈ (Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q)).comap π := by
            rw [spUCited_comap_normalizer_map π hπ hker hodd hX₂]
            exact hx.2
          exact hx'
        exact Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_inf.mpr ⟨hxNQ, (π.subgroupMap Sy x).2⟩))
    have hTidx : (Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q)).relIndex (Sy.map π)
        = (Sy ⊓ Subgroup.normalizer (X₂ : Set G)).relIndex Sy := by
      rw [← Subgroup.inf_relIndex_right
        (H := Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q)) (K := Sy.map π)]
      show (((Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q) ⊓
            Sy.map π).subgroupOf (Sy.map π)).index)
          = (((Sy ⊓ Subgroup.normalizer (X₂ : Set G)).subgroupOf Sy).index)
      have hii := Subgroup.index_comap_of_surjective (H :=
          ((Subgroup.normalizer ((X₂.map π : Subgroup Q) : Set Q) ⊓
            Sy.map π).subgroupOf (Sy.map π)))
        (f := π.subgroupMap Sy) (MonoidHom.subgroupMap_surjective π Sy)
      rw [← hii]
      rw [hcomap]
    rw [hTidx, inf_comm, Subgroup.inf_relIndex_right]
  refine
    { mem := ?_
      index := ?_
      one_le := h.one_le
      le := Subgroup.map_mono h.le
      isPGroup := ?_
      normal := ?_
      largest := ?_
      not_le := ?_
      maximal := ?_
      invariant := hinv }
  · refine ⟨⟨π g, ?_⟩, Subgroup.map_mono hX₂le⟩
    rw [hg]
    exact spUCitedParQuot_conjSubgroup_map π R g
  · rw [hindex_eq, spUCited_card_map_of_isPGroup π hodd hR]
    exact h.index
  · rw [← hmap]
    exact h.isPGroup.map π
  · have hQle : Sy ⊓ Subgroup.normalizer (X₂ : Set G) ≤ Pα := inf_le_left.trans h.le
    have hnormal :
        (((Sy ⊓ Subgroup.normalizer (X₂ : Set G)).map π).subgroupOf (Pα.map π)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hQle)]
      calc Pα.map π
          ≤ (Subgroup.normalizer (Sy ⊓ Subgroup.normalizer (X₂ : Set G) : Set G)).map π :=
            Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mp h.normal)
        _ ≤ Subgroup.normalizer
              (((Sy ⊓ Subgroup.normalizer (X₂ : Set G)).map π : Subgroup Q) : Set Q) :=
            Subgroup.le_normalizer_map
              (H := Sy ⊓ Subgroup.normalizer (X₂ : Set G)) π
    rwa [hmap] at hnormal
  · intro N hNP hN hN2
    have hle := spUCited_le_map_of_normal_two π hπ hker hodd hPα h.largest hNP hN hN2
    rwa [hmap] at hle
  · intro hle
    apply h.not_le
    have hle' : Pα ≤ (Subgroup.normalizer ((R.map π : Subgroup Q) : Set Q)).comap π :=
      (Subgroup.le_comap_map π Pα).trans (Subgroup.comap_mono (f := π) hle)
    rwa [spUCited_comap_normalizer_map π hπ hker hodd hR] at hle'
  · intro M hM
    have hM' : Subgroup.normalizer (R : Set G) ≤ M.comap π := by
      have h := Subgroup.comap_mono (f := π) hM
      rwa [spUCited_comap_normalizer_map π hπ hker hodd hR] at h
    rcases h.maximal (M.comap π) hM' with hcase | hcase
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ M, hcase,
        spUCited_normalizer_map_of_ker π hπ hker hodd hR]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ M, hcase,
        Subgroup.map_top_of_surjective π hπ]

end CFSG.LocalAnalysis.WeakClosure81

end
