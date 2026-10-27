module

import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

@[expose] def HasNormalSimpleCentralizer (G : Type) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ IsSimpleGroup N ∧ ¬ (∀ x y : N, x * y = y * x) ∧
    Subgroup.centralizer (N : Set G) = ⊥

theorem HasNormalSimpleCentralizer.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hG : HasNormalSimpleCentralizer G) : HasNormalSimpleCentralizer H := by
  obtain ⟨N, hN, hs, hnab, hcent⟩ := hG
  refine ⟨N.map e.toMonoidHom, hN.map e.toMonoidHom e.surjective, ?_, ?_, ?_⟩
  · exact (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective).symm.isSimpleGroup
  · intro hc
    apply hnab
    intro x y
    have h1 := hc ⟨e (x : G), Subgroup.mem_map_of_mem e.toMonoidHom x.2⟩
      ⟨e (y : G), Subgroup.mem_map_of_mem e.toMonoidHom y.2⟩
    apply Subtype.ext
    apply e.injective
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_mul, map_mul] using h2
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_centralizer_iff] at hz
    have hz' : e.symm z ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (e n) (Subgroup.mem_map_of_mem e.toMonoidHom hn)
    rw [hcent, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'

theorem hasNormalSimpleCentralizer_projImage_glPi {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : Sec4.PiField π p f K) (hq2 : 2 < p ^ f) (hm : Sec4.ModThree π (p ^ f)) :
    HasNormalSimpleCentralizer ↥(projImage (Sec4.glPi π 3 (p ^ f) K)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  haveI : IsSimpleGroup (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  haveI : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : Subgroup ↥(projImage (Sec4.glPi π 3 (p ^ f) K)),
      N₀ = (projImage (Sec4.slPi π 3 (p ^ f) K)).subgroupOf
        (projImage (Sec4.glPi π 3 (p ^ f) K)) := ⟨_, rfl⟩
  refine ⟨N₀, ?_, ?_, ?_, ?_⟩
  · rw [hN₀, ← Sec8.Item8KFacts2Proof.perfectResidual_projImage_glPi_eq hK hq2]
    infer_instance
  · rw [hN₀]
    exact (Subgroup.subgroupOfEquivOfLe hSP).isSimpleGroup
  · intro hc
    have hNs : IsSimpleGroup ↥N₀ := by
      rw [hN₀]
      exact (Subgroup.subgroupOfEquivOfLe hSP).isSimpleGroup
    haveI := hNs.toNontrivial
    haveI : Group.IsPerfect ↥N₀ := by
      rw [hN₀]
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hSP).symm.toMonoidHom)
        (MulEquiv.surjective _)
    haveI : IsMulCommutative ↥N₀ := ⟨⟨hc⟩⟩
    exact Group.IsPerfect.not_isMulCommutative ↥N₀ this
  · rw [eq_bot_iff]
    rintro ⟨y, hy⟩ hx
    rw [Subgroup.mem_centralizer_iff] at hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    have hcomm : ∀ s ∈ Sec4.slPi π 3 (p ^ f) K,
        Matrix.ProjGenLinGroup.mk g * Matrix.ProjGenLinGroup.mk s =
          Matrix.ProjGenLinGroup.mk s * Matrix.ProjGenLinGroup.mk g := by
      intro s hs
      have hsN : (⟨Matrix.ProjGenLinGroup.mk s, hSP (Subgroup.mem_map_of_mem _ hs)⟩ :
          ↥(projImage (Sec4.glPi π 3 (p ^ f) K))) ∈ N₀ := by
        rw [hN₀]
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hs)
      exact (congrArg Subtype.val (hx _ hsN)).symm
    have hg' := Sec13.mem_statedScalars_of_commute_mk hK hm hq2 hcomm
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    show Matrix.ProjGenLinGroup.mk g = 1
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hg'

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
