module

public import CFSG.RankThree.PartOne.D4RC.ParaBruhat
public import CFSG.RankThree.PartOne.D4RC.ParaConn
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleLang
public import CFSG.LieType.AlgebraicGroups.ExactAffineRealizationGroups
public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.D4RC

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.SeitzReduction

open scoped CFSG.ConvolutionPoints

local notation "D4T" => TwistTag.D4.tag

variable {L : Type} [Field L] [CharP L 2]


theorem rcp_twistHom_pinnedX_highRoot (σ : L →+* L) (c : L) :
    twistHom TwistTag.D4 L σ (pinnedX D4T L (highRoot D4T) c) =
      pinnedX D4T L (highRoot D4T) (σ c) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have e1 : Units.map (entrywiseHom σ) (pinnedX D4T L (highRoot D4T) c) =
      pinnedX D4T L (highRoot D4T) (σ c) := Units.ext (entrywise_pinnedX σ _ c)
  have e2 := twistHom_id_pinnedX (t := TwistTag.D4) (K := L) h2 (isRoot_highRoot D4T) (σ c)
  have e3 : permLattice TwistTag.D4.perm (highRoot D4T) = highRoot D4T := by
    funext i
    revert i
    decide
  rw [e3] at e2
  rw [← e2, twistHom_apply, twistHom_apply, e1]
  congr 2
  exact (Units.ext (entrywise_id _)).symm

theorem rcp_twistHom_mem_parabolic (σ : L →+* L) {m : ModGL D4T L}
    (hm : m ∈ parabolicSubgroup D4T L d4PerpNodes) :
    twistHom TwistTag.D4 L σ m ∈ parabolicSubgroup D4T L d4PerpNodes := by
  have hmG : m ∈ adjointGroup D4T L := parabolicSubgroup_le_adjointGroup _ _ _ hm
  have hn := rcp_parabolicSubgroup_le_normalizer (K := L) hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn
  have hx : m * pinnedX D4T L (highRoot D4T) 1 * m⁻¹ ∈ rootSubgroup D4T L (highRoot D4T) := by
    rw [← hn]
    exact ⟨_, mem_rootSubgroup.2 ⟨1, rfl⟩, rfl⟩
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hx
  refine rcp_mem_parabolicSubgroup_of_conj (twistHom_mem_adjointGroup TwistTag.D4 L σ hmG)
    (c := 1) (e := σ c) one_ne_zero ?_
  have h1 := congrArg (twistHom TwistTag.D4 L σ) hc
  have h3 : twistHom TwistTag.D4 L σ (pinnedX D4T L (highRoot D4T) 1) =
      pinnedX D4T L (highRoot D4T) 1 := by
    rw [rcp_twistHom_pinnedX_highRoot, map_one]
  rw [map_mul, map_mul, map_inv, rcp_twistHom_pinnedX_highRoot, h3] at h1
  exact h1.symm

theorem rcp_exists_fixed_conj [IsAlgClosed L] {f : ℕ} (hf : 1 ≤ f) {d : ModGL D4T L}
    (hd : d ∈ adjointGroup D4T L) {c e : L} (hc : c ≠ 0)
    (hst : twistHom TwistTag.D4 L (iterateFrobenius L 2 f)
        (d * pinnedX D4T L (highRoot D4T) c * d⁻¹) =
      d * pinnedX D4T L (highRoot D4T) e * d⁻¹) :
    ∃ k ∈ adjointGroup D4T L, twistHom TwistTag.D4 L (iterateFrobenius L 2 f) k = k ∧
      (rootSubgroup D4T L (highRoot D4T)).map (MulAut.conj k).toMonoidHom =
        (rootSubgroup D4T L (highRoot D4T)).map (MulAut.conj d).toMonoidHom := by
  set σ := iterateFrobenius L 2 f with hσ
  set F := twistHom TwistTag.D4 L σ with hF
  have hFθ : ∀ c, F (pinnedX D4T L (highRoot D4T) c) = pinnedX D4T L (highRoot D4T) (σ c) :=
    rcp_twistHom_pinnedX_highRoot σ
  have hσc : σ c ≠ 0 := by
    rw [hσ, iterateFrobenius_def]
    exact pow_ne_zero _ hc
  have hgG : d⁻¹ * F d ∈ adjointGroup D4T L :=
    mul_mem (inv_mem hd) (twistHom_mem_adjointGroup TwistTag.D4 L σ hd)
  have hgθ : (d⁻¹ * F d) * pinnedX D4T L (highRoot D4T) (σ c) * (d⁻¹ * F d)⁻¹ =
      pinnedX D4T L (highRoot D4T) e := by
    have h1 := hst
    rw [map_mul, map_mul, map_inv, hFθ] at h1
    calc (d⁻¹ * F d) * pinnedX D4T L (highRoot D4T) (σ c) * (d⁻¹ * F d)⁻¹
        = d⁻¹ * (F d * pinnedX D4T L (highRoot D4T) (σ c) * (F d)⁻¹) * d := by group
      _ = d⁻¹ * (d * pinnedX D4T L (highRoot D4T) e * d⁻¹) * d := by rw [h1]
      _ = pinnedX D4T L (highRoot D4T) e := by group
  have hgP : d⁻¹ * F d ∈ parabolicSubgroup D4T L d4PerpNodes :=
    rcp_mem_parabolicSubgroup_of_conj hgG hσc hgθ
  have hM := rcp_isConnectedAlgebraicSubgroup_parabolic (K := L) (τ := D4T) d4PerpNodes
  obtain ⟨z, hzP, hgz⟩ := exists_eq_inv_mul_frobTwistGL (τ := D4T) (k := L) 2 hf
    (diagramMap TwistTag.D4 L) hM hM.smooth.1 (fun m hm => rcp_twistHom_mem_parabolic σ hm) hgP
  have hFz : frobTwistGL D4T L 2 f (diagramMap TwistTag.D4 L) z = F z := rfl
  rw [hFz] at hgz
  have hzG : z ∈ adjointGroup D4T L := parabolicSubgroup_le_adjointGroup _ _ _ hzP
  have hFd : F d = d * (z⁻¹ * F z) := by
    rw [← hgz]
    group
  refine ⟨d * z⁻¹, mul_mem hd (inv_mem hzG), ?_, ?_⟩
  · rw [map_mul, map_inv, hFd]
    group
  · have hzn := rcp_parabolicSubgroup_le_normalizer (K := L) (inv_mem hzP)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hzn
    have hcomp : (MulAut.conj (d * z⁻¹)).toMonoidHom =
        (MulAut.conj d).toMonoidHom.comp (MulAut.conj z⁻¹).toMonoidHom :=
      MonoidHom.ext fun x => by simp [mul_assoc]
    have hzn' : (rootSubgroup D4T L (highRoot D4T)).map (MulAut.conj z⁻¹).toMonoidHom =
        rootSubgroup D4T L (highRoot D4T) := hzn
    rw [hcomp, ← Subgroup.map_map, hzn']

end CFSG.RankThree.PartOne.D4RC
