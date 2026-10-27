module

public import CFSG.LocalAnalysis.ZStar.PrincipalBlockCandidate
public import CFSG.LocalAnalysis.ZStar.BrauerProjection

public section

namespace CFSG

namespace ZStar.BrauerPrincipal

open ZStar.Helpers ZStar
  ZStar.BrauerProjection

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

abbrev involutionCentralizer (w : G) : Subgroup G :=
  Subgroup.centralizer ({w} : Set G)

@[expose] noncomputable def projectedPrincipalBlock (w : G) :
    GroupAlgebraTwo (involutionCentralizer w) :=
  brauerProjection w (principalBlockCandidate G)

private theorem projectedPrincipalBlock_central (w : G) :
    IsGroupCentral (involutionCentralizer w)
      (projectedPrincipalBlock w) := by
  exact brauerProjection_isGroupCentral w (principalBlockCandidate G)
    (principalBlockCandidate_central G)

private theorem projectedPrincipalBlock_idempotent
    (w : G) (hw2 : w * w = 1) :
    projectedPrincipalBlock w * projectedPrincipalBlock w =
      projectedPrincipalBlock w := by
  exact (brauerProjection_central_idempotent w hw2
    (principalBlockCandidate G) (principalBlockCandidate_central G)
    (principalBlockCandidate_idempotent G)).2

private theorem projectedPrincipalBlock_augmentation
    (w : G) (hw2 : w * w = 1) :
    augmentationTwo (involutionCentralizer w)
      (projectedPrincipalBlock w) = 1 := by
  calc
    augmentationTwo (involutionCentralizer w)
        (projectedPrincipalBlock w) =
        augmentationTwo G (principalBlockCandidate G) :=
      augmentation_brauerProjection w hw2 (principalBlockCandidate G)
        (principalBlockCandidate_central G)
    _ = 1 := principalBlockCandidate_augmentation G

private theorem principalBlockCandidate_mul_projected
    (w : G) (hw2 : w * w = 1) :
    principalBlockCandidate (involutionCentralizer w) *
        projectedPrincipalBlock w =
      principalBlockCandidate (involutionCentralizer w) := by
  apply principalBlockCandidate_mul_eq_self_of_augmentation_one
    (involutionCentralizer w) (projectedPrincipalBlock w)
    (projectedPrincipalBlock_central w)
    (projectedPrincipalBlock_idempotent w hw2)
  rw [augmentationHom_apply, projectedPrincipalBlock_augmentation w hw2]

@[expose] noncomputable def brauerResidual (w : G) :
    GroupAlgebraTwo (involutionCentralizer w) :=
  projectedPrincipalBlock w -
    principalBlockCandidate (involutionCentralizer w)

theorem brauerResidual_central (w : G) :
    IsGroupCentral (involutionCentralizer w) (brauerResidual w) := by
  intro h
  rw [brauerResidual, mul_sub, sub_mul]
  rw [(projectedPrincipalBlock_central w) h]
  rw [(principalBlockCandidate_central (involutionCentralizer w)) h]

theorem brauerResidual_augmentation
    (w : G) (hw2 : w * w = 1) :
    augmentationHom (involutionCentralizer w) (brauerResidual w) = 0 := by
  rw [brauerResidual, map_sub]
  rw [augmentationHom_apply, projectedPrincipalBlock_augmentation w hw2]
  rw [augmentationHom_apply,
    principalBlockCandidate_augmentation (involutionCentralizer w)]
  exact sub_self 1

theorem brauerResidual_idempotent
    (w : G) (hw2 : w * w = 1) :
    brauerResidual w * brauerResidual w = brauerResidual w := by
  let H := involutionCentralizer w
  let q : GroupAlgebraTwo H := projectedPrincipalBlock w
  let e : GroupAlgebraTwo H := principalBlockCandidate H
  have hq2 : q * q = q := projectedPrincipalBlock_idempotent w hw2
  have he2 : e * e = e := principalBlockCandidate_idempotent H
  have heq : e * q = e := principalBlockCandidate_mul_projected w hw2
  have hqe : q * e = e := by
    calc
      q * e = e * q := ((principalBlockCandidate_central H).commute H q).eq.symm
      _ = e := heq
  change (q - e) * (q - e) = q - e
  calc
    (q - e) * (q - e) = q * q - q * e - e * q + e * e := by
      noncomm_ring
    _ = q - e := by rw [hq2, hqe, heq, he2]; abel

theorem brauerResidual_isAugmentationZeroCentralIdempotent
    (w : G) (hw2 : w * w = 1) :
    IsAugmentationZeroCentralIdempotent
      (involutionCentralizer w) (brauerResidual w) :=
  ⟨brauerResidual_central w, brauerResidual_idempotent w hw2,
    brauerResidual_augmentation w hw2⟩

private theorem principalBlockCandidate_mul_brauerResidual
    (w : G) (hw2 : w * w = 1) :
    principalBlockCandidate (involutionCentralizer w) * brauerResidual w = 0 := by
  rw [brauerResidual, mul_sub]
  rw [principalBlockCandidate_mul_projected w hw2]
  rw [principalBlockCandidate_idempotent, sub_self]

theorem brauerResidual_mul_principalBlockCandidate
    (w : G) (hw2 : w * w = 1) :
    brauerResidual w * principalBlockCandidate (involutionCentralizer w) = 0 := by
  have hcomm := (brauerResidual_central w).commute
    (involutionCentralizer w)
    (principalBlockCandidate (involutionCentralizer w))
  rw [hcomm.eq]
  exact principalBlockCandidate_mul_brauerResidual w hw2

private theorem projectedPrincipalBlock_mul_brauerResidual
    (w : G) (hw2 : w * w = 1) :
    projectedPrincipalBlock w * brauerResidual w = brauerResidual w := by
  rw [brauerResidual, mul_sub]
  rw [projectedPrincipalBlock_idempotent w hw2]
  have hcomm := (principalBlockCandidate_central (involutionCentralizer w)).commute
    (involutionCentralizer w) (projectedPrincipalBlock w)
  rw [← hcomm.eq, principalBlockCandidate_mul_projected w hw2]

@[expose] def ResidualHasGlobalBlockLift (w : G) : Prop :=
  ∃ f : GroupAlgebraTwo G,
    IsAugmentationZeroCentralIdempotent G f ∧
      brauerProjection w f = brauerResidual w

theorem brauerResidual_eq_zero_of_globalBlockLift
    (w : G) (hw2 : w * w = 1)
    (hlift : ResidualHasGlobalBlockLift w) :
    brauerResidual w = 0 := by
  obtain ⟨f, hf, hproj⟩ := hlift
  have hglobal : principalBlockCandidate G * f = 0 :=
    principalBlockCandidate_annihilates G f hf
  have hmul :
      brauerProjection w (principalBlockCandidate G * f) =
        projectedPrincipalBlock w * brauerProjection w f :=
    brauerProjection_mul w hw2 (principalBlockCandidate G) f
      (conjInvariantBy_of_isGroupCentral w (principalBlockCandidate G)
        (principalBlockCandidate_central G))
      (conjInvariantBy_of_isGroupCentral w f hf.1)
  have hzero : projectedPrincipalBlock w * brauerResidual w = 0 := by
    rw [← hproj, ← hmul, hglobal]
    exact map_zero (brauerProjection w)
  rw [projectedPrincipalBlock_mul_brauerResidual w hw2] at hzero
  exact hzero

end ZStar.BrauerPrincipal

end CFSG
