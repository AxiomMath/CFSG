module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverRootData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralCoverBilinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.BinaryScalarInvariance

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "G" => SuzukiMatrixGroup m

@[expose] def suzukiCoverTorusGL : Subgroup (GL (Fin 4) K) :=
  Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}

theorem suzukiCoverTorusGL_le : suzukiCoverTorusGL m ≤ G := by
  rw [suzukiCoverTorusGL, Subgroup.closure_le]
  intro A hA
  exact Subgroup.subset_closure (Or.inr (Or.inl hA))

@[expose] def suzukiCoverTorus : Subgroup G :=
  (suzukiCoverTorusGL m).subgroupOf G

@[expose] def suzukiCoverTorusBridge : suzukiCoverTorus m ≃* suzukiCoverTorusGL m :=
  Subgroup.subgroupOfEquivOfLe (suzukiCoverTorusGL_le m)

@[expose] def suzukiCoverTorusHom : Kˣ →* suzukiCoverTorus m where
  toFun x := ⟨⟨SuzukiTorusGL m x,
    suzukiCoverTorusGL_le m (Subgroup.subset_closure ⟨x, rfl⟩)⟩,
    Subgroup.subset_closure ⟨x, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact suzukiTorusGL_one m
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact (suzukiTorusGL_mul m x y).symm

@[simp] theorem suzukiCoverTorusHom_coe (x : Kˣ) :
    (((suzukiCoverTorusHom m x : suzukiCoverTorus m) : G) : GL (Fin 4) K) =
      SuzukiTorusGL m x := rfl

theorem suzukiCoverTorusHom_bijective (hm : 0 < m) :
    Function.Bijective (suzukiCoverTorusHom m) := by
  rcases huppert_blackburn_XI_3_1 m hm (suzukiCoverTits m) (suzukiCoverTits_square m) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, he⟩, _⟩
  constructor
  · intro x y hxy
    apply e.injective
    apply Subtype.ext
    exact (he x).trans ((congrArg
      (fun t : suzukiCoverTorus m => ((t : G) : GL (Fin 4) K)) hxy).trans (he y).symm)
  · intro t
    obtain ⟨x, hx⟩ := (suzukiTorusGL_mem_closure_iff m ((t : G) : GL (Fin 4) K)).mp t.property
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx.symm

@[expose] def suzukiCoverTorusEquiv (hm : 0 < m) : Kˣ ≃* suzukiCoverTorus m :=
  MulEquiv.ofBijective (suzukiCoverTorusHom m) (suzukiCoverTorusHom_bijective m hm)

@[simp] theorem suzukiCoverTorusEquiv_apply (hm : 0 < m) (x : Kˣ) :
    suzukiCoverTorusEquiv m hm x = suzukiCoverTorusHom m x := rfl

theorem suzukiCoverTorus_card (hm : 0 < m) :
    Nat.card (suzukiCoverTorus m) = 2 ^ (2 * m + 1) - 1 := by
  calc
    Nat.card (suzukiCoverTorus m) = Nat.card Kˣ :=
      Nat.card_congr (suzukiCoverTorusEquiv m hm).symm.toEquiv
    _ = Nat.card K - 1 := Nat.card_units K
    _ = 2 ^ (2 * m + 1) - 1 := by
      rw [GaloisField.card 2 (2 * m + 1) (by omega)]

theorem suzukiCoverTorus_odd (hm : 0 < m) : Odd (Nat.card (suzukiCoverTorus m)) := by
  rw [suzukiCoverTorus_card m hm]
  have hpos : 0 < 2 ^ (2 * m + 1) := by positivity
  have heven : Even (2 ^ (2 * m + 1)) := even_two.pow_of_ne_zero (by omega)
  exact Nat.Even.sub_odd hpos heven odd_one

theorem suzukiCoverTorus_le_normalizer :
    suzukiCoverTorus m ≤ Subgroup.normalizer (suzukiCoverRoot m : Set G) := by
  intro t ht
  have hnormal := suzukiTorusClosure_le_normalizer_rootClosure m (suzukiCoverTits m)
    (suzukiCoverTits_square m) (suzukiCoverTits_apply m) ht
  rw [Subgroup.mem_normalizer_iff] at hnormal ⊢
  intro z
  exact hnormal ((z : G) : GL (Fin 4) K)

theorem suzukiCoverTorus_action_root (x : Kˣ) (a b : K) :
    coverNormalizerAction (suzukiCoverRoot m) (suzukiCoverTorus m)
        (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x)
        (suzukiCoverRootElement m a b) =
      suzukiCoverRootElement m ((x : K) * a) ((x : K) * suzukiCoverTits m (x : K) * b) := by
  apply Subtype.ext
  rw [coverNormalizerAction_coe]
  apply Subtype.ext
  change SuzukiTorusGL m x * SuzukiRootGL m a b * (SuzukiTorusGL m x)⁻¹ =
    SuzukiRootGL m ((x : K) * a) ((x : K) * suzukiCoverTits m (x : K) * b)
  exact suzukiTorusGL_conj_root m (suzukiCoverTits m) (suzukiCoverTits_square m)
    (suzukiCoverTits_apply m) a b x

@[expose] def suzukiCoverNorm : Kˣ →* Kˣ where
  toFun x := x * Units.mapEquiv (suzukiCoverTits m).toMulEquiv x
  map_one' := by simp
  map_mul' x y := by simp [mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem suzukiCoverNorm_coe (x : Kˣ) :
    (suzukiCoverNorm m x : K) = (x : K) * suzukiCoverTits m (x : K) := rfl

theorem suzukiCoverNorm_bijective : Function.Bijective (suzukiCoverNorm m) := by
  have hinj : Function.Injective (suzukiCoverNorm m) := by
    apply (suzukiCoverNorm m).ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply (binaryGaloisField_tits_norm_eq_one_iff m (suzukiCoverTits m)
      (suzukiCoverTits_square m) x).mp
    exact congrArg Units.val (MonoidHom.mem_ker.mp hx)
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem suzukiCoverDerived_action (hm : 0 < m) (x : Kˣ)
    (w : commutator (suzukiCoverRoot m)) :
    (suzukiCoverDerivedEquiv m hm
      (coverDerivedAction (suzukiCoverRoot m) (suzukiCoverTorus m)
        (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x) w)).toAdd =
      (suzukiCoverNorm m x : K) * (suzukiCoverDerivedEquiv m hm w).toAdd := by
  obtain ⟨b, hb⟩ := ((suzukiCoverRoot_structure m hm).2.2.2 w.val).mp w.property
  rw [suzukiCoverDerivedEquiv_apply]
  change (((((coverNormalizerAction (suzukiCoverRoot m) (suzukiCoverTorus m)
    (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x) w.val : suzukiCoverRoot m) : G) :
      GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) = _
  rw [hb, suzukiCoverTorus_action_root, suzukiCoverDerivedEquiv_apply, hb]
  rfl

theorem suzukiCoverAbelian_action (hm : 0 < m) (x : Kˣ)
    (v : Abelianization (suzukiCoverRoot m)) :
    (suzukiCoverAbelianEquiv m hm
      (coverAbelianAction (suzukiCoverRoot m) (suzukiCoverTorus m)
        (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x) v)).toAdd =
      (x : K) * (suzukiCoverAbelianEquiv m hm v).toAdd := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (commutator (suzukiCoverRoot m)) v
  change (suzukiCoverAbelianEquiv m hm (Abelianization.map _ (Abelianization.of z))).toAdd =
    (x : K) * (suzukiCoverAbelianEquiv m hm (Abelianization.of z)).toAdd
  rw [Abelianization.map_of, suzukiCoverAbelianEquiv_of, suzukiCoverAbelianEquiv_of]
  obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective m z
  change (suzukiCoverFirstCoord m hm (coverNormalizerAction (suzukiCoverRoot m)
    (suzukiCoverTorus m) (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x)
      (suzukiCoverRootElement m a b))).toAdd = (x : K) * a
  rw [suzukiCoverTorus_action_root]
  rfl

end CFSG.ShultStronglyClosedTI
