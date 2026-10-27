module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCoverRootCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.BinaryScalarInvariance

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open Matrix
open scoped commutatorElement MatrixGroups IsMulCommutative

universe u v w

theorem linearCover_commutator_lift_independent {E : Type u} {J : Type v}
    [Group E] [Group J] (η : E →* J) (hcentral : η.ker ≤ Subgroup.center E)
    {x x' y y' : E} (hx : η x = η x') (hy : η y = η y') :
    ⁅x, y⁆ = ⁅x', y'⁆ := by
  have hc := hcentral (η.eq_iff.mp hx)
  have hd := hcentral (η.eq_iff.mp hy)
  have hxrep : x = x' * (x'⁻¹ * x) := by group
  have hyrep : y = y' * (y'⁻¹ * y) := by group
  have hccomm : Commute (x'⁻¹ * x) y := (Subgroup.mem_center_iff.mp hc y).symm
  have hdcomm : Commute x' (y'⁻¹ * y) := Subgroup.mem_center_iff.mp hd x'
  calc
    ⁅x, y⁆ = ⁅x' * (x'⁻¹ * x), y⁆ := congrArg (fun a : E => ⁅a, y⁆) hxrep
    _ = ⁅x', y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hccomm.commutator_eq,
        mul_one, mul_inv_cancel, one_mul]
    _ = ⁅x', y' * (y'⁻¹ * y)⁆ := congrArg (fun a : E => ⁅x', a⁆) hyrep
    _ = ⁅x', y'⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hdcomm.commutator_eq,
        mul_one, mul_inv_cancel_right]

variable {K : Type u} [Field K] {E : Type v} [Group E]

@[expose] def linearCoverPreimageSylow [Finite K] [CharP K 2]
    (f : ℕ) (hcard : Nat.card K = 2 ^ f) (η : E →* SpecialLinearGroup (Fin 2) K)
    (hsurj : Function.Surjective η) (hp : IsPGroup 2 η.ker) : Sylow 2 E :=
  (linearCoverRootSylow f hcard).comapOfKerIsPGroup η hp
    (by rw [η.range_eq_top_of_surjective hsurj]; exact le_top)

theorem linearCoverPreimageSylow_coe [Finite K] [CharP K 2]
    (f : ℕ) (hcard : Nat.card K = 2 ^ f) (η : E →* SpecialLinearGroup (Fin 2) K)
    (hsurj : Function.Surjective η) (hp : IsPGroup 2 η.ker) :
    (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E) =
      (linearCoverRootSubgroup K).comap η := rfl

theorem linearCover_root_commutator_mem_kernel [CharP K 2]
    (η : E →* SpecialLinearGroup (Fin 2) K) {x y : E}
    (hx : η x ∈ linearCoverRootSubgroup K) (hy : η y ∈ linearCoverRootSubgroup K) :
    ⁅x, y⁆ ∈ η.ker := by
  change η ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  exact congrArg Subtype.val
    (isMulCommutative_iff.mp linearCoverRoot_elementary.1
      (⟨η x, hx⟩ : linearCoverRootSubgroup K) ⟨η y, hy⟩)

theorem linearCover_sylow_derived_eq_kernel [Finite K] [CharP K 2] [Finite E]
    [Group.IsPerfect E] (f : ℕ) (hcard : Nat.card K = 2 ^ f)
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) :
    (commutator (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E)).map
      (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E).subtype = η.ker := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := linearCoverPreimageSylow f hcard η hsurj hp
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact linearCover_root_commutator_mem_kernel η x.property y.property
  · exact central_pSubgroup_le_sylow_derived P η.ker hcentral hp

@[expose] def linearCoverRootLift (η : E →* SpecialLinearGroup (Fin 2) K)
    (hsurj : Function.Surjective η) (t : K) : E :=
  (hsurj (linearCoverRoot t)).choose

theorem linearCoverRootLift_image (η : E →* SpecialLinearGroup (Fin 2) K)
    (hsurj : Function.Surjective η) (t : K) :
    η (linearCoverRootLift η hsurj t) = linearCoverRoot t :=
  (hsurj (linearCoverRoot t)).choose_spec

@[expose] def linearCoverCommutator [CharP K 2]
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η) (x y : K) :
    η.ker :=
  ⟨⁅linearCoverRootLift η hsurj x, linearCoverRootLift η hsurj y⁆,
    linearCover_root_commutator_mem_kernel η
      (by rw [linearCoverRootLift_image]; exact ⟨Multiplicative.ofAdd x, rfl⟩)
      (by rw [linearCoverRootLift_image]; exact ⟨Multiplicative.ofAdd y, rfl⟩)⟩

theorem linearCoverCommutator_eq_of_lifts [CharP K 2]
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) {x y : K} {a b : E}
    (ha : η a = linearCoverRoot x) (hb : η b = linearCoverRoot y) :
    (linearCoverCommutator η hsurj x y : E) = ⁅a, b⁆ :=
  linearCover_commutator_lift_independent η hcentral
    ((linearCoverRootLift_image η hsurj x).trans ha.symm)
    ((linearCoverRootLift_image η hsurj y).trans hb.symm)

theorem linearCoverCommutator_add_left [CharP K 2]
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (x x' y : K) :
    linearCoverCommutator η hsurj (x + x') y =
      linearCoverCommutator η hsurj x y * linearCoverCommutator η hsurj x' y := by
  apply Subtype.ext
  have h := linearCoverCommutator_eq_of_lifts η hsurj hcentral
    (a := linearCoverRootLift η hsurj x * linearCoverRootLift η hsurj x')
    (b := linearCoverRootLift η hsurj y)
    (by rw [map_mul, linearCoverRootLift_image, linearCoverRootLift_image,
      ← AddChar.map_add_eq_mul]) (linearCoverRootLift_image η hsurj y)
  rw [h, commutatorElement_mul_left_eq_conj_mul]
  have hc := hcentral (linearCoverCommutator η hsurj x' y).property
  have heq := Subgroup.mem_center_iff.mp hc (linearCoverRootLift η hsurj x)
  change linearCoverRootLift η hsurj x * (linearCoverCommutator η hsurj x' y : E) *
    (linearCoverRootLift η hsurj x)⁻¹ * (linearCoverCommutator η hsurj x y : E) =
    (linearCoverCommutator η hsurj x y : E) * (linearCoverCommutator η hsurj x' y : E)
  rw [heq, mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp hc (linearCoverCommutator η hsurj x y)).symm

theorem linearCoverCommutator_add_right [CharP K 2]
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (x y y' : K) :
    linearCoverCommutator η hsurj x (y + y') =
      linearCoverCommutator η hsurj x y * linearCoverCommutator η hsurj x y' := by
  apply Subtype.ext
  have h := linearCoverCommutator_eq_of_lifts η hsurj hcentral
    (a := linearCoverRootLift η hsurj x)
    (b := linearCoverRootLift η hsurj y * linearCoverRootLift η hsurj y')
    (linearCoverRootLift_image η hsurj x)
    (by rw [map_mul, linearCoverRootLift_image, linearCoverRootLift_image,
      ← AddChar.map_add_eq_mul])
  rw [h, commutatorElement_mul_right_eq_mul_conj]
  have hc := hcentral (linearCoverCommutator η hsurj x y').property
  have heq := Subgroup.mem_center_iff.mp hc (linearCoverRootLift η hsurj y)
  change (linearCoverCommutator η hsurj x y : E) * linearCoverRootLift η hsurj y *
    (linearCoverCommutator η hsurj x y' : E) * (linearCoverRootLift η hsurj y)⁻¹ =
      (linearCoverCommutator η hsurj x y : E) * (linearCoverCommutator η hsurj x y' : E)
  calc
    _ = (linearCoverCommutator η hsurj x y : E) *
        (linearCoverRootLift η hsurj y * (linearCoverCommutator η hsurj x y' : E) *
          (linearCoverRootLift η hsurj y)⁻¹) := by group
    _ = _ := by rw [heq, mul_inv_cancel_right]

theorem linearCoverCommutator_scalar_invariant [Finite K] [CharP K 2]
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (a : K) (ha : a ≠ 0) (x y : K) :
    linearCoverCommutator η hsurj (a * x) (a * y) =
      linearCoverCommutator η hsurj x y := by
  obtain ⟨d, hd⟩ := linearCover_scalar_conjugator a ha
  obtain ⟨e, he⟩ := hsurj d
  apply Subtype.ext
  have hx : η ((MulAut.conj e) (linearCoverRootLift η hsurj x)) =
      linearCoverRoot (a * x) := by
    simpa only [MulAut.conj_apply, map_mul, map_inv, he, linearCoverRootLift_image] using hd x
  have hy : η ((MulAut.conj e) (linearCoverRootLift η hsurj y)) =
      linearCoverRoot (a * y) := by
    simpa only [MulAut.conj_apply, map_mul, map_inv, he, linearCoverRootLift_image] using hd y
  rw [linearCoverCommutator_eq_of_lifts η hsurj hcentral hx hy,
    ← map_commutatorElement]
  have hc := hcentral (linearCoverCommutator η hsurj x y).property
  change e * (linearCoverCommutator η hsurj x y : E) * e⁻¹ =
    (linearCoverCommutator η hsurj x y : E)
  rw [Subgroup.mem_center_iff.mp hc e, mul_inv_cancel_right]

theorem linearCoverCommutator_eq_one [Finite K] [CharP K 2]
    (hcard : 4 < Nat.card K) (η : E →* SpecialLinearGroup (Fin 2) K)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E) :
    ∀ x y : K, linearCoverCommutator η hsurj x y = 1 := by
  let : IsMulCommutative η.ker :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp
      (hcentral a.property) b.val).symm)⟩⟩
  let : CommGroup η.ker := IsMulCommutative.instCommGroup
  let b : K → K → Additive η.ker := fun x y =>
    Additive.ofMul (linearCoverCommutator η hsurj x y)
  have hzero := binaryScalarInvariantBiadditive_eq_zero hcard b
    (fun x x' y => congrArg Additive.ofMul (linearCoverCommutator_add_left η hsurj hcentral x x' y))
    (fun x y y' => congrArg Additive.ofMul (linearCoverCommutator_add_right η hsurj hcentral x y y'))
    (fun a ha x y => congrArg Additive.ofMul
      (linearCoverCommutator_scalar_invariant η hsurj hcentral a ha x y))
  intro x y
  exact congrArg Additive.toMul (hzero x y)

theorem large_even_linear_central_two_cover_kernel_eq_bot [Finite K] [CharP K 2]
    [Finite E] [Group.IsPerfect E] (f : ℕ) (hf : 3 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (η : E →* SpecialLinearGroup (Fin 2) K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  have hlarge : 4 < Nat.card K := by
    rw [hcard]
    have h := Nat.pow_le_pow_right (n := 2) (by decide) hf
    omega
  let P := linearCoverPreimageSylow f hcard η hsurj hp
  have hcomm : IsMulCommutative (P : Subgroup E) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := a.property
    obtain ⟨y, hy⟩ := b.property
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hb := linearCoverCommutator_eq_of_lifts η hsurj hcentral
      (x := x.toAdd) (y := y.toAdd) hx.symm hy.symm
    exact hb.symm.trans (congrArg (fun c : η.ker => (c : E))
      (linearCoverCommutator_eq_one hlarge η hsurj hcentral x.toAdd y.toAdd))
  let : IsMulCommutative (P : Subgroup E) := hcomm
  have heq := linearCover_sylow_derived_eq_kernel f hcard η hsurj hcentral hp
  change (commutator (P : Subgroup E)).map (P : Subgroup E).subtype = η.ker at heq
  rw [commutator_eq_bot, Subgroup.map_bot] at heq
  exact heq.symm

theorem large_even_linear_central_two_cover_trivial {F : Type} [Field F] [Finite F]
    [CharP F 2] [Finite E] [Group.IsPerfect E] (f : ℕ) (hf : 3 ≤ f)
    (hcard : Nat.card F = 2 ^ f) (η : E →* GLAProj (GLASLGroup (Fin 2) F))
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hp : IsPGroup 2 η.ker) :
    η.ker = ⊥ ∧ ∃ e : E ≃* GLAProj (GLASLGroup (Fin 2) F), ∀ x : E, e x = η x := by
  let eJ := linearCover_glaEquivSL (F := F)
  let φ := eJ.toMonoidHom.comp η
  have hker : φ.ker = η.ker := by
    ext x
    change eJ (η x) = 1 ↔ η x = 1
    exact eJ.map_eq_one_iff
  have hbot : η.ker = ⊥ := by
    have h := large_even_linear_central_two_cover_kernel_eq_bot f hf hcard φ
      (eJ.surjective.comp hsurj) (hker.symm ▸ hcentral) (hker.symm ▸ hp)
    exact hker.symm.trans h
  exact ⟨hbot, MulEquiv.ofBijective η ⟨η.ker_eq_bot_iff.mp hbot, hsurj⟩, fun _ => rfl⟩

end CFSG.ShultStronglyClosedTI
