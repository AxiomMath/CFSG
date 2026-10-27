module

public import CFSG.LocalAnalysis.ZStar.Helpers

public section

namespace CFSG

namespace ZStar

open ZStar.Helpers

abbrev A (G : Type*) [Group G] := GroupAlgebraTwo G

theorem principalBlockCandidate_mul_eq_self_of_augmentation_one
    (G : Type*) [Group G] [Fintype G]
    (f : A G) (hfcentral : IsGroupCentral G f)
    (hfidempotent : f * f = f) (hfaugmentation : augmentationHom G f = 1) :
    principalBlockCandidate G * f = principalBlockCandidate G := by
  have hcomplement : IsAugmentationZeroCentralIdempotent G (1 - f) := by
    refine ⟨hfcentral.one_sub G, one_sub_idempotent hfidempotent, ?_⟩
    rw [map_sub, map_one, hfaugmentation, sub_self]
  have hannihilates := principalBlockCandidate_annihilates G (1 - f) hcomplement
  rw [mul_sub, mul_one] at hannihilates
  exact (sub_eq_zero.mp hannihilates).symm

theorem principalBlockCandidate_primitive
    (G : Type*) [Group G] [Fintype G]
    (f : A G) (hfcentral : IsGroupCentral G f)
    (hfidempotent : f * f = f)
    (hfbelow : principalBlockCandidate G * f = f) :
    f = 0 ∨ f = principalBlockCandidate G := by
  have haug_cases : augmentationHom G f = 0 ∨ augmentationHom G f = 1 := by
    let a := augmentationHom G f
    have ha : a.val = 0 ∨ a.val = 1 := by
      have := ZMod.val_lt a
      omega
    rcases ha with ha | ha
    · left
      exact (ZMod.val_eq_zero a).mp ha
    · right
      calc
        augmentationHom G f = (a.val : ZMod 2) :=
          (ZMod.natCast_zmod_val a).symm
        _ = 1 := by rw [ha]; rfl
  rcases haug_cases with haug | haug
  · left
    have hfzero := principalBlockCandidate_annihilates G f
      ⟨hfcentral, hfidempotent, haug⟩
    exact hfbelow.symm.trans hfzero
  · right
    have hftop := principalBlockCandidate_mul_eq_self_of_augmentation_one
      G f hfcentral hfidempotent haug
    exact hfbelow.symm.trans hftop

theorem principalBlockCandidate_unique
    (G : Type*) [Group G] [Fintype G]
    (b : A G) (hbcentral : IsGroupCentral G b)
    (hbidempotent : b * b = b) (hbaugmentation : augmentationHom G b = 1)
    (hbannihilates : ∀ f : A G,
      IsAugmentationZeroCentralIdempotent G f → b * f = 0) :
    b = principalBlockCandidate G := by
  let e := principalBlockCandidate G
  have hecentral : IsGroupCentral G e := principalBlockCandidate_central G
  have heidempotent : e * e = e := principalBlockCandidate_idempotent G
  have heaugmentation : augmentationHom G e = 1 := by
    rw [augmentationHom_apply]
    exact principalBlockCandidate_augmentation G
  have heb : e * b = e :=
    principalBlockCandidate_mul_eq_self_of_augmentation_one
      G b hbcentral hbidempotent hbaugmentation
  have hcomplement : IsAugmentationZeroCentralIdempotent G (1 - e) := by
    refine ⟨hecentral.one_sub G, one_sub_idempotent heidempotent, ?_⟩
    rw [map_sub, map_one, heaugmentation, sub_self]
  have hbcomp := hbannihilates (1 - e) hcomplement
  rw [mul_sub, mul_one] at hbcomp
  have hbe : b * e = b := (sub_eq_zero.mp hbcomp).symm
  calc
    b = b * e := hbe.symm
    _ = e * b := (hecentral.commute G b).eq.symm
    _ = e := heb

theorem fusion_of_central_multiple
    (G : Type*) [Group G] [Fintype G] (t : G)
    (ht2 : t * t = 1)
    (z : A G) (hz : IsGroupCentral G z)
    (hze : MonoidAlgebra.single t 1 * z * principalBlockCandidate G =
      principalBlockCandidate G) :
    ∀ g : G,
      MonoidAlgebra.single (g * t * g⁻¹) 1 * principalBlockCandidate G =
        MonoidAlgebra.single t 1 * principalBlockCandidate G := by
  let e := principalBlockCandidate G
  have he : IsGroupCentral G e := principalBlockCandidate_central G
  have hte : MonoidAlgebra.single t 1 * e = z * e := by
    have h := congrArg (fun a : A G => MonoidAlgebra.single t 1 * a) hze
    calc
      MonoidAlgebra.single t 1 * e =
          MonoidAlgebra.single t 1 *
            ((MonoidAlgebra.single t 1 * z) * e) := h.symm
      _ = ((MonoidAlgebra.single t 1 * MonoidAlgebra.single t 1) * z) * e := by
        simp only [mul_assoc]
      _ = z * e := by
        rw [MonoidAlgebra.single_mul_single, ht2]
        simp only [one_mul]
        rw [← MonoidAlgebra.one_def, one_mul]
  have htcentral : IsGroupCentral G (MonoidAlgebra.single t 1 * e) := by
    rw [hte]
    exact hz.mul G he
  intro g
  calc
    MonoidAlgebra.single (g * t * g⁻¹) 1 * e =
        MonoidAlgebra.single g 1 * MonoidAlgebra.single t 1 *
          (MonoidAlgebra.single g⁻¹ 1 * e) := by
      rw [← mul_assoc, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single]
      simp
    _ = MonoidAlgebra.single g 1 * (MonoidAlgebra.single t 1 * e) *
          MonoidAlgebra.single g⁻¹ 1 := by
      rw [he g⁻¹]
      simp only [mul_assoc]
    _ = (MonoidAlgebra.single t 1 * e) *
          (MonoidAlgebra.single g 1 * MonoidAlgebra.single g⁻¹ 1) := by
      rw [htcentral g]
      simp only [mul_assoc]
    _ = MonoidAlgebra.single t 1 * e := by
      have hginv : MonoidAlgebra.single g 1 * MonoidAlgebra.single g⁻¹ 1 =
          (1 : A G) := by
        rw [MonoidAlgebra.single_mul_single]
        rw [mul_inv_cancel]
        simp only [one_mul]
        rw [← MonoidAlgebra.one_def]
      rw [hginv, mul_one]

end ZStar

end CFSG
