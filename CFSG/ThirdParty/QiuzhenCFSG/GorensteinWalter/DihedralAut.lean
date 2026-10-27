module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Automorphisms of dihedral 2-groups

The automorphism group of `D_{2^{m+1}}` (`m ≥ 2`) is a 2-group.  The
construction below records an automorphism by its restriction to the cyclic
rotation subgroup and by the image of one reflection.  These data form the
semidirect product of the rotation subgroup by its automorphism group.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open DihedralGroup

universe u

private abbrev D (m : ℕ) := DihedralGroup (2 ^ m)

private abbrev R (m : ℕ) : Subgroup (D m) :=
  Subgroup.zpowers (DihedralGroup.r 1)

private lemma rotation_ne_zero (m : ℕ) : 2 ^ m ≠ 0 := by
  positivity

private lemma rotation_ne_one (m : ℕ) (hm : 2 ≤ m) : 2 ^ m ≠ 1 := by
  have : 4 ≤ 2 ^ m := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hm)
  omega

private lemma rotation_card (m : ℕ) (_hm : 1 ≤ m) :
    Nat.card (↥(R m)) = 2 ^ m := by
  let : NeZero (2 ^ m) := ⟨rotation_ne_zero m⟩
  change Nat.card (Subgroup.zpowers (DihedralGroup.r 1 : D m)) = 2 ^ m
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]

private lemma rotation_mem_image (m : ℕ) (hm : 2 ≤ m) (f : MulAut (D m)) :
    f (DihedralGroup.r 1) ∈ R m := by
  let : NeZero (2 ^ m) := ⟨rotation_ne_zero m⟩
  have horder : orderOf (f (DihedralGroup.r 1)) = 2 ^ m := by
    rw [MulEquiv.orderOf_eq f, DihedralGroup.orderOf_r_one]
  rcases dihedralGroup_cases (f (DihedralGroup.r 1)) with ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [hi]
    exact r_mem_zpowers_r_one i
  · exfalso
    rw [hi, DihedralGroup.orderOf_sr] at horder
    have hlt : 2 < 2 ^ m := by
      have hpow : 4 ≤ 2 ^ m := by
        simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hm)
      omega
    omega

private lemma rotation_characteristic (m : ℕ) (hm : 2 ≤ m) :
    (R m).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro f x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
  rcases (Subgroup.mem_zpowers_iff.mp hy) with ⟨k, hk⟩
  rw [← hxy, ← hk, map_zpow]
  exact (R m).zpow_mem (rotation_mem_image m hm f) k

private lemma reflection_not_rotation (m : ℕ) :
    DihedralGroup.sr 0 ∉ R m := by
  exact sr_not_mem_zpowers_r_one 0

private lemma reflection_image_exists (m : ℕ) (hm : 2 ≤ m)
    (f : MulAut (D m)) :
    ∃ b : R m, f (DihedralGroup.sr 0) = DihedralGroup.sr 0 * (b : D m) := by
  let : NeZero (2 ^ m) := ⟨rotation_ne_zero m⟩
  let : (R m).Characteristic := rotation_characteristic m hm
  have hsnot : f (DihedralGroup.sr 0) ∉ R m := by
    intro hs
    have hmap : Subgroup.map f.toMonoidHom (R m) = R m :=
      (Subgroup.characteristic_iff_map_eq.mp (rotation_characteristic m hm) f)
    have hs' : f (DihedralGroup.sr 0) ∈ Subgroup.map f.toMonoidHom (R m) := by
      rw [hmap]
      exact hs
    rcases (Subgroup.mem_map.mp hs') with ⟨y, hy, hfy⟩
    have hys : y = DihedralGroup.sr 0 := f.injective hfy
    exact reflection_not_rotation m (hys ▸ hy)
  rcases dihedralGroup_cases (f (DihedralGroup.sr 0)) with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact False.elim (hsnot (hi ▸ r_mem_zpowers_r_one i))
  · refine ⟨⟨DihedralGroup.r i, r_mem_zpowers_r_one i⟩, ?_⟩
    rw [hi, DihedralGroup.sr_mul_r]
    simp

private lemma reflection_image_unique (m : ℕ) (f : MulAut (D m))
    {b c : R m}
    (hb : f (DihedralGroup.sr 0) = DihedralGroup.sr 0 * (b : D m))
    (hc : f (DihedralGroup.sr 0) = DihedralGroup.sr 0 * (c : D m)) :
    b = c := by
  apply Subtype.ext
  apply mul_left_cancel (a := (DihedralGroup.sr 0 : D m))
  rw [← hb, hc]

private noncomputable def reflection_image (m : ℕ) (hm : 2 ≤ m)
    (f : MulAut (D m)) : R m :=
  Classical.choose (reflection_image_exists m hm f)

private lemma reflection_image_spec (m : ℕ) (hm : 2 ≤ m) (f : MulAut (D m)) :
    f (DihedralGroup.sr 0) = DihedralGroup.sr 0 * (reflection_image m hm f : D m) :=
  Classical.choose_spec (reflection_image_exists m hm f)

private lemma restriction_apply_coe (m : ℕ) (hm : 2 ≤ m)
    (f : MulAut (D m)) (x : R m) :
    ((letI : (R m).Characteristic := rotation_characteristic m hm
      MulAut.characteristic (R m) f) x : D m) = f (x : D m) := by
  let : (R m).Characteristic := rotation_characteristic m hm
  rfl

private lemma reflection_image_one (m : ℕ) (hm : 2 ≤ m) :
    reflection_image m hm (1 : MulAut (D m)) = 1 := by
  apply Subtype.ext
  apply mul_left_cancel (a := (DihedralGroup.sr 0 : D m))
  simpa using (reflection_image_spec m hm (1 : MulAut (D m))).symm

private lemma reflection_image_mul (m : ℕ) (hm : 2 ≤ m)
    (f g : MulAut (D m)) :
    reflection_image m hm (f * g) =
      reflection_image m hm f *
        ((letI : (R m).Characteristic := rotation_characteristic m hm
          MulAut.characteristic (R m) f) (reflection_image m hm g)) := by
  let : (R m).Characteristic := rotation_characteristic m hm
  apply Subtype.ext
  apply mul_left_cancel (a := (DihedralGroup.sr 0 : D m))
  calc
    (DihedralGroup.sr 0 : D m) * (reflection_image m hm (f * g) : D m) =
        (f * g) (DihedralGroup.sr 0) :=
      (reflection_image_spec m hm (f * g)).symm
    _ = f (g (DihedralGroup.sr 0)) := by rw [MulAut.mul_apply]
    _ = f (DihedralGroup.sr 0 * (reflection_image m hm g : D m)) := by
      rw [reflection_image_spec m hm g]
    _ = f (DihedralGroup.sr 0) * f (reflection_image m hm g : D m) := by
      rw [map_mul]
    _ = (DihedralGroup.sr 0 * (reflection_image m hm f : D m)) *
        f (reflection_image m hm g : D m) := by
      rw [reflection_image_spec m hm f]
    _ = (DihedralGroup.sr 0 : D m) *
        ((reflection_image m hm f : D m) *
          f (reflection_image m hm g : D m)) := by simp [mul_assoc]
    _ = (DihedralGroup.sr 0 : D m) *
        ((reflection_image m hm f *
          (MulAut.characteristic (R m) f) (reflection_image m hm g) : R m) : D m) := by
      congr 2

private lemma semidirect_card (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (R m ⋊[MonoidHom.id (MulAut (↥(R m)))] MulAut (↥(R m))) =
      2 ^ (m + (m - 1)) := by
  let : NeZero (2 ^ m) := ⟨rotation_ne_zero m⟩
  let : Fintype (↥(R m)) := Fintype.ofFinite _
  have hR : Nat.card (↥(R m)) = 2 ^ m := rotation_card m (by omega)
  have hA : Nat.card (MulAut (↥(R m))) = 2 ^ (m - 1) := by
    rw [IsCyclic.card_mulAut (↥(R m)), hR]
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  rw [SemidirectProduct.card, hR, hA, ← pow_add]

private noncomputable def encode (m : ℕ) (hm : 2 ≤ m) :
    MulAut (D m) →* (R m ⋊[MonoidHom.id (MulAut (↥(R m)))] MulAut (↥(R m))) := by
  letI : (R m).Characteristic := rotation_characteristic m hm
  let ρ : MulAut (D m) →* MulAut (↥(R m)) := MulAut.characteristic (R m)
  let b : MulAut (D m) → R m := reflection_image m hm
  exact
    { toFun := fun f => ⟨b f, ρ f⟩
      map_one' := by
        apply SemidirectProduct.ext
        · apply reflection_image_unique m (1 : MulAut (D m))
          · simpa [b] using reflection_image_spec m hm (1 : MulAut (D m))
          · simpa [b] using reflection_image_spec m hm (1 : MulAut (D m))
        · simp [ρ]
      map_mul' := by
        intro f g
        apply SemidirectProduct.ext
        · change reflection_image m hm (f * g) =
            reflection_image m hm f *
              (MulAut.characteristic (R m) f) (reflection_image m hm g)
          exact reflection_image_mul m hm f g
        · simp [ρ] }

private lemma encode_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (encode m hm) := by
  let : NeZero (2 ^ m) := ⟨rotation_ne_zero m⟩
  let : (R m).Characteristic := rotation_characteristic m hm
  intro f g hfg
  apply MulEquiv.ext
  intro x
  rcases dihedralGroup_cases x with ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [hi]
    have hρ := congrArg SemidirectProduct.right hfg
    have hx := DFunLike.congr_fun hρ ⟨DihedralGroup.r i, r_mem_zpowers_r_one i⟩
    have hx' := congrArg Subtype.val hx
    change f (DihedralGroup.r i) = g (DihedralGroup.r i)
    simpa [encode, restriction_apply_coe] using hx'
  · rw [hi]
    have hdecomp : DihedralGroup.sr i =
        DihedralGroup.sr 0 * DihedralGroup.r i := by
      rw [DihedralGroup.sr_mul_r, zero_add]
    rw [hdecomp]
    have hρ := congrArg SemidirectProduct.right hfg
    have hb := congrArg SemidirectProduct.left hfg
    have hri := DFunLike.congr_fun hρ ⟨DihedralGroup.r i, r_mem_zpowers_r_one i⟩
    have hri' := congrArg Subtype.val hri
    have hrot : f (DihedralGroup.r i) = g (DihedralGroup.r i) := by
      simpa [encode, restriction_apply_coe] using hri'
    change reflection_image m hm f = reflection_image m hm g at hb
    have hb' : (reflection_image m hm f : D m) =
        (reflection_image m hm g : D m) := congrArg Subtype.val hb
    rw [map_mul, map_mul, reflection_image_spec m hm f,
      reflection_image_spec m hm g, hrot, hb']

/-- For `m ≥ 2`, the automorphism group of `DihedralGroup (2^m)` is a 2-group. -/
public theorem dihedral_mulAut_is_twoGroup {m : ℕ} (hm : 2 ≤ m) :
    IsPGroup 2 (MulAut (DihedralGroup (2 ^ m))) := by
  let : NeZero (2 ^ m) := ⟨rotation_ne_zero m⟩
  let : Fintype (↥(R m)) := Fintype.ofFinite _
  have hSD : IsPGroup 2
      (R m ⋊[MonoidHom.id (MulAut (↥(R m)))] MulAut (↥(R m))) :=
    IsPGroup.of_card (semidirect_card m hm)
  exact hSD.of_injective (encode m hm) (encode_injective m hm)

end CFSG.GorensteinWalter
