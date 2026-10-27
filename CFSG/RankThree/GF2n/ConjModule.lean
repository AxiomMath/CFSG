module

public import CFSG.RankThree.GF2n.DihedralCompl
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Subgroup.Order

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n

variable {G : Type*} [Group G] (M : Subgroup G)

@[expose] def conjHom (x : G) (hx : x ∈ Subgroup.normalizer (M : Set G)) : ↥M →* ↥M where
  toFun m := ⟨x * m * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx m).mp m.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

variable {M}

@[simp] theorem coe_conjHom_apply {x : G} (hx : x ∈ Subgroup.normalizer (M : Set G)) (m : ↥M) :
    ((conjHom M x hx m : ↥M) : G) = x * m * x⁻¹ := rfl

section Module

variable [IsMulCommutative ↥M] [Module (ZMod 2) (Additive ↥M)]

variable (M) in
@[expose] def conjEndHom :
    ↥(Subgroup.normalizer (M : Set G)) →* Module.End (ZMod 2) (Additive ↥M) where
  toFun x := (MonoidHom.toAdditive (conjHom M x x.2)).toZModLinearMap 2
  map_one' := LinearMap.ext fun v => Additive.toMul.injective (Subtype.ext (by simp))
  map_mul' x y := LinearMap.ext fun v => Additive.toMul.injective (Subtype.ext (by
    simp [mul_assoc]))

theorem conjEndHom_apply (x : ↥(Subgroup.normalizer (M : Set G))) (v : Additive ↥M) :
    conjEndHom M x v = Additive.ofMul (conjHom M x x.2 v.toMul) := rfl

variable (M) in
@[expose] def toSubmod : Subgroup ↥M ≃o Submodule (ZMod 2) (Additive ↥M) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

theorem toSubmod_le_comap_iff {U : Subgroup ↥M} (x : ↥(Subgroup.normalizer (M : Set G))) :
    toSubmod M U ≤ (toSubmod M U).comap (conjEndHom M x) ↔ ∀ m ∈ U, conjHom M x x.2 m ∈ U :=
  ⟨fun h m hm => h (show Additive.ofMul m ∈ toSubmod M U from hm), fun h v hv => h v.toMul hv⟩

end Module

theorem exists_isCompl_of_dihedral_conj [Finite G] [IsMulCommutative ↥M]
    (hM2 : ∀ m ∈ M, m * m = 1) {a b : G} (haN : a ∈ Subgroup.normalizer (M : Set G))
    (hbN : b ∈ Subgroup.normalizer (M : Set G)) (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) (hfix : ∀ m ∈ M, a * m = m * a → b * m = m * b → m = 1)
    {U : Subgroup ↥M} (hUa : ∀ m ∈ U, conjHom M a haN m ∈ U)
    (hUb : ∀ m ∈ U, conjHom M b hbN m ∈ U) :
    ∃ W : Subgroup ↥M, (∀ m ∈ W, conjHom M a haN m ∈ W) ∧ (∀ m ∈ W, conjHom M b hbN m ∈ W) ∧
      IsCompl U W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Module (ZMod 2) (Additive ↥M) := AddCommGroup.zmodModule fun v => by
    rw [two_nsmul]
    exact Additive.toMul.injective (Subtype.ext (hM2 _ v.toMul.2))
  have : FiniteDimensional (ZMod 2) (Additive ↥M) := Module.Finite.of_finite
  set a' : ↥(Subgroup.normalizer (M : Set G)) := ⟨a, haN⟩
  set b' : ↥(Subgroup.normalizer (M : Set G)) := ⟨b, hbN⟩
  have hsq : ∀ x : ↥(Subgroup.normalizer (M : Set G)), (x : G) * x = 1 →
      conjEndHom M x * conjEndHom M x = 1 := fun x hx => by
    rw [← map_mul, show x * x = 1 from Subtype.ext hx, map_one]
  have hab : (conjEndHom M a' * conjEndHom M b') ^ orderOf (a * b) = 1 := by
    rw [← map_mul, ← map_pow, show (a' * b') ^ orderOf (a * b) = 1 from
      Subtype.ext (by simp [a', b', pow_orderOf_eq_one]), map_one]
  have hfix' : ∀ v, conjEndHom M a' v = v → conjEndHom M b' v = v → v = 0 := by
    intro v hva hvb
    have hcomm : ∀ x : ↥(Subgroup.normalizer (M : Set G)), conjEndHom M x v = v →
        (x : G) * (v.toMul : G) = (v.toMul : G) * x := fun x hx => by
      have h := congrArg (fun w : Additive ↥M => ((w.toMul : ↥M) : G)) hx
      simp only [conjEndHom_apply, toMul_ofMul, coe_conjHom_apply] at h
      calc (x : G) * (v.toMul : G) = (x : G) * v.toMul * (x : G)⁻¹ * x := by group
        _ = (v.toMul : G) * x := by rw [h]
    have h1 := hfix _ v.toMul.2 (hcomm a' hva) (hcomm b' hvb)
    exact Additive.toMul.injective (Subtype.ext h1)
  obtain ⟨W, hWa, hWb, hW⟩ := exists_isCompl_of_dihedral (hsq a' ha) (hsq b' hb) hodd hab hfix'
    ((toSubmod_le_comap_iff a').mpr hUa) ((toSubmod_le_comap_iff b').mpr hUb)
  refine ⟨(toSubmod M).symm W, ?_, ?_, ?_⟩
  · rw [← toSubmod_le_comap_iff a', OrderIso.apply_symm_apply]
    exact hWa
  · rw [← toSubmod_le_comap_iff b', OrderIso.apply_symm_apply]
    exact hWb
  · rw [(toSubmod M).isCompl_iff, OrderIso.apply_symm_apply]
    exact hW

theorem exists_supIndep_irred_of_dihedral [Finite G] [IsMulCommutative ↥M]
    (hM2 : ∀ m ∈ M, m * m = 1) {a b : G} (haN : a ∈ Subgroup.normalizer (M : Set G))
    (hbN : b ∈ Subgroup.normalizer (M : Set G)) (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) (hfix : ∀ m ∈ M, a * m = m * a → b * m = m * b → m = 1) :
    ∃ s : Finset (Subgroup ↥M), s.SupIndep id ∧ s.sup id = ⊤ ∧
      ∀ W ∈ s, ((∀ m ∈ W, conjHom M a haN m ∈ W) ∧ (∀ m ∈ W, conjHom M b hbN m ∈ W)) ∧
        W ≠ ⊥ ∧ ∀ U ≤ W, ((∀ m ∈ U, conjHom M a haN m ∈ U) ∧
          (∀ m ∈ U, conjHom M b hbN m ∈ U)) → U = ⊥ ∨ U = W :=
  exists_supIndep_irred
    (fun U : Subgroup ↥M => (∀ m ∈ U, conjHom M a haN m ∈ U) ∧ (∀ m ∈ U, conjHom M b hbN m ∈ U))
    (fun _ _ hx hy => ⟨fun m hm => Subgroup.mem_inf.mpr ⟨hx.1 m (Subgroup.mem_inf.mp hm).1,
        hy.1 m (Subgroup.mem_inf.mp hm).2⟩,
      fun m hm => Subgroup.mem_inf.mpr ⟨hx.2 m (Subgroup.mem_inf.mp hm).1,
        hy.2 m (Subgroup.mem_inf.mp hm).2⟩⟩)
    (fun _ hx => by
      obtain ⟨W, hWa, hWb, hW⟩ :=
        exists_isCompl_of_dihedral_conj hM2 haN hbN ha hb hodd hfix hx.1 hx.2
      exact ⟨W, ⟨hWa, hWb⟩, hW⟩)
    ⟨fun _ _ => Subgroup.mem_top _, fun _ _ => Subgroup.mem_top _⟩

end CFSG.RankThree.GF2n
