module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Module

section Vec3

variable {G : Type*} [Group G]

structure IsElem3 (D : Subgroup G) : Prop where
  comm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x
  pow3 : ∀ x ∈ D, x ^ 3 = 1

@[expose] def commGroupOfElem3 (D : Subgroup G) (h : IsElem3 D) : CommGroup D :=
  { (inferInstance : Group D) with
    mul_comm := fun x y => Subtype.ext (h.comm x x.2 y y.2) }

@[expose] def Vec (D : Subgroup G) : Type _ := Additive D

variable (D : Subgroup G) [hD : Fact (IsElem3 D)]

instance : AddCommGroup (Vec D) :=
  letI := commGroupOfElem3 D hD.out
  inferInstanceAs (AddCommGroup (Additive D))

@[expose] def Vec.ofD {D : Subgroup G} (x : D) : Vec D := Additive.ofMul x

@[expose] def Vec.toD {D : Subgroup G} (v : Vec D) : D := Additive.toMul v

@[simp] theorem Vec.toD_ofD {D : Subgroup G} (x : D) : Vec.toD (Vec.ofD x) = x := rfl
@[simp] theorem Vec.ofD_toD {D : Subgroup G} (v : Vec D) : Vec.ofD (Vec.toD v) = v := rfl

theorem Vec.toD_injective {D : Subgroup G} : Function.Injective (Vec.toD (D := D)) :=
  fun _ _ h => h

theorem Vec.toD_add {D : Subgroup G} [Fact (IsElem3 D)] (v w : Vec D) :
    Vec.toD (v + w) = Vec.toD v * Vec.toD w := rfl

theorem Vec.toD_zero {D : Subgroup G} [Fact (IsElem3 D)] : Vec.toD (0 : Vec D) = 1 := rfl

theorem Vec.toD_neg {D : Subgroup G} [Fact (IsElem3 D)] (v : Vec D) :
    Vec.toD (-v) = (Vec.toD v)⁻¹ := rfl

theorem Vec.toD_nsmul {D : Subgroup G} [Fact (IsElem3 D)] (n : ℕ) (v : Vec D) :
    Vec.toD (n • v) = (Vec.toD v) ^ n := rfl

instance : Module F3 (Vec D) :=
  AddCommGroup.zmodModule (n := 3) fun x => by
    apply Vec.toD_injective
    rw [Vec.toD_nsmul, Vec.toD_zero]
    exact Subtype.ext (by simpa using hD.out.pow3 _ (Vec.toD x).2)

@[expose] def conjAdd (n : Subgroup.normalizer (D : Set G)) : Vec D →+ Vec D where
  toFun v := Vec.ofD (D.normalizerMonoidHom n (Vec.toD v))
  map_zero' := by
    apply Vec.toD_injective
    simp only [Vec.toD_ofD, Vec.toD_zero]
    exact map_one _
  map_add' v w := by
    apply Vec.toD_injective
    simp only [Vec.toD_ofD, Vec.toD_add]
    exact map_mul _ _ _

@[simp] theorem Vec.toD_conjAdd (n : Subgroup.normalizer (D : Set G)) (v : Vec D) :
    Vec.toD (conjAdd D n v) = D.normalizerMonoidHom n (Vec.toD v) := rfl

theorem conjAdd_mul (n m : Subgroup.normalizer (D : Set G)) (v : Vec D) :
    conjAdd D (n * m) v = conjAdd D n (conjAdd D m v) := by
  apply Vec.toD_injective
  simp only [Vec.toD_conjAdd, map_mul]
  rfl

theorem conjAdd_one (v : Vec D) :
    conjAdd D (1 : Subgroup.normalizer (D : Set G)) v = v := by
  apply Vec.toD_injective
  simp only [Vec.toD_conjAdd, map_one]
  rfl

@[expose] def conjLin (n : Subgroup.normalizer (D : Set G)) : Vec D ≃ₗ[F3] Vec D :=
  LinearEquiv.ofLinear ((conjAdd D n).toZModLinearMap 3) ((conjAdd D n⁻¹).toZModLinearMap 3)
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, AddMonoidHom.coe_toZModLinearMap, LinearMap.id_apply]
      rw [← conjAdd_mul, mul_inv_cancel, conjAdd_one])
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, AddMonoidHom.coe_toZModLinearMap, LinearMap.id_apply]
      rw [← conjAdd_mul, inv_mul_cancel, conjAdd_one])

@[expose] def conjLinHom : Subgroup.normalizer (D : Set G) →* (Vec D ≃ₗ[F3] Vec D) where
  toFun := conjLin D
  map_one' := by ext v; exact conjAdd_one D v
  map_mul' n m := by ext v; exact conjAdd_mul D n m v

theorem toD_conjLinHom (n : Subgroup.normalizer (D : Set G)) (v : Vec D) :
    ((Vec.toD (conjLinHom D n v) : D) : G) = (n : G) * (Vec.toD v : D) * (n : G)⁻¹ := rfl

theorem conjLinHom_eq_one_iff (n : Subgroup.normalizer (D : Set G)) :
    conjLinHom D n = 1 ↔ (n : G) ∈ Subgroup.centralizer (D : Set G) := by
  obtain ⟨g, hg⟩ := n
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg (fun f : Vec D ≃ₗ[F3] Vec D => ((Vec.toD (f (Vec.ofD ⟨x, hx⟩)) : D) : G)) h
    simp only [toD_conjLinHom] at this
    change g * x * g⁻¹ = x at this
    calc x * g = (g * x * g⁻¹) * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext v
    apply Vec.toD_injective
    apply Subtype.ext
    rw [toD_conjLinHom]
    have := Subgroup.mem_centralizer_iff.mp h _ (Vec.toD v).2
    change g * (Vec.toD v : D) * g⁻¹ = (Vec.toD v : D)
    calc g * (Vec.toD v : D) * g⁻¹ = ((Vec.toD v : D) * g) * g⁻¹ := by rw [this]
      _ = _ := by group

end Vec3

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
