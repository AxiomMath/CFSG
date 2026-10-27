module

public import CFSG.Quasithin.Background.SmithB42HatA6Coord
public import CFSG.Quasithin.Background.A1cModuleDefs

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.HatA6

variable {V : Type} [CommGroup V]

structure IsF4Gen (z : MulAut V) : Prop where
  sq : ∀ v : V, v * v = 1
  zz : ∀ v : V, z (z v) = v * z v

structure F4Of (z : MulAut V) where
  toV : V

namespace F4Of

variable {z : MulAut V}

@[expose] def equivAdd : F4Of z ≃ Additive V where
  toFun x := Additive.ofMul x.toV
  invFun v := ⟨Additive.toMul v⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (F4Of z) := equivAdd.addCommGroup

@[expose] def of (v : V) : F4Of z := ⟨v⟩

theorem toV_of (v : V) : toV (of v : F4Of z) = v := rfl

theorem of_toV (x : F4Of z) : of (toV x) = x := rfl

theorem toV_zero : toV (0 : F4Of z) = 1 := rfl

theorem of_mul (v w : V) : (of (v * w) : F4Of z) = of v + of w := rfl

theorem of_one : (of 1 : F4Of z) = 0 := rfl

theorem toV_injective : Function.Injective (toV : F4Of z → V) := fun a b h => by
  cases a
  cases b
  cases h
  rfl

instance [Finite V] : Finite (F4Of z) := Finite.of_equiv _ equivAdd.symm

instance : SMul FieldFour (F4Of z) := ⟨fun c x => of (fsmul z c (toV x))⟩

instance instModule [h : Fact (IsF4Gen z)] : Module FieldFour (F4Of z) where
  one_smul x := toV_injective (fsmul_one z (toV x))
  mul_smul c d x := toV_injective (fsmul_mul h.out.sq h.out.zz c d (toV x))
  smul_zero c := toV_injective (fsmul_one_right z c)
  smul_add c x y := toV_injective (fsmul_mul_right z c (toV x) (toV y))
  add_smul c d x := toV_injective (fsmul_add h.out.sq c d (toV x))
  zero_smul x := toV_injective (fsmul_zero z (toV x))

theorem toV_ω_smul (x : F4Of z) : toV (FieldFour.ω • x) = z (toV x) := fsmul_ω z (toV x)

instance [Finite V] [Fact (IsF4Gen z)] : Module.Finite FieldFour (F4Of z) :=
  Module.Finite.of_finite

end F4Of

open F4Of

variable {z : MulAut V}

@[expose] def f4Lin [Fact (IsF4Gen z)] (x : MulAut V) (hx : ∀ v, x (z v) = z (x v)) :
    F4Of z →ₗ[FieldFour] F4Of z where
  toFun y := of (x (toV y))
  map_add' a b := by
    change of (x (toV a * toV b)) = of (x (toV a)) + of (x (toV b))
    rw [map_mul, of_mul]
  map_smul' c a := by
    change of (x (fsmul z c (toV a))) = of (fsmul z c (x (toV a)))
    rw [map_fsmul hx]

theorem f4Lin_apply [Fact (IsF4Gen z)] (x : MulAut V) (hx : ∀ v, x (z v) = z (x v))
    (y : F4Of z) : toV (f4Lin x hx y) = x (toV y) := rfl

@[expose] def repOfHom [Fact (IsF4Gen z)] {Γ : Type*} [Group Γ] {L : Subgroup (MulAut V)}
    (ψ : Γ →* ↥L) (hψ : ∀ γ v, (ψ γ : MulAut V) (z v) = z ((ψ γ : MulAut V) v)) :
    Representation FieldFour Γ (F4Of z) where
  toFun γ := f4Lin (ψ γ : MulAut V) (hψ γ)
  map_one' := LinearMap.ext fun y => by
    apply toV_injective
    rw [f4Lin_apply, map_one, Subgroup.coe_one]
    rfl
  map_mul' γ δ := LinearMap.ext fun y => by
    apply toV_injective
    rw [f4Lin_apply, map_mul, Subgroup.coe_mul]
    rfl

theorem repOfHom_apply [Fact (IsF4Gen z)] {Γ : Type*} [Group Γ] {L : Subgroup (MulAut V)}
    (ψ : Γ →* ↥L) (hψ : ∀ γ v, (ψ γ : MulAut V) (z v) = z ((ψ γ : MulAut V) v)) (γ : Γ)
    (y : F4Of z) : toV (repOfHom ψ hψ γ y) = (ψ γ : MulAut V) (toV y) := rfl

theorem isIrreducible_repOfHom [Fact (IsF4Gen z)] {Γ : Type*} [Group Γ]
    {L : Subgroup (MulAut V)} (ψ : Γ →* ↥L) (hsurj : Function.Surjective ψ)
    (hψ : ∀ γ v, (ψ γ : MulAut V) (z v) = z ((ψ γ : MulAut V) v))
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) : (repOfHom ψ hψ).IsIrreducible := by
  have hnt : Nontrivial (F4Of z) := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hirr.1
    refine ⟨⟨of v, 0, fun h => hv ?_⟩⟩
    have h1 : v = 1 := by
      have := congrArg toV h
      rwa [toV_of, toV_zero] at this
    rw [h1]
    exact Subgroup.one_mem _
  have hbt : (⊥ : Subrepresentation (repOfHom ψ hψ)) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : F4Of z)
    have hvt : v ∈ (⊤ : Subrepresentation (repOfHom ψ hψ)).toSubmodule := Submodule.mem_top
    rw [← h] at hvt
    exact hv ((Submodule.mem_bot _).mp hvt)
  have : Nontrivial (Subrepresentation (repOfHom ψ hψ)) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun U => ?_⟩
  let U' : Subgroup V :=
    { carrier := {v | (of v : F4Of z) ∈ U.toSubmodule}
      mul_mem' := fun {a b} ha hb => by
        change (of (a * b) : F4Of z) ∈ U.toSubmodule
        rw [of_mul]
        exact U.toSubmodule.add_mem ha hb
      one_mem' := by
        change (of 1 : F4Of z) ∈ U.toSubmodule
        rw [of_one]
        exact U.toSubmodule.zero_mem
      inv_mem' := fun {w} hw => by
        have hinv : w⁻¹ = w := by
          rw [inv_eq_iff_mul_eq_one]
          exact (Fact.out : IsF4Gen z).sq w
        change (of w⁻¹ : F4Of z) ∈ U.toSubmodule
        rw [hinv]
        exact hw }
  have hU' : XMod.IsInv ↥L U' := by
    intro g u hu
    obtain ⟨γ, rfl⟩ := hsurj g
    have h1 := U.apply_mem_toSubmodule γ hu
    exact h1
  rcases hirr.2 U' hU' bot_le le_top with h0 | h0
  · left
    ext x
    constructor
    · intro hx
      have hx' : toV x ∈ U' := hx
      rw [h0, Subgroup.mem_bot] at hx'
      have : x = 0 := toV_injective (hx'.trans toV_zero.symm)
      rw [this]
      exact Submodule.zero_mem _
    · intro hx
      have hx0 : x = 0 := (Submodule.mem_bot _).mp hx
      rw [hx0]
      exact U.toSubmodule.zero_mem
  · right
    ext x
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    have hx' : toV x ∈ U' := by
      rw [h0]
      exact Subgroup.mem_top _
    exact hx'

theorem card_eq_four_pow [Finite V] [Fact (IsF4Gen z)] :
    Nat.card V = 4 ^ Module.finrank FieldFour (F4Of z) := by
  have h := Module.natCard_eq_pow_finrank (K := FieldFour) (V := F4Of z)
  rw [FieldFour.natCard_eq] at h
  rw [← h]
  exact Nat.card_congr (equivAdd.trans (Equiv.refl V)).symm

theorem isF4Gen_of_fpf (hsq : ∀ v : V, v ^ 2 = 1) (h3 : z ^ 3 = 1)
    (hfp : ∀ v : V, z v = v → v = 1) : IsF4Gen z :=
  ⟨fun v => by rw [← pow_two]; exact hsq v,
    fun v => H13.zz_eq_of_fpf hsq h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw)
      trivial⟩

end CFSG.Quasithin.HM22
