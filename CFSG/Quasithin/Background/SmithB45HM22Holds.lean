module

public import CFSG.Quasithin.Background.SmithB45HM22Cls
public import CFSG.Quasithin.Background.SmithB45HM22F4
public import CFSG.Quasithin.Background.SmithB45M22HatSmall
public import CFSG.Quasithin.Background.SmithB42Alt7Fix
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.HM22 Module Matrix

namespace HM22

variable {V : Type} [CommGroup V]

theorem fpf_of_central {L : Subgroup (MulAut V)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤)
    {z : ↥L} (hz : z ∈ Subgroup.center ↥L) (hz1 : z ≠ 1) :
    ∀ v : V, (z : MulAut V) v = v → v = 1 := by
  let F : Subgroup V :=
    { carrier := {v | (z : MulAut V) v = v}
      mul_mem' := fun {a b} (ha : (z : MulAut V) a = a) (hb : (z : MulAut V) b = b) => by
        change (z : MulAut V) (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one (z : MulAut V)
      inv_mem' := fun {a} (ha : (z : MulAut V) a = a) => by
        change (z : MulAut V) a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hF : XMod.IsInv ↥L F := by
    intro g v (hv : (z : MulAut V) v = v)
    change (z : MulAut V) ((g : MulAut V) v) = (g : MulAut V) v
    have hc := Subgroup.mem_center_iff.mp hz g
    have := congrArg (fun x : ↥L => (x : MulAut V) v) hc
    simp only [Subgroup.coe_mul, MulAut.mul_apply] at this
    rw [← this, hv]
  rcases hirr.2 F hF bot_le le_top with h0 | h0
  · intro v hv
    have : v ∈ F := hv
    rw [h0, Subgroup.mem_bot] at this
    exact this
  · exfalso
    apply hz1
    apply Subtype.ext
    refine MulEquiv.ext fun v => ?_
    have : v ∈ F := by rw [h0]; exact Subgroup.mem_top v
    exact this

end HM22

theorem hatM22SmallModules_holds :
    HatM22SmallModules := by
  intro V _ _ hV2 L hL hirr hcard
  obtain ⟨ψ⟩ := nonempty_mulEquiv_hatM22Γ₀ hL
  set z : MulAut V := ((ψ hatM22Z : ↥L) : MulAut V) with hzdef
  have hzc : ψ hatM22Z ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨γ, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hatM22Z_mem_center γ]
  have hz1 : ψ hatM22Z ≠ 1 := by
    intro h
    apply hatM22Z_ne_one
    apply ψ.injective
    rw [h, map_one]
  have hfp := HM22.fpf_of_central hirr hzc hz1
  have h3 : z ^ 3 = 1 := by
    rw [hzdef, ← Subgroup.coe_pow, ← map_pow, hatM22Z_pow_three, map_one]
    rfl
  have hgen : IsF4Gen z := isF4Gen_of_fpf hV2 h3 hfp
  have : Fact (IsF4Gen z) := ⟨hgen⟩
  have hψ : ∀ (γ : ↥hatM22Γ₀) (v : V),
      ((ψ.toMonoidHom γ : ↥L) : MulAut V) (z v) = z (((ψ.toMonoidHom γ : ↥L) : MulAut V) v) := by
    intro γ v
    have hc := Subgroup.mem_center_iff.mp hzc (ψ γ)
    have := congrArg (fun x : ↥L => (x : MulAut V) v) hc
    simp only [Subgroup.coe_mul, MulAut.mul_apply] at this
    exact this
  set ρ := repOfHom ψ.toMonoidHom hψ with hρ
  have hρirr : ρ.IsIrreducible := isIrreducible_repOfHom ψ.toMonoidHom ψ.surjective hψ hirr
  have hz : ρ hatM22Z = ω • LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply F4Of.toV_injective
    rw [repOfHom_apply, LinearMap.smul_apply, LinearMap.id_apply, F4Of.toV_ω_smul]
    rfl
  have hdim : finrank FieldFour (F4Of z) ≤ 14 := by
    have h1 := card_eq_four_pow (z := z)
    rw [h1] at hcard
    have h2 : 4 ^ finrank FieldFour (F4Of z) = 2 ^ (2 * finrank FieldFour (F4Of z)) := by
      rw [pow_mul]
      norm_num
    rw [h2] at hcard
    have h3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hcard
    omega
  obtain ⟨Ψ, hΨ⟩ := hatM22_classify (F4Of z) ρ hz hdim
  let β : V ≃* ↥(⊤ : Subgroup (Multiplicative (Fin 6 → FieldFour))) :=
    { toFun := fun v => ⟨Multiplicative.ofAdd (Ψ.symm (F4Of.of v)), trivial⟩
      invFun := fun x => F4Of.toV (Ψ (Multiplicative.toAdd (x : Multiplicative _)))
      left_inv := fun v => by
        simp only [toAdd_ofAdd, LinearEquiv.apply_symm_apply]
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        simp only [F4Of.of_toV, LinearEquiv.symm_apply_apply, ofAdd_toAdd]
      map_mul' := fun v w => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← ofAdd_add, F4Of.of_mul, map_add] }
  refine ⟨ψ.toMonoidHom, B42Alt7.realizesVia_of_equivariant (FFModel.nat_isActionModel _) rfl
    L ψ.toMonoidHom ψ.surjective β fun γ s => ?_⟩
  change Multiplicative.ofAdd (Ψ.symm (F4Of.of ((ψ γ : MulAut V) s))) =
    Multiplicative.ofAdd (gmat γ *ᵥ Ψ.symm (F4Of.of s))
  congr 1
  have h1 : (F4Of.of ((ψ γ : MulAut V) s) : F4Of z) = ρ γ (F4Of.of s) := rfl
  have h2 := hΨ γ (Ψ.symm (F4Of.of s))
  rw [LinearEquiv.apply_symm_apply] at h2
  rw [h1, ← h2, LinearEquiv.symm_apply_apply]

end CFSG.Quasithin
