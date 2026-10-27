module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Equiv

private theorem perm_inv_three :
    ∀ s : Perm (Fin 5), s * s = 1 → s ≠ 1 →
      ∃ a : alternatingGroup (Fin 5), a ^ 3 = 1 ∧ a ≠ 1 ∧
        s * (a : Perm (Fin 5)) * s⁻¹ = (a : Perm (Fin 5))⁻¹ := by
  decide +kernel

theorem kA5InvertsThree_holds : KA5InvertsThree := by
  intro G _ L t hAlt ht2 hL hnc
  obtain ⟨φ⟩ := hAlt
  have ht : t * t = 1 := by rwa [pow_two] at ht2
  have htN : t ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hL x hx, fun hx => ?_⟩
    have h := hL (t * x * t⁻¹) hx
    have h' : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [inv_eq_of_mul_eq_one_right ht]
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [ht, one_mul, mul_one]
    rwa [h'] at h
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨t, htN⟩ with hσ
  have hσapp : ∀ x : ↥L, ((σ x : ↥L) : G) = t * (x : G) * t⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨t, htN⟩ x
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have htN2 : (⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨t, htN⟩ = 1 :=
      Subtype.ext ht
    rw [htN2, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    obtain ⟨x, hxL, hxne⟩ := hnc
    apply hxne
    have e := hσapp ⟨x, hxL⟩
    rw [h, MulAut.one_apply] at e
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = x * t := by rw [← e]
  set E := CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv with hE
  set α : MulAut (alternatingGroup (Fin 5)) := MulAut.congr φ σ with hα
  set s : Perm (Fin 5) := E.symm α with hs
  have hαs : α = E s := by rw [hs, MulEquiv.apply_symm_apply]
  have hαapp : ∀ a : alternatingGroup (Fin 5),
      ((α a : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        s * (a : Perm (Fin 5)) * s⁻¹ := fun a => by
    rw [hαs, hE, CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv_apply]
    rfl
  have hσα : ∀ x : ↥L, σ x = φ.symm (α (φ x)) := fun x => by
    rw [hα, MulAut.congr_apply]
    simp
  have hsq : s * s = 1 := by
    have h1 : α * α = 1 := by rw [hα, ← map_mul, hσ2, map_one]
    have h2 : E (s * s) = 1 := by rw [map_mul, ← hαs, h1]
    exact E.injective (h2.trans (map_one E).symm)
  have hs1 : s ≠ 1 := by
    intro h
    apply hσ1
    have hα1 : α = 1 := by rw [hαs, h, map_one]
    apply MulEquiv.ext
    intro x
    rw [hσα x, hα1, MulAut.one_apply, MulEquiv.symm_apply_apply, MulAut.one_apply]
  obtain ⟨a, ha3, ha1, hsa⟩ := perm_inv_three s hsq hs1
  have hαa : α a = a⁻¹ := by
    apply Subtype.ext
    rw [hαapp a, hsa]
    rfl
  let y : ↥L := φ.symm a
  have hyapp : φ y = a := MulEquiv.apply_symm_apply φ a
  have hy3 : y ^ 3 = 1 := by
    change (φ.symm a) ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    apply ha1
    have h' := congrArg φ h
    simpa [y] using h'
  have hσy : σ y = y⁻¹ := by
    rw [hσα y, show φ y = a from hyapp, hαa, map_inv]
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hy3 hy1
  · have h := congrArg (fun w : ↥L => (w : G)) hσy
    rw [hσapp y, Subgroup.coe_inv] at h
    exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
