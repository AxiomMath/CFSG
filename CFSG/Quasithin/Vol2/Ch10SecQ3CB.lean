module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.Dihedral.GorensteinWalter.PGL2CharTwo
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {F : Type} [Field F]

theorem center_sl2_eq_bot [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have h : (r + 1) * (r + 1) = 0 := by linear_combination hr + (r + 1) * h2
    have h' : r + 1 = 0 := mul_self_eq_zero.mp h
    linear_combination h' - h2
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1, map_one]
  rfl

theorem mk_sl2_injective [CharP F 2] :
    Function.Injective (QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_sl2_eq_bot]

theorem toPGL_surjective_of_charTwo [Finite F] [CharP F 2] :
    Function.Surjective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) :=
  CFSG.GorensteinWalter.toPGL_surjective_of_charTwo' F

end C11AmS

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo C11AmS

theorem factAutSL2Char2_holds :
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), Nat.card F = 2 ^ n →
      ∀ α : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        ∃ (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin 2) F),
          ∀ x, α x = g * Matrix.SpecialLinearGroup.map σ.toRingHom x * g⁻¹ := by
  intro F _ _ n hF α
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) with hπ
  have hπinj : Function.Injective π := mk_sl2_injective
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* PSL2 F :=
    MulEquiv.ofBijective π ⟨hπinj, QuotientGroup.mk'_surjective _⟩
  have he : ∀ x, e x = π x := fun _ => rfl
  let α' : MulAut (PSL2 F) := (e.symm.trans α).trans e
  have hα' : ∀ x, α' (e x) = e (α x) := fun x => by
    change e (α (e.symm (e x))) = e (α x)
    rw [e.symm_apply_apply]
  obtain ⟨p, hp⟩ := semilinearAction_surjective F α'
  obtain ⟨y, hy⟩ := toPGL_surjective_of_charTwo (F := F) p.left
  have hdec : semilinearAction F p =
      pglAction F p.left * psl2FieldAut F p.right := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right p]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  refine ⟨p.right, e.symm y, fun x => ?_⟩
  apply e.injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [← hα', ← hp, hdec, MulAut.mul_apply, toPGL_pglAction, psl2FieldAut_apply, he,
    psl2RingEquiv_mk, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
    MulEquiv.apply_symm_apply, hy, he]

end CFSG.Quasithin.Vol2.Ch10.SecB
