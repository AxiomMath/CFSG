module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Perm
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne

theorem isSolvable_centralizer_d4X_one :
    IsSolvable ↥((centralizer {d4X 1} : Subgroup (Equiv.Perm (Fin 2457))) ⊓ d4P) := by
  classical
  obtain ⟨hcl, hcard⟩ := d4_caseB
  rw [hcl] at hcard
  have h648 : Nat.card ↥((centralizer {d4X 1} : Subgroup (Equiv.Perm (Fin 2457))) ⊓ d4P) =
      2 ^ 3 * 3 ^ 4 := by rw [hcard]; norm_num
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h648)

theorem isSolvable_centralizer_conj {G : Type*} [Group G] {P : Subgroup G} {y k : G}
    (hk : ∀ x ∈ P, k⁻¹ * x * k ∈ P) (h : IsSolvable ↥(centralizer {y} ⊓ P)) :
    IsSolvable ↥(centralizer {k * y * k⁻¹} ⊓ P) := by
  let f : ↥(centralizer {k * y * k⁻¹} ⊓ P) →* ↥(centralizer {y} ⊓ P) :=
    ((MulAut.conj k⁻¹).toMonoidHom.comp (centralizer {k * y * k⁻¹} ⊓ P).subtype).codRestrict _
      fun x => by
        obtain ⟨x, hx⟩ := x
        obtain ⟨hxc, hxP⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [mem_centralizer_singleton_iff] at hxc ⊢
          simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
            Subgroup.coe_subtype, MulAut.conj_apply, inv_inv]
          have : x * (k * y * k⁻¹) = (k * y * k⁻¹) * x := hxc
          calc k⁻¹ * x * k * y = k⁻¹ * (x * (k * y * k⁻¹)) * k := by group
            _ = k⁻¹ * ((k * y * k⁻¹) * x) * k := by rw [this]
            _ = y * (k⁻¹ * x * k) := by group
        · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
            Subgroup.coe_subtype, MulAut.conj_apply, inv_inv]
          exact hk x hxP
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, MonoidHom.codRestrict_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, Subgroup.coe_subtype] at this
    exact Subtype.ext ((MulAut.conj k⁻¹).injective this)
  have : Group.IsSolvable ↥(centralizer {y} ⊓ P) := h
  exact solvable_of_solvable_injective hf

end CFSG.RankThree.PartTwo.Sec4.Item434D42
