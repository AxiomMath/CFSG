module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import Mathlib.Algebra.Order.Ring.Star

public section

open scoped MatrixGroups

namespace CFSG.Quasithin

open CFSG.GorensteinWalter

theorem center_specialLinearGroup_eq_bot_of_charP_two {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h : (r - 1) ^ 2 = 0 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hr + (1 - r) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h)
  subst hr1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

theorem exists_orderOf_nine_specialLinearGroup {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 8) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, orderOf g = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (k := 3)
      Nat.prime_two (by norm_num) hF
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 504 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
    norm_num
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := Matrix.SpecialLinearGroup (Fin 2) F) 3 (n := 2) (by rw [hSL]; norm_num)
  have hcen := center_specialLinearGroup_eq_bot_of_charP_two (F := F)
  let π : Matrix.SpecialLinearGroup (Fin 2) F →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  have hπ : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq_one_iff x).1 hx
    rw [hcen, Subgroup.mem_bot] at this
    exact this
  have hTp : IsPGroup 3 T := IsPGroup.of_card (n := 2) hT
  obtain ⟨R, hR⟩ := (hTp.map π).exists_le_sylow
  have hcyc : IsCyclic R :=
    psl2_sylow_isCyclic_of_coprime_field_card F (p := 2) (f := 3) (by rw [hF]; norm_num)
      (by rw [hF]; norm_num) 3 (by norm_num) (by rw [hF]; norm_num) R
  let φ : T →* (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
    MonoidHom.codRestrict (π.comp T.subtype) (R : Subgroup _) fun x => hR ⟨x, x.2, rfl⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    apply hπ
    exact congrArg Subtype.val hxy
  have hTcyc : IsCyclic T := isCyclic_of_injective φ hφ
  obtain ⟨t, ht⟩ := hTcyc.exists_generator
  refine ⟨t, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ht, hT]
  norm_num

end CFSG.Quasithin
