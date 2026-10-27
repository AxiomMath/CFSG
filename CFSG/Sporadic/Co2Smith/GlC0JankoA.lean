module

public import CFSG.Sporadic.Co2Smith.GlC0Jk45
public import CFSG.ClassicalGroups.Symplectic.Simple
public import Certificates.Certificate2012
public import CFSG.Sporadic.Co2Smith.GlC0JkInputs
import Certificates.Kernel.Co2Smith.Mark
import Certificates.Data.Kernel.Co2Smith.Rows
import Mathlib.Logic.Equiv.Defs
import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import Certificates.Kernel.Co2Smith.LettersData
import Certificates.Kernel.Co2Smith.JkData
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import Certificates.Certificate21165

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

@[expose] def x45P : QP45.originalSubgroup :=
  ⟨x45, by rw [QP45_closure]; exact subset_closure (Set.mem_insert _ _)⟩

theorem orderOf_x45P : orderOf x45P = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact (Schreier.orderIs_iff _ (by norm_num)).1 x45_facts.1

theorem lieModel_QP45 :
    CFSG.Blueprint.LieModel QP45.originalSubgroup .PSp 2 3 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩, ZMod 3, inferInstance,
    inferInstance, by simp, ⟨psp43EquivP.symm⟩⟩

theorem card_QP45 : Nat.card QP45.originalSubgroup = 25920 := by
  rw [card_group QP45 QP45_ok, QP45_valid.2]

theorem card_centralizer_x45P :
    Nat.card (centralizer ({x45P} : Set QP45.originalSubgroup)) = 576 := by
  rw [← card_centralizer_x45]
  exact Nat.card_congr
    { toFun := fun g => ⟨((g : QP45.originalSubgroup) : Equiv.Perm (Fin 45)),
        mem_inf.2 ⟨(g : QP45.originalSubgroup).2, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 g.2))⟩⟩
      invFun := fun g => ⟨⟨g, (mem_inf.1 g.2).1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem factorization_two_576 : (576 : ℕ).factorization 2 = 6 := by
  rw [show (576 : ℕ) = 2 ^ 6 * 9 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem factorization_two_25920 : (25920 : ℕ).factorization 2 = 6 := by
  rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem exists_sylow_x45P :
    ∃ S : Sylow 2 QP45.originalSubgroup, x45P ∈ (S : Subgroup QP45.originalSubgroup) ∧
      ∀ s ∈ (S : Subgroup QP45.originalSubgroup), x45P * s = s * x45P := by
  have hxC : x45P ∈ centralizer ({x45P} : Set QP45.originalSubgroup) :=
    mem_centralizer_singleton_iff.2 rfl
  have h2 : IsPGroup 2
      (zpowers (⟨x45P, hxC⟩ : centralizer ({x45P} : Set QP45.originalSubgroup))) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_x45P, pow_one]
  obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
  have hQc : Nat.card Q = 2 ^ 6 := by
    rw [Q.card_eq_multiplicity, card_centralizer_x45P, factorization_two_576]
  refine ⟨Sylow.ofCard ((Q : Subgroup _).map
    (centralizer ({x45P} : Set QP45.originalSubgroup)).subtype) ?_, ?_, ?_⟩
  · rw [card_map_of_injective (subtype_injective _), hQc, card_QP45, factorization_two_25920]
  · rw [Sylow.coe_ofCard]
    exact ⟨⟨x45P, hxC⟩, hQ (mem_zpowers _), rfl⟩
  · intro s hs
    rw [Sylow.coe_ofCard] at hs
    obtain ⟨c, -, rfl⟩ := hs
    exact (mem_centralizer_singleton_iff.1 c.2).symm

theorem card_mulAut_of_equiv {X : Type*} [Group X]
    (e : X ≃* QP45.originalSubgroup) : Nat.card (MulAut X) = 51840 := by
  obtain ⟨M, -, hA⟩ := exists_model e
  rw [M.card_mulAut, hA, card_QA45]

@[expose] def centralizerEquivOfEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (j : X) :
    centralizer ({j} : Set X) ≃* centralizer ({e j} : Set Y) where
  toFun g := ⟨e (g : X), mem_centralizer_singleton_iff.2 (by
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 g.2])⟩
  invFun g := ⟨e.symm (g : Y), mem_centralizer_singleton_iff.2 (by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_centralizer_singleton_iff.1 g.2)⟩
  left_inv g := Subtype.ext (e.symm_apply_apply (g : X))
  right_inv g := Subtype.ext (e.apply_symm_apply (g : Y))
  map_mul' g h := Subtype.ext (map_mul e (g : X) (h : X))

end CFSG.Sporadic.Co2Smith
