module

import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM22
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import Certificates.Data.Item434SporGenMathieu

public section

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG

@[expose] def alt7A : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide)⟩

@[expose] def alt7B : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide)⟩

theorem exists_e9_alt7 :
    ∃ E : Subgroup (alternatingGroup (Fin 7)), Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  have hx : alt7A ^ 3 = 1 := Subtype.ext (by
    simp only [Subgroup.coe_pow, Subgroup.coe_one, alt7A]
    decide)
  have hy : alt7B ^ 3 = 1 := Subtype.ext (by
    simp only [Subgroup.coe_pow, Subgroup.coe_one, alt7B]
    decide)
  have hxy : alt7A * alt7B = alt7B * alt7A := Subtype.ext (by
    simp only [Subgroup.coe_mul, alt7A, alt7B]
    decide)
  have hx1 : alt7A ≠ 1 := fun h => by
    have h1 := congrArg Subtype.val h
    simp only [Subgroup.coe_one, alt7A] at h1
    exact absurd h1 (by decide)
  have hyx : alt7B ∉ Subgroup.zpowers alt7A := by
    intro hmem
    rcases Sec4.Item434SporGen.eq_of_mem_zpowers_of_pow_three hx hmem with h | h | h
    · have h1 := congrArg Subtype.val h
      simp only [Subgroup.coe_one, alt7B] at h1
      exact absurd h1 (by decide)
    · have h1 := congrArg Subtype.val h
      simp only [alt7A, alt7B] at h1
      exact absurd h1 (by decide)
    · have h1 := congrArg Subtype.val h
      simp only [Subgroup.coe_pow, alt7A, alt7B] at h1
      exact absurd h1 (by decide)
  refine ⟨Subgroup.zpowers alt7A ⊔ Subgroup.zpowers alt7B,
    exponent_dvd_three_of_isElemAbelian (isElemAbelian_zpowers_sup hx hy hxy), ?_⟩
  have h9 := CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx hy hxy hx1 hyx
  rwa [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure] at h9

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
theorem exists_e9_m22 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.M22, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  have h := Sec4.Item434SporGen.m22_e9
  simp only [Sec4.Item434SporGen.e9Check, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h13⟩, h23⟩, hc⟩, -⟩, -⟩, -⟩, -⟩ := h
  set g₁ := Sec4.Item434SporGen.m22e1 with hg₁
  set g₂ := Sec4.Item434SporGen.m22e2 with hg₂
  have h₁ : Rep 22 Sec4.Item434SporGen.m22E1 (g₁ : Equiv.Perm (Fin 22)) :=
    Sec4.Item434SporGen.rep_m22E1
  have h₂ : Rep 22 Sec4.Item434SporGen.m22E2 (g₂ : Equiv.Perm (Fin 22)) :=
    Sec4.Item434SporGen.rep_m22E2
  have hx : g₁ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (Sec4.Item434SporGen.rep_powN h₁ 3) rep_idA h13)
  have hy : g₂ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (Sec4.Item434SporGen.rep_powN h₂ 3) rep_idA h23)
  have hxy : g₁ * g₂ = g₂ * g₁ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Sec4.Item434SporGen.mul_comm_of_commN h₁ h₂ hc)
  refine ⟨Subgroup.zpowers g₁ ⊔ Subgroup.zpowers g₂,
    exponent_dvd_three_of_isElemAbelian (isElemAbelian_zpowers_sup hx hy hxy), ?_⟩
  have h9 := Sec4.Item434SporGen.card_m22E
  rwa [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure] at h9

end CFSG.RankThree.PartTwo.Sec13.ResProof
