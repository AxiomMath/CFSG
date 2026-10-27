module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter

open scoped Pointwise

universe u

/-- In a finite semidirect product with an odd-prime-power normal kernel,
a Sylow subgroup for a distinct prime is conjugate into the cyclic
complement. -/
public theorem secondCase_linear_sylow_into_semidirect_complement
    {H : Type u} [Group H] [Finite H]
    {r p m : ℕ} [Fact r.Prime] [Fact p.Prime]
    (N C : Subgroup H)
    (hNnormal : N.Normal) (hNcard : Nat.card N = r ^ m)
    (hdisj : Disjoint N C) (hjoin : N ⊔ C = ⊤)
    (hpne : p ≠ r) (X : Sylow p H) :
    ∃ g : H, (X : Subgroup H).map (MulAut.conj g).toMonoidHom ≤ C := by
  classical
  let : N.Normal := hNnormal
  have hcomp : N.IsComplement' C := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    rw [← Subgroup.normal_mul N C, hjoin]
    rfl
  have hpN : ¬ p ∣ Nat.card N := by
    rw [hNcard]
    intro h
    have hpr : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow h
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime r)).mp hpr with h1 | heq
    · exact (Fact.out : Nat.Prime p).ne_one h1
    · exact hpne heq
  have hCindex : C.index = Nat.card N := by
    have hcard := hcomp.card_mul
    have hmul := C.card_mul_index
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C))
    calc
      Nat.card C * C.index = Nat.card H := hmul
      _ = Nat.card N * Nat.card C := hcard.symm
      _ = Nat.card C * Nat.card N := by ac_rfl
  let PC0 : Sylow p C := default
  let PC : Subgroup H := (PC0 : Subgroup C).map C.subtype
  have hPCp : IsPGroup p PC :=
    (PC0.isPGroup').map C.subtype
  have hPCindex : ¬ p ∣ PC.index := by
    rw [show PC = (PC0 : Subgroup C).map C.subtype by rfl,
      Subgroup.index_map_of_injective
        (H := (PC0 : Subgroup C)) C.subtype_injective]
    simp only [Subgroup.range_subtype, hCindex]
    exact Nat.Prime.not_dvd_mul Fact.out PC0.not_dvd_index hpN
  let PH : Sylow p H := hPCp.toSylow hPCindex
  obtain ⟨g, hg⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq H (Sylow p H)
      inferInstance inferInstance X PH
  refine ⟨g, ?_⟩
  have hg' := congrArg (fun S : Sylow p H => (S : Subgroup H)) hg
  rw [Sylow.coe_subgroup_smul] at hg'
  change (MulAut.conj g • (X : Subgroup H)) ≤ C
  rw [hg']
  have hPH : (PH : Subgroup H) = PC := by simp [PH]
  rw [hPH]
  simpa [PC, Subgroup.range_subtype] using
    (Subgroup.map_le_range C.subtype (PC0 : Subgroup C))

end CFSG.GorensteinWalter
