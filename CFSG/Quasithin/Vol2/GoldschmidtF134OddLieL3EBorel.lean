module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3EArith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3EIrred
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3EPlane
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3ETorus
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg

public section

namespace CFSG.Quasithin.H13.NQCore.Psl3Even

open CFSG.Quasithin.F134.LieL3
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped MatrixGroups

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem false_of_dvd_pred [Finite A] [hp : Fact p.Prime] (hp5 : 5 ≤ p) (h : OddCfg p L P T)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpK : p ∣ Nat.card K - 1)
    (e₁ : ↥L ≃* projectiveSL 3 K) : False := by
  classical
  obtain ⟨a, ha, hPa⟩ := h.exists_card
  have hS := h.isSylowTwoOf_inf
  have hUL2 : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  obtain ⟨e, hUe⟩ := exists_equiv_map_eq_projUnitriangular e₁ hUL2 hS.2.2
  set P' : Subgroup (projectiveSL 3 K) := (P.subgroupOf L).map e.toMonoidHom with hP'def
  have hP'card : Nat.card P' = p ^ a := by
    rw [hP'def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv, hPa]
  have hP'exp : ∀ x ∈ P', x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy3 : y ^ p = 1 := Subtype.ext (by simpa using h.exp y (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy3, map_one]
  have hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ P', ∃ y ∈ P', ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s := by
    intro u hu x hx
    rw [← hUe] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y, hy, s, hs, hys⟩ := h.mul_inf u' (Subgroup.mem_subgroupOf.mp hu') x'
      (Subgroup.mem_subgroupOf.mp hx')
    refine ⟨e ⟨y, h.le hy⟩, ⟨⟨y, h.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩,
      e ⟨s, hs.2⟩, ?_, ?_⟩
    · rw [← hUe]
      exact ⟨⟨s, hs.2⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    · change e u' * e x' = e ⟨y, h.le hy⟩ * e ⟨s, hs.2⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hys
  obtain ⟨c1, c2, c3⟩ := coprime_of_dvd_pred hp.out hp5 Finite.card_pos hpK
  have hcop : ∀ m, Nat.Coprime p m → Nat.Coprime (Nat.card P') m := fun m hm => by
    rw [hP'card]
    exact hm.pow_left a
  have hPB : ∀ g : SL(3, K), proj 3 K g ∈ P' → g ∈ upperTriangular 3 K := fun g hg =>
    mem_upperTriangular_of_coprime (hcop _ c1) (hcop _ c2) (hcop _ c3) hQU hg
  have hodd : Nat.Coprime (Nat.card P') 2 :=
    hcop 2 ((Nat.coprime_primes hp.out Nat.prime_two).mpr (by omega))
  have hlt : p < Nat.card P' := by
    rw [hP'card]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ a := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  have : NeZero p := ⟨hp.out.ne_zero⟩
  exact false_of_borel h e hUe (fun x hx y hy => mul_comm_of_borel hPB hodd hx hy)
    (inf_ratioGroup_ne_bot_of_exp hPB hlt hP'exp) (not_le_ratioGroup_of_exp hPB hlt hodd hP'exp)

end CFSG.Quasithin.H13.NQCore.Psl3Even
