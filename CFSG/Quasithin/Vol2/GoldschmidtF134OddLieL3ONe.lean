module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OCyc
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OModel
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OConjMain
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLinesMain
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem false_of_ne {A : Type} [Group A] [Finite A] {p r : ℕ} [hp : Fact p.Prime]
    {L P T : Subgroup A} (hr : r.Prime) (hp5 : 5 ≤ p) (hpr : p ≠ r)
    (hL : StatedClassicalModel ↥L .PSL 3 r 1) (hcfg : OddCfg p L P T) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL hL
  have hp3 : p ≠ 3 := by omega
  have hpG : IsPGroup p ↥P := hcfg.isPGroup
  set PG : Subgroup (projectiveSL 3 K) := (P.subgroupOf L).map e.toMonoidHom with hPG
  let eP : ↥P ≃* ↥PG := (Subgroup.subgroupOfEquivOfLe hcfg.le).symm.trans
    ((P.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)
  have hPGp : IsPGroup p ↥PG := hpG.of_equiv eP
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp.out hr).1 h)
  by_cases hdvd : p ∣ Nat.card K - 1
  · have hexp : ∀ x ∈ PG, x ^ p = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow]
      have : y ^ p = 1 := Subtype.ext (by simpa using hcfg.exp y (Subgroup.mem_subgroupOf.1 hy))
      rw [this, map_one]
    have hcard : p ^ 2 ≤ Nat.card PG := by
      rw [← Nat.card_congr eP.toEquiv]
      rcases hcfg.card with h | h
      · exact h.ge
      · rw [h]
        exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
    obtain ⟨g, hg⟩ := exists_conj_torusP hp5 hdvd hexp hcard
    have hPG2 : Nat.card PG = p ^ 2 := by
      have h1 : Nat.card (PG.map (MulAut.conj g).toMonoidHom) = Nat.card PG :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      rw [hg, card_torusP hp5 hdvd] at h1
      exact h1.symm
    have hP2 : Nat.card P = p ^ 2 := by
      rw [← hPG2]
      exact Nat.card_congr eP.toEquiv
    have hconj : (torusP K p).map (MulAut.conj g⁻¹).toMonoidHom = PG := by
      have hcomp : ∀ y : projectiveSL 3 K,
          ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) y = y := fun y => by
        change g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y
        group
      rw [← hg, Subgroup.map_map]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [hcomp]
        exact hy
      · intro hx
        exact ⟨x, hx, hcomp x⟩
    have hinv : OddInvariantSet p PG := by
      rw [← hconj]
      exact (oddInvariantSet_torusP hp5 hdvd).of_mulEquiv (MulAut.conj g⁻¹)
    exact false_of_oddInvariantSet hcfg e hP2 hinv
  · exact hcfg.not_isCyclic ((eP.isCyclic).2 (isCyclic_of_isPGroup_projectiveSL hp3 hpK hdvd hPGp))

end CFSG.Quasithin.H13.NQCore.L3Odd
