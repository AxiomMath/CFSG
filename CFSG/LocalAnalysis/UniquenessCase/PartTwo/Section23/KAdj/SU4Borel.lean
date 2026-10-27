module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Quasithin.H13.U4ParPoint
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Hall
import CFSG.RankThree.CentralLiftU.UnitaryBorelLift
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer)
open KTabD (lineStab mem_lineStab)

variable {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)

theorem su4_lineStab_eq_parP : lineStab (hypSU h 2 0) (Pi.single ie1 1) = parP h := by
  ext g
  rw [mem_lineStab, mem_parP_iff h g]
  constructor
  · rintro ⟨c, hc⟩ a ha
    have h := congrFun hc a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne ha,
      smul_zero] at h
    exact h
  · intro hcol
    refine ⟨((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1, ?_⟩
    funext a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply]
    by_cases ha : a = ie1
    · rw [ha]
      simp [smul_eq_mul]
    · simp [hcol a ha, Pi.single_eq_of_ne ha]

theorem su4_parP_inf_flagStabilizer_eq_hypBorel :
    parP h ⊓ flagStabilizer h 2 0 {2} = hypBorel h 2 0 := by
  ext g
  rw [Subgroup.mem_inf, mem_hypBorel, UnitaryHigher.mem_flagStabilizer,
    UnitaryHigher.mem_isoStabilizer]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hi2
    rcases (by omega : i = 1 ∨ i = 2) with hi | hi
    · rw [hi]; exact h1
    · rw [hi]; exact h2 2 (by simp)
  · intro hb
    refine ⟨hb 1 (by norm_num) (by norm_num), fun i hi => ?_⟩
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    exact hb 2 (by norm_num) (by norm_num)

private theorem hypTorus_card_odd_D02 : ¬ 2 ∣ Nat.card ↥(hypTorus h 2 0) := by
  let f : ↥(hypTorus h 2 0) →* (Fin 2 → Kˣ) :=
    (hypDiagHom h 2 0 (Nat.zero_le 1)).comp
      (Subgroup.inclusion (hypTorus_le_hypBorel h))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : Subgroup.inclusion (hypTorus_le_hypBorel h) x ∈
        (hypDiagHom h 2 0 (Nat.zero_le 1)).ker := hx
    rw [ker_hypDiagHom (Nat.zero_le 1), Subgroup.mem_subgroupOf] at hmem
    have hU : (x : hypSU h 2 0) ∈ hypUnitriangular h 2 0 := by simpa using hmem
    have hmem2 : (x : hypSU h 2 0) ∈ hypUnitriangular h 2 0 ⊓ hypTorus h 2 0 :=
      Subgroup.mem_inf.mpr ⟨hU, x.2⟩
    rw [CFSG.RankThree.CentralLiftU.hypUnitriangular_inf_hypTorus] at hmem2
    exact Subtype.ext (Subgroup.mem_bot.mp hmem2)
  have hdvd : Nat.card ↥(hypTorus h 2 0) ∣ Nat.card (Fin 2 → Kˣ) :=
    Subgroup.card_dvd_of_injective f hinj
  rw [card_fun_units h 2] at hdvd
  have hbase : Odd (((2 : ℕ) ^ a) ^ 2 - 1) := by
    refine Nat.Even.sub_odd ?_ ?_ odd_one
    · rw [← pow_mul]; exact Nat.one_le_two_pow
    · rw [Nat.even_pow]
      exact ⟨(Nat.even_pow).mpr ⟨even_two, by have := h.one_le; omega⟩, by norm_num⟩
  exact (Odd.of_dvd_nat (Odd.pow hbase) hdvd).not_two_dvd_nat

theorem su4_exists_conj_mem_hypTorus {t : ↥(hypSU h 2 0)} (ht : t ∈ hypBorel h 2 0)
    (hodd : ¬ 2 ∣ orderOf t) :
    ∃ e ∈ hypUnitriangular h 2 0, e * t * e⁻¹ ∈ hypTorus h 2 0 := by
  haveI : Finite K := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hET : hypTorus h 2 0 ≤
      Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact CFSG.RankThree.CentralLiftU.conj_mem_hypUnitriangular_of_mem_hypBorel
        (h := h) (r := 2) (ε := 0) (Nat.zero_le 1) (hypTorus_le_hypBorel h hb) hu
    · intro hu
      have hb' : b⁻¹ ∈ hypTorus h 2 0 := (hypTorus h 2 0).inv_mem hb
      have h := CFSG.RankThree.CentralLiftU.conj_mem_hypUnitriangular_of_mem_hypBorel
        (h := h) (r := 2) (ε := 0) (Nat.zero_le 1) (hypTorus_le_hypBorel h hb') hu
      rwa [show b⁻¹ * (b * u * b⁻¹) * (b⁻¹)⁻¹ = u by group] at h
  have hE : IsPGroup 2 (hypUnitriangular h 2 0) :=
    CFSG.RankThree.CentralLiftU.isPGroup_hypUnitriangular (h := h) (r := 2) (ε := 0)
      (Nat.zero_le 1)
  have hT : ¬ 2 ∣ Nat.card ↥(hypTorus h 2 0) := hypTorus_card_odd_D02 h
  have ht' : t ∈ hypUnitriangular h 2 0 ⊔ hypTorus h 2 0 :=
    CFSG.RankThree.CentralLiftU.hypBorel_le_sup (h := h) (r := 2) (ε := 0)
      (Nat.zero_le 1) (by norm_num) ht
  exact exists_conj_mem_of_mem_sup (G := ↥(hypSU h 2 0)) (p := 2)
    (E := hypUnitriangular h 2 0) (T := hypTorus h 2 0) hET hE hT ht' hodd

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
