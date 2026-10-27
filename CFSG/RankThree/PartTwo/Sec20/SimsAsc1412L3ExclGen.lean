module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Excl
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Index
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3L3Words
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3U3Words
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec20

theorem prime_dvd_two_pow_sub_one_le_eight1412 {p : ℕ} (hp : p.Prime) {e : ℕ} (he1 : 1 ≤ e)
    (he8 : e ≤ 8) (hpe : p ∣ 2 ^ e - 1) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
  have hp2 := hp.two_le
  have hle : p ≤ 2 ^ e - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))) hpe
  interval_cases e <;> norm_num at hpe hle <;> interval_cases p <;>
    first | omega | exact absurd hp (by norm_num)

theorem excl1412_of_isL3eps1412 {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (hL : IsL3eps1412 G p) (h5 : p ≠ 5) (h7 : p ≠ 7) (h17 : p ≠ 17) (h31 : p ≠ 31)
    (h127 : p ≠ 127) (α : MulAut G) (hα : orderOf α = 2) : Excl1412 α := by
  have hp3 := hL.1
  have he : ∀ {H : Type} [Group H] (ε : G ≃* H) (y : H),
      MulAut.congr ε α y * y⁻¹ = ε (α (ε.symm y) * (ε.symm y)⁻¹) := fun ε y => by
    simp [MulAut.congr_apply]
  have hex : ∃ x : G, p ∣ orderOf (α x * x⁻¹) := by
    obtain ⟨-, ⟨hp, ⟨e⟩⟩ | ⟨hp, ⟨e⟩⟩⟩ := hL
    ·
      have hp5 : 5 ≤ p := by omega
      set ε : G ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
          (GaloisField p 1) :=
        e.trans (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 _) with hε
      have hα' : orderOf (MulAut.congr ε α) = 2 := by rw [MulEquiv.orderOf_eq]; exact hα
      have hF : Nat.card (GaloisField p 1) = p := by
        rw [GaloisField.card p 1 (by norm_num), pow_one]
      obtain ⟨y, hy⟩ := exists_dvd_orderOf_mul_inv_projectiveSL3 hF hp5 _ hα'
      refine ⟨ε.symm y, ?_⟩
      rwa [he ε y, MulEquiv.orderOf_eq] at hy
    ·
      have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 p 1 :=
        ⟨Fact.out, le_rfl, le_rfl, fun h => by
          have h2 := (Prod.mk.inj h).2
          rw [pow_one] at h2
          omega⟩
      obtain ⟨-, K, _, _, hK, ⟨eD⟩⟩ :=
        CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e
      have hu : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 K :=
        ⟨Fact.out, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
      set ε := eD.trans
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm with hε
      have hα' : orderOf (MulAut.congr ε α) = 2 := by rw [MulEquiv.orderOf_eq]; exact hα
      obtain ⟨y, hy⟩ := exists_dvd_orderOf_mul_inv_unitaryPSU3 hu hp _ hα'
      refine ⟨ε.symm y, ?_⟩
      rwa [he ε y, MulEquiv.orderOf_eq] at hy
  obtain ⟨x, hx⟩ := hex
  refine Or.inl ⟨x, p, 1, Fact.out, by omega, le_rfl, fun e he1 he8 hdvd => ?_, by simpa using hx⟩
  rw [pow_one] at hdvd
  rcases prime_dvd_two_pow_sub_one_le_eight1412 Fact.out he1 he8 hdvd with h | h | h | h | h | h <;>
    omega

end CFSG.RankThree.PartTwo.Sec20
