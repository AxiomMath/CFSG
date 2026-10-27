module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114SolvOver
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem s21_14L34_holds (D : Data G) (Ch : Choice2011 G) : S21_14L34 D Ch := by
  intro _ c L hL _ _ hX _ hn hBL hfaith
  exfalso
  have h5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨h5⟩
  have h5B : 5 ∣ Nat.card c.B0 := by
    have h : 5 ∈ piSet c.B0 := by
      rw [c.hpi, hn]
      exact ⟨h5, by norm_num⟩
    exact h.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 5 h5B
  have hb5 : (b : G) ^ 5 = 1 := by
    rw [← Subgroup.orderOf_coe] at hb
    rw [← hb]
    exact pow_orderOf_eq_one _
  have hb1 : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ≠ 1 := fun h1 => by
    have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith b.2 h1
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hb
    exact h5.ne_one hb.symm
  have hd := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) le_rfl Nat.prime_two (LieModel.admissible hX).2.1
    (LieModel.statedClassicalModel hX (by decide))).1
  obtain ⟨U, hU, y, hy, hy1, hy5⟩ := uc22s2114_exists_of_solvOver c hL
    (fun _ hU => RankThreeUC.S15.K21dTitsProof.solvOver_of_lieModel le_rfl (Or.inl rfl) hX hU)
    b.2 (hBL b.2) hb5 hb1 fun _ => uc22p2214_out_mem_of_card_dvd hd h5 (by decide)
  exact hy1 (uc22s218_l3_eq_one_of_pow_eq_one hX h5 (by norm_num) (by norm_num) hU hy hy5)

end CFSG.LocalAnalysis.UniquenessCase.UC22
