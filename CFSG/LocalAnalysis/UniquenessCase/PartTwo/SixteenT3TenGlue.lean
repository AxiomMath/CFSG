module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3ElevTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Case3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16t_ten_map_conj_eq {T : Type} [CommGroup T] {X A : Subgroup (MulAut T)}
    (hAn : ∀ m ∈ X, ∀ a ∈ A, m * a * m⁻¹ ∈ A) {m : MulAut T} (hm : m ∈ X) :
    A.map (MulAut.conj m).toMonoidHom = A := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hAn m hm a ha
  · intro a ha
    refine ⟨m⁻¹ * a * m⁻¹⁻¹, ?_, ?_⟩
    · exact hAn m⁻¹ (X.inv_mem hm) a ha
    · simp [MulAut.conj_apply, mul_assoc]

variable {G : Type} [Group G] [Finite G]

theorem s16t_ten_blocks_of_case168_10 (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {p : ℕ} (hp : p = 3 ∨ p = 7)
    (h10 : Case168_10At D V₀ V hV L p) :
    ∃ Y : Fin 4 → Subgroup (Vtil V₀ V hV),
      S16tTenBlocks (Mbar D.M V₀ V hV) (fstarBar D.M V₀ V hV) Y p := by
  obtain ⟨hcyc, hrk, hs, -, hF⟩ := h10
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hpodd : Odd p := by rcases hp with rfl | rfl <;> decide
  have hodd : Odd (Nat.card ↥(barSub V₀ V hV L)) := by
    rw [show Nat.card ↥(barSub V₀ V hV L) = p from hcyc.2]
    exact hpodd
  obtain ⟨g, hg⟩ := s16t_twoConj_of_odd D h1217 hV hc hodd hs
  haveI : Fact p.Prime := ⟨hpp⟩
  have hLp : IsPGroup p ↥(lBar V₀ V hV L) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hcyc.2)
  have hLA : lBar V₀ V hV L ≤ fstarBar D.M V₀ V hV :=
    (s16c13bc_lBar_le_pCoreOf D hV hc hpp hLp hc.ne_bot).trans (s16t_pCoreOf_le_fstarBar D hV p)
  exact s16t_ten_blocks (s15_Infra_vtil_sq_eq_one V₀ V hV) hp hF
    (fun m hm a ha => s16t_fstarBar_conj_mem D hV hm ha) hLA hcyc.2 hrk hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
