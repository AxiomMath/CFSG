module

public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly.LowTwoRank

theorem psl_two_centralizer_comm {K : Type} [Group K] {g : ℕ}
    (hK : StatedClassicalModel K .PSL 2 2 g) {x a b : K} (hx1 : x ≠ 1) (ha : a * x = x * a)
    (hb : b * x = x * b) : a * b = b * a := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hK
  have hch : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcard
  obtain ⟨e'⟩ := CFSG.RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := F)
  let Φ : Matrix.SpecialLinearGroup (Fin 2) F ≃* K := e'.trans e.symm
  obtain ⟨x', rfl⟩ := Φ.surjective x
  obtain ⟨a', rfl⟩ := Φ.surjective a
  obtain ⟨b', rfl⟩ := Φ.surjective b
  have hx'1 : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hns : ¬ ∃ c : F, (x' : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rintro ⟨c, hc⟩
    apply hx'1
    have hdet : (x' : Matrix (Fin 2) (Fin 2) F).det = 1 := x'.2
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    have hc1 : c = 1 := by
      have h0 : (c - 1) ^ 2 = 0 := by linear_combination hdet - (c - 1) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
    apply Subtype.ext
    rw [hc, hc1, one_smul]
    rfl
  have ha' : a' * x' = x' * a' := Φ.injective (by rw [map_mul, map_mul]; exact ha)
  have hb' : b' * x' = x' * b' := Φ.injective (by rw [map_mul, map_mul]; exact hb)
  have h1 : (a' : Matrix (Fin 2) (Fin 2) F) * x' = x' * (a' : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F))
      ha'
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have h2 : (b' : Matrix (Fin 2) (Fin 2) F) * x' = x' * (b' : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F))
      hb'
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have h3 := CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hns h1.symm h2.symm
  have h4 : a' * b' = b' * a' := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact h3)
  rw [← map_mul, ← map_mul, h4]

end CFSG.RankThree.PartOne.K1327
