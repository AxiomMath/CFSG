module

public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem fiveShape_of_isShapeGroup {X : Type} [Group X]
    (h : Vol2.Ch10.SecA.IsShapeGroup X) : FiveShape X := by
  rcases h with ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ | ⟨n, hn⟩ | ⟨e⟩
  · refine Or.inl ⟨n, ?_⟩
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := n)
      (by rw [← Nat.card_eq_fintype_card, hK])
    have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
      H13.center_sl_eq_bot fun r hr => by
        have h1 : (r - 1) ^ 2 = 0 := by
          rw [sub_sq, hr, mul_one, two_mul, CharTwo.add_self_eq_zero, sub_zero, one_pow,
            CharTwo.add_self_eq_zero]
        exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)
    let eP : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have hn4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
      ⟨(e.trans eP.symm).trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  · exact Or.inr (Or.inl ⟨n, hn⟩)
  · refine Or.inr (Or.inr (Or.inr ?_))
    let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
      (QuotientGroup.quotientMulEquivOfEq
        CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
        QuotientGroup.quotientBot
    have hadm : StatedLieAdmissible .PSL 3 2 1 :=
      ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
    obtain ⟨e⟩ := e
    exact ⟨hadm, ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
      ⟨(e.trans e₂.symm).trans (projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))⟩⟩

end CFSG.Quasithin
