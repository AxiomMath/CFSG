module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Quasithin.Vol2.Ch10SecKIK4c
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem nonempty_sl2_equiv_alt5 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(alternatingGroup (Fin 5))) := by
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hK]
    rfl
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl hK)
  exact ⟨((QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K)).trans e⟩

variable {Y X : Type} [Group Y] [Group X]

theorem nonempty_equiv_of_ker_eq_bot (π : Y →* X) (hπ : Function.Surjective π)
    (hk : π.ker = ⊥) : Nonempty (X ≃* Y) :=
  ⟨(MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hk, hπ⟩).symm⟩

theorem nonempty_equiv_quot_of_ker_eq (π : Y →* X) (hπ : Function.Surjective π) {N : Subgroup Y}
    [N.Normal] (hk : π.ker = N) : Nonempty (X ≃* Y ⧸ N) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)).symm⟩

theorem center_eq_bot_of_psl {n : ℕ} (hn : 0 < n) (h : IsPSL n 2 1 X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  let e' := e.trans (Setup.Family.statedProjSL_equiv_of_card_two n K hK2)
  have hZ := center_SL_eq_bot hn (K := ZMod 2) (Nat.card_zmod 2)
  apply Subgroup.card_eq_one.mp
  rw [Nat.card_congr (Subgroup.centerCongr e').toEquiv, hZ, Subgroup.card_bot]

theorem nonempty_equiv_sl_of_psl {n : ℕ} (h : IsPSL n 2 1 X) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨e.trans (Setup.Family.statedProjSL_equiv_of_card_two n K (by rw [hK, pow_one]))⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
