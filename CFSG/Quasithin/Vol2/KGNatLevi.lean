module

public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.LieType.SteinbergBRSemidirectSLEven

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin

section Residual

theorem map_perfectResidual_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.perfectResidual A).map e.toMonoidHom = CFSG.perfectResidual B := by
  unfold CFSG.perfectResidual
  rw [Subgroup.map_iInf _ e.injective]
  exact iInf_congr fun n => map_derivedSeries_eq e.surjective n

@[expose] noncomputable def perfectResidualCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    ↥(CFSG.perfectResidual A) ≃* ↥(CFSG.perfectResidual B) :=
  ((CFSG.perfectResidual A).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_perfectResidual_equiv e))

@[expose] noncomputable def perfectCoreEquiv {G : Type*} [Group G] (X : Subgroup G) :
    ↥(perfectCore X) ≃* ↥(CFSG.perfectResidual ↥X) :=
  (MulEquiv.subgroupCongr (perfectCore_eq_map_perfectResidual X)).trans
    ((CFSG.perfectResidual ↥X).equivMapOfInjective X.subtype X.subtype_injective).symm

end Residual

section Levi

theorem levi_of_semidirect {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {N : Type*} [CommGroup N] [Finite N] (hN : IsPGroup 2 N)
    {φ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut N} {X : Type*} [Group X]
    (Φ : N ⋊[φ] Matrix.SpecialLinearGroup (Fin 2) F ≃* X) :
    Nonempty (X ⧸ CFSG.pCore 2 X ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  have hZ := CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (F := F) (m := 2)
    (by norm_num) (Or.inl rfl)
  obtain ⟨-, hO2, -, ⟨hq⟩⟩ :=
    CFSG.LieType.SteinbergBR.semidirect_SL_even_structure (by norm_num) (Or.inr ⟨s, hs⟩) hZ hN Φ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hO2).trans
    (hq.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))⟩

theorem isPGroup_mult_matrix {a b : Type*} {F : Type*} [Field F] [CharP F 2] :
    IsPGroup 2 (Multiplicative (Matrix a b F)) := fun x =>
  ⟨1, by
    rw [pow_one, sq]
    change Multiplicative.ofAdd (Multiplicative.toAdd x + Multiplicative.toAdd x) = 1
    have h : Multiplicative.toAdd x + Multiplicative.toAdd x = 0 := by
      ext i j
      exact CharTwo.add_self_eq_zero _
    rw [h]
    rfl⟩

end Levi

end CFSG.Quasithin.Vol2.KGNat
