module

public import CFSG.Quasithin.Background.FFC2Core

public section

namespace CFSG.Quasithin

theorem lka_card_of_alt5 {X : Type} [Group X] (e : X ≃* ↥(alternatingGroup (Fin 5))) :
    Nat.card X = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem lka_out_alt5 {X : Type} [Group X] (e : X ≃* ↥(alternatingGroup (Fin 5))) :
    Subgroup.center X = ⊥ ∧ Nat.card (MulAut X) ≤ 2 * Nat.card X := by
  have hcard : Nat.card X = 60 := lka_card_of_alt5 e
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup X := e.isSimpleGroup
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hcen : Subgroup.center X = ⊥ := by
    rcases (inferInstance : IsSimpleGroup X).eq_bot_or_eq_top_of_normal (Subgroup.center X) with
      hc | hc
    · exact hc
    · exfalso
      have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp hc
      have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp inferInstance
      rw [hcard] at hp
      norm_num at hp
  refine ⟨hcen, ?_⟩
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  have h1 := FFC.card_mulAut_alternating_le (n := 5) (Or.inl rfl)
  have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = Nat.card X := (Nat.card_congr e.toEquiv).symm
  omega

end CFSG.Quasithin
