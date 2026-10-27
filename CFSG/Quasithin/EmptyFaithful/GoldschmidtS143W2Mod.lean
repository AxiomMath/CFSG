module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Gen

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

theorem card_quotient_center_of_equiv {L X : Type} [Group L] [Group X] (e : L ≃* X)
    (hZ : Subgroup.center X = ⊥) :
    Subgroup.center L = ⊥ ∧ Nat.card (L ⧸ Subgroup.center L) = Nat.card X := by
  have h1 : (Subgroup.center L).map e.toMonoidHom = Subgroup.center X := Subgroup.map_center_eq e
  rw [hZ] at h1
  have hZL : Subgroup.center L = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  refine ⟨hZL, ?_⟩
  rw [hZL, Nat.card_congr (QuotientGroup.quotientBot (G := L)).toEquiv,
    Nat.card_congr e.toEquiv]

theorem numFactW_of_model_card_big {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (h : 2 ^ 7 ∣ Nat.card X) : NumFactW (fun L _ => Nonempty (L ≃* X)) :=
  numFactW_of_big fun _ _ _ _ ⟨e⟩ => by
    rw [(card_quotient_center_of_equiv e hZ).2]
    exact h

theorem numFactW_of_model_big_inv {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hc : ∀ t : X, orderOf t = 2 → 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({t} : Set X))) :
    NumFactW (fun L _ => Nonempty (L ≃* X)) := by
  refine numFactW_of_big_inv fun L _ _ _ ⟨e⟩ z hz2 hzc => ?_
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have hz2' : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
  have hz1' : e z ≠ 1 := fun h => hz1 (e.injective (by rw [h, map_one]))
  have hord : orderOf (e z) = 2 := orderOf_eq_prime (by rwa [sq]) hz1'
  rw [(card_quotient_center_of_equiv e hZ).2]
  exact (hc (e z) hord).trans (Subgroup.card_subgroup_dvd_card _)

end InspW2

end S143

end CFSG.Quasithin
