module

public import CFSG.Quasithin.Recognition.Kleidman.FiveObstruction
public import CFSG.Quasithin.Recognition.Kleidman.WordTransfer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Presentation
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.OrderDichotomy

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
open CFSG.Quasithin.Kleidman.ThreeLocal

namespace IsTypeH2

variable {G : Type} [Group G] [Finite G] {z : G}

theorem false_of_transfer_klein_five (h : IsTypeH2 G z) (hone : involutionClassCount G = 1)
    {J : Type*} [Group J] {e : Fin 7 → G} {j : Fin 7 → J}
    (htr : ∀ u : FreeGroup (Fin 7), FreeGroup.lift e u = 1 ↔ FreeGroup.lift j u = 1)
    (τw τ'w fw : FreeGroup (Fin 7))
    (hτ2 : FreeGroup.lift j τw * FreeGroup.lift j τw = 1) (hτ1 : FreeGroup.lift j τw ≠ 1)
    (hτ'2 : FreeGroup.lift j τ'w * FreeGroup.lift j τ'w = 1) (hτ'1 : FreeGroup.lift j τ'w ≠ 1)
    (hne : FreeGroup.lift j τw ≠ FreeGroup.lift j τ'w)
    (hcomm : FreeGroup.lift j τw * FreeGroup.lift j τ'w = FreeGroup.lift j τ'w * FreeGroup.lift j τw)
    (hf5 : FreeGroup.lift j fw ^ 5 = 1) (hf1 : FreeGroup.lift j fw ≠ 1)
    (hfτ : FreeGroup.lift j fw * FreeGroup.lift j τw = FreeGroup.lift j τw * FreeGroup.lift j fw)
    (hfτ' : FreeGroup.lift j fw * FreeGroup.lift j τ'w =
      FreeGroup.lift j τ'w * FreeGroup.lift j fw) : False := by
  have T := lift_eq_lift_iff htr
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have e1 : FreeGroup.lift e τw * FreeGroup.lift e τw = 1 := by
    have := (T (τw * τw) 1).mpr (by rw [map_mul, map_one]; exact hτ2)
    rwa [map_mul, map_one] at this
  have e2 : FreeGroup.lift e τw ≠ 1 := fun h1 =>
    hτ1 (by have := (T τw 1).mp (by rw [map_one]; exact h1); rwa [map_one] at this)
  have e3 : FreeGroup.lift e τ'w * FreeGroup.lift e τ'w = 1 := by
    have := (T (τ'w * τ'w) 1).mpr (by rw [map_mul, map_one]; exact hτ'2)
    rwa [map_mul, map_one] at this
  have e4 : FreeGroup.lift e τ'w ≠ 1 := fun h1 =>
    hτ'1 (by have := (T τ'w 1).mp (by rw [map_one]; exact h1); rwa [map_one] at this)
  have e5 : FreeGroup.lift e τw ≠ FreeGroup.lift e τ'w := fun h1 => hne ((T τw τ'w).mp h1)
  have e6 : FreeGroup.lift e τw * FreeGroup.lift e τ'w =
      FreeGroup.lift e τ'w * FreeGroup.lift e τw := by
    have := (T (τw * τ'w) (τ'w * τw)).mpr (by rw [map_mul, map_mul]; exact hcomm)
    rwa [map_mul, map_mul] at this
  have e7 : FreeGroup.lift e fw ^ 5 = 1 := by
    have := (T (fw ^ 5) 1).mpr (by rw [map_pow, map_one]; exact hf5)
    rwa [map_pow, map_one] at this
  have e8 : FreeGroup.lift e fw ≠ 1 := fun h1 =>
    hf1 (by have := (T fw 1).mp (by rw [map_one]; exact h1); rwa [map_one] at this)
  have e9 : FreeGroup.lift e fw * FreeGroup.lift e τw =
      FreeGroup.lift e τw * FreeGroup.lift e fw := by
    have := (T (fw * τw) (τw * fw)).mpr (by rw [map_mul, map_mul]; exact hfτ)
    rwa [map_mul, map_mul] at this
  have e10 : FreeGroup.lift e fw * FreeGroup.lift e τ'w =
      FreeGroup.lift e τ'w * FreeGroup.lift e fw := by
    have := (T (fw * τ'w) (τ'w * fw)).mpr (by rw [map_mul, map_mul]; exact hfτ')
    rwa [map_mul, map_mul] at this
  exact false_of_klein_five h hone e1 e2 e3 e4 e5 e6 (orderOf_eq_prime e7 e8) e9 e10

theorem false_of_rels_klein_five (h : IsTypeH2 G z) (hone : involutionClassCount G = 1)
    {J : Type*} [Group J] [Finite J] [IsSimpleGroup J] (R : List (List (Fin 7 × Bool)))
    (hbound : ∀ ρ : Fin 7 → G × J, (∀ r ∈ R, FreeGroup.lift ρ (FreeGroup.mk r) = 1) →
      Nat.card (Subgroup.closure (Set.range ρ)) ≤ Nat.card J)
    {e : Fin 7 → G} (he : ∀ r ∈ R, FreeGroup.lift e (FreeGroup.mk r) = 1) (he1 : ∃ i, e i ≠ 1)
    {j : Fin 7 → J} (hj : ∀ r ∈ R, FreeGroup.lift j (FreeGroup.mk r) = 1)
    (hjgen : Subgroup.closure (Set.range j) = ⊤) (τw τ'w fw : FreeGroup (Fin 7))
    (hτ2 : FreeGroup.lift j τw * FreeGroup.lift j τw = 1) (hτ1 : FreeGroup.lift j τw ≠ 1)
    (hτ'2 : FreeGroup.lift j τ'w * FreeGroup.lift j τ'w = 1) (hτ'1 : FreeGroup.lift j τ'w ≠ 1)
    (hne : FreeGroup.lift j τw ≠ FreeGroup.lift j τ'w)
    (hcomm : FreeGroup.lift j τw * FreeGroup.lift j τ'w = FreeGroup.lift j τ'w * FreeGroup.lift j τw)
    (hf5 : FreeGroup.lift j fw ^ 5 = 1) (hf1 : FreeGroup.lift j fw ≠ 1)
    (hfτ : FreeGroup.lift j fw * FreeGroup.lift j τw = FreeGroup.lift j τw * FreeGroup.lift j fw)
    (hfτ' : FreeGroup.lift j fw * FreeGroup.lift j τ'w =
      FreeGroup.lift j τ'w * FreeGroup.lift j fw) : False := by
  have hD : Nat.card (Subgroup.closure (Set.range fun i => (e i, j i))) ≤ 1 * Nat.card J := by
    rw [one_mul]
    exact hbound _ fun r hr => lift_pair_eq_one (he r hr) (hj r hr)
  have hK : ∀ K : Subgroup G, (∀ m ∈ Subgroup.closure (Set.range e), ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K ≤ 1 → K = ⊥ := fun K _ hK => Subgroup.eq_bot_of_card_le K hK
  exact false_of_transfer_klein_five h hone (lift_eq_one_iff e j hjgen hD hK he1) τw τ'w fw
    hτ2 hτ1 hτ'2 hτ'1 hne hcomm hf5 hf1 hfτ hfτ'

end IsTypeH2

end CFSG.Quasithin.Kleidman
