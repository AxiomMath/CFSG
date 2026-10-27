module

public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Bridges
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
import CFSG.Timmesfeld.Orders.PpdE6D4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

section Cert

theorem ggKSL_labOrd_eq {lab : LargeEvenLabel} {X : Type} [Group X] (hl : LargeEvenInLambda2 lab)
    (h : GGHasLabel lab X) : SporadicShape.labOrd lab = Nat.card X :=
  SporadicShape.labOrd_eq_of_rawDatum hl
    (largeEvenRawDatum_mono (fun _ _ _ _ ⟨e⟩ => (Nat.card_congr e.toEquiv).symm) h)

theorem ggKSL_labOrd_dvd {G : Type} [Group G] [Finite G] {J K : Subgroup G} (hJK : J ≤ K)
    {lab mu : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hK : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) (hm : LargeEvenInLambda2 mu)
    (hJ : GGHasLabel mu (↥J ⧸ Subgroup.center ↥J)) :
    SporadicShape.labOrd mu ∣ SporadicShape.labOrd lab := by
  rw [ggKSL_labOrd_eq hm hJ, ggKSL_labOrd_eq hl hK]
  exact RCKU33.card_centerQuot_dvd hJK

end Cert

theorem ggKSL_labOrd_typeA_three_not_dvd {t : LargeEvenLieTag}
    (ht : t = .triD4 ∨ t = .B2der ∨ t = .G2der ∨ t = .twF4der) {f : ℕ} (hf : 2 ≤ f) :
    ¬ SporadicShape.labOrd ⟨.A, 3, f⟩ ∣ SporadicShape.labOrd ⟨t, 0, 1⟩ := by
  intro h
  have h6 : 2 ^ (f * 6) ∣ SporadicShape.labOrd ⟨.A, 3, f⟩ := by
    rw [pow_mul]
    exact EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSL) (n := 4) (by decide) (2 ^ f)
  have hpow : ∀ k ≤ f * 6, 2 ^ k ∣ SporadicShape.labOrd ⟨t, 0, 1⟩ := fun k hk =>
    ((pow_dvd_pow 2 hk).trans h6).trans h
  rcases ht with rfl | rfl | rfl | rfl
  · rcases (by omega : f = 2 ∨ 3 ≤ f) with rfl | hf3
    · exact absurd h (by decide)
    · exact absurd (hpow 18 (by omega)) (by decide)
  all_goals exact absurd (hpow 12 (by omega)) (by decide)

end CFSG.StandardType

end
