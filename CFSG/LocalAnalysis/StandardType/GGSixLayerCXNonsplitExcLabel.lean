module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcTags
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ExcNonsplit

section Dvd

variable {C : Type} [Group C]

@[expose] def GGNonsplitDvdAt (C : Type) [Group C] (p : ℕ) : Prop :=
  ∀ a : C, a ^ p = 1 → ∀ X : Subgroup C, IsComponentOf X (Subgroup.centralizer {a}) →
    p ∣ Nat.card X

theorem ggNonsplitCoreAt_of_dvd {p : ℕ} (h : GGNonsplitDvdAt C p) : GGNonsplitCoreAt C p :=
  fun a _ ha _ _ X hX hpX => absurd (h a ha X hX) hpX

theorem eq_one_of_pow_prime_eq_one [Finite C] {p : ℕ} (hp : p.Prime) (hC : ¬ p ∣ Nat.card C)
    {a : C} (ha : a ^ p = 1) : a = 1 := by
  have hcop : Nat.Coprime p (Nat.card C) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hC
  have h1 : orderOf a ∣ Nat.gcd p (Nat.card C) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_natCard a)
  rwa [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1

theorem ggNonsplitCoreAt_of_not_dvd [Finite C] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hC : ¬ p ∣ Nat.card C)
    (hlab : ∀ X : Subgroup C, IsComponentOf X ⊤ →
      ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markChar lab = 2 →
        MarkedModel lab (↥X ⧸ Subgroup.center ↥X) →
          ¬ LargeEvenHalfSplit p lab (Subgroup.center ↥X = ⊥)) :
    GGNonsplitCoreAt C p := by
  intro a b ha hb _ X hX _
  obtain rfl := eq_one_of_pow_prime_eq_one hp hC ha
  obtain rfl := eq_one_of_pow_prime_eq_one hp hC hb
  have htop : Subgroup.centralizer ({1} : Set C) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr (one_mem _))
  refine ⟨X, hX, le_rfl, ?_⟩
  rw [htop] at hX
  exact ClNonsplit.not_ggNbrClauseFiveMarking_of_inner hp hp3
    ⟨1, one_mem _, fun l _ => by group⟩ (hlab X hX)
    (fun lab hl _ _ => ggRawInnFieldInput_holds p hp hp2 lab hl)

end Dvd

end ExcNonsplit

namespace ExcNonsplit

theorem ne_three_of_not_dvd_card {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hq1 : ¬ p ∣ Nat.card K - 1) (hq2 : ¬ p ∣ Nat.card K + 1) : p ≠ 3 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hk] at hq1 hq2
  exact LinNonsplit.ne_three_of_not_dvd hq1 hq2

end ExcNonsplit

section Tags

@[expose] def GGF4NonsplitDvdInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card K - 1 → ¬ p ∣ Nat.card K + 1 → p ∣ Nat.card ↥(adjointGroup .F4 K) →
      ExcNonsplit.GGNonsplitDvdAt ↥(adjointGroup .F4 K) p

@[expose] def GGF4NonsplitCoprimeLabelInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card K - 1 → ¬ p ∣ Nat.card K + 1 → ¬ p ∣ Nat.card ↥(adjointGroup .F4 K) →
      ∀ X : Subgroup ↥(adjointGroup .F4 K), IsComponentOf X ⊤ →
        ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markChar lab = 2 →
          MarkedModel lab (↥X ⧸ Subgroup.center ↥X) →
            ¬ LargeEvenHalfSplit p lab (Subgroup.center ↥X = ⊥)

theorem ggExcNonsplitCoreInput_F4_of_dvd (hD : GGF4NonsplitDvdInput)
    (hL : GGF4NonsplitCoprimeLabelInput) : GGExcNonsplitCoreInput .F4 := by
  intro K _ _ _ p hp hp2 hq1 hq2
  by_cases hC : p ∣ Nat.card ↥(adjointGroup .F4 K)
  · exact ExcNonsplit.ggNonsplitCoreAt_of_dvd (hD K p hp hp2 hq1 hq2 hC)
  · exact ExcNonsplit.ggNonsplitCoreAt_of_not_dvd hp hp2
      (ExcNonsplit.ne_three_of_not_dvd_card hq1 hq2) hC (hL K p hp hp2 hq1 hq2 hC)

end Tags

end CFSG.StandardType
