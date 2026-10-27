module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders

@[expose] def bmGlOrd (N q : ℕ) : ℕ :=
  q ^ (N * (N - 1) / 2) * (List.range N).foldl (fun a i => a * (q ^ (i + 1) - 1)) 1

@[expose] def OrdBMBound (t : StatedLieTag) (n p f : ℕ) (B : ℕ) : Prop :=
  ∀ (R : Type) [Group R] [Finite R], IsSimpleGroup R → LieModel R t n p f →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → (Nat.card (MulAut R)).factorization ℓ ≤ B.factorization ℓ

@[expose] def OrdBMRow (p k : ℕ) (lab : LargeEvenLabel) : Prop :=
  ∀ (R : Type) [Group R] [Finite R], IsSimpleGroup R → MarkedModel lab R →
    ¬ p ^ k ∣ Nat.card (MulAut R)

theorem bmOrd_of_rows
    {K : Type} [Group K] [Finite K] (p N : ℕ) (hK : Nat.card K = N)
    (hrows : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → labOrd lab ∣ N →
      OrdBMRow p (N.factorization p) lab) :
    BMOrd p K := by
  intro L hLs hmark
  obtain ⟨lab, hlab, hmodel, hcard⟩ := largeEvenMarking_card_labOrd hmark
  have hc : Subgroup.center ↥L = ⊥ := by
    rcases hLs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      have hbot : commutator ↥L = ⊥ := by
        rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro g _
        exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x)) g
      have htop : commutator ↥L = ⊤ := hmark.1
      haveI := hLs.toNontrivial
      rw [hbot] at htop
      exact bot_ne_top htop
  have e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hmodelL : MarkedModel lab ↥L := MarkedModel.of_mulEquiv e hmodel
  have hcardL : Nat.card ↥L = labOrd lab := by rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm
  have hdvd : labOrd lab ∣ N := by
    rw [← hcardL, ← hK]
    exact Subgroup.card_subgroup_dvd_card L
  rw [hK]
  exact hrows lab hlab hdvd ↥L hLs hmodelL

end CFSG.StandardType.SporadicShape
