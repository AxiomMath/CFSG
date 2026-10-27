module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoBridgeA
public import CFSG.LocalAnalysis.StandardType.GGLevTwoBridgeB
public import CFSG.LocalAnalysis.StandardType.GGLevTwoBridgeC

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem LevTwoType

section Bridge

variable {G : Type} [Group G] [Finite G]

theorem levTwoModel (T : LevTwoType) (hT : T.Valid) (p : ℕ) (Bs : Subgroup G)
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (A : Subgroup (MulAut ↥Bs)) (hA : A ≤ ggInduced ⊤ Bs)
    (f : T.coxeter.Group ≃* ↥A)
    (hf : ∀ i : Fin T.n, GGIsReflection p ((f (T.coxeter.simple i) : ↥A) : MulAut ↥Bs))
    (x : ↥Bs) (AL : Subgroup (MulAut ↥Bs)) (ιL : Type) [Fintype ιL] (ML : CoxeterMatrix ιL)
    (hAL : AL ≤ A) (hfix : ∀ a ∈ AL, a x = x) (hML : GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML)
    (hW : GGWeylOfType p ML AL) (hcard : Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1))
    (hSat : ∀ a ∈ A, GGIsReflection p a → a x = x →
      (∃ g ∈ A, ∃ r ∈ AL, GGIsReflection p r ∧ a = g * r * g⁻¹) → a ∈ AL) :
    ∃ (c : Fin T.n → ZMod p) (Φ : Set (Fin T.n → ℤ)) (ρ : Wg T.rootFT ≃* ↥A),
      LevTwoData T.rootFT p c Φ ∧
      (∀ a : MulAut ↥Bs, (a ∈ A ∧ GGIsReflection p a) ↔
        ∃ g ∈ Refl T.rootFT, ((ρ g : ↥A) : MulAut ↥Bs) = a) ∧
      (Wsub T.rootFT Φ).map (A.subtype.comp ρ.toMonoidHom) = AL := by
  obtain ⟨c, ρ, hdict, hfixiff, hrk⟩ := levTwoPairModel T hT p Bs hp hp2 hEl hNT A hA f hf x
  obtain ⟨hPS, ⟨s, hsΦ, hsli, hscard⟩, h3, hAL'⟩ :=
    levTwoPhiData T hT p Bs hp hp2 hEl hNT A hA ρ hdict AL ιL ML hAL hML hW
  obtain ⟨hr1, hr2⟩ := levTwoRankPairModP T hT p hp hp2
  have hrk' := hrk (Fintype.card ιL + 1) hcard
  have hrefl : ∀ γ, IsRt T.rootFT γ → ((ρ (rRefl T.rootFT γ) : ↥A) : MulAut ↥Bs) ∈ A ∧
      GGIsReflection p ((ρ (rRefl T.rootFT γ) : ↥A) : MulAut ↥Bs) := fun γ hγ =>
    (hdict _).2 ⟨rRefl T.rootFT γ, (mem_Refl_iff T.rootFT).2 ⟨γ, hγ, rfl⟩, rfl⟩
  refine ⟨c, levTwoPhiOf T ρ AL, ρ, ⟨hPS, ?_, ?_, ?_⟩, hdict, hAL'⟩
  · intro β hβ
    exact (hfixiff β hβ.1).1 (hfix _ hβ.2)
  · intro β hβ hlam hex
    obtain ⟨α, hα, w, hwα⟩ := hex
    refine ⟨hβ, ?_⟩
    have hconj : ((ρ (rRefl T.rootFT β) : ↥A) : MulAut ↥Bs) =
        ((ρ w : ↥A) : MulAut ↥Bs) * ((ρ (rRefl T.rootFT α) : ↥A) : MulAut ↥Bs) *
          ((ρ w : ↥A) : MulAut ↥Bs)⁻¹ := by
      rw [← hwα, rRefl_smul T.rootFT hα.1 w]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hSat _ (hrefl β hβ).1 (hrefl β hβ).2 ((hfixiff β hβ).2 hlam)
      ⟨((ρ w : ↥A) : MulAut ↥Bs), (ρ w).2, ((ρ (rRefl T.rootFT α) : ↥A) : MulAut ↥Bs), hα.2,
        (hrefl α hα.1).2, hconj⟩
  · refine ⟨s, hsΦ, hsli, ?_, ?_, ?_⟩
    · rw [hscard]; exact h3
    · rw [Fintype.card_fin, hscard]; omega
    · by_cases hd : (p : ℤ) ∣ T.pair.det
      · right
        rw [LevTwoType.root, Matrix.det_transpose]
        exact hd
      · left
        have := hr2 hd
        rw [Fintype.card_fin, hscard]
        omega

end Bridge

end CFSG.StandardType.LevTwo
