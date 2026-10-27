module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeAssembly2
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresComm
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeNilpCard

public section

namespace CFSG.StandardType.A6Red.CoreShape

open Matrix CFSG.StandardType.LayerCores

theorem exists_coreFamily_adjCent_lie {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (hHerm : HermCoreInputLie) (hAlt : AltCoreInputLie)
    {A : Subgroup (GL ι K)} (hA : (Nat.card A : K) ≠ 0)
    {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)
    (hstab : ∀ X : Matrix ι ι K, (∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) →
      ∀ g ∈ A, adj X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * adj X)
    (hsymd : ∃ Y : Matrix ι ι K, (∀ g ∈ A, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
      Y + adj Y = 1)
    (hbig : 4 ≤ Nat.card K ∨ (Group.IsNilpotent ↥A ∧
      ∀ v : ι → K, (∀ g ∈ A, (g : Matrix ι ι K).mulVec v = v) → v = 0)) :
    ∃ (β : Type) (S : β → Subgroup (GL ι K)), IsCoreFamily (adjCent A hadj) S ∧
      ∀ c, GGA6CharTwoLie ↥(S c) := by
  obtain ⟨r, D, d, _, _, _, _, Φ, hΦ, hR⟩ := exists_algHom_pi_matrix_commutant A hA
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap K (D i)).injective 2
  obtain ⟨τ, hτ, hτΦ, himg⟩ := exists_tau_of_adj Φ hΦ hR hadj fun X hX =>
    (hR _).mpr (hstab X ((hR X).mp hX))
  have hy : ∃ y, y + τ y = 1 := by
    obtain ⟨Y, hYc, hY⟩ := hsymd
    obtain ⟨y, rfl⟩ := (hR Y).mpr hYc
    exact ⟨y, hΦ (by rw [map_add, hτΦ, hY, map_one])⟩
  have hbigD : ∀ b : Fin r, τ (piE D d b) = piE D d b →
      (∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) = Matrix.scalar (Fin (d b)) c) →
      4 ≤ Nat.card (D b) := by
    intro b _ _
    rcases hbig with hK | ⟨hnil, hfree⟩
    · exact le_trans hK (Nat.card_le_card_of_injective (algebraMap K (D b))
        (algebraMap K (D b)).injective)
    · exact card_ge_four_of_nilpotent_free A hnil hfree Φ hΦ hR b
  obtain ⟨β, S, hS, hshape⟩ := exists_coreFamily_unitaryOf_lie hHerm hAlt hτ hy hbigD
  refine ⟨β, fun c => (S c).map (Units.map Φ.toMonoidHom), ?_, ?_⟩
  · rw [← himg]
    exact hS.map _ (Units.map_injective (f := Φ.toMonoidHom) hΦ)
  · intro c
    exact GGA6CharTwoLie.of_mulEquiv
      ((S c).equivMapOfInjective (Units.map Φ.toMonoidHom)
        (Units.map_injective (f := Φ.toMonoidHom) hΦ)) (hshape c)

end CFSG.StandardType.A6Red.CoreShape

end
