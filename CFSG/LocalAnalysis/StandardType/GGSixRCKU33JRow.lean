module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33B0
public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs

public section

namespace CFSG.StandardType.RCKU33

open CFSG.Assembly

theorem tag_eq_g2der_of_row {lab : LargeEvenLabel}
    (h : CFSG.StandardType.ggSixRCKLabelRow lab = .U33) : lab.tag = .G2der := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  all_goals first
    | rfl
    | (dsimp only [CFSG.StandardType.ggSixRCKLabelRow] at h
       first
         | (split_ifs at h <;> exact absurd h (by decide))
         | exact absurd h (by decide))


section Main


theorem card_centerQuot_of_jRow_U33
    {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (h : CFSG.StandardType.GGSixRCKJRow .U33 J) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = 6048 := by
  unfold CFSG.StandardType.GGSixRCKJRow at h
  first
    | (obtain ⟨-, lab, -, hraw⟩ := CFSG.StandardType.largeEvenMarking_markedModel h
       obtain ⟨R, _, I, F, -, -, θ, hrow, hm⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
       exact CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der (tag_eq_g2der_of_row hrow)
         (CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm))
    | (obtain ⟨-, lab, -, hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel h
       obtain ⟨R, _, I, F, -, -, θ, hrow, hm⟩ :=
         CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
       exact CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der (tag_eq_g2der_of_row hrow)
         (CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm))

theorem not_jRow_U33
    {X : Type} [Group X] [Finite X] (hIn : GGInnCoprimeRankInput) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {G₀ A B₁ D J L : Subgroup X}
    (hA : CFSG.Open.IsElemAbelian p A) (hB₁A : B₁ ≤ A) (hDB₁ : D ≤ B₁)
    (hD : Nat.card ↥D = p ^ 2) (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (hB₁ : p ^ 4 ≤ Nat.card ↥B₁) (hB₁L : B₁ ≤ Subgroup.normalizer (L : Set X))
    (hmark : CFSG.StandardType.LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      CFSG.Assembly.LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ))
    (hLx : ∃ x ∈ D, x ≠ 1 ∧
      CFSG.Assembly.IsComponentOf L (G₀ ⊓ Subgroup.centralizer ({x} : Set X)))
    (hDL : ¬ D ≤ Subgroup.centralizer (L : Set X))
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X))) :
    ¬ CFSG.StandardType.GGSixRCKJRow .U33 J := fun h =>
  u33_card_ne_6048_of_input hIn hp hp2 hA hB₁A hDB₁ hD hB₁J hB₁ hB₁L hmark hLx hDL hJ
    (card_centerQuot_of_jRow_U33 h)

end Main


end CFSG.StandardType.RCKU33
