module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKMarking
public import CFSG.LocalAnalysis.StandardType.GGSixRCKL32
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGSixRootCommKnownIf
    (P : ∀ {X : Type} [Group X], Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    P J →
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∃ (V : Subgroup X) (r : X),
      r ∈ V ∧ V ≤ J ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      r ∉ Subgroup.centralizer (J : Set X) ∧ (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) ∧
      (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (L : Set X) →
        Y ≤ Subgroup.normalizer (J : Set X) → Y ≤ Subgroup.centralizer (D : Set X) →
        Y ≤ Subgroup.centralizer {r} →
        (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
        ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
          v * y * v⁻¹ * y⁻¹ = r ^ k * z) ∧
      ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) →
        J ≤ K → Odd (Nat.card (Subgroup.center ↥K)) →
          pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.normalizer (V : Set X)

@[expose] def GGSixRootCommKnownRow
    (i : GGSixRCKRow) : Prop :=
  GGSixRootCommKnownIf (fun {_} [Group _] J => GGSixRCKJRow i J)


theorem ggSixRootCommKnown_iff_rows :
    GGSixRootCommKnown ↔ ∀ i : GGSixRCKRow, GGSixRootCommKnownRow i := by
  constructor
  · intro h i X _ _ t n f ψ p G₀ A B₁ D J L _ hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN hBC h4
      hsc hrank hAC hBL hmkL hJc hZ hLG hLx hDL hJL hA6
    exact h X t n f ψ p G₀ A B₁ D J L hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN hBC h4 hsc hrank
      hAC hBL hmkL hJc hZ hLG hLx hDL hJL hA6
  · intro h X _ _ t n f ψ p G₀ A B₁ D J L hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN hBC h4 hsc
      hrank hAC hBL hmkL hJc hZ hLG hLx hDL hJL hA6
    obtain ⟨i, hi⟩ := ggSixRCKJRow_of_marking
      (ggSixRootCommKnown_marking X p G₀ A D J hp hp2 hA (hDB.trans hBA) hAN hmk hJc)
    exact h i X t n f ψ p G₀ A B₁ D J L hi hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN hBC h4 hsc
      hrank hAC hBL hmkL hJc hZ hLG hLx hDL hJL hA6


theorem ggSixRootCommKnownRow_L32 :
    GGSixRootCommKnownRow .L32 := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L hrow _ _ hp hp2 hA hBA hDB hD _ _ hBN hBC h4 _ _ _ _ _ _ _ _ _ _ _ _
  exact absurd hrow (not_jRow_L32_of_hA hp hp2 (CFSG.Open.IsElemAbelian.mono hA hBA) hD hBN hBC h4)

end CFSG.StandardType
