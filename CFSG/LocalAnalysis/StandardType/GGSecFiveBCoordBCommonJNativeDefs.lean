module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGCoordDense {r p : ℕ} (f : Fin r → Multiplicative (ZMod p)) : Prop :=
  ∀ i, f i ≠ 1 ∧ ∀ j, f j = f i ∨ f j = (f i)⁻¹

@[expose] def GGCoordSparse {r p : ℕ} (f : Fin r → Multiplicative (ZMod p)) : Prop :=
  ∃ i, ∀ j, j ≠ i → f j = 1

@[expose] def GGSignedCoords {H : Type} [Group H] {p r : ℕ} (T : Subgroup H)
    (Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥T) : Prop :=
  ∀ (g : H) (hg : ∀ s ∈ T, g * s * g⁻¹ ∈ T),
    SpCoord.IsSignedPerm fun f => Θ.symm ⟨g * (Θ f : H) * g⁻¹, hg _ (Θ f).2⟩

@[expose] def GGSecFiveBNativeAt (H : Type) [Group H] (p r : ℕ) (SD SS : LargeEvenLabel → Prop)
    (T : Subgroup H) : Prop :=
  ∃ Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥T, GGSignedCoords T Θ ∧
    ∀ (t : ↥T) (J : Subgroup H),
      CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({(t : H)} : Set H)) →
      Nat.card ↥(T ⊓ Subgroup.centralizer (J : Set H)) = p →
        (GGCoordDense (Θ.symm t) ∧ ∃ lab, SD lab ∧ LargeEvenInLambda2 lab ∧
            GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧
            (lab = ⟨.twA, 3, 1⟩ → Subgroup.center ↥J = ⊥)) ∨
          (GGCoordSparse (Θ.symm t) ∧ ∃ lab, SS lab ∧ LargeEvenInLambda2 lab ∧
            GGHasLabel lab (↥J ⧸ Subgroup.center ↥J))

@[expose] def GGSecFiveBNativeRow (H : Type) [Group H] (p r : ℕ)
    (SD SS : LargeEvenLabel → Prop) : Prop :=
  ∀ T : Subgroup H, IsElemAbelian p T → Nat.card T = p ^ r → GGSecFiveBNativeAt H p r SD SS T

@[expose] def GGSecFiveBNativeSparseAt (H : Type) [Group H] (p r : ℕ) (T : Subgroup H) : Prop :=
  ∃ Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥T, GGSignedCoords T Θ ∧
    ∀ t : ↥T, t ≠ 1 → GGCoordSparse (Θ.symm t) →
      ∃ K : Subgroup H,
        CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({(t : H)} : Set H)) ∧
        (∀ K' : Subgroup H,
          CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer ({(t : H)} : Set H)) → K' = K) ∧
        T ⊓ Subgroup.centralizer (K : Set H) = Subgroup.zpowers (t : H) ∧ 7 ∣ Nat.card K

@[expose] def GGSecFiveBNativeSparseRow (H : Type) [Group H] (p r : ℕ) : Prop :=
  ∀ T : Subgroup H, IsElemAbelian p T → Nat.card T = p ^ r → GGSecFiveBNativeSparseAt H p r T

end CFSG.StandardType

end
