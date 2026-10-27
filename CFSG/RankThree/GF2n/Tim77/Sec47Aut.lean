module

public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAut

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.Open

theorem sec47_card_le_hom {B L : Type} [Group B] [Group L] (σ : B →* MulAut L)
    (hσ : Function.Injective σ) (hB : IsElemAbelian 2 (⊤ : Subgroup B)) :
    IsElemAbelian 2 σ.range ∧ Nat.card σ.range = Nat.card B := by
  rw [MonoidHom.range_eq_map]
  refine ⟨hB.map σ, ?_⟩
  rw [Subgroup.card_map_of_injective hσ, Subgroup.card_top]

theorem sec47_card_le_psl2 {L : Type} [Group L] [Finite L] {f : ℕ} (hf : 1 ≤ f)
    (hL : IsPSL2Model L f) {B : Subgroup (MulAut L)} (hB : IsElemAbelian 2 B) :
    Nat.card B ≤ 2 ^ f := by
  obtain ⟨e⟩ := hL
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have e' : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    CFSG.ShultStronglyClosedTI.linearCover_pslEquivSL (K := GaloisField 2 f)
  exact CFSG.LocalAnalysis.WeakClosure81.card_le_two_pow_of_isL2Gp
    (n := f) ⟨GaloisField 2 f, inferInstance, inferInstance, hcard, ⟨e.trans e'⟩⟩ hB

theorem sec47_card_le_sz {L : Type} [Group L] [Finite L] {k : ℕ}
    (hk : 1 ≤ k) (hL : IsSzModel L k) {B : Subgroup (MulAut L)} (hB : IsElemAbelian 2 B) :
    Nat.card B ≤ 2 ^ (2 * k + 1) := by
  obtain ⟨e⟩ := hL
  obtain ⟨e'⟩ :=
    CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup k
  have hcard : Nat.card (GaloisField 2 (2 * k + 1)) = 2 ^ (2 * k + 1) :=
    GaloisField.card 2 (2 * k + 1) (by omega)
  exact CFSG.LocalAnalysis.WeakClosure81.card_le_two_pow_of_isSzGp
    (n := 2 * k + 1)
    ⟨rfl, k, hk, GaloisField 2 (2 * k + 1), inferInstance, inferInstance, rfl, hcard,
      ⟨e.trans e'⟩⟩ hB

end CFSG.RankThree.GF2n.Tim77
