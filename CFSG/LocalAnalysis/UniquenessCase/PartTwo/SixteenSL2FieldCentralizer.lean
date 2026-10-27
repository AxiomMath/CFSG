module

public import CFSG.GroupTheory.PRankBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MbarSigmaRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_ne_bot_of_isL2_four_or_eight
    {X : Type} [Group X] [Finite X]
    {A H : Subgroup X} {p : ℕ}
    (hshape : (p = 3 ∧ UC22.IsL2 ↥H 2) ∨
      (p = 7 ∧ UC22.IsL2 ↥H 3))
    (hHn : A ≤ normalizer (H : Set X))
    (hpA : 2 ≤ CFSG.Open.pRank p A) :
    A ⊓ centralizer (H : Set X) ≠ ⊥ := by
  classical
  have finish (hp : p.Prime) (hcard : ¬ p ^ 2 ∣ Nat.card (MulAut ↥H)) :
      A ⊓ centralizer (H : Set X) ≠ ⊥ := by
    have hAutLe : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥H)) ≤ 1 := by
      refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ
        (G := MulAut ↥H) (H := ⊤) (p := p) (k := 1) hp ?_
      simpa [Subgroup.card_top] using hcard
    have hineq := CFSG.AGLEmbedding.pRank_le_pRank_inf_centralizer_add_pRank_mulAut
      (X := X) (K := H) (R := A) hp hHn
    by_contra hbot
    have hbotRank : CFSG.Open.pRank p (A ⊓ centralizer (H : Set X)) = 0 := by
      rw [hbot]
      exact CFSG.AGLEmbedding.pRank_bot_eq_zero (X := X) hp
    omega
  rcases hshape with ⟨hp3, hL2⟩ | ⟨hp7, hL2⟩
  · refine finish (by rw [hp3]; norm_num) ?_
    have hAut : Nat.card (MulAut ↥H) = 120 :=
      CFSG.LocalAnalysis.GLTheoremA.small_card_psl24 hL2
    rw [hAut, hp3]
    norm_num
  · refine finish (by rw [hp7]; norm_num) ?_
    have hAut : Nat.card (MulAut ↥H) = 1512 :=
      CFSG.LocalAnalysis.GLTheoremA.small_card_psl28 hL2
    rw [hAut, hp7]
    norm_num

theorem sl2_centralizer_ne_bot_of_natural
    {W : Type} [CommGroup W] [Finite W]
    {A H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    {p : ℕ} (hpK : p = Nat.card K - 1)
    (hHn : A ≤ normalizer (H : Set (MulAut W)))
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H U Z)
    (hpA : 2 ≤ CFSG.Open.pRank p A) :
    A ⊓ centralizer (H : Set (MulAut W)) ≠ ⊥ := by
  classical
  obtain ⟨π, hπ⟩ := hreal
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on
      (FFModel.nat_faithful (StatedSL 2 K)) hπ
  let e : StatedSL 2 K ≃* H := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  have hshape : (p = 3 ∧ UC22.IsL2 ↥H 2) ∨ (p = 7 ∧ UC22.IsL2 ↥H 3) := by
    rcases hK with h4 | h8
    · left
      refine ⟨by omega, ?_⟩
      exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_statedSL
        (X := ↥H) (n := 2) (by norm_num) (by rw [h4]; norm_num) e.symm
    · right
      refine ⟨by omega, ?_⟩
      exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_statedSL
        (X := ↥H) (n := 3) (by norm_num) (by rw [h8]; norm_num) e.symm
  exact centralizer_ne_bot_of_isL2_four_or_eight hshape hHn hpA

theorem sl2_centralizer_ne_bot_of_field_extension
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h125 : Hyp125 D V₀ V)
    (hsmall : mSub V₀ ≤ 2)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    {p : ℕ} (hpK : p = Nat.card K - 1) (hpσ : p ∈ D.sig)
    (H : Subgroup (MulAut (Vtil V₀ V h125.isElemAbelian)))
    (hHn : Mbar D.M V₀ V h125.isElemAbelian ≤
      normalizer (H : Set (MulAut (Vtil V₀ V h125.isElemAbelian))))
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H)) :
    Mbar D.M V₀ V h125.isElemAbelian ⊓
      centralizer (H : Set (MulAut (Vtil V₀ V h125.isElemAbelian))) ≠ ⊥ := by
  classical
  have hcardV₀ : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub (Hyp125.pairFacts h125).elemAbelian₀.isPGroup
  have hcard4 : Nat.card V₀ ≤ 4 := by
    rw [hcardV₀]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hsmall
      _ = 4 := by norm_num
  have hpA : 2 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V h125.isElemAbelian) :=
    S17.two_le_pRank_mbar_of_mem_sig h125 hx h61 h127 hcard4 hpσ
  exact sl2_centralizer_ne_bot_of_natural
    (W := Vtil V₀ V h125.isElemAbelian)
    (A := Mbar D.M V₀ V h125.isElemAbelian) (H := H)
    (U := ⊤) (Z := fixV H) (K := K) (p := p)
    hK hpK hHn hreal hpA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
