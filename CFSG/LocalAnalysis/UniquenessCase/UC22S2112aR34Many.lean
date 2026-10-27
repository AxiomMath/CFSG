module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.L2Over17

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (isL2Over17_of_mulEquiv)
open scoped Pointwise

theorem uc22s2112r34_exists_centralizing_two {X : Type} [Group X] {Δ : Set (Subgroup X)}
    (hΔ : 2 < Δ.ncard) (hc : ∀ K₁ ∈ Δ, ∀ K₂ ∈ Δ, K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥) {B : Subgroup X}
    (hB : B ≠ ⊥) (hs : ∀ K ∈ Δ, B = (B ⊓ K) ⊔ (B ⊓ centralizer (K : Set X))) :
    ∃ y ∈ B, y ≠ 1 ∧ ∃ K₂ ∈ Δ, ∃ K₃ ∈ Δ, K₂ ≠ K₃ ∧
      y ∈ centralizer (K₂ : Set X) ∧ y ∈ centralizer (K₃ : Set X) := by
  obtain ⟨K₁, K₂, K₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff (Set.finite_of_ncard_pos (by omega))).1 hΔ
  have hC : ∀ {K K' : Subgroup X}, K ∈ Δ → K' ∈ Δ → K ≠ K' → ∀ y ∈ K,
      y ∈ centralizer (K' : Set X) :=
    fun hK hK' hne _ hy => commutator_eq_bot_iff_le_centralizer.1 (hc _ hK _ hK' hne) hy
  have hle : ∀ {K : Subgroup X}, K ∈ Δ → B ⊓ K = ⊥ → ∀ y ∈ B, y ∈ centralizer (K : Set X) := by
    intro K hK hBK y hy
    have h := hs K hK
    rw [hBK, bot_sup_eq] at h
    exact (h.le hy).2
  by_cases hB1 : B ⊓ K₁ = ⊥
  · by_cases hB2 : B ⊓ K₂ = ⊥
    · obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
      exact ⟨y, hy, fun h => hy1 (Subtype.ext h), K₁, h₁, K₂, h₂, h12, hle h₁ hB1 y hy,
        hle h₂ hB2 y hy⟩
    · obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB2
      exact ⟨y, hy.1, fun h => hy1 (Subtype.ext h), K₁, h₁, K₃, h₃, h13, hle h₁ hB1 y hy.1,
        hC h₂ h₃ h23 y hy.2⟩
  · obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    exact ⟨y, hy.1, fun h => hy1 (Subtype.ext h), K₂, h₂, K₃, h₃, h23, hC h₁ h₂ h12 y hy.2,
      hC h₁ h₃ h13 y hy.2⟩


theorem uc22s2112r34_funCommute_of_simple (hKFun : PartTwo.Inputs1719.K_FunCommute) {X : Type}
    [Group X] [Finite X] [IsSimpleGroup X] (hnc : ∃ a b : X, a * b ≠ b * a) {t : StatedLieTag}
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : LieModel X t n p f) (hno : ∀ f : ℕ, ¬ LieModel X .PSL 2 p f)
    (h4 : 4 ≤ Open.pRank p (⊤ : Subgroup X)) (hree : ∀ f : ℕ, ¬ LieModel X .twistedG2 0 3 f)
    (hq : 3 < p ^ f) (P : Sylow 2 X) {K₁ K₂ : Subgroup X}
    (h₁ : K₁ ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X))
    (h₂ : K₂ ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X)) (hne : K₁ ≠ K₂) : ⁅K₁, K₂⁆ = ⊥ := by
  obtain ⟨a, b, hab⟩ := hnc
  have hZ : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · have hb : b ∈ center X := h ▸ mem_top b
      exact absurd (mem_center_iff.1 hb a) hab
  have hperf : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · rw [commutator_def, commutator_eq_bot_iff_le_centralizer] at h
      exact absurd (mem_centralizer_iff.1 (h (mem_top b)) a (mem_top a)) hab
    · exact h
  let e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine hKFun X p (p ^ f) hp hp2 ⟨t, n, f, hadm, rfl, LieModel.of_mulEquiv e.symm hX⟩
    ⟨hperf, e.isSimpleGroup⟩ (by rw [hZ, Subgroup.card_bot]; exact odd_one) ?_ ?_
    (uc22s2112r34_not_isReeOver17 hree) hq P K₁ h₁ K₂ h₂ hne
  · exact fun h => uc22s2112r34_not_isL2Over17 hp hno (isL2Over17_of_mulEquiv e.symm h)
  · rintro (h | h)
    · exact uc22s2112r34_not_isL3EpsOdd17 hp h4 (Or.inl (LieModel.of_mulEquiv e h))
    · exact uc22s2112r34_not_isL3EpsOdd17 hp h4 (Or.inr (LieModel.of_mulEquiv e h))

theorem uc22s2112r34_exists_fixed_pair (hKFun : PartTwo.Inputs1719.K_FunCommute)
    (hKc : KFunCount) (hKS : KFunSplit) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f) (ht : FunManyType t n)
    (hX : LieModel X t n p f) (hno : ∀ f : ℕ, ¬ LieModel X .PSL 2 p f)
    (h4 : 4 ≤ Open.pRank p (⊤ : Subgroup X)) (hree : ∀ f : ℕ, ¬ LieModel X .twistedG2 0 3 f)
    (hq : 3 < p ^ f) (P : Sylow 2 X) {B : Subgroup X} (hB : B ≠ ⊥) (hBc : IsMulCommutative B)
    (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B) (hBp : ¬ p ∣ Nat.card B)
    (hBP : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (hrk : ∀ s : ℕ, s.Prime → s ∣ Nat.card B → pRank s B ≤ 2 ∧ pRank s (⊤ : Subgroup X) ≤ 3) :
    ∃ y ∈ B, y ≠ 1 ∧ ∃ K₂ K₃ : Subgroup X, IsFundamentalOver (p ^ f) K₂ ∧
      IsFundamentalOver (p ^ f) K₃ ∧ ⁅K₂, K₃⁆ = ⊥ ∧
      K₂ ⊔ K₃ ≤ signalizerFixedSubgroup (MulAut.conj y) := by
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    simp [FunManyType] at ht
  have hRee : t ≠ .twistedG2 := by
    rintro rfl
    simp [FunManyType] at ht
  have hcomm : ∀ K₁ ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      ∀ K₂ ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ :=
    fun _ h₁ _ h₂ hne =>
      uc22s2112r34_funCommute_of_simple hKFun hnc hp hp2 hadm hX hno h4 hree hq P h₁ h₂ hne
  have h3 := (hKc X t n p f hp hp2 hadm hX P).2 ht
  obtain ⟨y, hyB, hy1, K₂, hK₂, K₃, hK₃, hne, hy₂, hy₃⟩ :=
    uc22s2112r34_exists_centralizing_two (by omega) hcomm hB
      fun K hK => hKS X t n p f hp hp2 hadm hX hA1 hRee P B hB hBc hBo hB3 hBp hBP hrk K hK
  have hfix : ∀ K : Subgroup X, y ∈ centralizer (K : Set X) →
      K ≤ signalizerFixedSubgroup (MulAut.conj y) := by
    intro K hy k hk
    show MulAut.conj y k = k
    rw [MulAut.conj_apply, ← mem_centralizer_iff.1 hy k hk, mul_inv_cancel_right]
  exact ⟨y, hyB, hy1, K₂, K₃, hK₂.1, hK₃.1, hcomm K₂ hK₂ K₃ hK₃ hne,
    sup_le (hfix K₂ hy₂) (hfix K₃ hy₃)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
