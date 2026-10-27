module

public import CFSG.RankThree.PartOne.K1320.U

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def Row6Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f →
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
      s' ∈ torusImage E L → orderOf (s * s') = 4 →
      ((kExceptional p (kZero p E s) f ∧ KFAt p E (2 * f) s') ∨
        (KFAt p E (2 * f) s ∧ kExceptional p (kZero p E s') f))

@[expose] def Row6Lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f →
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → kExceptional p (kZero p E s) f →
      PAIR22.PairLift p E s

@[expose] def KF1320U5' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → RowModel p L 6 → ¬ IsLThreeTypeAt p L →
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
    ∀ t₁ t₂ t₃ : MulAut E, Chain3 p E L t₁ t₂ t₃ → False

theorem kf1320U5'_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two) (hdist : RowModelsDistinct)
    (hRow6 : Row6Data) (hLift6 : Row6Lift) (hThree : KF1320UThreeAt 5) : KF1320U5' := by
  intro G _ _ p A c L E h hF hF13 hT hEA hrow hnL3 hweyl t₁ t₂ t₃ hch
  have hweyl' := hweyl
  obtain ⟨eX⟩ := hweyl
  obtain ⟨f, hf1, hpf, hmodel⟩ := hrow
  have hp := h.prime
  obtain ⟨z, hz⟩ := exists_inverter h hF13 eX
  have hn8 : ¬ RowModel p L 8 := fun ⟨_, _, _, h4⟩ => not_row8_of_psu hdist (Or.inr rfl) hmodel h4
  obtain ⟨w, hw, hs₁, hs₁L, hs₂, hs₂L, hord⟩ := chain_conj_into_L hp hch
  rcases hRow6 G p A c L E f h hF hF13 hT hEA hf1 hpf hmodel _ hs₁ hs₁L _ hs₂ hs₂L hord with
    ⟨-, hA₂⟩ | ⟨-, hEx⟩
  ·
    have hK₂ : KFAt p E (2 * f) t₂ := KFAt.of_conj hw hA₂
    exact hThree G p A c L E f h hF hF13 hT hf1 hpf hmodel hEA hnL3 hweyl' t₁ t₂ t₃
      hch (kZero p E t₂) (kfKt_of_kfAt hK₂).1 hK₂.2.1
  ·
    have hL₂ : PAIR22.PairLift p E t₂ :=
      PAIR22.PairLift.of_conj hw (hLift6 G p A c L E f h hF hF13 hT hEA hf1 hpf hmodel _ hs₂ hs₂L hEx)
    obtain ⟨w₃, hw₃, ht₃⟩ := chain_t₃_conj hch
    have hL₃ : PAIR22.PairLift p E t₃ := by rw [ht₃]; exact hL₂.conj hw₃
    have hEx' : kExceptional p (kZero p E t₂) f := by
      rw [kZero_conj p t₂ hw] at hEx
      exact (Equivariance.kExceptional_conjBy_iff p f w (kZero p E t₂)).1 hEx
    obtain ⟨f', hK2, -, -⟩ := chain_pair_data hGA hS h133 h hF hF13 hT hEA hn8 hz hch hL₂ hL₃
    exact hK2.1 ⟨f, hEx'⟩

end CFSG.RankThree.PartOne.K1320
