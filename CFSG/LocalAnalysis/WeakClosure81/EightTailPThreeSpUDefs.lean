module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpULie
public import CFSG.LocalAnalysis.WeakClosure81.EightSixDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

structure RootData {G : Type} [Group G] (V H T : Subgroup G) (S : Type) [Group S]
    (ψ : ↥(kGenIn V H) →* S) (ρ : ↥H →* MulAut S) (R Sy : Subgroup S) (e : ℕ) : Prop where
  hyp : Hyp83 V H T
  eq_sup : H = kGenIn V H ⊔ T
  surj : Function.Surjective ψ
  ker : ∀ k : ↥(kGenIn V H), ψ k = 1 ↔ (k : G) ∈ centerPre (kGenIn V H) (eCentSet V H T)
  act : ∀ (h : ↥H) (k x : ↥(kGenIn V H)), (x : G) = h * k * h⁻¹ → ρ h (ψ k) = ψ x
  root : barSub (kGenIn V H) ψ V = R
  sylow : barSub (kGenIn V H) ψ T = Sy
  sylow_normalizes : (∃ P : Sylow 2 S, (P : Subgroup S) = Sy) ∧ R ≤ Sy ∧
    Sy ≤ Subgroup.normalizer (R : Set S)
  lie : RootLieFacts S R Sy e
  card_V : (Nat.card R) ^ e < Nat.card V

end CFSG.LocalAnalysis.WeakClosure81

end
