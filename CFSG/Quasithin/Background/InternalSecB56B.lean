module

public import CFSG.Quasithin.Background.InternalSecB56M
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecB56

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def NotB56Factor {V : Type} [CommGroup V] (K : Subgroup (MulAut V)) : Prop :=
  ∀ X : Subgroup (MulAut V), K ≤ X → X ≤ Subgroup.normalizer (K : Set (MulAut V)) →
    ¬ (B56FactorList ↥X ∨ Nonempty (↥X ≃* ↥(alternatingGroup (Fin 6))) ∨
      Nonempty (↥X ≃* ↥(StatedSL 3 (ZMod 2))) ∨
      ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        ∃ π : ↥(StatedSL 2 F) →* ↥X, Function.Surjective π)

section B56

variable {V : Type} [CommGroup V] [Finite V]

theorem quasithinGenFitting_eq_of_b56Cases_of_commV {J K : Subgroup (MulAut V)} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hcomm : commV K = ⊤)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    quasithinGenFitting J = K := by
  have htop : ∀ {X : Subgroup (MulAut V)}, K ≤ X → commV X = ⊤ := fun h =>
    top_le_iff.1 (by rw [← hcomm]; exact commV_le_commV h)
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, -, W₁, W₂, -, -, -, -, -, hWinf, hp₁, hp₂⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, -, hc₂, -, -, ⟨-, hV12⟩, -, hcV₂, ht₁, ht₂, -⟩ |
      ⟨_, _, -, -, -, -, -, -, hidx, -⟩
  · exact eq_of_le_quasisimple hKJ hn hK h1.1
  · exact (not_le_perm_three hK hKJ e).elim
  ·
    exfalso
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · have hW₁ : W₁ = ⊤ := top_le_iff.1 ((htop h).symm.le.trans (commV_le_of_b56Piece hp₁))
      rw [hW₁, top_inf_eq] at hWinf
      rw [hWinf] at hp₂
      exact not_b56Piece_self hp₂
    · have hW₂ : W₂ = ⊤ := top_le_iff.1 ((htop h).symm.le.trans (commV_le_of_b56Piece hp₂))
      rw [hW₂, inf_top_eq] at hWinf
      rw [hWinf] at hp₁
      exact not_b56Piece_self hp₁
  ·
    exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hK with h | h
    · rw [htop h, top_inf_eq] at hV12
      rw [hV12, Subgroup.card_bot] at hcV₂
      norm_num at hcV₂
    · exact not_le_of_card_prime hK h hc₂
  ·
    exfalso
    rw [htop hKJ, top_sup_eq, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

theorem quasithinGenFitting_eq_of_b56Cases {J K : Subgroup (MulAut V)} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hfac : NotB56Factor K)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    quasithinGenFitting J = K := by
  have hJn : J ≤ Subgroup.normalizer (K : Set (MulAut V)) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hn x hx k hk, fun hk => by
        have := hn x⁻¹ (J.inv_mem hx) _ hk
        simpa [mul_assoc] using this⟩
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, -, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, h₂⟩
  · exact eq_of_le_quasisimple hKJ hn hK h1.1
  · exact (not_le_perm_three hK hKJ e).elim
  · exfalso
    have h₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
    have h₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · exact hfac G₁ h (h₁J.trans hJn) (Or.inl hf₁)
    · exact hfac G₂ h (h₂J.trans hJn) (Or.inl hf₂)
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h₁J : G₁ ≤ J := by rw [hJt]; exact le_sup_left.trans le_sup_left
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hK with h | h
    · exact hfac G₁ h (h₁J.trans hJn) (Or.inr (Or.inl ⟨e₁⟩))
    · exact not_le_of_card_prime hK h hc₂
  · exfalso
    have h₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
    have h₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · exact hfac G₁ h (h₁J.trans hJn) (Or.inr (Or.inr (Or.inl ⟨e₁⟩)))
    · refine hfac G₂ h (h₂J.trans hJn) ?_
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hcF, π, hR⟩
      · exact Or.inr (Or.inr (Or.inl ⟨e₂⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨n, F, inferInstance, inferInstance, hcF, π, hR.1⟩))

end B56

section Internal

variable {G : Type} [Group G] [Finite G] {W Y L : Subgroup G} [IsMulCommutative ↥W]

theorem b56Cases_ffJ_autOn (h56 : AsB56) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hLY : L ≤ Y)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hSY : SQTKGroup ↥Y)
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) {A : Subgroup (MulAut ↥W)}
    (hA : IsFFStarOffender (autOn Y W) A) (hLA : ⁅autOn L W, A⁆ = autOn L W) :
    autOn L W ≤ ffJ (autOn Y W) ∧
      (∀ x ∈ ffJ (autOn Y W), ∀ k ∈ autOn L W, x * k * x⁻¹ ∈ autOn L W) ∧
      pCoreOf 2 (ffJ (autOn Y W)) = ⊥ ∧ A ≤ ffJ (autOn Y W) ∧
      (B56Case1 (ffJ (autOn Y W)) ∨ B56Case2 (ffJ (autOn Y W)) ∨ B56Case3 (ffJ (autOn Y W)) ∨
        B56Case4 (ffJ (autOn Y W)) ∨ B56Case5 (ffJ (autOn Y W))) := by
  have hKX : autOn L W ≤ autOn Y W := autOn_le_autOn_of_le hLY
  have hKn := autOn_normal_of (U := W) hYL
  have hJX : ffJ (autOn Y W) ≤ autOn Y W := B6.ffJ_le _
  have hJn : ((ffJ (autOn Y W)).subgroupOf (autOn Y W)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (B6.le_normalizer_ffJ _)
  have hQ : pCoreOf 2 (ffJ (autOn Y W)) = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ hJX hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hV : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW2 v v.2)
  have hAJ : A ≤ ffJ (autOn Y W) := B6.le_ffJ hA
  have hJne : ffJ (autOn Y W) ≠ ⊥ := fun h => hA.2.1 (le_bot_iff.1 (h ▸ hAJ))
  exact ⟨B1Red.K_le_ffJ hKX hA hLA, fun x hx k hk => hKn x (hJX hx) k hk, hQ, hAJ,
    h56 ↥W hV _ hJne (b53Hyp_ffJ_autOn hYW hSY hO2)⟩

theorem b51Hyp_ffJ_autOn_of_b56 (h56 : AsB56) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hLY : L ≤ Y)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hSY : SQTKGroup ↥Y)
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) (hq : CFSG.IsQuasisimple ↥(autOn L W))
    (hS : SQTKGroup ↥(autOn L W)) {A : Subgroup (MulAut ↥W)}
    (hA : IsFFStarOffender (autOn Y W) A) (hLA : ⁅autOn L W, A⁆ = autOn L W)
    (hcomm : commV (autOn L W) = ⊤) :
    B51Hyp (ffJ (autOn Y W)) (autOn L W) ∧ A ≤ ffJ (autOn Y W) := by
  obtain ⟨hKJ, hn, hQ, hAJ, hcases⟩ := b56Cases_ffJ_autOn h56 hW2 hYW hLY hYL hSY hO2 hA hLA
  have hF := quasithinGenFitting_eq_of_b56Cases_of_commV hKJ hn hq hcomm hcases
  have hZ : centerOf (ffJ (autOn Y W)) ≤ autOn L W := hF ▸ centerOf_le_quasithinGenFitting _
  exact ⟨⟨by rw [hF, sup_eq_left.2 hZ], hq, hS, hKJ, hQ, (ffJ_ffJ _).symm⟩, hAJ⟩

theorem b51Hyp_ffJ_autOn_of_b56_of_commutator (h56 : AsB56) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hLY : L ≤ Y)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hSY : SQTKGroup ↥Y)
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) (hq : CFSG.IsQuasisimple ↥(autOn L W))
    (hS : SQTKGroup ↥(autOn L W)) {A : Subgroup (MulAut ↥W)}
    (hA : IsFFStarOffender (autOn Y W) A) (hLA : ⁅autOn L W, A⁆ = autOn L W)
    (hWL : ⁅W, L⁆ = W) :
    B51Hyp (ffJ (autOn Y W)) (autOn L W) ∧ A ≤ ffJ (autOn Y W) :=
  b51Hyp_ffJ_autOn_of_b56 h56 hW2 hYW hLY hYL hSY hO2 hq hS hA hLA
    (commV_autOn_eq_top (fun _ hl => hYW (hLY hl)) hWL)

theorem b51Hyp_ffJ_autOn_of_b56_of_notFactor (h56 : AsB56) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hLY : L ≤ Y)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hSY : SQTKGroup ↥Y)
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) (hq : CFSG.IsQuasisimple ↥(autOn L W))
    (hS : SQTKGroup ↥(autOn L W)) {A : Subgroup (MulAut ↥W)}
    (hA : IsFFStarOffender (autOn Y W) A) (hLA : ⁅autOn L W, A⁆ = autOn L W)
    (hfac : NotB56Factor (autOn L W)) :
    B51Hyp (ffJ (autOn Y W)) (autOn L W) ∧ A ≤ ffJ (autOn Y W) := by
  obtain ⟨hKJ, hn, hQ, hAJ, hcases⟩ := b56Cases_ffJ_autOn h56 hW2 hYW hLY hYL hSY hO2 hA hLA
  have hF := quasithinGenFitting_eq_of_b56Cases hKJ hn hq hfac hcases
  have hZ : centerOf (ffJ (autOn Y W)) ≤ autOn L W := hF ▸ centerOf_le_quasithinGenFitting _
  exact ⟨⟨by rw [hF, sup_eq_left.2 hZ], hq, hS, hKJ, hQ, (ffJ_ffJ _).symm⟩, hAJ⟩

end Internal

end CFSG.Quasithin.InternalSec
