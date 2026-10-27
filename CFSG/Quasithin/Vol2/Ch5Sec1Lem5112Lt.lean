module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Ctx
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.Quasithin.Vol2.Ch1Eight

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Lemma128TwoAS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → ∀ S L K : Subgroup G, quasithinIsLocal S L →
      quasithinIsLocal S K → L ≤ K → L < conjClosure L S →
        L = K ∨ (IsAlt 5 (ModO2 L) ∧ (IsSporadic .J1 (ModO2 K) ∨
          ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
            IsPSL 2 p 1 (ModO2 K)))

theorem Lemma128TwoAS.toLemma128Two (h : Lemma128TwoAS) : Lemma128Two := by
  intro G _ _ hQ hs hnab S L K hL hK hLK hLS
  rcases h G hQ hs hnab S L K hL hK hLK hLS with h1 | ⟨hA, hJ | ⟨p, hp, h5, -, hp1⟩⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hA, Or.inl hJ⟩
  · exact Or.inr ⟨hA, Or.inr ⟨p, hp, h5, hp1⟩⟩

variable {G : Type} [Group G] [Finite G]

namespace Emb512

variable {T M L H B D K₁ X Kh₁ : Subgroup G} {n k : ℕ}
  (e : Emb512 G T M L H B D K₁ X Kh₁ n k)
include e

theorem concl_of_lt (h128 : Lemma128TwoAS)
    (hlt : K₁ < oTwoUpper H) :
    K₁ < oTwoUpper H ∧ LieModel (O2Q K₁) .PSL 2 2 2 ∧
      (IsSporadic .J1 (O2Q Kh₁) ∨
        ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
          IsPSL 2 p 1 (O2Q Kh₁)) := by
  have h := e.hyp.toHyp5_0_1
  have hcc : K₁ < conjClosure K₁ T := e.closure ▸ hlt
  rcases h128 G h.qtke h.simple h.nonabelian T K₁ Kh₁ e.isLocal₁ e.isLocalHat e.K₁_le_hat hcc
    with hEq | ⟨hA5, hK⟩
  · exfalso
    have h1 := e.lt
    rw [← hEq, ← e.closure] at h1
    exact lt_irrefl _ h1
  · exact ⟨hlt, Or.inl ⟨by decide,
      CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ hA5⟩, hK⟩

end Emb512

end CFSG.Quasithin.H13
