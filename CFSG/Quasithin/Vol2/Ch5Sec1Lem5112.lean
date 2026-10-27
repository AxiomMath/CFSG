module

public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_12_emb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D K₁ : Subgroup G) (n k : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsFieldParam510 T H k →
    quasithinIsCComponent K₁ H → oTwoUpper H = conjClosure K₁ T →
    ∀ X Kh₁ : Subgroup G, InH H X → IsHatComp X K₁ Kh₁ → oTwoUpper H < conjClosure Kh₁ T →
      (K₁ < oTwoUpper H ∧ LieModel (O2Q K₁) .PSL 2 2 2 ∧
          (IsSporadic .J1 (O2Q Kh₁) ∨
            ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
              IsPSL 2 p 1 (O2Q Kh₁))) ∨
        (SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
        (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧
          IsRank2LieChar2 (O2Q (conjClosure Kh₁ T))) ∨
        (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ oTwoUpper H < conjClosure Kh₁ T ∧
          ¬ IsLieTypeChar2 (O2Q (conjClosure Kh₁ T)) ∧
          A314Statement (o2Img X T) (o2Img X (oTwoUpper H)) (o2Img X (conjClosure Kh₁ T)))

theorem stmt5_1_12_of
    (h39 : Vol2Native.A39ForSQTKCat) (hemb : Stmt5_1_12_emb) :
    Stmt5_1_12 := by
  intro G _ _ T M L H B D K₁ n k hyp hN hk hK₁ hKeq X hX
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : T ≤ H := hyp.hStar.1.1
  have hK₁H : K₁ ≤ H := A3.subnormal_le hK₁.2.2.1
  have hK₁X : K₁ ≤ X := hK₁H.trans hX.1
  have hSX : IsSylowTwoOf T X := h.isSylowTwoOf (hTH.trans hX.1)
  have hK₁loc : K₁ ∈ lFamily T := cComp_mem_of_le hK₁ le_sup_left (sup_le hK₁H hTH)
  obtain ⟨Kh₁, ⟨hKh₁, hK₁Kh₁⟩, huniq⟩ :=
    Vol2Native.lemma_1_2_4_existsUnique hloc Vol2Native.a37ForSQTKCat_proved h39 hX.2 hSX hK₁X
      hK₁loc
  have hhat : IsHatComp X K₁ Kh₁ := ⟨hKh₁, hK₁Kh₁, fun Y hY hK₁Y => huniq Y ⟨hY, hK₁Y⟩⟩
  have hKle : oTwoUpper H ≤ conjClosure Kh₁ T := by
    rw [hKeq]
    exact conjClosure_mono hK₁Kh₁ le_rfl
  refine ⟨Kh₁, hhat, hKle, ?_⟩
  by_cases heq : oTwoUpper H = conjClosure Kh₁ T
  · exact Or.inl heq
  · exact Or.inr (hemb G T M L H B D K₁ n k hyp hN hk hK₁ hKeq X Kh₁ hX hhat
      (lt_of_le_of_ne hKle heq))

end CFSG.Quasithin.H13
