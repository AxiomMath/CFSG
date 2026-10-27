module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Irr
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Top
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_3_low : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V I : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    ∀ hV : IsCh5Module T L V, thompsonJ T ≤ Subgroup.centralizer (V : Set G) →
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    qhatInt (L ⊔ T) V hV.isTwoReducedIn.2.2.1 ≤ 2 →
    IsIrrPlusIn L V T I → T ≤ Subgroup.normalizer (I : Set G) → I ≠ ⁅V, L⁆ →
      IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∨
      (n = 2 ∧ IsBarS5 L T V ∧ IsSumOfTwo (L ⊔ T) V (IsS5ModCh5 L T))

theorem stmt5_1_3_qhat_of
    (hD : D310L2Fact) (hF : Vol2.Ch10.SecA.Facts10_1) (h45 : AsB45)
    (h16 : ASInputs.AS_I_1_6) (hlow : Stmt5_1_3_low) : Stmt5_1_3_qhat := by
  intro G _ _ T M L V n h hV hJ hC hq
  obtain ⟨I, hI, hTI⟩ := h.exists_irrPlusIn_le_normalizer hD hV hC hq
  by_cases hIU : I = ⁅V, L⁆
  · have hbase : IsIrrPlusBase L V ⁅V, L⁆ := by
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hI
      rw [← hIU]
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    rcases h.lemma_5_1_3_top hF h45 h16 hV hC hq hbase with h3 | h4
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h4))
  · rcases hlow G T M L V I n h hV hJ hC hq hI hTI hIU with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)

end CFSG.Quasithin.H13
