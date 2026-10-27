module

public import CFSG.Quasithin.Recognition.St84.Gen.IdL2L2GenGlue
public import CFSG.Quasithin.Recognition.St84.Gen.TransportL3q

import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.Sec5Mixed
import CFSG.Quasithin.Recognition.St84.Gen.Sec7Gen

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
open CFSG.Quasithin.Stroth

@[expose] def St84LLOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (m n s : ℕ),
    F112HypW L1 L2 S → 2 ≤ m → 2 ≤ n → ¬ (m = 2 ∧ n = 2) →
      IsL2Quot m (oTwoQuot ↥L1) → IsL2Quot n (oTwoQuot ↥L2) →
        IsSingularity (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) s → Odd s → 5 ≤ s →
          (∀ Y : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
            Odd (Nat.card Y.GT)) →
            (m = n ∧ (L3qLocalData L1 L2 S n ∨ Sp4qLocalData L1 L2 S n ∨
                G2qLocalData L1 L2 S n ∨ G2qLocalData L2 L1 S n)) ∨
              (m = 3 * n ∧ D4qLocalData L1 L2 S n) ∨ (n = 3 * m ∧ D4qLocalData L2 L1 S m) ∨
              (n = 2 * m ∧ U4qLocalData L1 L2 S m) ∨ (m = 2 * n ∧ U4qLocalData L2 L1 S n)

theorem two_le_nOf_f112 {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    {m n : ℕ} (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (v : Fan86.Univ.Vtx (f112Gold L1 L2 S)) :
    2 ≤ nOf (f112Gold L1 L2 S).treeGraph v := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨g, rfl⟩ | ⟨g, rfl⟩ := Fan86.Univ.exists_smul_base (f112Gold L1 L2 S) v
  · rw [f112_nOf_alpha_of_isL2Quot hR (by omega) h1 g]
    exact hm
  · rw [f112_nOf_beta_of_isL2Quot hR (by omega) h2 g]
    exact hn

theorem st84LLLocal_of_odd (hodd : St84LLOdd) : St84LLLocal := by
  intro G _ _ L1 L2 S m n hF hm hn hmn h1 h2
  have h30 := f112ll_hyp30 hF hm hn h1 h2
  have hc := f112ll_charTwoStab hF hm hn h1 h2
  obtain ⟨s, -, hs, -⟩ := h30.exists_singular_setup
  have h3 : 3 ≤ s := three_le_of_isSingularity h30 hc hs
  have hne3 : s ≠ 3 := singularity_ne_three_gen h30 hc hs
  rcases Nat.even_or_odd s with hev | hodd'
  · obtain ⟨hmn', hL3⟩ := f112ll_l3qLocalData_of_even_singularity hF hm hn h1 h2 hs hev
    exact Or.inl ⟨hmn', Or.inl hL3⟩
  · have h5 : 5 ≤ s := by
      obtain ⟨k, rfl⟩ := hodd'
      omega
    exact hodd G L1 L2 S m n s hF hm hn hmn h1 h2 hs hodd' h5 fun Y =>
      Setup.odd_card_GT hc Y (Or.inl (two_le_nOf_f112 hF hm hn h1 h2 (Y.vert 0))) hs hodd' h5

end CFSG.Quasithin.F112R.St84

end
