module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.LRed5Pair
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple

variable {V : Type} [CommGroup V] [Finite V]

theorem b56_of_pairData (h56 : AsB56) (hV : ∀ v : V, v * v = 1)
    {Γ L₁ L₂ : Subgroup (MulAut V)} {t : MulAut V} (P : LRed5.PairData Γ L₁ L₂ t) :
    ffJ Γ = L₁ ⊔ L₂ ∧
      ((∃ W₁ W₂ : Subgroup V, fixV (ffJ Γ) ≤ W₁ ∧ fixV (ffJ Γ) ≤ W₂ ∧
          XMod.IsInv ↥(ffJ Γ) W₁ ∧ XMod.IsInv ↥(ffJ Γ) W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧
          W₁ ⊓ W₂ = fixV (ffJ Γ) ∧ B56Piece L₁ W₁ (fixV (ffJ Γ)) ∧
          B56Piece L₂ W₂ (fixV (ffJ Γ))) ∨
        ∃ G₁ G₂ : Subgroup (MulAut V), (G₁ = L₁ ∧ G₂ = L₂ ∨ G₁ = L₂ ∧ G₂ = L₁) ∧
          Nonempty (↥G₁ ≃* ↥(StatedSL 3 (ZMod 2))) ∧
          IsIntDirect (commV G₁) (commV G₂) (commV (ffJ Γ)) ∧ Nat.card ↥(commV G₁) = 2 ^ 3 ∧
          (commV (ffJ Γ) ⊔ fixV (ffJ Γ)).index = 2 ∧
          ∃ k : ℕ, k ≤ 2 ∧
            DirectSumOfCopies G₂ (commV G₂) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k) := by
  obtain ⟨A, hA⟩ := P.off
  have hJ : ffJ Γ ≠ ⊥ := fun h => hA.2.1 (le_bot_iff.mp (h ▸ B19.le_ffJ hA))
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [sq]; exact hV v
  have hLJ := LRed5.pair_le_ffJ P hJ
  have hL₁J : L₁ ≤ ffJ Γ := le_sup_left.trans hLJ
  rcases h56 V hV2 (ffJ Γ) hJ (LRed5.pair_b53 P) with ⟨hqF, -, -⟩ | h2 | h3 | h4 | h5
  · exact absurd hqF (fun hq => LRed5.pair_case1_false P hJ hq)
  · exact absurd h2 (fun h => FFL.false_of_case2 hL₁J (by rw [P.c₁]; norm_num) h)
  ·
    obtain ⟨G₁, G₂, hsup, hinf, hcomm, hf₁, hf₂, W₁, W₂, hW₁, hW₂, hinv₁, hinv₂, hWsup, hWinf,
      hp₁, hp₂⟩ := h3
    obtain ⟨hsplit, α, β, hα, hβ⟩ := LRed5.pair_split P hJ hsup hcomm hinf
      (FFL.ne_bot_of_factorList hf₁) (FFL.ne_bot_of_factorList hf₂)
    have h₁ := LRed5.factor_card_168 hf₁ hα
    have h₂ := LRed5.factor_card_168 hf₂ hβ
    rcases hsplit with ⟨a, b⟩ | ⟨a, b⟩
    · have e₁ : L₁ = G₁ := Subgroup.eq_of_le_of_card_ge a (by rw [h₁, P.c₁])
      have e₂ : L₂ = G₂ := Subgroup.eq_of_le_of_card_ge b (by rw [h₂, P.c₂])
      subst e₁ e₂
      exact ⟨hsup.symm, Or.inl ⟨W₁, W₂, hW₁, hW₂, hinv₁, hinv₂, hWsup, hWinf, hp₁, hp₂⟩⟩
    · have e₁ : L₁ = G₂ := Subgroup.eq_of_le_of_card_ge a (by rw [h₂, P.c₁])
      have e₂ : L₂ = G₁ := Subgroup.eq_of_le_of_card_ge b (by rw [h₁, P.c₂])
      subst e₁ e₂
      refine ⟨hsup.symm.trans (sup_comm _ _), Or.inl ⟨W₂, W₁, hW₂, hW₁, hinv₂, hinv₁, ?_, ?_,
        hp₂, hp₁⟩⟩
      · rw [sup_comm]; exact hWsup
      · rw [inf_comm]; exact hWinf
  · exact absurd h4 (fun h => LRed5.pair_case4_false P hJ h)
  ·
    obtain ⟨G₁, G₂, hsup, hinf, hcomm, hdir, ⟨e₁⟩, hc8, hidx, h₂⟩ := h5
    have hne₁ : G₁ ≠ ⊥ := by
      have := FFL.nontrivial_statedSL (n := 3) (by norm_num) (ZMod 2)
      exact FFL.ne_bot_of_mulEquiv e₁
    have hne₂ : G₂ ≠ ⊥ := by
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, K, _, _, -, π, hπ⟩
      · have := FFL.nontrivial_statedSL (n := 3) (by norm_num) (ZMod 2)
        exact FFL.ne_bot_of_mulEquiv e₂
      · have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
        have := FFL.nontrivial_statedSL le_rfl K
        intro hb
        subst hb
        obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥(StatedSL 2 K)
        exact hxy (hinj (Subsingleton.elim _ _))
    obtain ⟨hsplit, α, β, hα, hβ⟩ := LRed5.pair_split P hJ hsup hcomm hinf hne₁ hne₂
    have c₁ : Nat.card ↥G₁ = 168 := by
      rw [Nat.card_congr e₁.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
      norm_num
    have c₂ : Nat.card ↥G₂ = 168 := by
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, K, _, _, hK, π, hπ⟩
      · rw [Nat.card_congr e₂.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
        norm_num
      · exfalso
        have h1 := card_eq_of_nat_realizes1527d hπ
        rw [card_statedSL_two1527d, hK, hβ] at h1
        exact LRed5.sl2_ne_168_two_pow (FFL.one_le_of_card hK) h1.symm
    have hDS : ∃ k, k ≤ 2 ∧
        DirectSumOfCopies G₂ (commV G₂) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k := by
      rcases h₂ with ⟨-, k, hk, hD⟩ | ⟨n, K, _, _, hK, π, hπ⟩
      · exact ⟨k, hk, hD⟩
      · exfalso
        have h1 := card_eq_of_nat_realizes1527d hπ
        rw [card_statedSL_two1527d, hK, hβ] at h1
        exact LRed5.sl2_ne_168_two_pow (FFL.one_le_of_card hK) h1.symm
    rcases hsplit with ⟨a, b⟩ | ⟨a, b⟩
    · have e₁' : L₁ = G₁ := Subgroup.eq_of_le_of_card_ge a (by rw [c₁, P.c₁])
      have e₂' : L₂ = G₂ := Subgroup.eq_of_le_of_card_ge b (by rw [c₂, P.c₂])
      exact ⟨hsup.symm.trans (by rw [e₁', e₂']), Or.inr ⟨G₁, G₂, Or.inl ⟨e₁'.symm, e₂'.symm⟩,
        ⟨e₁⟩, hdir, hc8, hidx, hDS⟩⟩
    · have e₁' : L₁ = G₂ := Subgroup.eq_of_le_of_card_ge a (by rw [c₂, P.c₁])
      have e₂' : L₂ = G₁ := Subgroup.eq_of_le_of_card_ge b (by rw [c₁, P.c₂])
      exact ⟨hsup.symm.trans (by rw [e₁', e₂', sup_comm]), Or.inr ⟨G₁, G₂,
        Or.inr ⟨e₂'.symm, e₁'.symm⟩, ⟨e₁⟩, hdir, hc8, hidx, hDS⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
