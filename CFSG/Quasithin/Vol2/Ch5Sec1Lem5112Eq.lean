module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112A5
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112M23
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Loc

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch11.SecB (FactMathieuOrders)

variable {G : Type} [Group G] [Finite G]

namespace EmbLoc

variable {S X K Kh : Subgroup G} {k : ℕ} (l : EmbLoc G S X K Kh)
include l

theorem concl_bender
    (hM : FactMathieuOrders) (hF : A314Facts) (hNL : A314NotLie2)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK) (hk2 : 2 ≤ k)
    (hB : IsBenderCh5 k (O2Q K)) :
    (SuzukiModel (O2Q K) 2 k ∧ Is2F4 k (O2Q Kh)) ∨
      (LieModel (O2Q K) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Kh)) ∨
      (LieModel (O2Q K) .PSL 2 2 2 ∧ ¬ IsLieTypeChar2 (O2Q Kh) ∧
        A314Statement (o2Img X S) (o2Img X K) (o2Img X Kh)) := by
  rcases hB with hL2 | hSz | ⟨hq, hU⟩
  ·
    rcases Nat.lt_or_ge k 3 with hk | hk
    · obtain rfl : k = 2 := by omega
      rcases l.a5_cases hF hNL h36 h312 hL2 with h4 | ⟨h5, h314⟩
      · exact Or.inr (Or.inl ⟨hL2, h4⟩)
      · exact Or.inr (Or.inr ⟨hL2, h5, h314⟩)
    · exact Or.inr (Or.inl ⟨hL2, l.rank2_of_psl2 hP h36 h312 hk hL2⟩)
  ·
    exact Or.inl ⟨hSz, l.twoF4_of_suzuki hM h312 hSz⟩
  ·
    exact (l.false_of_unitary hM h312 hk2 hq hU).elim

theorem concl
    (hM : FactMathieuOrders) (hF : A314Facts) (hNL : A314NotLie2) (hM23 : FactM23L34)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK) (hk2 : 2 ≤ k)
    (hshape : IsBenderCh5 k (O2Q K) ∨
      ((IsSL3Ch5 k (O2Q K) ∨ LieModel (O2Q K) .PSp 2 2 k) ∧
        E2.IsDiagramNontrivial S K (S ⊓ K))) :
    (SuzukiModel (O2Q K) 2 k ∧ Is2F4 k (O2Q Kh)) ∨
      (LieModel (O2Q K) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Kh)) ∨
      (LieModel (O2Q K) .PSL 2 2 2 ∧ ¬ IsLieTypeChar2 (O2Q Kh) ∧
        A314Statement (o2Img X S) (o2Img X K) (o2Img X Kh)) := by
  rcases hshape with hB | ⟨hS, hD⟩
  · exact l.concl_bender hM hF hNL hP h36 h312 hk2 hB
  ·
    exfalso
    rcases hS with hSL | hSp
    · rcases Nat.lt_or_ge k 3 with hk | hk
      · obtain rfl : k = 2 := by omega
        exact l.false_of_l34 hM hM23 h312 hSL hD
      · rcases hSL with hL3 | ⟨F, _, _, hF, ⟨eF⟩⟩
        · exact l.false_of_psl3 hM h312 hk hL3
        · exact l.false_of_sl3 hM h312 hk hF eF
    · exact l.false_of_psp4 hM h312 hk2 hSp

end EmbLoc

namespace Emb512

variable {T M L H B D K₁ X Kh₁ : Subgroup G} {n k : ℕ}
  (e : Emb512 G T M L H B D K₁ X Kh₁ n k)
include e

theorem two_le_k : 2 ≤ k := e.field.1.1

theorem concl_of_eq
    (hM : FactMathieuOrders) (hF : A314Facts) (hNL : A314NotLie2) (hM23 : FactM23L34)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (heq : K₁ = oTwoUpper H) :
    (SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧
        IsRank2LieChar2 (O2Q (conjClosure Kh₁ T))) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ oTwoUpper H < conjClosure Kh₁ T ∧
        ¬ IsLieTypeChar2 (O2Q (conjClosure Kh₁ T)) ∧
        A314Statement (o2Img X T) (o2Img X (oTwoUpper H)) (o2Img X (conjClosure Kh₁ T))) := by
  have hk2 := e.two_le_k
  have hshape := e.shape heq
  have hlt := e.lt_hat_of_eq heq
  rw [e.conjClosure_hat_eq_of_eq heq, ← heq]
  rw [← heq] at hshape
  rcases (e.toLoc heq).concl hM hF hNL hM23 hP h36 h312 hk2 hshape with h3 | h4 | ⟨hL2, h5, h314⟩
  · exact Or.inl h3
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr ⟨hL2, hlt, h5, h314⟩)

end Emb512

theorem stmt5_1_12_loc_of
    (hM : FactMathieuOrders) (hF : A314Facts) (hNL : A314NotLie2)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK) :
    Stmt5_1_12_loc := by
  intro G _ _ hs hnab hQ S X K Kh k hk hOX hSX hKX hK hSK hhat hlt hB
  exact (⟨hs, hnab, hQ, hOX, hSX, hKX, hK, hSK, hhat, hlt⟩ : EmbLoc G S X K Kh).concl_bender hM hF
    hNL hP h36 h312 hk hB

end CFSG.Quasithin.H13
