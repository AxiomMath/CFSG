module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HOneLine
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

structure OLCfg {X : Type} [Group X] [Finite X] (P L Q : Subgroup X) : Prop where
  perf : Group.IsPerfect X
  triple : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON
  e27 : Late.IsE27 P
  normL : P ≤ Subgroup.normalizer (L : Set X)
  perfL : Group.IsPerfect L
  qsL : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L)
  thetaL : aschbacherSolvableCore 3 ↥L = ⊥
  cent : ∀ x ∈ P, (∀ l ∈ L, x * l = l * x) → x ∈ Subgroup.center X
  klein : IsKleinFour Q
  normQ : P ≤ Subgroup.normalizer (Q : Set X)
  pt : ∃ p ∈ P, p ∉ Subgroup.center X ∧ Q ≤ Subgroup.centralizer ({p} : Set X)
  QnormL : Q ≤ Subgroup.normalizer (L : Set X)
  Qnc : ¬ Q ≤ Subgroup.centralizer (L : Set X)
  inv : ∀ R : Subgroup X, R ≤ L ⊔ Q → R ∈ invariantPiSubgroups ⊤ P (piCompl 3) → R ≤ Q

@[expose] def OLRow (Φ : (T : Type) → [Group T] → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P L Q : Subgroup X), OLCfg P L Q → Φ ↥L → False

structure OLRows : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    OLRow (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField p e)))
  two_eps : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    OLRow (fun T _ => IsSLThreeEpsAt T (p ^ e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    OLRow (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField p e)))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    OLRow (fun T _ => Nonempty (T ≃* projSU 3 p e))
  three_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    OLRow (fun T _ => Blueprint.ChevalleyExceptionalModel T .G2 p 1)
  three_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    OLRow (fun T _ => Nonempty (T ≃* projSp 2 (GaloisField p 1)))
  three_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    OLRow (fun T _ => Nonempty (T ≃* projSU 4 p 1))
  three_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 →
    OLRow (fun T _ => Nonempty (T ≃* projSL 4 (GaloisField p 1)))
  four_alt : ∀ n : ℕ, n ≤ 9 → OLRow (fun T _ => Nonempty (T ≃* alternatingGroup (Fin n)))
  four_A6 : OLRow (fun T _ => IsExtOf T (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)))
  four_A7 : OLRow (fun T _ => IsExtOf T (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3)))
  five_spor : ∀ s ∈ sporadics46,
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier s))
  five_cover : ∀ s ∈ sporadicCovers46,
    OLRow (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3)))
  six_model : OLRow (fun T _ => IsChevTwoRankTwoModel T)
  six_SL3 : ∀ n : ℕ, 1 ≤ n → OLRow (fun T _ => IsSLThreeEpsAt T (2 ^ n))
  seven_SL52 : OLRow (fun T _ => Nonempty (T ≃* projSL 5 (GaloisField 2 1)))
  seven_Sp62 : OLRow (fun T _ => Nonempty (T ≃* projSp 3 (GaloisField 2 1)))
  seven_SU54 : OLRow (fun T _ => Nonempty (T ≃* projSU 5 2 2))
  eight_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 2 →
    OLRow (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField 3 e)))
  eight_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 2 → OLRow (fun T _ => Nonempty (T ≃* projSU 3 3 e))
  eight_SL43 : OLRow (fun T _ => Nonempty (T ≃* projSL 4 (GaloisField 3 1)))
  eight_cover : OLRow (fun T _ => Nat.card (Subgroup.center T) ≤ 3 ∧
    (Blueprint.ChevalleyExceptionalModel (T ⧸ Subgroup.center T) .G2 3 1 ∨
      Nonempty (T ⧸ Subgroup.center T ≃* projSU 4 3 1)))

noncomputable def equivThetaQuotOfBot {T : Type} [Group T] (h : aschbacherSolvableCore 3 T = ⊥) :
    T ⧸ aschbacherSolvableCore 3 T ≃* T :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem kf148OneLineComp_of_rows (h : OLRows) : KF148OneLineComp := by
  intro X _ _ hperf hT hKX P L Q hP hPL hLp hLq hθL hcent hK4 hPQ hpt hQL hQnc hall
  have hcfg : OLCfg P L Q :=
    ⟨hperf, hT, hP, hPL, hLp, hLq, hθL, hcent, hK4, hPQ, hpt, hQL, hQnc, hall⟩
  have hlist : IsList46 ↥L :=
    Sec21.Item223PrintProof.isList46_of_mulEquiv (equivThetaQuotOfBot hθL) (hKX L hLp hLq)
  rcases hlist with ⟨p, e, hp, hp2, he, hL⟩ | ⟨p, e, hp, hp3, he1, he2, hL | hL | hL⟩ |
      ⟨p, hp, hp3, hL | hL | ⟨hp1, hL⟩ | ⟨hp2, hL⟩⟩ | (⟨n, hn, hL⟩ | hL | hL) |
      (⟨s, hs, hL⟩ | ⟨s, hs, hL⟩) | (hL | ⟨n, hn, hL⟩) | (hL | hL | hL) |
      (⟨e, he1, he2, hL | hL⟩ | hL | hL)
  · exact h.one p e hp2 he X P L Q hcfg hL
  · exact h.two_eps p e hp3 he1 he2 X P L Q hcfg hL
  · exact h.two_SL p e hp3 he1 he2 X P L Q hcfg hL
  · exact h.two_SU p e hp3 he1 he2 X P L Q hcfg hL
  · exact h.three_G2 p hp3 X P L Q hcfg hL
  · exact h.three_Sp p hp3 X P L Q hcfg hL
  · exact h.three_SU p hp3 hp1 X P L Q hcfg hL
  · exact h.three_SL p hp3 hp2 X P L Q hcfg hL
  · exact h.four_alt n hn X P L Q hcfg hL
  · exact h.four_A6 X P L Q hcfg hL
  · exact h.four_A7 X P L Q hcfg hL
  · exact h.five_spor s hs X P L Q hcfg hL
  · exact h.five_cover s hs X P L Q hcfg hL
  · exact h.six_model X P L Q hcfg hL
  · exact h.six_SL3 n hn X P L Q hcfg hL
  · exact h.seven_SL52 X P L Q hcfg hL
  · exact h.seven_Sp62 X P L Q hcfg hL
  · exact h.seven_SU54 X P L Q hcfg hL
  · exact h.eight_SL3 e he1 he2 X P L Q hcfg hL
  · exact h.eight_SU3 e he1 he2 X P L Q hcfg hL
  · exact h.eight_SL43 X P L Q hcfg hL
  · exact h.eight_cover X P L Q hcfg hL

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
