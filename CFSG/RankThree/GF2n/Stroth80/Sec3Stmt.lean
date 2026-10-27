module

public import CFSG.RankThree.GF2n.Stroth80.Sec36

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth34Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B → Conc34 M Q Z B

theorem stroth_3_5 (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    (∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) →
        conjSubgroup m (LB M Q B) = LB M Q B) ∧
    CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) ∧
    Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) ∧
    Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
  stroth_3_5_of_3_4 hc hw hn hno fun m hm =>
    h34 G M Q Z (conjSubgroup m B) (hc.conj_of_mem hm) n hw hn (hc.noA2_conj hno hm)
      (hgen.conj_of_mem hm)

theorem stroth_3_6 (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {h : G} (hh : h ∈ M)
    (hne : conjSubgroup h (LB M Q B) ⊓ Subgroup.normalizer (LB M Q B : Set G) ≠ Q) :
    ∀ b ∈ B, ∀ c ∈ conjSubgroup h B, b * c = c * b :=
  stroth_3_6_of_3_5 hc (hc.CQt_eq_of_3_4 hw hn hno (h34 G M Q Z B hc n hw hn hno hgen)) hh hne

@[expose] def Stroth37Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    IsTIMod M Q (LB M Q B) →
    n = 4 ∧ bar M Q (Lgen M (LB M Q B)) = layer (Mbar M Q) ∧
      IsSLModel 2 (Nat.card Z ^ 3) ↥(layer (Mbar M Q))

@[expose] def Stroth310Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q →
    Rt M (LB M Q B) t = LB M Q B ∨
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
      ((∃ m : ℕ, 2 ≤ m ∧ NaturalRep (ι := Fin m) K (StatedSL m K) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ NaturalRep (ι := Fin m ⊕ Fin m) K (StatedSp m K)
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) ∨
        (∃ m : ℕ, 2 ≤ m ∧ NaturalRep (ι := Fin m ⊕ Fin m) K
          (StatedOmega (StatedQuadPlus m K)) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
          (hc.CN t)) ∨
        (∃ (m : ℕ) (b c : K), 2 ≤ m ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
          NaturalRep (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K
            (StatedOmega (StatedQuadMinus m K b c)) (Rt M (LB M Q B) t)
            (Vt M (LB M Q B) B Z t) Z (hc.CN t)))

end CFSG.RankThree.GF2n.Stroth80
