module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res3ProofSLTwoU

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

structure Cfg (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G) :
    Prop where
  hD : Sec13Data G A c L
  hSL : Sec4.IsSLThreePiTwo (lBarA c L A)
  hSU : ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
    2 ^ f % 3 = 2 ∧
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K)
  hEle : E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G)
  hEe : CFSG.Assembly.IsElemAbelian 3 E
  hE27 : Nat.card E = 27
  hEC : ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G)
  hEL : ¬ IsCyclic (E ⊓ L : Subgroup G)
  hodd : ∀ x ∈ E, x ≠ 1 → Odd (Nat.card
    (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G))))

@[expose] def List463 {G : Type} [Group G] [Finite G] (Y : Subgroup G) : Prop :=
  haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  Nonempty (Y ⧸ solvableRadical Y ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
    Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
    Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
    (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
      Sec4.IsoLThreePi (Y ⧸ solvableRadical Y) p e) ∨
    Nonempty (Y ⧸ solvableRadical Y ≃* projSL 2 (GaloisField 3 3))

structure YCfg (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (E F : Subgroup G) (a b : G) (R Y : Subgroup G) : Prop where
  hCfg : Cfg G A c L E
  hE : E ∉ partTwoE G
  hD : Sec13Data G F b Y
  hcE : c ∈ E
  hbE : b ∈ E
  hcF : c ∈ F
  haF : a ∈ F
  haE : a ∉ E
  haA : a ∈ A
  hcb : b ∉ Subgroup.zpowers c
  hEF : E ≤ Subgroup.normalizer (F : Set G)
  hFE : F ≤ Subgroup.normalizer (E : Set G)
  hcomm : ∀ f ∈ F, ∀ e ∈ E, f * e * f⁻¹ * e⁻¹ ∈ Subgroup.zpowers c
  hFEcard : Nat.card (E ⊓ F : Subgroup G) = 9
  hFgen : F = Subgroup.zpowers a ⊔ (E ⊓ F)
  hEY : E ≤ Subgroup.normalizer (Y : Set G)
  hR1 : R ≠ ⊥
  hR2 : IsPGroup 2 R
  hRa : R ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))
  hRb : R ≤ Subgroup.centralizer ({b} : Set G)
  hFR : F ≤ Subgroup.normalizer (R : Set G)
  hRc : ∀ r ∈ R, c * r * c⁻¹ = r → r = 1
  hlist : List463 Y

@[expose] def PieceStruct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Cfg G A c L E → c ∈ E ∧
      (∀ x ∈ A, ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers c) ∧
      A ≤ Subgroup.normalizer (E : Set G)

@[expose] def PieceLevel1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Cfg G A c L E → E ∉ partTwoE G →
      ∃ (F : Subgroup G) (a b : G) (R Y : Subgroup G), YCfg G A c L E F a b R Y

@[expose] def PieceA7M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      (haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
        Nonempty (Y ⧸ solvableRadical Y ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M22)) → False

@[expose] def PieceHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      (haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
        Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.J2)) → False

@[expose] def PieceL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      (haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
        ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
          Sec4.IsoLThreePi (Y ⧸ solvableRadical Y) p e) → False

@[expose] def PieceL227 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      (haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
        Nonempty (Y ⧸ solvableRadical Y ≃* projSL 2 (GaloisField 3 3))) → False

@[expose] def PieceM12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      (haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
        Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M12)) → False

theorem step131bSLTwoInEUOdd_of_pieces (hS : PieceStruct) (h1 : PieceLevel1)
    (hA7 : PieceA7M22) (hHJ : PieceHJ) (hL3 : PieceL3) (hL227 : PieceL227)
    (hM12 : PieceM12) : Step131bSLTwoInEUOdd := by
  intro G _ _ A c L hD hSL hSU E hEle hEe hE27 hEC hEL hodd
  by_contra hE
  have hcfg : Cfg G A c L E := ⟨hD, hSL, hSU, hEle, hEe, hE27, hEC, hEL, hodd⟩
  obtain ⟨F, a, b, R, Y, hY⟩ := h1 G A c L E hcfg hE
  have hlist := hY.hlist
  unfold List463 at hlist
  rcases hlist with h | h | h | h | h | h
  · exact hA7 G A c L E F a b R Y hY (Or.inl h)
  · exact hM12 G A c L E F a b R Y hY h
  · exact hHJ G A c L E F a b R Y hY h
  · exact hA7 G A c L E F a b R Y hY (Or.inr h)
  · exact hL3 G A c L E F a b R Y hY h
  · exact hL227 G A c L E F a b R Y hY h

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
