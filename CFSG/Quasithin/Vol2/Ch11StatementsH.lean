module

public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)

@[expose] def Stmt11_5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ), Hyp11 G T L I n →
    KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n

@[expose] def Stmt11_5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → KOf L V₁ V₁ = LOf L V₁ →
      (∀ g : G, g ∉ Subgroup.normalizer (fsuV T I : Set G) → ∃ y ∈ L,
        fsuV T I ⊓ conjSubgroup (fsuV T I) g ≤ conjSubgroup V₁ y) ∧
      (KindSL3 L (fsuV T I) n → ((2 * n : ℕ) : ℕ∞) ≤ E3.rParam (fsuV T I)) ∧
      (KindSp4 L (fsuV T I) n → ((3 * n : ℕ) : ℕ∞) ≤ E3.rParam (fsuV T I)) ∧
      ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))

@[expose] def Stmt11_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ →
      ¬ Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H ∧
        H ≤ Subgroup.normalizer (V₁ : Set G) ∧ oTwoUpper H ≤ Subgroup.centralizer (V₁ : Set G) ∧
        (⁅KOf L V₁ V₁, oTwoUpper H⁆ ≤ pCoreOf 2 (KOf L V₁ V₁) ∨ oTwoUpper H ≤ KOf L V₁ V₁)

@[expose] def Stmt11_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ H₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 3 V₃ → InH (LOf L V₁ ⊔ T) H₁ →
    ¬ H₁ ≤ Subgroup.normalizer (L : Set G) → H₁ ≤ Subgroup.normalizer (V₁ : Set G) →
      conjClosure V₃ H₁ ≤ pCoreOf 2 H₁ ∧
      ⁅conjClosure V₃ H₁, pCoreOf 2 H₁⁆ ≤ V₁ ∧
      (frattini ↥(conjClosure V₃ H₁)).map (conjClosure V₃ H₁).subtype ≤ V₁ ∧
      (KOf L V₁ V₁ = LOf L V₁ →
        ∃ (s : ℕ) (W : Fin s → Subgroup G) (F : Type) (_ : Field F) (_ : Fintype F),
          Fintype.card F = 2 ^ n ∧ (∀ i, V₁ ≤ W i ∧ W i ≤ conjClosure V₃ H₁) ∧
          (∀ i, W i ⊓ (V₁ ⊔ ⨆ (j : Fin s) (_ : j ≠ i), W j) = V₁) ∧
          (V₁ ⊔ ⨆ i, W i) = conjClosure V₃ H₁ ∧
          ∀ i, IsNaturalSection (KOf L V₁ V₁) (W i) V₁ (CFSG.pCore 2 ↥(KOf L V₁ V₁))
            (StatedSL 2 F))

section Defs

variable {G : Type} [Group G]

abbrev oTwoPrime (K : Subgroup G) (p : ℕ) : Subgroup G :=
  preimageModTwoCore K (CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K))

end Defs

@[expose] def Stmt11_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ X H₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsCartanX T L X → InH (LOf L V₁ ⊔ T) H₁ →
    ¬ H₁ ≤ Subgroup.normalizer (L : Set G) → H₁ ≤ Subgroup.normalizer (V₁ : Set G) →
      Nat.Coprime (Nat.card ↥(Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) (2 ^ n - 1) ∧
      CFSG.pRank 3 ↥(Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) ≤ 1 ∧
      (Even n → ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) ∧
      (∀ I' : Subgroup G, quasithinIsCComponent I' (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) →
        CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I') →
        ⁅I', X⁆ ≤ pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) ∧
      (∀ P : Subgroup G, P = ⁅P, X⁆ → P ≤ T →
        (frattini ↥P).map P.subtype ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) →
        ⁅P, Subgroup.centralizer (V₁ : Set G) ⊓
            sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))⁆ ≤
          pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
            sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) ∧
      ⁅pCoreOf 2 (L ⊔ T), X⁆ ≤ pCoreOf 2 (KOf L V₁ V₁ ⊔ T) ∧
      (oTwoUpper H₁ ≤ KOf L V₁ V₁ →
        (Case11_1_2Two L (KOf L V₁ V₁) ∨
          (∃ p : ℕ, p.Prime ∧ IsPGroup p ↥(CFSG.fittingSubgroup
            (↥(KOf L V₁ V₁) ⧸ CFSG.pCore 2 ↥(KOf L V₁ V₁)))) ∨
          ∃ p : ℕ, p.Prime ∧ oTwoUpper H₁ ≤ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁) →
        ∀ A : Subgroup G, A ≤ ROf T L V₁ → IsElemAbelian 2 A →
          E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≤ 1)

@[expose] def Stmt11_5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ →
      IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))

@[expose] def Stmt11_5_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → KOf L V₁ V₁ = LOf L V₁

theorem stmt11_0_1_of_steps (hq : RankTwoQuasisimple) (h1100 : Stmt11_0_0)
    (hfsu : Ch10.StmtFSUChoice) (h1110 : Stmt11_1_0) (h1153 : Stmt11_5_3)
    (h1157 : Stmt11_5_7) (h1158 : Stmt11_5_8) : Stmt11_0_1 := by
  intro G _ _ T L hs hn hQ hT hmax hf
  rintro ⟨n, hn1, hshape⟩
  have hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hq _ n hn1 hshape
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    h1100 G T L n hs hn hQ hT hmax hf hn1 hshape
  obtain ⟨I, hI⟩ := hfsu G T L hs hn hQ hT hmax hf hqs
  have hyp : Hyp11 G T L I n := ⟨hI, hTL, hn1, hshape⟩
  obtain ⟨V₁, hV₁, -⟩ := (h1110 G T L I n hyp).1 1 le_rfl (by norm_num)
  exact (h1153 G T L I n V₁ hyp hV₁ (h1158 G T L I n V₁ hyp hV₁)).2.2.2
    (h1157 G T L I n V₁ hyp hV₁)

end CFSG.Quasithin.Vol2.Ch11
