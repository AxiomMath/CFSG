module

public import CFSG.Quasithin.Vol2.Ch11SecDSetup
public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Vol2.Ch11SecABasicV
public import CFSG.Quasithin.Vol2.Ch11StatementsG

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def NatModule11 (T L I : Subgroup G) (n : ℕ) : Prop :=
  ∃ _ : IsMulCommutative ↥(fsuV T I),
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥(autOn L (fsuV T I)) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
        ∃ π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I)),
          (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π ∧
          NoGraphAutomorphism π (autOn T (fsuV T I))) ∨
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥(autOn L (fsuV T I)) ≃* ↥(StatedSp 2 K)) ∧
        ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I)),
          (FFModel.nat (StatedSp 2 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π ∧
          NoGraphAutomorphismSp4 π (autOn T (fsuV T I))) ∨
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥(autOn L (fsuV T I)) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧
        G2NaturalDerived (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) n)

structure NatSetting11 (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) : Prop where
  one_lt : 1 < n
  sylow : quasithinIsSylowTwo T
  normal : T ≤ Subgroup.normalizer (L : Set G)
  perfect : ⁅L, L⁆ = L
  elem : IsElemAbelian 2 (fsuV T I)
  le_normalizer : L ≤ Subgroup.normalizer (fsuV T I : Set G)
  cV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  quot : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L (fsuV T I)))
  nat : NatModule11 T L I n

theorem perfect_of_hyp11 [Finite G] {T L I : Subgroup G} {n : ℕ} (h : Hyp11 G T L I n) :
    ⁅L, L⁆ = L :=
  h.fsu.maximal.1.2.1.2.1

theorem natSetting11_of [Finite G] (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1)
    {T L I V₁ : Subgroup G} {n : ℕ} (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    NatSetting11 G T L I n := by
  obtain ⟨X, hX⟩ := exists_isCartanX h
  obtain ⟨hc, -, -, hq, hk⟩ := h1102 G T L I n h
  exact ⟨h.one_lt, h.fsu.sylow, h.normal, perfect_of_hyp11 h, SecA.isElemAbelian_fsuV h,
    SecA.L_le_normalizer_fsuV h, (h1141 G T L I n V₁ X h hV₁ hX).1.1, hq, ⟨hc, hk⟩⟩

@[expose] def PointsTIFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    NatSetting11 G T L I n → IsVi T L I n 1 V₁ →
      ∀ l ∈ L, V₁ ⊓ conjSubgroup V₁ l ≠ ⊥ → conjSubgroup V₁ l = V₁

@[expose] def NatV3Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 1 V₁ → IsVi T L I n 3 V₃ →
      V₁ ≤ V₃ ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsNaturalSection (LOf L V₁) V₃ V₁ (CFSG.pCore 2 ↥(LOf L V₁)) (StatedSL 2 F)

end CFSG.Quasithin.Vol2.Ch11.SecD
