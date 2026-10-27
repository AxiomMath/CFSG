module

public import CFSG.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

section Conclusions

variable {G : Type} [Group G] [Finite G] (T L V₀ : Subgroup G)
  [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
    (Subgroup.normalizer (conjClosure L T : Set G)))]

@[expose] def Concl326Cab : Prop :=
  (∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
          CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G)) =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
      (⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G))) ⊓
        (CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G))) =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
          Subgroup.centralizer (conjClosure L T : Set G) ∧
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
        Subgroup.centralizer (CFSG.conjugate L t : Set G)) ∧
    (∀ A ∈ QhatStar (V := ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))),
      ∀ a ∈ A, ∀ u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        (u : G) ∈ ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ →
        ((a u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) : G) ∈
          ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆) ∧
    ∃ _ : IsMulCommutative ↥⁅conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)), L⁆,
      qhatOf (V := ↥⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆)
        (autOn (conjClosure L T ⊔ T) ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆) ≤ 2

@[expose] def Case3_2_6_iv : Prop :=
  ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 2 2 n ∧
    DirectSumOfCopies (V := ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
      (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
      ((⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      ((⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊓
          Subgroup.centralizer (conjClosure L T : Set G)).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      (FFModel.nat (StatedSL 2 K)) 2

@[expose] def Concl326Cc : Prop :=
  (∃ x ∈ T, ⁅conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ = CFSG.conjugate V₀ x ∧
      conjClosure V₀ T =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ∨
    (Nonempty (↥(autOn (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))))) ≃*
        MulAut ↥(StatedSL 3 (ZMod 2))) ∧
      conjClosure V₀ T =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
      (∃ s ∈ T ⊓ Subgroup.normalizer (L : Set G),
        s ∉ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)))) ∧
      (∃ x ∈ T, ∀ s ∈ T ⊓ Subgroup.normalizer (L : Set G),
        s ∉ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) →
        ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ =
          CFSG.conjugate V₀ x ⊔ CFSG.conjugate (CFSG.conjugate V₀ x) s ∧
        CFSG.conjugate V₀ x ⊓ CFSG.conjugate (CFSG.conjugate V₀ x) s = ⊥) ∧
      Nat.card V₀ = 2 ^ 3) ∨
    Case3_2_6_iii T L V₀ ∨ Case3_2_6_iv T L V₀

@[expose] def Concl326C3 : Prop := Concl326Cab T L V₀ ∧ Concl326Cc T L V₀

end Conclusions

@[expose] def Stmt3_2_6C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    L ≠ conjClosure L T →
      (∃ _ : IsMulCommutative ↥(conjClosure V₀ T),
        qhatOf (V := ↥(conjClosure V₀ T)) (autOn (conjClosure L T ⊔ T) (conjClosure V₀ T)) ≤ 2) ∧
      ∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        qhatOf (V := ↥(conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))))
          (autOn (Subgroup.normalizer (conjClosure L T : Set G))
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) ≤ 2 ∧
        ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
            LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
              (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 2 2 n ∧
            V₀ = conjClosure V₀ T ∧
            conjClosure V₀ T =
              conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
            (tensorNatModel 2 K).Realizes
              (V := ↥(conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G))))
              (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G)))) ⊤ ⊥) ∨
          (LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
              (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 3 2 1 ∧
            V₀ = conjClosure V₀ T ∧
            conjClosure V₀ T =
              conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
            (tensorNatModel 3 (ZMod 2)).Realizes
              (V := ↥(conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G))))
              (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G)))) ⊤ ⊥) ∨
          Concl326C3 T L V₀)

private theorem conjugate_one_aux {G : Type} [Group G] (V : Subgroup G) :
    CFSG.conjugate V 1 = V := by
  ext x
  simp [CFSG.conjugate]

theorem concl326_imp_C (h : Stmt3_2_6) : Stmt3_2_6C := by
  intro G _ _ T L V₀ hfsu hne
  obtain ⟨hV, hVM, hq, hc⟩ := h G T L V₀ hfsu hne
  refine ⟨hV, hVM, hq, ?_⟩
  rcases hc with h1 | h2 | ⟨ha, hb, hq', hci | ⟨hA, hVeq, hs, hall, hcard⟩ | hiii⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨⟨ha, hb, hq'⟩, Or.inl ⟨1, T.one_mem, ?_, hci.2⟩⟩)
    rw [conjugate_one_aux]
    exact hci.1
  · refine Or.inr (Or.inr ⟨⟨ha, hb, hq'⟩, Or.inr (Or.inl ⟨hA, hVeq, hs, ⟨1, T.one_mem, ?_⟩,
      hcard⟩)⟩)
    intro s hsT hsn
    rw [conjugate_one_aux]
    exact hall s hsT hsn
  · exact Or.inr (Or.inr ⟨⟨ha, hb, hq'⟩, Or.inr (Or.inr (Or.inl hiii))⟩)

end CFSG.Quasithin.H13
