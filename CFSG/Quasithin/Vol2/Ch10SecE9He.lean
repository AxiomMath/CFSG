module

public import CFSG.Quasithin.Vol2.Ch10SecB4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

@[expose] def HeReduce : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → ∀ P : Subgroup G, IsMaxSubgroupIn (fsuL0 T L ⊔ T) P → T ≤ P →
    ∀ H : Subgroup G, InH (oTwoUpper P ⊔ T) H →
    ∀ K : Subgroup G, K ∈ cComp H → H ≤ Subgroup.normalizer (K : Set G) → oTwoUpper P ≤ K →
      Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) →
      ¬ K ≤ fsuM T L ∧ T ⊓ K ≤ T1 T L ∧
        ∃ w ∈ ⁅fsuVM T L I, L⁆, w ≠ 1 ∧ K ≤ Subgroup.centralizer ({w} : Set G)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem kof_cases_of_red (hRed : HeReduce) (h1029 : Stmt10_2_9)
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (hFa : FactL33M11) (hFc : FactL4L5)
    (h3 : Case10_1_1Three T L I) (h : MaxCtx T L I t Ψ c) (hD : ParData A K E)
    (hA : A = L32.Pa ∨ A = L32.Pb) {H : Subgroup G} (hH : InH (XOf T L Ψ A ⊔ T) H) :
    conjClosure (XOf T L Ψ A) H = XOf T L Ψ A ∨
    (∃ K₁ : Subgroup G, ∃ s ∈ T, quasithinIsCComponent K₁ H ∧
        s ∉ Subgroup.normalizer (K₁ : Set G) ∧
        conjClosure (XOf T L Ψ A) H = K₁ ⊔ CFSG.conjugate K₁ s ∧
        ((∃ m : ℕ, 0 < m ∧ Even m ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
            Nat.card F = 2 ^ m ∧
            Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
          ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p)))) ∨
    (quasithinIsCComponent (conjClosure (XOf T L Ψ A) H) H ∧ ∃ k : ℕ, (k = 4 ∨ k = 5) ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥(conjClosure (XOf T L Ψ A) H) ⧸ CFSG.pCore 2 ↥(conjClosure (XOf T L Ψ A) H))
          .PSL k 2 1 ∧
        Nonempty (↥(conjClosure (XOf T L Ψ A) H ⊔ T) ⧸
            CFSG.pCore 2 ↥(conjClosure (XOf T L Ψ A) H ⊔ T) ≃*
          MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)))) := by
  rcases kof_cases h134 hFa hFc h hD hH with h1 | h2 | h3' | ⟨K₁, hK₁, hHK, hXK, he⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3')
  · exfalso
    obtain ⟨hKM, -, w, hw, hw1, hKw⟩ := hRed G T L I h.hyp h3 _
      (isMax_preIn_sup h.h37 h.h38 h.hyp h.ht h.htn h.hC hA) le_sup_right H hH K₁ hK₁ hHK hXK he
    exact hKM (hKw.trans ((h1029 G T L I h.hyp L (Or.inl rfl)).1 w hw hw1))

end CFSG.Quasithin.Vol2.Ch10.SecB
