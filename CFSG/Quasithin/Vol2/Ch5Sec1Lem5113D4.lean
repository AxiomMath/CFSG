module

public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

section Vocabulary

variable {G : Type} [Group G]

@[expose] def Case3D4L28 (T L V H : Subgroup G) (n : ℕ) : Prop :=
  LieModel (O2Q (oTwoUpper H)) .PSL 2 2 3 ∧ n = 2 ∧ IsA5ModuleSum L V ∧
    oTwoUpper H ≤ oThreePrimeResidual (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
    Is3D4 2 1 (O2Q (oThreePrimeResidual
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))))

theorem Case3D4L28.not_lieModel_two {T L V H : Subgroup G} {n : ℕ} (h : Case3D4L28 T L V H n)
    (h4 : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2) : False := by
  have c : ∀ {f : ℕ}, LieModel (O2Q (oTwoUpper H)) .PSL 2 2 f →
      Nat.card (O2Q (oTwoUpper H)) = ordA (2 - 1) (2 ^ f) := fun hf =>
    (CFSG.Timmesfeld.card_statedClassicalModel_two
      (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hf)).1 rfl
  have h8 := c h.1
  rw [c h4] at h8
  exact absurd h8 (by decide)

end Vocabulary

@[expose] def Stmt5_1_13_lie_D42C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n k : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsFieldParam510 T H k →
    IsCh5Module T L V →
    quasithinIsCComponent K₁ H → oTwoUpper H = conjClosure K₁ T → InH H X →
    IsHatComp X K₁ Kh₁ → oTwoUpper H < conjClosure Kh₁ T →
    ((SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q (conjClosure Kh₁ T)))) →
    (∃ U P : Subgroup (O2Q (conjClosure Kh₁ T)), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧
      Group.IsSolvable ↥P) →
      D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∨ Case3D4L28 T L V H n

@[expose] def Stmt5_1_13_lieC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n k : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsFieldParam510 T H k →
    IsCh5Module T L V →
    quasithinIsCComponent K₁ H → oTwoUpper H = conjClosure K₁ T → InH H X →
    IsHatComp X K₁ Kh₁ → oTwoUpper H < conjClosure Kh₁ T →
    ((SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q (conjClosure Kh₁ T)))) →
      D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∨ Case3D4L28 T L V H n

@[expose] def Stmt5_1_13C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    quasithinIsCComponent K₁ H → oTwoUpper H = conjClosure K₁ T →
    InH H X → IsHatComp X K₁ Kh₁ →
      D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ n = 2 ∧ IsA5ModuleSum L V ∧
        conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
        (Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (O2Q (conjClosure Kh₁ T) ≃* NativeSporadic.J2) ∨
          Nonempty (O2Q (conjClosure Kh₁ T) ≃* NativeSporadic.M23)) ∧
        ∀ Kz₁ : Subgroup G,
          IsHatComp (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) K₁ Kz₁ →
            conjClosure Kz₁ T =
                oThreePrimeResidual
                  (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
              (conjClosure Kh₁ T = conjClosure Kz₁ T ∨
                (Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) ∧
                  Nonempty (O2Q (conjClosure Kz₁ T) ≃* NativeSporadic.M23)))) ∨
      Case3D4L28 T L V H n

@[expose] def Stmt5_2_2C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
      D ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ n = 2 ∧ IsA5ModuleSum L V ∧
        oTwoUpper H ≤
          oThreePrimeResidual (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
        (Nonempty (O2Q (oThreePrimeResidual
            (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) ≃*
              alternatingGroup (Fin 7)) ∨
          Nonempty (O2Q (oThreePrimeResidual
            (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) ≃* NativeSporadic.J2) ∨
          Nonempty (O2Q (oThreePrimeResidual
            (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) ≃* NativeSporadic.M23))) ∨
      Case3D4L28 T L V H n

end CFSG.Quasithin.H13
