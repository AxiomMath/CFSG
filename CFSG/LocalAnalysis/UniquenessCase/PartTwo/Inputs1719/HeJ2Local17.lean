module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def K_SporadicNine : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    (∃ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .He ∨ s = .J4) ∧
        IsSpor (↥K ⧸ Subgroup.center ↥K) s) →
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ Permutes E S

@[expose] def K_M12SThreePair : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    CFSG.Open.IsQuasisimple ↥K → Odd (Nat.card (Subgroup.center ↥K)) →
    IsSpor (↥K ⧸ Subgroup.center ↥K) .M12 →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∃ P₁ P₂ : Subgroup Y, S ≤ P₁ ∧ S ≤ P₂ ∧ P₁ ⊔ P₂ = ⊤ ∧
        Nonempty (Bar2 P₁ ≃* Equiv.Perm (Fin 3)) ∧
          Nonempty (Bar2 P₂ ≃* Equiv.Perm (Fin 3))

@[expose] def K_HSRuParabolics : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    CFSG.Open.IsQuasisimple ↥K → Odd (Nat.card (Subgroup.center ↥K)) →
    (IsSpor (↥K ⧸ Subgroup.center ↥K) .HS ∨ IsSpor (↥K ⧸ Subgroup.center ↥K) .Ru) →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∃ H₁ H₂ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ H₁ ⊔ H₂ = ⊤ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H₁ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H₂ ∧
            3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂

@[expose] def K_HeParabolics : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    CFSG.Open.IsQuasisimple ↥K → Odd (Nat.card (Subgroup.center ↥K)) →
    IsSpor ↥K .He →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∃ H₁ H₂ H₃ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ S ≤ H₃ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
            CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ ∧
              H₁ ⊔ H₂ ⊔ H₃ = ⊤

theorem not_thin_of_pRank_three {L : Subgroup G} (h : 2 ≤ CFSG.Open.pRank 3 L) :
    ¬ F08.Thin8 L :=
  fun ht => absurd (ht 3 Nat.prime_three (by norm_num)) (by omega)

theorem uniqueMax_sup_T_of_not_thin {D : Data G} (h869 : F08.R869 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hnt : ¬ F08.Thin8 L) : UniqueMax D.M (L ⊔ D.T) := by
  have hN : calNOf L = {D.M} :=
    h869 L (Or.inl hL) L le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
  have hU : UniqueMax D.M L := UC22.uc22p22u_uniqueMax_of_calN D hL.1.le hN
  exact UC22.uc22p22u_uniqueMax_mono D le_sup_left (sup_le hL.1.le D.sylowM.le) hU

theorem conjClosure_eq_self_of_normal {D : Data G} {L : Subgroup G} (hLM : L ≤ D.M)
    (hN : (L.subgroupOf D.M).Normal) : UC22.conjClosure D.M L = L :=
  le_antisymm
    (uc22p22v_conjClosure_le ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN) le_rfl)
    (TwelveTwentyThree.le_conjClosure D.M L)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
