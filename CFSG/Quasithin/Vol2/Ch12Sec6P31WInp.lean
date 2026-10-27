module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Vol2.Ch12Sec6Final
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126P31
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise

abbrev starMod_w31 {G : Type} [Group G] (H K : Subgroup G) : Type :=
  ↥(star H K) ⧸ Subgroup.center ↥(star H K)

@[expose] def benderFam_w31 (n : ℕ) (X : Type) [Group X] : Prop :=
  IsPSL 2 2 n X ∨ IsSz n X ∨ IsPSU 3 2 n X ∨ IsPSL 3 2 n X ∨ IsPSp4 2 n X ∨ IsG2 2 n X

@[expose] def fiveFam_w31 (n : ℕ) (X : Type) [Group X] : Prop :=
  IsPSL 2 2 n X ∨ IsSz n X ∨ (n = 2 ∧ IsAlt 5 X)

@[expose] def E114List_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K →
        ((∃ n : ℕ, E1.nParam H = (n : ℕ∞) ∧
            ((conjClosure K T = K ∧ benderFam_w31 n (starMod_w31 H K)) ∨
             (conjClosure K T ≠ K ∧ fiveFam_w31 n (starMod_w31 H K)))) ∨
          (E1.nParam H = 2 ∧ (IsSporadic .M22 ↥(star H (conjClosure K T)) ∨
            IsHat ↥(star H (conjClosure K T)) (CFSG.Blueprint.NativeSporadic.Carrier .M22))))

@[expose] def NoM22_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → E1.nParam H = 2 →
        ¬ (IsSporadic .M22 ↥(star H (conjClosure K T)) ∨
          IsHat ↥(star H (conjClosure K T)) (CFSG.Blueprint.NativeSporadic.Carrier .M22))

@[expose] def NoPermL_w31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ P : Subgroup G, P ≤ L → ∀ p : ℕ, p.Prime → 3 < p → IsPGroup p ↥P →
        (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) → P = ⊥

end CFSG.Quasithin.H13
