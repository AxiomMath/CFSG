module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WInp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126P31
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise

@[expose] def E114ListF_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K →
        ((∃ n : ℕ, 2 ≤ n ∧
            ((conjClosure K T = K ∧ benderFam_w31 n (starMod_w31 H K)) ∨
             (conjClosure K T ≠ K ∧ fiveFam_w31 n (starMod_w31 H K)))) ∨
          (E1.nParam H = 2 ∧ (IsSporadic .M22 ↥(star H (conjClosure K T)) ∨
            IsHat ↥(star H (conjClosure K T)) (CFSG.Blueprint.NativeSporadic.Carrier .M22))))

@[expose] def NoSzF_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K →
        ∀ n : ℕ, 2 ≤ n → ¬ IsSz n (starMod_w31 H K)

@[expose] def ParityF_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → conjClosure K T = K →
        ∀ n : ℕ, 2 ≤ n →
          (IsPSL 2 2 n (starMod_w31 H K) ∨ IsPSL 3 2 n (starMod_w31 H K) ∨
            IsPSU 3 2 n (starMod_w31 H K)) → Even n

@[expose] def BorelF_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → conjClosure K T = K →
        ∀ n : ℕ, 2 ≤ n → Even n →
          ((IsPSL 2 2 n (starMod_w31 H K) ∨ IsPSL 3 2 n (starMod_w31 H K)) ∧ 4 ≤ n ∨
            IsPSU 3 2 n (starMod_w31 H K)) →
          ∃ P : Subgroup G, P ≤ L ∧ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ P ≠ ⊥ ∧ IsPGroup p ↥P ∧
            (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G)

@[expose] def NoSp4F_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → conjClosure K T = K →
        ∀ n : ℕ, 2 ≤ n → ¬ IsPSp4 2 n (starMod_w31 H K)

@[expose] def NoG2F_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → conjClosure K T = K →
        ∀ n : ℕ, 2 ≤ n → ¬ IsG2 2 n (starMod_w31 H K)

@[expose] def NoL2PairF_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → conjClosure K T ≠ K →
        ∀ m : ℕ, 2 ≤ m → IsPSL 2 2 m (starMod_w31 H K) → m = 2

end CFSG.Quasithin.H13
