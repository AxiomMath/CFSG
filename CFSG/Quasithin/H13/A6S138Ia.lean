module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.H13.A6S1383

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

structure Hyp138 (S : Setting4 G T L V) : Prop where
  hNS : ¬ LieModel G .PSp 3 2 1
  hNU : ¬ LieModel G .PSU 4 3 1
  hG1 : S.G1 ∈ S.Hz
  hab : IsMulCommutative ↥(conjClosure V S.G1)
  hF : ∀ H ∈ S.Hz, HypF98 T V L (fsuV1 T V) S.V3 H

noncomputable abbrev KSt (S : Setting4 G T L V) (H K : Subgroup G) :
    Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
  autOn (tildeOf (fsuV1 T V) K) (tildeOf (fsuV1 T V) (conjClosure S.V3 H))

theorem hyp138_of {S : Setting4 G T L V}
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hNS : ¬ LieModel G .PSp 3 2 1)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hG1 : S.G1 ∈ S.Hz)
    (hab : IsMulCommutative ↥(conjClosure V S.G1)) : S.Hyp138 :=
  ⟨hNS, hNU, hG1, hab, fun _ hH => S.hypF98 hNS h13315 h1356two hab hH⟩

end Setting4

@[expose] def Lem13813 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ X : Subgroup G, S.L1 ⊔ T ≤ X → X ≤ S.G1 → Group.IsSolvable ↥X →
      X ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lem13816 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
      (H ≤ Subgroup.normalizer (K : Set G) ∧ (K ⊔ S.L1) ⊔ T ∈ S.Hz) ∧
        ¬ ∃ e, IsSz e ↥(S.KSt H K)

@[expose] def Lem13821 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
      S.L1 ≤ K ∧
        (IsPSL 3 2 1 ↥(S.KSt H K) ∨ IsPSL 4 2 1 ↥(S.KSt H K) ∨ IsPSL 5 2 1 ↥(S.KSt H K) ∨
          IsAlt 6 ↥(S.KSt H K) ∨ IsAlt 7 ↥(S.KSt H K) ∨ IsPSU 3 3 1 ↥(S.KSt H K)) ∧
        (K ⊔ T = H ∧
          (IsPSL 3 2 1 ↥(S.KSt H K) → Nonempty (↥(S.KSt H H) ≃* MulAut ↥(S.KSt H K)))) ∧
        ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H

@[expose] def Lem13824 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ¬ IsAlt 7 ↥(S.KSt H K)

@[expose] def Lem13825 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ∀ n, 3 ≤ n → n ≤ 5 → IsPSL n 2 1 ↥(S.KSt H K) →
      n = 4 ∧ (IsHatA6 L ∧ ∃ ρ : ↥H →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
        Function.Surjective ρ ∧ (∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
        ∃ β : ↥(conjClosure S.V3 H) →* Multiplicative (Fin 4 → ZMod 2),
          Function.Surjective β ∧
          (∀ u : ↥(conjClosure S.V3 H), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
          ∀ (h : ↥H) (u v : ↥(conjClosure S.V3 H)), (v : G) = h * u * h⁻¹ →
            Multiplicative.toAdd (β v) =
              ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
                Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u))) ∧
        H = S.G1

@[expose] def Lem13826 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, IsAlt 6 ↥(S.KSt H K) →
      ∃ α : ↥K →* alternatingGroup (Fin 6), Function.Surjective α ∧
        (∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) ∧
        (∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 → ∀ u ∈ conjClosure S.V3 H,
          (∀ k ∈ K, k * (c * u * c⁻¹ * u⁻¹) * k⁻¹ * (c * u * c⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V) →
          ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧
        ((∃ β : ↥(conjClosure S.V3 H) →* Multiplicative (AltHeart 6),
            Function.Surjective β ∧
            (∀ u : ↥(conjClosure S.V3 H), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
            ∀ (k : ↥K) (u v : ↥(conjClosure S.V3 H)), (v : G) = k * u * k⁻¹ →
              ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) =
                Multiplicative.toAdd (β u) →
                (QuotientAddGroup.mk (permWeight 6 (α k : Perm (Fin 6)) x) : AltHeart 6) =
                  Multiplicative.toAdd (β v)) ∨
          (∃ β : ↥(conjClosure S.V3 H) →* Multiplicative ↥(evenWeight 6),
            Function.Surjective β ∧
            (∀ u : ↥(conjClosure S.V3 H), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
            ∀ (k : ↥K) (u v : ↥(conjClosure S.V3 H)), (v : G) = k * u * k⁻¹ →
              Multiplicative.toAdd (β v) =
                permWeight 6 (α k : Perm (Fin 6)) (Multiplicative.toAdd (β u))))

@[expose] def Lem13827G2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ K ∈ cComp S.G1, ¬ IsPSU 3 3 1 ↥(S.KSt S.G1 K)

end CFSG.Quasithin.H13.A6
