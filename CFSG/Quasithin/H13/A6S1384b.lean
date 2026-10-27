module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.H13.A6S1383

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] def Struct13827 (S : Setting4 G T L V) : Prop :=
  ∃ K : Subgroup G, S.G1 ≤ Subgroup.normalizer (K : Set G) ∧ K ⊔ T = S.G1 ∧ S.L1 ≤ K ∧
    (∀ h ∈ S.G1, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 S.G1) → h ∈ pCoreOf 2 S.G1) ∧
    ((¬ IsHatA6 L ∧ ∃ ρ : ↥S.G1 →* Perm (Fin 6),
        (∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) ∧
        (∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6)) ∧
        (∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ) ∧
        ((∃ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6),
            Function.Surjective β ∧
            (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
            ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
              ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) =
                Multiplicative.toAdd (β u) →
                (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) =
                  Multiplicative.toAdd (β v)) ∨
          (∃ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6),
            Function.Surjective β ∧
            (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
            ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
              Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u))))) ∨
      (IsHatA6 L ∧ ∃ ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
        Function.Surjective ρ ∧ (∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) ∧
        ∃ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2),
          Function.Surjective β ∧
          (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
          ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
            Multiplicative.toAdd (β v) =
              ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
                Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u)))) ∧
    ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
      (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) ∨
        F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1) →
      F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1 ∧
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) ∧
        IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V) ∧
        fsuV1 T V ≤ F8.Uγ S.V3 S.G1 (g : G) ∧ ¬ F8.Uγ V S.G1 (g : G) ≤ pCoreOf 2 S.G1

end Setting4

@[expose] def Input13827Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827

@[expose] def Input13828Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827 → ¬ IsHatA6 L

@[expose] def Input13833Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827 → ¬ IsHatA6 L →
      ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) < F8.Uγ S.V3 S.G1 (g : G)

@[expose] def Input13834Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827 → ¬ IsHatA6 L →
      (∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) < F8.Uγ S.V3 S.G1 (g : G)) → False

theorem input1384Six_of (h27 : Input13827Six) (h28 : Input13828Six) (h33 : Input13833Six)
    (h34 : Input13834Six) : Input1384Six := by
  intro G _ _ T L V S hNS hNU hG1 hab hF
  have hst := h27 G T L V S hNS hNU hG1 hab hF
  have hhat := h28 G T L V S hNS hNU hG1 hab hF hst
  exact h34 G T L V S hNS hNU hG1 hab hF hst hhat (h33 G T L V S hNS hNU hG1 hab hF hst hhat)

end CFSG.Quasithin.H13.A6
