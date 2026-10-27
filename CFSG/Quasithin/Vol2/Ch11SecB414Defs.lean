module

public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank

structure Hyp {G : Type} [Group G] (Γ V Z L X : Subgroup G) (F : Type) [Field F] [Fintype F]
    (α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
    (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))) : Prop where
  card : Fintype.card F = 4
  le_normalizer_V : Γ ≤ Subgroup.normalizer (V : Set G)
  le_normalizer_Z : Γ ≤ Subgroup.normalizer (Z : Set G)
  lt : Z < V
  sq_mem : ∀ v ∈ V, v ^ 2 ∈ Z
  comm_mem : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ Z
  irred : ∀ J : Subgroup G, Z ≤ J → J ≤ V → Γ ≤ Subgroup.normalizer (J : Set G) → J = Z ∨ J = V
  le_L : L ≤ Γ
  le_X : X ≤ Γ
  surj : Function.Surjective α
  ker_iff : ∀ γ : ↥Γ, α γ = 1 ↔ ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z
  maxParabolic : IsMaxParabolic2 ⊤ P
  map_L : (L.subgroupOf Γ).map α = perfectCore P
  map_X_le : (X.subgroupOf Γ).map α ≤ P
  card_X : Nat.card ↥((X.subgroupOf Γ).map α) = 3
  comm_X : ∀ x ∈ (X.subgroupOf Γ).map α, ∀ l ∈ (L.subgroupOf Γ).map α,
    x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 ((L.subgroupOf Γ).map α)
  natural : ∀ C₁ C₂ : Subgroup G, Z ≤ C₁ → C₁ < C₂ → C₂ ≤ V →
    L ≤ Subgroup.normalizer (C₁ : Set G) → L ≤ Subgroup.normalizer (C₂ : Set G) →
    (∀ J : Subgroup G, C₁ ≤ J → J ≤ C₂ → L ≤ Subgroup.normalizer (J : Set G) →
      J = C₁ ∨ J = C₂) →
    (∃ l ∈ L, ∃ c ∈ C₂, l * c * l⁻¹ * c⁻¹ ∉ C₁) →
    ∃ N' : Subgroup ↥L, IsNaturalSection L C₂ C₁ N' (StatedSL 2 F)

@[expose] def LemmaB414Class : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Γ V Z L X : Subgroup G) (F : Type) [Field F] [Fintype F]
    (α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
    (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))),
    Hyp Γ V Z L X F α P → ∃ k : ℕ, k < 3 ∧ IsTwAdjointSection k Γ V Z α.ker F

@[expose] def LemmaB414Model : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Γ V Z L X : Subgroup G) (F : Type) [Field F] [Fintype F]
    (α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
    (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))),
    Hyp Γ V Z L X F α P →
    ∀ k : ℕ, k < 3 → IsTwAdjointSection k Γ V Z α.ker F →
      (k = 0 → UntwistedFixed V Z L X (α.ker.map Γ.subtype)) ∧
      (k ≠ 0 → TwistedFixed V Z L X (α.ker.map Γ.subtype)) ∧
      ∃ j : ℕ, j < 3 ∧ (j = 0 ↔ k = 0) ∧
        (j = 1 → ∀ v ∈ V, IsFixedMod X Z v →
          (∀ γ : ↥Γ, α γ ∈ pCoreOf 2 (perfectCore P) → (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z) →
            v ∈ Z) ∧
        ∀ α₀' : ↥(perfectCore P) →* ↥(StatedSL 2 F), Function.Surjective α₀' →
          α₀'.ker = (pCoreOf 2 (perfectCore P)).subgroupOf (perfectCore P) →
          ∀ α₀ : ↥L →* ↥(StatedSL 2 F),
            (∀ (l : ↥L) (γ : ↥Γ) (p : ↥(perfectCore P)), (γ : G) = l →
              (p : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) = α γ → α₀ l = α₀' p) →
          ∀ γx : ↥Γ, (γx : G) ∈ X → α γx ≠ 1 →
            ∃ μ : F, IsNatEigSection (perfectCore P) (α γx) α₀' ⊥ (pCoreOf 2 (perfectCore P)) μ ∧
              ∃ l : List (Subgroup G × Option F), IsLabSeries (L ⊔ X) L (γx : G) α₀ Z l V ∧
                labMultiset l = ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F)

theorem lemmaB414Corrected_of (h1 : LemmaB414Class) (h2 : LemmaB414Model) :
    LemmaB414Corrected := by
  intro G _ _ Γ V Z L X F _ _ hF hV hZ hZV hsq hcomm hirr hL hX α hα hker P hP hLP hXP hX3 hXL
    hnat
  have hyp : Hyp Γ V Z L X F α P :=
    ⟨hF, hV, hZ, hZV, hsq, hcomm, hirr, hL, hX, hα, hker, hP, hLP, hXP, hX3, hXL, hnat⟩
  exact ⟨h1 G Γ V Z L X F α P hyp, h2 G Γ V Z L X F α P hyp⟩

end CFSG.Quasithin.H13.Ch4.B414
