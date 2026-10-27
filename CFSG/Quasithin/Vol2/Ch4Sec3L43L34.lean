module

public import CFSG.Quasithin.Vol2.Ch4Sec3Core
public import CFSG.Quasithin.Background.OperatorJordanHolder

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

@[expose] def sl3 (F : Type) [Field F] : AddSubgroup (Matrix (Fin 3) (Fin 3) F) :=
  (Matrix.traceAddMonoidHom (Fin 3) F).ker

@[expose] def twAdj {F : Type} [Field F] (k : ℕ) (g : GL (Fin 3) F)
    (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  ((g : Matrix (Fin 3) (Fin 3) F).det) ^ k •
    ((g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))

variable {G : Type} [Group G]

@[expose] def IsTwAdjointSection (k : ℕ) (Γ V Z : Subgroup G) (N : Subgroup Γ) (F : Type)
    [Field F] : Prop :=
  Γ ≤ Subgroup.normalizer (V : Set G) ∧ Z ≤ V ∧
    ∃ α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F), Function.Surjective α ∧
      α.ker = N ∧
      ∃ β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F),
        (∀ v : ↥V, Multiplicative.toAdd (β v) ∈ sl3 F) ∧
        (∀ M ∈ sl3 F, ∃ v : ↥V, Multiplicative.toAdd (β v) = M) ∧ β.ker = Z.subgroupOf V ∧
        ∀ (γ : ↥Γ) (u v : ↥V), (v : G) = γ * u * γ⁻¹ → ∀ g : GL (Fin 3) F,
          (QuotientGroup.mk g : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) = α γ →
          Multiplicative.toAdd (β v) = twAdj k g (Multiplicative.toAdd (β u))

@[expose] def IsFixedMod (X Z : Subgroup G) (v : G) : Prop :=
  ∀ x ∈ X, x * v * x⁻¹ * v⁻¹ ∈ Z

@[expose] def IsCentMod (X N : Subgroup G) (l : G) : Prop :=
  ∀ x ∈ X, l * x * l⁻¹ * x⁻¹ ∈ N

@[expose] def UntwistedFixed (V Z L X N : Subgroup G) : Prop :=
  (∀ J : Subgroup G, Z < J → (∀ j ∈ J, j ∈ V ∧ IsFixedMod X Z j) →
      (∀ l ∈ L, IsCentMod X N l → ∀ j ∈ J, l * j * l⁻¹ ∈ J) →
      ∃ j ∈ J, j ∉ Z ∧ ∀ l ∈ L, IsCentMod X N l → l * j * l⁻¹ * j⁻¹ ∈ Z) ∧
    ∃ l ∈ L, IsCentMod X N l ∧ ∃ v ∈ V, IsFixedMod X Z v ∧ l * v * l⁻¹ * v⁻¹ ∉ Z

@[expose] def TwistedFixed (V Z L X N : Subgroup G) : Prop :=
  (∃ v ∈ V, IsFixedMod X Z v ∧ v ∉ Z) ∧
    (∀ J : Subgroup G, Z ≤ J → (∀ j ∈ J, j ∈ V ∧ IsFixedMod X Z j) →
      (∀ l ∈ L, IsCentMod X N l → ∀ j ∈ J, l * j * l⁻¹ ∈ J) →
      J = Z ∨ ∀ v ∈ V, IsFixedMod X Z v → v ∈ J) ∧
    ∀ v ∈ V, IsFixedMod X Z v → (∀ l ∈ L, IsCentMod X N l → l * v * l⁻¹ * v⁻¹ ∈ Z) → v ∈ Z

@[expose] def LemmaB414Corrected : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Γ V Z L X : Subgroup G) (F : Type) [Field F] [Fintype F],
    Fintype.card F = 4 →
    Γ ≤ Subgroup.normalizer (V : Set G) → Γ ≤ Subgroup.normalizer (Z : Set G) → Z < V →
    (∀ v ∈ V, v ^ 2 ∈ Z) → (∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ Z) →
    (∀ J : Subgroup G, Z ≤ J → J ≤ V → Γ ≤ Subgroup.normalizer (J : Set G) → J = Z ∨ J = V) →
    L ≤ Γ → X ≤ Γ →
    ∀ α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F), Function.Surjective α →
    (∀ γ : ↥Γ, α γ = 1 ↔ ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z) →
    ∀ P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)), IsMaxParabolic2 ⊤ P →
    (L.subgroupOf Γ).map α = perfectCore P → (X.subgroupOf Γ).map α ≤ P →
    Nat.card ↥((X.subgroupOf Γ).map α) = 3 →
    (∀ x ∈ (X.subgroupOf Γ).map α, ∀ l ∈ (L.subgroupOf Γ).map α,
      x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 ((L.subgroupOf Γ).map α)) →
    (∀ C₁ C₂ : Subgroup G, Z ≤ C₁ → C₁ < C₂ → C₂ ≤ V →
      L ≤ Subgroup.normalizer (C₁ : Set G) → L ≤ Subgroup.normalizer (C₂ : Set G) →
      (∀ J : Subgroup G, C₁ ≤ J → J ≤ C₂ → L ≤ Subgroup.normalizer (J : Set G) →
        J = C₁ ∨ J = C₂) →
      (∃ l ∈ L, ∃ c ∈ C₂, l * c * l⁻¹ * c⁻¹ ∉ C₁) →
      ∃ N' : Subgroup ↥L, IsNaturalSection L C₂ C₁ N' (StatedSL 2 F)) →
    (∃ k : ℕ, k < 3 ∧ IsTwAdjointSection k Γ V Z α.ker F) ∧
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

structure Config43L34 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ)
    (I H K : Subgroup G) (t : G) (F : Type) [Field F] [Fintype F]
    (ZS K₂ R₂ X KZ Γ A B : Subgroup G)
    (α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
    (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))) : Prop where
  sk : Setting432K G T M L n I H K t
  charTwo : CharTwo K
  c41 : C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K
  c3 : C41Case3 H (pCoreOf 2 I) (H ⊓ M) L
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K
  c134 : IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K
  cent : T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥
  card_F : Fintype.card F = 4
  ZS_eq : ZS = ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ ⊓
    Subgroup.centralizer ((T ⊓ H ⊓ L : Subgroup G) : Set G)
  K₂_eq : K₂ = perfectCore (K ⊓ Subgroup.centralizer (ZS : Set G))
  R₂_eq : R₂ = pCoreOf 2 (K₂ ⊔ T ⊓ H)
  KZ_mem : KZ ∈ cComp (Subgroup.normalizer (ZS : Set G))
  KZ_normal : Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G)
  K₂_le : K₂ ≤ KZ
  KZ_L34 : IsPSL 3 2 2 (ModO2 KZ)
  O2KZ_le : pCoreOf 2 KZ ≤ R₂
  X_card : Nat.card X = 3
  X_le : X ≤ K
  X_center : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K
  X_ZS : X ≤ Subgroup.normalizer (ZS : Set G)
  X_K₂ : X ≤ Subgroup.normalizer (K₂ : Set G)
  Γ_eq : Γ = KZ ⊔ X
  A_le : A ≤ pCoreOf 2 KZ
  B_lt : B < A
  Γ_A : Γ ≤ Subgroup.normalizer (A : Set G)
  Γ_B : Γ ≤ Subgroup.normalizer (B : Set G)
  sq : ∀ a ∈ A, a ^ 2 ∈ B
  comm : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B
  irred : ∀ J : Subgroup G, B ≤ J → J ≤ A → Γ ≤ Subgroup.normalizer (J : Set G) →
    J = B ∨ J = A
  α_surj : Function.Surjective α
  α_ker : ∀ γ : ↥Γ, α γ = 1 ↔ ∀ a ∈ A, (γ : G) * a * (γ : G)⁻¹ * a⁻¹ ∈ B
  α_ker_le : ∀ γ : ↥Γ, α γ = 1 → (γ : G) ∈ pCoreOf 2 KZ
  P_max : IsMaxParabolic2 ⊤ P
  P_K₂ : (K₂.subgroupOf Γ).map α = perfectCore P
  P_X : (X.subgroupOf Γ).map α ≤ P
  αX_card : Nat.card ↥((X.subgroupOf Γ).map α) = 3
  αX_cent : ∀ x ∈ (X.subgroupOf Γ).map α, ∀ l ∈ (K₂.subgroupOf Γ).map α,
    x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 ((K₂.subgroupOf Γ).map α)
  star : ∀ C₁ C₂ : Subgroup G, B ≤ C₁ → C₁ < C₂ → C₂ ≤ A →
    K₂ ≤ Subgroup.normalizer (C₁ : Set G) → K₂ ≤ Subgroup.normalizer (C₂ : Set G) →
    (∀ J : Subgroup G, C₁ ≤ J → J ≤ C₂ → K₂ ≤ Subgroup.normalizer (J : Set G) →
      J = C₁ ∨ J = C₂) →
    (∃ l ∈ K₂, ∃ c ∈ C₂, l * c * l⁻¹ * c⁻¹ ∉ C₁) →
    ∃ N' : Subgroup ↥K₂, IsNaturalSection K₂ C₂ C₁ N' (StatedSL 2 F)
  D_irred : ∀ J : Subgroup G, J ≤ pCoreOf 2 K₂ ⊓ Subgroup.centralizer (X : Set G) →
    K₂ ⊓ Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (J : Set G) →
    J = ⊥ ∨ J = pCoreOf 2 K₂ ⊓ Subgroup.centralizer (X : Set G)
  D_fix : ∀ d ∈ pCoreOf 2 K₂ ⊓ Subgroup.centralizer (X : Set G),
    (∀ k ∈ K₂ ⊓ Subgroup.centralizer (X : Set G), k * d * k⁻¹ = d) → d = 1
  D_comm : ∀ r ∈ R₂ ⊓ Subgroup.centralizer (X : Set G),
    ∀ k ∈ K₂ ⊓ Subgroup.centralizer (X : Set G),
    k * r * k⁻¹ * r⁻¹ ∈ pCoreOf 2 K₂ ⊓ Subgroup.centralizer (X : Set G)
  KZ_cent : KZ ≤ Subgroup.centralizer (ZS : Set G)
  labels : ∃ (α₀' : ↥(perfectCore P) →* ↥(StatedSL 2 F)) (α₀ : ↥K₂ →* ↥(StatedSL 2 F)),
    Function.Surjective α₀' ∧
    α₀'.ker = (pCoreOf 2 (perfectCore P)).subgroupOf (perfectCore P) ∧
    (∀ (l : ↥K₂) (γ : ↥Γ) (p : ↥(perfectCore P)), (γ : G) = l →
      (p : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) = α γ → α₀ l = α₀' p) ∧
    ∀ γx : ↥Γ, (γx : G) ∈ X → α γx ≠ 1 →
      ∃ (U : Subgroup G) (ω₀ μ' : F), ω₀ ≠ 1 ∧ ω₀ ^ 3 = 1 ∧
        IsNatEigSection (perfectCore P) (α γx) α₀' ⊥ (pCoreOf 2 (perfectCore P)) μ' ∧
        (∃ l : List (Subgroup G × Option F), IsLabSeries (K₂ ⊔ X) K₂ (γx : G) α₀ ⊥ l R₂ ∧
          labMultiset l = ({ω₀, ω₀⁻¹, ω₀⁻¹, 1} : Multiset F)) ∧
        (∃ l : List (Subgroup G × Option F), IsLabSeries (K₂ ⊔ X) K₂ (γx : G) α₀ ⊥ l B ∧
          ∀ q ∈ l, q.2 = none) ∧
        (∃ l : List (Subgroup G × Option F),
          IsLabSeries (K₂ ⊔ X) K₂ (γx : G) α₀ A l (pCoreOf 2 KZ) ∧ ∀ q ∈ l, q.2 = none) ∧
        (∃ l : List (Subgroup G × Option F),
          IsLabSeries (K₂ ⊔ X) K₂ (γx : G) α₀ (pCoreOf 2 KZ) l R₂ ∧
          labMultiset l = ({μ'} : Multiset F)) ∧
        IsLabFactor (K₂ ⊔ X) K₂ (γx : G) α₀ ZS U (some ω₀) ∧
        U ≤ pCoreOf 2 K₂ ∧ ⁅U, pCoreOf 2 K₂⁆ ≤ ZS ∧ (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧
        K₂ ⊔ X ≤ Subgroup.normalizer (U : Set G) ∧
        pCoreOf 2 KZ ≤ Subgroup.normalizer (U : Set G)

@[expose] def Gap432L34Twisted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G)
    (F : Type) [Field F] [Fintype F] (ZS K₂ R₂ X KZ Γ A B : Subgroup G)
    (α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
    (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))),
    Config43L34 G T M L n I H K t F ZS K₂ R₂ X KZ Γ A B α P →
    ∀ k : ℕ, (k = 1 ∨ k = 2) → ¬ IsTwAdjointSection k Γ A B α.ker F

theorem exists_mul_fixed_of_isPGroup [Finite G] {X B : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hX : IsPGroup p X) (hB : ¬ p ∣ Nat.card B) (hXB : X ≤ Subgroup.normalizer (B : Set G))
    {a : G} (ha : ∀ x ∈ X, a⁻¹ * (x * a * x⁻¹) ∈ B) :
    ∃ b ∈ B, ∀ x ∈ X, x * (a * b) * x⁻¹ = a * b := by
  have hmem : ∀ (x : ↥X) (b : ↥B), a⁻¹ * ((x : G) * (a * b) * (x : G)⁻¹) ∈ B := by
    intro x b
    have h1 := ha x x.2
    have h2 : (x : G) * b * (x : G)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hXB x.2) b).mp b.2
    have e : a⁻¹ * ((x : G) * (a * b) * (x : G)⁻¹) =
        (a⁻¹ * ((x : G) * a * (x : G)⁻¹)) * ((x : G) * b * (x : G)⁻¹) := by group
    rw [e]
    exact B.mul_mem h1 h2
  let _ : MulAction ↥X ↥B :=
    { smul := fun x b => ⟨a⁻¹ * ((x : G) * (a * b) * (x : G)⁻¹), hmem x b⟩
      one_smul := fun b => Subtype.ext (by
        show a⁻¹ * (((1 : ↥X) : G) * (a * b) * ((1 : ↥X) : G)⁻¹) = b
        simp)
      mul_smul := fun x y b => Subtype.ext (by
        show a⁻¹ * (((x * y : ↥X) : G) * (a * b) * ((x * y : ↥X) : G)⁻¹) =
          a⁻¹ * ((x : G) * (a * (a⁻¹ * ((y : G) * (a * b) * (y : G)⁻¹))) * (x : G)⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨b, hb⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card ↥B hB
  refine ⟨b, b.2, fun x hx => ?_⟩
  have h2 : a⁻¹ * (x * (a * (b : G)) * x⁻¹) = b := congrArg Subtype.val (hb ⟨x, hx⟩)
  calc x * (a * (b : G)) * x⁻¹ = a * (a⁻¹ * (x * (a * (b : G)) * x⁻¹)) := by group
    _ = a * b := by rw [h2]

omit [Group G] in
theorem not_three_dvd_card_of_isPGroup {B : Type} [Group B] [Finite B] (hB : IsPGroup 2 B) :
    ¬ 3 ∣ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hB
  rw [hm]
  intro h
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  omega

theorem false_of_config43L34 [Finite G] (hB414 : LemmaB414Corrected)
    (hgap : Gap432L34Twisted) {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G}
    {F : Type} [Field F] [Fintype F] {ZS K₂ R₂ X KZ Γ A B : Subgroup G}
    {α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}
    {P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))}
    (c : Config43L34 G T M L n I H K t F ZS K₂ R₂ X KZ Γ A B α P) : False := by
  have hK₂Γ : K₂ ≤ Γ := by
    rw [c.Γ_eq]
    exact c.K₂_le.trans le_sup_left
  have hXΓ : X ≤ Γ := by
    rw [c.Γ_eq]
    exact le_sup_right
  have hAΓ : A ≤ Γ := by
    rw [c.Γ_eq]
    exact (c.A_le.trans (pCoreOf_le 2 KZ)).trans le_sup_left
  obtain ⟨⟨k, hk3, hTw⟩, hdata⟩ := hB414 G Γ A B K₂ X F c.card_F c.Γ_A c.Γ_B c.B_lt c.sq c.comm
    c.irred hK₂Γ hXΓ α c.α_surj c.α_ker P c.P_max c.P_K₂ c.P_X c.αX_card c.αX_cent c.star
  have hk0 : k = 0 := by
    by_contra hk
    exact hgap G T M L n I H K t F ZS K₂ R₂ X KZ Γ A B α P c k (by omega) hTw
  obtain ⟨hU, -, -⟩ := hdata k hk3 hTw
  obtain ⟨hU1, l, hlK, hlX, v, hvA, hvX, hlv⟩ := hU hk0
  set N' := α.ker.map Γ.subtype with hN'
  have hN'mem : ∀ g ∈ N', ∃ γ : ↥Γ, α γ = 1 ∧ (γ : G) = g := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨γ, hγ, rfl⟩
  have hN'act : ∀ g ∈ N', ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ B := by
    intro g hg a ha
    obtain ⟨γ, hγ, rfl⟩ := hN'mem g hg
    exact (c.α_ker γ).mp hγ a ha
  have hN'2 : IsPGroup 2 N' := by
    refine (pCoreOf_isPGroup 2 KZ).to_le fun g hg => ?_
    obtain ⟨γ, hγ, rfl⟩ := hN'mem g hg
    exact c.α_ker_le γ hγ
  have hN'conj : ∀ γ ∈ Γ, ∀ g ∈ N', γ * g * γ⁻¹ ∈ N' := by
    intro γ hγ g hg
    obtain ⟨δ, hδ, rfl⟩ := hN'mem g hg
    refine Subgroup.mem_map.mpr ⟨⟨γ, hγ⟩ * δ * ⟨γ, hγ⟩⁻¹, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, hδ, mul_one, map_inv, mul_inv_cancel]
  have hN'norm : Γ ≤ Subgroup.normalizer (N' : Set G) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hN'conj γ hγ g hg, fun hg => ?_⟩
    have := hN'conj γ⁻¹ (Γ.inv_mem hγ) _ hg
    simpa [mul_assoc] using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [c.X_card, pow_one])
  have hB2 : IsPGroup 2 B :=
    (pCoreOf_isPGroup 2 KZ).to_le (c.B_lt.le.trans c.A_le)
  have hB3 : ¬ 3 ∣ Nat.card B := not_three_dvd_card_of_isPGroup hB2
  have hKN3 : ¬ 3 ∣ Nat.card ↥(K₂ ⊓ N') := not_three_dvd_card_of_isPGroup (hN'2.to_le inf_le_right)
  have hXB : X ≤ Subgroup.normalizer (B : Set G) := hXΓ.trans c.Γ_B
  have hXKN : X ≤ Subgroup.normalizer ((K₂ ⊓ N' : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (c.X_K₂ hx) (hN'norm (hXΓ hx))
  have hdecL : ∀ l ∈ K₂, IsCentMod X N' l →
      ∃ m ∈ K₂ ⊓ N', l * m ∈ K₂ ⊓ Subgroup.centralizer (X : Set G) := by
    intro l hl hlX
    have ha : ∀ x ∈ X, l⁻¹ * (x * l * x⁻¹) ∈ K₂ ⊓ N' := by
      intro x hx
      refine ⟨K₂.mul_mem (K₂.inv_mem hl)
        ((Subgroup.mem_normalizer_iff.mp (c.X_K₂ hx) l).mp hl), ?_⟩
      have h1 : x * l * x⁻¹ * l⁻¹ ∈ N' := by
        have := N'.inv_mem (hlX x hx)
        simpa [mul_assoc] using this
      have h2 := hN'conj l⁻¹ (Γ.inv_mem (hK₂Γ hl)) _ h1
      have e : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
      rwa [e] at h2
    obtain ⟨m, hm, hfix⟩ := exists_mul_fixed_of_isPGroup hX3 hKN3 hXKN ha
    refine ⟨m, hm, K₂.mul_mem hl hm.1, ?_⟩
    show l * m ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hfix x hx
    calc x * (l * m) = x * (l * m) * x⁻¹ * x := by group
      _ = l * m * x := by rw [this]
  have hdecV : ∀ v ∈ A, IsFixedMod X B v →
      ∃ b ∈ B, v * b ∈ A ⊓ Subgroup.centralizer (X : Set G) := by
    intro v hv hvX
    have ha : ∀ x ∈ X, v⁻¹ * (x * v * x⁻¹) ∈ B := by
      intro x hx
      have h2 := (Subgroup.mem_normalizer_iff.mp (c.Γ_B (Γ.inv_mem (hAΓ hv))) _).mp (hvX x hx)
      have e : v⁻¹ * (x * v * x⁻¹ * v⁻¹) * v⁻¹⁻¹ = v⁻¹ * (x * v * x⁻¹) := by group
      rwa [e] at h2
    obtain ⟨b, hb, hfix⟩ := exists_mul_fixed_of_isPGroup hX3 hB3 hXB ha
    refine ⟨b, hb, A.mul_mem hv (c.B_lt.le hb), ?_⟩
    show v * b ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hfix x hx
    calc x * (v * b) = x * (v * b) * x⁻¹ * x := by group
      _ = v * b * x := by rw [this]
  have hcommN : ∀ l ∈ Γ, ∀ m ∈ N', ∀ w ∈ A,
      (l * m) * w * (l * m)⁻¹ * w⁻¹ ∈ B ↔ l * w * l⁻¹ * w⁻¹ ∈ B := by
    intro l hl m hm w hw
    have e : (l * m) * w * (l * m)⁻¹ * w⁻¹ =
        (l * (m * w * m⁻¹ * w⁻¹) * l⁻¹) * (l * w * l⁻¹ * w⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem_cancel_left _
      ((Subgroup.mem_normalizer_iff.mp (c.Γ_B hl) _).mp (hN'act m hm w hw))
  have hcommB : ∀ l ∈ Γ, ∀ w ∈ A, ∀ b ∈ B,
      l * (w * b) * l⁻¹ * (w * b)⁻¹ ∈ B ↔ l * w * l⁻¹ * w⁻¹ ∈ B := by
    intro l hl w hw b hb
    have e : l * (w * b) * l⁻¹ * (w * b)⁻¹ =
        (l * w * l⁻¹ * w⁻¹) * (w * (l * b * l⁻¹ * b⁻¹) * w⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem_cancel_right _ ?_
    refine (Subgroup.mem_normalizer_iff.mp (c.Γ_B (hAΓ hw)) _).mp ?_
    exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (c.Γ_B hl) b).mp hb) (B.inv_mem hb)
  set A' := A ⊓ Subgroup.centralizer (X : Set G) with hA'
  set D := pCoreOf 2 K₂ ⊓ Subgroup.centralizer (X : Set G) with hD
  set CK := K₂ ⊓ Subgroup.centralizer (X : Set G) with hCK
  have hCKD : CK ≤ Subgroup.normalizer (D : Set G) := fun k hk =>
    mem_normalizer_inf (le_normalizer_pCoreOf 2 K₂ hk.1) (Subgroup.le_normalizer hk.2)
  have hCKA' : CK ≤ Subgroup.normalizer (A' : Set G) := fun k hk =>
    mem_normalizer_inf (c.Γ_A (hK₂Γ hk.1)) (Subgroup.le_normalizer hk.2)
  have hCKcent : ∀ k ∈ CK, IsCentMod X N' k := by
    intro k hk x hx
    have : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hk.2 x hx).symm
    rw [this, mul_inv_cancel_right, mul_inv_cancel]
    exact N'.one_mem
  by_cases hJ : A' ⊓ D ≤ B
  ·
    obtain ⟨m, hm, hlm⟩ := hdecL l hlK hlX
    obtain ⟨b, hb, hvb⟩ := hdecV v hvA hvX
    have h1 : (l * m) * v * (l * m)⁻¹ * v⁻¹ ∉ B := fun h =>
      hlv ((hcommN l (hK₂Γ hlK) m hm.2 v hvA).mp h)
    have h2 : (l * m) * (v * b) * (l * m)⁻¹ * (v * b)⁻¹ ∉ B := fun h =>
      h1 ((hcommB _ (hK₂Γ hlm.1) v hvA b hb).mp h)
    apply h2
    apply hJ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (c.Γ_A (hK₂Γ hlm.1)) _).mp hvb.1)
        (A.inv_mem hvb.1)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlm.2 hvb.2)
        (Subgroup.inv_mem _ hlm.2)) (Subgroup.inv_mem _ hvb.2)
    · exact c.D_comm _ ⟨c.O2KZ_le (c.A_le hvb.1), hvb.2⟩ _ hlm
  ·
    set J₀ := A' ⊓ D ⊔ B with hJ₀
    have hADB : A' ⊓ D ≤ Subgroup.normalizer (B : Set G) := fun d hd =>
      c.Γ_B (hAΓ hd.1.1)
    have hJ₀set : (J₀ : Set G) = ((A' ⊓ D : Subgroup G) : Set G) * (B : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right (A' ⊓ D) B hADB
    have hJ₀mem : ∀ j ∈ J₀, ∃ d ∈ A' ⊓ D, ∃ b ∈ B, j = d * b := by
      intro j hj
      have hj' : j ∈ ((A' ⊓ D : Subgroup G) : Set G) * (B : Set G) := by
        rw [← hJ₀set]
        exact hj
      obtain ⟨d, hd, b, hb, rfl⟩ := hj'
      exact ⟨d, hd, b, hb, rfl⟩
    have hlt : B < J₀ := lt_of_le_of_ne le_sup_right fun h => hJ (h ▸ le_sup_left)
    have hsub : ∀ j ∈ J₀, j ∈ A ∧ IsFixedMod X B j := by
      intro j hj
      obtain ⟨d, hd, b, hb, rfl⟩ := hJ₀mem j hj
      refine ⟨A.mul_mem hd.1.1 (c.B_lt.le hb), fun x hx => ?_⟩
      have hdx : x * d * x⁻¹ = d := by
        have := Subgroup.mem_centralizer_iff.mp hd.1.2 x hx
        rw [this, mul_inv_cancel_right]
      have e : x * (d * b) * x⁻¹ * (d * b)⁻¹ = d * (x * b * x⁻¹ * b⁻¹) * d⁻¹ := by
        calc x * (d * b) * x⁻¹ * (d * b)⁻¹ = (x * d * x⁻¹) * (x * b * x⁻¹ * b⁻¹) * d⁻¹ := by
              group
          _ = d * (x * b * x⁻¹ * b⁻¹) * d⁻¹ := by rw [hdx]
      rw [e]
      refine (Subgroup.mem_normalizer_iff.mp (hADB hd) _).mp ?_
      exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXB hx) b).mp hb) (B.inv_mem hb)
    have hinv : ∀ l ∈ K₂, IsCentMod X N' l → ∀ j ∈ J₀, l * j * l⁻¹ ∈ J₀ := by
      intro l hl hlX j hj
      obtain ⟨m, hm, hlm⟩ := hdecL l hl hlX
      have hjA := (hsub j hj).1
      have h1 : m⁻¹ * j * m⁻¹⁻¹ * j⁻¹ ∈ B := hN'act m⁻¹ (N'.inv_mem hm.2) j hjA
      have h2 : m⁻¹ * j * m ∈ J₀ := by
        have e : m⁻¹ * j * m = (m⁻¹ * j * m⁻¹⁻¹ * j⁻¹) * j := by group
        rw [e]
        exact J₀.mul_mem ((le_sup_right : B ≤ A' ⊓ D ⊔ B) h1) hj
      obtain ⟨d, hd, b, hb, he⟩ := hJ₀mem _ h2
      have e : l * j * l⁻¹ = (l * m) * (m⁻¹ * j * m) * (l * m)⁻¹ := by group
      rw [e, he]
      have e2 : (l * m) * (d * b) * (l * m)⁻¹ =
          ((l * m) * d * (l * m)⁻¹) * ((l * m) * b * (l * m)⁻¹) := by group
      rw [e2]
      refine J₀.mul_mem ((le_sup_left : A' ⊓ D ≤ A' ⊓ D ⊔ B) ⟨?_, ?_⟩)
        ((le_sup_right : B ≤ A' ⊓ D ⊔ B) ?_)
      · exact (Subgroup.mem_normalizer_iff.mp (hCKA' hlm) d).mp hd.1
      · exact (Subgroup.mem_normalizer_iff.mp (hCKD hlm) d).mp hd.2
      · exact (Subgroup.mem_normalizer_iff.mp (c.Γ_B (hK₂Γ hlm.1)) b).mp hb
    obtain ⟨j, hj, hjB, hjfix⟩ := hU1 J₀ hlt hsub hinv
    obtain ⟨d, hd, b, hb, rfl⟩ := hJ₀mem j hj
    have hdB : d ∉ B := fun h => hjB (B.mul_mem h hb)
    have hcomm : ∀ k ∈ CK, k * d * k⁻¹ * d⁻¹ ∈ B ⊓ D := by
      intro k hk
      refine ⟨(hcommB k (hK₂Γ hk.1) d hd.1.1 b hb).mp (hjfix k hk.1 (hCKcent k hk)), ?_⟩
      exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCKD hk) d).mp hd.2) (D.inv_mem hd.2)
    have hBD : CK ≤ Subgroup.normalizer ((B ⊓ D : Subgroup G) : Set G) := fun k hk =>
      mem_normalizer_inf (c.Γ_B (hK₂Γ hk.1)) (hCKD hk)
    rcases c.D_irred (B ⊓ D) inf_le_right hBD with h0 | hD'
    · apply hdB
      have hd1 : d = 1 := by
        refine c.D_fix d hd.2 fun k hk => ?_
        have h3 := hcomm k hk
        rw [h0, Subgroup.mem_bot] at h3
        calc k * d * k⁻¹ = k * d * k⁻¹ * d⁻¹ * d := by group
          _ = d := by rw [h3, one_mul]
      rw [hd1]
      exact B.one_mem
    · have hdBD : d ∈ B ⊓ D := by
        rw [hD']
        exact hd.2
      exact hdB hdBD.1

@[expose] def Lemma43Upto : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      C41Case3 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K →
      T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥ →
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (ZS K₂ R₂ X KZ Γ A B : Subgroup G)
        (α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
        (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))),
        Config43L34 G T M L n I H K t F ZS K₂ R₂ X KZ Γ A B α P

theorem lemma43End_of (hUpto : Lemma43Upto) (hB414 : LemmaB414Corrected)
    (hgap : Gap432L34Twisted) : Lemma43End := by
  intro G _ _ T M L n I H K t sk hchar h41 h3 h134 hcent
  obtain ⟨F, _, _, ZS, K₂, R₂, X, KZ, Γ, A, B, α, P, c⟩ :=
    hUpto G T M L n I H K t sk hchar h41 h3 h134 hcent
  exact false_of_config43L34 hB414 hgap c

end CFSG.Quasithin.H13.Ch4
