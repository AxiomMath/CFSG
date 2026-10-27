
module

public import CFSG.Quasithin.Background.C3Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Schemes

variable {G : Type} [Group G]

@[expose] def IsMatrixBlockTypeWith (L : Subgroup G) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] (H : Subgroup (Matrix.GeneralLinearGroup ι F)) (α : ↥L →* ↥H)
    (β : ↥(blockU L) →* Multiplicative (ι → F)) : Prop :=
  Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧ Function.Surjective β ∧
    β.ker = (blockZ L).subgroupOf (blockU L) ∧
    ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α ℓ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (β u))

theorem isMatrixBlockType_iff_exists_with (L : Subgroup G) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] (H : Subgroup (Matrix.GeneralLinearGroup ι F)) :
    IsMatrixBlockType L H ↔ ∃ (α : ↥L →* ↥H) (β : ↥(blockU L) →* Multiplicative (ι → F)),
      IsMatrixBlockTypeWith L H α β := by
  constructor
  · rintro ⟨α, hα, hker, β, hβ, hβker, hβeq⟩
    exact ⟨α, β, hα, hker, hβ, hβker, hβeq⟩
  · rintro ⟨α, β, hα, hker, hβ, hβker, hβeq⟩
    exact ⟨α, hα, hker, β, hβ, hβker, hβeq⟩

@[expose] def IsNaturalSectionWith (A V Z : Subgroup G) (N : Subgroup ↥A) {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] (Γ : Subgroup (Matrix.GeneralLinearGroup ι F))
    (α : ↥A →* ↥Γ) (β : ↥V →* Multiplicative (ι → F)) : Prop :=
  A ≤ Subgroup.normalizer (V : Set G) ∧ Function.Surjective α ∧ α.ker = N ∧
    Function.Surjective β ∧ β.ker = Z.subgroupOf V ∧
    ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (β u))

theorem isNaturalSection_iff_exists_with (A V Z : Subgroup G) (N : Subgroup ↥A) {ι : Type}
    [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) :
    IsNaturalSection A V Z N Γ ↔ ∃ (α : ↥A →* ↥Γ) (β : ↥V →* Multiplicative (ι → F)),
      IsNaturalSectionWith A V Z N Γ α β := by
  constructor
  · rintro ⟨hA, α, hα, hker, β, hβ, hβker, hβeq⟩
    exact ⟨α, β, hA, hα, hker, hβ, hβker, hβeq⟩
  · rintro ⟨α, β, hA, hα, hker, hβ, hβker, hβeq⟩
    exact ⟨hA, α, hα, hker, β, hβ, hβker, hβeq⟩

end Schemes

section DirectSums

variable {G : Type} [Group G]

@[expose] def moduleAct {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] (dual : Bool)
    (g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F :=
  if dual then (((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F)).transpose
  else (g : Matrix ι ι F)

@[expose] def IsSumOfNaturalModulesVia (A V Z : Subgroup G) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} (α : ↥A →* ↥Γ)
    (dual : Bool) (k : ℕ) : Prop :=
  A ≤ Subgroup.normalizer (V : Set G) ∧ Z ≤ V ∧
    ∃ β : ↥V →* Multiplicative (Fin k → ι → F), Function.Surjective β ∧
      β.ker = Z.subgroupOf V ∧
      ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
        Multiplicative.toAdd (β v) i =
          (moduleAct dual (α a : Matrix.GeneralLinearGroup ι F)).mulVec
            (Multiplicative.toAdd (β u) i)

@[expose] def IsSumOfNaturalModules (A V Z : Subgroup G) (N : Subgroup ↥A) {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] (Γ : Subgroup (Matrix.GeneralLinearGroup ι F))
    (dual : Bool) (k : ℕ) : Prop :=
  ∃ α : ↥A →* ↥Γ, Function.Surjective α ∧ α.ker = N ∧ IsSumOfNaturalModulesVia A V Z α dual k

theorem isNaturalSection_iff_isSumOfNaturalModules_one {A V Z : Subgroup G} (N : Subgroup ↥A)
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) (hZ : Z ≤ V) :
    IsNaturalSection A V Z N Γ ↔ IsSumOfNaturalModules A V Z N Γ false 1 := by
  let e : Multiplicative (Fin 1 → ι → F) ≃* Multiplicative (ι → F) :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (ι → F))
  constructor
  · rintro ⟨hA, α, hα, hker, β, hβ, hβker, hβeq⟩
    refine ⟨α, hα, hker, hA, hZ, e.symm.toMonoidHom.comp β, ?_, ?_, ?_⟩
    · exact e.symm.surjective.comp hβ
    · rw [MonoidHom.ker_comp_of_injective β _ e.symm.injective, hβker]
    · intro a u v huv i
      have h := hβeq a u v huv
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa [moduleAct, e] using h
  · rintro ⟨α, hα, hker, hA, -, β, hβ, hβker, hβeq⟩
    refine ⟨hA, α, hα, hker, e.toMonoidHom.comp β, ?_, ?_, ?_⟩
    · exact e.surjective.comp hβ
    · rw [MonoidHom.ker_comp_of_injective β _ e.injective, hβker]
    · intro a u v huv
      have h := hβeq a u v huv 0
      simpa [moduleAct, e] using h

end DirectSums

section Alternating

variable {G : Type} [Group G]

@[expose] def IsAltNaturalSection (A V Z : Subgroup G) (N : Subgroup ↥A) (m : ℕ) : Prop :=
  A ≤ Subgroup.normalizer (V : Set G) ∧
    ∃ α : ↥A →* alternatingGroup (Fin m), Function.Surjective α ∧ α.ker = N ∧
      ∃ β : ↥V →* Multiplicative (AltHeart m), Function.Surjective β ∧
        β.ker = Z.subgroupOf V ∧
        ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
          ∀ x : ↥(evenWeight m), (QuotientAddGroup.mk x : AltHeart m) = Multiplicative.toAdd (β u) →
            (QuotientAddGroup.mk (permWeight m (α a : Equiv.Perm (Fin m)) x) : AltHeart m) =
              Multiplicative.toAdd (β v)

@[expose] def InducesTransposition (R K : Subgroup G) (m : ℕ) : Prop :=
  R ≤ Subgroup.normalizer (K : Set G) ∧
    ∃ α : ↥K →* alternatingGroup (Fin m), IsAltBlockTypeWith K m α ∧
      ∃ σ : Equiv.Perm (Fin m), σ.IsSwap ∧
        (∀ t : ↥(Subgroup.normalizer (K : Set G)), (t : G) ∈ R →
          ((∀ k : ↥K, α ((conjAct K t) k) = α k) ∨
            ∀ k : ↥K, ((α ((conjAct K t) k) : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
              σ * (α k : Equiv.Perm (Fin m)) * σ⁻¹)) ∧
        ∃ t : ↥(Subgroup.normalizer (K : Set G)), (t : G) ∈ R ∧
          ∀ k : ↥K, ((α ((conjAct K t) k) : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
            σ * (α k : Equiv.Perm (Fin m)) * σ⁻¹

end Alternating

section Lines

variable {G : Type} [Group G]

@[expose] def IsFLineVia (U V : Subgroup G) {ι : Type} {F : Type} [Field F]
    (β : ↥U →* Multiplicative (ι → F)) : Prop :=
  V ≤ U ∧ ∃ W : Submodule F (ι → F), Module.finrank F ↥W = 2 ∧
    ∀ u : ↥U, (u : G) ∈ V ↔ Multiplicative.toAdd (β u) ∈ W

end Lines

section C134

variable {G : Type} [Group G]

@[expose] def IsModO2Surj (L : Subgroup G) {H : Type} [Group H] (α : ↥L →* H) : Prop :=
  Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L

@[expose] def c134Q (G₀ L : Subgroup G) : Subgroup G := ⁅pCoreOf 2 G₀, L⁆

@[expose] def c134CQ (G₀ L : Subgroup G) : Subgroup G :=
  c134Q G₀ L ⊓ Subgroup.centralizer (L : Set G)

@[expose] def C134NotCentralizerCore (G₀ R : Subgroup G) : Prop :=
  ∀ S : Subgroup G, IsSylowTwoOf S G₀ → R ≤ S →
    R ≠ pCoreOf 2 (G₀ ⊓ Subgroup.centralizer (omegaOneCenterOf S : Set G))

@[expose] def IsC134Case1 (G₀ _R L : Subgroup G) : Prop :=
  IsSL3Block L ∧ ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    IsNaturalSection L (c134Q G₀ L) ⊥ (CFSG.pCore 2 ↥L) (StatedSL 3 F)

@[expose] def IsC134Case2 (G₀ R L : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false 2) ∧ C134NotCentralizerCore G₀ R

@[expose] def IsC134Case3 (G₀ R L : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      IsSumOfNaturalModulesVia L (centerOf (c134Q G₀ L)) ⊥ α false 1 ∧
      IsSumOfNaturalModulesVia L (c134Q G₀ L) (centerOf (c134Q G₀ L)) α true 2) ∧
    C134NotCentralizerCore G₀ R

@[expose] def IsC134Case4 (G₀ R L : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      IsE2 (2 * n) ↥(c134CQ G₀ L) ∧ c134CQ G₀ L ≤ centerOf G₀ ∧
      centerOf (c134Q G₀ L) = c134CQ G₀ L ⊔ ⁅centerOf (c134Q G₀ L), L⁆ ∧
      c134CQ G₀ L ⊓ ⁅centerOf (c134Q G₀ L), L⁆ = ⊥ ∧
      IsSumOfNaturalModulesVia L ⁅centerOf (c134Q G₀ L), L⁆ ⊥ α false 1 ∧
      IsSumOfNaturalModulesVia L (frattiniIn (c134Q G₀ L)) (centerOf (c134Q G₀ L)) α true 1 ∧
      IsSumOfNaturalModulesVia L (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G))
        (frattiniIn (c134Q G₀ L)) α true 2 ∧
      IsSumOfNaturalModulesVia L (c134Q G₀ L)
        (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G)) α false 2) ∧
    C134NotCentralizerCore G₀ R

@[expose] def IsC134Case5 (G₀ R L : Subgroup G) : Prop :=
  (∃ α : ↥L →* ↥(StatedSL 3 (ZMod 2)), IsModO2Surj L α ∧ Nat.card ↥(c134CQ G₀ L) = 2 ∧
      IsSumOfNaturalModulesVia L (c134Q G₀ L) (c134CQ G₀ L) α false 1) ∧
    ∀ S : Subgroup G, IsSylowTwoOf S G₀ → R ≤ S →
      omegaOneCenterOf S ≤ centerOf G₀ ∧
      ∃ (q : G) (G₁ : Subgroup G), q ∈ c134Q G₀ L ∧ q ∉ c134CQ G₀ L ∧
        (∀ g : G, g ∈ G₁ ↔ g ∈ G₀ ∧ g * q * g⁻¹ * q⁻¹ ∈ c134CQ G₀ L) ∧
        G₁.relIndex G₀ = 7 ∧ S ≤ G₁ ∧ R = pCoreOf 2 G₁

@[expose] def IsC134Case (i : ℕ) (G₀ R L : Subgroup G) : Prop :=
  match i with
  | 1 => IsC134Case1 G₀ R L
  | 2 => IsC134Case2 G₀ R L
  | 3 => IsC134Case3 G₀ R L
  | 4 => IsC134Case4 G₀ R L
  | 5 => IsC134Case5 G₀ R L
  | _ => False

end C134

section Consistency

variable {G : Type} [Group G]

theorem isMatrixBlockType_iff_isNaturalSection (L : Subgroup G) {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] (Γ : Subgroup (Matrix.GeneralLinearGroup ι F))
    (hL : L ≤ Subgroup.normalizer (blockU L : Set G)) :
    IsMatrixBlockType L Γ ↔ IsNaturalSection L (blockU L) (blockZ L) (CFSG.pCore 2 ↥L) Γ := by
  constructor
  · rintro ⟨α, hα, hker, β, hβ, hβker, hβeq⟩
    exact ⟨hL, α, hα, hker, β, hβ, hβker, hβeq⟩
  · rintro ⟨-, α, hα, hker, β, hβ, hβker, hβeq⟩
    exact ⟨α, hα, hker, β, hβ, hβker, hβeq⟩

theorem exists_isAltBlockTypeWith_iff_isAltNaturalSection (L : Subgroup G) (m : ℕ)
    (hL : L ≤ Subgroup.normalizer (blockU L : Set G)) :
    (∃ α : ↥L →* alternatingGroup (Fin m), IsAltBlockTypeWith L m α) ↔
      IsAltNaturalSection L (blockU L) (blockZ L) (CFSG.pCore 2 ↥L) m := by
  constructor
  · rintro ⟨α, hα, hker, β, hβ, hβker, hβeq⟩
    exact ⟨hL, α, hα, hker, β, hβ, hβker, hβeq⟩
  · rintro ⟨-, α, hα, hker, β, hβ, hβker, hβeq⟩
    exact ⟨α, hα, hker, β, hβ, hβker, hβeq⟩

end Consistency

end CFSG.Quasithin
