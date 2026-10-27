module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.II

variable {G : Type} [Group G] [Finite G]

@[expose] def Plane2 {H M : Subgroup G} (δ l : Geo H M) : Subgroup G :=
  ⁅⁅Vn δ, stab δ ⊓ stab l⁆, stab δ ⊓ stab l⁆ ⊔ Zv δ

@[expose] def That2 {H M : Subgroup G} (δ l : Geo H M) : Subgroup G :=
  cSecIn (stab δ ⊓ stab l) (Zv δ) (Plane2 δ l)

@[expose] def CommonHyp {H M : Subgroup G} (β : Geo H M) (K : Subgroup G) : Prop :=
  stab β ≤ Subgroup.normalizer (K : Set G) ∧ Vn β ≤ K ∧ K ≤ Wb β ∧
    ∀ l ∈ nbrs β, K ≤ Wl l ∧ K.relIndex (Wl l) = 2 ∧ ∀ δ ∈ nbrs l, δ ≠ β → ¬ Vn δ ≤ K

@[expose] def NbarFull (H M : Subgroup G) : Prop :=
  ∀ δ l ρ : Geo H M, vtype δ = false → l ∈ nbrs δ → l ∈ nbrs ρ → ρ ≠ δ →
    stab ρ ⊓ stab l ≤ (Qv δ ⊓ Qv l) ⊔ Qv ρ

@[expose] def NbarThat (H M : Subgroup G) : Prop :=
  ∀ δ l ρ : Geo H M, vtype δ = false → l ∈ nbrs δ → l ∈ nbrs ρ → ρ ≠ δ →
    That2 ρ l ≤ (Qv δ ⊓ Qv l) ⊔ Qv ρ

@[expose] def NbarT (H M : Subgroup G) : Prop :=
  ∀ δ l ρ : Geo H M, vtype δ = false → l ∈ nbrs δ → l ∈ nbrs ρ → ρ ≠ δ →
    (Qv δ ⊓ Qv l) ⊔ Qv ρ ≤ That2 ρ l

@[expose] def ThatFacts (H M : Subgroup G) : Prop :=
  ∀ δ l : Geo H M, vtype δ = false → l ∈ nbrs δ →
    Qv δ ≤ That2 δ l ∧ That2 δ l ≤ stab δ ⊓ stab l ∧
      (That2 δ l).relIndex (stab δ ⊓ stab l) = 2

@[expose] def ZvBlock (H M : Subgroup G) : Prop :=
  ∀ δ l l' : Geo H M, vtype δ = false → l ∈ nbrs δ → l' ∈ nbrs δ →
    (Zv l = Zv l' ↔ S34.SameBlock δ l l')

@[expose] def ZvInf (H M : Subgroup G) : Prop :=
  ∀ δ : Geo H M, vtype δ = false → ∀ x ∈ stab δ,
    (∀ l ∈ nbrs δ, x ∈ Subgroup.normalizer (Zv l : Set G)) → x ∈ Qv δ

@[expose] def RkZvEq (H M : Subgroup G) : Prop :=
  ∀ δ : Geo H M, vtype δ = false → ∀ v ∈ stab δ,
    secIdx (Subgroup.zpowers v) (Zv δ) (Vn δ) = S34.rk δ v

@[expose] def PDCrit (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, S34.PD β α' → ∃ α : Geo H M, vtype α = true ∧ IsCritData α β α'

@[expose] def Claim3a (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, S34.PD β α' → Back H M β α' m γ' →
    ⁅Vn β, Vn α'⁆ ≠ ⊥ ∧ ¬ ⁅Vn β, Vn α'⁆ ≤ Zv m

@[expose] def Claim3 (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, S34.PD β α' → Back H M β α' m γ' → Wb β ⊓ stab m ≤ stab α'

@[expose] def ClaimS6 (H M : Subgroup G) : Prop :=
  ∀ β : Geo H M, vtype β = false → 4 ≤ (Kb β).relIndex (Qv β)

@[expose] def ClaimTT (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, S34.PD β α' → Back H M β α' m γ' → HasTransp β α' →
    Vn β ≤ That2 α' m

@[expose] def Claim9T (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, S34.PD β α' → Back H M β α' m γ' → Vn β ≤ That2 α' m →
    (Wb β ⊓ stab m).relIndex (Wb β) ≤ 2

@[expose] def NoTrivialAct (H M : Subgroup G) : Prop :=
  ∀ β : Geo H M, vtype β = false → ∀ x ∈ stab β, (∀ w ∈ Wb β, ⁅x, w⁆ ∈ Vn β) → x ∈ Qv β

@[expose] def RCent (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, S34.PD β α' → Back H M β α' m γ' → Vn β ≤ That2 α' m →
    ∀ r ∈ ⁅Vn β, Vn α'⁆, ∀ q ∈ That2 α' m, ⁅q, r⁆ ∈ Zv α'

@[expose] def Lemma7s (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, S34.PD β α' → HasTransp β α' → Zv α' ≤ Vn β →
    ∀ x ∈ Vn α', x ∉ Qv β → ∀ K : Subgroup G, Vn β ≤ K → K ≤ Wb β → K.relIndex (Wb β) ≤ 2 →
      (∀ h ∈ K, ⁅h, x⁆ ∈ Vn β) → ¬ Wb β ≤ stab α' → False

@[expose] def Step1 (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, S34.PD β α' → Back H M β α' m γ' → HasTransp β α' →
    Vn β ≤ That2 α' m → (∀ w ∈ Wb β, ∀ z ∈ Zv α', ⁅w, z⁆ = 1) → ¬ Wb β ≤ stab m →
      NbarFull H M

@[expose] def Step21 (H M : Subgroup G) : Prop :=
  NbarFull H M → ∀ β l δ σ : Geo H M, vtype β = false → l ∈ nbrs β → δ ∈ nbrs l → σ ∈ nbrs l →
    δ ≠ β → σ ≠ β → δ ≠ σ → (Vn β).relIndex ((Vn δ ⊔ Vn β) ⊓ (Vn σ ⊔ Vn β)) ≤ 2

@[expose] def Step2L (H M : Subgroup G) : Prop :=
  NbarFull H M → ∀ β : Geo H M, vtype β = false → ∀ x ∈ stab β, x ∉ Qv β → x ^ 2 ∈ Qv β →
    ∀ K₀ : Subgroup G, Vn β ≤ K₀ → K₀ ≤ Wb β → K₀.relIndex (Wb β) ≤ 2 →
      (∀ h ∈ K₀, ⁅h, x⁆ ∈ Vn β) → ∃ K : Subgroup G, CommonHyp β K ∧ K ≤ K₀

@[expose] def Step3 (H M : Subgroup G) : Prop :=
  NbarFull H M → ∀ β : Geo H M, vtype β = false → ∀ x ∈ stab β, x ∉ Qv β →
    ∀ K : Subgroup G, CommonHyp β K → (∀ h ∈ K, ⁅h, x⁆ ∈ Vn β) → False

@[expose] def Claim10A (H M : Subgroup G) : Prop :=
  (∀ δ δ' : Geo H M, ¬ Lam δ δ') → ∀ α β α' m γ' : Geo H M, IsCritData α β α' →
    vtype α = true → Back H M β α' m γ' → HasTransp β α' → Vn β ≤ That2 α' m →
      ¬ Wl α ≤ Qv γ' → False

@[expose] def Claim10B (H M : Subgroup G) : Prop :=
  (∀ δ δ' : Geo H M, ¬ Lam δ δ') → ∀ α β α' m γ' : Geo H M, IsCritData α β α' →
    vtype α = true → Back H M β α' m γ' → HasTransp β α' → Vn β ≤ That2 α' m →
      Wl α ≤ Qv γ' → Vn α' ≤ Qv β → False

@[expose] def Claim10C (H M : Subgroup G) : Prop :=
  (∀ δ δ' : Geo H M, ¬ Lam δ δ') → ∀ α β α' m γ' : Geo H M, IsCritData α β α' →
    vtype α = true → Back H M β α' m γ' → HasTransp β α' → Vn β ≤ That2 α' m →
      Wl α ≤ Qv γ' → ¬ Vn α' ≤ Qv β → False

@[expose] def Claim10Sym (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, Lam β α' → Lam α' β

@[expose] def WbSec7 (H M : Subgroup G) : Prop :=
  7 ≤ bMin H M → ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β)

@[expose] def Lem81II (H M : Subgroup G) : Prop :=
  ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β) →
    ∀ y ∈ stab β, y ∉ Qv β → secIdx (Subgroup.zpowers y) (Vn β) (Wb β) = 2 →
      ∃ E : Subgroup G, stab β ≤ Subgroup.normalizer (E : Set G) ∧ Vn β ≤ E ∧ E ≤ Wb β ∧
        ⁅E, Lr β⁆ ≤ Vn β ∧ IsOrthSec (stab β) E (Wb β) ∧
        secIdx (Subgroup.zpowers y) (Vn β) E = 1 ∧ secIdx (Subgroup.zpowers y) E (Wb β) = 2

@[expose] def Lem191 (H M : Subgroup G) : Prop :=
  ∀ β : Geo H M, vtype β = false → ∀ E : Subgroup G,
    stab β ≤ Subgroup.normalizer (E : Set G) → Vn β ≤ E → E ≤ Wb β → ⁅E, Lr β⁆ ≤ Vn β →
      IsOrthSec (stab β) E (Wb β) → False

@[expose] def NoTransvII (H M : Subgroup G) : Prop :=
  ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β) →
    ∀ y ∈ stab β, y ∉ Qv β → secIdx (Subgroup.zpowers y) (Vn β) (Wb β) ≠ 2

@[expose] def Lem192 (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, Lam β α' → Back H M β α' m γ' →
    Zv α' ≤ Wb β ∧ (Wb β ⊓ stab α').relIndex (Wb β) = 2 ∧ ∀ l ∈ Delta0 β α', Wl l ≤ stab α'

@[expose] def Claim8aC (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, Lam β α' → Back H M β α' m γ' → ∀ l ∈ Delta0 β α',
    ∃ x ∈ Vn α', x ∉ Subgroup.normalizer (Zv l : Set G) ∧
      secIdx (Subgroup.zpowers x) (Zv β) (Vn β) = 2 ∧ ∀ w ∈ Wl l, ⁅w, x⁆ ∈ Zv α' ⊔ Vn β

@[expose] def Step2C (H M : Subgroup G) : Prop :=
  NbarFull H M → ∀ β : Geo H M, vtype β = false → (∀ u ∈ Wb β, ∀ v ∈ Wb β, u * v = v * u) →
    ∀ Zt : Subgroup G, Nat.card Zt = 2 → Zt ≤ Wb β → ¬ Zt ≤ Vn β →
      ∀ l ∈ nbrs β, ∀ x ∈ stab β, x ∉ Subgroup.normalizer (Zv l : Set G) →
        secIdx (Subgroup.zpowers x) (Zv β) (Vn β) = 2 → (∀ w ∈ Wl l, ⁅w, x⁆ ∈ Zt ⊔ Vn β) →
          ∃ K : Subgroup G, CommonHyp β K ∧ ∀ h ∈ K, ⁅h, x⁆ ∈ Vn β

@[expose] def ThmBa (H M : Subgroup G) : Prop :=
  bMin H M = 5 → ∀ β la γ lb α' : Geo H M, Lam β α' → Lam α' β → la ∈ nbrs β → γ ∈ nbrs la →
    Back H M β α' lb γ → ∃ r ∈ ⁅Vn β, Vn α'⁆, r ∉ Zv la ∧ r ∉ Zv lb

@[expose] def SuborbitDich (H M : Subgroup G) : Prop :=
  ∀ γ la lb : Geo H M, vtype γ = false → la ∈ nbrs γ → lb ∈ nbrs γ →
    ¬ S34.SameBlock γ la lb →
      (That2 γ la ⊔ That2 γ lb).relIndex (stab γ) = 1 ∨
        (That2 γ la ⊔ That2 γ lb).relIndex (stab γ) = 10

@[expose] def NbarDich (H M : Subgroup G) : Prop := NbarFull H M ∨ NbarT H M

@[expose] def ThmBcase23 (H M : Subgroup G) : Prop :=
  Claim6b H M → ∀ γ la lb β α' : Geo H M, vtype γ = false → la ∈ nbrs γ → lb ∈ nbrs γ →
    β ∈ nbrs la → β ≠ γ → α' ∈ nbrs lb → α' ≠ γ → ¬ S34.SameBlock γ la lb →
    (NbarFull H M ∨ (That2 γ la ⊔ That2 γ lb).relIndex (stab γ) = 1) →
    ∀ r ∈ Vn β ⊓ Vn α', r ∉ Zv lb → (∀ v ∈ Vn γ, ⁅r, v⁆ = 1) →
      (∀ q ∈ Qv lb ⊓ That2 α' lb, ⁅q, r⁆ ∈ Zv α') →
      (∀ q ∈ Qv la ⊓ That2 β la, ⁅q, r⁆ ∈ Zv β) → False

@[expose] def ThmBcase4 (H M : Subgroup G) : Prop :=
  NbarT H M → ∀ γ la lb β α' : Geo H M, vtype γ = false → la ∈ nbrs γ → lb ∈ nbrs γ →
    β ∈ nbrs la → β ≠ γ → α' ∈ nbrs lb → α' ≠ γ → ¬ S34.SameBlock γ la lb →
    (That2 γ la ⊔ That2 γ lb).relIndex (stab γ) = 10 →
    ∀ r ∈ Vn β ⊓ Vn α', r ∉ Zv la → r ∉ Zv lb → (∀ v ∈ Vn γ, ⁅r, v⁆ = 1) →
      (∀ q ∈ Qv lb ⊓ That2 α' lb, ⁅q, r⁆ ∈ Zv α') →
      (∀ q ∈ Qv la ⊓ That2 β la, ⁅q, r⁆ ∈ Zv β) → False

end S35.II

end F53.Stellmacher

end CFSG.Quasithin
