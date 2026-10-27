module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Notation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G]

@[expose] def Back (H M : Subgroup G) (β α' m γ' : Geo H M) : Prop :=
  m ∈ nbrs α' ∧ γ' ∈ nbrs m ∧ dist β m + 1 = dist β α' ∧ dist β γ' + 1 = dist β m

@[expose] def ClaimR (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, S34.PD β α' → Back H M β α' m γ' →
    ⁅Vn β, Vn α'⁆ ≠ ⊥ ∧ ⁅Vn β, Vn α'⁆ ≤ Vn α' ⊓ Vn γ' ∧ ¬ ⁅Vn β, Vn α'⁆ ≤ Zv m

@[expose] def Claim9 (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, S34.PD β α' → Back H M β α' m γ' →
    (Wb β ⊓ stab m).relIndex (Wb β) ≤ 2

@[expose] def HasTransp {H M : Subgroup G} (β α' : Geo H M) : Prop :=
  ∃ v ∈ Vn β, v ∈ stab α' ∧ secIdx (Subgroup.zpowers v) (Zv α') (Vn α') = 2

@[expose] def Claim8a (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, S34.PD β α' → HasTransp β α' →
    ∃ A B : Subgroup G, A ≤ Vn α' ∧ B ≤ Vn α' ∧ A ⊔ B = Vn α' ∧ ⁅Vn β, A⁆ ≤ Zv α' ∧
      ⁅Wb β ⊓ stab α', B⁆ ≤ Zv α' ⊔ ⁅Vn β, B⁆ ∧
      ∀ l ∈ nbrs β, ¬ Zv l ≤ Qv α' → ⁅B, Zv l⁆ ≠ ⊥

@[expose] def Claim8b (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, S34.PD β α' → HasTransp β α' →
    (Wb β ⊓ stab α').relIndex (Wb β) ≤ 2 →
      Zv α' ≤ Wb β ∧ (Wb β ⊓ stab α').relIndex (Wb β) = 2

@[expose] def Claim7s (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, S34.PD β α' → ∀ x ∈ Vn α', x ∉ Qv β →
    ∀ _ : IsSec (stab β) (Vn β) (Wb β), secIdx (Subgroup.zpowers x) (Vn β) (Wb β) ≠ 2

@[expose] def Claim10 (H M : Subgroup G) : Prop :=
  (∃ δ δ' : Geo H M, Lam δ δ') ∧ ∀ δ δ' : Geo H M, Lam δ δ' → Lam δ' δ

@[expose] def Claim11 (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, Lam β α' → ¬ Vn α' ≤ Lr β ⊔ Qv β

@[expose] def Claim13 (H M : Subgroup G) : Prop := bMin H M ≠ 5

@[expose] def Claim14 (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, Lam β α' → ¬ Zv α' ≤ Wb β

@[expose] def Claim15a (H M : Subgroup G) : Prop :=
  ∀ β α' m γ' : Geo H M, Lam β α' → Back H M β α' m γ' → ¬ (Wb β ⊓ stab m ≤ stab α')

@[expose] def Claim15c (H M : Subgroup G) : Prop :=
  ∀ β : Geo H M, vtype β = false → ⁅Wb β, Kb β⁆ ≤ Vn β

@[expose] def ClaimLP (H M : Subgroup G) : Prop :=
  ∃ β α' : Geo H M, S34.PD β α' ∧ HasTransp β α'

@[expose] def Claim16a (H M : Subgroup G) : Prop :=
  ∀ β α' : Geo H M, Lam β α' → HasTransp β α'

@[expose] def ClaimT (H M : Subgroup G) : Prop :=
  ∀ l : Geo H M, vtype l = true → ∀ x ∈ stab l, x ∉ Qv l →
    4 ≤ secIdx (Subgroup.zpowers x) (Zv l) (Wl l)

@[expose] def Claim6a (H M : Subgroup G) : Prop :=
  ∀ β l : Geo H M, vtype β = false → l ∈ nbrs β → ¬ ⁅Qv β, Lr β⁆ ≤ Qv l

@[expose] def Claim6b (H M : Subgroup G) : Prop :=
  ∀ (β l δ : Geo H M) (E : Subgroup G), vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → δ ≠ β →
    stab β ≤ Subgroup.normalizer (E : Set G) → Vn β ≤ E → E ≤ Wb β → ⁅E, Lr β⁆ ≤ Vn β →
      Vn δ ⊓ E = Vn δ ⊓ Vn β

@[expose] def Claim5b (H M : Subgroup G) : Prop :=
  ∀ (β l δ : Geo H M) (E F B : Subgroup G), vtype β = false → l ∈ nbrs β → l ∈ nbrs δ →
    δ ≠ β → stab β ≤ Subgroup.normalizer (E : Set G) → stab β ≤ Subgroup.normalizer (F : Set G) →
    Vn β ≤ E → E ≤ F → F ≤ Wb β → IsOrthSec (stab β) E F →
    (∀ w ∈ Wb β, (∀ g ∈ stab β, g * w * g⁻¹ * w⁻¹ ∈ E) → w ∈ E) →
    B ≤ Vn δ → Qv l ≤ Subgroup.normalizer (B : Set G) → ⁅B, Lr β⁆ ≤ F → B ≤ F

end S35

end F53.Stellmacher

end CFSG.Quasithin
