module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7

variable {G : Type} [Group G] [Finite G]

@[expose] def HypZ (H M : Subgroup G) : Prop :=
  ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ)

@[expose] def HypR (H M : Subgroup G) : Prop :=
  ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' → δ ≠ β →
    δ' ≠ β → δ' ≠ δ →
    Vn β ⊓ Vn δ = Vn β ⊓ Vn δ' ∧ Vn β ⊓ Vn δ = Vn δ ⊓ Vn δ' ∧
      stab l ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G)

@[expose] def AbstractPlaneLemma : Prop :=
  ∀ M : Model 5, M.Faithful → ∀ t : Perm (Fin 5), idx M t = 2 →
  ∀ π : M.W →* orth.W, Function.Surjective π →
    (∀ (σ : Perm (Fin 5)) (m : M.W), π (M.act σ m) = orth.act σ (π m)) →
  ∀ U : Subgroup M.W, IsInvSub M S5Syl U → (∀ u ∈ U, π u = 1 → u = 1) → Nat.card U = 4 →
    Subgroup.closure {m : M.W | ∃ σ : Perm (Fin 5), ∃ u ∈ U, m = M.act σ u} = ⊤ →
  ∀ f : M.W →* orth.W,
    (∀ σ : Perm (Fin 5), ∀ u ∈ U, ∃ u' ∈ U, f (M.act σ u) = orth.act σ (π u')) →
    (∃ σ0 : Perm (Fin 5), ∀ u ∈ U, f (M.act σ0 u) = 1) → f = 1

@[expose] def Lem81 (H M S : Subgroup G) : Prop :=
  Sit H M S → CaseI H M → Claim5b H M → Claim6b H M →
  ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β) →
  ∀ y ∈ stab β, y ∉ Qv β → secIdx (Subgroup.zpowers y) (Vn β) (Wb β) = 2 →
  ∃ E : Subgroup G, stab β ≤ Subgroup.normalizer (E : Set G) ∧ Vn β ≤ E ∧ E ≤ Wb β ∧
    ⁅E, Lr β⁆ ≤ Vn β ∧ IsOrthSec (stab β) E (Wb β) ∧
    secIdx (Subgroup.zpowers y) (Vn β) E = 1 ∧ secIdx (Subgroup.zpowers y) E (Wb β) = 2

@[expose] def KernelStruct (H M S : Subgroup G) : Prop :=
  Sit H M S →
  ∀ β : Geo H M, vtype β = false → ∀ E : Subgroup G,
    stab β ≤ Subgroup.normalizer (E : Set G) → Vn β ≤ E → E ≤ Wb β → IsOrthSec (stab β) E (Wb β) →
  ∀ y ∈ stab β, y ∉ Qv β → secIdx (Subgroup.zpowers y) (Vn β) E = 1 →
    secIdx (Subgroup.zpowers y) E (Wb β) = 2 →
  ∃ K : Subgroup G, stab β ≤ Subgroup.normalizer (K : Set G) ∧ Vn β ≤ K ∧ K ≤ E ∧
    (∀ l ∈ nbrs β, K ≤ Wl l ∧ Wl l ⊓ E = K) ∧ ∀ w ∈ Wb β, ∀ q ∈ Qv β, ⁅w, q⁆ ∈ K

structure WModule {H M : Subgroup G} {β : Geo H M} (c : Ch.Chart β) (K : Subgroup G)
    (l₀ : Geo H M) where
  mod : Model 5
  proj : ↥(Wb β) →* mod.W
  proj_surj : Function.Surjective proj
  proj_eq_one : ∀ w : ↥(Wb β), proj w = 1 ↔ (w : G) ∈ K
  proj_conj : ∀ (g : ↥(stab β)) (w : ↥(Wb β)) (h : (g : G) * (w : G) * (g : G)⁻¹ ∈ Wb β),
    mod.act (c.θ g) (proj w) = proj ⟨(g : G) * (w : G) * (g : G)⁻¹, h⟩
  faithful : mod.Faithful
  t : Perm (Fin 5)
  idx_t : idx mod t = 2
  π : mod.W →* orth.W
  π_surj : Function.Surjective π
  π_act : ∀ (σ : Perm (Fin 5)) (m : mod.W), π (mod.act σ m) = orth.act σ (π m)
  U : Subgroup mod.W
  U_eq : U = ((Wl l₀).subgroupOf (Wb β)).map proj
  inv : IsInvSub mod S5Syl U
  π_inj : ∀ u ∈ U, π u = 1 → u = 1
  card_U : Nat.card U = 4
  gen : Subgroup.closure {m : mod.W | ∃ σ : Perm (Fin 5), ∃ u ∈ U, m = mod.act σ u} = ⊤

@[expose] def WModuleExists (H M S : Subgroup G) : Prop :=
  Sit H M S → CaseI H M → HypZ H M → HypR H M → Claim6b H M →
  ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β) →
  ∀ (c : Ch.Chart β) (l₀ : Geo H M), l₀ ∈ nbrs β →
    ((stab β ⊓ stab l₀).subgroupOf (stab β)).map c.θ = S5Syl →
  ∀ E K : Subgroup G, stab β ≤ Subgroup.normalizer (E : Set G) → Vn β ≤ E → E ≤ Wb β →
    ⁅E, Lr β⁆ ≤ Vn β → IsOrthSec (stab β) E (Wb β) →
  ∀ y ∈ stab β, y ∉ Qv β → secIdx (Subgroup.zpowers y) (Vn β) (Wb β) = 2 →
    secIdx (Subgroup.zpowers y) (Vn β) E = 1 → secIdx (Subgroup.zpowers y) E (Wb β) = 2 →
  stab β ≤ Subgroup.normalizer (K : Set G) → Vn β ≤ K → K ≤ E →
    (∀ l ∈ nbrs β, K ≤ Wl l ∧ Wl l ⊓ E = K) → (∀ w ∈ Wb β, ∀ q ∈ Qv β, ⁅w, q⁆ ∈ K) →
  Nonempty (WModule c K l₀)

@[expose] def PM (H M : Subgroup G) : Prop :=
  ∀ γ : Geo H M, vtype γ = false → IsSec (stab γ) (Vn γ) (Wb γ) →
  ∀ y ∈ stab γ, y ∉ Qv γ → secIdx (Subgroup.zpowers y) (Vn γ) (Wb γ) = 2 →
  ∀ u ∈ stab γ, (∀ v ∈ Vn γ, ⁅u, v⁆ = 1) → (∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Vn γ) →
  (∀ μ ∈ nbrs γ, ∀ δ ∈ nbrs μ, δ ≠ γ → ∀ v ∈ Vn δ, ⁅v, u⁆ ∈ Vn γ ⊓ Vn δ) →
  (∃ μ₀ ∈ nbrs γ, ∀ w ∈ Wl μ₀, ⁅w, u⁆ = 1) → ∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Zv γ

@[expose] def Claim16d (H M : Subgroup G) : Prop :=
  ∀ γ μ δ : Geo H M, vtype γ = false → μ ∈ nbrs γ → δ ∈ nbrs μ → δ ≠ γ →
    ∀ u ∈ Kb γ, ∀ v ∈ Vn δ, ⁅v, u⁆ ∈ Vn γ ⊓ Vn δ

end S35.G7

end F53.Stellmacher

end CFSG.Quasithin
