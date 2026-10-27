module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal
public import CFSG.SignalizerFunctorTheorem.NonLocal.Unipotent
public import CFSG.SignalizerFunctorTheorem.NonLocal.LowerBound
public import CFSG.SignalizerFunctorTheorem.NonLocal.Faithful

public section

open Module Module.End CFSG.SignalizerFunctorTheorem.CatalogBridge
open scoped commutatorElement Matrix

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {H X : Type*} [Group H]
  [Group X]

theorem ProjData.nonLocalized_of_closing_gen [Finite H] [Nonempty ι] [Finite K] {r : ℕ}
    [Fact r.Prime] [CharP K r] (P : ProjData K ι H X) {Γ : Type*} [Group Γ] (φH : Γ →* H)
    (hdef : ∀ E : Subgroup X, IsPGroup r E →
      (∀ g : Γ, ∀ v ∈ E, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ E) → E = ⊥)
    (N : Subgroup Γ) (hsimple : IsSimpleGroup (P.π.comp (φH.comp N.subtype)).range)
    (hcent : ∀ x : X, (∀ n : N, x * P.π (φH n) = P.π (φH n) * x) → x = 1)
    (hclose : ∀ s : ℕ, s.Prime → s ≠ r → ∀ V : Subgroup X, V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ g : Γ, ∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V) →
      (∀ n ∈ N, (∀ v ∈ V, P.π (φH n) * v * (P.π (φH n))⁻¹ = v) → P.π (φH n) = 1) →
      (Nat.card V ≤ s ^ (Fintype.card ι - 1) ∨
        ∃ e : ℕ, e ≤ Fintype.card ι ∧ e ∣ Nat.card V ∧ Nat.card V ≤ e ^ 2) → False) :
    NonLocalized (P.π.comp φH).range := by
  classical
  have : Finite X := Finite.of_surjective P.π P.hπ
  apply nonLocalized_of_elemAbelian
  intro s E hs hE0 hEcomm hEexp hle
  have hnormE : ∀ g : Γ, ∀ v ∈ E, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ E := by
    intro g v hv
    have hmem : P.π (φH g) ∈ Subgroup.normalizer (E : Set X) := hle ⟨g, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hmem v).mp hv
  by_cases hsr : s = r
  · subst hsr
    refine hE0 (hdef E ?_ hnormE)
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  ·
    let S : Set (Subgroup X) := {V | V ≤ E ∧ V ≠ ⊥ ∧
      ∀ g : Γ, ∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V}
    have hSne : S.Nonempty := ⟨E, le_rfl, hE0, hnormE⟩
    obtain ⟨V, ⟨hVE, hV0, hVnorm⟩, hVmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min S hSne
    have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
      hEcomm x (hVE hx) y (hVE hy)
    have hVexp : ∀ v ∈ V, v ^ s = 1 := fun v hv => hEexp v (hVE hv)
    have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
    have hmin : ∀ V' : Subgroup X, V' ≤ V → V' ≠ ⊥ →
        (∀ g : Γ, ∀ v ∈ V', P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V') → V' = V := by
      intro V' hV'V hV'0 hV'norm
      by_contra hne
      exact hVmin V' ⟨hV'V.trans hVE, hV'0, hV'norm⟩ (lt_of_le_of_ne hV'V hne)
    have hfaithN : ∀ n ∈ N, (∀ v ∈ V, P.π (φH n) * v * (P.π (φH n))⁻¹ = v) →
        P.π (φH n) = 1 := by
      intro n hn hnV
      have := faithful_of_simple (P.π.comp (φH.comp N.subtype)) hsimple V hV0
        (by
          rintro c ⟨m, rfl⟩ v hv
          exact hVnorm m v hv)
        hcent ⟨n, hn⟩ hnV
      exact this
    have hup := P.card_le_of_minimal hs hsr φH V hVexp hVnorm hmin
    exact hclose s hs hsr V hV0 hVcomm hVexp hVnorm hfaithN hup

theorem ProjData.nonLocalized_of_closing_sub [Finite H] [Nonempty ι] [Finite K] {r : ℕ}
    [Fact r.Prime] [CharP K r] (P : ProjData K ι H X) {Γ : Type*} [Group Γ] (φH : Γ →* H)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ g : Γ, ∀ n ∈ W, (P.ρ (φH g) : Matrix ι ι K) *ᵥ n ∈ W) → W = ⊥ ∨ W = ⊤)
    (N : Subgroup Γ) (hsimple : IsSimpleGroup (P.π.comp (φH.comp N.subtype)).range)
    (hcent : ∀ x : X, (∀ n : N, x * P.π (φH n) = P.π (φH n) * x) → x = 1)
    (hclose : ∀ s : ℕ, s.Prime → s ≠ r → ∀ V : Subgroup X, V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ g : Γ, ∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V) →
      (∀ n ∈ N, (∀ v ∈ V, P.π (φH n) * v * (P.π (φH n))⁻¹ = v) → P.π (φH n) = 1) →
      (Nat.card V ≤ s ^ (Fintype.card ι - 1) ∨
        ∃ e : ℕ, e ≤ Fintype.card ι ∧ e ∣ Nat.card V ∧ Nat.card V ≤ e ^ 2) → False) :
    NonLocalized (P.π.comp φH).range :=
  P.nonLocalized_of_closing_gen φH (fun E hE hnorm => P.eq_bot_of_isPGroup φH hirr E hE hnorm) N
    hsimple hcent hclose

theorem ProjData.nonLocalized_of_closing [Finite H] [Nonempty ι] [Finite K] {r : ℕ}
    [Fact r.Prime] [CharP K r] (P : ProjData K ι H X) {Γ : Type*} [Group Γ] (φH : Γ →* H)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ g : Γ, ∀ n ∈ W, (P.ρ (φH g) : Matrix ι ι K) *ᵥ n ∈ W) → W = ⊥ ∨ W = ⊤)
    (hsimple : IsSimpleGroup (P.π.comp φH).range)
    (hcent : ∀ x : X, (∀ g : Γ, x * P.π (φH g) = P.π (φH g) * x) → x = 1)
    (hclose : ∀ s : ℕ, s.Prime → s ≠ r → ∀ V : Subgroup X, V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ g : Γ, ∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V) →
      (∀ g : Γ, (∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ = v) → P.π (φH g) = 1) →
      (Nat.card V ≤ s ^ (Fintype.card ι - 1) ∨
        ∃ e : ℕ, e ≤ Fintype.card ι ∧ e ∣ Nat.card V ∧ Nat.card V ≤ e ^ 2) → False) :
    NonLocalized (P.π.comp φH).range := by
  have hrange : (P.π.comp (φH.comp (⊤ : Subgroup Γ).subtype)).range = (P.π.comp φH).range := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
  refine P.nonLocalized_of_closing_sub φH hirr ⊤ (by rw [hrange]; exact hsimple)
    (fun x hx => hcent x fun g => hx ⟨g, Subgroup.mem_top g⟩) ?_
  intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaithN hup
  exact hclose s hs hsr V hV0 hVcomm hVexp hVnorm
    (fun g hg => hfaithN g (Subgroup.mem_top g) hg) hup

theorem ProjData.nonLocalized_of_heisenberg [Finite H] [Nonempty ι] [Finite K] {r : ℕ}
    [Fact r.Prime] [CharP K r] (P : ProjData K ι H X) {Γ : Type*} [Group Γ] (φH : Γ →* H)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ g : Γ, ∀ n ∈ W, (P.ρ (φH g) : Matrix ι ι K) *ᵥ n ∈ W) → W = ⊥ ∨ W = ⊤)
    (hsimple : IsSimpleGroup (P.π.comp φH).range)
    (hcent : ∀ x : X, (∀ g : Γ, x * P.π (φH g) = P.π (φH g) * x) → x = 1)
    (A Z : Subgroup Γ) [Finite A] (hA : IsMulCommutative A) (hArp : IsPGroup r A) (hZA : Z ≤ A)
    {ι' : Type*} [Finite ι'] (y : ι' → Γ) (hcomm : ∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z)
    (hZnt : ∃ z ∈ Z, P.π (φH z) ≠ 1)
    (hdist : ∀ (s : ℕ), s.Prime → ∀ (F : Type) [Field F] [CharP F s], ∀ ξ : Γ → F,
      (∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z') → (∀ z ∈ Z, ξ z ≠ 0) →
      (∃ z ∈ Z, ξ z ≠ 1) → ∀ i j, i ≠ j → ∃ a ∈ A, ξ ⁅(y i)⁻¹, a⁆ ≠ ξ ⁅(y j)⁻¹, a⁆)
    (hclose : ∀ s : ℕ, s.Prime → s ≠ r → ∀ V : Subgroup X, V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ g : Γ, ∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V) →
      (∀ g : Γ, (∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ = v) → P.π (φH g) = 1) →
      s ^ Nat.card ι' ≤ Nat.card V →
      (Nat.card V ≤ s ^ (Fintype.card ι - 1) ∨
        ∃ e : ℕ, e ≤ Fintype.card ι ∧ e ∣ Nat.card V ∧ Nat.card V ≤ e ^ 2) → False) :
    NonLocalized (P.π.comp φH).range := by
  classical
  have : Finite X := Finite.of_surjective P.π P.hπ
  have hr : r.Prime := Fact.out
  refine P.nonLocalized_of_closing φH hirr hsimple hcent ?_
  intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hup
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  have hZact : ∃ z ∈ Z, ∃ v ∈ V, (P.π.comp φH) z * v * ((P.π.comp φH) z)⁻¹ ≠ v := by
    obtain ⟨z, hz, hz1⟩ := hZnt
    refine ⟨z, hz, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hz1 (hfaith z hcon)
  have hlow : s ^ Nat.card ι' ≤ Nat.card V :=
    pow_le_card_of_heisenberg (P.π.comp φH) V hr hs (Ne.symm hsr) hVexp hVnorm A Z hA hArp hZA y
      hcomm hZact (fun F _ _ ξ h1 h2 h3 => hdist s hs F ξ h1 h2 h3)
  exact hclose s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hlow hup

end CFSG.SignalizerFunctorTheorem.NonLocal
