module

public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Smith81.Sec1Main
public import CFSG.RankThree.GF2n.Smith81.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec34Symm

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Lin22Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → CaseD2 M Q Z B →
    ¬ NoA2 Q Z (LB M Q B) → ∃ V₁ V₂ : Subgroup G, LinSetup M Q Z B 2 V₁ V₂

@[expose] def Lin31Prop (M Q Z B : Subgroup G) (n : ℕ) : Prop :=
  ∃ V₁ V₂ : Subgroup G, LinSetup M Q Z B n V₁ V₂ ∧ B ≤ V₁ ∧
    ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)

theorem Lin31Prop.sq_eq_one {M Q Z : Subgroup G} {V₁ V₂ : Subgroup G}
    [Finite G] (H : StrothHyp M Q Z) (hV₁ : V₁ ≤ Q)
    (h : ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) :
    ∀ v ∈ V₁, v * v = 1 := by
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1, one_mul]
  · obtain ⟨g, z, hz, -, rfl⟩ := (h v (hV₁ hv) hv1).mpr (Or.inl hv)
    have hz2 : z * z = 1 := by rw [← sq]; exact Z_sq H hz
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group

@[expose] def Lin31Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 2 ≤ n →
      Lin31Prop M Q Z B n

@[expose] def Lin28Prop (M Q Z : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
    ∃ A : Subgroup G, (∃ g : G, A = conjSubgroup g Z) ∧ A ≤ Q ⊓ QB X

@[expose] def Lin28Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 2 ≤ n → Lin28Prop M Q Z

section Facts

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem lin29_of_sit (hs : Sit M Q Z X x) {A : Subgroup G} (hA : ∃ g : G, A = conjSubgroup g Z)
    (hAQ : A ≤ Q) (hAX : A ≤ QB X) : A ≠ Z ∧ A ≠ X ∧ X ≤ LB M Q A := by
  have h12 : Post12 M Q Z X := smith_1_12 hs
  have hAX' : A ≠ X := by
    intro e
    have hXQ : X ≤ Q := e ▸ hAQ
    have hxQ : x ∈ X ⊓ Q := ⟨hs.mem, hXQ hs.mem⟩
    rw [h12.2, Subgroup.mem_bot] at hxQ
    exact hs.ne_one hxQ
  have hAZ : A ≠ Z := by
    intro e
    rw [e] at hAX
    have hZbot : Z ≤ Z ⊓ QB X := le_inf le_rfl hAX
    rw [Z_inf_QB_eq_bot hs h12] at hZbot
    have h4 := hs.hyp.q4
    rw [le_bot_iff.mp hZbot, Subgroup.card_bot] at h4
    omega
  refine ⟨hAZ, hAX', fun y hy => ?_⟩
  obtain ⟨g, hg⟩ := hs.conj
  have hXA : X ≤ QB A :=
    (hs.hyp.le_QB_iff_le_QB (B := A) (C := X) hA ⟨g, hg⟩ hAX').mp hAX
  have hyM : y ∈ M := (h12.1 hy).1
  exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hXA hy, hyM⟩)

end Facts

@[expose] def Lin212Prop (M Q Z B : Subgroup G) (V₁ V₂ : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
    x ∈ Lgen M (LB M Q B) ∧ HasDimOn V₁ Z 1 x ∧ HasDimOn V₂ Z 1 x ∧
    (∀ z' ∈ Z, InZClass Z (x * z') → z' = 1) ∧
    ((Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z) ∧
    (CQt Q Z (Subgroup.zpowers x) =
      (((Q ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ Z : Subgroup G) : Set G)) ∧
    (∀ g q : G, q ∈ Q → g * x * g⁻¹ = x * q → ∃ q' ∈ Q, g * x * g⁻¹ = q' * x * q'⁻¹) ∧
    (∃ K : Subgroup G, K ≤ M ∧ K ⊓ Q = ⊥ ∧ K ⊔ Q = M ∧ ∃ q ∈ Q, q * x * q⁻¹ ∈ K)

@[expose] def Lin212Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 2 ≤ n →
      Lin212Prop M Q Z B V₁ V₂

@[expose] def Lin213Prop (M Z : Subgroup G) : Prop :=
  ∀ x y : G, x ∈ M → y ∈ M → InZClass Z x → InZClass Z y →
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2))

@[expose] def Lin213Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 2 ≤ n → Lin213Prop M Z

@[expose] def Lin26Prop (M Q : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K ≤ M ∧ K ⊓ Q = ⊥ ∧ K ⊔ Q = M

@[expose] def Lin26Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 2 ≤ n → Lin26Prop M Q

structure Lin3Facts (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G) : Prop where
  h31 : Lin31Prop M Q Z B n
  h28 : Lin28Prop M Q Z
  h212 : Lin212Prop M Q Z B V₁ V₂
  h213 : Lin213Prop M Z
  h26 : Lin26Prop M Q

@[expose] def Lin3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 2 ≤ n →
      Lin3Facts M Q Z B n V₁ V₂

theorem lin3Statement_of (h31 : Lin31Statement) (h28 : Lin28Statement) (h212 : Lin212Statement)
    (h213 : Lin213Statement) (h26 : Lin26Statement) : Lin3Statement :=
  fun G _ _ M Q Z B n V₁ V₂ hb hc hS hn =>
    ⟨h31 G M Q Z B n V₁ V₂ hb hc hS hn, h28 G M Q Z B n V₁ V₂ hb hc hS hn,
      h212 G M Q Z B n V₁ V₂ hb hc hS hn, h213 G M Q Z B n V₁ V₂ hb hc hS hn,
      h26 G M Q Z B n V₁ V₂ hb hc hS hn⟩

end CFSG.RankThree.GF2n.Smith81
