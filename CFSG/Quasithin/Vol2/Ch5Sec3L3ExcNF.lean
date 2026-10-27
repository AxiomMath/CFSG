module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcCoords
public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcLoc
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.SL2Semilinear

section Heis

variable {G : Type} [Group G]

structure HeisCoords (S V₁ V₂ Z : Subgroup G) (F : Type) [Field F] where
  Φ : F × F × F → G
  mem : ∀ p, Φ p ∈ S
  surj : ∀ s ∈ S, ∃ p, Φ p = s
  inj : Function.Injective Φ
  mul : ∀ c a b c' a' b' : F,
    Φ (c, a, b) * Φ (c', a', b') = Φ (c + c' + a' * b, a + a', b + b')
  mem_V₁ : ∀ g, g ∈ V₁ ↔ ∃ c a, Φ (c, a, 0) = g
  mem_V₂ : ∀ g, g ∈ V₂ ↔ ∃ c b, Φ (c, 0, b) = g
  mem_Z : ∀ g, g ∈ Z ↔ ∃ c, Φ (c, 0, 0) = g

variable {S V₁ V₂ Z : Subgroup G} {F : Type} [Field F]

theorem HeisCoords.zero (Φc : HeisCoords S V₁ V₂ Z F) : Φc.Φ (0, 0, 0) = 1 := by
  have h := Φc.mul 0 0 0 0 0 0
  simp only [add_zero, mul_zero] at h
  exact mul_eq_left.mp h

theorem HeisCoords.conj (Φc : HeisCoords S V₁ V₂ Z F) (h2 : (2 : F) = 0) (c₀ a₀ b₀ c a b : F) :
    Φc.Φ (c₀, a₀, b₀) * Φc.Φ (c, a, b) * (Φc.Φ (c₀, a₀, b₀))⁻¹ =
      Φc.Φ (c + a * b₀ + a₀ * b, a, b) := by
  rw [mul_inv_eq_iff_eq_mul, Φc.mul, Φc.mul]
  congr 1
  rw [Prod.mk.injEq, Prod.mk.injEq]
  exact ⟨by linear_combination -(a₀ * b) * h2, by ring, by ring⟩

theorem HeisCoords.exists_rescale (Φc : HeisCoords S V₁ V₂ Z F) {μ ν : F} (hμ : μ ≠ 0)
    (hν : ν ≠ 0) : ∃ Φ' : HeisCoords S V₁ V₂ Z F,
      ∀ c a b, Φ'.Φ (c, a, b) = Φc.Φ (μ * ν * c, μ * a, ν * b) := by
  have hμν : μ * ν ≠ 0 := mul_ne_zero hμ hν
  have e : ∀ c a b : F, ((μ * ν * ((μ * ν)⁻¹ * c), μ * (μ⁻¹ * a), ν * (ν⁻¹ * b)) : F × F × F) =
      (c, a, b) := fun c a b => by
    rw [mul_inv_cancel_left₀ hμν, mul_inv_cancel_left₀ hμ, mul_inv_cancel_left₀ hν]
  refine ⟨{
    Φ := fun p => Φc.Φ (μ * ν * p.1, μ * p.2.1, ν * p.2.2)
    mem := fun p => Φc.mem _
    surj := fun s hs => by
      obtain ⟨⟨c, a, b⟩, rfl⟩ := Φc.surj s hs
      exact ⟨((μ * ν)⁻¹ * c, μ⁻¹ * a, ν⁻¹ * b), congrArg Φc.Φ (e c a b)⟩
    inj := fun p q h => by
      have h' := Φc.inj h
      rw [Prod.mk.injEq, Prod.mk.injEq] at h'
      obtain ⟨h1, h2, h3⟩ := h'
      exact Prod.ext (mul_left_cancel₀ hμν h1)
        (Prod.ext (mul_left_cancel₀ hμ h2) (mul_left_cancel₀ hν h3))
    mul := fun c a b c' a' b' => by
      show Φc.Φ (μ * ν * c, μ * a, ν * b) * Φc.Φ (μ * ν * c', μ * a', ν * b') =
        Φc.Φ (μ * ν * (c + c' + a' * b), μ * (a + a'), ν * (b + b'))
      rw [Φc.mul]
      congr 1
      rw [Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨by ring, by ring, by ring⟩
    mem_V₁ := fun g => by
      rw [Φc.mem_V₁]
      constructor
      · rintro ⟨c, a, rfl⟩
        refine ⟨(μ * ν)⁻¹ * c, μ⁻¹ * a, ?_⟩
        show Φc.Φ (μ * ν * ((μ * ν)⁻¹ * c), μ * (μ⁻¹ * a), ν * 0) = Φc.Φ (c, a, 0)
        rw [mul_zero, mul_inv_cancel_left₀ hμν, mul_inv_cancel_left₀ hμ]
      · rintro ⟨c, a, rfl⟩
        refine ⟨μ * ν * c, μ * a, ?_⟩
        show Φc.Φ (μ * ν * c, μ * a, 0) = Φc.Φ (μ * ν * c, μ * a, ν * 0)
        rw [mul_zero]
    mem_V₂ := fun g => by
      rw [Φc.mem_V₂]
      constructor
      · rintro ⟨c, b, rfl⟩
        refine ⟨(μ * ν)⁻¹ * c, ν⁻¹ * b, ?_⟩
        show Φc.Φ (μ * ν * ((μ * ν)⁻¹ * c), μ * 0, ν * (ν⁻¹ * b)) = Φc.Φ (c, 0, b)
        rw [mul_zero, mul_inv_cancel_left₀ hμν, mul_inv_cancel_left₀ hν]
      · rintro ⟨c, b, rfl⟩
        refine ⟨μ * ν * c, ν * b, ?_⟩
        show Φc.Φ (μ * ν * c, 0, ν * b) = Φc.Φ (μ * ν * c, μ * 0, ν * b)
        rw [mul_zero]
    mem_Z := fun g => by
      rw [Φc.mem_Z]
      constructor
      · rintro ⟨c, rfl⟩
        refine ⟨(μ * ν)⁻¹ * c, ?_⟩
        show Φc.Φ (μ * ν * ((μ * ν)⁻¹ * c), μ * 0, ν * 0) = Φc.Φ (c, 0, 0)
        rw [mul_zero, mul_zero, mul_inv_cancel_left₀ hμν]
      · rintro ⟨c, rfl⟩
        refine ⟨μ * ν * c, ?_⟩
        show Φc.Φ (μ * ν * c, 0, 0) = Φc.Φ (μ * ν * c, μ * 0, ν * 0)
        rw [mul_zero, mul_zero] }, fun c a b => rfl⟩

theorem HeisCoords.exists_transport (Φc : HeisCoords S V₁ V₂ Z F) {K : Type} [Field K]
    (e : K ≃+* F) :
    ∃ Ψ : HeisCoords S V₁ V₂ Z K, ∀ c a b, Ψ.Φ (c, a, b) = Φc.Φ (e c, e a, e b) := by
  refine ⟨{
    Φ := fun p => Φc.Φ (e p.1, e p.2.1, e p.2.2)
    mem := fun p => Φc.mem _
    surj := fun s hs => by
      obtain ⟨⟨c, a, b⟩, rfl⟩ := Φc.surj s hs
      refine ⟨(e.symm c, e.symm a, e.symm b), ?_⟩
      show Φc.Φ (e (e.symm c), e (e.symm a), e (e.symm b)) = _
      rw [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
    inj := fun p q h => by
      have h' := Φc.inj h
      rw [Prod.mk.injEq, Prod.mk.injEq] at h'
      obtain ⟨h1, h2, h3⟩ := h'
      exact Prod.ext (e.injective h1) (Prod.ext (e.injective h2) (e.injective h3))
    mul := fun c a b c' a' b' => by
      show Φc.Φ (e c, e a, e b) * Φc.Φ (e c', e a', e b') =
        Φc.Φ (e (c + c' + a' * b), e (a + a'), e (b + b'))
      rw [Φc.mul]
      simp only [map_add, map_mul]
    mem_V₁ := fun g => by
      rw [Φc.mem_V₁]
      constructor
      · rintro ⟨c, a, rfl⟩
        refine ⟨e.symm c, e.symm a, ?_⟩
        show Φc.Φ (e (e.symm c), e (e.symm a), e 0) = _
        rw [e.apply_symm_apply, e.apply_symm_apply, map_zero]
      · rintro ⟨c, a, rfl⟩
        refine ⟨e c, e a, ?_⟩
        show Φc.Φ (e c, e a, 0) = Φc.Φ (e c, e a, e 0)
        rw [map_zero]
    mem_V₂ := fun g => by
      rw [Φc.mem_V₂]
      constructor
      · rintro ⟨c, b, rfl⟩
        refine ⟨e.symm c, e.symm b, ?_⟩
        show Φc.Φ (e (e.symm c), e 0, e (e.symm b)) = _
        rw [e.apply_symm_apply, e.apply_symm_apply, map_zero]
      · rintro ⟨c, b, rfl⟩
        refine ⟨e c, e b, ?_⟩
        show Φc.Φ (e c, 0, e b) = Φc.Φ (e c, e 0, e b)
        rw [map_zero]
    mem_Z := fun g => by
      rw [Φc.mem_Z]
      constructor
      · rintro ⟨c, rfl⟩
        refine ⟨e.symm c, ?_⟩
        show Φc.Φ (e (e.symm c), e 0, e 0) = _
        rw [e.apply_symm_apply, map_zero]
      · rintro ⟨c, rfl⟩
        refine ⟨e c, ?_⟩
        show Φc.Φ (e c, 0, 0) = Φc.Φ (e c, e 0, e 0)
        rw [map_zero] }, fun c a b => rfl⟩

theorem HeisCoords.exists_normalized [CharP F 2] [Finite F] (hF : Nat.card F = 4)
    {T : Subgroup G} (hST : S ≤ T) (hTS : ∀ t ∈ T, (∀ g ∈ Z, g * t = t * g) → t ∈ S)
    (Φc : HeisCoords S V₁ V₂ Z F) {x₀ : G} (hx₀T : x₀ ∈ T) (hx₀S : x₀ ∉ S)
    {A₁ A₂ B₁ B₂ E : F} (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0)
    (hact : ∀ c a b, x₀ * Φc.Φ (c, a, b) * x₀⁻¹ =
      Φc.Φ (E * c ^ 2 + B₁ * a ^ 2 + B₂ * b ^ 2, A₁ * a ^ 2, A₂ * b ^ 2)) :
    ∃ (Φ' : HeisCoords S V₁ V₂ Z F) (x : G), x ∈ T ∧ x ∉ S ∧ x * x = 1 ∧
      ∀ c a b, x * Φ'.Φ (c, a, b) * x⁻¹ = Φ'.Φ (c ^ 2, a ^ 2, b ^ 2) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h4 : ∀ s : F, (s ^ 2) ^ 2 = s := fun s => by
    rw [← pow_mul]
    exact pow_four_of_card_four hF s
  have hE : E = A₁ * A₂ := by
    have hp : Φc.Φ (0, 0, 1) * Φc.Φ (0, 1, 0) = Φc.Φ (1, 1, 1) := by
      rw [Φc.mul]
      congr 1
      rw [Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨by ring, by ring, by ring⟩
    have e : x₀ * (Φc.Φ (0, 0, 1) * Φc.Φ (0, 1, 0)) * x₀⁻¹ = x₀ * Φc.Φ (1, 1, 1) * x₀⁻¹ := by
      rw [hp]
    have e' : x₀ * (Φc.Φ (0, 0, 1) * Φc.Φ (0, 1, 0)) * x₀⁻¹ =
        (x₀ * Φc.Φ (0, 0, 1) * x₀⁻¹) * (x₀ * Φc.Φ (0, 1, 0) * x₀⁻¹) := by group
    rw [e', hact, hact, hact, Φc.mul] at e
    have h' := Φc.inj e
    rw [Prod.mk.injEq] at h'
    linear_combination -h'.1
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ = Φc.Φ (0, B₂ * A₂⁻¹, B₁ * A₁⁻¹) * x₀ := ⟨_, rfl⟩
  have hact₁ : ∀ c a b, x₁ * Φc.Φ (c, a, b) * x₁⁻¹ = Φc.Φ (E * c ^ 2, A₁ * a ^ 2, A₂ * b ^ 2) := by
    intro c a b
    have e : x₁ * Φc.Φ (c, a, b) * x₁⁻¹ = Φc.Φ (0, B₂ * A₂⁻¹, B₁ * A₁⁻¹) *
        (x₀ * Φc.Φ (c, a, b) * x₀⁻¹) * (Φc.Φ (0, B₂ * A₂⁻¹, B₁ * A₁⁻¹))⁻¹ := by
      rw [hx₁]
      group
    rw [e, hact, Φc.conj h2]
    congr 1
    rw [Prod.mk.injEq, Prod.mk.injEq]
    refine ⟨?_, rfl, rfl⟩
    have e1 : A₁ * a ^ 2 * (B₁ * A₁⁻¹) = B₁ * a ^ 2 := by
      calc A₁ * a ^ 2 * (B₁ * A₁⁻¹) = (A₁ * A₁⁻¹) * (B₁ * a ^ 2) := by ring
        _ = B₁ * a ^ 2 := by rw [mul_inv_cancel₀ hA₁, one_mul]
    have e2 : B₂ * A₂⁻¹ * (A₂ * b ^ 2) = B₂ * b ^ 2 := by
      calc B₂ * A₂⁻¹ * (A₂ * b ^ 2) = (A₂ * A₂⁻¹) * (B₂ * b ^ 2) := by ring
        _ = B₂ * b ^ 2 := by rw [mul_inv_cancel₀ hA₂, one_mul]
    rw [e1, e2]
    linear_combination h2 * (B₁ * a ^ 2 + B₂ * b ^ 2)
  obtain ⟨Φ', hΦ'⟩ := Φc.exists_rescale (inv_ne_zero hA₁) (inv_ne_zero hA₂)
  have hact₂ : ∀ c a b, x₁ * Φ'.Φ (c, a, b) * x₁⁻¹ = Φ'.Φ (c ^ 2, a ^ 2, b ^ 2) := by
    intro c a b
    rw [hΦ', hΦ', hact₁]
    congr 1
    rw [Prod.mk.injEq, Prod.mk.injEq, hE]
    refine ⟨?_, ?_, ?_⟩
    · field_simp
    · field_simp
    · field_simp
  have hx₁T : x₁ ∈ T := by
    rw [hx₁]
    exact T.mul_mem (hST (Φc.mem _)) hx₀T
  have hx₁S : x₁ ∉ S := by
    intro h
    apply hx₀S
    have e : x₀ = (Φc.Φ (0, B₂ * A₂⁻¹, B₁ * A₁⁻¹))⁻¹ * x₁ := by
      rw [hx₁]
      group
    rw [e]
    exact S.mul_mem (S.inv_mem (Φc.mem _)) h
  have hsq : ∀ c a b, (x₁ * x₁) * Φ'.Φ (c, a, b) * (x₁ * x₁)⁻¹ = Φ'.Φ (c, a, b) := by
    intro c a b
    have e : (x₁ * x₁) * Φ'.Φ (c, a, b) * (x₁ * x₁)⁻¹ =
        x₁ * (x₁ * Φ'.Φ (c, a, b) * x₁⁻¹) * x₁⁻¹ := by group
    rw [e, hact₂, hact₂, h4, h4, h4]
  have hx₁₁S : x₁ * x₁ ∈ S := by
    refine hTS _ (T.mul_mem hx₁T hx₁T) fun g hg => ?_
    obtain ⟨c, rfl⟩ := (Φ'.mem_Z g).mp hg
    calc Φ'.Φ (c, 0, 0) * (x₁ * x₁) =
        (x₁ * x₁) * Φ'.Φ (c, 0, 0) * (x₁ * x₁)⁻¹ * (x₁ * x₁) := by rw [hsq]
      _ = (x₁ * x₁) * Φ'.Φ (c, 0, 0) := by group
  obtain ⟨⟨e, a₁, b₁⟩, he⟩ := Φ'.surj _ hx₁₁S
  have hcen : ∀ c a b, Φ'.Φ (e, a₁, b₁) * Φ'.Φ (c, a, b) = Φ'.Φ (c, a, b) * Φ'.Φ (e, a₁, b₁) := by
    intro c a b
    rw [he]
    calc (x₁ * x₁) * Φ'.Φ (c, a, b) =
        (x₁ * x₁) * Φ'.Φ (c, a, b) * (x₁ * x₁)⁻¹ * (x₁ * x₁) := by group
      _ = Φ'.Φ (c, a, b) * (x₁ * x₁) := by rw [hsq]
  have hb₁ : b₁ = 0 := by
    have h1 := hcen 0 1 0
    rw [Φ'.mul, Φ'.mul] at h1
    have h' := Φ'.inj h1
    rw [Prod.mk.injEq] at h'
    linear_combination h'.1
  have ha₁ : a₁ = 0 := by
    have h1 := hcen 0 0 1
    rw [Φ'.mul, Φ'.mul] at h1
    have h' := Φ'.inj h1
    rw [Prod.mk.injEq] at h'
    linear_combination -h'.1
  rw [ha₁, hb₁] at he
  have he2 : e ^ 2 = e := by
    have h1 : x₁ * (x₁ * x₁) * x₁⁻¹ = x₁ * x₁ := by group
    rw [← he, hact₂] at h1
    have h' := Φ'.inj h1
    rw [Prod.mk.injEq] at h'
    exact h'.1
  obtain ⟨w, hw⟩ : ∃ w : F, w ^ 2 + w = e := by
    have hm : e * (e - 1) = 0 := by linear_combination he2
    rcases mul_eq_zero.mp hm with h0 | h1
    · exact ⟨0, by rw [h0]; ring⟩
    · obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_one_of_card_four hF
      refine ⟨t, ?_⟩
      have ht := sq_add_self_add_one_of_card_four hF ht0 ht1
      linear_combination ht - h1 - h2
  refine ⟨Φ', Φ'.Φ (w, 0, 0) * x₁, T.mul_mem (hST (Φ'.mem _)) hx₁T, ?_, ?_, ?_⟩
  · intro h
    apply hx₁S
    have e1 : x₁ = (Φ'.Φ (w, 0, 0))⁻¹ * (Φ'.Φ (w, 0, 0) * x₁) := by group
    rw [e1]
    exact S.mul_mem (S.inv_mem (Φ'.mem _)) h
  · have e1 : Φ'.Φ (w, 0, 0) * x₁ * (Φ'.Φ (w, 0, 0) * x₁) =
        Φ'.Φ (w, 0, 0) * (x₁ * Φ'.Φ (w, 0, 0) * x₁⁻¹) * (x₁ * x₁) := by group
    rw [e1, hact₂, ← he, Φ'.mul, Φ'.mul, ← Φ'.zero]
    congr 1
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨by linear_combination hw + h2 * e, by ring, by ring⟩
  · intro c a b
    have e1 : Φ'.Φ (w, 0, 0) * x₁ * Φ'.Φ (c, a, b) * (Φ'.Φ (w, 0, 0) * x₁)⁻¹ =
        Φ'.Φ (w, 0, 0) * (x₁ * Φ'.Φ (c, a, b) * x₁⁻¹) * (Φ'.Φ (w, 0, 0))⁻¹ := by group
    rw [e1, hact₂, Φ'.conj h2]
    congr 1
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨by ring, rfl, rfl⟩

end Heis

section FromCoords

variable {G : Type} [Group G] {S V₁ V₂ Z G₁ G₂ B L K : Subgroup G} {F : Type} [Field F]

theorem V1Coords.map_zero' (C : V1Coords G₁ B L V₁ V₂ Z F) : C.ι 0 = 1 := by
  have h := C.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem V1Coords.inv_eq (C : V1Coords G₁ B L V₁ V₂ Z F) (p : F × F) : (C.ι p)⁻¹ = C.ι (-p) := by
  rw [inv_eq_iff_mul_eq_one, ← C.add, add_neg_cancel, C.map_zero']

theorem exists_heisCoords_of (C₁ : V1Coords G₁ B L V₁ V₂ Z F) (C₂ : V1Coords G₂ B K V₂ V₁ Z F)
    (h0 : ∀ c, C₁.ι (0, c) = C₂.ι (0, c)) (hy : ∀ β, C₁.ye β = C₂.ι (β, 0))
    (hsup : V₁ ⊔ V₂ = S) (hinf : V₁ ⊓ V₂ = Z) :
    ∃ Φc : HeisCoords S V₁ V₂ Z F, ∀ c a b, Φc.Φ (c, a, b) = C₁.ι (a, c) * C₂.ι (b, 0) := by
  have h00 : ((0 : F), (0 : F)) = 0 := rfl
  have hcomm : ∀ a c b : F,
      C₂.ι (b, 0) * C₁.ι (a, c) = C₁.ι (a, c + b * a) * C₂.ι (b, 0) := by
    intro a c b
    have h := C₁.ye_act b (a, c)
    rw [hy, tvY_apply] at h
    calc C₂.ι (b, 0) * C₁.ι (a, c) =
        C₂.ι (b, 0) * C₁.ι (a, c) * (C₂.ι (b, 0))⁻¹ * C₂.ι (b, 0) := by group
      _ = C₁.ι (a, c + b * a) * C₂.ι (b, 0) := by rw [h]
  have hΦV₂ : ∀ c b : F, C₁.ι (0, c) * C₂.ι (b, 0) = C₂.ι (b, c) := by
    intro c b
    rw [h0, ← C₂.add, Prod.mk_add_mk, zero_add, add_zero]
  have hmul : ∀ c a b c' a' b' : F, C₁.ι (a, c) * C₂.ι (b, 0) * (C₁.ι (a', c') * C₂.ι (b', 0)) =
      C₁.ι (a + a', c + c' + a' * b) * C₂.ι (b + b', 0) := by
    intro c a b c' a' b'
    calc C₁.ι (a, c) * C₂.ι (b, 0) * (C₁.ι (a', c') * C₂.ι (b', 0)) =
        C₁.ι (a, c) * (C₂.ι (b, 0) * C₁.ι (a', c')) * C₂.ι (b', 0) := by group
      _ = C₁.ι (a, c) * C₁.ι (a', c' + b * a') * (C₂.ι (b, 0) * C₂.ι (b', 0)) := by
        rw [hcomm]
        group
      _ = C₁.ι ((a, c) + (a', c' + b * a')) * C₂.ι ((b, 0) + (b', 0)) := by
        rw [C₁.add, C₂.add]
      _ = C₁.ι (a + a', c + c' + a' * b) * C₂.ι (b + b', 0) := by
        rw [Prod.mk_add_mk, Prod.mk_add_mk, add_zero]
        congr 2
        rw [Prod.mk.injEq]
        exact ⟨rfl, by ring⟩
  have hone : C₁.ι (0, 0) * C₂.ι (0, 0) = 1 := by
    rw [h00, C₁.map_zero', C₂.map_zero', one_mul]
  let R : Subgroup G :=
    { carrier := Set.range fun p : F × F × F => C₁.ι (p.2.1, p.1) * C₂.ι (p.2.2, 0)
      mul_mem' := by
        rintro _ _ ⟨⟨c, a, b⟩, rfl⟩ ⟨⟨c', a', b'⟩, rfl⟩
        exact ⟨(c + c' + a' * b, a + a', b + b'), (hmul c a b c' a' b').symm⟩
      one_mem' := ⟨(0, 0, 0), hone⟩
      inv_mem' := by
        rintro _ ⟨⟨c, a, b⟩, rfl⟩
        refine ⟨(-c + a * b, -a, -b), ?_⟩
        show C₁.ι (-a, -c + a * b) * C₂.ι (-b, 0) = (C₁.ι (a, c) * C₂.ι (b, 0))⁻¹
        rw [eq_inv_iff_mul_eq_one, hmul]
        have e1 : ((-a + a, -c + a * b + c + a * -b) : F × F) = (0, 0) := by
          rw [Prod.mk.injEq]
          exact ⟨by ring, by ring⟩
        have e2 : ((-b + b, 0) : F × F) = (0, 0) := by
          rw [Prod.mk.injEq]
          exact ⟨by ring, rfl⟩
        rw [e1, e2, hone] }
  have hV₁R : V₁ ≤ R := by
    intro v hv
    obtain ⟨⟨a, c⟩, rfl⟩ := C₁.surj v hv
    refine ⟨(c, a, 0), ?_⟩
    show C₁.ι (a, c) * C₂.ι (0, 0) = C₁.ι (a, c)
    rw [h00, C₂.map_zero', mul_one]
  have hV₂R : V₂ ≤ R := by
    intro v hv
    obtain ⟨⟨b, c⟩, rfl⟩ := C₂.surj v hv
    exact ⟨(c, 0, b), hΦV₂ c b⟩
  refine ⟨{
    Φ := fun p => C₁.ι (p.2.1, p.1) * C₂.ι (p.2.2, 0)
    mem := fun p => by
      rw [← hsup]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (C₁.mem _))
        (Subgroup.mem_sup_right (C₂.mem _))
    surj := fun s hs => by
      rw [← hsup] at hs
      exact (sup_le hV₁R hV₂R) hs
    inj := fun p q h => by
      obtain ⟨c, a, b⟩ := p
      obtain ⟨c', a', b'⟩ := q
      have h' : C₁.ι (a, c) * C₂.ι (b, 0) = C₁.ι (a', c') * C₂.ι (b', 0) := h
      have h1 : C₁.ι (-(a', c') + (a, c)) = C₂.ι ((b', 0) + -(b, 0)) := by
        rw [C₁.add, C₂.add, ← C₁.inv_eq, ← C₂.inv_eq]
        calc (C₁.ι (a', c'))⁻¹ * C₁.ι (a, c) =
            (C₁.ι (a', c'))⁻¹ * (C₁.ι (a, c) * C₂.ι (b, 0)) * (C₂.ι (b, 0))⁻¹ := by group
          _ = (C₁.ι (a', c'))⁻¹ * (C₁.ι (a', c') * C₂.ι (b', 0)) * (C₂.ι (b, 0))⁻¹ := by
            rw [h']
          _ = C₂.ι (b', 0) * (C₂.ι (b, 0))⁻¹ := by group
      have hZ : C₁.ι (-(a', c') + (a, c)) ∈ Z := by
        have hm : C₁.ι (-(a', c') + (a, c)) ∈ V₁ ⊓ V₂ :=
          Subgroup.mem_inf.mpr ⟨C₁.mem _, by rw [h1]; exact C₂.mem _⟩
        rwa [hinf] at hm
      obtain ⟨d, hd⟩ := (C₂.center _).mp hZ
      have hb := C₂.inj (h1.symm.trans hd)
      have hb1 : b' + -b = 0 := by
        have := congrArg Prod.fst hb
        simp only [Prod.fst_add, Prod.fst_neg] at this
        exact this
      have hd0 : d = 0 := by
        have := congrArg Prod.snd hb
        simp only [Prod.snd_add, Prod.snd_neg, neg_zero, add_zero] at this
        exact this.symm
      have hac : -(a', c') + (a, c) = 0 := by
        apply C₁.inj
        rw [hd, hd0, h00, C₁.map_zero']
        exact C₂.map_zero'
      have ha : a = a' := by
        have := congrArg Prod.fst hac
        simp only [Prod.fst_add, Prod.fst_neg, Prod.fst_zero] at this
        linear_combination this
      have hc : c = c' := by
        have := congrArg Prod.snd hac
        simp only [Prod.snd_add, Prod.snd_neg, Prod.snd_zero] at this
        linear_combination this
      have hb' : b = b' := by linear_combination -hb1
      rw [ha, hc, hb']
    mul := fun c a b c' a' b' => hmul c a b c' a' b'
    mem_V₁ := fun g => by
      constructor
      · intro hg
        obtain ⟨⟨a, c⟩, rfl⟩ := C₁.surj g hg
        refine ⟨c, a, ?_⟩
        show C₁.ι (a, c) * C₂.ι (0, 0) = C₁.ι (a, c)
        rw [h00, C₂.map_zero', mul_one]
      · rintro ⟨c, a, rfl⟩
        show C₁.ι (a, c) * C₂.ι (0, 0) ∈ V₁
        rw [h00, C₂.map_zero', mul_one]
        exact C₁.mem _
    mem_V₂ := fun g => by
      constructor
      · intro hg
        obtain ⟨⟨b, c⟩, rfl⟩ := C₂.surj g hg
        exact ⟨c, b, hΦV₂ c b⟩
      · rintro ⟨c, b, rfl⟩
        show C₁.ι (0, c) * C₂.ι (b, 0) ∈ V₂
        rw [hΦV₂]
        exact C₂.mem _
    mem_Z := fun g => by
      rw [C₁.center]
      constructor
      · rintro ⟨c, rfl⟩
        refine ⟨c, ?_⟩
        show C₁.ι (0, c) * C₂.ι (0, 0) = C₁.ι (0, c)
        rw [h00, C₂.map_zero', mul_one]
      · rintro ⟨c, rfl⟩
        refine ⟨c, ?_⟩
        show C₁.ι (0, c) * C₂.ι (0, 0) = C₁.ι (0, c)
        rw [h00, C₂.map_zero', mul_one] }, fun c a b => rfl⟩

theorem heis_conj_of_frobenius (Φc : HeisCoords S V₁ V₂ Z F) (C₁ : V1Coords G₁ B L V₁ V₂ Z F)
    (C₂ : V1Coords G₂ B K V₂ V₁ Z F) (hΦ : ∀ c a b, Φc.Φ (c, a, b) = C₁.ι (a, c) * C₂.ι (b, 0))
    (h0 : ∀ c, C₁.ι (0, c) = C₂.ι (0, c)) {x : G} {τ₁ τ₂ : F × F ≃+ F × F} {σ₁ σ₂ : F →+* F}
    (hτ₁ : ∀ p, C₁.ι (τ₁ p) = x * C₁.ι p * x⁻¹)
    (hσ₁ : ∀ (c : F) (p : F × F), τ₁ (c • p) = σ₁ c • τ₁ p)
    (hτ₂ : ∀ p, C₂.ι (τ₂ p) = x * C₂.ι p * x⁻¹)
    (hσ₂ : ∀ (c : F) (p : F × F), τ₂ (c • p) = σ₂ c • τ₂ p) (hZ₁ : (τ₁ (0, 1)).1 = 0)
    (hs₁ : ∀ s, σ₁ s = s ^ 2) (hs₂ : ∀ s, σ₂ s = s ^ 2) (c a b : F) :
    x * Φc.Φ (c, a, b) * x⁻¹ = Φc.Φ ((τ₁ (0, 1)).2 * c ^ 2 + (τ₁ (1, 0)).2 * a ^ 2 +
      (τ₂ (1, 0)).2 * b ^ 2, (τ₁ (1, 0)).1 * a ^ 2, (τ₂ (1, 0)).1 * b ^ 2) := by
  have e1 : τ₁ (a, c) =
      ((τ₁ (1, 0)).1 * a ^ 2, (τ₁ (1, 0)).2 * a ^ 2 + (τ₁ (0, 1)).2 * c ^ 2) := by
    have e : ((a, c) : F × F) = a • ((1 : F), (0 : F)) + c • ((0 : F), (1 : F)) := by
      ext <;> simp
    rw [e, map_add, hσ₁, hσ₁, hs₁, hs₁]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hZ₁]
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      ring
  have e2 : τ₂ (b, 0) = ((τ₂ (1, 0)).1 * b ^ 2, (τ₂ (1, 0)).2 * b ^ 2) := by
    have e : ((b, 0) : F × F) = b • ((1 : F), (0 : F)) := by ext <;> simp
    rw [e, hσ₂, hs₂]
    ext
    · simp only [Prod.smul_fst, smul_eq_mul]
      ring
    · simp only [Prod.smul_snd, smul_eq_mul]
      ring
  have e3 : C₂.ι ((τ₂ (1, 0)).1 * b ^ 2, (τ₂ (1, 0)).2 * b ^ 2) =
      C₁.ι (0, (τ₂ (1, 0)).2 * b ^ 2) * C₂.ι ((τ₂ (1, 0)).1 * b ^ 2, 0) := by
    rw [h0, ← C₂.add, Prod.mk_add_mk, zero_add, add_zero]
  have hsplit : x * (C₁.ι (a, c) * C₂.ι (b, 0)) * x⁻¹ = C₁.ι (τ₁ (a, c)) * C₂.ι (τ₂ (b, 0)) := by
    rw [hτ₁, hτ₂]
    group
  rw [hΦ, hΦ, hsplit, e1, e2, e3, ← mul_assoc, ← C₁.add, Prod.mk_add_mk]
  congr 2
  rw [Prod.mk.injEq]
  exact ⟨by ring, by ring⟩

end FromCoords

theorem f4_eq_one_of_sq_eq_self (c : CFSG.Fischer.F4) : c ^ 2 = c → c ≠ 0 → c = 1 := by
  obtain ⟨i⟩ := c
  revert i
  decide

variable {G : Type} [Group G]

structure ExcNF (T S V₁ V₂ Z : Subgroup G) extends HeisCoords S V₁ V₂ Z CFSG.Fischer.F4 where
  x : G
  x_mem : x ∈ T
  x_not_mem : x ∉ S
  x_mul_self : x * x = 1
  x_act : ∀ c a b, x * Φ (c, a, b) * x⁻¹ = Φ (c ^ 2, a ^ 2, b ^ 2)
  cover : ∀ t ∈ T, t ∈ S ∨ t * x ∈ S

variable [Finite G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}

theorem exists_excNF (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : f = 2) {z : G} (hz : z ∈ sec53ZS T L) (hzT : z ∈ centerOf T) (hz1 : z ≠ 1)
    (hO : pCoreOf 2 (sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G)) ≠ sec53S T L) :
    ∃ N : ExcNF T (sec53S T L) (pCoreOf 2 L) (pCoreOf 2 (oTwoUpper H)) (sec53ZS T L),
      N.Φ (1, 0, 0) = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := hf.ge
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hST : sec53S T L ≤ T := inf_le_left
  rw [(exc_centralizer_eq h527 h531 hyp hty hf hz hzT hz1 hO).1] at hO
  obtain ⟨x₀, hx₀T, hx₀S⟩ : ∃ x₀ ∈ T, x₀ ∉ sec53S T L := by
    by_contra hcon
    push Not at hcon
    apply hO
    have hP : pCoreOf 2 T = T := le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 T)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
        h.sylow.1)
    rw [hP]
    exact le_antisymm (fun t ht => hcon t ht) hST
  obtain ⟨F, _, _, _, hFcard, C₁, C₂, h0, hy₁, -⟩ := exists_sCoords h527 hyp hty hf2
  have hF : Nat.card F = 4 := by rw [hFcard, hf]; norm_num
  have hsup := sup_sec53 h527 hyp hty hf2
  have hinf := (l3facts_two h527 hyp hty hf2).2.2.2.1
  obtain ⟨Φc, hΦ⟩ := exists_heisCoords_of C₁ C₂ h0 hy₁ hsup hinf
  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  have hKG : oTwoUpper H ≤ sec53G2 M L H D := le_sup_right
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L := (le_sup_right.trans hsup.le).trans inf_le_right
  have hV₁K : pCoreOf 2 L ≤ oTwoUpper H :=
    (le_sup_left.trans hsup.le).trans (sec53S_le_K h527 hyp)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  obtain ⟨τ₁, σ₁, hτ₁, hσ₁⟩ := C₁.exists_semilinear hLG hV₂L (hTL hx₀T)
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hTL hx₀T))
  obtain ⟨τ₂, σ₂, hτ₂, hσ₂⟩ := C₂.exists_semilinear hKG hV₁K (hTK hx₀T)
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hTK hx₀T))
  have hs₁ := ringHom_eq_sq_of_ne hF
    (exists_sigma_ne h527 h531 hyp hty hf2 C₁ hz hzT hz1 hx₀T hx₀S hτ₁ hσ₁)
  have hs₂ := ringHom_eq_sq_of_ne hF
    (exists_sigma_ne h527 h531 hyp hty hf2 C₂ hz hzT hz1 hx₀T hx₀S hτ₂ hσ₂)
  have hTN := le_normalizer_sec53S (L := L) hyp
  have hZ₁ : (τ₁ (0, 1)).1 = 0 := by
    have h1 : C₁.ι (τ₁ (0, 1)) ∈ sec53ZS T L := by
      rw [hτ₁]
      exact conj_mem_centerOf (hTN hx₀T) ((C₁.center _).mpr ⟨1, rfl⟩)
    obtain ⟨c, hc⟩ := (C₁.center _).mp h1
    rw [C₁.inj hc]
  have hZ₂ : (τ₂ (0, 1)).1 = 0 := by
    have h1 : C₂.ι (τ₂ (0, 1)) ∈ sec53ZS T L := by
      rw [hτ₂]
      exact conj_mem_centerOf (hTN hx₀T) ((C₂.center _).mpr ⟨1, rfl⟩)
    obtain ⟨c, hc⟩ := (C₂.center _).mp h1
    rw [C₂.inj hc]
  have hA₁ : (τ₁ (1, 0)).1 ≠ 0 := by
    intro h0'
    have := fst_of_semilinear hσ₁ hZ₁ (τ₁.symm (1, 0))
    rw [τ₁.apply_symm_apply, h0', mul_zero] at this
    exact one_ne_zero this
  have hA₂ : (τ₂ (1, 0)).1 ≠ 0 := by
    intro h0'
    have := fst_of_semilinear hσ₂ hZ₂ (τ₂.symm (1, 0))
    rw [τ₂.apply_symm_apply, h0', mul_zero] at this
    exact one_ne_zero this
  have hact := heis_conj_of_frobenius Φc C₁ C₂ hΦ h0 hτ₁ hσ₁ hτ₂ hσ₂ hZ₁ hs₁ hs₂
  have hTS : ∀ t ∈ T, (∀ g ∈ sec53ZS T L, g * t = t * g) → t ∈ sec53S T L := by
    intro t ht hc
    rw [← l3facts_one h527 h531 hyp hty hf2]
    exact Subgroup.mem_inf.mpr ⟨ht, Subgroup.mem_centralizer_iff.mpr hc⟩
  obtain ⟨Φ', x, hxT, hxS, hxx, hxact⟩ :=
    Φc.exists_normalized hF hST hTS hx₀T hx₀S hA₁ hA₂ hact
  have := Fintype.ofFinite F
  have hcard : Fintype.card CFSG.Fischer.F4 = Fintype.card F := by
    rw [CFSG.Fischer.F4.card, ← Nat.card_eq_fintype_card, hF]
  obtain ⟨Ψ, hΨ⟩ := Φ'.exists_transport (FiniteField.ringEquivOfCardEq hcard)
  have hΨact : ∀ c a b, x * Ψ.Φ (c, a, b) * x⁻¹ = Ψ.Φ (c ^ 2, a ^ 2, b ^ 2) := by
    intro c a b
    rw [hΨ, hΨ, hxact, map_pow, map_pow, map_pow]
  obtain ⟨cz, hcz⟩ := (Ψ.mem_Z z).mp hz
  have hcz2 : cz ^ 2 = cz := by
    have hxz : x * z * x⁻¹ = z := by
      have hc := Subgroup.mem_centralizer_iff.mp
        ((inf_le_right : centerOf T ≤ Subgroup.centralizer (T : Set G)) hzT) x hxT
      rw [hc]
      group
    rw [← hcz, hΨact] at hxz
    have h' := Ψ.inj hxz
    rw [Prod.mk.injEq] at h'
    exact h'.1
  have hcz0 : cz ≠ 0 := by
    rintro rfl
    exact hz1 (hcz.symm.trans Ψ.zero)
  have hcz1 : cz = 1 := f4_eq_one_of_sq_eq_self cz hcz2 hcz0
  have hcover : ∀ t ∈ T, t ∈ sec53S T L ∨ t * x ∈ sec53S T L := by
    intro t ht
    by_cases htS : t ∈ sec53S T L
    · exact Or.inl htS
    · exact Or.inr (exc_mul_mem_S h527 h531 hyp hty hf hz hzT hz1 ht htS hxT hxS)
  refine ⟨{ Ψ with
    x := x
    x_mem := hxT
    x_not_mem := hxS
    x_mul_self := hxx
    x_act := hΨact
    cover := hcover }, ?_⟩
  show Ψ.Φ (1, 0, 0) = z
  rw [← hcz1]
  exact hcz

end CFSG.Quasithin.H13.Sec53L3
