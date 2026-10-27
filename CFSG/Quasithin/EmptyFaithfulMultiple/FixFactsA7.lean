module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421Props
public import CFSG.Quasithin.SteinbergCBI16FourGroup

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open Equiv Matrix CFSG.Quasithin
open CFSG.Quasithin.SteinbergCB.I16 (Vec4 Mat4 InW fixed_PU indep_W mulVec_inj_of_cube
  eq_one_of_mulVec zmod2_cases vec4_add_self fixed_of_add_eq_zero fixed_eq_zero_of_fourGroup)

namespace FFL

section Lin

variable {X : Mat4}

theorem inW_of_fixed_eq_zero (hX3 : X ^ 3 = 1) (hfix : ∀ v : Vec4, X *ᵥ v = v → v = 0)
    (v : Vec4) : InW X v :=
  hfix _ (fixed_PU hX3 v)

theorem sq_mulVec_of_inW {v : Vec4} (hv : InW X v) : X *ᵥ (X *ᵥ v) = v + X *ᵥ v := by
  unfold InW at hv
  rw [add_mulVec, add_mulVec, one_mulVec, ← mulVec_mulVec] at hv
  apply fixed_of_add_eq_zero
  rw [← hv]
  abel

theorem cube_mulVec (hX3 : X ^ 3 = 1) (v : Vec4) : X *ᵥ (X *ᵥ (X *ᵥ v)) = v := by
  rw [mulVec_mulVec, mulVec_mulVec, ← pow_three', hX3, one_mulVec]

theorem eq_of_fixed (hX3 : X ^ 3 = 1) (hfix : ∀ v : Vec4, X *ᵥ v = v → v = 0) {E₁ : Mat4}
    (hE₁ : E₁ ≠ 1) (hXE : X * E₁ = E₁ * X) {v₀ : Vec4} (hv₀ : v₀ ≠ 0) (hEv₀ : E₁ *ᵥ v₀ = v₀)
    {w : Vec4} (hEw : E₁ *ᵥ w = w) :
    w = 0 ∨ w = v₀ ∨ w = X *ᵥ v₀ ∨ w = X *ᵥ (X *ᵥ v₀) := by
  by_contra hne
  push Not at hne
  obtain ⟨hw0, hw1, hw2, hw3⟩ := hne
  have hW : ∀ v, InW X v := inW_of_fixed_eq_zero hX3 hfix
  have hinj : ∀ {a b : Vec4}, X *ᵥ a = X *ᵥ b → a = b := fun h => mulVec_inj_of_cube hX3 h
  have hsq : ∀ v, X *ᵥ (X *ᵥ v) = v + X *ᵥ v := fun v => sq_mulVec_of_inW (hW v)
  have hEX : ∀ v, E₁ *ᵥ v = v → E₁ *ᵥ (X *ᵥ v) = X *ᵥ v := fun v hv => by
    rw [mulVec_mulVec, ← hXE, ← mulVec_mulVec, hv]
  let c : Vec4 → Vec4 := fun b => b 0 • v₀ + b 1 • (X *ᵥ v₀) + b 2 • w + b 3 • (X *ᵥ w)
  have hc_add : ∀ a b, c (a + b) = c a + c b := by
    intro a b
    simp only [c, Pi.add_apply, add_smul]
    abel
  have hS : ∀ b₀ b₁ : ZMod 2, b₀ • v₀ + b₁ • (X *ᵥ v₀) ≠ w := by
    intro b₀ b₁ h
    rcases zmod2_cases b₀ with rfl | rfl <;> rcases zmod2_cases b₁ with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at h
    · exact hw0 h.symm
    · exact hw2 h.symm
    · exact hw1 h.symm
    · exact hw3 (h.symm.trans (hsq v₀).symm)
  have hSX : ∀ b₀ b₁ : ZMod 2, b₀ • v₀ + b₁ • (X *ᵥ v₀) ≠ X *ᵥ w := by
    intro b₀ b₁ h
    rcases zmod2_cases b₀ with rfl | rfl <;> rcases zmod2_cases b₁ with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at h
    · exact hw0 (hinj (h.symm.trans (mulVec_zero X).symm))
    · exact hw1 (hinj h.symm)
    · apply hw3
      have h1 := congrArg (fun v => X *ᵥ (X *ᵥ v)) h
      simp only [cube_mulVec hX3] at h1
      exact h1.symm
    · apply hw2
      apply hinj
      rw [hsq v₀]
      exact h.symm
  have hSXX : ∀ b₀ b₁ : ZMod 2, b₀ • v₀ + b₁ • (X *ᵥ v₀) ≠ w + X *ᵥ w := by
    intro b₀ b₁ h
    rw [← hsq w] at h
    rcases zmod2_cases b₀ with rfl | rfl <;> rcases zmod2_cases b₁ with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at h
    · apply hw0
      have h1 := congrArg (fun v => X *ᵥ v) h
      simp only [cube_mulVec hX3, mulVec_zero] at h1
      exact h1.symm
    · apply hw3
      have h1 := congrArg (fun v => X *ᵥ v) h
      simp only [cube_mulVec hX3] at h1
      exact h1.symm
    · apply hw2
      have h1 := congrArg (fun v => X *ᵥ v) h
      simp only [cube_mulVec hX3] at h1
      exact h1.symm
    · apply hw1
      have h1 := congrArg (fun v => X *ᵥ v) h
      rw [← hsq v₀, cube_mulVec hX3, cube_mulVec hX3] at h1
      exact h1.symm
  have hc0 : ∀ b, c b = 0 → b = 0 := by
    intro b hb
    have hb' : b 0 • v₀ + b 1 • (X *ᵥ v₀) = b 2 • w + b 3 • (X *ᵥ w) := by
      apply fixed_of_add_eq_zero
      rw [← hb]
      simp only [c]
      abel
    have h23 : b 2 = 0 ∧ b 3 = 0 := by
      rcases zmod2_cases (b 2) with h2 | h2 <;> rcases zmod2_cases (b 3) with h3 | h3 <;>
        rw [h2, h3] at hb' <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hb'
      · exact ⟨h2, h3⟩
      · exact absurd hb' (hSX _ _)
      · exact absurd hb' (hS _ _)
      · exact absurd hb' (hSXX _ _)
    have h01 : b 0 • v₀ + b 1 • (X *ᵥ v₀) = 0 := by
      rw [hb', h23.1, h23.2, zero_smul, zero_smul, add_zero]
    obtain ⟨h0, h1⟩ := indep_W hX3 (hW v₀) hv₀ (b 0) (b 1) h01
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h23.1
    · exact h23.2
  have hcinj : Function.Injective c := by
    intro a b hab
    apply fixed_of_add_eq_zero
    apply hc0
    rw [hc_add, hab, vec4_add_self]
  apply hE₁
  apply eq_one_of_mulVec
  intro z
  obtain ⟨b, rfl⟩ := Finite.injective_iff_surjective.1 hcinj z
  simp only [c, mulVec_add, mulVec_smul, hEv₀, hEX v₀ hEv₀, hEw, hEX w hEw]

theorem exists_fixed_pair {E₁ E₂ : Mat4} (h₁ : E₁ * E₁ = 1) (h₂ : E₂ * E₂ = 1)
    (h₁₂ : E₁ * E₂ = E₂ * E₁) (hE₁ : E₁ ≠ 1) :
    ∃ v : Vec4, v ≠ 0 ∧ E₁ *ᵥ v = v ∧ E₂ *ᵥ v = v := by
  have hN : ∀ {E : Mat4}, E * E = 1 → ∀ z, E *ᵥ ((E + 1) *ᵥ z) = (E + 1) *ᵥ z := by
    intro E hE z
    rw [mulVec_mulVec, mul_add, hE, mul_one, add_comm]
  obtain ⟨z, hz⟩ : ∃ z, (E₁ + 1) *ᵥ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hE₁
    apply eq_one_of_mulVec
    intro z
    apply fixed_of_add_eq_zero
    have := hcon z
    rwa [add_mulVec, one_mulVec] at this
  set u := (E₁ + 1) *ᵥ z with hu
  have hEu : E₁ *ᵥ u = u := hN h₁ z
  by_cases h2u : E₂ *ᵥ u = u
  · exact ⟨u, hz, hEu, h2u⟩
  · refine ⟨(E₂ + 1) *ᵥ u, ?_, ?_, hN h₂ u⟩
    · intro h0
      apply h2u
      apply fixed_of_add_eq_zero
      rw [← h0, add_mulVec, one_mulVec]
    · rw [mulVec_mulVec, mul_add, h₁₂, mul_one, add_mulVec, add_mulVec, ← mulVec_mulVec, hEu,
        one_mulVec]

end Lin

@[expose] def a7e₁P : Perm (Fin 7) := swap 0 1 * swap 2 3
@[expose] def a7e₂P : Perm (Fin 7) := swap 0 2 * swap 1 3
@[expose] def a7tP : Perm (Fin 7) := swap 4 5 * swap 5 6
@[expose] def a7cP : Perm (Fin 7) := swap 0 1 * swap 1 2

theorem a7P_mem : a7e₁P ∈ alternatingGroup (Fin 7) ∧ a7e₂P ∈ alternatingGroup (Fin 7) ∧
    a7tP ∈ alternatingGroup (Fin 7) ∧ a7cP ∈ alternatingGroup (Fin 7) := by
  simp only [Perm.mem_alternatingGroup, a7e₁P, a7e₂P, a7tP, a7cP]
  decide +kernel

@[expose] def a7e₁ : ↥(alternatingGroup (Fin 7)) := ⟨a7e₁P, a7P_mem.1⟩
@[expose] def a7e₂ : ↥(alternatingGroup (Fin 7)) := ⟨a7e₂P, a7P_mem.2.1⟩
@[expose] def a7t : ↥(alternatingGroup (Fin 7)) := ⟨a7tP, a7P_mem.2.2.1⟩
@[expose] def a7c : ↥(alternatingGroup (Fin 7)) := ⟨a7cP, a7P_mem.2.2.2⟩

theorem a7P_relations : a7e₁P * a7e₁P = 1 ∧ a7e₂P * a7e₂P = 1 ∧ a7e₁P * a7e₂P = a7e₂P * a7e₁P ∧
    a7e₁P ≠ 1 ∧ a7e₂P ≠ 1 ∧ a7e₁P ≠ a7e₂P ∧ a7tP ^ 3 = 1 ∧ a7tP ≠ 1 ∧
    a7tP * a7e₁P = a7e₁P * a7tP ∧ a7tP * a7e₂P = a7e₂P * a7tP ∧ a7cP * a7tP = a7tP * a7cP ∧
    a7e₁P * a7cP = a7cP * a7e₂P ∧ a7e₂P * a7cP = a7cP * (a7e₁P * a7e₂P) ∧
    a7cP ^ 3 = 1 ∧ a7cP ≠ 1 ∧ (a7cP * a7tP) ^ 3 = 1 ∧ a7cP * a7tP ≠ 1 ∧
    (a7cP * (a7tP * a7tP)) ^ 3 = 1 ∧ a7cP * (a7tP * a7tP) ≠ 1 := by
  simp only [a7e₁P, a7e₂P, a7tP, a7cP]
  decide +kernel

theorem a7_relations : a7e₁ * a7e₁ = 1 ∧ a7e₂ * a7e₂ = 1 ∧ a7e₁ * a7e₂ = a7e₂ * a7e₁ ∧
    a7e₁ ≠ 1 ∧ a7e₂ ≠ 1 ∧ a7e₁ ≠ a7e₂ ∧ a7t ^ 3 = 1 ∧ a7t ≠ 1 ∧
    a7t * a7e₁ = a7e₁ * a7t ∧ a7t * a7e₂ = a7e₂ * a7t ∧ a7c * a7t = a7t * a7c ∧
    a7e₁ * a7c = a7c * a7e₂ ∧ a7e₂ * a7c = a7c * (a7e₁ * a7e₂) ∧
    a7c ^ 3 = 1 ∧ a7c ≠ 1 ∧ (a7c * a7t) ^ 3 = 1 ∧ a7c * a7t ≠ 1 ∧
    (a7c * (a7t * a7t)) ^ 3 = 1 ∧ a7c * (a7t * a7t) ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := a7P_relations
  refine ⟨Subtype.ext h1, Subtype.ext h2, Subtype.ext h3, fun h => h4 (congrArg Subtype.val h),
    fun h => h5 (congrArg Subtype.val h), fun h => h6 (congrArg Subtype.val h), Subtype.ext h7,
    fun h => h8 (congrArg Subtype.val h), Subtype.ext h9, Subtype.ext h10, Subtype.ext h11,
    Subtype.ext h12, Subtype.ext h13, Subtype.ext h14, fun h => h15 (congrArg Subtype.val h),
    Subtype.ext h16, fun h => h17 (congrArg Subtype.val h), Subtype.ext h18,
    fun h => h19 (congrArg Subtype.val h)⟩

theorem sq_eq_one_of_mem_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure {a, b}) :
    x * x = 1 := by
  have hgen : ∀ y ∈ Subgroup.closure {a, b}, Commute y a ∧ Commute y b := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ⟨Commute.refl _, hab⟩
      · exact ⟨hab.symm, Commute.refl _⟩
    | one => exact ⟨Commute.one_left _, Commute.one_left _⟩
    | mul y z _ _ hy hz => exact ⟨hy.1.mul_left hz.1, hy.2.mul_left hz.2⟩
    | inv y _ hy => exact ⟨hy.1.inv_left, hy.2.inv_left⟩
  have hcomm : ∀ y ∈ Subgroup.closure {a, b}, ∀ z ∈ Subgroup.closure {a, b}, Commute y z := by
    intro y hy z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact (hgen y hy).1
      · exact (hgen y hy).2
    | one => exact Commute.one_right _
    | mul z w _ _ hz hw => exact hz.mul_right hw
    | inv z _ hz => exact hz.inv_right
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  | one => simp
  | mul y z hy hz hy2 hz2 =>
    rw [mul_assoc, ← mul_assoc z, ← (hcomm y hy z hz).eq, mul_assoc, hz2, mul_one, hy2]
  | inv y _ hy2 => rw [← _root_.mul_inv_rev, hy2, inv_one]

theorem isPGroup_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) : IsPGroup 2 ↥(Subgroup.closure {a, b}) := by
  rintro ⟨x, hx⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_one, sq]
  exact sq_eq_one_of_mem_closure_pair ha hb hab hx

theorem altLift7_injective' : Function.Injective altLift7 := by
  intro σ τ h
  apply Subtype.ext
  have h' := congrArg (fun x : alternatingGroup (Fin 8) => (x : Perm (Fin 8))) h
  exact Equiv.Perm.viaEmbeddingHom_injective Fin.castSuccEmb h'

theorem exists_gamma_a7 (M : ↥(alternatingGroup (Fin 7)) →* GL (Fin 4) (ZMod 2))
    (hM : Function.Injective M) :
    ∃ γ : ↥(alternatingGroup (Fin 7)), γ ^ 3 = 1 ∧ γ ≠ 1 ∧ ∀ v : Vec4,
      ((M a7e₁ : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v →
      ((M a7e₂ : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v →
      ((M γ : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := a7_relations
  set m : ↥(alternatingGroup (Fin 7)) → Mat4 := fun σ => ((M σ : GL (Fin 4) (ZMod 2)) : Mat4)
    with hm
  have hmul : ∀ σ τ, m (σ * τ) = m σ * m τ := fun σ τ => by
    simp only [hm, map_mul, Units.val_mul]
  have hone : m 1 = 1 := by simp only [hm, map_one, Units.val_one]
  have hpow3 : ∀ σ, m (σ ^ 3) = m σ ^ 3 := fun σ => by
    simp only [hm, map_pow, Units.val_pow_eq_pow_val]
  have hne : ∀ σ τ, σ ≠ τ → m σ ≠ m τ := fun σ τ hστ h =>
    hστ (hM (Units.ext h))
  set X := m a7t with hX
  set E₁ := m a7e₁ with hE₁
  set E₂ := m a7e₂ with hE₂
  set Y := m a7c with hY
  have hX3 : X ^ 3 = 1 := by rw [hX, ← hpow3, h7, hone]
  have hE₁₁ : E₁ * E₁ = 1 := by rw [hE₁, ← hmul, h1, hone]
  have hE₂₂ : E₂ * E₂ = 1 := by rw [hE₂, ← hmul, h2, hone]
  have hE₁₂ : E₁ * E₂ = E₂ * E₁ := by rw [hE₁, hE₂, ← hmul, ← hmul, h3]
  have hXE₁ : X * E₁ = E₁ * X := by rw [hX, hE₁, ← hmul, ← hmul, h9]
  have hXE₂ : X * E₂ = E₂ * X := by rw [hX, hE₂, ← hmul, ← hmul, h10]
  have hYX : Y * X = X * Y := by rw [hX, hY, ← hmul, ← hmul, h11]
  have hE₁Y : E₁ * Y = Y * E₂ := by rw [hY, hE₁, hE₂, ← hmul, ← hmul, h12]
  have hE₂Y : E₂ * Y = Y * (E₁ * E₂) := by rw [hY, hE₁, hE₂, ← hmul, ← hmul, ← hmul, h13]
  have hE₁1 : E₁ ≠ 1 := by rw [hE₁, ← hone]; exact hne _ _ h4
  have hX1 : X ≠ 1 := by rw [hX, ← hone]; exact hne _ _ h8
  have hfixX : ∀ v : Vec4, X *ᵥ v = v → v = 0 := fun v hv =>
    fixed_eq_zero_of_fourGroup hX3 hX1 hE₁₁ hE₂₂ hXE₁ hXE₂ hE₁₂ hE₁1
      (by rw [hE₂, ← hone]; exact hne _ _ h5) (by rw [hE₁, hE₂]; exact hne _ _ h6) hv
  obtain ⟨v₀, hv₀, hE₁v₀, hE₂v₀⟩ := exists_fixed_pair hE₁₁ hE₂₂ hE₁₂ hE₁1
  have hcases := fun w hw => eq_of_fixed hX3 hfixX hE₁1 hXE₁ hv₀ hE₁v₀ (w := w) hw
  have hYv₀ : E₁ *ᵥ (Y *ᵥ v₀) = Y *ᵥ v₀ := by
    rw [mulVec_mulVec, hE₁Y, ← mulVec_mulVec, hE₂v₀]
  have hYne : Y *ᵥ v₀ ≠ 0 := by
    intro h0
    have hY3 : Y ^ 3 = 1 := by rw [hY, ← hpow3, h14, hone]
    apply hv₀
    rw [← cube_mulVec hY3 v₀, h0, mulVec_zero, mulVec_zero]
  have key : ∀ γ : ↥(alternatingGroup (Fin 7)), m γ *ᵥ v₀ = v₀ → m γ * X = X * m γ →
      ∀ v : Vec4, E₁ *ᵥ v = v → m γ *ᵥ v = v := by
    intro γ hγ hγX v hv
    have hγXv : m γ *ᵥ (X *ᵥ v₀) = X *ᵥ v₀ := by
      rw [mulVec_mulVec, hγX, ← mulVec_mulVec, hγ]
    have hγXXv : m γ *ᵥ (X *ᵥ (X *ᵥ v₀)) = X *ᵥ (X *ᵥ v₀) := by
      rw [mulVec_mulVec, hγX, ← mulVec_mulVec, hγXv]
    rcases hcases v hv with rfl | rfl | rfl | rfl
    · exact mulVec_zero _
    · exact hγ
    · exact hγXv
    · exact hγXXv
  rcases hcases _ hYv₀ with h0 | hY0 | hY1 | hY2
  · exact absurd h0 hYne
  · exact ⟨a7c, h14, h15, fun v hv _ => key a7c hY0 hYX v hv⟩
  ·
    have hγm : m (a7c * (a7t * a7t)) = X * X * Y := by
      rw [hmul, hmul, ← hX, ← hY, ← mul_assoc, hYX, mul_assoc, hYX, ← mul_assoc]
    refine ⟨a7c * (a7t * a7t), h18, h19, fun v hv _ => key _ ?_ ?_ v hv⟩
    · rw [hγm, ← mulVec_mulVec, ← mulVec_mulVec, hY1, cube_mulVec hX3]
    · rw [hγm]
      simp only [mul_assoc, hYX]
  ·
    have hγm : m (a7c * a7t) = X * Y := by
      rw [hmul, ← hX, ← hY, hYX]
    refine ⟨a7c * a7t, h16, h17, fun v hv _ => key _ ?_ ?_ v hv⟩
    · rw [hγm, ← mulVec_mulVec, hY2, cube_mulVec hX3]
    · rw [hγm]
      simp only [mul_assoc, hYX]

end FFL

open FFL

theorem fixA7Four_holds : FixA7Four := by
  intro α
  obtain ⟨h1, h2, h3, -⟩ := a7_relations
  have hM : Function.Injective (α.toMonoidHom.comp altLift7) :=
    α.injective.comp altLift7_injective'
  obtain ⟨γ, hγ3, hγ1, hγ⟩ := exists_gamma_a7 _ hM
  refine ⟨Subgroup.closure {a7e₁, a7e₂}, isPGroup_closure_pair h1 h2 h3, γ, hγ3, hγ1, ?_⟩
  intro (m : Multiplicative (Fin 4 → ZMod 2)) _ hm
  have hfix : ∀ τ ∈ Subgroup.closure {a7e₁, a7e₂},
      ((α (altLift7 τ) : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ Multiplicative.toAdd m =
        Multiplicative.toAdd m := by
    intro τ hτ
    have h : a7Act α τ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) := hm τ hτ
    rw [Subgroup.mem_bot] at h
    exact congrArg Multiplicative.toAdd (mul_inv_eq_one.mp h)
  have hγm := hγ (Multiplicative.toAdd m)
    (hfix _ (Subgroup.subset_closure (Set.mem_insert _ _)))
    (hfix _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  show a7Act α γ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2)))
  rw [Subgroup.mem_bot]
  exact mul_inv_eq_one.mpr (congrArg Multiplicative.ofAdd hγm)

end CFSG.Quasithin.EmptyFaithfulMultiple
