module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace Ctx

theorem exists_swap (c : Ctx A B z V) {a : D} (haA : a ∈ A) (haT : a ∉ A ⊓ B)
    (ha2T : a * a ∉ A ⊓ B) : ∃ τ ∈ A ⊓ B, ∃ t' ∈ A ⊓ B, τ * a = a * a * t' := by
  by_contra hcon
  push Not at hcon
  have hconj : ∀ τ ∈ A ⊓ B, a⁻¹ * τ * a ∈ A ⊓ B := by
    intro τ hτ
    have hτk : τ * a ∈ A := A.mul_mem hτ.1 haA
    rcases coset_decomp c.hyp.gold.relIndex_left haA haT ha2T hτk with
      hT | ⟨t', ht', e⟩ | ⟨t', ht', e⟩
    · exfalso
      apply haT
      have : a = τ⁻¹ * (τ * a) := by group
      rw [this]
      exact (A ⊓ B).mul_mem ((A ⊓ B).inv_mem hτ) hT
    · have : a⁻¹ * τ * a = t' := by
        calc a⁻¹ * τ * a = a⁻¹ * (τ * a) := by group
          _ = a⁻¹ * (a * t') := by rw [e]
          _ = t' := by group
      rw [this]; exact ht'
    · exact absurd e (hcon τ hτ t' ht')
  have hle : A ⊓ B ≤ conjSub a (A ⊓ B) := fun τ hτ => by
    rw [mem_conjSub]; exact hconj τ hτ
  have heq : A ⊓ B = conjSub a (A ⊓ B) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hkN : a ∈ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) :=
    mem_normalizer_of_conjSub_eq heq.symm
  apply c.not_normal_T_left
  intro g hg
  rcases coset_decomp c.hyp.gold.relIndex_left haA haT ha2T hg with
    hT | ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
  · exact Subgroup.le_normalizer hT
  · exact Subgroup.mul_mem _ hkN (Subgroup.le_normalizer htT)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN hkN) (Subgroup.le_normalizer htT)

end Ctx

structure Gen (c : Ctx A B z V) where
  a : D
  a_mem : a ∈ A
  a_cube : a * a * a = 1
  a_not_T : a ∉ A ⊓ B
  a2_not_T : a * a ∉ A ⊓ B
  u₀ : D
  u₀_mem : u₀ ∈ conjClosure V B
  u₀_not : u₀ ∉ V
  τ : D
  τ_mem : τ ∈ A ⊓ B
  t' : D
  t'_mem : t' ∈ A ⊓ B
  swap : τ * a = a * a * t'

omit [Finite D] in
theorem Ctx.z_mem_V (c : Ctx A B z V) : z ∈ V := c.hyp.natural.z_mem_V

omit [Finite D] in
theorem Ctx.z_ne_one (c : Ctx A B z V) : z ≠ 1 := c.hyp.natural.z_ne

omit [Finite D] in
theorem Ctx.one_ne_z (c : Ctx A B z V) : (1 : D) ≠ z := c.hyp.natural.z_ne.symm

theorem Ctx.nonempty_gen (c : Ctx A B z V) : Nonempty (Gen c) := by
  obtain ⟨a, haA, ha3⟩ := c.hyp.gold.vertex_left.exists_order_three
  have haT := c.hyp.gold.vertex_left.not_mem_of_orderOf ha3
  have ha2T := c.hyp.gold.vertex_left.sq_not_mem_of_orderOf ha3
  have hcube : a * a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha3, pow_three'] at this
  obtain ⟨u₀, hu₀U, hu₀V⟩ : ∃ u₀ ∈ conjClosure V B, u₀ ∉ V := by
    by_contra hcon
    push Not at hcon
    exact c.hyp.not_conjClosure_le fun u hu => hcon u hu
  obtain ⟨τ, hτ, t', ht', hsw⟩ := c.exists_swap haA haT ha2T
  exact ⟨⟨a, haA, hcube, haT, ha2T, u₀, hu₀U, hu₀V, τ, hτ, t', ht', hsw⟩⟩

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

@[expose] def u₁ : D := g.a * g.u₀ * g.a⁻¹

@[expose] def u₂ : D := g.a * g.u₁ * g.a⁻¹

@[expose] def z₁ : D := g.a * z * g.a⁻¹

@[expose] def z₂ : D := g.a * g.z₁ * g.a⁻¹

omit [Finite D] in
theorem conj3 (x : D) : g.a * (g.a * (g.a * x * g.a⁻¹) * g.a⁻¹) * g.a⁻¹ = x := by
  have h := g.a_cube
  calc g.a * (g.a * (g.a * x * g.a⁻¹) * g.a⁻¹) * g.a⁻¹
      = (g.a * g.a * g.a) * x * (g.a * g.a * g.a)⁻¹ := by group
    _ = x := by rw [h]; group

omit [Finite D] in
theorem a_conj_u₂ : g.a * g.u₂ * g.a⁻¹ = g.u₀ := g.conj3 g.u₀

omit [Finite D] in
theorem ainv_conj_u₀ : g.a⁻¹ * g.u₀ * g.a = g.u₂ := by
  calc g.a⁻¹ * g.u₀ * g.a = g.a⁻¹ * (g.a * g.u₂ * g.a⁻¹) * g.a := by rw [g.a_conj_u₂]
    _ = g.u₂ := by group

omit [Finite D] in
theorem ainv_conj_u₁ : g.a⁻¹ * g.u₁ * g.a = g.u₀ := by
  unfold u₁; group

omit [Finite D] in
theorem ainv_conj_u₂ : g.a⁻¹ * g.u₂ * g.a = g.u₁ := by
  unfold u₂; group

omit [Finite D] in
theorem a_conj_z₂ : g.a * g.z₂ * g.a⁻¹ = z := g.conj3 z

omit [Finite D] in
theorem ainv_conj_z : g.a⁻¹ * z * g.a = g.z₂ := by
  calc g.a⁻¹ * z * g.a = g.a⁻¹ * (g.a * g.z₂ * g.a⁻¹) * g.a := by rw [g.a_conj_z₂]
    _ = g.z₂ := by group

omit [Finite D] in
theorem ainv_conj_z₁ : g.a⁻¹ * g.z₁ * g.a = z := by
  unfold z₁; group

omit [Finite D] in
theorem ainv_conj_z₂ : g.a⁻¹ * g.z₂ * g.a = g.z₁ := by
  unfold z₂; group

omit [Finite D] in
theorem u₂_eq : g.u₂ = (g.a * g.a) * g.u₀ * (g.a * g.a)⁻¹ := by
  unfold u₂ u₁; group

omit [Finite D] in
theorem u₀_mem_W : g.u₀ ∈ Wsub A B V := c.U_le_W g.u₀_mem

omit [Finite D] in
theorem u₁_mem_W : g.u₁ ∈ Wsub A B V := c.conj_mem_W g.a_mem g.u₀_mem

omit [Finite D] in
theorem u₂_mem_W : g.u₂ ∈ Wsub A B V := c.W_normal g.a_mem g.u₁_mem_W

theorem u₀_mem_Q : g.u₀ ∈ pCoreOf 2 A := c.W_le_Q g.u₀_mem_W

theorem u₁_mem_Q : g.u₁ ∈ pCoreOf 2 A := c.W_le_Q g.u₁_mem_W

theorem u₂_mem_Q : g.u₂ ∈ pCoreOf 2 A := c.W_le_Q g.u₂_mem_W

omit [Finite D] in
theorem z₁_mem : g.z₁ ∈ V := c.V_normal g.a_mem c.z_mem_V

omit [Finite D] in
theorem z₂_mem : g.z₂ ∈ V := c.V_normal g.a_mem g.z₁_mem

end Gen

omit [Finite D] in
theorem Ctx.U_comm (c : Ctx A B z V) {u u' : D} (hu : u ∈ conjClosure V B)
    (hu' : u' ∈ conjClosure V B) : u * u' = u' * u :=
  isElemAbelian_comm c.hyp.abelian hu hu'

omit [Finite D] in
theorem Ctx.U_sq (c : Ctx A B z V) {u : D} (hu : u ∈ conjClosure V B) : u * u = 1 := by
  have := isElemAbelian_pow_eq_one c.hyp.abelian hu
  rwa [pow_two] at this

omit [Finite D] in
theorem Ctx.V_comm_V (c : Ctx A B z V) {v v' : D} (hv : v ∈ V) (hv' : v' ∈ V) :
    v * v' = v' * v :=
  c.U_comm (le_conjClosure V B hv) (le_conjClosure V B hv')

omit [Finite D] in
theorem Ctx.V_sq (c : Ctx A B z V) {v : D} (hv : v ∈ V) : v * v = 1 :=
  c.U_sq (le_conjClosure V B hv)

omit [Finite D] in
theorem Ctx.exists_basis (c : Ctx A B z V) :
    ∃ a₀ : D, a₀ ≠ 1 ∧ a₀ ≠ z ∧ a₀ ∈ V ∧ z * a₀ ∈ V ∧
      ∀ v ∈ V, v = 1 ∨ v = z ∨ v = a₀ ∨ v = z * a₀ := by
  obtain ⟨a₀, h1, h2, hset⟩ := c.hyp.natural.basis
  have hmem : ∀ u, u ∈ V ↔ u = 1 ∨ u = z ∨ u = a₀ ∨ u = z * a₀ := by
    intro u
    have := Set.ext_iff.mp hset u
    simpa using this
  exact ⟨a₀, h1, h2, (hmem a₀).mpr (Or.inr (Or.inr (Or.inl rfl))),
    (hmem _).mpr (Or.inr (Or.inr (Or.inr rfl))), fun v hv => (hmem v).mp hv⟩

omit [Finite D] in
theorem Ctx.z_sq (c : Ctx A B z V) : z * z = 1 := by
  have := c.hyp.natural.z_sq
  rwa [pow_two] at this

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

theorem z₁_ne_z : g.z₁ ≠ z := by
  intro h
  apply g.a_not_T
  refine inf_normalizer_zpowers_le c.hyp.gold c.hyp.natural ⟨g.a_mem, ?_⟩
  exact mem_normalizer_zpowers_of_mul_comm (mul_eq_of_conj_eq h)

theorem z₂_ne_z : g.z₂ ≠ z := by
  intro h
  apply g.z₁_ne_z
  have e := g.a_conj_z₂
  rw [h] at e
  exact e

theorem z₁_ne_z₂ : g.z₁ ≠ g.z₂ := by
  intro h
  apply g.z₂_ne_z
  have e := g.a_conj_z₂
  calc g.z₂ = g.a * g.z₁ * g.a⁻¹ := rfl
    _ = g.a * g.z₂ * g.a⁻¹ := by rw [h]
    _ = z := e

omit [Finite D] in
theorem z₁_ne_one : g.z₁ ≠ 1 := by
  intro h
  apply c.hyp.natural.z_ne
  have : g.a⁻¹ * g.z₁ * g.a = z := g.ainv_conj_z₁
  rw [h] at this
  simpa using this.symm

omit [Finite D] in
theorem z₂_ne_one : g.z₂ ≠ 1 := by
  intro h
  apply g.z₁_ne_one
  have : g.a⁻¹ * g.z₂ * g.a = g.z₁ := g.ainv_conj_z₂
  rw [h] at this
  simpa using this.symm

theorem V_structure :
    (∀ v ∈ V, v = 1 ∨ v = z ∨ v = g.z₁ ∨ v = g.z₂) ∧ z * g.z₁ = g.z₂ := by
  obtain ⟨a₀, h1, h2, ha₀, hza₀, hcases⟩ := c.exists_basis
  have hz1 := hcases _ g.z₁_mem
  have hz2 := hcases _ g.z₂_mem
  have hzz := c.z_sq
  have e1 := g.z₁_ne_one
  have e2 := g.z₂_ne_one
  have n1 := g.z₁_ne_z
  have n2 := g.z₂_ne_z
  have n12 := g.z₁_ne_z₂
  have hmul : ∀ x : D, z * (z * x) = x := fun x => by rw [← mul_assoc, hzz, one_mul]
  rcases hz1 with h | h | h | h
  · exact absurd h e1
  · exact absurd h n1
  · rcases hz2 with h' | h' | h' | h'
    · exact absurd h' e2
    · exact absurd h' n2
    · exact absurd (h.trans h'.symm) n12
    · refine ⟨fun v hv => ?_, by rw [h, h']⟩
      rcases hcases v hv with e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl (e.trans h.symm)))
      · exact Or.inr (Or.inr (Or.inr (e.trans h'.symm)))
  · rcases hz2 with h' | h' | h' | h'
    · exact absurd h' e2
    · exact absurd h' n2
    · refine ⟨fun v hv => ?_, by rw [h, h', hmul]⟩
      rcases hcases v hv with e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr (e.trans h'.symm)))
      · exact Or.inr (Or.inr (Or.inl (e.trans h.symm)))
    · exact absurd (h.trans h'.symm) n12

theorem V_cases {v : D} (hv : v ∈ V) : v = 1 ∨ v = z ∨ v = g.z₁ ∨ v = g.z₂ :=
  g.V_structure.1 v hv

theorem z_mul_z₁ : z * g.z₁ = g.z₂ := g.V_structure.2

theorem z₁_mul_z : g.z₁ * z = g.z₂ := by
  rw [← g.z_mul_z₁]; exact (c.V_comm_V g.z₁_mem c.z_mem_V)

theorem z₁_mul_z₂ : g.z₁ * g.z₂ = z := by
  have h1 := c.V_comm_V g.z₁_mem c.z_mem_V
  have h2 := c.V_sq g.z₁_mem
  calc g.z₁ * g.z₂ = g.z₁ * (z * g.z₁) := by rw [g.z_mul_z₁]
    _ = (g.z₁ * z) * g.z₁ := by rw [mul_assoc]
    _ = (z * g.z₁) * g.z₁ := by rw [h1]
    _ = z * (g.z₁ * g.z₁) := by rw [mul_assoc]
    _ = z := by rw [h2, mul_one]

theorem z₂_mul_z₁ : g.z₂ * g.z₁ = z :=
  (c.V_comm_V g.z₂_mem g.z₁_mem).trans g.z₁_mul_z₂

theorem z_mul_z₂ : z * g.z₂ = g.z₁ := by
  rw [← g.z_mul_z₁, ← mul_assoc, c.z_sq, one_mul]

theorem z₂_mul_z : g.z₂ * z = g.z₁ := by
  rw [← g.z_mul_z₂]; exact c.V_comm_V g.z₂_mem c.z_mem_V

omit [Finite D] in
theorem z₁_mul_z₁ : g.z₁ * g.z₁ = 1 := c.V_sq g.z₁_mem

omit [Finite D] in
theorem z₂_mul_z₂ : g.z₂ * g.z₂ = 1 := c.V_sq g.z₂_mem

omit [Finite D] in
theorem a_conj_z : g.a * z * g.a⁻¹ = g.z₁ := rfl

omit [Finite D] in
theorem a_conj_z₁ : g.a * g.z₁ * g.a⁻¹ = g.z₂ := rfl

omit [Finite D] in
theorem a_conj_u₀ : g.a * g.u₀ * g.a⁻¹ = g.u₁ := rfl

omit [Finite D] in
theorem a_conj_u₁ : g.a * g.u₁ * g.a⁻¹ = g.u₂ := rfl

theorem z_ne_z₁ : z ≠ g.z₁ := g.z₁_ne_z.symm

theorem z_ne_z₂ : z ≠ g.z₂ := g.z₂_ne_z.symm

theorem z₂_ne_z₁ : g.z₂ ≠ g.z₁ := g.z₁_ne_z₂.symm

omit [Finite D] in
theorem one_ne_z₁ : (1 : D) ≠ g.z₁ := g.z₁_ne_one.symm

omit [Finite D] in
theorem one_ne_z₂ : (1 : D) ≠ g.z₂ := g.z₂_ne_one.symm

omit [Finite D] in
theorem U_form {u : D} (hu : u ∈ conjClosure V B) : ∃ v ∈ V, u = v ∨ u = v * g.u₀ := by
  by_cases huV : u ∈ V
  · exact ⟨u, huV, Or.inl rfl⟩
  · refine ⟨u * g.u₀⁻¹, c.hyp.mul_inv_mem_V_of_not_mem c.card_eq hu g.u₀_mem huV g.u₀_not,
      Or.inr ?_⟩
    group

omit [Finite D] in
theorem conj_form_U {x u' w : D} (hx : x ∈ A) (hxw : x * g.u₀ * x⁻¹ = w)
    (hu' : u' ∈ conjClosure V B) : ∃ v ∈ V, x * u' * x⁻¹ = v ∨ x * u' * x⁻¹ = v * w := by
  obtain ⟨v₀, hv₀, h | h⟩ := g.U_form hu'
  · refine ⟨x * v₀ * x⁻¹, c.V_normal hx hv₀, Or.inl ?_⟩
    rw [h]
  · refine ⟨x * v₀ * x⁻¹, c.V_normal hx hv₀, Or.inr ?_⟩
    rw [h, ← hxw]; group

theorem gen_form {g' u : D} (hg' : g' ∈ A) (hu : u ∈ conjClosure V B) :
    ∃ v ∈ V, g' * u * g'⁻¹ = v ∨ g' * u * g'⁻¹ = v * g.u₀ ∨ g' * u * g'⁻¹ = v * g.u₁ ∨
      g' * u * g'⁻¹ = v * g.u₂ := by
  have hAA : g.a * g.a ∈ A := A.mul_mem g.a_mem g.a_mem
  rcases coset_decomp c.hyp.gold.relIndex_left g.a_mem g.a_not_T g.a2_not_T hg' with
    hT | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · obtain ⟨v, hv, h⟩ := g.conj_form_U (w := g.u₀) (A.one_mem) (by group)
      (c.U_normal hT.2 hu)
    refine ⟨v, hv, ?_⟩
    simp only [inv_one, one_mul, mul_one] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨v, hv, h⟩ := g.conj_form_U g.a_mem g.a_conj_u₀ (c.U_normal ht.2 hu)
    have e : g.a * t * u * (g.a * t)⁻¹ = g.a * (t * u * t⁻¹) * g.a⁻¹ := by group
    refine ⟨v, hv, ?_⟩
    rw [e]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨v, hv, h⟩ := g.conj_form_U hAA g.u₂_eq.symm (c.U_normal ht.2 hu)
    have e : g.a * g.a * t * u * (g.a * g.a * t)⁻¹ =
        (g.a * g.a) * (t * u * t⁻¹) * (g.a * g.a)⁻¹ := by group
    refine ⟨v, hv, ?_⟩
    rw [e]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))

omit [Finite D] in
theorem T_conj_u₀ {t : D} (ht : t ∈ A ⊓ B) : ∃ v ∈ V, t * g.u₀ * t⁻¹ = v * g.u₀ := by
  have hU' : t * g.u₀ * t⁻¹ ∈ conjClosure V B := c.U_normal ht.2 g.u₀_mem
  have hnV : t * g.u₀ * t⁻¹ ∉ V := by
    intro hV
    apply g.u₀_not
    have := c.V_normal (A.inv_mem ht.1) hV
    simpa [mul_assoc] using this
  refine ⟨t * g.u₀ * t⁻¹ * g.u₀⁻¹, c.hyp.mul_inv_mem_V_of_not_mem c.card_eq hU' g.u₀_mem hnV
    g.u₀_not, ?_⟩
  group

theorem comm01_ne : ⁅g.u₀, g.u₁⁆ ≠ 1 := by
  intro h01
  have h01' : g.u₀ * g.u₁ = g.u₁ * g.u₀ := comm_eq_one_iff.mp h01
  have h20 : g.u₂ * g.u₀ = g.u₀ * g.u₂ := by
    have e := conj_comm g.a⁻¹ g.u₀ g.u₁
    simp only [inv_inv, g.ainv_conj_u₀, g.ainv_conj_u₁, h01] at e
    have e' : ⁅g.u₂, g.u₀⁆ = 1 := by simpa using e.symm
    exact (comm_eq_one_iff.mp e').symm.symm
  have hVK : ∀ v ∈ V, v ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := fun v hv =>
    c.M_le_K (c.V_le_M hv)
  have hu₀K : g.u₀ ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B :=
    (c.mem_K_iff).mpr ⟨g.u₀_mem_Q, fun u' hu' => c.U_comm hu' g.u₀_mem⟩
  have hu₁K : g.u₁ ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B :=
    (c.mem_K_iff).mpr ⟨g.u₁_mem_Q, fun u' hu' => by
      obtain ⟨v, hv, h | h⟩ := g.U_form hu'
      · subst h; exact c.V_comm hv g.u₁_mem_Q
      · subst h
        calc v * g.u₀ * g.u₁ = v * (g.u₀ * g.u₁) := by group
          _ = v * (g.u₁ * g.u₀) := by rw [h01']
          _ = (v * g.u₁) * g.u₀ := by group
          _ = (g.u₁ * v) * g.u₀ := by rw [c.V_comm hv g.u₁_mem_Q]
          _ = g.u₁ * (v * g.u₀) := by group⟩
  have hu₂K : g.u₂ ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B :=
    (c.mem_K_iff).mpr ⟨g.u₂_mem_Q, fun u' hu' => by
      obtain ⟨v, hv, h | h⟩ := g.U_form hu'
      · subst h; exact c.V_comm hv g.u₂_mem_Q
      · subst h
        calc v * g.u₀ * g.u₂ = v * (g.u₀ * g.u₂) := by group
          _ = v * (g.u₂ * g.u₀) := by rw [h20]
          _ = (v * g.u₂) * g.u₀ := by group
          _ = (g.u₂ * v) * g.u₀ := by rw [c.V_comm hv g.u₂_mem_Q]
          _ = g.u₂ * (v * g.u₀) := by group⟩
  have hWK : conjClosure (conjClosure V B) A ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
    refine conjClosure_le fun g' hg' u hu => ?_
    obtain ⟨v, hv, h | h | h | h⟩ := g.gen_form hg' hu <;> rw [h]
    · exact hVK v hv
    · exact Subgroup.mul_mem _ (hVK v hv) hu₀K
    · exact Subgroup.mul_mem _ (hVK v hv) hu₁K
    · exact Subgroup.mul_mem _ (hVK v hv) hu₂K
  have h4 := c.hyp.four_le_critDist_iff_le_coreIn.mpr hWK
  have h3 := c.crit_eq
  omega

theorem τ_not_Q : g.τ ∉ pCoreOf 2 A := by
  intro hτ
  apply g.a_not_T
  have h1 : g.a⁻¹ * g.τ * g.a ∈ pCoreOf 2 A := by
    simpa using pCoreOf_conj_mem (A.inv_mem g.a_mem) hτ
  have h2 : g.a * g.t' = g.a⁻¹ * g.τ * g.a := by
    calc g.a * g.t' = g.a⁻¹ * (g.a * g.a * g.t') := by group
      _ = g.a⁻¹ * (g.τ * g.a) := by rw [g.swap]
      _ = _ := by group
  have h3 : g.a = (g.a⁻¹ * g.τ * g.a) * g.t'⁻¹ := by rw [← h2]; group
  rw [h3]
  exact (A ⊓ B).mul_mem (c.Q_le_T h1) ((A ⊓ B).inv_mem g.t'_mem)

theorem τ_sq_mem : g.τ * g.τ ∈ pCoreOf 2 A := by
  have := GoldAmN.sq_mem_of_relIndex_two c.Q_le_T (inf_le_left.trans (le_normalizer_pCoreOf 2 A))
    c.hyp.gold.relIndex_pCoreOf_T_left g.τ_mem
  rwa [pow_two] at this

theorem fix_tau {v : D} (hv : v ∈ V) (hfix : g.τ * v * g.τ⁻¹ = v) : v = 1 ∨ v = z := by
  by_contra hcon
  push Not at hcon
  apply g.τ_not_Q
  rw [← c.hyp.natural.centralizer_eq]
  have hz : g.τ * z = z * g.τ :=
    Subgroup.mem_centralizer_iff.mp c.hyp.natural.z_mem.2 g.τ g.τ_mem
  have hv' : g.τ * v = v * g.τ := mul_eq_of_conj_eq hfix
  have hz₁₂ : g.τ * g.z₁ = g.z₁ * g.τ ∧ g.τ * g.z₂ = g.z₂ * g.τ := by
    have key : ∀ x y : D, g.τ * x = x * g.τ → g.τ * y = y * g.τ → g.τ * (x * y) = (x * y) * g.τ :=
      fun x y hx hy => by
        calc g.τ * (x * y) = (g.τ * x) * y := by rw [mul_assoc]
          _ = x * (g.τ * y) := by rw [hx, mul_assoc]
          _ = x * (y * g.τ) := by rw [hy]
          _ = (x * y) * g.τ := by rw [mul_assoc]
    rcases g.V_cases hv with e | e | e | e
    · exact absurd e hcon.1
    · exact absurd e hcon.2
    · subst e
      refine ⟨hv', ?_⟩
      rw [← g.z_mul_z₁]
      exact key z _ hz hv'
    · subst e
      refine ⟨?_, hv'⟩
      rw [← g.z_mul_z₂]
      exact key z _ hz hv'
  refine ⟨g.τ_mem.1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  rcases g.V_cases hx with e | e | e | e
  · subst e; simp
  · subst e; exact hz.symm
  · subst e; exact hz₁₂.1.symm
  · subst e; exact hz₁₂.2.symm

omit [Finite D] in
theorem swap_u₁ : ∃ v ∈ V, g.τ * g.u₁ * g.τ⁻¹ = v * g.u₂ := by
  obtain ⟨v, hv, hvt⟩ := g.T_conj_u₀ g.t'_mem
  refine ⟨(g.a * g.a) * v * (g.a * g.a)⁻¹, c.V_normal (A.mul_mem g.a_mem g.a_mem) hv, ?_⟩
  have e : g.τ * g.u₁ * g.τ⁻¹ = (g.a * g.a) * (g.t' * g.u₀ * g.t'⁻¹) * (g.a * g.a)⁻¹ := by
    calc g.τ * g.u₁ * g.τ⁻¹ = (g.τ * g.a) * g.u₀ * (g.τ * g.a)⁻¹ := by unfold u₁; group
      _ = (g.a * g.a * g.t') * g.u₀ * (g.a * g.a * g.t')⁻¹ := by rw [g.swap]
      _ = _ := by group
  rw [e, hvt, g.u₂_eq]
  group

theorem swap_u₂ : ∃ v ∈ V, g.τ * g.u₂ * g.τ⁻¹ = v * g.u₁ := by
  obtain ⟨v₂, hv₂, h₂⟩ := g.swap_u₁
  have hτA : g.τ ∈ A := g.τ_mem.1
  have hc : ⁅g.τ * g.τ, g.u₁⁆ ∈ V := by
    have h1 := c.comm_W_Q g.u₁_mem_W g.τ_sq_mem
    rw [← commutatorElement_inv]
    exact V.inv_mem h1
  refine ⟨(g.τ * v₂ * g.τ⁻¹)⁻¹ * ⁅g.τ * g.τ, g.u₁⁆,
    V.mul_mem (V.inv_mem (c.V_normal hτA hv₂)) hc, ?_⟩
  have e1 : g.τ * (g.τ * g.u₁ * g.τ⁻¹) * g.τ⁻¹ = ⁅g.τ * g.τ, g.u₁⁆ * g.u₁ := by
    simp only [commutatorElement_def]; group
  rw [h₂] at e1
  calc g.τ * g.u₂ * g.τ⁻¹ = (g.τ * v₂ * g.τ⁻¹)⁻¹ * (g.τ * (v₂ * g.u₂) * g.τ⁻¹) := by group
    _ = _ := by rw [e1]; group

end Gen

theorem Ctx.comm_V_mul_left (c : Ctx A B z V) {v u y : D} (hv : v ∈ V) (hu : u ∈ pCoreOf 2 A)
    (hy : y ∈ pCoreOf 2 A) : ⁅v * u, y⁆ = ⁅u, y⁆ := by
  have h1 : ⁅v, y⁆ = 1 := comm_eq_one_iff.mpr (c.V_comm hv hy)
  have hQ : ⁅u, y⁆ ∈ pCoreOf 2 A := by
    simp only [commutatorElement_def]
    exact (pCoreOf 2 A).mul_mem ((pCoreOf 2 A).mul_mem ((pCoreOf 2 A).mul_mem hu hy)
      ((pCoreOf 2 A).inv_mem hu)) ((pCoreOf 2 A).inv_mem hy)
  rw [comm_mul_left, h1, mul_one]
  exact conj_eq_of_comm (c.V_comm hv hQ)

theorem Ctx.comm_V_mul_right (c : Ctx A B z V) {v u y : D} (hv : v ∈ V) (hu : u ∈ pCoreOf 2 A)
    (hy : y ∈ pCoreOf 2 A) : ⁅y, v * u⁆ = ⁅y, u⁆ := by
  have h1 : ⁅y, v⁆ = 1 := comm_eq_one_iff.mpr (c.V_comm hv hy).symm
  have hQ : ⁅y, u⁆ ∈ pCoreOf 2 A := by
    simp only [commutatorElement_def]
    exact (pCoreOf 2 A).mul_mem ((pCoreOf 2 A).mul_mem ((pCoreOf 2 A).mul_mem hy hu)
      ((pCoreOf 2 A).inv_mem hy)) ((pCoreOf 2 A).inv_mem hu)
  rw [comm_mul_right, h1, one_mul]
  exact conj_eq_of_comm (c.V_comm hv hQ)

omit [Finite D] in
theorem Ctx.inv_eq_self (c : Ctx A B z V) {v : D} (hv : v ∈ V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (c.V_sq hv)

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

theorem comm12 : ⁅g.u₁, g.u₂⁆ = z := by
  have hxV : ⁅g.u₁, g.u₂⁆ ∈ V := c.comm_W_Q g.u₁_mem_W g.u₂_mem_Q
  obtain ⟨v₂, hv₂, h₂⟩ := g.swap_u₁
  obtain ⟨v₃, hv₃, h₃⟩ := g.swap_u₂
  have hfix : g.τ * ⁅g.u₁, g.u₂⁆ * g.τ⁻¹ = ⁅g.u₁, g.u₂⁆ := by
    rw [conj_comm, h₂, h₃, c.comm_V_mul_left hv₂ g.u₂_mem_Q
      ((pCoreOf 2 A).mul_mem (c.U_le_Q (c.V_le_U hv₃)) g.u₁_mem_Q),
      c.comm_V_mul_right hv₃ g.u₁_mem_Q g.u₂_mem_Q, ← commutatorElement_inv]
    exact c.inv_eq_self hxV
  have hne : ⁅g.u₁, g.u₂⁆ ≠ 1 := by
    intro h1
    apply g.comm01_ne
    have e := conj_comm g.a g.u₀ g.u₁
    rw [g.a_conj_u₀, g.a_conj_u₁, h1] at e
    simpa using e
  rcases g.fix_tau hxV hfix with h | h
  · exact absurd h hne
  · exact h

theorem comm01 : ⁅g.u₀, g.u₁⁆ = g.z₂ := by
  have e := conj_comm g.a⁻¹ g.u₁ g.u₂
  rw [inv_inv, g.ainv_conj_u₁, g.ainv_conj_u₂, g.comm12, g.ainv_conj_z] at e
  exact e.symm

theorem comm20 : ⁅g.u₂, g.u₀⁆ = g.z₁ := by
  have e := conj_comm g.a g.u₁ g.u₂
  rw [g.a_conj_u₁, g.a_conj_u₂, g.comm12] at e
  exact e.symm

end Gen

end GoldAmL3E

end F6

end CFSG.Quasithin
