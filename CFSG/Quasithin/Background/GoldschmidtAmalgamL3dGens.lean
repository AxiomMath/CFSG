module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Card

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure Gens (A B : Subgroup D) (z : D) (V : Subgroup D) : Type _ where
  x : D
  a : D
  mem_B : x ∈ B
  cube : x * x * x = 1
  not_mem_T : x ∉ A ⊓ B
  sq_not_mem_T : x * x ∉ A ⊓ B
  mem_V : a ∈ V
  ne_one : a ≠ 1
  ne_z : a ≠ z
  V_eq : (V : Set D) = {1, z, a, z * a}

namespace Gens

variable (g : Gens A B z V)

@[expose] def a₂ : D := g.x * g.a * g.x⁻¹

@[expose] def a₃ : D := g.x * g.x * g.a * (g.x * g.x)⁻¹

@[expose] def c₂₃ : D := g.a₂ * g.a₃

end Gens

omit [Finite D] in
theorem T_conj_U {t w : D} (ht : t ∈ A ⊓ B) (hw : w ∈ conjClosure V B) :
    t * w * t⁻¹ ∈ conjClosure V B :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B ht.2) w).mp hw

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem nonempty_gens : Nonempty (Gens A B z V) := by
  obtain ⟨x, hxB, hx3⟩ := h.gold.vertex_right.exists_order_three
  obtain ⟨a, ha1, haz, hVset⟩ := h.natural.basis
  have hx3' : x * x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3, pow_three'] at this
  have haV : a ∈ V := by
    have : a ∈ (V : Set D) := by rw [hVset]; simp
    exact this
  exact ⟨⟨x, a, hxB, hx3', h.gold.vertex_right.not_mem_of_orderOf hx3,
    h.gold.vertex_right.sq_not_mem_of_orderOf hx3, haV, ha1, haz, hVset⟩⟩

omit [Finite D] in
theorem U_comm {u v : D} (hu : u ∈ conjClosure V B) (hv : v ∈ conjClosure V B) :
    u * v = v * u :=
  isElemAbelian_comm h.abelian hu hv

omit [Finite D] in
theorem U_sq {u : D} (hu : u ∈ conjClosure V B) : u * u = 1 := by
  have := h.abelian.2 u hu
  rwa [pow_two] at this

omit [Finite D] in
theorem z_mem_U : z ∈ conjClosure V B := le_conjClosure V B h.natural.z_mem_V

omit [Finite D] in
theorem T_comm_z {t : D} (ht : t ∈ A ⊓ B) : t * z = z * t :=
  Subgroup.mem_centralizer_iff.mp h.natural.z_mem.2 t ht

omit [Finite D] in
theorem T_conj_V {t v : D} (ht : t ∈ A ⊓ B) (hv : v ∈ V) : t * v * t⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 ht.1) v).mp hv

omit [Finite D] in
theorem mem_V_of_conj_mem_V {t w : D} (ht : t ∈ A ⊓ B) (hw : t * w * t⁻¹ ∈ V) : w ∈ V := by
  have := h.T_conj_V (Subgroup.inv_mem _ ht) hw
  simpa [mul_assoc] using this

theorem card_sup_zpowers_le {w : D} (hw : w ∈ conjClosure V B) :
    Nat.card ↥(V ⊔ Subgroup.zpowers w) ≤ 8 := by
  have hw2 : w ^ 2 = 1 := h.abelian.2 w hw
  have hV : V ≤ Subgroup.normalizer (Subgroup.zpowers w : Set D) := fun v hv =>
    mem_normalizer_zpowers_of_mul_comm (h.U_comm (le_conjClosure V B hv) hw)
  have c1 := GoldAmN.card_sup_le_of_le_normalizer V (Subgroup.zpowers w) hV
  rw [h.natural.card_eq] at c1
  have c2 := Nat.mul_le_mul_left 4 (card_zpowers_le_two hw2)
  omega

omit [Finite D] in
theorem T_conj_z {t : D} (ht : t ∈ A ⊓ B) : t * z * t⁻¹ = z := by
  have := h.T_comm_z ht
  calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [this]
    _ = z := by group

omit [Finite D] in
theorem U_conj_of_mem_zpowers {x c : D} (hx : x ∈ conjClosure V B)
    (hc : c ∈ Subgroup.zpowers z) : x * c * x⁻¹ = c := by
  have hxz : x ∈ Subgroup.centralizer (Subgroup.zpowers z : Set D) :=
    mem_centralizer_zpowers_of_mul_comm (h.U_comm hx h.z_mem_U)
  have := Subgroup.mem_centralizer_iff.mp hxz c hc
  calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [← this]
    _ = c := by group

omit [Finite D] in
theorem U_inv_conj_of_mem_zpowers {x c : D} (hx : x ∈ conjClosure V B)
    (hc : c ∈ Subgroup.zpowers z) : x⁻¹ * c * x = c := by
  have := h.U_conj_of_mem_zpowers (Subgroup.inv_mem _ hx) hc
  simpa using this

omit [Finite D] in
theorem line_mul_mem {w p q : D} (hw : w ∈ conjClosure V B) (hp : p = w ∨ p = z * w)
    (hq : q = w ∨ q = z * w) : p * q ∈ V := by
  have hww : w * w = 1 := h.U_sq hw
  have hzw : z * w = w * z := h.U_comm h.z_mem_U hw
  have hzz : z * z = 1 := by
    have := h.natural.z_sq
    rwa [pow_two] at this
  have hzV : z ∈ V := h.natural.z_mem_V
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq]
  · rw [hww]; exact V.one_mem
  · have : w * (z * w) = z := by
      calc w * (z * w) = (w * z) * w := by group
        _ = (z * w) * w := by rw [← hzw]
        _ = z * (w * w) := by group
        _ = z := by rw [hww, mul_one]
    rw [this]; exact hzV
  · have : z * w * w = z := by
      calc z * w * w = z * (w * w) := by group
        _ = z := by rw [hww, mul_one]
    rw [this]; exact hzV
  · have : z * w * (z * w) = 1 := by
      calc z * w * (z * w) = z * (w * z) * w := by group
        _ = z * (z * w) * w := by rw [← hzw]
        _ = (z * z) * (w * w) := by group
        _ = 1 := by rw [hzz, hww, mul_one]
    rw [this]; exact V.one_mem

omit [Finite D] in
theorem line_mul_eq {w₁ w₂ p q : D} (hw₁ : w₁ ∈ conjClosure V B)
    (hp : p = w₁ ∨ p = z * w₁) (hq : q = w₂ ∨ q = z * w₂) :
    p * q = w₁ * w₂ ∨ p * q = z * (w₁ * w₂) := by
  have hzw : z * w₁ = w₁ * z := h.U_comm h.z_mem_U hw₁
  have hzz : z * z = 1 := by
    have := h.natural.z_sq
    rwa [pow_two] at this
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq]
  · exact Or.inl rfl
  · right
    calc w₁ * (z * w₂) = (w₁ * z) * w₂ := by group
      _ = z * (w₁ * w₂) := by rw [← hzw]; group
  · right
    group
  · left
    calc z * w₁ * (z * w₂) = z * (w₁ * z) * w₂ := by group
      _ = z * (z * w₁) * w₂ := by rw [← hzw]
      _ = (z * z) * (w₁ * w₂) := by group
      _ = w₁ * w₂ := by rw [hzz, one_mul]

end GoldHyp3

namespace Gens

variable (g : Gens A B z V) (h : GoldHyp3 A B z V)

include h

omit [Finite D] h in
theorem a_mem_U : g.a ∈ conjClosure V B := le_conjClosure V B g.mem_V

omit [Finite D] h in
theorem a₂_mem_U : g.a₂ ∈ conjClosure V B :=
  HypF91.conjSub_le_conjClosure g.mem_B (mul_mem_conjSub g.mem_V)

omit [Finite D] h in
theorem a₃_mem_U : g.a₃ ∈ conjClosure V B :=
  HypF91.conjSub_le_conjClosure (B.mul_mem g.mem_B g.mem_B) (mul_mem_conjSub g.mem_V)

omit [Finite D] h in
theorem c₂₃_mem_U : g.c₂₃ ∈ conjClosure V B :=
  Subgroup.mul_mem _ (g.a₂_mem_U) (g.a₃_mem_U)

omit [Finite D] in
theorem c₂₃_sq : g.c₂₃ * g.c₂₃ = 1 := by
  have h2 := h.U_sq (g.a₂_mem_U)
  have h3 := h.U_sq (g.a₃_mem_U)
  have hc : g.a₂ * g.a₃ = g.a₃ * g.a₂ := h.U_comm (g.a₂_mem_U) (g.a₃_mem_U)
  unfold Gens.c₂₃
  calc g.a₂ * g.a₃ * (g.a₂ * g.a₃) = g.a₂ * (g.a₃ * g.a₂) * g.a₃ := by group
    _ = g.a₂ * (g.a₂ * g.a₃) * g.a₃ := by rw [← hc]
    _ = (g.a₂ * g.a₂) * (g.a₃ * g.a₃) := by group
    _ = 1 := by rw [h2, h3, one_mul]

theorem conjClosure_le_sup :
    conjClosure V B ≤ V ⊔ Subgroup.zpowers g.a₂ ⊔ Subgroup.zpowers g.a₃ := by
  have hxB := g.mem_B
  have hxxB : g.x * g.x ∈ B := B.mul_mem hxB hxB
  have hzV : z ∈ V := h.natural.z_mem_V
  have hmemV : ∀ v' ∈ V, v' = 1 ∨ v' = z ∨ v' = g.a ∨ v' = z * g.a := by
    intro v' hv'
    have : v' ∈ (V : Set D) := hv'
    rw [g.V_eq] at this
    simpa using this
  have hz₁ : g.x * z * g.x⁻¹ = z := h.central g.x hxB
  have hz₂ : g.x * g.x * z * (g.x * g.x)⁻¹ = z := h.central (g.x * g.x) hxxB
  have hS₁ : ∀ v' ∈ V, g.x * v' * g.x⁻¹ ∈
      V ⊔ Subgroup.zpowers g.a₂ ⊔ Subgroup.zpowers g.a₃ := by
    intro v' hv'
    rcases hmemV v' hv' with e | e | e | e
    · simp [e]
    · rw [e, hz₁]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hzV)
    · rw [e]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · have e' : g.x * (z * g.a) * g.x⁻¹ = (g.x * z * g.x⁻¹) * (g.x * g.a * g.x⁻¹) := by group
      rw [e, e', hz₁]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hzV))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hS₂ : ∀ v' ∈ V, g.x * g.x * v' * (g.x * g.x)⁻¹ ∈
      V ⊔ Subgroup.zpowers g.a₂ ⊔ Subgroup.zpowers g.a₃ := by
    intro v' hv'
    rcases hmemV v' hv' with e | e | e | e
    · simp [e]
    · rw [e, hz₂]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hzV)
    · rw [e]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · have e' : g.x * g.x * (z * g.a) * (g.x * g.x)⁻¹ =
          (g.x * g.x * z * (g.x * g.x)⁻¹) * (g.x * g.x * g.a * (g.x * g.x)⁻¹) := by group
      rw [e, e', hz₂]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hzV))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  refine conjClosure_le fun k hk v hv => ?_
  rcases coset_decomp h.gold.relIndex_right hxB g.not_mem_T g.sq_not_mem_T hk with hkT |
      ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
  · have : k * v * k⁻¹ ∈ V := h.T_conj_V hkT hv
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left this)
  · have htv : t * v * t⁻¹ ∈ V := h.T_conj_V htT hv
    have e : g.x * t * v * (g.x * t)⁻¹ = g.x * (t * v * t⁻¹) * g.x⁻¹ := by group
    rw [e]; exact hS₁ _ htv
  · have htv : t * v * t⁻¹ ∈ V := h.T_conj_V htT hv
    have e : g.x * g.x * t * v * (g.x * g.x * t)⁻¹ =
        g.x * g.x * (t * v * t⁻¹) * (g.x * g.x)⁻¹ := by group
    rw [e]; exact hS₂ _ htv

theorem a₂_not_mem_sup (hU : Nat.card (conjClosure V B) = 16) :
    g.a₂ ∉ V ⊔ Subgroup.zpowers g.a₃ := by
  intro hmem
  have hle : conjClosure V B ≤ V ⊔ Subgroup.zpowers g.a₃ :=
    (g.conjClosure_le_sup h).trans
      (sup_le (sup_le le_sup_left (Subgroup.zpowers_le.mpr hmem)) le_sup_right)
  have h1 := Subgroup.card_le_of_le hle
  have h2 := h.card_sup_zpowers_le (g.a₃_mem_U)
  omega

theorem a₂_mul_a₃_not_mem_V (hU : Nat.card (conjClosure V B) = 16) : g.a₂ * g.a₃ ∉ V := by
  intro hmem
  apply g.a₂_not_mem_sup h hU
  have e : g.a₂ = g.a₂ * g.a₃ * g.a₃⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
    (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))

omit [Finite D] in
theorem T_conj_a {t : D} (ht : t ∈ A ⊓ B) :
    t * g.a * t⁻¹ = g.a ∨ t * g.a * t⁻¹ = z * g.a := by
  have hmem : t * g.a * t⁻¹ ∈ (V : Set D) := h.T_conj_V ht g.mem_V
  rw [g.V_eq] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with e | e | e | e
  · exfalso
    apply g.ne_one
    have := congrArg (fun w => t⁻¹ * w * t) e
    simpa [mul_assoc] using this
  · exfalso
    apply g.ne_z
    have h1 : g.a = t⁻¹ * (t * g.a * t⁻¹) * t := by group
    rw [h1, e]
    have h2 := h.T_conj_z (Subgroup.inv_mem _ ht)
    simpa using h2
  · exact Or.inl e
  · exact Or.inr e

theorem T_conj_a₂ {t : D} (ht : t ∈ A ⊓ B) :
    (t * g.a₂ * t⁻¹ = g.a₂ ∨ t * g.a₂ * t⁻¹ = z * g.a₂) ∨
      (t * g.a₂ * t⁻¹ = g.a₃ ∨ t * g.a₂ * t⁻¹ = z * g.a₃) := by
  have htx : t * g.x ∈ B := B.mul_mem ht.2 g.mem_B
  have hz₁ : g.x * z * g.x⁻¹ = z := h.central g.x g.mem_B
  have hz₂ : g.x * g.x * z * (g.x * g.x)⁻¹ = z :=
    h.central (g.x * g.x) (B.mul_mem g.mem_B g.mem_B)
  rcases coset_decomp h.gold.relIndex_right g.mem_B g.not_mem_T g.sq_not_mem_T htx with
    hT | ⟨t', ht', e⟩ | ⟨t', ht', e⟩
  · exfalso
    apply g.not_mem_T
    have : g.x = t⁻¹ * (t * g.x) := by group
    rw [this]
    exact (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht) hT
  · have e1 : t * g.a₂ * t⁻¹ = g.x * (t' * g.a * t'⁻¹) * g.x⁻¹ := by
      calc t * g.a₂ * t⁻¹ = (t * g.x) * g.a * (t * g.x)⁻¹ := by unfold Gens.a₂; group
        _ = (g.x * t') * g.a * (g.x * t')⁻¹ := by rw [e]
        _ = g.x * (t' * g.a * t'⁻¹) * g.x⁻¹ := by group
    rcases g.T_conj_a h ht' with e2 | e2
    · exact Or.inl (Or.inl (by rw [e1, e2]; rfl))
    · refine Or.inl (Or.inr ?_)
      rw [e1, e2]
      calc g.x * (z * g.a) * g.x⁻¹ = (g.x * z * g.x⁻¹) * (g.x * g.a * g.x⁻¹) := by group
        _ = z * g.a₂ := by rw [hz₁]; rfl
  · have e1 : t * g.a₂ * t⁻¹ = g.x * g.x * (t' * g.a * t'⁻¹) * (g.x * g.x)⁻¹ := by
      calc t * g.a₂ * t⁻¹ = (t * g.x) * g.a * (t * g.x)⁻¹ := by unfold Gens.a₂; group
        _ = (g.x * g.x * t') * g.a * (g.x * g.x * t')⁻¹ := by rw [e]
        _ = g.x * g.x * (t' * g.a * t'⁻¹) * (g.x * g.x)⁻¹ := by group
    rcases g.T_conj_a h ht' with e2 | e2
    · exact Or.inr (Or.inl (by rw [e1, e2]; rfl))
    · refine Or.inr (Or.inr ?_)
      rw [e1, e2]
      calc g.x * g.x * (z * g.a) * (g.x * g.x)⁻¹ =
          (g.x * g.x * z * (g.x * g.x)⁻¹) * (g.x * g.x * g.a * (g.x * g.x)⁻¹) := by group
        _ = z * g.a₃ := by rw [hz₂]; rfl

theorem T_conj_a₃ {t : D} (ht : t ∈ A ⊓ B) :
    (t * g.a₃ * t⁻¹ = g.a₂ ∨ t * g.a₃ * t⁻¹ = z * g.a₂) ∨
      (t * g.a₃ * t⁻¹ = g.a₃ ∨ t * g.a₃ * t⁻¹ = z * g.a₃) := by
  have hxx : g.x * g.x ∈ B := B.mul_mem g.mem_B g.mem_B
  have htx : t * (g.x * g.x) ∈ B := B.mul_mem ht.2 hxx
  have hz₁ : g.x * z * g.x⁻¹ = z := h.central g.x g.mem_B
  have hz₂ : g.x * g.x * z * (g.x * g.x)⁻¹ = z := h.central (g.x * g.x) hxx
  rcases coset_decomp h.gold.relIndex_right g.mem_B g.not_mem_T g.sq_not_mem_T htx with
    hT | ⟨t', ht', e⟩ | ⟨t', ht', e⟩
  · exfalso
    apply g.sq_not_mem_T
    have : g.x * g.x = t⁻¹ * (t * (g.x * g.x)) := by group
    rw [this]
    exact (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht) hT
  · have e1 : t * g.a₃ * t⁻¹ = g.x * (t' * g.a * t'⁻¹) * g.x⁻¹ := by
      calc t * g.a₃ * t⁻¹ = (t * (g.x * g.x)) * g.a * (t * (g.x * g.x))⁻¹ := by
            unfold Gens.a₃; group
        _ = (g.x * t') * g.a * (g.x * t')⁻¹ := by rw [e]
        _ = g.x * (t' * g.a * t'⁻¹) * g.x⁻¹ := by group
    rcases g.T_conj_a h ht' with e2 | e2
    · exact Or.inl (Or.inl (by rw [e1, e2]; rfl))
    · refine Or.inl (Or.inr ?_)
      rw [e1, e2]
      calc g.x * (z * g.a) * g.x⁻¹ = (g.x * z * g.x⁻¹) * (g.x * g.a * g.x⁻¹) := by group
        _ = z * g.a₂ := by rw [hz₁]; rfl
  · have e1 : t * g.a₃ * t⁻¹ = g.x * g.x * (t' * g.a * t'⁻¹) * (g.x * g.x)⁻¹ := by
      calc t * g.a₃ * t⁻¹ = (t * (g.x * g.x)) * g.a * (t * (g.x * g.x))⁻¹ := by
            unfold Gens.a₃; group
        _ = (g.x * g.x * t') * g.a * (g.x * g.x * t')⁻¹ := by rw [e]
        _ = g.x * g.x * (t' * g.a * t'⁻¹) * (g.x * g.x)⁻¹ := by group
    rcases g.T_conj_a h ht' with e2 | e2
    · exact Or.inr (Or.inl (by rw [e1, e2]; rfl))
    · refine Or.inr (Or.inr ?_)
      rw [e1, e2]
      calc g.x * g.x * (z * g.a) * (g.x * g.x)⁻¹ =
          (g.x * g.x * z * (g.x * g.x)⁻¹) * (g.x * g.x * g.a * (g.x * g.x)⁻¹) := by group
        _ = z * g.a₃ := by rw [hz₂]; rfl

theorem T_fix_or_swap (hU : Nat.card (conjClosure V B) = 16) {t : D} (ht : t ∈ A ⊓ B) :
    ((t * g.a₂ * t⁻¹ = g.a₂ ∨ t * g.a₂ * t⁻¹ = z * g.a₂) ∧
        (t * g.a₃ * t⁻¹ = g.a₃ ∨ t * g.a₃ * t⁻¹ = z * g.a₃)) ∨
      ((t * g.a₂ * t⁻¹ = g.a₃ ∨ t * g.a₂ * t⁻¹ = z * g.a₃) ∧
        (t * g.a₃ * t⁻¹ = g.a₂ ∨ t * g.a₃ * t⁻¹ = z * g.a₂)) := by
  have hprod : t * g.a₂ * t⁻¹ * (t * g.a₃ * t⁻¹) = t * (g.a₂ * g.a₃) * t⁻¹ := by group
  rcases g.T_conj_a₂ h ht with hp | hp <;> rcases g.T_conj_a₃ h ht with hq | hq
  · exfalso
    have := h.line_mul_mem (g.a₂_mem_U) hp hq
    rw [hprod] at this
    exact g.a₂_mul_a₃_not_mem_V h hU (h.mem_V_of_conj_mem_V ht this)
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exfalso
    have := h.line_mul_mem (g.a₃_mem_U) hp hq
    rw [hprod] at this
    exact g.a₂_mul_a₃_not_mem_V h hU (h.mem_V_of_conj_mem_V ht this)

theorem T_conj_mul (hU : Nat.card (conjClosure V B) = 16) {t : D} (ht : t ∈ A ⊓ B) :
    t * (g.a₂ * g.a₃) * t⁻¹ = g.a₂ * g.a₃ ∨ t * (g.a₂ * g.a₃) * t⁻¹ = z * (g.a₂ * g.a₃) := by
  have hprod : t * g.a₂ * t⁻¹ * (t * g.a₃ * t⁻¹) = t * (g.a₂ * g.a₃) * t⁻¹ := by group
  rw [← hprod]
  rcases g.T_fix_or_swap h hU ht with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact h.line_mul_eq (g.a₂_mem_U) hp hq
  · have := h.line_mul_eq (g.a₃_mem_U) hp hq
    rwa [h.U_comm (g.a₃_mem_U) (g.a₂_mem_U)] at this

theorem mem_pCoreOf_of_fix {t : D} (ht : t ∈ A ⊓ B)
    (h2 : t * g.a₂ * t⁻¹ = g.a₂ ∨ t * g.a₂ * t⁻¹ = z * g.a₂)
    (h3 : t * g.a₃ * t⁻¹ = g.a₃ ∨ t * g.a₃ * t⁻¹ = z * g.a₃) : t ∈ pCoreOf 2 B := by
  rw [h.pCoreOf_eq_centralizerMod]
  refine ⟨ht.2, mem_normalizer_zpowers_of_mul_comm (h.T_comm_z ht), ?_⟩
  have hzmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  have hgen : conjClosure V B ≤ Subgroup.closure ({z, g.a, g.a₂, g.a₃} : Set D) := by
    refine (g.conjClosure_le_sup h).trans ?_
    refine sup_le (sup_le ?_ ?_) ?_
    · intro v hv
      have hv' : v ∈ (V : Set D) := hv
      rw [g.V_eq] at hv'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
      rcases hv' with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have key : ∀ w ∈ Subgroup.closure ({z, g.a, g.a₂, g.a₃} : Set D),
      w ∈ conjClosure V B ∧ t * w * t⁻¹ * w⁻¹ ∈ Subgroup.zpowers z := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · refine ⟨h.z_mem_U, ?_⟩
        rw [h.T_conj_z ht]
        simp
      · refine ⟨g.a_mem_U, ?_⟩
        rcases g.T_conj_a h ht with e | e
        · rw [e]; simp
        · rw [e]
          have : z * g.a * g.a⁻¹ = z := by group
          rw [this]; exact hzmem
      · refine ⟨g.a₂_mem_U, ?_⟩
        rcases h2 with e | e
        · rw [e]; simp
        · rw [e]
          have : z * g.a₂ * g.a₂⁻¹ = z := by group
          rw [this]; exact hzmem
      · refine ⟨g.a₃_mem_U, ?_⟩
        rcases h3 with e | e
        · rw [e]; simp
        · rw [e]
          have : z * g.a₃ * g.a₃⁻¹ = z := by group
          rw [this]; exact hzmem
    | one => exact ⟨one_mem _, by simp⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxU, hx⟩ := ihx
      obtain ⟨hyU, hy⟩ := ihy
      refine ⟨Subgroup.mul_mem _ hxU hyU, ?_⟩
      have e : t * (x * y) * t⁻¹ * (x * y)⁻¹ =
          (t * x * t⁻¹ * x⁻¹) * (x * (t * y * t⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e, h.U_conj_of_mem_zpowers hxU hy]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ ih =>
      obtain ⟨hxU, hx⟩ := ih
      refine ⟨Subgroup.inv_mem _ hxU, ?_⟩
      have e : t * x⁻¹ * t⁻¹ * x⁻¹⁻¹ = x⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * x := by group
      rw [e, h.U_inv_conj_of_mem_zpowers hxU (Subgroup.inv_mem _ hx)]
      exact Subgroup.inv_mem _ hx
  intro u hu
  exact (key u (hgen hu)).2

end Gens

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem V_le_core : V ≤ coreIn (conjClosure V B) A := by
  intro v hv
  refine ⟨pCoreOf_le 2 A (h.natural.le_pCoreOf hv), fun a ha => ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 (A.inv_mem ha)) v).mp hv
  have : a⁻¹ * v * a ∈ V := by simpa using this
  exact le_conjClosure V B this

end GoldHyp3

omit [Finite D] in
theorem mul_inv_mem_of_relIndex_two {H K : Subgroup D} (hHK : H.relIndex K = 2) {x y : D}
    (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : x * y⁻¹ ∈ H := by
  obtain ⟨a₀, -, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp hHK
  have h1 : x * a₀ ∈ H := by
    rcases hxor x hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hxH
  have h2 : y * a₀ ∈ H := by
    rcases hxor y hy with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hyH
  have := H.mul_mem h1 (H.inv_mem h2)
  have e : x * a₀ * (y * a₀)⁻¹ = x * y⁻¹ := by group
  rwa [e] at this

namespace Gens

theorem T_conj_a_of_not_mem (g : Gens A B z V) (h : GoldHyp3 A B z V) {τ : D} (hτ : τ ∈ A ⊓ B)
    (hτQ : τ ∉ pCoreOf 2 A) : τ * g.a * τ⁻¹ = z * g.a := by
  rcases g.T_conj_a h hτ with e | e
  · exfalso
    apply hτQ
    rw [← inf_inf_centralizer_eq_pCoreOf h.natural]
    refine ⟨hτ, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : v ∈ (V : Set D) := hv
    rw [g.V_eq] at hv'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
    have hτa : τ * g.a = g.a * τ := by
      calc τ * g.a = (τ * g.a * τ⁻¹) * τ := by group
        _ = g.a * τ := by rw [e]
    have hτz : τ * z = z * τ := h.T_comm_z hτ
    rcases hv' with rfl | rfl | rfl | rfl
    · simp
    · exact hτz.symm
    · exact hτa.symm
    · calc z * g.a * τ = z * (g.a * τ) := by group
        _ = z * (τ * g.a) := by rw [hτa]
        _ = (z * τ) * g.a := by group
        _ = (τ * z) * g.a := by rw [hτz]
        _ = τ * (z * g.a) := by group
  · exact e

end Gens

namespace Gens

theorem T_conj_c₂₃ (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) {t : D} (ht : t ∈ A ⊓ B) :
    t * g.c₂₃ * t⁻¹ = g.c₂₃ ∨ t * g.c₂₃ * t⁻¹ = z * g.c₂₃ :=
  g.T_conj_mul h hU ht

end Gens

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem z_mul_z : z * z = 1 := by
  have := h.natural.z_sq
  rwa [pow_two] at this

omit [Finite D] in
theorem z_mul_mul_z_mul {x y : D} (hx : x ∈ conjClosure V B) : z * x * (z * y) = x * y := by
  have hzx : x * z = z * x := h.U_comm hx h.z_mem_U
  calc z * x * (z * y) = z * (x * z) * y := by group
    _ = z * (z * x) * y := by rw [hzx]
    _ = (z * z) * x * y := by group
    _ = x * y := by rw [h.z_mul_z, one_mul]

end GoldHyp3

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_T_not_mem_QA : ∃ τ ∈ A ⊓ B, τ ∉ pCoreOf 2 A := by
  by_contra hcon
  push Not at hcon
  have hle : A ⊓ B ≤ pCoreOf 2 A := fun t ht => hcon t ht
  have h1 : (pCoreOf 2 A).relIndex (A ⊓ B) = 1 := Subgroup.relIndex_eq_one.mpr hle
  have h2 := h.gold.relIndex_pCoreOf_T_left
  omega

end GoldHyp3

namespace Gens

variable (g : Gens A B z V)

omit [Finite D] in
theorem x_conj_a : g.x * g.a * g.x⁻¹ = g.a₂ := rfl

omit [Finite D] in
theorem x_conj_a₂ : g.x * g.a₂ * g.x⁻¹ = g.a₃ := by
  unfold Gens.a₂ Gens.a₃; group

omit [Finite D] in
theorem x_conj_a₃ : g.x * g.a₃ * g.x⁻¹ = g.a := by
  unfold Gens.a₃
  calc g.x * (g.x * g.x * g.a * (g.x * g.x)⁻¹) * g.x⁻¹
      = (g.x * g.x * g.x) * g.a * (g.x * g.x * g.x)⁻¹ := by group
    _ = g.a := by rw [g.cube]; group

theorem B_fixed_of {ω : D} (h : GoldHyp3 A B z V) (hωT : ∀ t ∈ A ⊓ B, t * ω * t⁻¹ = ω)
    (hωx : g.x * ω * g.x⁻¹ = ω) : ∀ b ∈ B, b * ω * b⁻¹ = ω := by
  intro b hb
  rcases coset_decomp h.gold.relIndex_right g.mem_B g.not_mem_T g.sq_not_mem_T hb with
    hT | ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
  · exact hωT b hT
  · calc g.x * t * ω * (g.x * t)⁻¹ = g.x * (t * ω * t⁻¹) * g.x⁻¹ := by group
      _ = ω := by rw [hωT t htT, hωx]
  · calc g.x * g.x * t * ω * (g.x * g.x * t)⁻¹
        = g.x * (g.x * (t * ω * t⁻¹) * g.x⁻¹) * g.x⁻¹ := by group
      _ = ω := by rw [hωT t htT, hωx, hωx]

omit [Finite D] in
theorem x_conj_c₂₃_mul_a (h : GoldHyp3 A B z V) :
    g.x * (g.c₂₃ * g.a) * g.x⁻¹ = g.c₂₃ * g.a := by
  have hc1 : g.a * g.a₂ = g.a₂ * g.a := h.U_comm (g.a_mem_U) (g.a₂_mem_U)
  have hc2 : g.a₃ * g.a₂ = g.a₂ * g.a₃ := h.U_comm (g.a₃_mem_U) (g.a₂_mem_U)
  calc g.x * (g.c₂₃ * g.a) * g.x⁻¹
      = (g.x * g.a₂ * g.x⁻¹) * (g.x * g.a₃ * g.x⁻¹) * (g.x * g.a * g.x⁻¹) := by
        unfold Gens.c₂₃; group
    _ = g.a₃ * g.a * g.a₂ := by rw [g.x_conj_a₂, g.x_conj_a₃, g.x_conj_a]
    _ = g.a₃ * (g.a * g.a₂) := by group
    _ = g.a₃ * (g.a₂ * g.a) := by rw [hc1]
    _ = (g.a₃ * g.a₂) * g.a := by group
    _ = (g.a₂ * g.a₃) * g.a := by rw [hc2]

omit [Finite D] in
theorem x_conj_c₂₃ : g.x * g.c₂₃ * g.x⁻¹ = g.a₃ * g.a := by
  calc g.x * g.c₂₃ * g.x⁻¹ = (g.x * g.a₂ * g.x⁻¹) * (g.x * g.a₃ * g.x⁻¹) := by
        unfold Gens.c₂₃; group
    _ = g.a₃ * g.a := by rw [g.x_conj_a₂, g.x_conj_a₃]

end Gens

namespace Gens

variable (g : Gens A B z V)

omit [Finite D] in
theorem x_conj_a₃_mul_a : g.x * (g.a₃ * g.a) * g.x⁻¹ = g.a * g.a₂ := by
  calc g.x * (g.a₃ * g.a) * g.x⁻¹ = (g.x * g.a₃ * g.x⁻¹) * (g.x * g.a * g.x⁻¹) := by group
    _ = g.a * g.a₂ := by rw [g.x_conj_a₃, g.x_conj_a]

omit [Finite D] in
theorem c₁_mul_c₂ (h : GoldHyp3 A B z V) : (g.a₃ * g.a) * (g.a * g.a₂) = g.c₂₃ := by
  have haa : g.a * g.a = 1 := h.U_sq (g.a_mem_U)
  have hc : g.a₃ * g.a₂ = g.a₂ * g.a₃ := h.U_comm (g.a₃_mem_U) (g.a₂_mem_U)
  calc (g.a₃ * g.a) * (g.a * g.a₂) = g.a₃ * (g.a * g.a) * g.a₂ := by group
    _ = g.a₃ * g.a₂ := by rw [haa]; group
    _ = g.c₂₃ := by rw [hc]; rfl

omit [Finite D] in
theorem c₂_mul_c₁ (h : GoldHyp3 A B z V) : (g.a * g.a₂) * (g.a₃ * g.a) = g.c₂₃ := by
  have haa : g.a * g.a = 1 := h.U_sq (g.a_mem_U)
  have hc : g.a * g.c₂₃ = g.c₂₃ * g.a := h.U_comm (g.a_mem_U) (g.c₂₃_mem_U)
  calc (g.a * g.a₂) * (g.a₃ * g.a) = g.a * g.c₂₃ * g.a := by unfold Gens.c₂₃; group
    _ = g.c₂₃ * g.a * g.a := by rw [hc]
    _ = g.c₂₃ * (g.a * g.a) := by group
    _ = g.c₂₃ := by rw [haa, mul_one]

end Gens

end GoldAmL3

end F6

end CFSG.Quasithin
