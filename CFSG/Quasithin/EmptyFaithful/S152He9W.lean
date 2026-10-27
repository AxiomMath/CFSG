module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.He9

open Equiv

abbrev S5 : Type := Equiv.Perm (Fin 5)

abbrev Q2 : Type := Multiplicative (ZMod 2)

abbrev W5 : Type := S5 ≀ᵣ Q2

@[expose] def g2 : Q2 := Multiplicative.ofAdd 1

theorem g2_ne_one : g2 ≠ 1 := by decide

theorem g2_mul_g2 : g2 * g2 = 1 := by decide

theorem Q2_cases (q : Q2) : q = 1 ∨ q = g2 := by
  revert q
  decide

theorem Q2_inv (q : Q2) : q⁻¹ = q := by
  rcases Q2_cases q with rfl | rfl
  · simp
  · exact inv_eq_of_mul_eq_one_right g2_mul_g2

theorem Q2_mul_self (q : Q2) : q * q = 1 := by
  rcases Q2_cases q with rfl | rfl
  · simp
  · exact g2_mul_g2

theorem Q2_one_mul_g2 : (1 : Q2) * g2 = g2 := one_mul _

theorem g2_mul_g2' : g2 * g2 = 1 := g2_mul_g2

namespace W5

theorem ext' {w w' : W5} (h1 : w.left 1 = w'.left 1) (h2 : w.left g2 = w'.left g2)
    (h3 : w.right = w'.right) : w = w' := by
  refine RegularWreathProduct.ext ?_ h3
  funext x
  rcases Q2_cases x with rfl | rfl <;> assumption

theorem mul_l1 (a b : W5) : (a * b).left 1 = a.left 1 * b.left a.right := by
  simp [RegularWreathProduct.mul_left, Q2_inv]

theorem mul_lg (a b : W5) : (a * b).left g2 = a.left g2 * b.left (a.right * g2) := by
  simp [RegularWreathProduct.mul_left, Q2_inv]

theorem mul_r (a b : W5) : (a * b).right = a.right * b.right := rfl

theorem inv_l1 (a : W5) : (a⁻¹).left 1 = (a.left a.right)⁻¹ := by
  simp [RegularWreathProduct.inv_left]

theorem inv_lg (a : W5) : (a⁻¹).left g2 = (a.left (a.right * g2))⁻¹ := by
  simp [RegularWreathProduct.inv_left]

theorem inv_r (a : W5) : (a⁻¹).right = a.right⁻¹ := rfl

@[expose] def mk (a b : S5) (q : Q2) : W5 := ⟨fun x => if x = 1 then a else b, q⟩

@[simp] theorem mk_l1 (a b : S5) (q : Q2) : (mk a b q).left 1 = a := by simp [mk]

@[simp] theorem mk_lg (a b : S5) (q : Q2) : (mk a b q).left g2 = b := by
  simp [mk, g2_ne_one]

@[simp] theorem mk_r (a b : S5) (q : Q2) : (mk a b q).right = q := rfl

theorem eta (w : W5) : w = mk (w.left 1) (w.left g2) w.right := by
  apply ext' <;> simp

@[expose] def incl1 : S5 →* W5 where
  toFun σ := mk σ 1 1
  map_one' := by
    apply ext' <;> simp [mk_l1, mk_lg]
  map_mul' σ τ := by
    apply ext' <;> simp [mul_l1, mul_lg, mk_l1, mk_lg]

@[expose] def incl2 : S5 →* W5 where
  toFun σ := mk 1 σ 1
  map_one' := by
    apply ext' <;> simp [mk_l1, mk_lg]
  map_mul' σ τ := by
    apply ext' <;> simp [mul_l1, mul_lg, mk_l1, mk_lg]

theorem incl1_apply (σ : S5) : incl1 σ = mk σ 1 1 := rfl

theorem incl2_apply (σ : S5) : incl2 σ = mk 1 σ 1 := rfl

@[expose] def tau : W5 := mk 1 1 g2

theorem tau_mul_tau : tau * tau = 1 := by
  apply ext' <;> simp [tau, mul_l1, mul_lg, g2_mul_g2]

theorem tau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_mul_tau

theorem mk_one_eq (a b : S5) : mk a b 1 = incl1 a * incl2 b := by
  apply ext' <;> simp [mul_l1, mul_lg, mk_l1, mk_lg, incl1_apply, incl2_apply]

theorem incl1_mul_incl2_comm (a b : S5) : incl1 a * incl2 b = incl2 b * incl1 a := by
  apply ext' <;> simp [mul_l1, mul_lg, incl1_apply, incl2_apply]

theorem incl1_injective : Function.Injective incl1 := by
  intro a b h
  have := congrArg (fun w : W5 => w.left 1) h
  simpa [incl1_apply] using this

theorem incl2_injective : Function.Injective incl2 := by
  intro a b h
  have := congrArg (fun w : W5 => w.left g2) h
  simpa [incl2_apply] using this

@[expose] def base : Subgroup W5 := (RegularWreathProduct.rightHom : W5 →* Q2).ker

theorem mem_base {w : W5} : w ∈ base ↔ w.right = 1 := Iff.rfl

theorem eq_mk_of_mem_base {w : W5} (hw : w ∈ base) : w = incl1 (w.left 1) * incl2 (w.left g2) := by
  have hr : w.right = 1 := hw
  rw [← mk_one_eq]
  apply ext' <;> simp [hr]

theorem incl1_mem_base (a : S5) : incl1 a ∈ base := mem_base.2 (by simp [incl1_apply])

theorem incl2_mem_base (a : S5) : incl2 a ∈ base := mem_base.2 (by simp [incl2_apply])

theorem conj_incl1_of_base {p : W5} (hp : p ∈ base) (σ : S5) :
    p * incl1 σ * p⁻¹ = incl1 (p.left 1 * σ * (p.left 1)⁻¹) := by
  have hr : p.right = 1 := hp
  apply ext' <;> simp [mul_l1, mul_lg, inv_l1, inv_lg, hr, incl1_apply]

theorem conj_incl2_of_base {p : W5} (hp : p ∈ base) (σ : S5) :
    p * incl2 σ * p⁻¹ = incl2 (p.left g2 * σ * (p.left g2)⁻¹) := by
  have hr : p.right = 1 := hp
  apply ext' <;> simp [mul_l1, mul_lg, inv_l1, inv_lg, hr, incl2_apply]

theorem conj_incl1_of_not_base {p : W5} (hp : p.right = g2) (σ : S5) :
    p * incl1 σ * p⁻¹ = incl2 (p.left g2 * σ * (p.left g2)⁻¹) := by
  apply ext' <;> simp [mul_l1, mul_lg, inv_l1, inv_lg, hp, incl1_apply, incl2_apply,
    g2_mul_g2, Q2_inv]

theorem conj_incl2_of_not_base {p : W5} (hp : p.right = g2) (σ : S5) :
    p * incl2 σ * p⁻¹ = incl1 (p.left 1 * σ * (p.left 1)⁻¹) := by
  apply ext' <;> simp [mul_l1, mul_lg, inv_l1, inv_lg, hp, incl1_apply, incl2_apply,
    g2_mul_g2, Q2_inv]

theorem tau_conj_incl1 (σ : S5) : tau * incl1 σ * tau⁻¹ = incl2 σ := by
  rw [conj_incl1_of_not_base (p := tau) rfl]
  simp [tau]

theorem tau_conj_incl2 (σ : S5) : tau * incl2 σ * tau⁻¹ = incl1 σ := by
  rw [conj_incl2_of_not_base (p := tau) rfl]
  simp [tau]

@[expose] def c3 : S5 := Equiv.swap 0 1 * Equiv.swap 1 2

theorem c3_even : Equiv.Perm.sign c3 = 1 := by
  simp [c3, Equiv.Perm.sign_mul]

theorem c3_cube : c3 ^ 3 = 1 := by decide +kernel

theorem c3_ne_one : c3 ≠ 1 := by decide +kernel

theorem c3_four : c3 4 = 4 := by decide +kernel

theorem centralizer_A5 : ∀ σ : S5, (∀ a : S5, Equiv.Perm.sign a = 1 → σ * a = a * σ) → σ = 1 := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1000 in
theorem involution_fixed_unique : ∀ σ : S5, Equiv.Perm.sign σ = 1 → σ * σ = 1 → σ ≠ 1 → σ 4 = 4 →
    ∀ x : Fin 5, σ x = x → x = 4 := by
  decide +kernel

theorem A5_nonabelian : ∃ a b : S5, Equiv.Perm.sign a = 1 ∧ Equiv.Perm.sign b = 1 ∧
    a * b ≠ b * a := by
  decide +kernel

theorem card_stab4 : Fintype.card {σ : S5 // σ 4 = 4} = 24 := by decide +kernel

abbrev A5 : Subgroup S5 := alternatingGroup (Fin 5)

theorem mem_A5 {σ : S5} : σ ∈ A5 ↔ Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup

instance A5_simple : IsSimpleGroup ↥A5 := alternatingGroup.isSimpleGroup (by simp)

@[expose] def A1 : Subgroup W5 := (A5).map incl1

@[expose] def A2 : Subgroup W5 := (A5).map incl2

theorem mem_A1 {w : W5} :
    w ∈ A1 ↔ w.right = 1 ∧ w.left g2 = 1 ∧ w.left 1 ∈ A5 := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨by simp [incl1_apply], by simp [incl1_apply], by simpa [incl1_apply] using hσ⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨w.left 1, h3, ?_⟩
    apply ext' <;> simp [incl1_apply, h1, h2]

theorem mem_A2 {w : W5} :
    w ∈ A2 ↔ w.right = 1 ∧ w.left 1 = 1 ∧ w.left g2 ∈ A5 := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨by simp [incl2_apply], by simp [incl2_apply], by simpa [incl2_apply] using hσ⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨w.left g2, h3, ?_⟩
    apply ext' <;> simp [incl2_apply, h1, h2]

theorem A1_le_base : A1 ≤ base := fun _ hw => mem_base.2 (mem_A1.1 hw).1

theorem A2_le_base : A2 ≤ base := fun _ hw => mem_base.2 (mem_A2.1 hw).1

theorem A1_inf_A2 : A1 ⊓ A2 = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨h1, h2⟩
  obtain ⟨r1, l1, l2⟩ := mem_A1.1 h1
  obtain ⟨-, m1, -⟩ := mem_A2.1 h2
  rw [Subgroup.mem_bot]
  apply ext' <;> simp [r1, l1, m1]

theorem A1_comm {a b : W5} (ha : a ∈ A1) (hb : b ∈ A2) : a * b = b * a := by
  obtain ⟨r1, l1, -⟩ := mem_A1.1 ha
  obtain ⟨r2, m1, -⟩ := mem_A2.1 hb
  apply ext' <;> simp [mul_l1, mul_lg, r1, r2, l1, m1]

theorem tau_conj_A1 {x : W5} (hx : x ∈ A1) : tau * x * tau⁻¹ ∈ A2 := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  rw [tau_conj_incl1]
  exact ⟨σ, hσ, rfl⟩

theorem tau_conj_A2 {x : W5} (hx : x ∈ A2) : tau * x * tau⁻¹ ∈ A1 := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  rw [tau_conj_incl2]
  exact ⟨σ, hσ, rfl⟩

noncomputable def A1equiv : ↥(A5) ≃* ↥A1 :=
  Subgroup.equivMapOfInjective _ incl1 incl1_injective

noncomputable def A2equiv : ↥(A5) ≃* ↥A2 :=
  Subgroup.equivMapOfInjective _ incl2 incl2_injective

theorem A1_simple : IsSimpleGroup ↥A1 := by
  exact A1equiv.symm.isSimpleGroup

theorem A2_simple : IsSimpleGroup ↥A2 := by
  exact A2equiv.symm.isSimpleGroup

theorem A1_ne_bot : A1 ≠ ⊥ := by
  intro h
  have : incl1 c3 ∈ A1 := ⟨c3, (mem_A5).2 c3_even, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact c3_ne_one (incl1_injective (this.trans incl1.map_one.symm))

theorem A2_ne_bot : A2 ≠ ⊥ := by
  intro h
  have : incl2 c3 ∈ A2 := ⟨c3, (mem_A5).2 c3_even, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact c3_ne_one (incl2_injective (this.trans incl2.map_one.symm))

theorem key_conj_A1 {q : W5} (hq : q ∈ base) {x : W5} (hx : x ∈ A1) : q * x * q⁻¹ ∈ A1 := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  rw [conj_incl1_of_base hq]
  exact ⟨_, Subgroup.Normal.conj_mem inferInstance σ hσ (q.left 1), rfl⟩

theorem normalizer_A1 : Subgroup.normalizer (A1 : Set W5) = base := by
  apply le_antisymm
  · intro p hp
    by_contra hpb
    have hr : p.right = g2 := by
      rcases Q2_cases p.right with h | h
      · exact absurd (mem_base.2 h) hpb
      · exact h
    have hx : incl1 c3 ∈ A1 := ⟨c3, mem_A5.2 c3_even, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 hp (incl1 c3)).1 hx
    rw [conj_incl1_of_not_base hr] at h1
    have h2 := (mem_A1.1 h1).2.1
    simp only [incl2_apply, mk_lg] at h2
    apply c3_ne_one
    have h3 := congrArg (fun y => (p.left g2)⁻¹ * y * p.left g2) h2
    simpa [mul_assoc] using h3
  · intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key_conj_A1 hp hx, fun hx => ?_⟩
    have h := key_conj_A1 (inv_mem hp : p⁻¹ ∈ base) hx
    have e : p⁻¹ * (p * x * p⁻¹) * p⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem key_conj_A2 {q : W5} (hq : q ∈ base) {x : W5} (hx : x ∈ A2) : q * x * q⁻¹ ∈ A2 := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  rw [conj_incl2_of_base hq]
  exact ⟨_, Subgroup.Normal.conj_mem inferInstance σ hσ (q.left g2), rfl⟩

theorem normalizer_A2 : Subgroup.normalizer (A2 : Set W5) = base := by
  apply le_antisymm
  · intro p hp
    by_contra hpb
    have hr : p.right = g2 := by
      rcases Q2_cases p.right with h | h
      · exact absurd (mem_base.2 h) hpb
      · exact h
    have hx : incl2 c3 ∈ A2 := ⟨c3, mem_A5.2 c3_even, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 hp (incl2 c3)).1 hx
    rw [conj_incl2_of_not_base hr] at h1
    have h2 := (mem_A2.1 h1).2.1
    simp only [incl1_apply, mk_l1] at h2
    apply c3_ne_one
    have h3 := congrArg (fun y => (p.left 1)⁻¹ * y * p.left 1) h2
    simpa [mul_assoc] using h3
  · intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key_conj_A2 hp hx, fun hx => ?_⟩
    have h := key_conj_A2 (inv_mem hp : p⁻¹ ∈ base) hx
    have e : p⁻¹ * (p * x * p⁻¹) * p⁻¹⁻¹ = x := by group
    rwa [e] at h

@[expose] def S0 : Subgroup W5 where
  carrier := {w | w.right = 1 ∧ w.left 1 ∈ A5 ∧ w.left g2 ∈ A5}
  one_mem' := ⟨rfl, one_mem _, one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨by simp [ha, hb], ?_, ?_⟩
    · rw [mul_l1, ha]
      exact mul_mem ha1 hb1
    · rw [mul_lg, ha]
      simpa using mul_mem ha2 hb2
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨by simp [ha], ?_, ?_⟩
    · rw [inv_l1, ha]
      exact inv_mem ha1
    · rw [inv_lg, ha]
      simpa using inv_mem ha2

theorem mem_S0 {w : W5} : w ∈ S0 ↔ w.right = 1 ∧ w.left 1 ∈ A5 ∧ w.left g2 ∈ A5 := Iff.rfl

theorem A1_le_S0 : A1 ≤ S0 := by
  intro w hw
  obtain ⟨r, l, h⟩ := mem_A1.1 hw
  exact ⟨r, h, by rw [l]; exact one_mem _⟩

theorem A2_le_S0 : A2 ≤ S0 := by
  intro w hw
  obtain ⟨r, l, h⟩ := mem_A2.1 hw
  exact ⟨r, by rw [l]; exact one_mem _, h⟩

theorem S0_le_base : S0 ≤ base := fun _ hw => mem_base.2 hw.1

theorem eq_incl_mul_of_mem_S0 {w : W5} (hw : w ∈ S0) :
    w = incl1 (w.left 1) * incl2 (w.left g2) := eq_mk_of_mem_base (S0_le_base hw)

theorem incl1_mem_A1 {σ : S5} (hσ : σ ∈ A5) : incl1 σ ∈ A1 := ⟨σ, hσ, rfl⟩

theorem incl2_mem_A2 {σ : S5} (hσ : σ ∈ A5) : incl2 σ ∈ A2 := ⟨σ, hσ, rfl⟩

theorem S0_eq_mul {w : W5} (hw : w ∈ S0) : ∃ a ∈ A1, ∃ b ∈ A2, w = a * b :=
  ⟨incl1 (w.left 1), incl1_mem_A1 hw.2.1, incl2 (w.left g2), incl2_mem_A2 hw.2.2,
    eq_incl_mul_of_mem_S0 hw⟩

theorem mul_mem_S0 {a b : W5} (ha : a ∈ A1) (hb : b ∈ A2) : a * b ∈ S0 :=
  mul_mem (A1_le_S0 ha) (A2_le_S0 hb)

theorem conj_mem_S0 (p : W5) {w : W5} (hw : w ∈ S0) : p * w * p⁻¹ ∈ S0 := by
  obtain ⟨σ, hσ, τ', hτ, rfl⟩ : ∃ σ ∈ A5, ∃ τ' ∈ A5, w = incl1 σ * incl2 τ' :=
    ⟨w.left 1, hw.2.1, w.left g2, hw.2.2, eq_incl_mul_of_mem_S0 hw⟩
  have e : p * (incl1 σ * incl2 τ') * p⁻¹ = (p * incl1 σ * p⁻¹) * (p * incl2 τ' * p⁻¹) := by
    group
  rw [e]
  rcases Q2_cases p.right with hr | hr
  · have hp : p ∈ base := mem_base.2 hr
    rw [conj_incl1_of_base hp, conj_incl2_of_base hp]
    exact mul_mem_S0 (incl1_mem_A1 (Subgroup.Normal.conj_mem inferInstance σ hσ _))
      (incl2_mem_A2 (Subgroup.Normal.conj_mem inferInstance τ' hτ _))
  · rw [conj_incl1_of_not_base hr, conj_incl2_of_not_base hr]
    exact mul_mem (A2_le_S0 (incl2_mem_A2 (Subgroup.Normal.conj_mem inferInstance σ hσ _)))
      (A1_le_S0 (incl1_mem_A1 (Subgroup.Normal.conj_mem inferInstance τ' hτ _)))

instance S0_normal : S0.Normal := ⟨fun _ hn g => conj_mem_S0 g hn⟩

theorem simple_inf_dichotomy {G : Type*} [Group G] {A N : Subgroup G} (hA : IsSimpleGroup ↥A)
    (hnorm : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) : N ⊓ A = ⊥ ∨ A ≤ N := by
  let H : Subgroup ↥A := (N ⊓ A).subgroupOf A
  have : H.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Subgroup.mem_inf.2 ⟨hnorm g g.2 n (Subgroup.mem_inf.1 hn).1,
      A.mul_mem (A.mul_mem g.2 (Subgroup.mem_inf.1 hn).2) (A.inv_mem g.2)⟩⟩
  rcases hA.eq_bot_or_eq_top_of_normal H with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, (Subgroup.mem_inf.1 hx).2⟩ : ↥A) ∈ H := hx
    rw [h, Subgroup.mem_bot] at hx'
    have := congrArg Subtype.val hx'
    simpa using this
  · right
    intro a ha
    have : (⟨a, ha⟩ : ↥A) ∈ H := by rw [h]; exact Subgroup.mem_top _
    exact this.1

theorem A1_conj_of_S0 {n a : W5} (hn : n ∈ S0) (ha : a ∈ A1) : n * a * n⁻¹ ∈ A1 :=
  key_conj_A1 (S0_le_base hn) ha

theorem A2_conj_of_S0 {n a : W5} (hn : n ∈ S0) (ha : a ∈ A2) : n * a * n⁻¹ ∈ A2 :=
  key_conj_A2 (S0_le_base hn) ha

theorem eq_one_of_centralizes {n : W5} (hn : n ∈ S0) (h1 : ∀ a ∈ A1, n * a = a * n)
    (h2 : ∀ b ∈ A2, n * b = b * n) : n = 1 := by
  have hr : n.right = 1 := hn.1
  have e1 : n.left 1 = 1 := by
    apply centralizer_A5
    intro a ha
    have := congrArg (fun w : W5 => w.left 1) (h1 (incl1 a) (incl1_mem_A1 (mem_A5.2 ha)))
    simpa [mul_l1, hr, incl1_apply] using this
  have e2 : n.left g2 = 1 := by
    apply centralizer_A5
    intro a ha
    have := congrArg (fun w : W5 => w.left g2) (h2 (incl2 a) (incl2_mem_A2 (mem_A5.2 ha)))
    simpa [mul_lg, hr, incl2_apply] using this
  apply ext' <;> simp [e1, e2, hr]

theorem normal_in_S0 {N : Subgroup W5} (hN : N ≤ S0)
    (hnorm : ∀ s ∈ S0, ∀ n ∈ N, s * n * s⁻¹ ∈ N) : N = ⊥ ∨ N = A1 ∨ N = A2 ∨ N = S0 := by
  have h1 := simple_inf_dichotomy A1_simple (fun a ha n hn => hnorm a (A1_le_S0 ha) n hn)
  have h2 := simple_inf_dichotomy A2_simple (fun a ha n hn => hnorm a (A2_le_S0 ha) n hn)
  have comm1 : N ⊓ A1 = ⊥ → ∀ n ∈ N, ∀ a ∈ A1, n * a = a * n := by
    intro h n hn a ha
    have hc : a * n * a⁻¹ * n⁻¹ ∈ N ⊓ A1 := by
      refine Subgroup.mem_inf.2 ⟨N.mul_mem (hnorm a (A1_le_S0 ha) n hn) (N.inv_mem hn), ?_⟩
      have : a * n * a⁻¹ * n⁻¹ = a * (n * a⁻¹ * n⁻¹) := by group
      rw [this]
      exact A1.mul_mem ha (by simpa using A1_conj_of_S0 (hN hn) (A1.inv_mem ha))
    rw [h, Subgroup.mem_bot] at hc
    calc n * a = (a * n * a⁻¹ * n⁻¹) * (n * a) := by rw [hc]; simp
      _ = a * n := by group
  have comm2 : N ⊓ A2 = ⊥ → ∀ n ∈ N, ∀ a ∈ A2, n * a = a * n := by
    intro h n hn a ha
    have hc : a * n * a⁻¹ * n⁻¹ ∈ N ⊓ A2 := by
      refine Subgroup.mem_inf.2 ⟨N.mul_mem (hnorm a (A2_le_S0 ha) n hn) (N.inv_mem hn), ?_⟩
      have : a * n * a⁻¹ * n⁻¹ = a * (n * a⁻¹ * n⁻¹) := by group
      rw [this]
      exact A2.mul_mem ha (by simpa using A2_conj_of_S0 (hN hn) (A2.inv_mem ha))
    rw [h, Subgroup.mem_bot] at hc
    calc n * a = (a * n * a⁻¹ * n⁻¹) * (n * a) := by rw [hc]; simp
      _ = a * n := by group
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    exact eq_one_of_centralizes (hN hn) (comm1 h1 n hn) (comm2 h2 n hn)
  · right; right; left
    apply le_antisymm
    · intro n hn
      obtain ⟨a, ha, b, hb, rfl⟩ := S0_eq_mul (hN hn)
      have hbN : b ∈ N := h2 hb
      have haN : a ∈ N := by simpa using mul_mem hn (inv_mem hbN)
      have : a = 1 := by
        have : a ∈ N ⊓ A1 := ⟨haN, ha⟩
        rw [h1, Subgroup.mem_bot] at this
        exact this
      simpa [this] using hb
    · exact h2
  · right; left
    apply le_antisymm
    · intro n hn
      obtain ⟨a, ha, b, hb, rfl⟩ := S0_eq_mul (hN hn)
      have haN : a ∈ N := h1 ha
      have hbN : b ∈ N := by simpa using mul_mem (inv_mem haN) hn
      have : b = 1 := by
        have : b ∈ N ⊓ A2 := ⟨hbN, hb⟩
        rw [h2, Subgroup.mem_bot] at this
        exact this
      simpa [this] using ha
    · exact h1
  · right; right; right
    apply le_antisymm hN
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := S0_eq_mul hw
    exact mul_mem (h1 ha) (h2 hb)

theorem centralizer_S0 {w : W5} (h : ∀ s ∈ S0, w * s = s * w) : w = 1 := by
  have hr : w.right = 1 := by
    rcases Q2_cases w.right with h' | h'
    · exact h'
    · exfalso
      have hx : incl1 c3 ∈ S0 := A1_le_S0 (incl1_mem_A1 (mem_A5.2 c3_even))
      have h1 := h (incl1 c3) hx
      have e : w * incl1 c3 * w⁻¹ = incl1 c3 := by rw [h1]; group
      rw [conj_incl1_of_not_base h'] at e
      have := congrArg (fun y : W5 => y.left 1) e
      simp [incl1_apply, incl2_apply] at this
      exact c3_ne_one this.symm
  have hb : w ∈ base := mem_base.2 hr
  have e1 : w.left 1 = 1 := by
    apply centralizer_A5
    intro a ha
    have hx : incl1 a ∈ S0 := A1_le_S0 (incl1_mem_A1 (mem_A5.2 ha))
    have h1 := h (incl1 a) hx
    have e : w * incl1 a * w⁻¹ = incl1 a := by rw [h1]; group
    rw [conj_incl1_of_base hb] at e
    have := incl1_injective e
    calc w.left 1 * a = (w.left 1 * a * (w.left 1)⁻¹) * w.left 1 := by group
      _ = a * w.left 1 := by rw [this]
  have e2 : w.left g2 = 1 := by
    apply centralizer_A5
    intro a ha
    have hx : incl2 a ∈ S0 := A2_le_S0 (incl2_mem_A2 (mem_A5.2 ha))
    have h1 := h (incl2 a) hx
    have e : w * incl2 a * w⁻¹ = incl2 a := by rw [h1]; group
    rw [conj_incl2_of_base hb] at e
    have := incl2_injective e
    calc w.left g2 * a = (w.left g2 * a * (w.left g2)⁻¹) * w.left g2 := by group
      _ = a * w.left g2 := by rw [this]
  apply ext' <;> simp [e1, e2, hr]

theorem S0_le_of_normal {N : Subgroup W5} [hN : N.Normal] (hne : N ≠ ⊥) : S0 ≤ N := by
  have hN' : N ⊓ S0 ≤ S0 := inf_le_right
  have hnorm : ∀ s ∈ S0, ∀ n ∈ N ⊓ S0, s * n * s⁻¹ ∈ N ⊓ S0 := fun s hs n hn =>
    ⟨hN.conj_mem n hn.1 s, conj_mem_S0 s hn.2⟩
  rcases normal_in_S0 hN' hnorm with h | h | h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply centralizer_S0
    intro s hs
    have hc : s * n * s⁻¹ * n⁻¹ ∈ N ⊓ S0 := by
      refine Subgroup.mem_inf.2 ⟨N.mul_mem (hN.conj_mem n hn s) (N.inv_mem hn), ?_⟩
      have : s * n * s⁻¹ * n⁻¹ = s * (n * s⁻¹ * n⁻¹) := by group
      rw [this]
      exact S0.mul_mem hs (by simpa using conj_mem_S0 n (S0.inv_mem hs))
    rw [h, Subgroup.mem_bot] at hc
    calc n * s = (s * n * s⁻¹ * n⁻¹) * (n * s) := by rw [hc]; simp
      _ = s * n := by group
  · exfalso
    have hA1N : A1 ≤ N := by rw [← h]; exact inf_le_left
    have hA2 : A2 ≤ N ⊓ S0 := by
      intro x hx
      refine Subgroup.mem_inf.2 ⟨?_, A2_le_S0 hx⟩
      have h1 : tau * x * tau⁻¹ ∈ N := hA1N (tau_conj_A2 hx)
      have h2 := hN.conj_mem _ h1 tau⁻¹
      have e : tau⁻¹ * (tau * x * tau⁻¹) * tau⁻¹⁻¹ = x := by group
      rwa [e] at h2
    rw [h] at hA2
    apply A2_ne_bot
    rw [eq_bot_iff, ← A1_inf_A2]
    exact le_inf hA2 le_rfl
  · exfalso
    have hA2N : A2 ≤ N := by rw [← h]; exact inf_le_left
    have hA1 : A1 ≤ N ⊓ S0 := by
      intro x hx
      refine Subgroup.mem_inf.2 ⟨?_, A1_le_S0 hx⟩
      have h1 : tau * x * tau⁻¹ ∈ N := hA2N (tau_conj_A1 hx)
      have h2 := hN.conj_mem _ h1 tau⁻¹
      have e : tau⁻¹ * (tau * x * tau⁻¹) * tau⁻¹⁻¹ = x := by group
      rwa [e] at h2
    rw [h] at hA1
    apply A1_ne_bot
    rw [eq_bot_iff, ← A1_inf_A2]
    exact le_inf le_rfl hA1
  · rw [← h]; exact inf_le_left

theorem card_S5 : Nat.card S5 = 120 := by
  rw [Nat.card_perm]
  simp [Nat.factorial]

theorem card_A5 : Nat.card ↥A5 = 60 := by
  have h : 2 * Nat.card ↥A5 = Nat.card S5 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [card_S5] at h
  omega

theorem card_Q2 : Nat.card Q2 = 2 := by
  rw [Nat.card_eq_fintype_card]
  simp

theorem card_W5 : Nat.card W5 = 28800 := by
  rw [RegularWreathProduct.card, card_S5, card_Q2]
  norm_num

theorem index_base : base.index = 2 := by
  have hr : (RegularWreathProduct.rightHom : W5 →* Q2).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro q
    exact ⟨RegularWreathProduct.inl q, by simp⟩
  unfold base
  rw [Subgroup.index_ker, hr, Subgroup.card_top, card_Q2]

theorem card_base : Nat.card ↥base = 14400 := by
  have h := base.card_mul_index
  rw [index_base, card_W5] at h
  omega

@[expose] def S0equiv : ↥S0 ≃ ↥A5 × ↥A5 where
  toFun w := (⟨w.1.left 1, w.2.2.1⟩, ⟨w.1.left g2, w.2.2.2⟩)
  invFun p := ⟨mk p.1 p.2 1, rfl, by simpa using p.1.2, by simpa using p.2.2⟩
  left_inv w := by
    apply Subtype.ext
    apply ext' <;> simp [w.2.1]
  right_inv p := by simp

theorem card_S0 : Nat.card ↥S0 = 3600 := by
  rw [Nat.card_congr S0equiv, Nat.card_prod, card_A5]

theorem index_S0 : S0.index = 8 := by
  have h := S0.card_mul_index
  rw [card_S0, card_W5] at h
  omega

theorem S0_sup_eq_top {P : Subgroup W5} (hP : ¬ 2 ∣ P.index) : S0 ⊔ P = ⊤ := by
  have h1 : (S0 ⊔ P).index ∣ 8 := index_S0 ▸ Subgroup.index_dvd_of_le le_sup_left
  have h2 : (S0 ⊔ P).index ∣ P.index := Subgroup.index_dvd_of_le le_sup_right
  have hcop : Nat.Coprime 8 P.index := by
    have : Nat.Coprime 2 P.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hP
    simpa using Nat.Coprime.pow_left 3 this
  exact Subgroup.index_eq_one.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem card_pow_of_sylow {P : Subgroup W5} (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) :
    Nat.card ↥P = 128 := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have h := P.card_mul_index
  rw [card_W5, hn] at h
  have hcop : Nat.Coprime (2 ^ 7) P.index :=
    Nat.Coprime.pow_left 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hidx)
  have h7 : (2 : ℕ) ^ 7 ∣ 2 ^ n * P.index := by rw [h]; norm_num
  have h7n : (2 : ℕ) ^ 7 ∣ 2 ^ n := hcop.dvd_of_dvd_mul_right h7
  have hge : 7 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h7n
  have hle : n ≤ 7 := by
    by_contra hlt
    push Not at hlt
    have h8 : (2 : ℕ) ^ 8 ∣ 28800 := (pow_dvd_pow 2 hlt).trans ⟨P.index, h.symm⟩
    norm_num at h8
  rw [hn, show n = 7 by omega]
  norm_num

@[expose] def Sw : Subgroup W5 where
  carrier := {w | w.left 1 4 = 4 ∧ w.left g2 4 = 4}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    have hb : ∀ q : Q2, b.left q 4 = 4 := by
      intro q
      rcases Q2_cases q with rfl | rfl
      · exact hb1
      · exact hb2
    constructor
    · rw [mul_l1]
      show a.left 1 (b.left a.right 4) = 4
      rw [hb, ha1]
    · rw [mul_lg]
      show a.left g2 (b.left (a.right * g2) 4) = 4
      rw [hb, ha2]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have ha : ∀ q : Q2, a.left q 4 = 4 := by
      intro q
      rcases Q2_cases q with rfl | rfl
      · exact ha1
      · exact ha2
    constructor
    · rw [inv_l1]
      show (a.left a.right)⁻¹ 4 = 4
      rw [Equiv.Perm.inv_eq_iff_eq, ha]
    · rw [inv_lg]
      show (a.left (a.right * g2))⁻¹ 4 = 4
      rw [Equiv.Perm.inv_eq_iff_eq, ha]

theorem mem_Sw {w : W5} : w ∈ Sw ↔ w.left 1 4 = 4 ∧ w.left g2 4 = 4 := Iff.rfl

theorem incl1_mem_Sw {σ : S5} (h : σ 4 = 4) : incl1 σ ∈ Sw :=
  ⟨by simpa [incl1_apply] using h, by simp [incl1_apply]⟩

theorem incl2_mem_Sw {σ : S5} (h : σ 4 = 4) : incl2 σ ∈ Sw := ⟨by simp [incl2_apply], by simpa [incl2_apply] using h⟩

@[expose] def Swequiv : ↥Sw ≃ ({σ : S5 // σ 4 = 4} × {σ : S5 // σ 4 = 4}) × Q2 where
  toFun w := ((⟨w.1.left 1, w.2.1⟩, ⟨w.1.left g2, w.2.2⟩), w.1.right)
  invFun x := ⟨mk x.1.1.1 x.1.2.1 x.2, by simpa using x.1.1.2, by simpa using x.1.2.2⟩
  left_inv w := by
    apply Subtype.ext
    apply ext' <;> simp
  right_inv x := by simp

theorem card_Sw : Nat.card ↥Sw = 1152 := by
  rw [Nat.card_congr Swequiv, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card,
    card_stab4, card_Q2]

theorem Sw_ne_top : Sw ≠ ⊤ := by
  intro h
  have : mk (Equiv.swap 4 0) 1 1 ∈ Sw := by rw [h]; exact Subgroup.mem_top _
  have h4 := this.1
  simp at h4

theorem exists_conj_le_Sw {P : Subgroup W5} (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) :
    ∃ g : W5, ∀ x ∈ P, g * x * g⁻¹ ∈ Sw := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥Sw) := inferInstance
  have hQcard : Nat.card ↥(Q : Subgroup ↥Sw) = 128 := by
    obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
    have h := (Q : Subgroup ↥Sw).card_mul_index
    have hodd : ¬ 2 ∣ (Q : Subgroup ↥Sw).index := Q.not_dvd_index
    rw [card_Sw, hn] at h
    have hcop : Nat.Coprime (2 ^ 7) (Q : Subgroup ↥Sw).index :=
      Nat.Coprime.pow_left 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    have h7 : (2 : ℕ) ^ 7 ∣ 2 ^ n * (Q : Subgroup ↥Sw).index := by rw [h]; norm_num
    have h7n : (2 : ℕ) ^ 7 ∣ 2 ^ n := hcop.dvd_of_dvd_mul_right h7
    have hge : 7 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h7n
    have hle : n ≤ 7 := by
      by_contra hlt
      push Not at hlt
      have h8 : (2 : ℕ) ^ 8 ∣ 1152 := (pow_dvd_pow 2 hlt).trans ⟨(Q : Subgroup ↥Sw).index, h.symm⟩
      norm_num at h8
    rw [hn, show n = 7 by omega]
    norm_num
  set Q' : Subgroup W5 := (Q : Subgroup ↥Sw).map Sw.subtype with hQ'
  have hQ'card : Nat.card ↥Q' = 128 := by
    rw [hQ', ← hQcard]
    exact (Nat.card_congr ((Subgroup.equivMapOfInjective _ Sw.subtype
      Subtype.val_injective).toEquiv)).symm
  have hQ'p : IsPGroup 2 Q' := by
    rw [hQ']
    exact Q.isPGroup'.map Sw.subtype
  have hQ'idx : ¬ 2 ∣ Q'.index := by
    have h := Q'.card_mul_index
    rw [card_W5, hQ'card] at h
    have : Q'.index = 225 := by omega
    rw [this]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W5 (hP.toSylow hidx) (hQ'p.toSylow hQ'idx)
  refine ⟨g, fun x hx => ?_⟩
  have hx' : x ∈ ((hP.toSylow hidx : Sylow 2 W5) : Set W5) := by simpa using hx
  have h1 : (MulAut.conj g) • x ∈ ((g • hP.toSylow hidx : Sylow 2 W5) : Set W5) := by
    rw [Sylow.coe_smul]
    exact Set.smul_mem_smul_set hx'
  rw [hg] at h1
  have h2 : g * x * g⁻¹ ∈ Q' := by simpa using h1
  obtain ⟨y, -, hy⟩ := h2
  rw [← hy]
  exact y.2

theorem pow_mk_one (a b : S5) (n : ℕ) : (mk a b 1) ^ n = mk (a ^ n) (b ^ n) 1 := by
  induction n with
  | zero => apply ext' <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    apply ext' <;> simp [mul_l1, mul_lg, pow_succ]

theorem orderOf_c3 : orderOf c3 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime c3_cube c3_ne_one

theorem c3_pow_two_pow_ne_one (k : ℕ) : c3 ^ (2 ^ k) ≠ 1 := by
  intro h
  have h3 : 3 ∣ 2 ^ k := by rw [← orderOf_c3]; exact orderOf_dvd_of_pow_eq_one h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem commutator_not_two_element {p : W5} (hp : p ∉ base) (k : ℕ) :
    (p * incl1 c3 * p⁻¹ * (incl1 c3)⁻¹) ^ (2 ^ k) ≠ 1 := by
  have hr : p.right = g2 := by
    rcases Q2_cases p.right with h | h
    · exact absurd (mem_base.2 h) hp
    · exact h
  rw [conj_incl1_of_not_base hr, ← map_inv, ← incl1_mul_incl2_comm, ← mk_one_eq, pow_mk_one]
  intro h
  have := congrArg (fun w : W5 => w.left 1) h
  simp only [mk_l1] at this
  exact c3_pow_two_pow_ne_one k (by simpa using this)

@[expose] def E0 : Subgroup W5 where
  carrier := {w | w.right = 1 ∧ w.left 1 ∈ Subgroup.zpowers c3 ∧ w.left g2 ∈ Subgroup.zpowers c3}
  one_mem' := ⟨rfl, one_mem _, one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨by simp [ha, hb], ?_, ?_⟩
    · rw [mul_l1, ha]
      exact mul_mem ha1 hb1
    · rw [mul_lg, ha]
      simpa using mul_mem ha2 hb2
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨by simp [ha], ?_, ?_⟩
    · rw [inv_l1, ha]
      exact inv_mem ha1
    · rw [inv_lg, ha]
      simpa using inv_mem ha2

theorem mem_E0 {w : W5} :
    w ∈ E0 ↔ w.right = 1 ∧ w.left 1 ∈ Subgroup.zpowers c3 ∧ w.left g2 ∈ Subgroup.zpowers c3 :=
  Iff.rfl

theorem E0_le_S0 : E0 ≤ S0 := by
  intro w hw
  have hle : Subgroup.zpowers c3 ≤ A5 := (Subgroup.zpowers_le).2 ((mem_A5).2 c3_even)
  exact ⟨hw.1, hle hw.2.1, hle hw.2.2⟩

theorem zpowers_c3_le_stab {σ : S5} (h : σ ∈ Subgroup.zpowers c3) : σ 4 = 4 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self c3_four k

theorem E0_le_Sw : E0 ≤ Sw := fun _ hw => ⟨zpowers_c3_le_stab hw.2.1, zpowers_c3_le_stab hw.2.2⟩

theorem E0_cube {w : W5} (hw : w ∈ E0) : w ^ 3 = 1 := by
  obtain ⟨hr, h1, h2⟩ := hw
  have : w = mk (w.left 1) (w.left g2) 1 := by
    have := eta w
    rwa [hr] at this
  rw [this, pow_mk_one]
  have hc : ∀ σ ∈ Subgroup.zpowers c3, σ ^ 3 = 1 := by
    intro σ hσ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
    have h3 : c3 ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, c3_cube]
    calc (c3 ^ k) ^ 3 = (c3 ^ k) ^ ((3 : ℕ) : ℤ) := (zpow_natCast _ 3).symm
      _ = c3 ^ (k * 3) := (zpow_mul c3 k 3).symm
      _ = (c3 ^ (3 : ℤ)) ^ k := by rw [mul_comm, zpow_mul]
      _ = 1 := by rw [h3, one_zpow]
  rw [hc _ h1, hc _ h2]
  apply ext' <;> simp

theorem E0_comm {a b : W5} (ha : a ∈ E0) (hb : b ∈ E0) : a * b = b * a := by
  obtain ⟨hra, ha1, ha2⟩ := ha
  obtain ⟨hrb, hb1, hb2⟩ := hb
  have hcomm : ∀ x ∈ Subgroup.zpowers c3, ∀ y ∈ Subgroup.zpowers c3, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self c3 i j).eq
  apply ext' <;> simp [mul_l1, mul_lg, hra, hrb, hcomm _ ha1 _ hb1, hcomm _ ha2 _ hb2, mul_r]

theorem card_E0 : Nat.card ↥E0 = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : ↥E0 ≃ ↥(Subgroup.zpowers c3) × ↥(Subgroup.zpowers c3) :=
    { toFun := fun w => (⟨w.1.left 1, w.2.2.1⟩, ⟨w.1.left g2, w.2.2.2⟩)
      invFun := fun x => ⟨mk x.1.1 x.2.1 1, rfl, by simpa using x.1.2, by simpa using x.2.2⟩
      left_inv := fun w => by
        apply Subtype.ext
        apply ext' <;> simp [w.2.1]
      right_inv := fun x => by simp }
  rw [Nat.card_congr f, Nat.card_prod, Nat.card_zpowers, orderOf_c3]

theorem normalizer_le_Sw {Q : Subgroup W5} (hQ : Q ≤ A1 ⊓ Sw) (hne : Q ≠ ⊥) (hP : IsPGroup 2 Q)
    {a : W5} (ha : a ∈ A1) (hn : a ∈ Subgroup.normalizer (Q : Set W5)) : a ∈ Sw := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn2⟩ := hP.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    rw [Subgroup.eq_bot_iff_card]
    simpa using hn2
  have h2dvd : 2 ∣ Nat.card ↥Q := by
    rw [hn2]
    exact dvd_pow_self 2 hn0
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 2 h2dvd
  have hq2 : (q : W5) * q = 1 := by
    have := pow_orderOf_eq_one q
    rw [hq] at this
    simpa [pow_two] using congrArg Subtype.val this
  have hq1 : (q : W5) ≠ 1 := by
    intro h
    have : q = 1 := Subtype.ext h
    rw [this, orderOf_one] at hq
    omega
  obtain ⟨hqr, hqg, hqe⟩ := mem_A1.1 (Subgroup.mem_inf.1 (hQ q.2)).1
  have hqS := mem_Sw.1 (Subgroup.mem_inf.1 (hQ q.2)).2
  set σ := (q : W5).left 1 with hσ
  have hσσ : σ * σ = 1 := by
    have := congrArg (fun w : W5 => w.left 1) hq2
    simpa [mul_l1, hqr] using this
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hq1
    apply ext' <;> simp [hqg, hqr, ← hσ, h]
  have hfix : ∀ x : Fin 5, σ x = x → x = 4 :=
    involution_fixed_unique σ (mem_A5.1 hqe) hσσ hσ1 hqS.1
  obtain ⟨α, hαA, rfl⟩ := ha
  have hconj : incl1 α * (q : W5) * (incl1 α)⁻¹ ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 hn (q : W5)).1 q.2
    simpa using this
  have h4 := (mem_Sw.1 (Subgroup.mem_inf.1 (hQ hconj)).2).1
  have hq' : (q : W5) = incl1 σ := by
    apply ext' <;> simp [incl1_apply, hqr, hqg, ← hσ]
  have e : incl1 α * (q : W5) * (incl1 α)⁻¹ = incl1 (α * σ * α⁻¹) := by
    rw [hq']
    simp [map_mul, map_inv]
  rw [e] at h4
  have h5 : (α * σ * α⁻¹) 4 = 4 := by simpa [incl1_apply] using h4
  have h6 : σ (α⁻¹ 4) = α⁻¹ 4 := by
    have h8 : α (σ (α⁻¹ 4)) = 4 := by simpa [Equiv.Perm.mul_apply] using h5
    have h9 := congrArg (fun x => α⁻¹ x) h8
    simpa using h9
  have h7 : α⁻¹ 4 = 4 := hfix _ h6
  apply incl1_mem_Sw
  have := congrArg α h7
  simpa using this.symm

theorem inj_quot {N A : Subgroup W5} [N.Normal] (h : N ⊓ A = ⊥) :
    Function.Injective ((QuotientGroup.mk' N).comp A.subtype) := by
  intro x y hxy
  have h1 : (x : W5)⁻¹ * y ∈ N := by
    have := (QuotientGroup.eq (a := (x : W5)) (b := (y : W5)) (s := N)).1 hxy
    exact this
  have h2 : (x : W5)⁻¹ * y ∈ N ⊓ A :=
    Subgroup.mem_inf.2 ⟨h1, A.mul_mem (A.inv_mem x.2) y.2⟩
  rw [h, Subgroup.mem_bot] at h2
  exact Subtype.ext (inv_mul_eq_one.1 h2)

theorem card_A1 : Nat.card ↥A1 = 60 := by rw [← Nat.card_congr A1equiv.toEquiv, card_A5]

theorem card_A2 : Nat.card ↥A2 = 60 := by rw [← Nat.card_congr A2equiv.toEquiv, card_A5]

theorem eq_base_of_equiv_prod {J : Subgroup W5} (e : ↥J ≃* S5 × S5) : J = base := by
  have hcardJ : Nat.card ↥J = 14400 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_S5]
  have hidx : J.index = 2 := by
    have h := J.card_mul_index
    rw [hcardJ, card_W5] at h
    omega
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hidx
  have hq : Nat.card (W5 ⧸ J) = 2 := hidx
  have hAJ : ∀ {A : Subgroup W5}, IsSimpleGroup ↥A → Nat.card ↥A = 60 → A ≤ J := by
    intro A hA hAc
    rcases simple_inf_dichotomy hA (fun a _ n hn => hJn.conj_mem n hn a) with h | h
    · exfalso
      have := Nat.card_le_card_of_injective _ (inj_quot (N := J) (A := A) h)
      rw [hAc, hq] at this
      omega
    · exact h
  have hA1J : A1 ≤ J := hAJ A1_simple card_A1
  have hA2J : A2 ≤ J := hAJ A2_simple card_A2
  have hS0J : S0 ≤ J := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := S0_eq_mul hw
    exact J.mul_mem (hA1J ha) (hA2J hb)
  let φ : S5 →* W5 := J.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl S5 S5))
  have hφ : Function.Injective φ := by
    intro a b h
    have h1 : e.symm (a, 1) = e.symm (b, 1) := Subtype.ext h
    have := e.symm.injective h1
    exact (Prod.mk.inj this).1
  let D : Subgroup W5 := A5.map φ
  have hDe : ↥A5 ≃* ↥D := Subgroup.equivMapOfInjective A5 φ hφ
  have hDsimple : IsSimpleGroup ↥D := hDe.symm.isSimpleGroup
  have hDcard : Nat.card ↥D = 60 := by rw [← Nat.card_congr hDe.toEquiv, card_A5]
  have hDJ : D ≤ J := by
    rintro _ ⟨a, -, rfl⟩
    exact (e.symm (a, 1)).2
  have hDnorm : ∀ j ∈ J, ∀ d ∈ D, j * d * j⁻¹ ∈ D := by
    intro j hj d hd
    obtain ⟨a, ha, rfl⟩ := hd
    obtain ⟨x, hx⟩ : ∃ x : S5 × S5, e.symm x = ⟨j, hj⟩ := ⟨e ⟨j, hj⟩, e.symm_apply_apply _⟩
    refine ⟨x.1 * a * x.1⁻¹, Subgroup.Normal.conj_mem inferInstance a ha x.1, ?_⟩
    have key : e.symm (x.1 * a * x.1⁻¹, 1) = e.symm x * e.symm (a, 1) * (e.symm x)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    show ((e.symm (x.1 * a * x.1⁻¹, 1) : ↥J) : W5) = j * ((e.symm (a, 1) : ↥J) : W5) * j⁻¹
    rw [key, hx]
    rfl
  have hDS0 : D ≤ S0 := by
    rcases simple_inf_dichotomy hDsimple (fun a _ n hn => conj_mem_S0 a hn) with h | h
    · exfalso
      have := Nat.card_le_card_of_injective _ (inj_quot (N := S0) (A := D) h)
      have hq8 : Nat.card (W5 ⧸ S0) = 8 := index_S0
      rw [hDcard, hq8] at this
      omega
    · exact h
  have hDnormS0 : ∀ s ∈ S0, ∀ n ∈ D, s * n * s⁻¹ ∈ D := fun s hs n hn => hDnorm s (hS0J hs) n hn
  have hJle : D = A1 ∨ D = A2 → J ≤ base := by
    intro hD
    intro j hj
    have hjn : j ∈ Subgroup.normalizer (D : Set W5) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hDnorm j hj h hh, fun hh => ?_⟩
      have := hDnorm j⁻¹ (J.inv_mem hj) _ hh
      have e' : j⁻¹ * (j * h * j⁻¹) * j⁻¹⁻¹ = h := by group
      rwa [e'] at this
    rcases hD with hD | hD
    · rw [hD, normalizer_A1] at hjn
      exact hjn
    · rw [hD, normalizer_A2] at hjn
      exact hjn
  rcases normal_in_S0 hDS0 hDnormS0 with h | h | h | h
  · rw [h, Subgroup.card_bot] at hDcard
    omega
  · exact Subgroup.eq_of_le_of_card_ge (hJle (Or.inl h)) (by rw [hcardJ, card_base])
  · exact Subgroup.eq_of_le_of_card_ge (hJle (Or.inr h)) (by rw [hcardJ, card_base])
  · rw [h, card_S0] at hDcard
    omega

theorem mem_base_of_odd_orderOf {w : W5} (h : Odd (orderOf w)) : w ∈ base := by
  have hd : orderOf w.right ∣ orderOf w := by
    have := orderOf_map_dvd (RegularWreathProduct.rightHom : W5 →* Q2) w
    exact this
  have hQ : orderOf w.right ∣ 2 := by
    rcases Q2_cases w.right with h' | h'
    · rw [h']; simp
    · rw [h']
      have : g2 ^ 2 = 1 := by rw [pow_two]; exact g2_mul_g2
      exact orderOf_dvd_of_pow_eq_one this
  have h1 : orderOf w.right = 1 := by
    have h2 : orderOf w.right ∣ Nat.gcd (orderOf w) 2 := Nat.dvd_gcd hd hQ
    have hg : Nat.gcd (orderOf w) 2 = 1 := by
      exact Nat.coprime_two_right.2 h
    rw [hg] at h2
    exact Nat.dvd_one.1 h2
  exact mem_base.2 (orderOf_eq_one_iff.1 h1)

theorem not_le_base_of_sylow {P : Subgroup W5} (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) :
    ¬ P ≤ base := by
  intro hle
  have h1 := Subgroup.card_dvd_of_le hle
  rw [card_pow_of_sylow hP hidx, card_base] at h1
  norm_num at h1

end W5

end CFSG.Quasithin.He9
