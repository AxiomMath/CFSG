module

public import CFSG.Quasithin.EmptyFaithful.S143KD

public section

namespace CFSG.Quasithin.S143

namespace A6Model

@[expose] def V4.zero : V4 := ⟨false, false, false, false⟩

theorem V4.add_assoc (u v w : V4) : (u.add v).add w = u.add (v.add w) := by
  cases u; cases v; cases w; simp only [V4.add, Bool.xor_assoc]

theorem V4.add_eq_zero {v w : V4} (h : v.add w = V4.zero) : v = w := by
  have hb : ∀ a b : Bool, (a ^^ b) = false → a = b := by decide
  cases v; cases w
  simp only [V4.add, V4.zero, V4.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp [hb _ _ h0, hb _ _ h1, hb _ _ h2, hb _ _ h3]

theorem V4.sm_true (v : V4) : V4.sm true v = v := by
  cases v; simp [V4.sm]

theorem V4.sm_false (v : V4) : V4.sm false v = V4.zero := by
  cases v; simp [V4.sm, V4.zero]

@[expose] def V4.equivProd : V4 ≃ Bool × Bool × Bool × Bool where
  toFun v := (v.x0, v.x1, v.x2, v.x3)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv v := by cases v; rfl
  right_inv p := rfl

theorem V4.card : Nat.card V4 = 16 := by
  rw [Nat.card_congr V4.equivProd]
  simp

theorem vm_I4 (v : V4) : vm v I4 = v := by
  cases v with
  | mk a b c d => cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem vm_zero (M : Mat4) : vm V4.zero M = V4.zero := by
  simp [vm, V4.zero, V4.sm, V4.add]

variable {G : Type*} [Group G]

@[expose] def embV (e0 e1 e2 e3 : G) (v : V4) : G :=
  (if v.x0 then e0 else 1) * (if v.x1 then e1 else 1) * (if v.x2 then e2 else 1) *
    (if v.x3 then e3 else 1)

theorem embV_zero (e0 e1 e2 e3 : G) : embV e0 e1 e2 e3 V4.zero = 1 := by
  simp [embV, V4.zero]

structure IsBasis (A : Subgroup G) (e0 e1 e2 e3 : G) : Prop where
  mem0 : e0 ∈ A
  mem1 : e1 ∈ A
  mem2 : e2 ∈ A
  mem3 : e3 ∈ A
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  sq : ∀ a ∈ A, a * a = 1
  card : Nat.card ↥A = 16
  indep : ∀ v : V4, embV e0 e1 e2 e3 v = 1 → v = V4.zero

section Basis

variable {A : Subgroup G} {e0 e1 e2 e3 : G} (h : IsBasis A e0 e1 e2 e3)

include h

abbrev IsBasis.commGroup : CommGroup ↥A :=
  { (inferInstance : Group ↥A) with
    mul_comm := fun a b => Subtype.ext (h.comm a.1 a.2 b.1 b.2) }

theorem IsBasis.embV_mem (v : V4) : embV e0 e1 e2 e3 v ∈ A := by
  unfold embV
  refine A.mul_mem (A.mul_mem (A.mul_mem ?_ ?_) ?_) ?_
  · split_ifs
    exacts [h.mem0, A.one_mem]
  · split_ifs
    exacts [h.mem1, A.one_mem]
  · split_ifs
    exacts [h.mem2, A.one_mem]
  · split_ifs
    exacts [h.mem3, A.one_mem]

theorem IsBasis.val_embV (v : V4) :
    ((embV (⟨e0, h.mem0⟩ : ↥A) ⟨e1, h.mem1⟩ ⟨e2, h.mem2⟩ ⟨e3, h.mem3⟩ v : ↥A) : G) =
      embV e0 e1 e2 e3 v := by
  cases v with
  | mk a b c d => cases a <;> cases b <;> cases c <;> cases d <;> simp [embV]

theorem IsBasis.embV_add (v w : V4) :
    embV e0 e1 e2 e3 (v.add w) = embV e0 e1 e2 e3 v * embV e0 e1 e2 e3 w := by
  let _ : CommGroup ↥A := h.commGroup
  have hx : ∀ (b c : Bool) (n : ↥A), n * n = 1 →
      (if xor b c = true then n else 1) = (if b = true then n else 1) * (if c = true then n else 1) := by
    intro b c n hn
    cases b <;> cases c <;> simp [hn]
  have hsq : ∀ n : ↥A, n * n = 1 := fun n => Subtype.ext (h.sq n.1 n.2)
  have main : embV (⟨e0, h.mem0⟩ : ↥A) ⟨e1, h.mem1⟩ ⟨e2, h.mem2⟩ ⟨e3, h.mem3⟩ (v.add w) =
      embV (⟨e0, h.mem0⟩ : ↥A) ⟨e1, h.mem1⟩ ⟨e2, h.mem2⟩ ⟨e3, h.mem3⟩ v *
        embV (⟨e0, h.mem0⟩ : ↥A) ⟨e1, h.mem1⟩ ⟨e2, h.mem2⟩ ⟨e3, h.mem3⟩ w := by
    have key : embV (⟨e0, h.mem0⟩ : ↥A) ⟨e1, h.mem1⟩ ⟨e2, h.mem2⟩ ⟨e3, h.mem3⟩ (v.add w) =
        (if xor v.x0 w.x0 = true then (⟨e0, h.mem0⟩ : ↥A) else 1) *
          (if xor v.x1 w.x1 = true then (⟨e1, h.mem1⟩ : ↥A) else 1) *
          (if xor v.x2 w.x2 = true then (⟨e2, h.mem2⟩ : ↥A) else 1) *
          (if xor v.x3 w.x3 = true then (⟨e3, h.mem3⟩ : ↥A) else 1) := rfl
    rw [key, hx v.x0 w.x0 _ (hsq _), hx v.x1 w.x1 _ (hsq _), hx v.x2 w.x2 _ (hsq _),
      hx v.x3 w.x3 _ (hsq _)]
    unfold embV
    ac_rfl
  have := congrArg Subtype.val main
  rwa [Subgroup.coe_mul, h.val_embV, h.val_embV, h.val_embV] at this

open Classical in
noncomputable def coordsOf (e0 e1 e2 e3 : G) (a : G) : V4 :=
  if h : ∃ v, embV e0 e1 e2 e3 v = a then h.choose else V4.zero

theorem IsBasis.embV_inj (v w : V4) (hvw : embV e0 e1 e2 e3 v = embV e0 e1 e2 e3 w) : v = w := by
  apply V4.add_eq_zero
  apply h.indep
  rw [h.embV_add, hvw]
  exact h.sq _ (h.embV_mem w)

theorem IsBasis.embV_surj {a : G} (ha : a ∈ A) : ∃ v, embV e0 e1 e2 e3 v = a := by
  have hfin : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  let f : V4 → ↥A := fun v => ⟨embV e0 e1 e2 e3 v, h.embV_mem v⟩
  have hf : Function.Injective f := fun v w hvw => h.embV_inj v w (congrArg Subtype.val hvw)
  have hb := hf.bijective_of_nat_card_le (by rw [h.card, V4.card])
  obtain ⟨v, hv⟩ := hb.2 ⟨a, ha⟩
  exact ⟨v, congrArg Subtype.val hv⟩

theorem IsBasis.embV_coordsOf {a : G} (ha : a ∈ A) :
    embV e0 e1 e2 e3 (coordsOf e0 e1 e2 e3 a) = a := by
  have hex := h.embV_surj ha
  unfold coordsOf
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem IsBasis.coordsOf_embV (v : V4) : coordsOf e0 e1 e2 e3 (embV e0 e1 e2 e3 v) = v := by
  apply h.embV_inj
  rw [h.embV_coordsOf (h.embV_mem v)]

theorem IsBasis.coordsOf_inj {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (hab : coordsOf e0 e1 e2 e3 a = coordsOf e0 e1 e2 e3 b) : a = b := by
  rw [← h.embV_coordsOf ha, ← h.embV_coordsOf hb, hab]

theorem IsBasis.coordsOf_mul {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    coordsOf e0 e1 e2 e3 (a * b) =
      (coordsOf e0 e1 e2 e3 a).add (coordsOf e0 e1 e2 e3 b) := by
  have : a * b = embV e0 e1 e2 e3 ((coordsOf e0 e1 e2 e3 a).add (coordsOf e0 e1 e2 e3 b)) := by
    rw [h.embV_add, h.embV_coordsOf ha, h.embV_coordsOf hb]
  rw [this, h.coordsOf_embV]

theorem IsBasis.coordsOf_one : coordsOf e0 e1 e2 e3 1 = V4.zero := by
  rw [← embV_zero e0 e1 e2 e3, h.coordsOf_embV]

theorem IsBasis.coordsOf_ite (b : Bool) (e : G) :
    coordsOf e0 e1 e2 e3 (if b = true then e else 1) = V4.sm b (coordsOf e0 e1 e2 e3 e) := by
  cases b
  · simp [h.coordsOf_one, V4.sm_false]
  · simp [V4.sm_true]

theorem IsBasis.coordsOf_e0 : coordsOf e0 e1 e2 e3 e0 = ⟨true, false, false, false⟩ := by
  have hh : e0 = embV e0 e1 e2 e3 ⟨true, false, false, false⟩ := by simp [embV]
  exact (congrArg (coordsOf e0 e1 e2 e3) hh).trans (h.coordsOf_embV _)

theorem IsBasis.coordsOf_e1 : coordsOf e0 e1 e2 e3 e1 = ⟨false, true, false, false⟩ := by
  have hh : e1 = embV e0 e1 e2 e3 ⟨false, true, false, false⟩ := by simp [embV]
  exact (congrArg (coordsOf e0 e1 e2 e3) hh).trans (h.coordsOf_embV _)

theorem IsBasis.coordsOf_e2 : coordsOf e0 e1 e2 e3 e2 = ⟨false, false, true, false⟩ := by
  have hh : e2 = embV e0 e1 e2 e3 ⟨false, false, true, false⟩ := by simp [embV]
  exact (congrArg (coordsOf e0 e1 e2 e3) hh).trans (h.coordsOf_embV _)

theorem IsBasis.coordsOf_e3 : coordsOf e0 e1 e2 e3 e3 = ⟨false, false, false, true⟩ := by
  have hh : e3 = embV e0 e1 e2 e3 ⟨false, false, false, true⟩ := by simp [embV]
  exact (congrArg (coordsOf e0 e1 e2 e3) hh).trans (h.coordsOf_embV _)

@[expose] noncomputable def cmat (e0 e1 e2 e3 : G) (γ : G) : Mat4 :=
  ⟨coordsOf e0 e1 e2 e3 (γ * e0 * γ⁻¹), coordsOf e0 e1 e2 e3 (γ * e1 * γ⁻¹),
    coordsOf e0 e1 e2 e3 (γ * e2 * γ⁻¹), coordsOf e0 e1 e2 e3 (γ * e3 * γ⁻¹)⟩

omit h in
theorem conj_mem_of_mem_normalizer {γ : G} (hγ : γ ∈ Subgroup.normalizer (A : Set G)) {a : G}
    (ha : a ∈ A) : γ * a * γ⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp hγ a).mp ha

theorem IsBasis.cmat_spec {γ : G} (hγ : γ ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) :
    coordsOf e0 e1 e2 e3 (γ * a * γ⁻¹) = vm (coordsOf e0 e1 e2 e3 a) (cmat e0 e1 e2 e3 γ) := by
  set v := coordsOf e0 e1 e2 e3 a with hv
  have hav : a = embV e0 e1 e2 e3 v := (h.embV_coordsOf ha).symm
  have hc : ∀ (b : Bool) (e : G), γ * (if b = true then e else 1) * γ⁻¹ =
      if b = true then γ * e * γ⁻¹ else 1 := by
    intro b e; cases b <;> simp
  have hm : ∀ (b : Bool) (e : G), e ∈ A → (if b = true then γ * e * γ⁻¹ else 1) ∈ A := by
    intro b e he
    cases b
    · simp
    · simpa using conj_mem_of_mem_normalizer hγ he
  have h0 := hm v.x0 e0 h.mem0
  have h1 := hm v.x1 e1 h.mem1
  have h2 := hm v.x2 e2 h.mem2
  have h3 := hm v.x3 e3 h.mem3
  have hconj : γ * a * γ⁻¹ = (if v.x0 = true then γ * e0 * γ⁻¹ else 1) *
      (if v.x1 = true then γ * e1 * γ⁻¹ else 1) * (if v.x2 = true then γ * e2 * γ⁻¹ else 1) *
      (if v.x3 = true then γ * e3 * γ⁻¹ else 1) := by
    rw [← hc, ← hc, ← hc, ← hc, hav]
    unfold embV
    group
  rw [hconj, h.coordsOf_mul (A.mul_mem (A.mul_mem h0 h1) h2) h3, h.coordsOf_mul (A.mul_mem h0 h1) h2,
    h.coordsOf_mul h0 h1, h.coordsOf_ite, h.coordsOf_ite, h.coordsOf_ite, h.coordsOf_ite]
  simp only [V4.add_assoc]
  rfl

theorem IsBasis.cmat_mul {γ₁ γ₂ : G} (h₁ : γ₁ ∈ Subgroup.normalizer (A : Set G))
    (h₂ : γ₂ ∈ Subgroup.normalizer (A : Set G)) :
    cmat e0 e1 e2 e3 (γ₁ * γ₂) = mm (cmat e0 e1 e2 e3 γ₂) (cmat e0 e1 e2 e3 γ₁) := by
  have key : ∀ e ∈ A, coordsOf e0 e1 e2 e3 (γ₁ * γ₂ * e * (γ₁ * γ₂)⁻¹) =
      vm (coordsOf e0 e1 e2 e3 (γ₂ * e * γ₂⁻¹)) (cmat e0 e1 e2 e3 γ₁) := by
    intro e he
    rw [← h.cmat_spec h₁ (conj_mem_of_mem_normalizer h₂ he)]
    congr 1
    group
  show (⟨coordsOf e0 e1 e2 e3 (γ₁ * γ₂ * e0 * (γ₁ * γ₂)⁻¹), coordsOf e0 e1 e2 e3 (γ₁ * γ₂ * e1 * (γ₁ * γ₂)⁻¹),
      coordsOf e0 e1 e2 e3 (γ₁ * γ₂ * e2 * (γ₁ * γ₂)⁻¹),
      coordsOf e0 e1 e2 e3 (γ₁ * γ₂ * e3 * (γ₁ * γ₂)⁻¹)⟩ : Mat4) = _
  rw [key e0 h.mem0, key e1 h.mem1, key e2 h.mem2, key e3 h.mem3]
  rfl

theorem IsBasis.cmat_one : cmat e0 e1 e2 e3 (1 : G) = I4 := by
  show (⟨coordsOf e0 e1 e2 e3 (1 * e0 * 1⁻¹), coordsOf e0 e1 e2 e3 (1 * e1 * 1⁻¹),
      coordsOf e0 e1 e2 e3 (1 * e2 * 1⁻¹), coordsOf e0 e1 e2 e3 (1 * e3 * 1⁻¹)⟩ : Mat4) = I4
  simp only [one_mul, inv_one, mul_one, h.coordsOf_e0, h.coordsOf_e1, h.coordsOf_e2, h.coordsOf_e3]
  rfl

theorem IsBasis.cmat_eq_one_iff {γ : G} (hγ : γ ∈ Subgroup.normalizer (A : Set G)) :
    cmat e0 e1 e2 e3 γ = I4 ↔ ∀ a ∈ A, γ * a * γ⁻¹ = a := by
  constructor
  · intro hI a ha
    apply h.coordsOf_inj (conj_mem_of_mem_normalizer hγ ha) ha
    rw [h.cmat_spec hγ ha, hI, vm_I4]
  · intro hc
    show (⟨coordsOf e0 e1 e2 e3 (γ * e0 * γ⁻¹), coordsOf e0 e1 e2 e3 (γ * e1 * γ⁻¹),
      coordsOf e0 e1 e2 e3 (γ * e2 * γ⁻¹), coordsOf e0 e1 e2 e3 (γ * e3 * γ⁻¹)⟩ : Mat4) = I4
    rw [hc e0 h.mem0, hc e1 h.mem1, hc e2 h.mem2, hc e3 h.mem3, h.coordsOf_e0, h.coordsOf_e1,
      h.coordsOf_e2, h.coordsOf_e3]
    rfl

theorem IsBasis.cmat_eq_iff {γ γ' : G} (hγ : γ ∈ Subgroup.normalizer (A : Set G))
    (hγ' : γ' ∈ Subgroup.normalizer (A : Set G)) :
    cmat e0 e1 e2 e3 γ = cmat e0 e1 e2 e3 γ' ↔ ∀ a ∈ A, γ * a * γ⁻¹ = γ' * a * γ'⁻¹ := by
  constructor
  · intro hI a ha
    apply h.coordsOf_inj (conj_mem_of_mem_normalizer hγ ha) (conj_mem_of_mem_normalizer hγ' ha)
    rw [h.cmat_spec hγ ha, h.cmat_spec hγ' ha, hI]
  · intro hc
    show (⟨coordsOf e0 e1 e2 e3 (γ * e0 * γ⁻¹), coordsOf e0 e1 e2 e3 (γ * e1 * γ⁻¹),
      coordsOf e0 e1 e2 e3 (γ * e2 * γ⁻¹), coordsOf e0 e1 e2 e3 (γ * e3 * γ⁻¹)⟩ : Mat4) =
      ⟨coordsOf e0 e1 e2 e3 (γ' * e0 * γ'⁻¹), coordsOf e0 e1 e2 e3 (γ' * e1 * γ'⁻¹),
      coordsOf e0 e1 e2 e3 (γ' * e2 * γ'⁻¹), coordsOf e0 e1 e2 e3 (γ' * e3 * γ'⁻¹)⟩
    rw [hc e0 h.mem0, hc e1 h.mem1, hc e2 h.mem2, hc e3 h.mem3]

end Basis

theorem ncard_image_mul_card {S E : Subgroup G} (hES : E ≤ S) {X : Type*} (f : G → X)
    (hf : ∀ s ∈ S, ∀ s' ∈ S, f s = f s' ↔ s⁻¹ * s' ∈ E) :
    (f '' (S : Set G)).ncard * Nat.card E = Nat.card S := by
  let q : Subgroup ↥S := E.subgroupOf S
  let F : ↥S ⧸ q → ↥(f '' (S : Set G)) :=
    Quotient.lift (fun s : ↥S => (⟨f s, s, s.2, rfl⟩ : ↥(f '' (S : Set G)))) (by
      intro a b hab
      have hab' : (a : G)⁻¹ * b ∈ E := by
        have := (QuotientGroup.leftRel_apply (s := q)).mp hab
        exact this
      exact Subtype.ext ((hf a a.2 b b.2).mpr hab'))
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      induction x using Quotient.inductionOn with
      | h a =>
        induction y using Quotient.inductionOn with
        | h b =>
          have h1 : f a = f b := congrArg Subtype.val hxy
          exact Quotient.sound ((QuotientGroup.leftRel_apply (s := q)).mpr
            ((hf a a.2 b b.2).mp h1))
    · rintro ⟨m, s, hs, rfl⟩
      exact ⟨Quotient.mk _ ⟨s, hs⟩, rfl⟩
  have h1 : Nat.card ↥(f '' (S : Set G)) = q.index := by
    rw [Subgroup.index, Nat.card_congr (Equiv.ofBijective F hF)]
  have h2 : Nat.card q = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  rw [← Nat.card_coe_set_eq, h1, ← h2]
  exact Subgroup.index_mul_card q

end A6Model

end CFSG.Quasithin.S143
