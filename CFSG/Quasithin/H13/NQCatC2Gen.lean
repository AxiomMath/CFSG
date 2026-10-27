module

public import CFSG.Quasithin.H13.NQCatC2Prod

public section

namespace CFSG.Quasithin.H13.NQCat.C2

open scoped Pointwise

variable {A : Type} [Group A]

section Inner

variable (Q D : Subgroup A)

@[expose] def InnerOn : Prop := ∀ d ∈ D, ∃ q ∈ Q, ∀ x ∈ Q, d * x * d⁻¹ = q * x * q⁻¹

variable {Q D}

@[expose] def CenterFree (Q : Subgroup A) : Prop := ∀ z ∈ Q, (∀ x ∈ Q, z * x = x * z) → z = 1

theorem CenterFree.eq_of_conj (hZ : CenterFree Q) {q q' : A} (hq : q ∈ Q) (hq' : q' ∈ Q)
    (h : ∀ x ∈ Q, q * x * q⁻¹ = q' * x * q'⁻¹) : q = q' := by
  have h1 : q'⁻¹ * q = 1 := by
    apply hZ _ (mul_mem (inv_mem hq') hq)
    intro x hx
    have := h x hx
    calc q'⁻¹ * q * x = q'⁻¹ * (q * x * q⁻¹) * q := by group
      _ = q'⁻¹ * (q' * x * q'⁻¹) * q := by rw [this]
      _ = x * (q'⁻¹ * q) := by group
  exact (inv_mul_eq_one.mp h1).symm

variable (hinn : InnerOn Q D)

@[expose] noncomputable def rep (d : ↥D) : A := (hinn d d.2).choose

theorem rep_mem (d : ↥D) : rep hinn d ∈ Q := (hinn d d.2).choose_spec.1

theorem rep_spec (d : ↥D) {x : A} (hx : x ∈ Q) :
    (d : A) * x * (d : A)⁻¹ = rep hinn d * x * (rep hinn d)⁻¹ :=
  (hinn d d.2).choose_spec.2 x hx

variable {hinn}

theorem eq_rep (hZ : CenterFree Q) {d : ↥D} {q : A} (hq : q ∈ Q)
    (h : ∀ x ∈ Q, (d : A) * x * (d : A)⁻¹ = q * x * q⁻¹) : q = rep hinn d :=
  hZ.eq_of_conj hq (rep_mem hinn d) fun x hx => by rw [← h x hx, rep_spec hinn d hx]

variable (hinn)

@[expose] noncomputable def repHom (hZ : CenterFree Q) (hDN : D ≤ Subgroup.normalizer (Q : Set A)) :
    ↥D →* A where
  toFun := rep hinn
  map_one' := (eq_rep hZ (one_mem Q) fun x _ => by simp).symm
  map_mul' d e := by
    refine (eq_rep hZ (mul_mem (rep_mem hinn d) (rep_mem hinn e)) fun x hx => ?_).symm
    have he : (e : A) * x * (e : A)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hDN e.2) x).mp hx
    calc ((d * e : ↥D) : A) * x * ((d * e : ↥D) : A)⁻¹
        = (d : A) * ((e : A) * x * (e : A)⁻¹) * (d : A)⁻¹ := by
          simp only [Subgroup.coe_mul]; group
      _ = rep hinn d * (rep hinn e * x * (rep hinn e)⁻¹) * (rep hinn d)⁻¹ := by
          rw [rep_spec hinn d he, rep_spec hinn e hx]
      _ = rep hinn d * rep hinn e * x * (rep hinn d * rep hinn e)⁻¹ := by group

@[expose] noncomputable def img (hZ : CenterFree Q) (hDN : D ≤ Subgroup.normalizer (Q : Set A)) :
    Subgroup A :=
  (repHom hinn hZ hDN).range

variable (hZ : CenterFree Q) (hDN : D ≤ Subgroup.normalizer (Q : Set A))

theorem img_le : img hinn hZ hDN ≤ Q := by
  rintro _ ⟨d, rfl⟩
  exact rep_mem hinn d

theorem isCyclic_img (hc : IsCyclic ↥D) : IsCyclic ↥(img hinn hZ hDN) :=
  isCyclic_of_surjective (repHom hinn hZ hDN).rangeRestrict
    (repHom hinn hZ hDN).rangeRestrict_surjective

theorem odd_card_img [Finite A] (ho : Odd (Nat.card ↥D)) : Odd (Nat.card ↥(img hinn hZ hDN)) :=
  Odd.of_dvd_nat ho (Subgroup.card_range_dvd _)

theorem mul_inv_rep_mem (d : ↥D) :
    (d : A) * (rep hinn d)⁻¹ ∈ Subgroup.centralizer (Q : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : (rep hinn d)⁻¹ * x * rep hinn d ∈ Q :=
    mul_mem (mul_mem (inv_mem (rep_mem hinn d)) hx) (rep_mem hinn d)
  have h2 := rep_spec hinn d h1
  calc x * ((d : A) * (rep hinn d)⁻¹) =
      (rep hinn d * ((rep hinn d)⁻¹ * x * rep hinn d) * (rep hinn d)⁻¹) * (d : A) *
        (rep hinn d)⁻¹ := by group
    _ = ((d : A) * ((rep hinn d)⁻¹ * x * rep hinn d) * (d : A)⁻¹) * (d : A) *
        (rep hinn d)⁻¹ := by rw [h2]
    _ = (d : A) * (rep hinn d)⁻¹ * x := by group

theorem le_img_sup : D ≤ img hinn hZ hDN ⊔ Subgroup.centralizer (Q : Set A) := by
  intro d hd
  have h1 := mul_inv_rep_mem hinn ⟨d, hd⟩
  have h2 : d = ((d : A) * (rep hinn ⟨d, hd⟩)⁻¹) * rep hinn ⟨d, hd⟩ := by group
  rw [h2]
  exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left ⟨⟨d, hd⟩, rfl⟩)

theorem conj_mem_img {b : A} (hbQ : b ∈ Q) (hbD : b ∈ Subgroup.normalizer (D : Set A))
    {x : A} (hx : x ∈ img hinn hZ hDN) : b * x * b⁻¹ ∈ img hinn hZ hDN := by
  obtain ⟨d, rfl⟩ := hx
  have hd' : b * (d : A) * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hbD _).mp d.2
  refine ⟨⟨_, hd'⟩, (eq_rep (hinn := hinn) hZ
    (mul_mem (mul_mem hbQ (rep_mem hinn d)) (inv_mem hbQ)) fun y hy => ?_).symm⟩
  have hy' : b⁻¹ * y * b ∈ Q := mul_mem (mul_mem (inv_mem hbQ) hy) hbQ
  have := rep_spec hinn d hy'
  calc b * (d : A) * b⁻¹ * y * (b * (d : A) * b⁻¹)⁻¹ =
      b * ((d : A) * (b⁻¹ * y * b) * (d : A)⁻¹) * b⁻¹ := by group
    _ = b * (repHom hinn hZ hDN d * (b⁻¹ * y * b) * (repHom hinn hZ hDN d)⁻¹) * b⁻¹ := by
        rw [this]; rfl
    _ = b * repHom hinn hZ hDN d * b⁻¹ * y * (b * repHom hinn hZ hDN d * b⁻¹)⁻¹ := by group

end Inner

section ActS

variable {Q S : Subgroup A}

@[expose] def actS (Q S : Subgroup A) (hSN : S ≤ Subgroup.normalizer (Q : Set A)) : Subgroup A where
  carrier := {y | y ∈ Q ∧ ∃ g ∈ S, ∀ q ∈ Q, y * q * y⁻¹ = g * q * g⁻¹}
  one_mem' := ⟨one_mem Q, 1, one_mem S, fun q _ => by simp⟩
  mul_mem' {a b} ha hb := by
    obtain ⟨haQ, g, hg, hga⟩ := ha
    obtain ⟨hbQ, k, hk, hkb⟩ := hb
    refine ⟨mul_mem haQ hbQ, g * k, mul_mem hg hk, fun q hq => ?_⟩
    have hkq : k * q * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hSN hk) q).mp hq
    calc a * b * q * (a * b)⁻¹ = a * (b * q * b⁻¹) * a⁻¹ := by group
      _ = g * (k * q * k⁻¹) * g⁻¹ := by rw [hkb q hq, hga _ hkq]
      _ = g * k * q * (g * k)⁻¹ := by group
  inv_mem' {a} ha := by
    obtain ⟨haQ, g, hg, hga⟩ := ha
    refine ⟨inv_mem haQ, g⁻¹, inv_mem hg, fun q hq => ?_⟩
    have hgq : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hSN (inv_mem hg)) q).mp hq
      simpa using this
    have := hga _ hgq
    calc a⁻¹ * q * a⁻¹⁻¹ = a⁻¹ * (g * (g⁻¹ * q * g) * g⁻¹) * a := by group
      _ = a⁻¹ * (a * (g⁻¹ * q * g) * a⁻¹) * a := by rw [this]
      _ = g⁻¹ * q * g⁻¹⁻¹ := by group

theorem actS_le (hSN : S ≤ Subgroup.normalizer (Q : Set A)) : actS Q S hSN ≤ Q :=
  fun _ hy => hy.1

theorem inf_le_actS (hSN : S ≤ Subgroup.normalizer (Q : Set A)) : S ⊓ Q ≤ actS Q S hSN :=
  fun y hy => ⟨(Subgroup.mem_inf.mp hy).2, y, (Subgroup.mem_inf.mp hy).1, fun _ _ => rfl⟩

theorem isPGroup_actS (hSN : S ≤ Subgroup.normalizer (Q : Set A)) (hZ : CenterFree Q)
    (hS2 : IsPGroup 2 ↥S) : IsPGroup 2 ↥(actS Q S hSN) := by
  intro y
  obtain ⟨hyQ, g, hg, hgy⟩ := y.2
  obtain ⟨n, hn⟩ := hS2 ⟨g, hg⟩
  have hgn : g ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hpow : ∀ k : ℕ, ∀ q ∈ Q, (y : A) ^ k * q * ((y : A) ^ k)⁻¹ = g ^ k * q * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro q _; simp
    | succ k ih =>
      intro q hq
      have hgq : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hSN hg) q).mp hq
      calc (y : A) ^ (k + 1) * q * ((y : A) ^ (k + 1))⁻¹ =
          (y : A) ^ k * ((y : A) * q * (y : A)⁻¹) * ((y : A) ^ k)⁻¹ := by group
        _ = g ^ k * (g * q * g⁻¹) * (g ^ k)⁻¹ := by rw [hgy q hq, ih _ hgq]
        _ = g ^ (k + 1) * q * (g ^ (k + 1))⁻¹ := by group
  refine ⟨n, Subtype.ext ?_⟩
  have hc := hZ _ (pow_mem hyQ _) fun q hq => by
    have := hpow (2 ^ n) q hq
    rw [hgn] at this
    simp only [one_mul, inv_one, mul_one] at this
    calc (y : A) ^ 2 ^ n * q = (y : A) ^ 2 ^ n * q * ((y : A) ^ 2 ^ n)⁻¹ * (y : A) ^ 2 ^ n := by
          group
      _ = q * (y : A) ^ 2 ^ n := by rw [this]
  simpa using hc

end ActS

section NConj

variable (Q : Subgroup A)

@[expose] noncomputable def nConj : ↥(Subgroup.normalizer (Q : Set A)) →* MulAut ↥Q :=
  (MulAut.congr (Q.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := Q)))).toMonoidHom.comp
    MulAut.conjNormal

theorem coe_nConj (n : ↥(Subgroup.normalizer (Q : Set A))) (q : ↥Q) :
    ((nConj Q n q : ↥Q) : A) = n * q * n⁻¹ := rfl

variable {Q}

theorem innerOn_of_odd [Finite A] {D : Subgroup A} (hDN : D ≤ Subgroup.normalizer (Q : Set A))
    (hD : Odd (Nat.card D))
    (hinn : ∀ α : MulAut ↥Q, Odd (orderOf α) → ∃ q : ↥Q, α = MulAut.conj q) : InnerOn Q D := by
  intro d hd
  have h1 : orderOf (nConj Q ⟨d, hDN hd⟩) ∣ orderOf d := by
    have := orderOf_map_dvd (nConj Q) ⟨d, hDN hd⟩
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨q, hq⟩ := hinn (nConj Q ⟨d, hDN hd⟩)
    (Odd.of_dvd_nat hD (h1.trans (Subgroup.orderOf_dvd_natCard D hd)))
  refine ⟨q, q.2, fun x hx => ?_⟩
  have := congrArg (fun α : MulAut ↥Q => ((α ⟨x, hx⟩ : ↥Q) : A)) hq
  simpa [coe_nConj, MulAut.conj_apply] using this

end NConj

section Perm

variable {Q S D : Subgroup A} (hinn : InnerOn Q D) (hZ : CenterFree Q)
  (hDN : D ≤ Subgroup.normalizer (Q : Set A))

theorem conj_mem_img_mul (hSN : S ≤ Subgroup.normalizer (Q : Set A)) (hS2 : IsPGroup 2 ↥S)
    (hDS : (D : Set A) * (S : Set A) = (S : Set A) * (D : Set A))
    (hT : ∀ X : Subgroup A, X ≤ Q → IsPGroup 2 ↥X → S ⊓ Q ≤ X → X = S ⊓ Q)
    {g : A} (hg : g ∈ S) {x : A} (hx : x ∈ img hinn hZ hDN) :
    ∃ x' ∈ img hinn hZ hDN, ∃ t ∈ S ⊓ Q, g * x * g⁻¹ = x' * t := by
  obtain ⟨d, rfl⟩ := hx
  have hgd : g * (d : A) ∈ (S : Set A) * (D : Set A) := Set.mul_mem_mul hg d.2
  rw [← hDS] at hgd
  obtain ⟨d', hd', g', hg', he⟩ := hgd
  have he' : d' * g' = g * (d : A) := he
  set x' := rep hinn ⟨d', hd'⟩
  have hx'Q : x' ∈ Q := rep_mem hinn _
  have hxQ : repHom hinn hZ hDN d ∈ Q := rep_mem hinn d
  have hgxQ : g * repHom hinn hZ hDN d * g⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hSN hg) _).mp hxQ
  refine ⟨x', ⟨⟨d', hd'⟩, rfl⟩, x'⁻¹ * (g * repHom hinn hZ hDN d * g⁻¹), ?_, by group⟩
  have hy : x'⁻¹ * (g * repHom hinn hZ hDN d * g⁻¹) ∈ actS Q S hSN := by
    refine ⟨mul_mem (inv_mem hx'Q) hgxQ, g' * g⁻¹, mul_mem hg' (inv_mem hg), fun q hq => ?_⟩
    have hq1 : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hSN (inv_mem hg)) q).mp hq
      simpa using this
    have hq2 : g' * g⁻¹ * q * (g' * g⁻¹)⁻¹ ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hSN (mul_mem hg' (inv_mem hg))) q).mp hq
      simpa using this
    have h1 := rep_spec hinn d hq1
    have hr : rep hinn d = repHom hinn hZ hDN d := rfl
    rw [hr] at h1
    have h2 := rep_spec hinn ⟨d', hd'⟩ hq2
    have h3 : (d : A) = g⁻¹ * d' * g' := by
      calc (d : A) = g⁻¹ * (g * (d : A)) := by group
        _ = g⁻¹ * (d' * g') := by rw [he']
        _ = g⁻¹ * d' * g' := by group
    calc x'⁻¹ * (g * repHom hinn hZ hDN d * g⁻¹) * q *
          (x'⁻¹ * (g * repHom hinn hZ hDN d * g⁻¹))⁻¹
        = x'⁻¹ * (g * (repHom hinn hZ hDN d * (g⁻¹ * q * g) * (repHom hinn hZ hDN d)⁻¹) * g⁻¹) *
            x' := by group
      _ = x'⁻¹ * (g * ((d : A) * (g⁻¹ * q * g) * (d : A)⁻¹) * g⁻¹) * x' := by
          rw [← h1]
      _ = x'⁻¹ * ((d' : A) * (g' * g⁻¹ * q * (g' * g⁻¹)⁻¹) * (d' : A)⁻¹) * x' := by
          rw [h3]; group
      _ = x'⁻¹ * (x' * (g' * g⁻¹ * q * (g' * g⁻¹)⁻¹) * x'⁻¹) * x' := by rw [h2]
      _ = g' * g⁻¹ * q * (g' * g⁻¹)⁻¹ := by group
  have hTeq := hT _ (actS_le hSN) (isPGroup_actS hSN hZ hS2) (inf_le_actS hSN)
  rw [← hTeq]
  exact hy

end Perm

section Two

variable {Q₁ Q₂ : Subgroup A} (h : CommPair Q₁ Q₂)
include h

theorem CommPair.centerFree_sup (h₁ : CenterFree Q₁) (h₂ : CenterFree Q₂) :
    CenterFree (Q₁ ⊔ Q₂) := by
  intro z hz hc
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hz
  have hca : ∀ x ∈ Q₁, a * x = x * a := by
    intro x hx
    have h1 := hc x (Subgroup.mem_sup_left hx)
    have h2 : b * x = x * b := (h.comm x hx b hb).symm
    calc a * x = a * b * x * b⁻¹ := by rw [mul_assoc a b x, h2]; group
      _ = x * (a * b) * b⁻¹ := by rw [h1]
      _ = x * a := by group
  have hcb : ∀ x ∈ Q₂, b * x = x * b := by
    intro x hx
    have h1 := hc x (Subgroup.mem_sup_right hx)
    have h2 : a * x = x * a := h.comm a ha x hx
    calc b * x = a⁻¹ * (a * b * x) := by group
      _ = a⁻¹ * (x * (a * b)) := by rw [h1]
      _ = a⁻¹ * (x * a) * b := by group
      _ = x * b := by rw [← h2]; group
  rw [h₁ a ha hca, h₂ b hb hcb, one_mul]

omit h in
theorem CommPair.conj_eq_or_eq (h : CommPair Q₁ Q₂) [IsSimpleGroup ↥Q₁] [IsSimpleGroup ↥Q₂]
    (hZ₁ : CenterFree Q₁) {g : A} (hg : g ∈ Subgroup.normalizer ((Q₁ ⊔ Q₂ : Subgroup A) : Set A))
    {Q' : Subgroup A} (hQ' : Q' = Q₁ ∨ Q' = Q₂) :
    Q'.map (MulAut.conj g).toMonoidHom = Q₁ ∨ Q'.map (MulAut.conj g).toMonoidHom = Q₂ := by
  have hsimple : IsSimpleGroup ↥(Q'.map (MulAut.conj g).toMonoidHom) := by
    have e : ↥Q' ≃* ↥(Q'.map (MulAut.conj g).toMonoidHom) :=
      Q'.equivMapOfInjective _ (MulAut.conj g).injective
    rcases hQ' with rfl | rfl
    · exact e.symm.isSimpleGroup
    · exact e.symm.isSimpleGroup
  have hQ'le : Q' ≤ Q₁ ⊔ Q₂ := by rcases hQ' with rfl | rfl; exact le_sup_left; exact le_sup_right
  have hQ'n : Q₁ ⊔ Q₂ ≤ Subgroup.normalizer (Q' : Set A) := by
    rcases hQ' with rfl | rfl
    · rw [sup_le_iff]
      refine ⟨Subgroup.le_normalizer, fun b hb => ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        rw [← h.comm a ha b hb, mul_inv_cancel_right]
        exact ha
      · intro ha
        have := h.comm (b * a * b⁻¹) ha b hb
        have e : a = b * a * b⁻¹ := by
          calc a = b⁻¹ * (b * a * b⁻¹ * b) := by group
            _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [this]
            _ = b * a * b⁻¹ := by group
        rw [e]
        exact ha
    · rw [sup_le_iff]
      refine ⟨fun b hb => ?_, Subgroup.le_normalizer⟩
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        rw [h.comm b hb a ha, mul_inv_cancel_right]
        exact ha
      · intro ha
        have := h.comm b hb (b * a * b⁻¹) ha
        have e : a = b * a * b⁻¹ := by
          calc a = b⁻¹ * (b * a * b⁻¹ * b) := by group
            _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [← this]
            _ = b * a * b⁻¹ := by group
        rw [e]
        exact ha
  apply h.eq_or_eq_of_simple hZ₁
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hQ'le hx)
  · intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hgq : g⁻¹ * q * g ∈ Q₁ ⊔ Q₂ := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) q).mp hq
      simpa using this
    have hn := Subgroup.mem_normalizer_iff.mp (hQ'n hgq)
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(g⁻¹ * q * g) * x * (g⁻¹ * q * g)⁻¹, (hn x).mp hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨x, hx, hxe⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxe
      refine ⟨(g⁻¹ * q * g)⁻¹ * x * (g⁻¹ * q * g), ?_, ?_⟩
      · have := (hn ((g⁻¹ * q * g)⁻¹ * x * (g⁻¹ * q * g))).mpr (by
          rw [show g⁻¹ * q * g * ((g⁻¹ * q * g)⁻¹ * x * (g⁻¹ * q * g)) * (g⁻¹ * q * g)⁻¹ = x by
            group]
          exact hx)
        exact this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hy : y = q⁻¹ * (q * y * q⁻¹) * q := by group
        rw [hy, ← hxe]
        group

omit h in
theorem CommPair.mem_normalizer_of_odd (h : CommPair Q₁ Q₂) [IsSimpleGroup ↥Q₁]
    [IsSimpleGroup ↥Q₂] (hZ₁ : CenterFree Q₁) {g : A}
    (hg : g ∈ Subgroup.normalizer ((Q₁ ⊔ Q₂ : Subgroup A) : Set A)) (hodd : Odd (orderOf g)) :
    g ∈ Subgroup.normalizer (Q₁ : Set A) := by
  have hmap : ∀ {Q' Q'' : Subgroup A}, Q'.map (MulAut.conj g).toMonoidHom = Q'' →
      ∀ x, x ∈ Q' ↔ g * x * g⁻¹ ∈ Q'' := by
    intro Q' Q'' he x
    rw [← he]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hye⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hye
      have : y = x := by simpa using hye
      rw [← this]
      exact hy
  rcases h.conj_eq_or_eq hZ₁ hg (Or.inl rfl) with h1 | h1
  · exact Subgroup.mem_normalizer_iff.mpr (hmap h1)
  · exfalso
    have e1 := hmap h1
    have hne : Q₁ ≠ Q₂ := by
      intro he
      have : Q₁ = ⊥ := by rw [← h.inf_eq, ← he, inf_idem]
      exact (Subgroup.nontrivial_iff_ne_bot Q₁).mp inferInstance this
    rcases h.conj_eq_or_eq hZ₁ hg (Or.inr rfl) with h2 | h2
    · have e2 := hmap h2
      have hpow : ∀ n : ℕ, ∀ x, x ∈ Q₁ ↔ g ^ (2 * n) * x * (g ^ (2 * n))⁻¹ ∈ Q₁ := by
        intro n
        induction n with
        | zero => intro x; simp
        | succ n ih =>
          intro x
          rw [ih x, e1, e2]
          rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pow_succ, pow_succ]
          constructor <;> intro hx <;> convert hx using 1 <;> group
      obtain ⟨n, hn⟩ := hodd
      apply hne
      ext x
      rw [hpow n x, e1, show g * (g ^ (2 * n) * x * (g ^ (2 * n))⁻¹) * g⁻¹ =
        g ^ orderOf g * x * (g ^ orderOf g)⁻¹ by rw [hn, pow_succ']; group, pow_orderOf_eq_one]
      simp
    · apply hne
      ext x
      rw [hmap h1 x, hmap h2 x]

theorem CommPair.innerOn_sup {D : Subgroup A} (h₁ : InnerOn Q₁ D) (h₂ : InnerOn Q₂ D) :
    InnerOn (Q₁ ⊔ Q₂) D := by
  intro d hd
  obtain ⟨q₁, hq₁, e₁⟩ := h₁ d hd
  obtain ⟨q₂, hq₂, e₂⟩ := h₂ d hd
  refine ⟨q₁ * q₂, mul_mem (Subgroup.mem_sup_left hq₁) (Subgroup.mem_sup_right hq₂),
    fun x hx => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
  have hc1 : a * q₂ = q₂ * a := h.comm a ha q₂ hq₂
  have hw : q₁ * (q₂ * b * q₂⁻¹) * q₁⁻¹ = q₂ * b * q₂⁻¹ := by
    rw [h.comm q₁ hq₁ _ (mul_mem (mul_mem hq₂ hb) (inv_mem hq₂)), mul_inv_cancel_right]
  calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
    _ = (q₁ * a * q₁⁻¹) * (q₂ * b * q₂⁻¹) := by rw [e₁ a ha, e₂ b hb]
    _ = (q₁ * a * q₁⁻¹) * (q₁ * (q₂ * b * q₂⁻¹) * q₁⁻¹) := by rw [hw]
    _ = q₁ * (a * q₂) * b * (q₁ * q₂)⁻¹ := by group
    _ = q₁ * (q₂ * a) * b * (q₁ * q₂)⁻¹ := by rw [hc1]
    _ = q₁ * q₂ * (a * b) * (q₁ * q₂)⁻¹ := by group

end Two

end CFSG.Quasithin.H13.NQCat.C2
