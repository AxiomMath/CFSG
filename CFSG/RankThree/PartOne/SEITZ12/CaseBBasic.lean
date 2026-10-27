module

public import CFSG.RankThree.PartOne.SEITZ12.Defs
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open Subgroup

variable {G : Type*} [Group G]

theorem phi4B_inv_eq {t : G} (ht2 : t * t = 1) : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2

theorem phi4B_tau_tau {t : G} (ht2 : t * t = 1) (x : G) : t * (t * x * t) * t = x := by
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by simp only [mul_assoc]
    _ = x := by rw [ht2, one_mul, mul_one]

theorem phi4B_tau_mul {t : G} (ht2 : t * t = 1) (x y : G) :
    (t * x * t) * (t * y * t) = t * (x * y) * t := by
  calc (t * x * t) * (t * y * t) = t * x * (t * t) * y * t := by simp only [mul_assoc]
    _ = t * (x * y) * t := by rw [ht2, mul_one]; simp only [mul_assoc]

theorem phi4B_mem_conj {t : G} (ht2 : t * t = 1) {H : Subgroup G} {x : G} :
    x ∈ conjSub H t ↔ t * x * t ∈ H := by
  rw [mem_conjSub, phi4B_inv_eq ht2]

theorem phi4B_tau_mem {t : G} (ht2 : t * t = 1) {H : Subgroup G} {x : G} (hx : x ∈ H) :
    t * x * t ∈ conjSub H t := by
  rw [phi4B_mem_conj ht2, phi4B_tau_tau ht2]
  exact hx

theorem phi4B_tau_mem' {t : G} (ht2 : t * t = 1) {H : Subgroup G} {x : G}
    (hx : x ∈ conjSub H t) : t * x * t ∈ H := (phi4B_mem_conj ht2).1 hx

theorem phi4B_pow_four (x : G) : x ^ 4 = (x * x) * (x * x) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]

theorem phi4B_comm_of_sq {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * (x * y) = 1) : x * y = y * x := by
  have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  calc x * y = (x * y)⁻¹ := h3.symm
    _ = y * x := by rw [mul_inv_rev, h1, h2]

theorem phi4B_mem_sup_iff {H K : Subgroup G} (h : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  constructor
  · intro hx
    let L : Subgroup G :=
      { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, x = a * b}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
            _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
            _ = a * a' * (b * b') := by simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
          rw [mul_inv_rev]
          exact (h a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)).symm }
    have hle : H ⊔ K ≤ L :=
      sup_le (fun a ha => ⟨a, ha, 1, one_mem _, (mul_one a).symm⟩)
        (fun b hb => ⟨1, one_mem _, b, hb, (one_mul b).symm⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem phi4B_suz_conj {q : ℕ} {S Z : Subgroup G} (h : SuzukiTwo q S Z) (g : G) :
    SuzukiTwo q (conjSub S g) (conjSub Z g) where
  Z_le := Subgroup.map_mono h.Z_le
  card_S := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h.card_S
  card_Z := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h.card_Z
  sq_mem := by
    intro s hs
    rw [mem_conjSub] at hs ⊢
    have e : g⁻¹ * (s * s) * g = (g⁻¹ * s * g) * (g⁻¹ * s * g) := by group
    rw [e]
    exact h.sq_mem _ hs
  exists_sq := by
    intro z hz hz1
    rw [mem_conjSub] at hz
    have hz1' : g⁻¹ * z * g ≠ 1 := by
      intro e
      apply hz1
      have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [this, e]
      group
    obtain ⟨s, hs, hss⟩ := h.exists_sq _ hz hz1'
    refine ⟨g * s * g⁻¹, ?_, ?_⟩
    · rw [mem_conjSub]
      have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
      rw [e]
      exact hs
    · have e : g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      rw [e, hss]
      group
  eq_one_of_sq := by
    intro s hs hss
    rw [mem_conjSub] at hs ⊢
    apply h.eq_one_of_sq _ hs
    have e : g⁻¹ * s * g * (g⁻¹ * s * g) = g⁻¹ * (s * s) * g := by group
    rw [e, hss]
    group
  sq_Z := by
    intro z hz
    rw [mem_conjSub] at hz
    have h1 := h.sq_Z _ hz
    have e : z * z = g * ((g⁻¹ * z * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
    rw [e, h1]
    group
  central := by
    intro z hz s hs
    rw [mem_conjSub] at hz hs
    have h1 := h.central _ hz _ hs
    have e1 : z * s = g * ((g⁻¹ * z * g) * (g⁻¹ * s * g)) * g⁻¹ := by group
    have e2 : s * z = g * ((g⁻¹ * s * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
    rw [e1, e2, h1]

structure phi4B_Core (X₂ S₂ Z₂ : Subgroup G) (t : G) (q : ℕ) : Prop where
  q_ge : 8 ≤ q
  t_sq : t * t = 1
  comm : ∀ x ∈ X₂, ∀ y ∈ conjSub X₂ t, x * y = y * x
  inf : X₂ ⊓ conjSub X₂ t = ⊥
  S₂_le : S₂ ≤ X₂
  suz : SuzukiTwo q S₂ Z₂

@[expose] def phi4B_B0 (S₂ : Subgroup G) (t : G) : Subgroup G := conjSub S₂ t ⊔ S₂

@[expose] def phi4B_Om (Z₂ : Subgroup G) (t : G) : Subgroup G := conjSub Z₂ t ⊔ Z₂

namespace phi4B_Core

variable {X₂ S₂ Z₂ : Subgroup G} {t : G} {q : ℕ}

theorem S₁_le (h : phi4B_Core X₂ S₂ Z₂ t q) : conjSub S₂ t ≤ conjSub X₂ t :=
  Subgroup.map_mono h.S₂_le

theorem Z₁_le (h : phi4B_Core X₂ S₂ Z₂ t q) : conjSub Z₂ t ≤ conjSub S₂ t :=
  Subgroup.map_mono h.suz.Z_le

theorem suz₁ (h : phi4B_Core X₂ S₂ Z₂ t q) :
    SuzukiTwo q (conjSub S₂ t) (conjSub Z₂ t) := phi4B_suz_conj h.suz t

theorem comm_S (h : phi4B_Core X₂ S₂ Z₂ t q) {a b : G} (ha : a ∈ conjSub S₂ t) (hb : b ∈ S₂) :
    a * b = b * a := (h.comm b (h.S₂_le hb) a (h.S₁_le ha)).symm

theorem comm_Z (h : phi4B_Core X₂ S₂ Z₂ t q) {a b : G} (ha : a ∈ conjSub Z₂ t) (hb : b ∈ Z₂) :
    a * b = b * a := h.comm_S (h.Z₁_le ha) (h.suz.Z_le hb)

theorem eq_one_of_mul (h : phi4B_Core X₂ S₂ Z₂ t q) {a b : G} (ha : a ∈ conjSub X₂ t)
    (hb : b ∈ X₂) (hab : a * b = 1) : a = 1 ∧ b = 1 := by
  have ha' : a = b⁻¹ := eq_inv_of_mul_eq_one_left hab
  have hmem : a ∈ X₂ ⊓ conjSub X₂ t :=
    Subgroup.mem_inf.2 ⟨by rw [ha']; exact inv_mem hb, ha⟩
  rw [h.inf] at hmem
  have h1 : a = 1 := (Subgroup.mem_bot).1 hmem
  refine ⟨h1, ?_⟩
  rw [h1, one_mul] at hab
  exact hab

theorem mul_inj (h : phi4B_Core X₂ S₂ Z₂ t q) {a a' b b' : G} (ha : a ∈ conjSub X₂ t)
    (ha' : a' ∈ conjSub X₂ t) (hb : b ∈ X₂) (hb' : b' ∈ X₂) (hab : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have e : a'⁻¹ * a * (b * b'⁻¹) = 1 := by
    calc a'⁻¹ * a * (b * b'⁻¹) = a'⁻¹ * (a * b) * b'⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hab]; group
  obtain ⟨e1, e2⟩ := h.eq_one_of_mul (a := a'⁻¹ * a) (b := b * b'⁻¹)
    (mul_mem (inv_mem ha') ha) (mul_mem hb (inv_mem hb')) e
  constructor
  · calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [e1, mul_one]
  · calc b = (b * b'⁻¹) * b' := by group
      _ = b' := by rw [e2, one_mul]

theorem mem_B0 (h : phi4B_Core X₂ S₂ Z₂ t q) {x : G} :
    x ∈ phi4B_B0 S₂ t ↔ ∃ a ∈ conjSub S₂ t, ∃ b ∈ S₂, x = a * b :=
  phi4B_mem_sup_iff (fun _ ha _ hb => h.comm_S ha hb)

theorem mem_Om (h : phi4B_Core X₂ S₂ Z₂ t q) {x : G} :
    x ∈ phi4B_Om Z₂ t ↔ ∃ a ∈ conjSub Z₂ t, ∃ b ∈ Z₂, x = a * b :=
  phi4B_mem_sup_iff (fun _ ha _ hb => h.comm_Z ha hb)

theorem Om_le_B0 (h : phi4B_Core X₂ S₂ Z₂ t q) : phi4B_Om Z₂ t ≤ phi4B_B0 S₂ t :=
  sup_le_sup h.Z₁_le h.suz.Z_le

theorem S₁_le_B0 (_h : phi4B_Core X₂ S₂ Z₂ t q) : conjSub S₂ t ≤ phi4B_B0 S₂ t := le_sup_left

theorem S₂_le_B0 (_h : phi4B_Core X₂ S₂ Z₂ t q) : S₂ ≤ phi4B_B0 S₂ t := le_sup_right

theorem tau_S₁ (h : phi4B_Core X₂ S₂ Z₂ t q) {a : G} (ha : a ∈ conjSub S₂ t) :
    t * a * t ∈ S₂ := phi4B_tau_mem' h.t_sq ha

theorem tau_S₂ (h : phi4B_Core X₂ S₂ Z₂ t q) {b : G} (hb : b ∈ S₂) :
    t * b * t ∈ conjSub S₂ t := phi4B_tau_mem h.t_sq hb

theorem tau_B0 (h : phi4B_Core X₂ S₂ Z₂ t q) {x : G} (hx : x ∈ phi4B_B0 S₂ t) :
    t * x * t ∈ phi4B_B0 S₂ t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_B0).1 hx
  rw [← phi4B_tau_mul h.t_sq]
  exact mul_mem (h.S₂_le_B0 (h.tau_S₁ ha)) (h.S₁_le_B0 (h.tau_S₂ hb))

theorem Z₂_ne (h : phi4B_Core X₂ S₂ Z₂ t q) : ∃ z ∈ Z₂, z ≠ 1 := by
  by_contra hcon
  have hbot : Z₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun z hz => by
    by_contra hz1
    exact hcon ⟨z, hz, hz1⟩
  have hc := h.suz.card_Z
  rw [hbot, Subgroup.card_bot] at hc
  have := h.q_ge
  omega

theorem tau_ne_one (h : phi4B_Core X₂ S₂ Z₂ t q) {z : G} (hz : z ≠ 1) : t * z * t ≠ 1 := by
  intro e
  apply hz
  calc z = t * (t * z * t) * t := (phi4B_tau_tau h.t_sq z).symm
    _ = 1 := by rw [e, mul_one]; exact h.t_sq

theorem t_ne_one (h : phi4B_Core X₂ S₂ Z₂ t q) : t ≠ 1 := by
  intro ht
  obtain ⟨z, hz, hz1⟩ := h.Z₂_ne
  have hzX : z ∈ X₂ := h.S₂_le (h.suz.Z_le hz)
  have hzX1 : z ∈ conjSub X₂ t := by
    rw [phi4B_mem_conj h.t_sq, ht]
    simpa using hzX
  have hmem : z ∈ X₂ ⊓ conjSub X₂ t := Subgroup.mem_inf.2 ⟨hzX, hzX1⟩
  rw [h.inf] at hmem
  exact hz1 ((Subgroup.mem_bot).1 hmem)

theorem sq_mul (h : phi4B_Core X₂ S₂ Z₂ t q) {a b : G} (ha : a ∈ conjSub S₂ t) (hb : b ∈ S₂) :
    (a * b) * (a * b) = (a * a) * (b * b) := by
  calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b) * b := by rw [← h.comm_S ha hb]
    _ = (a * a) * (b * b) := by simp only [mul_assoc]

theorem inv_B0 (h : phi4B_Core X₂ S₂ Z₂ t q) {a b : G} (ha : a ∈ conjSub S₂ t) (hb : b ∈ S₂)
    (hab : (a * b) * (a * b) = 1) : a ∈ conjSub Z₂ t ∧ b ∈ Z₂ := by
  rw [h.sq_mul ha hb] at hab
  obtain ⟨h1, h2⟩ := h.eq_one_of_mul (a := a * a) (b := b * b)
    (h.S₁_le (mul_mem ha ha)) (h.S₂_le (mul_mem hb hb)) hab
  exact ⟨h.suz₁.eq_one_of_sq a ha h1, h.suz.eq_one_of_sq b hb h2⟩

theorem Om_sq (h : phi4B_Core X₂ S₂ Z₂ t q) {x : G} (hx : x ∈ phi4B_Om Z₂ t) : x * x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_Om.1 hx
  have h1 := h.suz₁.sq_Z a ha
  have h2 := h.suz.sq_Z b hb
  calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b) * b := by rw [← h.comm_Z ha hb]
    _ = (a * a) * (b * b) := by simp only [mul_assoc]
    _ = 1 := by rw [h1, h2, one_mul]

theorem B0_sq_mem_Om (h : phi4B_Core X₂ S₂ Z₂ t q) {x : G} (hx : x ∈ phi4B_B0 S₂ t) :
    x * x ∈ phi4B_Om Z₂ t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_B0.1 hx
  rw [h.sq_mul ha hb]
  exact mul_mem (mem_sup_left (h.suz₁.sq_mem a ha)) (mem_sup_right (h.suz.sq_mem b hb))

theorem inv_mem_Om (h : phi4B_Core X₂ S₂ Z₂ t q) {x : G} (hx : x ∈ phi4B_B0 S₂ t)
    (hx2 : x * x = 1) : x ∈ phi4B_Om Z₂ t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_B0.1 hx
  obtain ⟨h1, h2⟩ := h.inv_B0 ha hb hx2
  exact mul_mem (mem_sup_left h1) (mem_sup_right h2)

theorem inv_B0t (h : phi4B_Core X₂ S₂ Z₂ t q) {b : G} (hb : b ∈ phi4B_B0 S₂ t)
    (hu : (b * t) * (b * t) = 1) : ∃ s ∈ conjSub S₂ t, b * t = s * t * s⁻¹ := by
  obtain ⟨a, ha, c, hc, rfl⟩ := h.mem_B0.1 hb
  have ha' := h.tau_S₁ ha
  have hc' := h.tau_S₂ hc
  have e : (a * c * t) * (a * c * t) = (a * (t * c * t)) * (c * (t * a * t)) := by
    calc (a * c * t) * (a * c * t) = a * c * ((t * a * t) * (t * c * t)) := by
          rw [phi4B_tau_mul h.t_sq]; simp only [mul_assoc]
      _ = a * c * ((t * c * t) * (t * a * t)) := by rw [h.comm_S hc' ha']
      _ = a * (c * (t * c * t)) * (t * a * t) := by simp only [mul_assoc]
      _ = a * ((t * c * t) * c) * (t * a * t) := by rw [h.comm_S hc' hc]
      _ = (a * (t * c * t)) * (c * (t * a * t)) := by simp only [mul_assoc]
  obtain ⟨h1, _⟩ := h.eq_one_of_mul (a := a * (t * c * t)) (b := c * (t * a * t))
    (h.S₁_le (mul_mem ha hc')) (h.S₂_le (mul_mem hc ha')) (e.symm.trans hu)
  refine ⟨a, ha, ?_⟩
  have hc2 : t * c * t = a⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hc3 : c = t * a⁻¹ * t := by
    calc c = t * (t * c * t) * t := (phi4B_tau_tau h.t_sq c).symm
      _ = t * a⁻¹ * t := by rw [hc2]
  rw [hc3]
  calc a * (t * a⁻¹ * t) * t = a * t * a⁻¹ * (t * t) := by simp only [mul_assoc]
    _ = a * t * a⁻¹ := by rw [h.t_sq, mul_one]

theorem cent_B0 (h : phi4B_Core X₂ S₂ Z₂ t q) {b : G} (hb : b ∈ phi4B_B0 S₂ t)
    (hb2 : b * b = 1) (hbt : t * b * t = b) : ∃ z ∈ conjSub Z₂ t, b = z * (t * z * t) := by
  obtain ⟨a, ha, c, hc, rfl⟩ := h.mem_B0.1 hb
  obtain ⟨hZa, _⟩ := h.inv_B0 ha hc hb2
  have ha' := h.tau_S₁ ha
  have hc' := h.tau_S₂ hc
  have e : (t * c * t) * (t * a * t) = a * c := by
    rw [h.comm_S hc' ha', phi4B_tau_mul h.t_sq]
    exact hbt
  obtain ⟨_, h2⟩ := h.mul_inj (h.S₁_le hc') (h.S₁_le ha) (h.S₂_le ha') (h.S₂_le hc) e
  exact ⟨a, hZa, by rw [h2]⟩

end phi4B_Core

@[expose] def phi4B_S {X₂ S₂ Z₂ : Subgroup G} {t : G} {q : ℕ} (h : phi4B_Core X₂ S₂ Z₂ t q) :
    Subgroup G where
  carrier := {x | x ∈ phi4B_B0 S₂ t ∨ ∃ b ∈ phi4B_B0 S₂ t, x = b * t}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro x y (hx | ⟨b, hb, rfl⟩) (hy | ⟨c, hc, rfl⟩)
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr ⟨x * c, mul_mem hx hc, by rw [mul_assoc]⟩
    · refine Or.inr ⟨b * (t * y * t), mul_mem hb (h.tau_B0 hy), ?_⟩
      calc b * t * y = b * t * y * (t * t) := by rw [h.t_sq, mul_one]
        _ = b * (t * y * t) * t := by simp only [mul_assoc]
    · refine Or.inl ?_
      have e : b * t * (c * t) = b * (t * c * t) := by simp only [mul_assoc]
      rw [e]
      exact mul_mem hb (h.tau_B0 hc)
  inv_mem' := by
    rintro x (hx | ⟨b, hb, rfl⟩)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ⟨t * b⁻¹ * t, h.tau_B0 (inv_mem hb), ?_⟩
      rw [mul_inv_rev, phi4B_inv_eq h.t_sq]
      calc t * b⁻¹ = t * b⁻¹ * (t * t) := by rw [h.t_sq, mul_one]
        _ = t * b⁻¹ * t * t := by simp only [mul_assoc]

namespace phi4B_Core

variable {X₂ S₂ Z₂ : Subgroup G} {t : G} {q : ℕ}

theorem B0_le_S (h : phi4B_Core X₂ S₂ Z₂ t q) : phi4B_B0 S₂ t ≤ phi4B_S h := fun _ hx => Or.inl hx

theorem t_mem_S (h : phi4B_Core X₂ S₂ Z₂ t q) : t ∈ phi4B_S h :=
  Or.inr ⟨1, one_mem _, (one_mul t).symm⟩

theorem S_le (h : phi4B_Core X₂ S₂ Z₂ t q) {T : Subgroup G} (hB : phi4B_B0 S₂ t ≤ T)
    (ht : t ∈ T) : phi4B_S h ≤ T := by
  rintro x (hx | ⟨b, hb, rfl⟩)
  · exact hB hx
  · exact mul_mem (hB hb) ht

theorem B0_pow4 (h : phi4B_Core X₂ S₂ Z₂ t q) {x : G} (hx : x ∈ phi4B_B0 S₂ t) : x ^ 4 = 1 := by
  have h1 := h.Om_sq (h.B0_sq_mem_Om hx)
  rw [phi4B_pow_four]
  exact h1

theorem S_pow8 (h : phi4B_Core X₂ S₂ Z₂ t q) {x : G} (hx : x ∈ phi4B_S h) : x ^ 8 = 1 := by
  rcases hx with hx | ⟨b, hb, rfl⟩
  · calc x ^ 8 = (x ^ 4) ^ 2 := pow_mul x 4 2
      _ = 1 := by rw [h.B0_pow4 hx, one_pow]
  · have hm : (b * t) * (b * t) ∈ phi4B_B0 S₂ t := by
      have e : (b * t) * (b * t) = b * (t * b * t) := by simp only [mul_assoc]
      rw [e]
      exact mul_mem hb (h.tau_B0 hb)
    calc (b * t) ^ 8 = (((b * t) * (b * t)) ^ 4) := by rw [← sq, ← pow_mul]
      _ = 1 := h.B0_pow4 hm

theorem isPGroup_S (h : phi4B_Core X₂ S₂ Z₂ t q) : IsPGroup 2 (phi4B_S h) := by
  intro x
  refine ⟨3, Subtype.ext ?_⟩
  have := h.S_pow8 x.2
  simpa using this

end phi4B_Core

end CFSG.RankThree.PartOne.SEITZ12
