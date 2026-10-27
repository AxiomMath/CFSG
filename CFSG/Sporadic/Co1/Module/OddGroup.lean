module

public import CFSG.Sporadic.Co1.Module.OddCount
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Interval.Set.Nat

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open MulAction

structure OddCert (G Ω : Type*) [Group G] [MulAction G Ω] where
  ω₀ : Ω
  ρ : G
  t₁ : G
  s : Fin 3 → G
  ρ_sq : ρ * ρ = 1
  ρ_mem : ρ ∈ stabilizer G ω₀
  s_mem : ∀ k, s k ∈ stabilizer G ω₀
  s_conj : ∀ k, IsConj ρ (s k)
  S_cover : ∀ t, t ∈ stabilizer G ω₀ → IsConj ρ t →
    ∃ n ∈ stabilizer G ω₀, t = n * t₁ * n⁻¹ ∨ t = n * ρ * n⁻¹
  scan₁ : ∀ t, t ∈ stabilizer G ω₀ → IsConj ρ t → t ≠ t₁ → ¬ Odd (orderOf (t₁ * t))
  partner : ∀ t, t ∈ stabilizer G ω₀ → IsConj ρ t → t ≠ ρ → Odd (orderOf (ρ * t)) →
    ∃ k, ∃ c ∈ stabilizer G ω₀ ⊓ Subgroup.centralizer {ρ}, t = c * s k * c⁻¹
  o : Fin 3 → ℕ
  d : Fin 3 → ℕ
  o_spec : ∀ k, orderOf (ρ * s k) = o k
  d_spec : ∀ k, ({ω : Ω | ρ • ω = ω} ∩ {ω | s k • ω = ω}).ncard = d k
  o_odd : ∀ k, Odd (o k)
  o_gt : ∀ k, 1 < o k
  sep : ∀ j k, o j = o k → d j = d k → j = k
  Zn : Fin 3 → ℕ
  z : Fin 3 → ℕ → G
  z_inj : ∀ k, ∀ i < Zn k, ∀ j < Zn k, z k i = z k j → i = j
  z_mem : ∀ k, ∀ i < Zn k,
    z k i ∈ stabilizer G ω₀ ⊓ Subgroup.centralizer {ρ} ⊓ Subgroup.centralizer {s k}
  Z_le : ∀ k, Nat.card ↥(stabilizer G ω₀ ⊓ Subgroup.centralizer {ρ} ⊓
    Subgroup.centralizer {s k}) ≤ Zn k
  faith : ∀ k : Fin 3, k ≠ 0 → ∀ i < Zn k,
    (∀ v : Ω, ρ • v = v → s k • v = v → z k i • v = v) → z k i = 1

section Cert

variable {G Ω : Type*} [Group G] [MulAction G Ω] (C : OddCert G Ω)

def OddCert.S : Set G := {t : G | t ∈ stabilizer G C.ω₀ ∧ IsConj C.ρ t}

theorem OddCert.conj_mem {n t : G} (hn : n ∈ stabilizer G C.ω₀) (ht : t ∈ C.S) :
    n * t * n⁻¹ ∈ C.S := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn ht.1) (Subgroup.inv_mem _ hn), ?_⟩
  exact ht.2.trans (isConj_iff.2 ⟨n, rfl⟩)

theorem OddCert.ρ_mem_S : C.ρ ∈ C.S := ⟨C.ρ_mem, IsConj.refl _⟩

omit [MulAction G Ω] in
theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  simpa using (MulAut.conj g).orderOf_eq x

theorem orderOf_mul_conj {c ρ s : G} (hc : c * ρ = ρ * c) :
    orderOf (ρ * (c * s * c⁻¹)) = orderOf (ρ * s) := by
  have : ρ * (c * s * c⁻¹) = c * (ρ * s) * c⁻¹ := by
    calc ρ * (c * s * c⁻¹) = (ρ * c) * s * c⁻¹ := by group
      _ = (c * ρ) * s * c⁻¹ := by rw [hc]
      _ = c * (ρ * s) * c⁻¹ := by group
  rw [this]
  exact (MulAut.conj c).orderOf_eq (ρ * s)

theorem OddCert.nf_pair {a b : G} (ha : a ∈ C.S) (hb : b ∈ C.S) (hab : a ≠ b)
    (hodd : Odd (orderOf (a * b))) :
    ∃ (k : Fin 3) (m : G), m ∈ stabilizer G C.ω₀ ∧ a = m * C.ρ * m⁻¹ ∧ b = m * C.s k * m⁻¹ := by
  obtain ⟨n, hn, hcase⟩ := C.S_cover a ha.1 ha.2
  have hn' : n⁻¹ ∈ stabilizer G C.ω₀ := Subgroup.inv_mem _ hn
  have hb' : n⁻¹ * b * n ∈ C.S := by
    have := C.conj_mem hn' hb
    rwa [inv_inv] at this
  have hprod : ∀ r : G, a = n * r * n⁻¹ →
      orderOf (r * (n⁻¹ * b * n)) = orderOf (a * b) := by
    intro r hr
    have : r * (n⁻¹ * b * n) = n⁻¹ * (a * b) * n := by
      rw [hr]
      group
    rw [this]
    simpa using (MulAut.conj n⁻¹).orderOf_eq (a * b)
  rcases hcase with hfi | hfi
  · exfalso
    have hne : n⁻¹ * b * n ≠ C.t₁ := by
      intro h
      apply hab
      rw [hfi, ← h]
      group
    exact C.scan₁ _ hb'.1 hb'.2 hne (by rw [hprod _ hfi]; exact hodd)
  · have hbne : n⁻¹ * b * n ≠ C.ρ := by
      intro h
      apply hab
      rw [hfi]
      have : b = n * (n⁻¹ * b * n) * n⁻¹ := by group
      rw [this, h]
    obtain ⟨k, c, hc, hgc⟩ :=
      C.partner _ hb'.1 hb'.2 hbne (by rw [hprod _ hfi]; exact hodd)
    have hcH : c ∈ stabilizer G C.ω₀ := (Subgroup.mem_inf.1 hc).1
    have hcρ : c * C.ρ = C.ρ * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2
    refine ⟨k, n * c, Subgroup.mul_mem _ hn hcH, ?_, ?_⟩
    · rw [hfi]
      have : c * C.ρ * c⁻¹ = C.ρ := by rw [hcρ]; group
      calc n * C.ρ * n⁻¹ = n * (c * C.ρ * c⁻¹) * n⁻¹ := by rw [this]
        _ = n * c * C.ρ * (n * c)⁻¹ := by group
    · have h1 : b = n * (n⁻¹ * b * n) * n⁻¹ := by group
      rw [h1, hgc]
      group

theorem ncard_fixInter_conj (g a b : G) :
    ({ω : Ω | (g * a * g⁻¹) • ω = ω} ∩ {ω | (g * b * g⁻¹) • ω = ω}).ncard =
      ({ω : Ω | a • ω = ω} ∩ {ω | b • ω = ω}).ncard := by
  have key : ∀ (x : G) (ω : Ω), (g * x * g⁻¹) • ω = ω ↔ x • g⁻¹ • ω = g⁻¹ • ω := by
    intro x ω
    rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul]
  have h : {ω : Ω | (g * a * g⁻¹) • ω = ω} ∩ {ω | (g * b * g⁻¹) • ω = ω} =
      (fun ω => g • ω) '' ({ω : Ω | a • ω = ω} ∩ {ω | b • ω = ω}) := by
    ext ω
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨g⁻¹ • ω, ⟨(key a ω).1 h1, (key b ω).1 h2⟩, by simp⟩
    · rintro ⟨ω', ⟨h1, h2⟩, rfl⟩
      refine ⟨(key a _).2 ?_, (key b _).2 ?_⟩
      · rw [inv_smul_smul]; exact h1
      · rw [inv_smul_smul]; exact h2
  rw [h, Set.ncard_image_of_injective _ (MulAction.injective g)]

def OddCert.Pairs (k : Fin 3) : Set (G × G) :=
  {p | p.1 ∈ stabilizer G C.ω₀ ∧ p.2 ∈ stabilizer G C.ω₀ ∧
    ∃ g : G, g * C.ρ * g⁻¹ = p.1 ∧ g * C.s k * g⁻¹ = p.2}

def OddCert.Orb (k : Fin 3) : Set (G × G) :=
  {p | ∃ n ∈ stabilizer G C.ω₀, p = (n * C.ρ * n⁻¹, n * C.s k * n⁻¹)}

theorem OddCert.pairs_eq_orbit (k : Fin 3) : C.Pairs k = C.Orb k := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨ha, hb, g, hga, hgb⟩
    simp only at hga hgb
    have haS : a ∈ C.S := ⟨ha, isConj_iff.2 ⟨g, hga⟩⟩
    have hbS : b ∈ C.S := ⟨hb, (C.s_conj k).trans (isConj_iff.2 ⟨g, hgb⟩)⟩
    have hprod : a * b = g * (C.ρ * C.s k) * g⁻¹ := by rw [← hga, ← hgb]; group
    have hord : orderOf (a * b) = C.o k := by rw [hprod, orderOf_conj', C.o_spec]
    have hab : a ≠ b := by
      intro h
      have h1 : C.ρ = C.s k := by
        rw [← hga, ← hgb] at h
        exact mul_left_cancel (mul_right_cancel h)
      have h2 : orderOf (C.ρ * C.s k) = 1 := by rw [← h1, C.ρ_sq, orderOf_one]
      rw [C.o_spec] at h2
      exact absurd (C.o_gt k) (by omega)
    obtain ⟨k', m, hm, hma, hmb⟩ := C.nf_pair haS hbS hab (hord ▸ C.o_odd k)
    have hprod' : a * b = m * (C.ρ * C.s k') * m⁻¹ := by rw [hma, hmb]; group
    have hk : k' = k := by
      apply C.sep k' k
      · rw [← C.o_spec, ← orderOf_conj' m, ← hprod', hord]
      · have h1 := ncard_fixInter_conj (Ω := Ω) m C.ρ (C.s k')
        have h2 := ncard_fixInter_conj (Ω := Ω) g C.ρ (C.s k)
        rw [← hma, ← hmb] at h1
        rw [hga, hgb] at h2
        rw [← C.d_spec, ← C.d_spec, ← h1, h2]
    subst hk
    exact ⟨m, hm, by rw [hma, hmb]⟩
  · rintro ⟨n, hn, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn C.ρ_mem) (Subgroup.inv_mem _ hn),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hn (C.s_mem k)) (Subgroup.inv_mem _ hn), n, rfl, rfl⟩

def OddCert.Z (k : Fin 3) : Subgroup G :=
  stabilizer G C.ω₀ ⊓ Subgroup.centralizer ({C.ρ} : Set G) ⊓ Subgroup.centralizer {C.s k}

variable [Finite G]

theorem OddCert.card_Z_mul (k : Fin 3) :
    Nat.card ↥(C.Z k) * (C.Orb k).ncard = Nat.card (stabilizer G C.ω₀) :=
  card_stabilizer_pair_mul_ncard_orbit (stabilizer G C.ω₀) C.ρ (C.s k)

theorem OddCert.Z_card (k : Fin 3) : Nat.card ↥(C.Z k) = C.Zn k := by
  have hsub : C.z k '' Set.Iio (C.Zn k) ⊆ (C.Z k : Set G) := by
    rintro _ ⟨i, hi, rfl⟩
    exact C.z_mem k i hi
  have hinj : Set.InjOn (C.z k) (Set.Iio (C.Zn k)) := fun i hi j hj e => C.z_inj k i hi j hj e
  have hge : C.Zn k ≤ Nat.card ↥(C.Z k) := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hinj.ncard_image, Set.ncard_Iio_nat] at this
    have e : Nat.card ↥(C.Z k) = (C.Z k : Set G).ncard := Nat.card_coe_set_eq (C.Z k : Set G)
    rw [e]
    exact this
  exact le_antisymm (C.Z_le k) hge

theorem OddCert.Z_eq (k : Fin 3) : (C.Z k : Set G) = C.z k '' Set.Iio (C.Zn k) := by
  have hsub : C.z k '' Set.Iio (C.Zn k) ⊆ (C.Z k : Set G) := by
    rintro _ ⟨i, hi, rfl⟩
    exact C.z_mem k i hi
  have hinj : Set.InjOn (C.z k) (Set.Iio (C.Zn k)) := fun i hi j hj e => C.z_inj k i hi j hj e
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [hinj.ncard_image, Set.ncard_Iio_nat]
  have e : Nat.card ↥(C.Z k) = (C.Z k : Set G).ncard := Nat.card_coe_set_eq (C.Z k : Set G)
  rw [← e]
  exact (C.Z_card k).le

theorem OddCert.card_centralizer_inf (k : Fin 3) {q : ℕ}
    (hq : {ω ∈ orbit G C.ω₀ | C.ρ • ω = ω ∧ C.s k • ω = ω}.ncard = q) :
    Nat.card ↥(Subgroup.centralizer ({C.ρ} : Set G) ⊓ Subgroup.centralizer {C.s k}) =
      C.Zn k * q := by
  have h3 := card_centralizer_inf_mul_ncard_pairs C.ρ (C.s k) C.ω₀
  rw [hq] at h3
  have hP : {p : G × G | p.1 ∈ stabilizer G C.ω₀ ∧ p.2 ∈ stabilizer G C.ω₀ ∧
      ∃ g : G, g * C.ρ * g⁻¹ = p.1 ∧ g * C.s k * g⁻¹ = p.2} = C.Orb k := C.pairs_eq_orbit k
  rw [hP] at h3
  have h4 := C.card_Z_mul k
  rw [C.Z_card k] at h4
  have hH : 0 < Nat.card (stabilizer G C.ω₀) := Nat.card_pos
  have hpos : 0 < (C.Orb k).ncard := by
    rcases Nat.eq_zero_or_pos (C.Orb k).ncard with h | h
    · rw [h, mul_zero] at h4
      omega
    · exact h
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card ↥(Subgroup.centralizer ({C.ρ} : Set G) ⊓ Subgroup.centralizer {C.s k}) *
        (C.Orb k).ncard = Nat.card (stabilizer G C.ω₀) * q := h3
    _ = (C.Zn k * (C.Orb k).ncard) * q := by rw [h4]
    _ = (C.Zn k * q) * (C.Orb k).ncard := by ring

omit [Finite G] in
theorem orderOf_conj_inv' (y x : G) : orderOf (y⁻¹ * x * y) = orderOf x := by
  simpa using orderOf_conj' y⁻¹ x

omit [Finite G] in
theorem OddCert.nf_vector {s : G} (hconj : IsConj C.ρ s) (hne : s ≠ C.ρ)
    (hodd : Odd (orderOf (C.ρ * s))) {v : Ω} (hv : v ∈ orbit G C.ω₀) (h1 : C.ρ • v = v)
    (h2 : s • v = v) :
    ∃ (k : Fin 3) (z : G), z ∈ Subgroup.centralizer ({C.ρ} : Set G) ∧ s = z * C.s k * z⁻¹ := by
  obtain ⟨y, rfl⟩ := hv
  have hρ' : y⁻¹ * C.ρ * y ∈ stabilizer G C.ω₀ := by
    rw [mem_stabilizer_iff, mul_smul, mul_smul, h1, inv_smul_smul]
  have hs' : y⁻¹ * s * y ∈ stabilizer G C.ω₀ := by
    rw [mem_stabilizer_iff, mul_smul, mul_smul, h2, inv_smul_smul]
  have haS : y⁻¹ * C.ρ * y ∈ C.S := ⟨hρ', isConj_iff.2 ⟨y⁻¹, by simp⟩⟩
  have hbS : y⁻¹ * s * y ∈ C.S := ⟨hs', hconj.trans (isConj_iff.2 ⟨y⁻¹, by simp⟩)⟩
  have hab : y⁻¹ * C.ρ * y ≠ y⁻¹ * s * y := by
    intro h
    apply hne
    exact (mul_left_cancel (mul_right_cancel h)).symm
  have hprod : (y⁻¹ * C.ρ * y) * (y⁻¹ * s * y) = y⁻¹ * (C.ρ * s) * y := by group
  have hodd' : Odd (orderOf ((y⁻¹ * C.ρ * y) * (y⁻¹ * s * y))) := by
    rw [hprod, orderOf_conj_inv']
    exact hodd
  obtain ⟨k, m, hm, ha, hb⟩ := C.nf_pair haS hbS hab hodd'
  refine ⟨k, y * m, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : y * m * C.ρ * (y * m)⁻¹ = C.ρ := by
      calc y * m * C.ρ * (y * m)⁻¹ = y * (m * C.ρ * m⁻¹) * y⁻¹ := by group
        _ = y * (y⁻¹ * C.ρ * y) * y⁻¹ := by rw [← ha]
        _ = C.ρ := by group
    exact mul_inv_eq_iff_eq_mul.1 hz
  · calc s = y * (y⁻¹ * s * y) * y⁻¹ := by group
      _ = y * (m * C.s k * m⁻¹) * y⁻¹ := by rw [hb]
      _ = y * m * C.s k * (y * m)⁻¹ := by group

theorem OddCert.faithful (k : Fin 3)
    (hfaith : ∀ i < C.Zn k,
      (∀ v : Ω, C.ρ • v = v → C.s k • v = v → C.z k i • v = v) → C.z k i = 1)
    {g : G} (hgρ : g ∈ Subgroup.centralizer ({C.ρ} : Set G))
    (hgs : g ∈ Subgroup.centralizer ({C.s k} : Set G))
    (hfix : ∀ v : Ω, C.ρ • v = v → C.s k • v = v → g • v = v) : g = 1 := by
  have hg0 : g ∈ stabilizer G C.ω₀ := by
    rw [mem_stabilizer_iff]
    exact hfix _ (mem_stabilizer_iff.1 C.ρ_mem) (mem_stabilizer_iff.1 (C.s_mem k))
  have hgZ : g ∈ (C.Z k : Set G) := Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg0, hgρ⟩, hgs⟩
  rw [C.Z_eq k] at hgZ
  obtain ⟨i, hi, rfl⟩ := hgZ
  exact hfaith i hi hfix

theorem OddCert.faithful_conj (k : Fin 3)
    (hfaith : ∀ i < C.Zn k,
      (∀ v : Ω, C.ρ • v = v → C.s k • v = v → C.z k i • v = v) → C.z k i = 1)
    {z : G} (hz : z ∈ Subgroup.centralizer ({C.ρ} : Set G)) {g : G}
    (hgρ : g ∈ Subgroup.centralizer ({C.ρ} : Set G))
    (hgs : g ∈ Subgroup.centralizer ({z * C.s k * z⁻¹} : Set G))
    (hfix : ∀ v : Ω, C.ρ • v = v → (z * C.s k * z⁻¹) • v = v → g • v = v) : g = 1 := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hz hgρ hgs
  have hzρ : z⁻¹ * C.ρ * z = C.ρ := by
    calc z⁻¹ * C.ρ * z = z⁻¹ * (C.ρ * z) := by group
      _ = z⁻¹ * (z * C.ρ) := by rw [hz]
      _ = C.ρ := by group
  have hg1 : z⁻¹ * g * z ∈ Subgroup.centralizer ({C.ρ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (z⁻¹ * g * z) * C.ρ = (z⁻¹ * g * z) * (z⁻¹ * C.ρ * z) := by rw [hzρ]
      _ = z⁻¹ * (g * C.ρ) * z := by group
      _ = z⁻¹ * (C.ρ * g) * z := by rw [hgρ]
      _ = (z⁻¹ * C.ρ * z) * (z⁻¹ * g * z) := by group
      _ = C.ρ * (z⁻¹ * g * z) := by rw [hzρ]
  have hg2 : z⁻¹ * g * z ∈ Subgroup.centralizer ({C.s k} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : g * (z * C.s k * z⁻¹) = (z * C.s k * z⁻¹) * g := hgs
    calc (z⁻¹ * g * z) * C.s k = z⁻¹ * (g * (z * C.s k * z⁻¹)) * z := by group
      _ = z⁻¹ * ((z * C.s k * z⁻¹) * g) * z := by rw [h]
      _ = C.s k * (z⁻¹ * g * z) := by group
  have hg3 : z⁻¹ * g * z = 1 := by
    refine C.faithful k hfaith hg1 hg2 fun v hv1 hv2 => ?_
    have hzv : (z⁻¹ * g * z) • v = v ↔ g • z • v = z • v := by
      rw [mul_smul, mul_smul, inv_smul_eq_iff]
    rw [hzv]
    refine hfix (z • v) ?_ ?_
    · rw [← mul_smul, ← hz, mul_smul, hv1]
    · rw [mul_smul, mul_smul, inv_smul_smul, hv2]
  calc g = z * (z⁻¹ * g * z) * z⁻¹ := by group
    _ = 1 := by rw [hg3]; group

end Cert

end CFSG.Sporadic.Co1.Module.Odd
