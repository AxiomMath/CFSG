module

public import CFSG.Monster.GMS.Leech.Module
public import CFSG.Monster.GMS.Leech.Linear

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement Matrix

section Coordinate

variable {G : Type*} [Group G]

open scoped Classical in
private noncomputable def ze (x : G) : ZMod 2 := if x = 1 then 0 else 1

private theorem ze_eq_zero_iff {x : G} : ze x = 0 ↔ x = 1 := by
  unfold ze
  split_ifs with h <;> simp [h]

private theorem ze_mul {z x y : G} (hz1 : z ≠ 1) (hzz : z * z = 1) (hx : x = 1 ∨ x = z)
    (hy : y = 1 ∨ y = z) : ze (x * y) = ze x + ze y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [ze, hz1, hzz]
  decide

private theorem ze_congr {x y : G} (h : x = 1 ↔ y = 1) : ze x = ze y := by
  classical
  exact if_congr h rfl rfl

private theorem ze_conj (c x : G) : ze (c * x * c⁻¹) = ze x := by
  refine ze_congr ?_
  constructor
  · intro h
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [mul_assoc] using this
  · rintro rfl
    simp

end Coordinate

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem z_mul_self : z * z = 1 := L.extraspecial.mul_self

theorem z_ne_one : z ≠ 1 := L.extraspecial.ne_one

theorem z_mem : z ∈ leechQ z := L.extraspecial.mem

theorem mem_centralizer {q : G} (hq : q ∈ leechQ z) :
    q ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (L.extraspecial.central q hq)

theorem conj_mem (c : Subgroup.centralizer ({z} : Set G)) {q : G} (hq : q ∈ leechQ z) :
    (c : G) * q * (c : G)⁻¹ ∈ leechQ z := by
  have h1 : L.φ ⟨q, L.mem_centralizer hq⟩ = 1 := (L.φ_ker _).2 hq
  have h2 : L.φ (c * ⟨q, L.mem_centralizer hq⟩ * c⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  exact (L.φ_ker _).1 h2

theorem conj_mem' {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) {q : G}
    (hq : q ∈ leechQ z) : g * q * g⁻¹ ∈ leechQ z :=
  L.conj_mem ⟨g, hg⟩ hq

theorem vec_one : L.vec 1 = 0 := (L.vec_eq_zero 1 (one_mem _)).2 (Or.inl rfl)

theorem vec_z : L.vec z = 0 := (L.vec_eq_zero z L.z_mem).2 (Or.inr rfl)

theorem vec_inv {q : G} (hq : q ∈ leechQ z) : L.vec q⁻¹ = L.vec q := by
  have h := L.vec_mul q hq q⁻¹ (inv_mem hq)
  rw [mul_inv_cancel, L.vec_one] at h
  exact add_left_cancel (h.symm.trans (CFSG.Sporadic.Co1.Module.vec_add_self (L.vec q)).symm)

theorem vec_mul_z {q : G} (hq : q ∈ leechQ z) : L.vec (q * z) = L.vec q := by
  rw [L.vec_mul q hq z L.z_mem, L.vec_z, add_zero]

theorem vec_conj' {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) {q : G}
    (hq : q ∈ leechQ z) : L.vec (g * q * g⁻¹) = co1Act (L.φ ⟨g, hg⟩) (L.vec q) :=
  L.vec_conj ⟨g, hg⟩ q hq

theorem eq_or_eq_mul_z {p q : G} (hp : p ∈ leechQ z) (hq : q ∈ leechQ z)
    (h : L.vec p = L.vec q) : p = q ∨ p = q * z := by
  have h1 : L.vec (q⁻¹ * p) = 0 := by
    rw [L.vec_mul q⁻¹ (inv_mem hq) p hp, L.vec_inv hq, h]
    exact CFSG.Sporadic.Co1.Module.vec_add_self (L.vec q)
  rcases (L.vec_eq_zero _ (mul_mem (inv_mem hq) hp)).1 h1 with h2 | h2
  · left
    exact (inv_mul_eq_one.1 h2).symm
  · right
    rw [← h2]
    group

theorem vec_ne_zero_iff {q : G} (hq : q ∈ leechQ z) : L.vec q ≠ 0 ↔ q ≠ 1 ∧ q ≠ z := by
  rw [Ne, L.vec_eq_zero q hq]
  tauto

omit L

private noncomputable def sqf (q : G) : ZMod 2 := ze (q * q)

private noncomputable def cf (p q : G) : ZMod 2 := ze ⁅p, q⁆

include L

private theorem sqf_mul {p q : G} (hp : p ∈ leechQ z) (hq : q ∈ leechQ z) :
    sqf (p * q) = sqf p + sqf q + cf p q := by
  have hE := L.extraspecial
  have ha := hE.comm p hp q hq
  have hs := hE.sq p hp
  have ht := hE.sq q hq
  have hz : ∀ x, x = 1 ∨ x = z → x * p = p * x := by
    rintro x (rfl | rfl)
    · simp
    · exact (hE.central p hp).symm
  have hcomm : ⁅p, q⁆ * p = p * ⁅p, q⁆ := hz _ ha
  have hid : (p * q) * (p * q) = ⁅p, q⁆ * ((p * p) * (q * q)) := by
    have h1 : q * p = ⁅p, q⁆⁻¹ * (p * q) := by
      simp only [commutatorElement_def]
      group
    have h2 : ⁅p, q⁆⁻¹ = ⁅p, q⁆ := by
      rcases ha with h | h
      · rw [h]; simp
      · rw [h]; exact inv_eq_of_mul_eq_one_right hE.mul_self
    calc (p * q) * (p * q) = p * (q * p) * q := by group
      _ = p * (⁅p, q⁆ * (p * q)) * q := by rw [h1, h2]
      _ = (p * ⁅p, q⁆) * (p * q) * q := by group
      _ = (⁅p, q⁆ * p) * (p * q) * q := by rw [← hcomm]
      _ = ⁅p, q⁆ * ((p * p) * (q * q)) := by group
  have hst : p * p * (q * q) = 1 ∨ p * p * (q * q) = z := by
    rcases hs with h | h <;> rcases ht with h' | h' <;> simp [h, h', hE.mul_self]
  unfold sqf cf
  rw [hid, ze_mul L.z_ne_one L.z_mul_self ha hst, ze_mul L.z_ne_one L.z_mul_self hs ht]
  ring

private theorem cf_mul_left {p p' q : G} (hp : p ∈ leechQ z) (hp' : p' ∈ leechQ z)
    (hq : q ∈ leechQ z) : cf (p * p') q = cf p q + cf p' q := by
  have hE := L.extraspecial
  unfold cf
  rw [hE.commutatorElement_mul_left hp hp' hq,
    ze_mul L.z_ne_one L.z_mul_self (hE.comm p hp q hq) (hE.comm p' hp' q hq)]

omit L in
private theorem sqf_conj (c q : G) : sqf (c * q * c⁻¹) = sqf q := by
  unfold sqf
  have : c * q * c⁻¹ * (c * q * c⁻¹) = c * (q * q) * c⁻¹ := by group
  rw [this, ze_conj]

private theorem sqf_mul_z {q : G} (hq : q ∈ leechQ z) : sqf (q * z) = sqf q := by
  have hE := L.extraspecial
  have : q * z * (q * z) = q * q := by
    calc q * z * (q * z) = q * (z * q) * z := by group
      _ = q * (q * z) * z := by rw [← hE.central q hq]
      _ = q * q * (z * z) := by group
      _ = q * q := by rw [hE.mul_self, mul_one]
  unfold sqf
  rw [this]

private noncomputable def Θ (w : Fin 24 → ZMod 2) : ZMod 2 :=
  sqf (Classical.choose (L.vec_surj w))

private theorem Θ_vec {q : G} (hq : q ∈ leechQ z) : L.Θ (L.vec q) = sqf q := by
  obtain ⟨hq', hv⟩ := Classical.choose_spec (L.vec_surj (L.vec q))
  rcases L.eq_or_eq_mul_z hq' hq hv with h | h
  · unfold Θ
    rw [h]
  · unfold Θ
    rw [h, L.sqf_mul_z hq]

private theorem Θ_co1Act (c : Subgroup.centralizer ({z} : Set G)) (w : Fin 24 → ZMod 2) :
    L.Θ (co1Act (L.φ c) w) = L.Θ w := by
  obtain ⟨q, hq, rfl⟩ := L.vec_surj w
  rw [← L.vec_conj c q hq, L.Θ_vec (L.conj_mem c hq), L.Θ_vec hq, sqf_conj]

private theorem polar_Θ {p q : G} (hp : p ∈ leechQ z) (hq : q ∈ leechQ z) :
    CFSG.Sporadic.Co1.Module.polar L.Θ (L.vec p) (L.vec q) = cf p q := by
  unfold CFSG.Sporadic.Co1.Module.polar
  rw [← L.vec_mul p hp q hq, L.Θ_vec (mul_mem hp hq), L.Θ_vec hp, L.Θ_vec hq, L.sqf_mul hp hq]
  ring

private theorem Θ_ne_zero : L.Θ ≠ 0 := by
  intro h0
  have hsq : ∀ q ∈ leechQ z, sqf q = 0 := fun q hq => by
    rw [← L.Θ_vec hq, h0]
    rfl
  have hcf : ∀ p ∈ leechQ z, ∀ q ∈ leechQ z, cf p q = 0 := by
    intro p hp q hq
    have h := L.sqf_mul hp hq
    rw [hsq _ (mul_mem hp hq), hsq _ hp, hsq _ hq] at h
    simpa using h.symm
  have hcomm : ∀ p ∈ leechQ z, ∀ q ∈ leechQ z, p * q = q * p := fun p hp q hq =>
    commutatorElement_eq_one_iff_mul_comm.1 (ze_eq_zero_iff.1 (hcf p hp q hq))
  obtain ⟨q, hq, hvq⟩ := L.vec_surj (Pi.single 0 1)
  have h1 := L.center_eq q hq (fun p hp => hcomm p hp q hq)
  have h2 : L.vec q = 0 := (L.vec_eq_zero q hq).2 h1
  rw [hvq] at h2
  have := congrFun h2 0
  simp at this

private theorem Θ_eq_q₀ :
    L.Θ = CFSG.Sporadic.Co1.Module.q₀ := by
  have hbil : ∀ u u' v, CFSG.Sporadic.Co1.Module.polar L.Θ (u + u') v =
      CFSG.Sporadic.Co1.Module.polar L.Θ u v + CFSG.Sporadic.Co1.Module.polar L.Θ u' v := by
    intro u u' v
    obtain ⟨p, hp, rfl⟩ := L.vec_surj u
    obtain ⟨p', hp', rfl⟩ := L.vec_surj u'
    obtain ⟨q, hq, rfl⟩ := L.vec_surj v
    rw [← L.vec_mul p hp p' hp', L.polar_Θ (mul_mem hp hp') hq, L.polar_Θ hp hq,
      L.polar_Θ hp' hq]
    exact L.cf_mul_left hp hp' hq
  have hinv : ∀ (g : Co1) (v : Fin 24 → ZMod 2), L.Θ (CFSG.Sporadic.Co1.Module.co1Act g v) =
      L.Θ v := by
    intro g v
    obtain ⟨c, rfl⟩ := L.φ_surj g
    exact L.Θ_co1Act c v
  rcases CFSG.Sporadic.Co1.Module.co1_invariant_quadratic hbil hinv with h | h
  · exact absurd h L.Θ_ne_zero
  · exact h

omit L in
private theorem ze_of_ne_one {x : G} (hx : x ≠ 1) : ze x = 1 := by
  unfold ze
  simp [hx]

theorem mul_self_eq_one_iff
    {q : G} (hq : q ∈ leechQ z) :
    q * q = 1 ↔ CFSG.Sporadic.Co1.Module.q₀ (L.vec q) = 0 := by
  rw [← L.Θ_eq_q₀, L.Θ_vec hq]
  exact ze_eq_zero_iff.symm

theorem mul_self_eq_z_iff
    {q : G} (hq : q ∈ leechQ z) :
    q * q = z ↔ CFSG.Sporadic.Co1.Module.q₀ (L.vec q) = 1 := by
  rw [← L.Θ_eq_q₀, L.Θ_vec hq]
  unfold sqf
  constructor
  · intro h
    rw [h]
    exact ze_of_ne_one L.z_ne_one
  · intro h
    rcases L.extraspecial.sq q hq with h' | h'
    · rw [h', ze_eq_zero_iff.2 rfl] at h
      exact absurd h (by decide)
    · exact h'

theorem comm_eq_one_iff
    {p q : G} (hp : p ∈ leechQ z) (hq : q ∈ leechQ z) :
    ⁅p, q⁆ = 1 ↔ CFSG.Sporadic.Co1.Module.bil₀ (L.vec p) (L.vec q) = 0 := by
  have h := L.polar_Θ hp hq
  rw [L.Θ_eq_q₀, CFSG.Sporadic.Co1.Module.polar_q₀] at h
  rw [h]
  exact ze_eq_zero_iff.symm

theorem comm_eq_z_iff
    {p q : G} (hp : p ∈ leechQ z) (hq : q ∈ leechQ z) :
    ⁅p, q⁆ = z ↔ CFSG.Sporadic.Co1.Module.bil₀ (L.vec p) (L.vec q) = 1 := by
  have h := L.polar_Θ hp hq
  rw [L.Θ_eq_q₀, CFSG.Sporadic.Co1.Module.polar_q₀] at h
  rw [h]
  unfold cf
  constructor
  · intro h'
    rw [h']
    exact ze_of_ne_one L.z_ne_one
  · intro h'
    rcases L.extraspecial.comm p hp q hq with h'' | h''
    · rw [h'', ze_eq_zero_iff.2 rfl] at h'
      exact absurd h' (by decide)
    · exact h''

theorem exists_conj_eq
    {ι : Type*} [Fintype ι] {a b : ι → G} (ha : ∀ i, a i ∈ leechQ z)
    (hb : ∀ i, b i ∈ leechQ z) (hv : ∀ i, L.vec (a i) = L.vec (b i))
    (hind : LinearIndependent (ZMod 2) fun i => L.vec (b i)) :
    ∃ p ∈ leechQ z, ∀ i, p * a i * p⁻¹ = b i := by
  classical
  let e : ι → ZMod 2 := fun i => if a i = b i then 0 else 1
  obtain ⟨w, hw⟩ := Leech.exists_bil₀_eq hind e
  obtain ⟨p, hp, rfl⟩ := L.vec_surj w
  refine ⟨p, hp, fun i => ?_⟩
  have hE := L.extraspecial
  rcases L.eq_or_eq_mul_z (ha i) (hb i) (hv i) with h | h
  · have he : e i = 0 := by simp [e, h]
    have h1 := (L.comm_eq_one_iff hp (hb i)).2 (by rw [hw i, he])
    rw [h]
    have h2 : p * b i * p⁻¹ * (b i)⁻¹ = 1 := h1
    calc p * b i * p⁻¹ = (p * b i * p⁻¹ * (b i)⁻¹) * b i := by group
      _ = b i := by rw [h2, one_mul]
  · have hne : a i ≠ b i := by
      rw [h]
      intro h'
      apply L.z_ne_one
      simpa using h'
    have he : e i = 1 := by simp [e, hne]
    have h1 := (L.comm_eq_z_iff hp (hb i)).2 (by rw [hw i, he])
    have h2 : p * b i * p⁻¹ = z * b i := by
      have h3 : p * b i * p⁻¹ * (b i)⁻¹ = z := h1
      calc p * b i * p⁻¹ = (p * b i * p⁻¹ * (b i)⁻¹) * b i := by group
        _ = z * b i := by rw [h3]
    have h4 : p * z * p⁻¹ = z := by
      rw [hE.central p hp]
      group
    rw [h]
    calc p * (b i * z) * p⁻¹ = (p * b i * p⁻¹) * (p * z * p⁻¹) := by group
      _ = z * b i * z := by rw [h2, h4]
      _ = b i * (z * z) := by rw [← hE.central (b i) (hb i)]; group
      _ = b i := by rw [hE.mul_self, mul_one]

theorem ncard_preimage (A : Set (Fin 24 → ZMod 2)) :
    {g : G | g ∈ leechQ z ∧ L.vec g ∈ A}.ncard = 2 * A.ncard := by
  classical
  choose σ hσQ hσ using L.vec_surj
  let f : (Fin 24 → ZMod 2) × Bool → G := fun p => if p.2 then σ p.1 * z else σ p.1
  have hfQ : ∀ p, f p ∈ leechQ z := by
    rintro ⟨w, b⟩
    cases b
    · exact hσQ w
    · exact mul_mem (hσQ w) L.z_mem
  have hfv : ∀ p, L.vec (f p) = p.1 := by
    rintro ⟨w, b⟩
    cases b
    · exact hσ w
    · show L.vec (σ w * z) = w
      rw [L.vec_mul_z (hσQ w), hσ w]
  have hinj : Function.Injective f := by
    rintro ⟨w, b⟩ ⟨w', b'⟩ h
    have hw : w = w' := by
      have := congrArg L.vec h
      rwa [hfv, hfv] at this
    subst hw
    cases b <;> cases b'
    · rfl
    · exfalso
      apply L.z_ne_one
      have h' : σ w = σ w * z := h
      simpa using h'.symm
    · exfalso
      apply L.z_ne_one
      have h' : σ w * z = σ w := h
      simpa using h'
    · rfl
  have himg : {g : G | g ∈ leechQ z ∧ L.vec g ∈ A} = f '' (A ×ˢ Set.univ) := by
    ext g
    constructor
    · rintro ⟨hg, hgA⟩
      rcases L.eq_or_eq_mul_z hg (hσQ (L.vec g)) (hσ (L.vec g)).symm with h | h
      · exact ⟨(L.vec g, false), ⟨hgA, Set.mem_univ _⟩, h.symm⟩
      · exact ⟨(L.vec g, true), ⟨hgA, Set.mem_univ _⟩, h.symm⟩
    · rintro ⟨p, ⟨hpA, -⟩, rfl⟩
      exact ⟨hfQ p, by rw [hfv]; exact hpA⟩
  rw [himg, Set.ncard_image_of_injective _ hinj, Set.ncard_prod, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm]

end LeechSystem

end CFSG.Monster.GMS
