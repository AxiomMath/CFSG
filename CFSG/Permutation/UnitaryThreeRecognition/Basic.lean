module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

structure IsRootSubgroup (Q : Subgroup G) (a : Ω) : Prop where
  le_stabilizer : Q ≤ stabilizer G a
  normal : ∀ g : G, g • a = a → ∀ x ∈ Q, g * x * g⁻¹ ∈ Q
  regular : ∀ β γ : Ω, β ≠ a → γ ≠ a → ∃! u : Q, (u : G) • β = γ

@[expose] def pairStab (G : Type*) [Group G] [MulAction G Ω] (a b : Ω) : Subgroup G :=
  stabilizer G a ⊓ stabilizer G b

theorem mem_pairStab {a b : Ω} {g : G} : g ∈ pairStab G a b ↔ g • a = a ∧ g • b = b :=
  Iff.rfl

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem smul_self {u : G} (hu : u ∈ Q) : u • a = a := hQ.le_stabilizer hu

theorem smul_ne {u : G} (hu : u ∈ Q) {β : Ω} (hβ : β ≠ a) : u • β ≠ a := by
  intro h
  apply hβ
  have : u⁻¹ • (u • β) = u⁻¹ • a := by rw [h]
  rw [inv_smul_smul] at this
  rw [this, inv_smul_eq_iff, hQ.smul_self hu]

theorem eq_of_smul_eq {u v : G} (hu : u ∈ Q) (hv : v ∈ Q) {β : Ω} (hβ : β ≠ a)
    (h : u • β = v • β) : u = v := by
  obtain ⟨w, _, hw⟩ := hQ.regular β (v • β) hβ (hQ.smul_ne hv hβ)
  have h1 := hw ⟨u, hu⟩ h
  have h2 := hw ⟨v, hv⟩ rfl
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem eq_one_of_smul_eq {u : G} (hu : u ∈ Q) {β : Ω} (hβ : β ≠ a) (h : u • β = β) :
    u = 1 :=
  hQ.eq_of_smul_eq hu Q.one_mem hβ (by rw [h, one_smul])

theorem exists_smul_eq {β γ : Ω} (hβ : β ≠ a) (hγ : γ ≠ a) : ∃ u ∈ Q, u • β = γ := by
  obtain ⟨u, hu, _⟩ := hQ.regular β γ hβ hγ
  exact ⟨u, u.property, hu⟩

theorem disjoint_pairStab {b : Ω} (hb : b ≠ a) : Disjoint Q (pairStab G a b) := by
  rw [Subgroup.disjoint_def]
  intro x hxQ hxT
  exact hQ.eq_one_of_smul_eq hxQ hb hxT.2

theorem exists_mul_pairStab {b : Ω} (hb : b ≠ a) {g : G} (hg : g • a = a) :
    ∃ x ∈ Q, ∃ h ∈ pairStab G a b, g = x * h := by
  have hgb : g • b ≠ a := by
    intro h
    apply hb
    have : g⁻¹ • (g • b) = g⁻¹ • a := by rw [h]
    rw [inv_smul_smul] at this
    rw [this, inv_smul_eq_iff, hg]
  obtain ⟨x, hxQ, hx⟩ := hQ.exists_smul_eq hb hgb
  refine ⟨x, hxQ, x⁻¹ * g, ⟨?_, ?_⟩, by group⟩
  · change (x⁻¹ * g) • a = a
    rw [mul_smul, hg, inv_smul_eq_iff, hQ.smul_self hxQ]
  · change (x⁻¹ * g) • b = b
    rw [mul_smul, inv_smul_eq_iff, hx]

theorem mul_pairStab_unique {b : Ω} (hb : b ≠ a) {x x' h h' : G} (hx : x ∈ Q) (hx' : x' ∈ Q)
    (hh : h ∈ pairStab G a b) (hh' : h' ∈ pairStab G a b) (heq : x * h = x' * h') :
    x = x' ∧ h = h' := by
  have hmem : x'⁻¹ * x = h' * h⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * h) * h⁻¹ := by group
      _ = x'⁻¹ * (x' * h') * h⁻¹ := by rw [heq]
      _ = h' * h⁻¹ := by group
  have h1 : x'⁻¹ * x = 1 := by
    have hQm : x'⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem hx') hx
    have hTm : x'⁻¹ * x ∈ pairStab G a b := by
      rw [hmem]; exact (pairStab G a b).mul_mem hh' ((pairStab G a b).inv_mem hh)
    exact Subgroup.disjoint_def.mp (hQ.disjoint_pairStab hb) hQm hTm
  have hxx : x = x' := by
    have := congrArg (x' * ·) h1
    simpa using this
  refine ⟨hxx, ?_⟩
  subst hxx
  simpa using heq

theorem bruhat_exists {b : Ω} (hb : b ≠ a) {s : G} (hsb : s • b = a)
    {g : G} (hg : g • a ≠ a) :
    ∃ x ∈ Q, ∃ h ∈ pairStab G a b, ∃ y ∈ Q, g = x * h * s * y := by
  have hginv : g⁻¹ • a ≠ a := by
    intro h
    apply hg
    have : g • (g⁻¹ • a) = g • a := by rw [h]
    rw [smul_inv_smul] at this
    exact this.symm
  obtain ⟨c, hcQ, hc⟩ := hQ.exists_smul_eq hb hginv
  have hsinv : s⁻¹ • a = b := by rw [inv_smul_eq_iff, hsb]
  have hk : (g * c * s⁻¹) • a = a := by
    rw [mul_smul, mul_smul, hsinv, hc, smul_inv_smul]
  obtain ⟨x, hxQ, h, hh, hk'⟩ := hQ.exists_mul_pairStab hb hk
  refine ⟨x, hxQ, h, hh, c⁻¹, Q.inv_mem hcQ, ?_⟩
  calc g = (g * c * s⁻¹) * s * c⁻¹ := by group
    _ = x * h * s * c⁻¹ := by rw [hk']

theorem bruhat_unique {b : Ω} (hb : b ≠ a) {s : G} (hsb : s • b = a)
    {x h y x' h' y' : G} (hx : x ∈ Q) (hh : h ∈ pairStab G a b) (hy : y ∈ Q)
    (hx' : x' ∈ Q) (hh' : h' ∈ pairStab G a b) (hy' : y' ∈ Q)
    (heq : x * h * s * y = x' * h' * s * y') : x = x' ∧ h = h' ∧ y = y' := by
  have hrel : (x' * h')⁻¹ * (x * h) = s * (y' * y⁻¹) * s⁻¹ := by
    calc (x' * h')⁻¹ * (x * h) = (x' * h')⁻¹ * (x * h * s * y) * y⁻¹ * s⁻¹ := by group
      _ = (x' * h')⁻¹ * (x' * h' * s * y') * y⁻¹ * s⁻¹ := by rw [heq]
      _ = s * (y' * y⁻¹) * s⁻¹ := by group
  have hfix : ((x' * h')⁻¹ * (x * h)) • a = a := by
    rw [mul_smul, mul_smul, hh.1, hQ.smul_self hx, inv_smul_eq_iff, mul_smul, hh'.1,
      hQ.smul_self hx']
  have hsinv : s⁻¹ • a = b := by rw [inv_smul_eq_iff, hsb]
  have hyy : y' * y⁻¹ = 1 := by
    apply hQ.eq_one_of_smul_eq (Q.mul_mem hy' (Q.inv_mem hy)) hb
    rw [hrel, mul_smul, mul_smul, hsinv] at hfix
    have := congrArg (s⁻¹ • ·) hfix
    simpa [hsinv] using this
  have hy_eq : y = y' := by
    have := congrArg (· * y) hyy
    simp only [inv_mul_cancel_right, one_mul] at this
    exact this.symm
  subst hy_eq
  have hxh : x * h = x' * h' := by
    have := congrArg (· * y⁻¹ * s⁻¹) heq
    simpa [mul_assoc] using this
  obtain ⟨h1, h2⟩ := hQ.mul_pairStab_unique hb hx hx' hh hh' hxh
  exact ⟨h1, h2, rfl⟩

omit hQ in
theorem conj_mem_pairStab {b : Ω} {s : G} (hsa : s • a = b) (hsb : s • b = a) {t : G}
    (ht : t ∈ pairStab G a b) : s * t * s⁻¹ ∈ pairStab G a b := by
  have hsinva : s⁻¹ • a = b := by rw [inv_smul_eq_iff, hsb]
  have hsinvb : s⁻¹ • b = a := by rw [inv_smul_eq_iff, hsa]
  refine ⟨?_, ?_⟩
  · change (s * t * s⁻¹) • a = a
    rw [mul_smul, mul_smul, hsinva, ht.2, hsb]
  · change (s * t * s⁻¹) • b = b
    rw [mul_smul, mul_smul, hsinvb, ht.1, hsa]

omit hQ in
theorem sq_mem_pairStab {b : Ω} {s : G} (hsa : s • a = b) (hsb : s • b = a) :
    s * s ∈ pairStab G a b :=
  ⟨by change (s * s) • a = a; rw [mul_smul, hsa, hsb],
    by change (s * s) • b = b; rw [mul_smul, hsb, hsa]⟩

theorem conj_eq_of_commute {b : Ω} (hb : b ≠ a) {s : G} (hsa : s • a = b) (hsb : s • b = a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {u : G} (huQ : u ∈ Q) (hu : u ≠ 1) {t : G} (ht : t ∈ pairStab G a b)
    (htu : t * u = u * t) : s * t * s⁻¹ = t := by
  have hsinva : s⁻¹ • a = b := by rw [inv_smul_eq_iff, hsb]
  have hmove : (s * u * s⁻¹) • a ≠ a := by
    rw [mul_smul, mul_smul, hsinva]
    intro h
    have h' : u • b = b := by
      have := congrArg (s⁻¹ • ·) h
      simpa [hsinva] using this
    exact hu (hQ.eq_one_of_smul_eq huQ hb h')
  obtain ⟨x, hxQ, h, hh, y, hyQ, hdec⟩ := hQ.bruhat_exists hb hsb hmove
  set t' := s * t * s⁻¹ with ht'def
  have ht' : t' ∈ pairStab G a b := conj_mem_pairStab hsa hsb ht
  have hss : s * s ∈ pairStab G a b := sq_mem_pairStab hsa hsb
  have hsst : (s * s) * t = t * (s * s) := hcomm _ hss _ ht
  have hut : u = t * u * t⁻¹ := by
    calc u = u * t * t⁻¹ := by group
      _ = t * u * t⁻¹ := by rw [← htu]
  have key : s * u * s⁻¹ = (t' * x * t'⁻¹) * (t' * h * t⁻¹) * s * (t' * y * t'⁻¹) := by
    have e1 : s * u * s⁻¹ = t' * (s * u * s⁻¹) * t'⁻¹ := by
      conv_lhs => rw [hut]
      simp only [ht'def]
      group
    have e2 : t⁻¹ * s * t' = s := by
      simp only [ht'def]
      calc t⁻¹ * s * (s * t * s⁻¹) = t⁻¹ * ((s * s) * t) * s⁻¹ := by group
        _ = t⁻¹ * (t * (s * s)) * s⁻¹ := by rw [hsst]
        _ = s := by group
    rw [e1, hdec]
    calc t' * (x * h * s * y) * t'⁻¹
        = t' * x * h * (t⁻¹ * s * t') * y * t'⁻¹ := by rw [e2]; group
      _ = (t' * x * t'⁻¹) * (t' * h * t⁻¹) * s * (t' * y * t'⁻¹) := by group
  have hx2 : t' * x * t'⁻¹ ∈ Q := hQ.normal t' ht'.1 x hxQ
  have hy2 : t' * y * t'⁻¹ ∈ Q := hQ.normal t' ht'.1 y hyQ
  have hh2 : t' * h * t⁻¹ ∈ pairStab G a b :=
    (pairStab G a b).mul_mem ((pairStab G a b).mul_mem ht' hh) ((pairStab G a b).inv_mem ht)
  obtain ⟨_, hheq, _⟩ := hQ.bruhat_unique hb hsb hxQ hh hyQ hx2 hh2 hy2 (hdec.symm.trans key)
  have hcomm' : t' * h = h * t' := hcomm _ ht' _ hh
  have : h = h * t' * t⁻¹ := by rw [← hcomm']; exact hheq
  have h3 : t' * t⁻¹ = 1 := by
    have := congrArg (h⁻¹ * ·) this
    simpa [mul_assoc] using this.symm
  have := congrArg (· * t) h3
  simpa using this

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
