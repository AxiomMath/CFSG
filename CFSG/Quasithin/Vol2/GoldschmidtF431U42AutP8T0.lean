module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Z

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem invL_mem_Thl : ∀ k < 43, invL k ∈ Thl := by decide +kernel

@[expose] def zt (k : ℕ) : Bool := invTgt.getD k 0 == 0 || invTgt.getD k 0 == 3

section Model


@[expose] noncomputable def ivA (k : ℕ) : Ah :=
  if hk : invL k ∈ Thl then Classical.choose (exists_That_of_mem_Thl hk) else 1

theorem ivA_spec {k : ℕ} (hk : k < 43) : ivA k ∈ That ∧ RepL (invL k) ((ivA k : Ah) : P45) := by
  have h := invL_mem_Thl k hk
  simp only [ivA, h, ↓reduceDIte]
  exact Classical.choose_spec (exists_That_of_mem_Thl h)

theorem ivA_inj {j k : ℕ} (hj : j < 43) (hk : k < 43) (h : ivA j = ivA k) : j = k := by
  have h1 := (ivA_spec hj).2
  have h2 := (ivA_spec hk).2
  rw [h] at h1
  exact invL_inj j hj k hk (repL_unique h1 h2)

theorem ivA_sq {k : ℕ} (hk : k < 43) : ivA k * ivA k = 1 := by
  have h := (ivA_spec hk).2
  have h2 : RepL (compL (invL k) (invL k)) ((1 : Ah) : P45) := by
    have e : compL (invL k) (invL k) = idL := (inv_check.1 k hk).1
    rw [e]
    exact repL_one 45
  exact Subtype.ext (eq_of_repL (repL_mul h h) h2)

theorem ivA_ne_one {k : ℕ} (hk : k < 43) : ivA k ≠ 1 := by
  intro h1
  have h := (ivA_spec hk).2
  rw [h1] at h
  exact (inv_check.1 k hk).2.1 (repL_unique h (repL_one 45))

theorem exists_ivA {u : Ah} (hu : u ∈ That) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ k < 43, u = ivA k := by
  obtain ⟨k, hk, hrep, -⟩ := inv_type hu hu2 hu1
  exact ⟨k, hk, Subtype.ext (eq_of_repL hrep (ivA_spec hk).2)⟩

theorem ivA_comm_iff {j k : ℕ} (hj : j < 43) (hk : k < 43) :
    ivA j * ivA k = ivA k * ivA j ↔ comp (invL j) (invL k) = comp (invL k) (invL j) := by
  constructor
  · intro h
    have h1 := repL_mul (ivA_spec hj).2 (ivA_spec hk).2
    have h2 := repL_mul (ivA_spec hk).2 (ivA_spec hj).2
    have h3 : RepL (comp (invL j) (invL k)) (((ivA k * ivA j : Ah)) : P45) := by
      rw [← h]
      exact h1
    exact repL_unique h3 h2
  · intro h
    apply Subtype.ext
    apply eq_of_repL (repL_mul (ivA_spec hj).2 (ivA_spec hk).2)
    have h' : compL (invL j) (invL k) = compL (invL k) (invL j) := h
    rw [h']
    exact repL_mul (ivA_spec hk).2 (ivA_spec hj).2

theorem ivA_type {k : ℕ} (hk : k < 43) :
    ∃ g : Ah, (g ∈ P1h ∨ g ∈ P2h) ∧ g * ivA k * g⁻¹ = repA (invTgt.getD k 0) := by
  obtain ⟨k', hk', hrep, g, hg, hgeq⟩ := inv_type (ivA_spec hk).1 (ivA_sq hk) (ivA_ne_one hk)
  have : k' = k := invL_inj k' hk' k hk (repL_unique hrep (ivA_spec hk).2)
  subst this
  exact ⟨g, hg, hgeq⟩

end Model

section InG

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

@[expose] noncomputable def ivB (k : ℕ) : ↥Bh :=
  if hk : k < 43 then ⟨ivA k, That_le_Bh (ivA_spec hk).1⟩ else 1

@[expose] noncomputable def ivG (c : AutCtx G M₁ M₂ z) (k : ℕ) : G := c.iso.toG (ivB k)

variable (c : AutCtx G M₁ M₂ z)

theorem ivB_coe {k : ℕ} (hk : k < 43) : ((ivB k : ↥Bh) : Ah) = ivA k := by
  simp only [ivB, hk, ↓reduceDIte]

theorem ivG_mem_T₀ {k : ℕ} (hk : k < 43) : ivG c k ∈ c.iso.imgG That :=
  c.iso.mem_imgG.2 ⟨ivB k, by rw [ivB_coe hk]; exact (ivA_spec hk).1, rfl⟩

theorem ivG_sq {k : ℕ} (hk : k < 43) : ivG c k * ivG c k = 1 := by
  have : ivB k * ivB k = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ivB_coe hk]; exact ivA_sq hk)
  rw [ivG, ← AutIso.toG_mul, this, AutIso.toG_one]

theorem ivG_ne_one {k : ℕ} (hk : k < 43) : ivG c k ≠ 1 := by
  intro h1
  have : ivB k = 1 := c.iso.toG_injective (by rw [← ivG, h1, AutIso.toG_one])
  exact ivA_ne_one hk (by rw [← ivB_coe hk, this]; rfl)

theorem ivG_inj {j k : ℕ} (hj : j < 43) (hk : k < 43) (h : ivG c j = ivG c k) : j = k := by
  have h1 : ivB j = ivB k := c.iso.toG_injective h
  apply ivA_inj hj hk
  rw [← ivB_coe hj, ← ivB_coe hk, h1]

theorem exists_ivG {y : G} (hy : y ∈ c.iso.imgG That) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ k < 43, ivG c k = y := by
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hy
  have hb2 : (b : Ah) * b = 1 := by
    have : b * b = 1 := c.iso.toG_injective (by rw [AutIso.toG_mul, AutIso.toG_one]; exact hy2)
    exact congrArg Subtype.val this
  have hb1 : (b : Ah) ≠ 1 := by
    intro h1
    apply hy1
    have : b = 1 := Subtype.ext h1
    rw [this, AutIso.toG_one]
  obtain ⟨k, hk, hkb⟩ := exists_ivA hb hb2 hb1
  refine ⟨k, hk, ?_⟩
  have : ivB k = b := Subtype.ext (by rw [ivB_coe hk]; exact hkb.symm)
  rw [ivG, this]

theorem ivG_comm_iff {j k : ℕ} (hj : j < 43) (hk : k < 43) :
    ivG c j * ivG c k = ivG c k * ivG c j ↔ comp (invL j) (invL k) = comp (invL k) (invL j) := by
  rw [← ivA_comm_iff hj hk]
  constructor
  · intro h
    rw [ivG, ivG, ← AutIso.toG_mul, ← AutIso.toG_mul] at h
    have h1 := c.iso.toG_injective h
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_mul, ivB_coe hj, ivB_coe hk] using h2
  · intro h
    rw [ivG, ivG, ← AutIso.toG_mul, ← AutIso.toG_mul]
    congr 1
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, ivB_coe hj, ivB_coe hk] using h

end InG

end CFSG.Quasithin.H13.F431.U42Aut
