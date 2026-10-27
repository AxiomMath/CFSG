module

public import CFSG.Quasithin.H13.AS91Sec3Invariance
public import CFSG.Quasithin.H13.AS91Sec5Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

structure ResM24 {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z) where
  φ : ↥c.G1 →* Equiv.Perm (Fin 24)
  range_eq : φ.range = M24g
  ker_eq : φ.ker = c.E.subgroupOf c.G1
  l₀ : Finset (Finset (Fin 24))
  U₀ : Finset (Finset (Fin 24))
  isTrio_l₀ : IsTrio l₀
  isSextet_U₀ : IsSextet U₀
  trioIn_l₀_U₀ : M24G.TrioIn l₀ U₀
  stab₂ : ∀ h : ↥c.G1, (h : G) ∈ c.G2 ↔ φ h • l₀ = l₀
  stab₃ : ∀ h : ↥c.G1, (h : G) ∈ c.G3 ↔ φ h • U₀ = U₀

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem exists_G1_smul_l0 {m : G ⧸ c.G2} (hm : CInc c.G1 c.G2 c.x0 m) :
    ∃ h : ↥c.G1, (h : G) • c.l0 = m := by
  obtain ⟨g, hg1, rfl⟩ := hm
  have hg : g ∈ c.G1 := by
    have h' : ((g : G) : G ⧸ c.G1) = ((1 : G) : G ⧸ c.G1) := hg1
    rw [QuotientGroup.eq] at h'
    simpa using h'
  exact ⟨⟨g, hg⟩, by simp [MulAction.Quotient.smul_mk]⟩

theorem exists_G1_smul_pi0 {σ : G ⧸ c.G3} (hσ : CInc c.G1 c.G3 c.x0 σ) :
    ∃ h : ↥c.G1, (h : G) • c.pi0 = σ := by
  obtain ⟨g, hg1, rfl⟩ := hσ
  have hg : g ∈ c.G1 := by
    have h' : ((g : G) : G ⧸ c.G1) = ((1 : G) : G ⧸ c.G1) := hg1
    rw [QuotientGroup.eq] at h'
    simpa using h'
  exact ⟨⟨g, hg⟩, by simp [MulAction.Quotient.smul_mk]⟩

theorem cInc_x0_smul_l0 (h : ↥c.G1) : CInc c.G1 c.G2 c.x0 ((h : G) • c.l0) := by
  refine ⟨h, ?_, by simp [MulAction.Quotient.smul_mk]⟩
  show ((h : G) : G ⧸ c.G1) = ((1 : G) : G ⧸ c.G1)
  rw [QuotientGroup.eq]
  simpa using h.2

theorem cInc_x0_smul_pi0 (h : ↥c.G1) : CInc c.G1 c.G3 c.x0 ((h : G) • c.pi0) := by
  refine ⟨h, ?_, by simp [MulAction.Quotient.smul_mk]⟩
  show ((h : G) : G ⧸ c.G1) = ((1 : G) : G ⧸ c.G1)
  rw [QuotientGroup.eq]
  simpa using h.2

theorem smul_l0_eq_iff (h h' : G) : h • c.l0 = h' • c.l0 ↔ h⁻¹ * h' ∈ c.G2 := by
  simp only [Loc49.l0, basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  exact QuotientGroup.eq

theorem smul_pi0_eq_iff (h h' : G) : h • c.pi0 = h' • c.pi0 ↔ h⁻¹ * h' ∈ c.G3 := by
  simp only [Loc49.pi0, basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  exact QuotientGroup.eq

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

theorem φ_mem (h : ↥c.G1) : ρ.φ h ∈ M24g := ρ.range_eq ▸ MonoidHom.mem_range.2 ⟨h, rfl⟩

theorem exists_φ_eq {σ : S24} (hσ : σ ∈ M24g) : ∃ h : ↥c.G1, ρ.φ h = σ := by
  rw [← ρ.range_eq] at hσ
  exact hσ

theorem φ_smul_l₀_eq_iff (h h' : ↥c.G1) :
    ρ.φ h • ρ.l₀ = ρ.φ h' • ρ.l₀ ↔ (h : G) • c.l0 = (h' : G) • c.l0 := by
  have e : ρ.φ h • ρ.l₀ = ρ.φ h' • ρ.l₀ ↔ ρ.φ (h⁻¹ * h') • ρ.l₀ = ρ.l₀ := by
    rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff, eq_comm]
  rw [e, ← ρ.stab₂, c.smul_l0_eq_iff]
  simp

theorem φ_smul_U₀_eq_iff (h h' : ↥c.G1) :
    ρ.φ h • ρ.U₀ = ρ.φ h' • ρ.U₀ ↔ (h : G) • c.pi0 = (h' : G) • c.pi0 := by
  have e : ρ.φ h • ρ.U₀ = ρ.φ h' • ρ.U₀ ↔ ρ.φ (h⁻¹ * h') • ρ.U₀ = ρ.U₀ := by
    rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff, eq_comm]
  rw [e, ← ρ.stab₃, c.smul_pi0_eq_iff]
  simp

open Classical in
@[expose] noncomputable def trio (m : G ⧸ c.G2) : Finset (Finset (Fin 24)) :=
  if hm : ∃ h : ↥c.G1, (h : G) • c.l0 = m then ρ.φ hm.choose • ρ.l₀ else ∅

open Classical in
@[expose] noncomputable def sext (σ : G ⧸ c.G3) : Finset (Finset (Fin 24)) :=
  if hσ : ∃ h : ↥c.G1, (h : G) • c.pi0 = σ then ρ.φ hσ.choose • ρ.U₀ else ∅

theorem trio_smul (h : ↥c.G1) : ρ.trio ((h : G) • c.l0) = ρ.φ h • ρ.l₀ := by
  have hex : ∃ h' : ↥c.G1, (h' : G) • c.l0 = (h : G) • c.l0 := ⟨h, rfl⟩
  rw [trio, dif_pos hex]
  exact (ρ.φ_smul_l₀_eq_iff _ _).2 hex.choose_spec

theorem sext_smul (h : ↥c.G1) : ρ.sext ((h : G) • c.pi0) = ρ.φ h • ρ.U₀ := by
  have hex : ∃ h' : ↥c.G1, (h' : G) • c.pi0 = (h : G) • c.pi0 := ⟨h, rfl⟩
  rw [sext, dif_pos hex]
  exact (ρ.φ_smul_U₀_eq_iff _ _).2 hex.choose_spec

theorem trio_l0 : ρ.trio c.l0 = ρ.l₀ := by
  have h := ρ.trio_smul 1
  simpa using h

theorem sext_pi0 : ρ.sext c.pi0 = ρ.U₀ := by
  have h := ρ.sext_smul 1
  simpa using h

theorem isTrio_trio {m : G ⧸ c.G2} (hm : CInc c.G1 c.G2 c.x0 m) : IsTrio (ρ.trio m) := by
  obtain ⟨h, rfl⟩ := c.exists_G1_smul_l0 hm
  rw [ρ.trio_smul]
  exact (M24G.isTrio_smul_iff (ρ.φ_mem h)).2 ρ.isTrio_l₀

theorem isSextet_sext {σ : G ⧸ c.G3} (hσ : CInc c.G1 c.G3 c.x0 σ) : IsSextet (ρ.sext σ) := by
  obtain ⟨h, rfl⟩ := c.exists_G1_smul_pi0 hσ
  rw [ρ.sext_smul]
  exact (M24G.isSextet_smul_iff (ρ.φ_mem h)).2 ρ.isSextet_U₀

theorem trio_smul_line (h : ↥c.G1) {m : G ⧸ c.G2} (hm : CInc c.G1 c.G2 c.x0 m) :
    ρ.trio ((h : G) • m) = ρ.φ h • ρ.trio m := by
  obtain ⟨h', rfl⟩ := c.exists_G1_smul_l0 hm
  rw [← mul_smul, ← Subgroup.coe_mul, ρ.trio_smul, ρ.trio_smul, map_mul, mul_smul]

theorem trio_injOn {m m' : G ⧸ c.G2} (hm : CInc c.G1 c.G2 c.x0 m)
    (hm' : CInc c.G1 c.G2 c.x0 m') (h : ρ.trio m = ρ.trio m') : m = m' := by
  obtain ⟨h₁, rfl⟩ := c.exists_G1_smul_l0 hm
  obtain ⟨h₂, rfl⟩ := c.exists_G1_smul_l0 hm'
  rw [ρ.trio_smul, ρ.trio_smul] at h
  exact (ρ.φ_smul_l₀_eq_iff _ _).1 h

theorem sext_injOn {σ σ' : G ⧸ c.G3} (hσ : CInc c.G1 c.G3 c.x0 σ)
    (hσ' : CInc c.G1 c.G3 c.x0 σ') (h : ρ.sext σ = ρ.sext σ') : σ = σ' := by
  obtain ⟨h₁, rfl⟩ := c.exists_G1_smul_pi0 hσ
  obtain ⟨h₂, rfl⟩ := c.exists_G1_smul_pi0 hσ'
  rw [ρ.sext_smul, ρ.sext_smul] at h
  exact (ρ.φ_smul_U₀_eq_iff _ _).1 h

theorem exists_trio_eq {σ : S24} (hσ : σ ∈ M24g) :
    ∃ m, CInc c.G1 c.G2 c.x0 m ∧ ρ.trio m = σ • ρ.l₀ := by
  obtain ⟨h, rfl⟩ := ρ.exists_φ_eq hσ
  exact ⟨_, c.cInc_x0_smul_l0 h, ρ.trio_smul h⟩

theorem exists_sext_eq {σ : S24} (hσ : σ ∈ M24g) :
    ∃ p, CInc c.G1 c.G3 c.x0 p ∧ ρ.sext p = σ • ρ.U₀ := by
  obtain ⟨h, rfl⟩ := ρ.exists_φ_eq hσ
  exact ⟨_, c.cInc_x0_smul_pi0 h, ρ.sext_smul h⟩

end ResM24

end CFSG.Quasithin.H13.AS91
