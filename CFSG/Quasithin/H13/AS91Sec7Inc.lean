module

public import CFSG.Quasithin.H13.AS91Sec3XiKappa
public import CFSG.Quasithin.H13.AS91Sec5Tri
public import CFSG.Quasithin.H13.AS91Sec7Res

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace M24G


theorem exists_smul_fix_trio_sextet {l U U' : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hU : IsSextet U) (hU' : IsSextet U') (hlU : TrioIn l U) (hlU' : TrioIn l U') :
    ∃ g ∈ M24g, g • l = l ∧ g • U = U' := by
  obtain ⟨a, ha, haU⟩ := sextet_transitive hU
  obtain ⟨b, hb, hbU⟩ := sextet_transitive hU'
  set g := b⁻¹ * a with hg
  have hgm : g ∈ M24g := mul_mem (inv_mem hb) ha
  have hgU : g • U = U' := by rw [hg, mul_smul, haU, ← hbU, inv_smul_smul]
  have hgl : TrioIn (g • l) U' := by
    rw [← hgU]
    exact (trioIn_smul_iff g).2 hlU
  obtain ⟨k, hk, hkU, hkl⟩ := kappa_orbit hU' ((isTrio_smul_iff hgm).2 hl) hl
    (i := 0) hgl hlU'
  refine ⟨k * g, mul_mem hk hgm, by rw [mul_smul, hkl], by rw [mul_smul, hgU, hkU]⟩

end M24G

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem exists_flag_of_cInc {m : G ⧸ c.G2} {σ : G ⧸ c.G3} (hm : CInc c.G1 c.G2 c.x0 m)
    (hmσ : CInc c.G2 c.G3 m σ) : ∃ k : ↥c.G1, (k : G) • c.l0 = m ∧ (k : G) • c.pi0 = σ := by
  obtain ⟨h, rfl⟩ := c.exists_G1_smul_l0 hm
  obtain ⟨g, hg2, hg3⟩ := hmσ
  have ha : (h : G)⁻¹ * g ∈ c.G2 := by
    have e : ((g : G) : G ⧸ c.G2) = (h : G) • c.l0 := hg2
    rw [show (h : G) • c.l0 = (((h : G) : G) : G ⧸ c.G2) by
      simp [Loc49.l0, basePt, MulAction.Quotient.smul_mk]] at e
    rw [QuotientGroup.eq] at e
    rw [← inv_mem_iff]
    simpa using e
  obtain ⟨κ, hκ, s, hs, hκs⟩ := c.G2_eq_mul ha
  refine ⟨⟨(h : G) * κ, mul_mem h.2 (c.K_le_G1 hκ)⟩, ?_, ?_⟩
  · show ((h : G) * κ) • c.l0 = (h : G) • c.l0
    rw [mul_smul]
    congr 1
    have := (c.smul_l0_eq_iff κ 1).2 (by simpa using inv_mem (c.K_le_G2 hκ))
    simpa using this
  · show ((h : G) * κ) • c.pi0 = σ
    rw [← hg3]
    have e : (h : G) * κ = g * s⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hκs, mul_inv_cancel_left]
    rw [e]
    simp only [Loc49.pi0, basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [QuotientGroup.eq]
    simpa using c.CZ_le_G3 hs

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)


theorem cInc_iff_trioIn {m : G ⧸ c.G2} {σ : G ⧸ c.G3} (hm : CInc c.G1 c.G2 c.x0 m)
    (hσ : CInc c.G1 c.G3 c.x0 σ) :
    CInc c.G2 c.G3 m σ ↔ M24G.TrioIn (ρ.trio m) (ρ.sext σ) := by
  constructor
  · intro hmσ
    obtain ⟨k, rfl, rfl⟩ := c.exists_flag_of_cInc hm hmσ
    rw [ρ.trio_smul, ρ.sext_smul]
    exact (M24G.trioIn_smul_iff _).2 ρ.trioIn_l₀_U₀
  · intro hin
    obtain ⟨h, rfl⟩ := c.exists_G1_smul_l0 hm
    obtain ⟨h', rfl⟩ := c.exists_G1_smul_pi0 hσ
    rw [ρ.trio_smul, ρ.sext_smul] at hin
    have hin' : M24G.TrioIn ρ.l₀ (ρ.φ (h⁻¹ * h') • ρ.U₀) := by
      have := (M24G.trioIn_smul_iff (ρ.φ h⁻¹)).2 hin
      rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, ← mul_smul, ← map_mul]
        at this
    obtain ⟨τ, hτ, hτl, hτU⟩ := M24G.exists_smul_fix_trio_sextet ρ.isTrio_l₀ ρ.isSextet_U₀
      ((M24G.isSextet_smul_iff (ρ.φ_mem _)).2 ρ.isSextet_U₀) ρ.trioIn_l₀_U₀ hin'
    obtain ⟨t, rfl⟩ := ρ.exists_φ_eq hτ
    have ht2 : (t : G) ∈ c.G2 := (ρ.stab₂ t).2 hτl
    have ht3 : ((t⁻¹ * (h⁻¹ * h') : ↥c.G1) : G) ∈ c.G3 := by
      rw [ρ.stab₃, map_mul, mul_smul, ← hτU, ← mul_smul, ← map_mul, inv_mul_cancel, map_one,
        one_smul]
    refine ⟨(h : G) * t, ?_, ?_⟩
    · show (((h : G) * t : G) : G ⧸ c.G2) = (h : G) • c.l0
      simp only [Loc49.l0, basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      rw [QuotientGroup.eq]
      simpa using inv_mem ht2
    · show (((h : G) * t : G) : G ⧸ c.G3) = (h' : G) • c.pi0
      simp only [Loc49.pi0, basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using ht3

theorem coplanar_iff {m n : G ⧸ c.G2} (hm : CInc c.G1 c.G2 c.x0 m)
    (hn : CInc c.G1 c.G2 c.x0 n) :
    (∃ σ, CInc c.G2 c.G3 m σ ∧ CInc c.G2 c.G3 n σ) ↔
      M24G.Coplanar (ρ.trio m) (ρ.trio n) := by
  constructor
  · rintro ⟨σ, hmσ, hnσ⟩
    have hσ : CInc c.G1 c.G3 c.x0 σ := c.inc_pt_plane hm hmσ
    exact ⟨ρ.sext σ, ρ.isSextet_sext hσ, (ρ.cInc_iff_trioIn hm hσ).1 hmσ,
      (ρ.cInc_iff_trioIn hn hσ).1 hnσ⟩
  · rintro ⟨U, hU, hmU, hnU⟩
    obtain ⟨a, ha, haU⟩ := M24G.sextet_transitive hU
    obtain ⟨b, hb, hbU⟩ := M24G.sextet_transitive ρ.isSextet_U₀
    obtain ⟨σ, hσ, hσU⟩ := ρ.exists_sext_eq (σ := a⁻¹ * b) (mul_mem (inv_mem ha) hb)
    have hU' : ρ.sext σ = U := by rw [hσU, mul_smul, hbU, ← haU, inv_smul_smul]
    refine ⟨σ, (ρ.cInc_iff_trioIn hm hσ).2 (hU' ▸ hmU), (ρ.cInc_iff_trioIn hn hσ).2 (hU' ▸ hnU)⟩

theorem coplanar_iff_at {g : G} {a : G ⧸ c.G1} (hg : g • c.x0 = a) {m n : G ⧸ c.G2}
    (hm : CInc c.G1 c.G2 a m) (hn : CInc c.G1 c.G2 a n) :
    (∃ σ, CInc c.G2 c.G3 m σ ∧ CInc c.G2 c.G3 n σ) ↔
      M24G.Coplanar (ρ.trio (g⁻¹ • m)) (ρ.trio (g⁻¹ • n)) := by
  have hm' : CInc c.G1 c.G2 c.x0 (g⁻¹ • m) := by
    rw [← cInc_smul c.G1 c.G2 g, smul_inv_smul, hg]
    exact hm
  have hn' : CInc c.G1 c.G2 c.x0 (g⁻¹ • n) := by
    rw [← cInc_smul c.G1 c.G2 g, smul_inv_smul, hg]
    exact hn
  rw [← ρ.coplanar_iff hm' hn']
  constructor
  · rintro ⟨σ, h1, h2⟩
    refine ⟨g⁻¹ • σ, ?_, ?_⟩
    · rw [← cInc_smul c.G2 c.G3 g, smul_inv_smul, smul_inv_smul]
      exact h1
    · rw [← cInc_smul c.G2 c.G3 g, smul_inv_smul, smul_inv_smul]
      exact h2
  · rintro ⟨σ, h1, h2⟩
    refine ⟨g • σ, ?_, ?_⟩
    · rw [← smul_inv_smul g m, cInc_smul]
      exact h1
    · rw [← smul_inv_smul g n, cInc_smul]
      exact h2

end ResM24

end CFSG.Quasithin.H13.AS91
