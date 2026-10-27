module

public import CFSG.Quasithin.H13.AS91Sec7Res
public import CFSG.Quasithin.H13.AS91Sec5More
public import CFSG.Quasithin.H13.AS91Sec3Delta
public import CFSG.Quasithin.H13.AS91Sec5Local

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem smul_x0_of_mem {h : G} (hh : h ∈ c.G1) : h • c.x0 = c.x0 := by
  show h • ((1 : G) : G ⧸ c.G1) = ((1 : G) : G ⧸ c.G1)
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  simpa using hh

theorem cInc_x0_smul {h : G} (hh : h ∈ c.G1) {n : G ⧸ c.G2} :
    CInc c.G1 c.G2 c.x0 (h • n) ↔ CInc c.G1 c.G2 c.x0 n := by
  conv_lhs => rw [← c.smul_x0_of_mem hh]
  exact cInc_smul c.G1 c.G2 h c.x0 n

theorem deltaSize_injective : Function.Injective deltaSize := by
  unfold deltaSize
  decide

theorem smul_mem_delta {g : G} (hg : g ∈ c.G1 ⊓ c.G2) (i : Fin 5) {n : G ⧸ c.G2} :
    g • n ∈ c.delta i ↔ n ∈ c.delta i := by
  have horb : MulAction.orbit ↥(c.G1 ⊓ c.G2) (g • n) = MulAction.orbit ↥(c.G1 ⊓ c.G2) n := by
    have := MulAction.orbit_smul (⟨g, hg⟩ : ↥(c.G1 ⊓ c.G2)) n
    rwa [Subgroup.mk_smul] at this
  simp only [delta, Set.mem_setOf_eq, horb, lnsX, mem_objOf]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h
    exact (c.cInc_x0_smul hg.1).1 h.symm'
      |>.symm'
  · intro h
    exact ((c.cInc_x0_smul hg.1).2 h.symm').symm'

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

theorem trio_image_orbit {n : G ⧸ c.G2} (hn : CInc c.G1 c.G2 c.x0 n) :
    ρ.trio '' MulAction.orbit ↥(c.G1 ⊓ c.G2) n =
      {k | ∃ σ ∈ M24g, σ • ρ.l₀ = ρ.l₀ ∧ σ • ρ.trio n = k} := by
  ext k
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    let h : ↥c.G1 := ⟨g, g.2.1⟩
    refine ⟨ρ.φ h, ρ.φ_mem h, (ρ.stab₂ h).1 g.2.2, ?_⟩
    show ρ.φ h • ρ.trio n = ρ.trio ((h : G) • n)
    exact (ρ.trio_smul_line h hn).symm
  · rintro ⟨σ, hσ, hσl, rfl⟩
    obtain ⟨h, rfl⟩ := ρ.exists_φ_eq hσ
    have h2 : (h : G) ∈ c.G2 := (ρ.stab₂ h).2 hσl
    refine ⟨(⟨h, h.2, h2⟩ : ↥(c.G1 ⊓ c.G2)) • n, ⟨_, rfl⟩, ?_⟩
    show ρ.trio ((h : G) • n) = ρ.φ h • ρ.trio n
    exact ρ.trio_smul_line h hn

theorem ncard_orbit_G12 {n : G ⧸ c.G2} (hn : CInc c.G1 c.G2 c.x0 n) :
    (MulAction.orbit ↥(c.G1 ⊓ c.G2) n).ncard =
      {k | ∃ σ ∈ M24g, σ • ρ.l₀ = ρ.l₀ ∧ σ • ρ.trio n = k}.ncard := by
  rw [← ρ.trio_image_orbit hn]
  refine (Set.InjOn.ncard_image ?_).symm
  rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩ he
  change ρ.trio ((g : G) • n) = ρ.trio ((g' : G) • n) at he
  change (g : G) • n = (g' : G) • n
  exact ρ.trio_injOn ((c.cInc_x0_smul g.2.1).2 hn) ((c.cInc_x0_smul g'.2.1).2 hn) he

section Cert


theorem orbit_eq_delta {t : Finset (Finset (Fin 24))} (ht : IsTrio t) {i : Fin 5}
    (hi : M24G.Delta ρ.l₀ t i) :
    {k | ∃ σ ∈ M24g, σ • ρ.l₀ = ρ.l₀ ∧ σ • t = k} = {k | IsTrio k ∧ M24G.Delta ρ.l₀ k i} := by
  ext k
  constructor
  · rintro ⟨σ, hσ, hσl, rfl⟩
    refine ⟨(M24G.isTrio_smul_iff hσ).2 ht, ?_⟩
    have := (M24G.delta_smul_iff hσ (l := ρ.l₀) (k := t) i).2 hi
    rwa [hσl] at this
  · rintro ⟨hk, hki⟩
    obtain ⟨g, hg, hgl, hgk⟩ := M24G.delta_orbit ρ.isTrio_l₀ ht hk hi hki
    exact ⟨g, hg, hgl, hgk⟩

theorem mem_delta_iff (i : Fin 5) {n : G ⧸ c.G2} :
    n ∈ c.delta i ↔ CInc c.G1 c.G2 c.x0 n ∧ M24G.Delta ρ.l₀ (ρ.trio n) i := by
  simp only [Loc49.delta, Set.mem_setOf_eq, Loc49.lnsX, mem_objOf]
  constructor
  · rintro ⟨hn, hcard⟩
    have hn' : CInc c.G1 c.G2 c.x0 n := hn.symm'
    refine ⟨hn', ?_⟩
    obtain ⟨j, hj, -⟩ := M24G.delta_existsUnique ρ.isTrio_l₀ (ρ.isTrio_trio hn')
    have hc := ρ.ncard_orbit_G12 hn'
    rw [ρ.orbit_eq_delta (ρ.isTrio_trio hn') hj, M24G.ncard_delta ρ.isTrio_l₀] at hc
    have hij : i = j := Loc49.deltaSize_injective (by rw [← hcard, hc]; rfl)
    rwa [hij]
  · rintro ⟨hn, hi⟩
    refine ⟨hn.symm', ?_⟩
    rw [ρ.ncard_orbit_G12 hn, ρ.orbit_eq_delta (ρ.isTrio_trio hn) hi,
      M24G.ncard_delta ρ.isTrio_l₀]
    rfl

theorem mem_deltaAt_iff (i : Fin 5) {g : G} {a : G ⧸ c.G1} (hg : g • c.x0 = a)
    {m n : G ⧸ c.G2} (hm : CInc c.G1 c.G2 a m) (hn : CInc c.G1 c.G2 a n) :
    n ∈ c.deltaAt i a m ↔ M24G.Delta (ρ.trio (g⁻¹ • m)) (ρ.trio (g⁻¹ • n)) i := by
  have hm' : CInc c.G1 c.G2 c.x0 (g⁻¹ • m) := by
    rw [← cInc_smul c.G1 c.G2 g, smul_inv_smul, hg]
    exact hm
  have hn' : CInc c.G1 c.G2 c.x0 (g⁻¹ • n) := by
    rw [← cInc_smul c.G1 c.G2 g, smul_inv_smul, hg]
    exact hn
  obtain ⟨h, hh⟩ := c.exists_G1_smul_l0 hm'
  have hx : (g * h) • c.x0 = a := by rw [mul_smul, c.smul_x0_of_mem h.2, hg]
  have hl : (g * h) • c.l0 = m := by rw [mul_smul, hh, smul_inv_smul]
  have key : ∀ g' : G, g' • c.x0 = a → g' • c.l0 = m →
      (g'⁻¹ • n ∈ c.delta i ↔ (g * h)⁻¹ • n ∈ c.delta i) := by
    intro g' hx' hl'
    have hmem : g'⁻¹ * (g * h) ∈ c.G1 ⊓ c.G2 := by
      refine ⟨?_, ?_⟩
      · have h1 : g'⁻¹ * (g * h) ∈ stabilizer G c.x0 := MulAction.mem_stabilizer_iff.2 (by
          rw [mul_smul, hx, ← hx', inv_smul_smul])
        rw [c.stab_x0] at h1
        exact h1
      · have : (g'⁻¹ * (g * h)) • c.l0 = c.l0 := by
          rw [mul_smul, hl, ← hl', inv_smul_smul]
        have h' := (c.smul_l0_eq_iff 1 (g'⁻¹ * (g * h))).1 (by rw [one_smul]; exact this.symm)
        rwa [inv_one, one_mul] at h'
    have e : g'⁻¹ • n = (g'⁻¹ * (g * h)) • ((g * h)⁻¹ • n) := by
      rw [← mul_smul]
      group
    rw [e, c.smul_mem_delta hmem]
  have htr : ρ.trio ((g * h)⁻¹ • n) = ρ.φ h⁻¹ • ρ.trio (g⁻¹ • n) := by
    have e : (g * h)⁻¹ • n = ((h⁻¹ : ↥c.G1) : G) • (g⁻¹ • n) := by
      rw [mul_inv_rev, mul_smul, Subgroup.coe_inv]
    rw [e, ρ.trio_smul_line h⁻¹ hn']
  have hl₀ : ρ.trio (g⁻¹ • m) = ρ.φ h • ρ.l₀ := by rw [← hh, ρ.trio_smul]
  constructor
  · rintro ⟨g', hx', hl', hd⟩
    have h1 := (ρ.mem_delta_iff i).1 ((key g' hx' hl').1 hd)
    rw [htr] at h1
    rw [hl₀, ← M24G.delta_smul_iff (ρ.φ_mem h⁻¹), ← mul_smul, ← map_mul, inv_mul_cancel,
      map_one, one_smul]
    exact h1.2
  · intro hd
    refine ⟨g * h, hx, hl, ?_⟩
    refine (ρ.mem_delta_iff i).2 ⟨?_, ?_⟩
    · rw [mul_inv_rev, mul_smul]
      exact (c.cInc_x0_smul (inv_mem h.2)).2 hn'
    · rw [htr]
      rw [hl₀, ← M24G.delta_smul_iff (ρ.φ_mem h⁻¹), ← mul_smul, ← map_mul, inv_mul_cancel,
        map_one, one_smul] at hd
      exact hd

end Cert

end ResM24

end CFSG.Quasithin.H13.AS91
