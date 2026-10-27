module

public import CFSG.Quasithin.MS93.S5Q2X52Coc

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512H

section Sp

open MSP

variable {F : Type} [Field F]

theorem mem_of_forall_form_smul_mem {p : Submodule F (V4 F)} (hp : IsPoint p) {w : V4 F}
    (hw : ∀ v ∈ perp p, form F v w • v ∈ p) : w ∈ p := by
  by_contra hwp
  have h1 : w ∉ perp (perp p) := by rwa [perp_perp]
  rw [mem_perp] at h1
  push Not at h1
  obtain ⟨v₀, hv₀, hv₀w⟩ := h1
  have hlt : ¬ perp p ≤ p := by
    intro hle
    have h2 := Submodule.finrank_mono hle
    have h3 := finrank_perp p
    rw [show Module.finrank F p = 1 from hp] at h2 h3
    omega
  obtain ⟨v₁, hv₁, hv₁p⟩ := Set.not_subset.1 hlt
  have key : ∀ v ∈ perp p, form F v w ≠ 0 → v ∈ p := fun v hv hne =>
    (Submodule.smul_mem_iff p hne).1 (hw v hv)
  by_cases h₀ : v₀ ∈ p
  · by_cases h₁ : form F v₁ w = 0
    · have hne : form F (v₁ + v₀) w ≠ 0 := by
        rw [map_add, LinearMap.add_apply, h₁, zero_add]
        exact hv₀w
      exact hv₁p ((Submodule.add_mem_iff_left p h₀).1 (key _ (add_mem hv₁ hv₀) hne))
    · exact hv₁p (key v₁ hv₁ h₁)
  · exact h₀ (key v₀ hv₀ hv₀w)

theorem cocycle_mem_of_mem_xPoint {φ : Sp4 F → V4 F}
    (hφ : ∀ g g', φ (g * g') = φ g + mat g *ᵥ φ g') {p : Submodule F (V4 F)} (hp : IsPoint p)
    {t : Sp4 F} (ht : t ∈ xPoint p) : φ t ∈ p := by
  refine mem_of_forall_form_smul_mem hp fun v hv => ?_
  set s := transv v 1 with hs
  have hcomm : s * t = t * s := by
    have e := transv_conj t v 1
    rw [mem_fixer.1 ht v hv] at e
    rw [← hs] at e
    calc s * t = t * s * t⁻¹ * t := by rw [e]
      _ = t * s := by group
  have h1 := hφ s t
  have h2 := hφ t s
  rw [hcomm, h2] at h1
  have h3 : mat s *ᵥ φ t - φ t = mat t *ᵥ φ s - φ s := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm (mat s *ᵥ φ t), ← h1, add_comm]
  have h4 : mat s *ᵥ φ t - φ t = form F v (φ t) • v := by
    rw [hs, transv_mulVec, one_mul, add_sub_cancel_left]
  rw [← h4, h3]
  exact sub_mem_of_mem_fixer_perp ht (φ s)

end Sp

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem uCoord_comm_mem_of_xPoint (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (nv : S5.NatVec M T L a) {x : G} (hx : x ∈ S5Q2.X52.xFix h) {p : Submodule F (MSP.V4 F)}
    (hp : MSP.IsPoint p) {z : G} (hz : z ∈ M) (hzp : a ⟨z, hz⟩ ∈ MSP.xPoint p) :
    S5.uCoord nv ⁅z, x⁆ ∈ p := by
  have hφ := S5.cocSp_mul hd h nv hx.1 hx.2
  rw [← S5.cocSp_a hd h nv hx.1 hx.2 hz]
  exact cocycle_mem_of_mem_xPoint hφ hp hzp

theorem commutator_mem_zq_of_xPoint (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) {x : G} (hx : x ∈ S5Q2.X52.xFix h)
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) {z : G} (hz : z ∈ M)
    (hzp : a ⟨z, hz⟩ ∈ MSP.xPoint p) {Q : Subgroup G} (hQM : Q ≤ M)
    (hpQ : p ⊓ MSP.fixSp (S5.imSp a Q) = ⊥)
    (hzx : ⁅z, x⁆ ∈ Subgroup.centralizer (Q : Set G)) : ⁅z, x⁆ ∈ Zq M L := by
  obtain ⟨nv⟩ := S5.IsSp4Data.nonempty_natVec hd
  have hmem := uCoord_comm_mem_of_xPoint h hd nv hx hp hz hzp
  obtain ⟨u, hu, c, hc, e⟩ := (S5.mem_Uq_sup_cXL h).1 (hx.2 z hz)
  rw [← e, S5.uCoord_mul nv hu hc] at hmem
  have hcQ : c ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.centralizer_le hQM (hZc hc)
  have huQ : u ∈ Subgroup.centralizer (Q : Set G) := by
    have e2 : u = ⁅z, x⁆ * c⁻¹ := by rw [← e, mul_inv_cancel_right]
    rw [e2]
    exact mul_mem hzx (inv_mem hcQ)
  have hfix := nv.vec_mem_fixSp ⟨u, hu⟩ huQ
  have h0 : nv.vec ⟨u, hu⟩ = 0 := by
    have : nv.vec ⟨u, hu⟩ ∈ p ⊓ MSP.fixSp (S5.imSp a Q) := ⟨hmem, hfix⟩
    rwa [hpQ, Submodule.mem_bot] at this
  have huL := (nv.vec_eq_zero_iff ⟨u, hu⟩).1 h0
  rw [← e]
  exact mul_mem ⟨h.Uq_le_Xq hu, huL⟩ hc

end S512H

end CFSG.Quasithin.MS93
