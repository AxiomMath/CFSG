module

public import CFSG.RankThree.GF2n.Smith81.S81BNBeta
public import CFSG.RankThree.GF2n.Smith81.S81BNNorm
public import CFSG.RankThree.GF2n.Smith81.S81BW2E3L

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube

section Isometry

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ψ : M₀.E ≃ₗ[K] Cube K}

private theorem lgen_le_H0' (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ H0 M Z := by
  unfold Lgen
  refine iSup₂_le fun m hm x hx => ?_
  have hy : m⁻¹ * x * m ∈ H0 M Z := hc.LB_le_H0 (mem_conjSubgroup.mp hx)
  obtain ⟨hyM, hyC⟩ := hy
  have hxM : x ∈ M := by
    have h := M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)
    have hxe : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [hxe] at h
  refine ⟨hxM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hzm : m⁻¹ * z * m ∈ Z := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hm)) z).mp hz
    rwa [inv_inv] at h
  have hcomm := Subgroup.mem_centralizer_iff.mp hyC (m⁻¹ * z * m) hzm
  calc z * x = m * ((m⁻¹ * z * m) * (m⁻¹ * x * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * x * m) * (m⁻¹ * z * m)) * m⁻¹ := by rw [hcomm]
    _ = x * z := by group

theorem ActsOnQtAs.isometry (hg : GlobalModelData M Q Z γ M₀) {m : G}
    {T : Cube K ≃ₗ[K] Cube K} (hm : m ∈ H0 M Z) (h : ActsOnQtAs ψ m T) (u v : Cube K) :
    M₀.B (ψ.symm (T u)) (ψ.symm (T v)) = M₀.B (ψ.symm u) (ψ.symm v) := by
  obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.mp hm
  have hc : ∀ z ∈ Z, m * z * m⁻¹ = z := fun z hz => by
    have h1 := Subgroup.mem_centralizer_iff.mp hmC z hz
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  obtain ⟨T', hT', -, hB⟩ := hg.linear_of_centralizes hmM hc
  have hT₂ : ActsOnQtAs ψ m (ψ.symm.trans (T'.trans ψ)) := fun x hx => by
    simp [LinearEquiv.trans_apply, hT' x hx]
  have hEq : T = ψ.symm.trans (T'.trans ψ) := h.unique ψ hT₂
  rw [hEq]
  simpa [LinearEquiv.trans_apply] using hB (ψ.symm u) (ψ.symm v)

end Isometry

theorem smith24E3LFormStatement_holds : Smith24E3LFormStatement := by
  intro G _ _ M Q Z B IH hc h3L K _ _ γ M₀ hg ψ φ d
  have hctx : Ctx M Q Z B := hc.ctx
  let B' : Cube K →ₗ[K] Cube K →ₗ[K] K :=
    M₀.B.compl₁₂ (ψ.symm : Cube K →ₗ[K] M₀.E) (ψ.symm : Cube K →ₗ[K] M₀.E)
  have hB' : ∀ u v, B' u v = M₀.B (ψ.symm u) (ψ.symm v) := fun u v => rfl
  have hinv : ∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
      ∀ u v, B' (rho K g u) (rho K g v) = B' u v := by
    intro g hg1 u v
    have hgS : g ∈ StatedSL 6 K := CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hg1
    have hgG : rhoEquiv K g ∈ Gam K := Subgroup.mem_map_of_mem _ hgS
    rw [← d.range] at hgG
    obtain ⟨s, hs⟩ := hgG
    have hsH : (s : G) ∈ H0 M Z := lgen_le_H0' hctx s.2
    have h1 := (actsOnQtAs_phi d s).isometry hg hsH u v
    rw [hs] at h1
    simpa [hB', rhoEquiv_apply] using h1
  obtain ⟨lam, hlam⟩ := bilinear_eq_smul_beta B' hinv
  refine ⟨lam, ?_, fun e f => ?_⟩
  · intro h0
    have hzero : ∀ e f, M₀.B e f = 0 := fun e f => by
      have h1 := hlam (ψ e) (ψ f)
      simpa [hB', h0] using h1
    have hne : ψ.symm (p0 K) ≠ 0 := by
      intro h
      exact p0_ne_zero (by simpa using congrArg ψ h)
    exact hne (M₀.nondeg _ fun f => hzero _ f)
  · have h1 := hlam (ψ e) (ψ f)
    simpa [hB'] using h1

end CFSG.RankThree.GF2n.Smith81
