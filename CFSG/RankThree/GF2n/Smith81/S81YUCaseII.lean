module

public import CFSG.RankThree.GF2n.Smith81.S81UBridge
public import CFSG.RankThree.GF2n.Smith81.S81CTransvBase
public import CFSG.RankThree.GF2n.Smith81.S81LRoot
public import CFSG.RankThree.GF2n.Smith81.S81U6Transv
public import CFSG.RankThree.GF2n.Smith81.S81UInvol1
public import CFSG.RankThree.GF2n.Smith81.S81UTransport
public import CFSG.RankThree.GF2n.Smith81.TiRecognition

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  Matrix exteriorPower
  CFSG.RankThree.GF2n.Smith81.E3UBridge
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem isTransvec_tInv1_F : IsTransvec F (tInv1 F) := by
  have hk : ((tInv1 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      1 + Matrix.vecMulVec (Pi.single 0 1) (Pi.single 1 1) := by
    rw [tInv1, transvGL_val, Matrix.transvection]
    congr 1
    ext p q
    fin_cases p <;> fin_cases q <;> simp [Matrix.vecMulVec, Matrix.single_apply, Pi.single_apply]
  have hu : (Pi.single 0 1 : Fin 6 → F) ≠ 0 := by
    intro h
    simpa using congrFun h 0
  have hφ : (Pi.single 1 1 : Fin 6 → F) ≠ 0 := by
    intro h
    simpa using congrFun h 1
  have huφ : (Pi.single 1 1 : Fin 6 → F) ⬝ᵥ (Pi.single 0 1 : Fin 6 → F) = 0 := by
    rw [dotProduct_single]
    simp [Pi.single_apply]
  exact CFSG.RankThree.GF2n.Smith81.S81C.isTransvectionMat_of_vecMulVec hu hφ huφ hk

theorem isTransvec_tSU1 {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) :
    IsTransvec F ((tSU1 hσ hω : SUid σ 6) : GL (Fin 6) F) := by
  have h := isTransvec_conj (c := (CFSG.RankThree.GF2n.Smith81.U6Cube.frameGL σ ω hω)⁻¹)
    isTransvec_tInv1_F
  rw [inv_inv] at h
  exact h

theorem transvec_involModel12 {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (h4 : 4 ≤ 2 ^ f)
    {g : SUid (unitaryInvolution F 2 f) 6} (hg : IsTransvec F (g : GL (Fin 6) F)) :
    UInvolModel12 (unitaryInvolution F 2 f) g := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one (unitaryInvolution F 2 f))
  obtain ⟨h, hhS, hh⟩ := CFSG.RankThree.GF2n.Smith81.U6Cube.transvec_conj hσ (by norm_num)
    g.2 (tSU1 hσ hω).2 hg (isTransvec_tSU1 hσ hω)
  obtain ⟨H, hH⟩ : ∃ H : SUid (unitaryInvolution F 2 f) 6, (H : GL (Fin 6) F) = h :=
    ⟨⟨h, hhS⟩, rfl⟩
  have htS : tSU1 hσ hω = H * g * H⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hH]
    exact hh.symm
  have hk : UInvolModel12 (unitaryInvolution F 2 f) (H⁻¹ * tSU1 hσ hω * H⁻¹⁻¹) :=
    UInvolModel12.conj hσ H⁻¹ (involModel12_tSU1 hF h4 hω)
  have hkg : H⁻¹ * tSU1 hσ hω * H⁻¹⁻¹ = g := by
    rw [htS]
    group
  rw [hkg] at hk
  exact hk

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {X : Subgroup G} {x : G}

theorem u6_caseII {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (h4 : 4 ≤ 2 ^ f)
    (e : K ≃+* Fσ (unitaryInvolution F 2 f))
    {ψ : M₀.E ≃ₗ[K] E3UWspace (unitaryInvolution F 2 f) e}
    {φ : Lgen M (LB M Q B) →*
      (E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K] E3UWspace (unitaryInvolution F 2 f) e)}
    (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam (unitaryInvolution F 2 f) e)
      (e3uP0 (unitaryInvolution F 2 f) e) (e3uU0 (unitaryInvolution F 2 f) e))
    (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B))
    {g : SUid (unitaryInvolution F 2 f) 6} (hg : IsTransvec F (g : GL (Fin 6) F))
    (hφ : φ ⟨x, hxL⟩ = e3uWact (unitaryInvolution F 2 f) e g)
    (hNF : ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)) : CaseII Q Z x := by
  classical
  have hM : UInvolModel12 (unitaryInvolution F 2 f) g := transvec_involModel12 hF h4 hg
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  have hV0 : ∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g' ∈ Gcent (unitaryInvolution F 2 f) g,
      φ ⟨u, hu⟩ = e3uWact (unitaryInvolution F 2 f) e g'}, u ∈ H0 M Z := by
    rintro u ⟨hu, -⟩
    exact Lgen_le_H0 hc hu
  have hVx : ∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g' ∈ Gcent (unitaryInvolution F 2 f) g,
      φ ⟨u, hu⟩ = e3uWact (unitaryInvolution F 2 f) e g'}, ⁅u, x⁆ ∈ Q := by
    rintro u ⟨hu, g', hg', hφu⟩
    exact comm_mem_Q_of_lift_U d hxL hu hφ hφu hg'
  have hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0 :=
    qf_zero_of_coinv hD hs Tx _ hV0 hVx (covW_transport hc d hM.covW)
  rcases theta_dichotomy_of_coinv hD hs Tx hQf _ hV0 hVx
      (covC_transport hc d hxL Tx hφ hM.covC) with hI | hII
  · exfalso
    obtain ⟨w, hw, hw1, -⟩ := exists_mem_Z_ne hs.hyp (1 : G)
    obtain ⟨q, hq, hqw⟩ := hI w hw
    apply hNF w hw hw1
    refine isConj_iff.mpr ⟨q, ?_⟩
    have hxw : x * w = w * x := mul_inv_eq_iff_eq_mul.mp (hs.x_cent h12 w hw)
    calc q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
      _ = w * x := by rw [hqw]
      _ = x * w := hxw.symm
  · exact hII

end CFSG.RankThree.GF2n.Smith81.RootGenU
