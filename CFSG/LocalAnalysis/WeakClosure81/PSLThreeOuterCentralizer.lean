module

public import CFSG.LocalAnalysis.WeakClosure81.OuterInvolutionCentralizer
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IV
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphRed
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Orth3Mod
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11 CFSG.Blueprint Matrix Subgroup
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.KGroups.L3Eps
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups commutatorElement

theorem sigmaFacts_psl3_of_equiv
    {G : Type} [Group G] {L : Subgroup G} [L.Normal]
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcard : Nat.card K = p ^ f)
    (hf : Odd f) (hq : 5 ≤ p ^ f)
    (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (e : ↥L ≃* projectiveSL 3 K)
    {b : G} (hbL : b ∉ L) (hb2 : orderOf b = 2) :
    SecU1.SigmaFacts L b := by
  classical
  let σ : MulAut ↥L := MulAut.conjNormal b
  let β : MulAut (projectiveSL 3 K) := MulAut.congr e σ
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hσ2 : σ * σ = 1 := by
    ext x
    simp only [σ, MulAut.mul_apply, MulAut.one_apply, MulAut.conjNormal_apply]
    have hbinv : b⁻¹ * b⁻¹ = 1 := by rw [← _root_.mul_inv_rev, hbb, inv_one]
    calc b * (b * ↑x * b⁻¹) * b⁻¹ = (b * b) * ↑x * (b⁻¹ * b⁻¹) := by group
      _ = ↑x := by rw [hbb, hbinv]; group
  have hβ2 : β * β = 1 := by
    change MulAut.congr e σ * MulAut.congr e σ = 1
    rw [← map_mul, hσ2, map_one]
  have hout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL 3 K) := by
    intro hin
    apply hbL
    obtain ⟨g, hg⟩ := hin
    exact SecU1.L3I.mem_of_congr_eq_conj hC e (t := b) (by
      simpa [β, σ] using hg.symm)
  have hoddK : Odd (Nat.card K) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hoddK
  have hchar : ringChar K ≠ 2 := fun h => h2 (by
    have : CharP K 2 := h ▸ ringChar.charP K
    exact CharTwo.two_eq_zero)
  have hcard5 : 5 ≤ Nat.card K := by rw [hcard]; exact hq
  have hcard3 : Nat.card K ≠ 3 := by rw [hcard]; omega
  obtain ⟨A, hA, hβA⟩ := lin_involution_form hp hcard hf h2 hβ2 hout
  obtain ⟨N, hQ, hNfix, -, hNcomm, ⟨eN⟩⟩ :=
    CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3.lin_graph_centralizer_psl2
      hchar hcard3 hA
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hsimple : IsSimpleGroup ↥N := eN.isSimpleGroup
  have hperfect : Group.IsPerfect ↥N := hQ.1
  have hfixed : ∀ n ∈ N, MulAut.congr e σ n = n := by
    intro n hn
    change β n = n
    rw [hβA]
    exact hNfix n hn
  have hcomm : ∀ x y : projectiveSL 3 K, MulAut.congr e σ x = x →
      MulAut.congr e σ y = y → ⁅x, y⁆ ∈ N := by
    intro x y hx hy
    change β x = x at hx
    change β y = y at hy
    rw [hβA] at hx hy
    exact hNcomm x y hx hy
  have hcent : Subgroup.centralizer (N : Set (projectiveSL 3 K)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    set R : GL (Fin 3) K := A⁻¹ with hR
    have hRsymm : (R : Matrix (Fin 3) (Fin 3) K)ᵀ = R := transpose_inv_of_symm A hA
    set Ω : Subgroup SL(3, K) := omega3 R with hΩ
    have hΩperf : Group.IsPerfect ↥Ω := omega3_perfect hoddK hcard5 R hRsymm
    have hΩcomm : ∀ T : Matrix (Fin 3) (Fin 3) K,
        (∀ g ∈ Ω, T * (g : Matrix (Fin 3) (Fin 3) K) =
          (g : Matrix (Fin 3) (Fin 3) K) * T) →
          ∃ c : K, T = c • (1 : Matrix (Fin 3) (Fin 3) K) :=
      fun T hT => omega3_commutant hoddK hcard5 R hRsymm T hT
    set P : Subgroup (projectiveSL 3 K) := Ω.map (proj 3 K) with hP
    have hPfix : ∀ p ∈ P, β p = p := by
      intro p hp
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hp
      change β (proj 3 K g) = proj 3 K g
      rw [hβA]
      have hgΩ : g ∈ omega3 R := by rwa [hΩ] at hg
      have hgl : CFSG.ComponentClassification.Burgoyne.PSL.graphLift A g = g := by
        rw [CFSG.ComponentClassification.Burgoyne.PSL.graphLift_eq_iff]
        simpa [hR] using omega3_le_isometrySL R hgΩ
      rw [CFSG.ComponentClassification.Burgoyne.PSL.conjAut_mul_dualAut_proj, hgl]
    let πΩ : ↥Ω →* ↥P := (proj 3 K).subgroupMap Ω
    have hπΩ : Function.Surjective πΩ := MonoidHom.subgroupMap_surjective _ _
    haveI : Group.IsPerfect ↥Ω := hΩperf
    have hPperf : Group.IsPerfect ↥P :=
      Group.IsPerfect.ofSurjective (f := πΩ) hπΩ
    have hNcommβ : ∀ x y : projectiveSL 3 K, β x = x → β y = y → ⁅x, y⁆ ∈ N := by
      intro x y hx hy
      rw [hβA] at hx hy
      exact hNcomm x y hx hy
    have hP_le_N : P ≤ N := by
      calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.mp hPperf).symm
        _ ≤ N := by
          rw [Subgroup.commutator_le]
          intro p hp q hq
          exact hNcommβ p q (hPfix p hp) (hPfix q hq)
    have hyP : ∀ p ∈ P, p * y = y * p := by
      intro p hp
      exact Subgroup.mem_centralizer_iff.mp hy p (hP_le_N hp)
    obtain ⟨g, hg⟩ := proj_surjective 3 K y
    have hgcomm : ∀ h ∈ Ω, proj 3 K g * proj 3 K h = proj 3 K h * proj 3 K g := by
      intro h hh
      rw [hg]
      exact (hyP (proj 3 K h) (Subgroup.mem_map_of_mem _ hh)).symm
    have hproj : proj 3 K g = 1 := fl3g_proj_eq_one_of_commute hΩperf hΩcomm hgcomm
    rw [hg] at hproj
    exact hproj
  exact sigmaFacts_of_fixed_perfect_model e hsimple hperfect hfixed hcomm hcent

theorem sigmaFacts_psl3_outer
    {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hAS : SecE3.AlmostSimple L)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : Odd f) (hq : 5 ≤ p ^ f)
    (hL : LieModel ↥L .PSL 3 p f)
    {b : G} (hbL : b ∉ L) (hb2 : orderOf b = 2) :
    SecU1.SigmaFacts L b := by
  obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.ClassicalInvolution.Q3.TL4.E3C269G.exists_projectiveSL_equiv hL
  letI : Field K := hKfld
  letI : Finite K := hKfin
  exact sigmaFacts_psl3_of_equiv hp hp2 hKcard hf hq hAS.centralizer_eq e hbL hb2

end CFSG.LocalAnalysis.WeakClosure81

end
