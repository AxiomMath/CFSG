module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutQ2
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeRadical
public import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Two
import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSU
import CFSG.LocalAnalysis.StandardType.SURadicalVector
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearSU
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DE0
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure37Base
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.A3Structure37Frattini
import CFSG.Quasithin.Background.A3Structure37KeyBase
import CFSG.Quasithin.Background.A3Structure37Schur
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType.SUTransvection

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (aform)

private theorem heisData_map_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    {X P w F : M} (hH : HeisData M X P w F) :
    HeisData N (e X) (e P) (e w) (e F) where
  card := by
    rw [← hH.card]
    exact (Nat.card_congr e.toEquiv).symm
  w_central g := by
    simpa using congrArg e (hH.w_central (e.symm g))
  w_pow := by rw [← map_pow, hH.w_pow, map_one]
  w_ne h := hH.w_ne (e.injective (by simpa using h))
  X_pow := by rw [← map_pow, hH.X_pow, map_one]
  P_pow := by rw [← map_pow, hH.P_pow, map_one]
  XP := by simpa [map_mul] using congrArg e hH.XP
  FP := by simpa [map_mul, map_inv] using congrArg e hH.FP
  FX := by simpa [map_mul, map_inv] using congrArg e hH.FX
  F_pow := by rw [← map_pow, hH.F_pow, map_one]
  F_sq h := hH.F_sq (e.injective (by simpa using h))
  cent y h1 h2 := by
    have hy : e.symm y ∈ Subgroup.center M := by
      refine hH.cent (e.symm y) ?_ ?_
      · apply e.injective
        simpa using h1
      · apply e.injective
        simpa using h2
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    simpa using congrArg e (hy (e.symm g))
  center_le z hz := by
    rw [Subgroup.mem_center_iff] at hz
    have hzM : e.symm z ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      simpa using hz (e g)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hH.center_le (e.symm z) hzM)
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨k, by rw [← map_zpow, hk]; exact e.apply_symm_apply z⟩

private theorem exists_scalar_mat_conjEquiv {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {P : GL (Fin 3) F}
    (hP : conjTr (unitaryInvolution F 2 1) (P : Matrix (Fin 3) (Fin 3) F) *
      (P : Matrix (Fin 3) (Fin 3) F) = antidiag 3)
    {B : CFSG.Open.StatedSU 3 (2 ^ 1) F}
    (hB : (B : GL (Fin 3) F) ∈ CFSG.Open.StatedScalars (Fin 3) F) :
    ∃ c : F, mat (unitaryInvolution F 2 1) 3
      (((conjEquiv (σ := unitaryInvolution F 2 1) P hP).trans
        (MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := 1) hF 3))).symm B) =
      c • 1 := by
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hB
  refine ⟨(u : F), ?_⟩
  have hmat : mat (unitaryInvolution F 2 1) 3
      (((conjEquiv (σ := unitaryInvolution F 2 1) P hP).trans
        (MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := 1) hF 3))).symm B) =
      ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (B : GL (Fin 3) F) *
        (P : Matrix (Fin 3) (Fin 3) F) := by
    rw [mat_apply, MulEquiv.symm_trans_apply]
    rfl
  rw [hmat]
  have hBm : (B : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) u := hu.symm
  rw [hBm]
  have hunit : ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (P : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  rw [mul_assoc, Matrix.scalar_comm (u : F) (fun r => Commute.all _ _)
    (P : Matrix (Fin 3) (Fin 3) F), ← mul_assoc, hunit, one_mul]
  rw [Matrix.scalar_apply, smul_one_eq_diagonal]

theorem exists_heisData_SU_three {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) :
    ∃ X P w Fe : SU (unitaryInvolution F 2 1) 3,
      HeisData (SU (unitaryInvolution F 2 1) 3) X P w Fe ∧
        ∃ c : F, mat (unitaryInvolution F 2 1) 3 w = c • 1 := by
  obtain ⟨X, P, w, Fe, hH, hw⟩ := exists_heisData_statedSU_two (K := F) hF
  let P0 : GL (Fin 3) F := (exists_wittMatrix (p := 2) (f := 1) hF 3).choose
  have hP0 : conjTr (unitaryInvolution F 2 1) (P0 : Matrix (Fin 3) (Fin 3) F) *
      (P0 : Matrix (Fin 3) (Fin 3) F) = antidiag 3 :=
    (exists_wittMatrix (p := 2) (f := 1) hF 3).choose_spec
  let e : CFSG.Open.StatedSU 3 (2 ^ 1) F ≃* SU (unitaryInvolution F 2 1) 3 :=
    ((conjEquiv (σ := unitaryInvolution F 2 1) P0 hP0).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := 1) hF 3))).symm
  refine ⟨e X, e P, e w, e Fe, heisData_map_mulEquiv e hH, ?_⟩
  obtain ⟨c, hc⟩ := exists_scalar_mat_conjEquiv hF hP0 hw
  exact ⟨c, hc⟩


private theorem map_suRad_commutator_mem {F : Type} [Field F] [Finite F] [CharP F 2]
    {G : Type*} [Group G] (ψ : SU (unitaryInvolution F 2 1) 3 →* G) {N : Subgroup G}
    (hN2 : ∀ P : Subgroup (SU (unitaryInvolution F 2 1) 3), IsPGroup 2 P →
      ⁅P.map ψ, P.map ψ⁆ ≤ N) {x y : SU (unitaryInvolution F 2 1) 3}
    (hx : x ∈ RCSTSU.suRad (unitaryInvolution F 2 1) 1)
    (hy : y ∈ RCSTSU.suRad (unitaryInvolution F 2 1) 1) :
    ψ (x * y * x⁻¹ * y⁻¹) ∈ N := by
  have hle := hN2 (RCSTSU.suRad (unitaryInvolution F 2 1) 1) RCSTSU.suRad_isPGroup
  have hmem : ψ x * ψ y * (ψ x)⁻¹ * (ψ y)⁻¹ ∈
      ⁅(RCSTSU.suRad (unitaryInvolution F 2 1) 1).map ψ,
        (RCSTSU.suRad (unitaryInvolution F 2 1) 1).map ψ⁆ := by
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem ψ hx)
      (Subgroup.mem_map_of_mem ψ hy)
    simpa [commutatorElement_def] using h
  have hz : ψ (x * y * x⁻¹ * y⁻¹) = ψ x * ψ y * (ψ x)⁻¹ * (ψ y)⁻¹ := by
    simp [map_mul, map_inv]
  rw [hz]
  exact hle hmem

private theorem exists_suRad_commutator {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {G : Type*} [Group G]
    (ψ : SU (unitaryInvolution F 2 1) 3 →* G) {N : Subgroup G}
    (hN2 : ∀ P : Subgroup (SU (unitaryInvolution F 2 1) 3), IsPGroup 2 P →
      ⁅P.map ψ, P.map ψ⁆ ≤ N) :
    ∃ z0 : SU (unitaryInvolution F 2 1) 3,
      z0 ∈ RCSTSU.suRad (unitaryInvolution F 2 1) 1 ∧ z0 ^ 2 = 1 ∧ z0 ≠ 1 ∧
        ψ z0 ∈ N := by
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution F 2 1) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) hF
  obtain ⟨x0, hx0, y0, hy0, hxy⟩ :=
    exists_mem_suRad_not_commute (σ := unitaryInvolution F 2 1) hσ (k := 1) (by norm_num)
  let z0 : SU (unitaryInvolution F 2 1) 3 := x0 * y0 * x0⁻¹ * y0⁻¹
  have hz0R : z0 ∈ RCSTSU.suRad (unitaryInvolution F 2 1) 1 := by
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx0 hy0)
      (Subgroup.inv_mem _ hx0)) (Subgroup.inv_mem _ hy0)
  have hz0N : ψ z0 ∈ N := by
    change ψ (x0 * y0 * x0⁻¹ * y0⁻¹) ∈ N
    exact map_suRad_commutator_mem ψ hN2 hx0 hy0
  have hrad : radCol (σ := unitaryInvolution F 2 1) (k := 1) z0 = 0 := by
    have h1 : radCol (σ := unitaryInvolution F 2 1) (k := 1) (x0 * y0) =
        radCol x0 + radCol y0 := radCol_mul hx0 hy0
    have h2 : radCol (σ := unitaryInvolution F 2 1) (k := 1) (x0 * y0 * x0⁻¹) =
        radCol (x0 * y0) + radCol x0⁻¹ :=
      radCol_mul (Subgroup.mul_mem _ hx0 hy0) (Subgroup.inv_mem _ hx0)
    have h3 : radCol (σ := unitaryInvolution F 2 1) (k := 1) (x0 * y0 * x0⁻¹ * y0⁻¹) =
        radCol (x0 * y0 * x0⁻¹) + radCol y0⁻¹ :=
      radCol_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx0 hy0) (Subgroup.inv_mem _ hx0))
        (Subgroup.inv_mem _ hy0)
    change radCol (σ := unitaryInvolution F 2 1) (k := 1)
      (x0 * y0 * x0⁻¹ * y0⁻¹) = 0
    rw [h3, h2, h1, radCol_inv hx0, radCol_inv hy0]
    abel
  have hz0sq : z0 ^ 2 = 1 :=
    sq_eq_one_of_radCol_eq_zero (σ := unitaryInvolution F 2 1) (k := 1) hσ.invol hz0R hrad
  have hz0ne : z0 ≠ 1 := by
    intro h
    apply hxy
    have h' : x0 * y0 * x0⁻¹ = y0 := by
      have := congrArg (fun t => t * y0) h
      simpa [z0, mul_assoc] using this
    calc x0 * y0 = (x0 * y0 * x0⁻¹) * x0 := by group
      _ = y0 * x0 := by rw [h']
  exact ⟨z0, hz0R, hz0sq, hz0ne, hz0N⟩

private theorem exists_conj_of_orderOf_eq_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {u v : SU (unitaryInvolution F 2 1) 3}
    (hu : orderOf u = 2) (hv : orderOf v = 2) :
    ∃ b : SU (unitaryInvolution F 2 1) 3, u = b * v * b⁻¹ := by
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution F 2 1) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) hF
  obtain ⟨l, hl1, hl2, a, ha⟩ :=
    exists_conj_ggInvSU_of_orderOf_eq_two (σ := unitaryInvolution F 2 1) hσ hu
  obtain ⟨l', hl'1, hl'2, b, hb⟩ :=
    exists_conj_ggInvSU_of_orderOf_eq_two (σ := unitaryInvolution F 2 1) hσ hv
  have hl : l = 1 := by omega
  have hl' : l' = 1 := by omega
  subst hl
  subst hl'
  exact ⟨a * b⁻¹, by rw [ha, hb]; group⟩

private theorem heis_pair_relations {F : Type} [Field F] [Finite F] [CharP F 2]
    {X P w Fe : SU (unitaryInvolution F 2 1) 3}
    (hH : HeisData (SU (unitaryInvolution F 2 1) 3) X P w Fe) :
    (Fe ^ 2) ^ 2 = 1 ∧ Fe ^ 2 * X * (Fe ^ 2)⁻¹ = X⁻¹ ∧
      X * Fe ^ 2 * X⁻¹ * (Fe ^ 2)⁻¹ = X ^ 2 ∧ P = Fe⁻¹ * X * Fe := by
  have hF2sq : (Fe ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, hH.F_pow]
  have hg2 : Fe ^ 2 * Fe ^ 2 = 1 := by simpa [pow_two] using hF2sq
  have hg_inv : (Fe ^ 2)⁻¹ = Fe ^ 2 := inv_eq_of_mul_eq_one_right hg2
  have hFX2 : Fe ^ 2 * X * (Fe ^ 2)⁻¹ = X⁻¹ := by
    calc Fe ^ 2 * X * (Fe ^ 2)⁻¹ = Fe * (Fe * X * Fe⁻¹) * Fe⁻¹ := by
          rw [pow_two, _root_.mul_inv_rev]
          group
      _ = Fe * P⁻¹ * Fe⁻¹ := by rw [hH.FX]
      _ = (Fe * P * Fe⁻¹)⁻¹ := by
          rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv]
          group
      _ = X⁻¹ := by rw [hH.FP]
  have hFX2' : Fe ^ 2 * X * Fe ^ 2 = X⁻¹ := by simpa [hg_inv] using hFX2
  have hXg : X * Fe ^ 2 = Fe ^ 2 * X⁻¹ := by
    calc X * Fe ^ 2 = (Fe ^ 2 * Fe ^ 2) * X * Fe ^ 2 := by rw [hg2, one_mul]
      _ = Fe ^ 2 * (Fe ^ 2 * X * Fe ^ 2) := by group
      _ = Fe ^ 2 * X⁻¹ := by rw [hFX2']
  have hgXg : Fe ^ 2 * X⁻¹ * Fe ^ 2 = X := by
    have h := congrArg Inv.inv hFX2'
    simpa [mul_assoc, _root_.mul_inv_rev, hg_inv] using h
  have hcomm : X * Fe ^ 2 * X⁻¹ * (Fe ^ 2)⁻¹ = X ^ 2 := by
    rw [hg_inv]
    calc X * Fe ^ 2 * X⁻¹ * Fe ^ 2 = (X * Fe ^ 2) * X⁻¹ * Fe ^ 2 := by rw [mul_assoc]
      _ = (Fe ^ 2 * X⁻¹) * X⁻¹ * Fe ^ 2 := by rw [hXg]
      _ = Fe ^ 2 * X⁻¹ * (Fe ^ 2 * Fe ^ 2) * X⁻¹ * Fe ^ 2 := by rw [hg2]; group
      _ = (Fe ^ 2 * X⁻¹ * Fe ^ 2) * (Fe ^ 2 * X⁻¹ * Fe ^ 2) := by group
      _ = X * X := by rw [hgXg]
      _ = X ^ 2 := by rw [pow_two]
  have hP : P = Fe⁻¹ * X * Fe := by
    rw [← hH.FP]
    group
  exact ⟨hF2sq, hFX2, hcomm, hP⟩

private theorem map_heis_generators_mem {F : Type} [Field F] [Finite F] [CharP F 2]
    {G : Type*} [Group G] (ψ : SU (unitaryInvolution F 2 1) 3 →* G) {N : Subgroup G}
    (hN1 : ∀ c : SU (unitaryInvolution F 2 1) 3, ∀ h ∈ N, ψ c * h * (ψ c)⁻¹ ∈ N)
    {X P w Fe : SU (unitaryInvolution F 2 1) 3}
    (hH : HeisData (SU (unitaryInvolution F 2 1) 3) X P w Fe)
    (hF2N : ψ (Fe ^ 2) ∈ N) : ψ X ∈ N ∧ ψ P ∈ N := by
  obtain ⟨-, -, hcomm, hP⟩ := heis_pair_relations hH
  have hX2N : ψ (X ^ 2) ∈ N := by
    have heq : ψ (X ^ 2) = ψ X * ψ (Fe ^ 2) * (ψ X)⁻¹ * (ψ (Fe ^ 2))⁻¹ := by
      have h := congrArg ψ hcomm.symm
      simpa [map_mul, map_inv] using h
    rw [heq]
    exact Subgroup.mul_mem _ (hN1 X (ψ (Fe ^ 2)) hF2N) (Subgroup.inv_mem _ hF2N)
  have hXN : ψ X ∈ N := by
    have hX4 : (X ^ 2) ^ 2 = X := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hH.X_pow, one_mul]
    have heq : ψ X = (ψ (X ^ 2)) ^ 2 := by
      rw [← map_pow, hX4]
    rw [heq]
    exact Subgroup.pow_mem _ hX2N 2
  have hPN : ψ P ∈ N := by
    rw [hP]
    have h := hN1 Fe⁻¹ (ψ X) hXN
    simpa [map_mul, map_inv] using h
  exact ⟨hXN, hPN⟩

theorem heisR_le_comap_of_conj_mem {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {G : Type*} [Group G]
    (ψ : SU (unitaryInvolution F 2 1) 3 →* G) {N : Subgroup G}
    (hN1 : ∀ c : SU (unitaryInvolution F 2 1) 3, ∀ h ∈ N, ψ c * h * (ψ c)⁻¹ ∈ N)
    (hN2 : ∀ P : Subgroup (SU (unitaryInvolution F 2 1) 3), IsPGroup 2 P → ⁅P.map ψ, P.map ψ⁆ ≤ N)
    {X P w Fe : SU (unitaryInvolution F 2 1) 3}
    (hH : HeisData (SU (unitaryInvolution F 2 1) 3) X P w Fe) : heisR X P ≤ N.comap ψ := by
  obtain ⟨z0, -, hz0sq, hz0ne, hz0N⟩ := exists_suRad_commutator hF ψ hN2
  have hz0ord : orderOf z0 = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hz0sq hz0ne
  obtain ⟨hF2sq, -, -, -⟩ := heis_pair_relations hH
  have hF2ord : orderOf (Fe ^ 2) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hF2sq hH.F_sq
  obtain ⟨b, hb⟩ := exists_conj_of_orderOf_eq_two hF hF2ord hz0ord
  have hF2N : ψ (Fe ^ 2) ∈ N := by
    rw [hb]
    have h := hN1 b (ψ z0) hz0N
    simpa [map_mul, map_inv] using h
  obtain ⟨hXN, hPN⟩ := map_heis_generators_mem ψ hN1 hH hF2N
  rw [heisR, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact hXN
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hPN


theorem eq_bot_of_isPGroup_of_heisR {M : Type*} [Group M] [Finite M] {X P w Fe : M}
    (hH : HeisData M X P w Fe) (H : Subgroup M) (hH2 : IsPGroup 2 H)
    (hHR : ∀ l ∈ heisR X P, ∀ h ∈ H, l * h * l⁻¹ ∈ H) : H = ⊥ := by
  have hdisj : H ⊓ heisR X P = ⊥ :=
    disjoint_iff.mp (hH2.disjoint_of_coprime hH.isPGroup_R (by norm_num))
  rw [eq_bot_iff]
  intro h hh
  have hcomm : ∀ x ∈ heisR X P, h * x = x * h := by
    intro x hx
    have hc : h * x * h⁻¹ * x⁻¹ ∈ H ⊓ heisR X P := by
      refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (hH.normal_R.conj_mem x hx h) (inv_mem hx)⟩
      rw [show h * x * h⁻¹ * x⁻¹ = h * (x * h⁻¹ * x⁻¹) by group]
      exact mul_mem hh (hHR x hx _ (inv_mem hh))
    rw [hdisj, Subgroup.mem_bot] at hc
    calc h * x = h * x * h⁻¹ * x⁻¹ * (x * h) := by group
      _ = x * h := by rw [hc, one_mul]
  have hz := hH.cent h (hcomm X (X_mem_heisR X P)) (hcomm P (P_mem_heisR X P))
  have h3 : orderOf h ∣ 3 := (orderOf_dvd_of_mem_zpowers (hH.center_le h hz)).trans
    (orderOf_dvd_of_pow_eq_one hH.w_pow)
  obtain ⟨e, he⟩ := hH2 ⟨h, hh⟩
  have he' : orderOf h ∣ 2 ^ e :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val he)
  have h1 := Nat.dvd_gcd h3 he'
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact Subgroup.mem_bot.mpr h1

private theorem heis_cube_root {F : Type} [Field F] [Finite F] [CharP F 2]
    (_hF : Nat.card F = (2 ^ 1) ^ 2) {w : SU (unitaryInvolution F 2 1) 3} {c : F}
    (hw : mat (unitaryInvolution F 2 1) 3 w = c • 1) (hw3 : w ^ 3 = 1) (hwne : w ≠ 1) :
    c ^ 3 = 1 ∧ c ≠ 1 ∧ c ≠ 0 ∧ c ^ 2 + c + 1 = 0 := by
  have hc3 : c ^ 3 = 1 := by
    have hmatw : (mat (unitaryInvolution F 2 1) 3 w) ^ 3 = 1 := by
      rw [← map_pow, hw3, map_one]
    have h := hmatw
    rw [hw] at h
    have hsm : (c • (1 : Matrix (Fin 3) (Fin 3) F)) = Matrix.scalar (Fin 3) c := by
      rw [smul_one_eq_diagonal, Matrix.scalar_apply]
    rw [hsm] at h
    have hscalar : (Matrix.scalar (Fin 3) c) ^ 3 = Matrix.scalar (Fin 3) (c ^ 3) := by
      rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_pow]
      rfl
    rw [hscalar] at h
    exact Matrix.scalar_inj.mp (by simpa using h)
  have hc1 : c ≠ 1 := by
    intro hc
    apply hwne
    apply mat_injective
    rw [hw, hc, one_smul, map_one]
  refine ⟨hc3, hc1, ?_, ?_⟩
  · intro h0
    rw [h0] at hc3
    norm_num at hc3
  · have h : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc1)

private theorem heis_four_cases {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {c : F} (hc3 : c ^ 3 = 1) (_hc1 : c ≠ 1)
    (hc2 : c ^ 2 + c + 1 = 0) : ∀ a : F, a = 0 ∨ a = 1 ∨ a = c ∨ a = c ^ 2 := by
  have : Fintype F := Fintype.ofFinite F
  intro a
  have ha4 : a ^ 4 = a := by
    have h := FiniteField.pow_card (K := F) a
    rwa [← Nat.card_eq_fintype_card, hF, show (2 ^ 1) ^ 2 = 4 by norm_num] at h
  have hmid : (a - c) * (a - c ^ 2) = a ^ 2 + a + 1 := by
    linear_combination -a * hc2 + hc3
  have hfac : a * ((a - 1) * ((a - c) * (a - c ^ 2))) = 0 := by
    calc a * ((a - 1) * ((a - c) * (a - c ^ 2)))
        = a * ((a - 1) * (a ^ 2 + a + 1)) := by rw [hmid]
      _ = a ^ 4 - a := by ring
      _ = 0 := by rw [ha4]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl h
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h)))

private theorem heisR_smul_mem {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {X P w : SU (unitaryInvolution F 2 1) 3} {c : F}
    (hw : mat (unitaryInvolution F 2 1) 3 w = c • 1) (hwR : w ∈ heisR X P)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hc2 : c ^ 2 + c + 1 = 0)
    (V : AddSubgroup (Fin 3 → F))
    (hV : ∀ g ∈ heisR X P, ∀ v ∈ V, mat (unitaryInvolution F 2 1) 3 g *ᵥ v ∈ V) :
    ∀ a : F, ∀ v ∈ V, a • v ∈ V := by
  have hcw : ∀ v ∈ V, c • v ∈ V := by
    intro v hv
    have h := hV w hwR v hv
    rwa [hw, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  intro a v hv
  rcases heis_four_cases hF hc3 hc1 hc2 a with rfl | rfl | rfl | rfl
  · rw [zero_smul]
    exact V.zero_mem
  · rw [one_smul]
    exact hv
  · exact hcw v hv
  · rw [show c ^ 2 • v = c • (c • v) by rw [pow_two, smul_smul]]
    exact hcw _ (hcw v hv)

private theorem heis_projection_sum {F : Type} [Field F] [CharP F 2]
    (M : Matrix (Fin 3) (Fin 3) F) {c : F} (hc3 : c ^ 3 = 1) (_hc1 : c ≠ 1)
    (hc2 : c ^ 2 + c + 1 = 0) {v : Fin 3 → F} {u : F → (Fin 3 → F)}
    (hu : ∀ mu : F, u mu = v + mu⁻¹ • (M *ᵥ v) + (mu ^ 2)⁻¹ • (M *ᵥ (M *ᵥ v))) :
    u 1 + u c + u (c ^ 2) = v := by
  have hc_inv : c⁻¹ = c ^ 2 := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ', show 1 + 2 = 3 by norm_num, hc3])
  have hc2_inv : (c ^ 2)⁻¹ = c := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, show 2 + 1 = 3 by norm_num, hc3])
  have hc4_inv : ((c ^ 2) ^ 2)⁻¹ = c ^ 2 := by
    rw [← inv_pow (c ^ 2) 2, hc2_inv]
  rw [hu 1, hu c, hu (c ^ 2)]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [hc_inv, hc2_inv, hc4_inv]
  simp only [inv_one]
  have hc2' : c ^ 2 = -c - 1 := by linear_combination hc2
  rw [hc2']
  ring_nf
  have h3 : (3 : F) = 1 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination h2
  rw [h3, mul_one]

private theorem heis_projection_eigen {F : Type} [Field F] [CharP F 2]
    (M : Matrix (Fin 3) (Fin 3) F) (hM3 : M * M * M = 1) {v : Fin 3 → F} {u : F → (Fin 3 → F)}
    (hu : ∀ mu : F, u mu = v + mu⁻¹ • (M *ᵥ v) + (mu ^ 2)⁻¹ • (M *ᵥ (M *ᵥ v)))
    {mu : F} (hmu3 : mu ^ 3 = 1) : M *ᵥ u mu = mu • u mu := by
  have hmuinv : mu⁻¹ = mu ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', show 1 + 2 = 3 by norm_num, hmu3])
  have hmu2inv : (mu ^ 2)⁻¹ = mu :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ, show 2 + 1 = 3 by norm_num, hmu3])
  have hM3v : M *ᵥ (M *ᵥ (M *ᵥ v)) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM3, Matrix.one_mulVec]
  rw [hu mu]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hM3v]
  rw [hmuinv, hmu2inv]
  rw [smul_add, smul_add, smul_smul, smul_smul]
  have hmu2 : mu * mu ^ 2 = 1 := by rw [← pow_succ' mu 2, hmu3]
  have hmu : mu * mu = mu ^ 2 := by rw [pow_two]
  rw [hmu2, hmu, one_smul]
  abel

private theorem heisR_exists_eigenvector {F : Type} [Field F] [Finite F] [CharP F 2]
    {X P : SU (unitaryInvolution F 2 1) 3} {c : F} (hX3 : X ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hc2 : c ^ 2 + c + 1 = 0)
    (V : AddSubgroup (Fin 3 → F))
    (hV : ∀ g ∈ heisR X P, ∀ v ∈ V, mat (unitaryInvolution F 2 1) 3 g *ᵥ v ∈ V)
    (hsmul : ∀ a : F, ∀ v ∈ V, a • v ∈ V)
    {v : Fin 3 → F} (hv : v ∈ V) (hv0 : v ≠ 0) :
    ∃ u ∈ V, u ≠ 0 ∧ ∃ mu : F, mu ^ 3 = 1 ∧
      mat (unitaryInvolution F 2 1) 3 X *ᵥ u = mu • u := by
  let M : Matrix (Fin 3) (Fin 3) F := mat (unitaryInvolution F 2 1) 3 X
  have hM3 : M * M * M = 1 := by
    have h : M ^ 3 = 1 := by
      rw [show M ^ 3 = (mat (unitaryInvolution F 2 1) 3 X) ^ 3 from rfl, ← map_pow, hX3,
        map_one]
    rwa [pow_three'] at h
  let u : F → (Fin 3 → F) := fun mu =>
    v + mu⁻¹ • (M *ᵥ v) + (mu ^ 2)⁻¹ • (M *ᵥ (M *ᵥ v))
  have hu : ∀ mu : F, u mu = v + mu⁻¹ • (M *ᵥ v) + (mu ^ 2)⁻¹ • (M *ᵥ (M *ᵥ v)) :=
    fun mu => rfl
  have hsum := heis_projection_sum M hc3 hc1 hc2 hu
  have hsome : u 1 ≠ 0 ∨ u c ≠ 0 ∨ u (c ^ 2) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3⟩ := h
    apply hv0
    rw [← hsum, h1, h2, h3, add_zero, add_zero]
  have huV : ∀ mu : F, u mu ∈ V := by
    intro mu
    have hXv : M *ᵥ v ∈ V := hV X (X_mem_heisR X P) v hv
    have hX2v : M *ᵥ (M *ᵥ v) ∈ V := by
      have h := hV (X ^ 2) (Subgroup.pow_mem _ (X_mem_heisR X P) 2) v hv
      simpa [M, map_pow, pow_two, Matrix.mulVec_mulVec] using h
    exact V.add_mem (V.add_mem hv (hsmul mu⁻¹ _ hXv)) (hsmul ((mu ^ 2)⁻¹) _ hX2v)
  have hc23 : (c ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
  rcases hsome with h1 | h2 | h3
  · exact ⟨u 1, huV 1, h1, 1, one_pow 3, heis_projection_eigen M hM3 hu (one_pow 3)⟩
  · exact ⟨u c, huV c, h2, c, hc3, heis_projection_eigen M hM3 hu hc3⟩
  · exact ⟨u (c ^ 2), huV (c ^ 2), h3, c ^ 2, hc23,
      heis_projection_eigen M hM3 hu hc23⟩

private theorem heis_mat_commutator_pow {F : Type} [Field F] [Finite F] [CharP F 2]
    {X P w : SU (unitaryInvolution F 2 1) 3} {c : F}
    (hXP : X * P = w * (P * X)) (hw : mat (unitaryInvolution F 2 1) 3 w = c • 1) (i : ℕ) :
    mat (unitaryInvolution F 2 1) 3 X * (mat (unitaryInvolution F 2 1) 3 P) ^ i =
      (c ^ i) • ((mat (unitaryInvolution F 2 1) 3 P) ^ i *
        mat (unitaryInvolution F 2 1) 3 X) := by
  let M : Matrix (Fin 3) (Fin 3) F := mat (unitaryInvolution F 2 1) 3 X
  let N : Matrix (Fin 3) (Fin 3) F := mat (unitaryInvolution F 2 1) 3 P
  have hMN : M * N = c • (N * M) := by
    have h := congrArg (mat (unitaryInvolution F 2 1) 3) hXP
    simpa [M, N, map_mul, hw, Matrix.smul_mul] using h
  change M * N ^ i = (c ^ i) • (N ^ i * M)
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih, Matrix.smul_mul, mul_assoc, hMN,
      Matrix.mul_smul, smul_smul, ← mul_assoc]

private theorem heis_mat_pow_eigen {F : Type} [Field F] [Finite F] [CharP F 2]
    {X P w : SU (unitaryInvolution F 2 1) 3} {c mu : F}
    (hXP : X * P = w * (P * X)) (hw : mat (unitaryInvolution F 2 1) 3 w = c • 1)
    {u : Fin 3 → F} (hu : mat (unitaryInvolution F 2 1) 3 X *ᵥ u = mu • u) (i : ℕ) :
    mat (unitaryInvolution F 2 1) 3 X *ᵥ ((mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ u) =
      (mu * c ^ i) • ((mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ u) := by
  calc (mat (unitaryInvolution F 2 1) 3 X) *ᵥ
        ((mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ u)
      = (mat (unitaryInvolution F 2 1) 3 X *
          (mat (unitaryInvolution F 2 1) 3 P) ^ i) *ᵥ u := by rw [Matrix.mulVec_mulVec]
    _ = ((c ^ i) • ((mat (unitaryInvolution F 2 1) 3 P) ^ i *
          mat (unitaryInvolution F 2 1) 3 X)) *ᵥ u := by
          rw [heis_mat_commutator_pow hXP hw i]
    _ = (c ^ i) • (((mat (unitaryInvolution F 2 1) 3 P) ^ i *
          mat (unitaryInvolution F 2 1) 3 X) *ᵥ u) := by rw [Matrix.smul_mulVec]
    _ = (c ^ i) • ((mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ
          (mat (unitaryInvolution F 2 1) 3 X *ᵥ u)) := by rw [Matrix.mulVec_mulVec]
    _ = (c ^ i) • ((mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ (mu • u)) := by rw [hu]
    _ = (c ^ i) • (mu • ((mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ u)) := by
          rw [Matrix.mulVec_smul]
    _ = ((c ^ i) * mu) • ((mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ u) := by
          rw [smul_smul]
    _ = (mu * c ^ i) • ((mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ u) := by
          rw [mul_comm]

private theorem heis_mat_pow_ne_zero {F : Type} [Field F] [Finite F] [CharP F 2]
    {P : SU (unitaryInvolution F 2 1) 3}
    {u : Fin 3 → F} (hu0 : u ≠ 0) (i : ℕ) :
    (mat (unitaryInvolution F 2 1) 3 P) ^ i *ᵥ u ≠ 0 := by
  have hNdet : (mat (unitaryInvolution F 2 1) 3 P).det ≠ 0 := by
    rw [mat_apply]
    exact Matrix.GeneralLinearGroup.det_ne_zero (P : GL (Fin 3) F)
  have hdet : ((mat (unitaryInvolution F 2 1) 3 P) ^ i).det ≠ 0 := by
    rw [Matrix.det_pow]
    exact pow_ne_zero i hNdet
  have hinj := Matrix.mulVec_injective_of_det_ne_zero hdet
  intro h
  apply hu0
  apply hinj
  simpa using h

private theorem heis_mat_span_top {F : Type} [Field F] [Finite F] [CharP F 2]
    {X P w : SU (unitaryInvolution F 2 1) 3} {c mu : F}
    (hXP : X * P = w * (P * X))
    (hw : mat (unitaryInvolution F 2 1) 3 w = c • 1)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hmu0 : mu ≠ 0)
    {u : Fin 3 → F} (hu : mat (unitaryInvolution F 2 1) 3 X *ᵥ u = mu • u)
    (hu0 : u ≠ 0) :
    Submodule.span F (Set.range fun i : Fin 3 =>
      (mat (unitaryInvolution F 2 1) 3 P) ^ (i : ℕ) *ᵥ u) = ⊤ := by
  have hc_ord : orderOf c = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hc3 hc1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc3
    norm_num at hc3
  let cu : Fˣ := Units.mk0 c hc0
  have hcu_ord : orderOf cu = 3 := by
    rw [← orderOf_units (y := cu)]
    exact hc_ord
  have hinj_pow : Function.Injective fun i : Fin 3 => cu ^ (i : ℕ) := by
    intro i j h
    have h' := (pow_inj_mod (x := cu)).mp h
    rw [hcu_ord] at h'
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hinj : Function.Injective fun i : Fin 3 => mu * c ^ (i : ℕ) := by
    intro i j h
    have hcij : c ^ (i : ℕ) = c ^ (j : ℕ) := mul_left_cancel₀ hmu0 h
    apply hinj_pow
    apply Units.ext
    simpa [cu, Units.val_pow_eq_pow_val] using hcij
  have hli : LinearIndependent F (fun i : Fin 3 =>
      (mat (unitaryInvolution F 2 1) 3 P) ^ (i : ℕ) *ᵥ u) := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.mulVecLin
      (mat (unitaryInvolution F 2 1) 3 X))
      (fun i : Fin 3 => mu * c ^ (i : ℕ)) hinj _ (fun i => ?_)
    rw [Module.End.hasEigenvector_iff]
    refine ⟨?_, heis_mat_pow_ne_zero hu0 (i : ℕ)⟩
    rw [Module.End.mem_eigenspace_iff]
    exact heis_mat_pow_eigen (X := X) (P := P) (w := w) hXP hw hu (i : ℕ)
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp)
  simpa using htop

private theorem addSubgroup_eq_top_of_span {F : Type} [Field F] [Finite F] [CharP F 2]
    {P : SU (unitaryInvolution F 2 1) 3} {V : AddSubgroup (Fin 3 → F)}
    (hsmul : ∀ a : F, ∀ v ∈ V, a • v ∈ V)
    {u : Fin 3 → F} (huV : u ∈ V)
    (hNW : ∀ i : Fin 3, (mat (unitaryInvolution F 2 1) 3 P) ^ (i : ℕ) *ᵥ u ∈ V)
    (hspan : Submodule.span F (Set.range fun i : Fin 3 =>
      (mat (unitaryInvolution F 2 1) 3 P) ^ (i : ℕ) *ᵥ u) = ⊤) : V = ⊤ := by
  let W : Submodule F (Fin 3 → F) :=
    { carrier := V
      zero_mem' := V.zero_mem
      add_mem' := fun ha hb => V.add_mem ha hb
      smul_mem' := fun a v hv => hsmul a v hv }
  have huW : u ∈ W := by
    simpa [W] using huV
  have hNW' : ∀ i : Fin 3, (mat (unitaryInvolution F 2 1) 3 P) ^ (i : ℕ) *ᵥ u ∈ W := by
    intro i
    simpa [W] using hNW i
  have hWtop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hNW' i)
  have hVtop : V = ⊤ := by
    ext x
    constructor
    · intro _
      exact AddSubgroup.mem_top x
    · intro _
      have hxW : x ∈ W := by rw [hWtop]; exact Submodule.mem_top
      simpa [W] using hxW
  exact hVtop

private theorem heisR_span_eq_top {F : Type} [Field F] [Finite F] [CharP F 2]
    (_hF : Nat.card F = (2 ^ 1) ^ 2) {X P w Fe : SU (unitaryInvolution F 2 1) 3}
    (hH : HeisData (SU (unitaryInvolution F 2 1) 3) X P w Fe) {c : F}
    (hw : mat (unitaryInvolution F 2 1) 3 w = c • 1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hc2 : c ^ 2 + c + 1 = 0) (V : AddSubgroup (Fin 3 → F))
    (hV : ∀ g ∈ heisR X P, ∀ v ∈ V, mat (unitaryInvolution F 2 1) 3 g *ᵥ v ∈ V)
    (hsmul : ∀ a : F, ∀ v ∈ V, a • v ∈ V)
    {v : Fin 3 → F} (hv : v ∈ V) (hv0 : v ≠ 0) : V = ⊤ := by
  obtain ⟨u, huV, hu0, mu, hmu3, huEig⟩ :=
    heisR_exists_eigenvector hH.X_pow hc3 hc1 hc2 V hV hsmul hv hv0
  have hmu0 : mu ≠ 0 := by
    intro h
    rw [h] at hmu3
    norm_num at hmu3
  have hspan := heis_mat_span_top hH.XP hw hc3 hc1 hmu0 huEig hu0
  have hNW : ∀ i : Fin 3, (mat (unitaryInvolution F 2 1) 3 P) ^ (i : ℕ) *ᵥ u ∈ V := by
    intro i
    have hP : P ^ (i : ℕ) ∈ heisR X P := Subgroup.pow_mem _ (P_mem_heisR X P) _
    simpa [map_pow] using hV (P ^ (i : ℕ)) hP u huV
  exact addSubgroup_eq_top_of_span hsmul huV hNW hspan

theorem eq_bot_of_heisR_aform_comm {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {X P w Fe : SU (unitaryInvolution F 2 1) 3}
    (hH : HeisData (SU (unitaryInvolution F 2 1) 3) X P w Fe) {c : F}
    (hw : mat (unitaryInvolution F 2 1) 3 w = c • 1) (V : AddSubgroup (Fin 3 → F))
    (hV : ∀ g ∈ heisR X P, ∀ v ∈ V, mat (unitaryInvolution F 2 1) 3 g *ᵥ v ∈ V)
    (hVV : ∀ v ∈ V, ∀ v' ∈ V,
      aform (unitaryInvolution F 2 1) v v' = aform (unitaryInvolution F 2 1) v' v) :
    V = ⊥ := by

  obtain ⟨hc3, hc1, hc0, hc2⟩ := heis_cube_root hF hw hH.w_pow hH.w_ne
  have hsmul := heisR_smul_mem hF hw hH.w_mem hc3 hc1 hc2 V hV
  rw [eq_bot_iff]
  intro v hv
  by_contra hv0
  have htop := heisR_span_eq_top hF hH hw hc3 hc1 hc2 V hV hsmul hv hv0
  have he0 : (Pi.single (0 : Fin 3) (1 : F) : Fin 3 → F) ∈ V := by
    rw [htop]
    exact AddSubgroup.mem_top _
  have he2 : (c • (Pi.single (2 : Fin 3) (1 : F) : Fin 3 → F)) ∈ V := by
    rw [htop]
    exact AddSubgroup.mem_top _
  have hsym := hVV _ he0 _ he2
  have hσc : unitaryInvolution F 2 1 c = c ^ 2 := by
    rw [unitaryInvolution_apply]
    norm_num
  have h1 : aform (unitaryInvolution F 2 1) (Pi.single (0 : Fin 3) (1 : F))
      (c • (Pi.single (2 : Fin 3) (1 : F))) = c := by
    rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_smul_right,
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_single]
    simp [antidiag]
  have h2 : aform (unitaryInvolution F 2 1) (c • (Pi.single (2 : Fin 3) (1 : F)))
      (Pi.single (0 : Fin 3) (1 : F)) = c ^ 2 := by
    rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_smul_left,
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_single, hσc]
    simp [antidiag]
  rw [h1, h2] at hsym
  have hc_eq : c = 1 := by
    have h : c * 1 = c * c := by
      rw [mul_one, ← pow_two]
      exact hsym
    exact (mul_left_cancel₀ hc0 h).symm
  exact hc1 hc_eq


end CFSG.StandardType.SUTransvection
