module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3EightFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMModel
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

namespace CFSG.StandardType

namespace ResU3Eight

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.LocalAnalysis.GLTheoremA.T156.Uni
open scoped commutatorElement

variable {d : ℕ} {K : Type} [Field K] [Finite K] {j : ℕ}

theorem guSet_conj_mem_U3Eight (hK : Nat.card K = (2 ^ j) ^ 2) {U A : GL (Fin d) K}
    (hU : U ∈ LargeEvenGUSet (Fin d) K (2 ^ j)) (hA : A ∈ LargeEvenGUSet (Fin d) K (2 ^ j)) :
    U⁻¹ * A * U ∈ LargeEvenGUSet (Fin d) K (2 ^ j) := by
  have hG := (CFSG.LocalAnalysis.GLTheoremA.T173A.uni_GU_facts (d := d) hK).1
  rw [← hG] at hU hA ⊢
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hU) hA) hU

variable [CharP K 2]

local notation "SUq" => LargeEvenSUGroup (Fin d) K (2 ^ j)

theorem exists_descend_of_commute_U3Eight (hd : 3 ≤ d) (hj : 1 ≤ j)
    (hK : Nat.card K = (2 ^ j) ^ 2) (hdK : (d, 2 ^ j) ≠ (3, 2)) {σ : K ≃+* K}
    (hσ : Odd (orderOf σ)) {f : MulAut (LargeEvenProj SUq)} (hf : Induced (2 ^ j) σ f)
    (M : Subgroup.normalizer (SUq : Set (GL (Fin d) K)))
    (hM : (M : GL (Fin d) K) ∈ LargeEvenGUSet (Fin d) K (2 ^ j))
    (hc : TableB.projConj SUq M * f = f * TableB.projConj SUq M) :
    ∃ (μ : Kˣ) (B : GL (Fin d) (fixF σ)),
      B ∈ LargeEvenGUSet (Fin d) (fixF σ) (2 ^ (j / orderOf σ)) ∧
      Matrix.GeneralLinearGroup.map (fixF σ).subtype B =
        Matrix.GeneralLinearGroup.scalar (Fin d) μ * (M : GL (Fin d) K) := by
  set A : GL (Fin d) K := (M : GL (Fin d) K) with hAdef
  set φ := TableB.projConj SUq M with hφdef
  have hA : ∀ g g' : SUq, (g' : GL (Fin d) K) = A * g * A⁻¹ →
      φ ((LargeEvenProjMk SUq) g) = (LargeEvenProjMk SUq) g' := by
    intro g g' hg
    change TableB.projConj SUq M (g : LargeEvenProj SUq) = (g' : LargeEvenProj SUq)
    rw [TableB.projConj_mk]
    congr 1
    exact Subtype.ext hg.symm
  have hmem : ∀ x : SUq, A * (x : GL (Fin d) K) * A⁻¹ ∈ SUq := fun x => conj_mem_su hM x.2
  let conjA : SUq → SUq := fun x => ⟨A * (x : GL (Fin d) K) * A⁻¹, hmem x⟩
  have conjA_val : ∀ x : SUq, ((conjA x : SUq) : GL (Fin d) K) = A * (x : GL (Fin d) K) * A⁻¹ :=
    fun _ => rfl
  let ρ : MulAut SUq := matAct SUq (suMapStable d K (2 ^ j)) σ
  have hc_apply : ∀ x : SUq,
      φ (f ((LargeEvenProjMk SUq) x)) = f (φ ((LargeEvenProjMk SUq) x)) := by
    intro x
    have h := congrArg (fun ψ : MulAut (LargeEvenProj SUq) => ψ ((LargeEvenProjMk SUq) x)) hc
    simpa only [MulAut.mul_apply] using h
  set S : GL (Fin d) K := Matrix.GeneralLinearGroup.map σ.toRingHom A with hSdef
  set T : GL (Fin d) K := A⁻¹ * S with hTdef
  have hcenter_x : ∀ x : SUq,
      ⁅((ρ x : SUq) : GL (Fin d) K)⁻¹, T⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro x
    have hstep : (LargeEvenProjMk SUq) (conjA (ρ x)) = (LargeEvenProjMk SUq) (ρ (conjA x)) := by
      calc (LargeEvenProjMk SUq) (conjA (ρ x))
          = φ ((LargeEvenProjMk SUq) (ρ x)) := (hA (ρ x) (conjA (ρ x)) rfl).symm
        _ = φ (f ((LargeEvenProjMk SUq) x)) := congrArg φ (hf x).symm
        _ = f (φ ((LargeEvenProjMk SUq) x)) := hc_apply x
        _ = f ((LargeEvenProjMk SUq) (conjA x)) := by rw [hA x (conjA x) rfl]
        _ = (LargeEvenProjMk SUq) (ρ (conjA x)) := hf (conjA x)
    have hZ := QuotientGroup.eq.mp hstep
    have hZgl : ((conjA (ρ x) : SUq) : GL (Fin d) K)⁻¹ * ((ρ (conjA x) : SUq) : GL (Fin d) K) ∈
        LargeEvenScalars (Fin d) K := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (Subgroup.mem_subgroupOf.mp hZ)
    have h2 : ((ρ (conjA x) : SUq) : GL (Fin d) K) =
        S * ((ρ x : SUq) : GL (Fin d) K) * S⁻¹ := by
      rw [matAct_coe SUq (suMapStable d K (2 ^ j)) σ (conjA x), conjA_val x,
        Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv, matAct_coe SUq (suMapStable d K (2 ^ j)) σ x, hSdef]
    rw [conjA_val, h2] at hZgl
    have hEk : A * ⁅((ρ x : SUq) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹ ∈ LargeEvenScalars (Fin d) K := by
      convert hZgl using 1
      rw [hTdef, commutatorElement_def]
      group
    have hcenter : A * ⁅((ρ x : SUq) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹ ∈
        Subgroup.center (GL (Fin d) K) := by
      simpa only [largeEvenScalars_def, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        using hEk
    have hconj := Subgroup.Normal.conj_mem'
      (inferInstance : (Subgroup.center (GL (Fin d) K)).Normal)
      (A * ⁅((ρ x : SUq) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹) hcenter A
    convert hconj using 1
    group
  have hcomm : ∀ g ∈ SUq, ⁅T, g⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g hg
    have h1 : ⁅g, T⁆ ∈ Subgroup.center (GL (Fin d) K) := by
      let y : SUq := ⟨g⁻¹, Subgroup.inv_mem _ hg⟩
      have h := hcenter_x (ρ.symm y)
      rw [ρ.apply_symm_apply] at h
      dsimp only [y] at h
      simpa using h
    rw [← commutatorElement_inv g T]
    exact (Subgroup.center (GL (Fin d) K)).inv_mem h1
  have hT : T ∈ LargeEvenScalars (Fin d) K := by
    refine mem_scalars_of_commute_su (k := K) (g := j) hj hK hd (RingHom.id K) fun x hx => ?_
    have hid : Matrix.GeneralLinearGroup.map (RingHom.id K) x = x := by
      apply Units.ext
      ext a b
      rfl
    rw [hid]
    exact LinearFieldFix.commute_of_commutator_mem_center (commutator_su hK hd hdK) hcomm hx
  rw [largeEvenScalars_def] at hT
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hT
  have hS : Matrix.GeneralLinearGroup.map σ.toRingHom A =
      A * Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    rw [hc, hTdef, hSdef]
    group
  have hmat : ((Matrix.GeneralLinearGroup.map σ.toRingHom A : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (c : K) • (A : Matrix (Fin d) (Fin d) K) := by
    rw [hS, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨μ, B, hdesc⟩ := LinearFieldFix.exists_descend_of_map_eq_smul σ A c hmat
  have hBGU : B ∈ LargeEvenGUSet (Fin d) (fixF σ) (2 ^ (j / orderOf σ)) := by
    refine mem_guSet_of_map (fixF σ).subtype (q := 2 ^ j) (fun b => ?_) (pow_pow_eq_self hK)
      (by omega) hM μ.ne_zero hdesc
    rw [map_pow]
    exact (fixF_pow hj hK σ hσ b).symm
  refine ⟨μ, B, hBGU, ?_⟩
  apply Units.ext
  rw [hdesc, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

end ResU3Eight

end CFSG.StandardType

end
