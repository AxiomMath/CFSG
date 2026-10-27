module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinCoords
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5TorusGen
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart14
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section

namespace CFSG.StandardType.F4ExplicitPos.ProjectiveRank
open Matrix CFSG.Open
variable {K L : Type} [Field K] [Field L]

theorem card_le_pow_of_isElemAbelian_statedProj
    {F Ω : Type} [Field F] [Finite F] [CharP F 2] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] [IsAlgClosed Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 0 < n)
    (E : Subgroup (GL (Fin n) Ω ⧸ StatedScalars (Fin n) Ω)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ (n - 1) := by
  classical
  have : CharP Ω 2 :=
    charP_of_injective_ringHom (f := algebraMap F Ω) (algebraMap F Ω).injective 2
  have hpΩ : (p : Ω) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := Ω) (p := 2) hp (Ne.symm hp2)
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_units_of_isAlgClosed (Ω := Ω) hp hpΩ
  let Q := GL (Fin n) Ω ⧸ StatedScalars (Fin n) Ω
  let mkQ : GL (Fin n) Ω →* Q := QuotientGroup.mk' (StatedScalars (Fin n) Ω)
  let : Fintype E := Fintype.ofFinite E
  let rep (e : E) : GL (Fin n) Ω := Quotient.out (e : Q)
  have hrep (e : E) : (QuotientGroup.mk (rep e) : Q) = (e : Q) := QuotientGroup.out_eq' _
  let entryF (g : GL (Fin n) Ω) : Finset Ω :=
    Finset.univ.image fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) Ω) ij.1 ij.2
  let S : Finset Ω :=
    (Finset.univ.biUnion fun e : E => entryF (rep e) ∪ entryF ((rep e)⁻¹)) ∪ {(ζ : Ω)}
  obtain ⟨F', hF'fin, hSF', -⟩ :=
    CFSG.LieType.Chevalley.exists_finite_subfield_of_finset (K := F) (L := Ω) S
  have : Finite F' := hF'fin
  have hζF' : (ζ : Ω) ∈ F' := by
    apply hSF'
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  have hmem_rep (e : E) (i j : Fin n) :
      ((rep e : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω) i j ∈ F' := by
    apply hSF'
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e,
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩))
  have hmem_rep_inv (e : E) (i j : Fin n) :
      ((((rep e)⁻¹ : GL (Fin n) Ω)) : Matrix (Fin n) (Fin n) Ω) i j ∈ F' := by
    apply hSF'
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e,
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩))
  have hpK : p ∣ Nat.card F'ˣ := by
    have : NeZero p := ⟨hp.ne_zero⟩
    let ζ' : F' := ⟨(ζ : Ω), hζF'⟩
    have hζ' : IsPrimitiveRoot ζ' p := by
      apply IsPrimitiveRoot.of_map_of_injective (f := F'.subtype) (hf := F'.subtype_injective)
      simpa [ζ'] using (IsPrimitiveRoot.coe_units_iff.mpr hζ)
    have hζ'0 : ζ' ≠ 0 := by
      intro h0
      have := hζ'.pow_eq_one
      rw [h0, zero_pow hp.pos.ne'] at this
      exact zero_ne_one this
    let u : F'ˣ := Units.mk0 ζ' hζ'0
    have hu : IsPrimitiveRoot u p := IsPrimitiveRoot.coe_units_iff.mp (by
      rw [Units.val_mk0]; exact hζ')
    have horder : orderOf u = p := hu.eq_orderOf.symm
    rw [← horder]
    exact orderOf_dvd_natCard u
  let φ : GL (Fin n) F' →* GL (Fin n) Ω := Matrix.GeneralLinearGroup.map F'.subtype
  let U : Subgroup (GL (Fin n) F') := ⊤
  let ρ : U →* Q := mkQ.comp (φ.comp U.subtype)
  have hker : ∀ A : U, ρ A = 1 ↔
      (A : GL (Fin n) F') ∈ Subgroup.center (GL (Fin n) F') := by
    intro A
    change (QuotientGroup.mk (φ A.1) : Q) = 1 ↔
      (A : GL (Fin n) F') ∈ Subgroup.center (GL (Fin n) F')
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hsc
      exact mem_center_of_map_mem_statedScalars F'.subtype F'.subtype_injective hn hsc
    · intro hcenter
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center] at hcenter
      obtain ⟨c, hc⟩ := hcenter
      refine ⟨Units.map F'.subtype c, ?_⟩
      rw [← hc, Matrix.GeneralLinearGroup.map_scalar]
  have hEρ : E ≤ ρ.range := by
    intro e he
    have hrange_e : rep ⟨e, he⟩ ∈ (Matrix.GeneralLinearGroup.map F'.subtype).range :=
      mem_range_glMap_of_entries F'.subtype F'.subtype_injective
        (fun i j => ⟨⟨_, hmem_rep ⟨e, he⟩ i j⟩, rfl⟩)
        (fun i j => ⟨⟨_, hmem_rep_inv ⟨e, he⟩ i j⟩, rfl⟩)
    obtain ⟨A, hA⟩ := hrange_e
    refine ⟨⟨A, Subgroup.mem_top A⟩, ?_⟩
    show (QuotientGroup.mk (Matrix.GeneralLinearGroup.map F'.subtype A) : Q) = e
    rw [hA, hrep]
  exact CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel
    (K := F') (n := n) hp hp2 hpK hn U ρ hker E hEρ hE

theorem card_le_sq_of_isElemAbelian_statedProj_three
    {F Ω : Type} [Field F] [Finite F] [CharP F 2] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] [IsAlgClosed Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (GL (Fin 3) Ω ⧸ StatedScalars (Fin 3) Ω)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have h := card_le_pow_of_isElemAbelian_statedProj (F := F) (Ω := Ω) (n := 3)
    hp hp2 (by norm_num) E hE
  simpa using h

theorem card_le_p_of_isElemAbelian_statedProj_two
    {F Ω : Type} [Field F] [Finite F] [CharP F 2] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] [IsAlgClosed Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (GL (Fin 2) Ω ⧸ StatedScalars (Fin 2) Ω)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p := by
  have h := card_le_pow_of_isElemAbelian_statedProj (F := F) (Ω := Ω) (n := 2)
    hp hp2 (by norm_num) E hE
  simpa using h

end CFSG.StandardType.F4ExplicitPos.ProjectiveRank

end

end
end
end
end
end
end

end
