module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitClassFunctionInner
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Pair
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.RankThree.PartOne.KF4.F4Traces
public import CFSG.RankThree.PartOne.KF4.Strings
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralTrace
public import CFSG.ClassicalInvolution.Models.Transfer.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResSL2Trace
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.ClassicalInvolution.Models.Transfer CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups


@[expose] def f4SimpleLongRoot : Fin (Tag.rank .F4) := ⟨0, by decide⟩

@[expose] def f4StandardRootSubgroup (K : Type) [Field K] : Subgroup (adjointGroup .F4 K) :=
  stdRankOne (f4Datum K) (Pi.single f4SimpleLongRoot 1)

@[expose] def f4StandardChart (K : Type) [Field K] : SL2 K →* adjointGroup .F4 K :=
  MonoidHom.codRestrict (simpleRootSL2 .F4 K f4SimpleLongRoot) (adjointGroup .F4 K)
    (fun A => simpleRootSL2_mem_adjointGroup f4SimpleLongRoot A)

theorem f4StandardChart_apply {K : Type} [Field K] (A : SL2 K) :
    (f4StandardChart K A : ModGL .F4 K) = simpleRootSL2 .F4 K f4SimpleLongRoot A := rfl

theorem f4StandardChart_range {K : Type} [Field K] :
    (f4StandardChart K).range = f4StandardRootSubgroup K := by
  have hroot_eq : rootSL2 .F4 K (Pi.single f4SimpleLongRoot 1) =
      simpleRootSL2 .F4 K f4SimpleLongRoot := by
    rw [rootSL2]
    simp [pinnedWeyl, pinnedData_single]
    ext A
    rfl
  have hroot : IsRoot .F4 (Pi.single f4SimpleLongRoot 1) := isRoot_single (τ := .F4) f4SimpleLongRoot
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    rw [f4StandardRootSubgroup, Levi.mem_stdRankOne_f4_iff' hroot]
    refine ⟨A, ?_⟩
    rw [f4StandardChart_apply, hroot_eq]
  · intro hx
    rw [f4StandardRootSubgroup, Levi.mem_stdRankOne_f4_iff' hroot] at hx
    obtain ⟨A, hA⟩ := hx
    refine ⟨A, ?_⟩
    apply Subtype.ext
    rw [f4StandardChart_apply]
    rw [hroot_eq] at hA
    exact hA.symm

theorem f4StandardChart_inner
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {y : adjointGroup .F4 K}
    (hy : y ∈ Subgroup.normalizer (f4StandardRootSubgroup K : Set (adjointGroup .F4 K)))
    (hyo : Odd (orderOf y)) :
    ∃ w ∈ f4StandardRootSubgroup K,
      ∀ x ∈ f4StandardRootSubgroup K, y * x * y⁻¹ = w * x * w⁻¹ := by
  let ρ : SL2 K →* adjointGroup .F4 K := f4StandardChart K
  have hrange : ρ.range = f4StandardRootSubgroup K := f4StandardChart_range
  have hker : ∀ g : SL2 K, ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro g hg
    have h1 : simpleRootSL2 .F4 K f4SimpleLongRoot g = 1 := by
      have := congrArg (fun z : adjointGroup .F4 K => (z : ModGL .F4 K)) hg
      simpa [ρ, f4StandardChart] using this
    have h2 : g = 1 := simpleRootSL2_injective hK f4SimpleLongRoot (by simpa using h1)
    exact ⟨1, by simp, by rw [h2]; simp⟩
  let χ : adjointGroup .F4 K → K := fun z =>
    LinearMap.trace K (RootModule .F4 K) ((z : ModGL .F4 K) : Module.End K (RootModule .F4 K))
  have hχ : ∀ g h : adjointGroup .F4 K, χ (h * g * h⁻¹) = χ g := by
    intro g h
    simp [χ, Subgroup.coe_mul]
  have hχd : ∀ t : Kˣ, χ (ρ (sl2Diag K t)) =
      (RingHom.id K) (((t : K) + (t : K)⁻¹) ^ 2 +
        (14 : K) * ((t : K) + (t : K)⁻¹)) + 20 := by
    intro t
    change LinearMap.trace K (RootModule .F4 K)
      (simpleRootSL2 .F4 K f4SimpleLongRoot (sl2Diag K t) : Module.End K (RootModule .F4 K)) = _
    rw [trace_simpleRootSL2_F4_long f4SimpleLongRoot (Or.inl rfl) (sl2Diag K t)]
    simp [sl2Diag, Matrix.trace_fin_two]
  have hJ : ρ.range.map (MulAut.conj y).toMonoidHom = ρ.range := by
    rw [hrange]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
  have hinner := CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_normalizer_inner_of_odd
    (ρ := ρ) hker (RingHom.id K) 14 20 χ hχ hχd hyo hJ
  rwa [hrange] at hinner



theorem f4_generic_mem_modelFacts {K : Type} [Field K]
    {R : Subgroup (adjointGroup .F4 K)}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .F4 (f4Datum K)) :
    R ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups .F4 (f4Datum K) := by
  rcases hR with ⟨g, γ, hγ, rfl⟩
  refine ⟨g, γ, ?_, rfl⟩
  rcases hγ with hγ | ⟨hG2, _⟩ | ⟨hD4, _⟩
  · exact Or.inl ((isLongestRoot_iff (D := f4Datum K) (γ := γ)).mpr ⟨hγ.1, hγ.2⟩)
  · exact absurd hG2 (by decide)
  · exact absurd hD4 (by decide)

theorem odd_normalizer_inner_fundamental_f4_model
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (n e : ℕ)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .F4 n p e)
    {R : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv .F4 n p e hp.out).K}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .F4
      (CFSG.ClassicalInvolution.Generic.modelUniv .F4 n p e hp.out).D)
    {g : (CFSG.ClassicalInvolution.Generic.modelUniv .F4 n p e hp.out).K}
    (hg : g ∈ Subgroup.normalizer
      (R : Set (CFSG.ClassicalInvolution.Generic.modelUniv .F4 n p e hp.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain rfl : n = 0 := hadm.2.2
  let K := GaloisField p e
  let R' : Subgroup (adjointGroup .F4 K) := R
  let g' : adjointGroup .F4 K := g
  have hR' : R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .F4 (f4Datum K) := hR
  have hg' : g' ∈ Subgroup.normalizer (R' : Set (adjointGroup .F4 K)) := hg
  have hgo' : Odd (orderOf g') := hgo
  change ∃ r ∈ R', ∀ x ∈ R', g' * x * g'⁻¹ = r * x * r⁻¹
  have hR_model : R' ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups .F4 (f4Datum K) :=
    f4_generic_mem_modelFacts hR'
  let R0 : Subgroup (adjointGroup .F4 K) := f4StandardRootSubgroup K
  have hsingle : CFSG.ClassicalInvolution.ModelFacts.FundamentalSingleClass .F4 (f4Datum K) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .F4 0 p e hp.out trivial hadm
      (by decide) (by decide)
  have hnode : CFSG.ClassicalInvolution.ModelFacts.IsLongNode .F4 0 f4SimpleLongRoot.val := by
    change f4SimpleLongRoot.val < 2
    decide
  have hθlong : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot (f4Datum K)
      (Pi.single f4SimpleLongRoot 1) :=
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .F4 0 p e hp.out trivial hadm
      f4SimpleLongRoot hnode
  have hR0 : R0 ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups .F4 (f4Datum K) := by
    refine ⟨1, Pi.single f4SimpleLongRoot 1, Or.inl hθlong, ?_⟩
    exact (CFSG.ClassicalInvolution.Generic.conjSub_one R0).symm
  obtain ⟨c, hc⟩ := hsingle R' hR_model R0 hR0
  have hR_eq : R' = CFSG.ClassicalInvolution.Generic.conjSub c⁻¹ R0 := by
    have hc' : CFSG.ClassicalInvolution.Generic.conjSub c R' = R0 := hc.symm
    have h' : CFSG.ClassicalInvolution.Generic.conjSub c⁻¹ R0 = R' := by
      rw [← hc']
      exact CFSG.ClassicalInvolution.Generic.conjSub_inv_conjSub c R'
    exact h'.symm
  have hgN : g' ∈ Subgroup.normalizer (R' : Set (adjointGroup .F4 K)) := hg'
  rw [hR_eq] at hgN
  have hg0 : c * g' * c⁻¹ ∈ Subgroup.normalizer (R0 : Set (adjointGroup .F4 K)) := by
    rw [Subgroup.mem_normalizer_iff] at hgN ⊢
    intro x
    constructor
    · intro hx
      have hy : c⁻¹ * x * c ∈ CFSG.ClassicalInvolution.Generic.conjSub c⁻¹ R0 := by
        rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff]
        simpa [mul_assoc] using hx
      have hgy : g' * (c⁻¹ * x * c) * g'⁻¹ ∈
          CFSG.ClassicalInvolution.Generic.conjSub c⁻¹ R0 := (hgN _).mp hy
      rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff] at hgy
      simpa [mul_assoc] using hgy
    · intro hx
      have hgy : g' * (c⁻¹ * x * c) * g'⁻¹ ∈
          CFSG.ClassicalInvolution.Generic.conjSub c⁻¹ R0 := by
        rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff]
        simpa [mul_assoc] using hx
      have hy : c⁻¹ * x * c ∈ CFSG.ClassicalInvolution.Generic.conjSub c⁻¹ R0 :=
        (hgN _).mpr hgy
      rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff] at hy
      simpa [mul_assoc] using hy
  have hgo0 : Odd (orderOf (c * g' * c⁻¹)) := by
    have hord : orderOf (c * g' * c⁻¹) = orderOf g' := by
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj c) g'
    rwa [hord]
  have hK : ringChar K ≠ 2 := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  obtain ⟨w, hw, hwj⟩ := f4StandardChart_inner (K := K) hK hg0 hgo0
  refine ⟨c⁻¹ * w * c, ?_, ?_⟩
  · rw [hR_eq]
    exact Subgroup.mem_map_of_mem _ (by simpa [MulAut.conj_apply] using hw)
  · intro x hx
    have hx0 : c * x * c⁻¹ ∈ R0 := by
      rw [hR_eq] at hx
      exact (CFSG.ClassicalInvolution.Generic.mem_conjSub_iff.mp hx)
    have h := hwj (c * x * c⁻¹) hx0
    calc
      g' * x * g'⁻¹ = c⁻¹ * ((c * g' * c⁻¹) * (c * x * c⁻¹) * (c * g' * c⁻¹)⁻¹) * c := by
        group
      _ = c⁻¹ * (w * (c * x * c⁻¹) * w⁻¹) * c := by rw [h]
      _ = (c⁻¹ * w * c) * x * (c⁻¹ * w * c)⁻¹ := by group

end CFSG.LocalAnalysis.UniquenessCase.UC22
