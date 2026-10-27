module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus2
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinOrd3
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma four_le_of_card {R : Type} [Group R] {n : ℕ} {M : Type} [Field M] [Finite M]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} {E : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R}
    (hE : ∀ g : R, g ∈ E ↔ ∃ A : ↥(heldGU n M τ hτ),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) ∧ ρ A = g)
    (hM : Nat.card M = 4) (hEcard : 3 ^ 4 ≤ Nat.card E) : 4 ≤ n := by
  classical
  let AOf : E → ↥(heldGU n M τ hτ) := fun g => Classical.choose ((hE g.1).mp g.2)
  have hAOf : ∀ g : E, (∀ i j, i ≠ j → ((AOf g : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i j = 0) ∧ ρ (AOf g) = g.1 := fun g =>
    Classical.choose_spec ((hE g.1).mp g.2)
  let f : E → (Fin n → Mˣ) := fun g i =>
    Units.mk0 (((AOf g : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i)
      (QTwoFrameTorus.frame_diag_entry_ne_zero (hAOf g).1 i)
  have hinj : Function.Injective f := by
    intro g g' hgg
    have hdiag : ∀ i, ((AOf g : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        ((AOf g' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i := by
      intro i
      have h := congrArg Units.val (congrFun hgg i)
      simpa [f, Units.val_mk0] using h
    have hmat : ((AOf g : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
        ((AOf g' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        exact hdiag i
      · rw [(hAOf g).1 i j hij, (hAOf g').1 i j hij]
    have hAeq : AOf g = AOf g' := Subtype.ext (Units.ext hmat)
    apply Subtype.ext
    calc (g : R) = ρ (AOf g) := ((hAOf g).2).symm
      _ = ρ (AOf g') := by rw [hAeq]
      _ = (g' : R) := (hAOf g').2
  exact QTwoFrameTorus.frame_four_le_of_injective hM hinj hEcard

private lemma map_heldSU_le_centralizer {R : Type} [Group R] {n : ℕ} {M : Type} [Field M]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} {ρ : ↥(heldGU n M τ hτ) →* R}
    {x : R} {A₀ : ↥(heldGU n M τ hτ)} {c : M}
    (hA₀ : ((A₀ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = Matrix.diagonal (fun _ => c))
    (hx : ρ A₀ = x) :
    ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ ≤
      Subgroup.centralizer ({x} : Set R) := by
  intro g hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨A, hA, rfl⟩ := hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst h
  have hAB : A₀ * A = A * A₀ := by
    apply Subtype.ext
    apply Units.ext
    calc ((A₀ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)
        = Matrix.scalar (Fin n) c * ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
            rw [hA₀, ← Matrix.scalar_apply]
      _ = ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) * Matrix.scalar (Fin n) c :=
            (Matrix.scalar_commute c (fun r' => mul_comm c r') _).eq
      _ = ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
          ((A₀ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
            rw [hA₀, ← Matrix.scalar_apply]
  calc x * ρ A = ρ A₀ * ρ A := by rw [hx]
    _ = ρ (A₀ * A) := by rw [map_mul]
    _ = ρ (A * A₀) := by rw [hAB]
    _ = ρ A * ρ A₀ := by rw [map_mul]
    _ = ρ A * x := by rw [hx]

private lemma map_heldSU_subnormal {R : Type} [Group R] {n : ℕ} {M : Type} [Field M]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} {ρ : ↥(heldGU n M τ hτ) →* R}
    {x : R} {A₀ : ↥(heldGU n M τ hτ)} {c : M}
    (hA₀ : ((A₀ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = Matrix.diagonal (fun _ => c))
    (hx : ρ A₀ = x)
    (hN : ∀ g ∈ Subgroup.centralizer ({x} : Set R), ∀ A : ↥(heldGU n M τ hτ),
      (A : GL (Fin n) M) ∈ heldSU n M τ hτ → ∃ A' : ↥(heldGU n M τ hτ),
        (A' : GL (Fin n) M) ∈ heldSU n M τ hτ ∧ g * ρ A * g⁻¹ = ρ A') :
    CFSG.Assembly.IsSubnormal (((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ)
      (Subgroup.centralizer ({x} : Set R)) := by
  have hSC : ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ ≤
      Subgroup.centralizer ({x} : Set R) := map_heldSU_le_centralizer hA₀ hx
  refine CFSG.Assembly.IsSubnormal.step hSC ?_ (CFSG.Assembly.IsSubnormal.refl _)
  rw [Subgroup.normal_subgroupOf_iff hSC]
  intro h k hh hk
  rw [Subgroup.mem_map] at hh ⊢
  obtain ⟨A, hA, hAeq⟩ := hh
  obtain ⟨A', hA'su, hconj⟩ := hN k hk A hA
  exact ⟨A', hA'su, by rw [← hAeq]; exact hconj.symm⟩

private lemma isQuasisimple_map_heldSU {R : Type} [Group R] {n : ℕ} {M : Type} [Field M]
    [Finite M] {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {ρ : ↥(heldGU n M τ hτ) →* R} (hρ : Function.Injective ρ)
    (hM : Nat.card M = 4) (hn4 : 4 ≤ n) :
    CFSG.Assembly.IsQuasisimple
      (((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ) := by
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by omega)
  have hct : heldSU n M τ hτ = CFSG.Open.StatedSU n 2 M :=
    hct_heldSU_eq_statedSU (Q := 2) hτ2
  have hnat : CFSG.IsQuasisimple (CFSG.Open.StatedSU n 2 M) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := 1) (n := n)
      (F := M) (by rw [hM]; norm_num) hn3 hnq).1
  have hasm : CFSG.Assembly.IsQuasisimple ↥(CFSG.Open.StatedSU n 2 M) :=
    ⟨Group.isPerfect_def.mp hnat.1, hnat.2.1⟩
  rw [← hct] at hasm
  let e1 : ↥((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)) ≃* ↥(heldSU n M τ hτ) :=
    Subgroup.subgroupOfEquivOfLe inf_le_left
  let e2 : ↥((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)) ≃*
      ↥(((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ) :=
    Subgroup.equivMapOfInjective _ ρ hρ
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv e2.symm
    (CFSG.Assembly.IsQuasisimple.of_mulEquiv e1 hasm)

private lemma commutator_map_heldSU_ne_bot {R : Type} [Group R] [Finite R] {E : Subgroup R}
    {x : R} {L : Subgroup R} (hECL : E ⊓ Subgroup.centralizer (L : Set R) = Subgroup.zpowers x)
    {n : ℕ} {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4) (hn4 : 4 ≤ n)
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (hτ2 : ∀ y, τ y = y ^ 2) {ρ : ↥(heldGU n M τ hτ) →* R}
    (hρ : Function.Injective ρ)
    (hE : ∀ g : R, g ∈ E ↔ ∃ A : ↥(heldGU n M τ hτ),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) ∧ ρ A = g)
    {A₀ : ↥(heldGU n M τ hτ)} {c : M} (hc : c ^ 2 ≠ c)
    (hA₀ : ((A₀ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = Matrix.diagonal (fun _ => c))
    (hx : ρ A₀ = x) :
    ⁅L, ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ⁆ ≠ ⊥ := by
  classical
  have hc0 : c ≠ 0 := by
    intro h
    exact hc (by rw [h]; norm_num)
  have hc1 : c ≠ 1 := by
    intro h
    exact hc (by rw [h]; norm_num)
  have hc3 : c ^ 3 = 1 := QTwoFrameTorus.frame_pow_three_eq_one hM hc0
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h20 : i2 ≠ i0 := by simp [i2, i0]
  have h21 : i2 ≠ i1 := by simp [i2, i1]
  let d : Fin n → M := fun i => if i = i0 then c else if i = i1 then c ^ 2 else 1
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    by_cases h0 : i = i0
    · dsimp only [d]; rw [if_pos h0]; exact hc0
    · by_cases h1 : i = i1
      · dsimp only [d]; rw [if_neg h0, if_pos h1]; exact pow_ne_zero 2 hc0
      · dsimp only [d]; rw [if_neg h0, if_neg h1]; exact one_ne_zero
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    intro i
    by_cases h0 : i = i0
    · dsimp only [d]; rw [if_pos h0]; exact hc3
    · by_cases h1 : i = i1
      · dsimp only [d]; rw [if_neg h0, if_pos h1]
        calc (c ^ 2) ^ 3 = (c ^ 3) ^ 2 := by ring
          _ = 1 := by rw [hc3, one_pow]
      · dsimp only [d]; rw [if_neg h0, if_neg h1]; norm_num
  have hu : ∀ i, τ (d i) * d i = 1 := by
    intro i
    rw [hτ2, ← pow_succ]
    simpa using hd3 i
  have hdet : ∏ i, d i = 1 := by
    rw [Fintype.prod_eq_mul i0 i1 (by simp [i0, i1])]
    · have hd0 : d i0 = c := by simp [d, i0]
      have hd1 : d i1 = c ^ 2 := by simp [d, i0, i1]
      rw [hd0, hd1]
      calc c * c ^ 2 = c ^ 3 := by rw [mul_comm, ← pow_succ]
        _ = 1 := hc3
    · intro i hi
      dsimp only [d]; rw [if_neg hi.1, if_neg hi.2]
  have hD₁SU : CFSG.LocalAnalysis.GLTheoremA.HSubT.diagUnit d hd ∈ heldSU n M τ hτ :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.diagUnit_mem_heldSU hτ d hd hu hdet
  let D₁ : ↥(heldGU n M τ hτ) := ⟨CFSG.LocalAnalysis.GLTheoremA.HSubT.diagUnit d hd,
    (Subgroup.mem_inf.mp hD₁SU).1⟩
  let δ : R := ρ D₁
  have hδE : δ ∈ E := by
    rw [hE δ]
    refine ⟨D₁, ?_, rfl⟩
    intro i j hij
    change ((CFSG.LocalAnalysis.GLTheoremA.HSubT.diagUnit d hd : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i j = 0
    rw [CFSG.LocalAnalysis.GLTheoremA.HSubT.diagUnit_val, Matrix.diagonal_apply_ne _ hij]
  have hδS : δ ∈ ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ :=
    Subgroup.mem_map.mpr ⟨D₁, Subgroup.mem_subgroupOf.mpr hD₁SU, rfl⟩
  intro hcomm
  have hLle : L ≤ Subgroup.centralizer
      (((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  have hδ_cent : δ ∈ Subgroup.centralizer (L : Set R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff).mp (hLle hl) δ hδS).symm
  have hδECL : δ ∈ E ⊓ Subgroup.centralizer (L : Set R) := Subgroup.mem_inf.mpr ⟨hδE, hδ_cent⟩
  rw [hECL] at hδECL
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hδECL
  have hmap : ρ (A₀ ^ k) = δ := by
    rw [map_zpow, hx, hk]
  have hAk : A₀ ^ k = D₁ := hρ hmap
  let u : Fin n → Mˣ := fun _ => Units.mk0 c hc0
  let A₁ : GL (Fin n) M := CFSG.ClassicalGroups.SpecialLinear.diagGLHom n M u
  have hA₁ : ((A₁ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun _ => c) := by
    change ((CFSG.ClassicalGroups.SpecialLinear.diagGLHom n M u : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) = Matrix.diagonal (fun _ => c)
    rw [CFSG.ClassicalGroups.SpecialLinear.coe_diagGLHom]
    simp [u]
  have hAeq : (A₀ : GL (Fin n) M) = A₁ := Units.ext (by rw [hA₀, hA₁])
  have hpow_GL : ((A₀ : GL (Fin n) M) ^ k) =
      CFSG.ClassicalGroups.SpecialLinear.diagGLHom n M (u ^ k) := by
    rw [hAeq]
    exact (map_zpow (f := CFSG.ClassicalGroups.SpecialLinear.diagGLHom n M) u k).symm
  have hpow : (((A₀ : GL (Fin n) M) ^ k : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) = Matrix.diagonal (fun _ => c ^ k) := by
    have hcongr := congrArg (fun g : GL (Fin n) M =>
      ((g : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) hpow_GL
    rw [hcongr, CFSG.ClassicalGroups.SpecialLinear.coe_diagGLHom]
    simp [u, Units.val_zpow_eq_zpow_val]
  have hmat : (((A₀ : GL (Fin n) M) ^ k : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) =
      ((CFSG.LocalAnalysis.GLTheoremA.HSubT.diagUnit d hd : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) := by
    have h := congrArg (fun A : ↥(heldGU n M τ hτ) =>
      ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) hAk
    simpa [Subgroup.coe_zpow] using h
  have h00 : c ^ k = c := by
    have h := congrArg (fun Mx : Matrix (Fin n) (Fin n) M => Mx i0 i0) hmat
    simpa [hpow, CFSG.LocalAnalysis.GLTheoremA.HSubT.diagUnit_val,
      Matrix.diagonal_apply_eq, d, i0] using h
  have h22 : c ^ k = 1 := by
    have h := congrArg (fun Mx : Matrix (Fin n) (Fin n) M => Mx i2 i2) hmat
    simpa [hpow, CFSG.LocalAnalysis.GLTheoremA.HSubT.diagUnit_val,
      Matrix.diagonal_apply_eq, d, i2, i0, i1, h20, h21] using h
  exact hc1 (h00.symm.trans h22)

theorem ggQTwo_L_eq_map_heldSU {R : Type} [Group R] [Finite R] {E : Subgroup R} {x : R}
    {L D J : Subgroup R} (hC : GGQTwoFRCfg E x L D J) {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {ρ : ↥(heldGU n M τ hτ) →* R} (hρ : Function.Injective ρ)
    (hE : ∀ g : R, g ∈ E ↔ ∃ A : ↥(heldGU n M τ hτ),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) ∧ ρ A = g)
    {A₀ : ↥(heldGU n M τ hτ)} {c : M} (hc : c ^ 2 ≠ c)
    (hA₀ : ((A₀ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = Matrix.diagonal (fun _ => c))
    (hx : ρ A₀ = x)
    (hN : ∀ g ∈ Subgroup.centralizer ({x} : Set R), ∀ A : ↥(heldGU n M τ hτ),
      (A : GL (Fin n) M) ∈ heldSU n M τ hτ → ∃ A' : ↥(heldGU n M τ hτ),
        (A' : GL (Fin n) M) ∈ heldSU n M τ hτ ∧ g * ρ A * g⁻¹ = ρ A') :
    L = ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ := by
  obtain ⟨hEab, hEcard, h3mem, hxE, hxne, hxL, hLcomp, hEnorm, hECL, hDE, hDcard, hxD,
    hJcomp, hEJ⟩ := hC
  let S : Subgroup R := ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ
  have hn4 : 4 ≤ n := four_le_of_card hE hM hEcard
  have hSle : S ≤ Subgroup.centralizer ({x} : Set R) :=
    map_heldSU_le_centralizer hA₀ hx
  have hSsub : CFSG.Assembly.IsSubnormal S (Subgroup.centralizer ({x} : Set R)) :=
    map_heldSU_subnormal hA₀ hx hN
  have hSq : CFSG.Assembly.IsQuasisimple S := isQuasisimple_map_heldSU hτ2 hρ hM hn4
  have hScomp : IsComponentOf S (Subgroup.centralizer ({x} : Set R)) := ⟨hSle, hSsub, hSq⟩
  have hne : ⁅L, S⁆ ≠ ⊥ := commutator_map_heldSU_ne_bot hECL hM hn4 hτ2 hρ hE hc hA₀ hx
  have hLS : L ≤ S := by
    rcases isComponentOf_le_or_commutator_eq_bot hLcomp hSsub with h | h
    · exact h
    · exact absurd h hne
  have hSL : S ≤ L := by
    rcases isComponentOf_le_or_commutator_eq_bot hScomp hLcomp.2.1 with h | h
    · exact h
    · exfalso
      exact hne (by rwa [Subgroup.commutator_comm] at h)
  exact le_antisymm hLS hSL

end CFSG.StandardType

end
