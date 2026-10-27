module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGenFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUO
public import CFSG.RankThree.PartOne.AUTSL.OmegaOut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3D4Blk
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Cases
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Indep
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDX
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharOmTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU4
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Maximal
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecOrthFact
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGU
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSympMain
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import Certificates.Certificate14953
public import Certificates.Certificate2246
public import Certificates.Certificate5133
public import Certificates.Certificate7233Base

public section

namespace CFSG.StandardType

namespace NoOffOm

open Matrix Module SUTB Multiplicative
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Fix

variable {K : Type} [Field K] {d : ℕ}

theorem coe_glFieldAut_apply (θ : K ≃+* K) (X : GL (Fin d) K) :
    ((glFieldAut (Fin d) K θ X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (X : Matrix (Fin d) (Fin d) K).map θ := rfl

theorem glin_eq_self_iff_of_conjField {X X' A' : GL (Fin d) K} {θ : K ≃+* K}
    (hX' : X' = A' * glFieldAut (Fin d) K θ X * A'⁻¹) (v : Fin d → K) :
    glin X' v = v ↔
      glin X (fun i => θ.symm ((((A'⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) i)) =
        fun i => θ.symm ((((A'⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) i) := by
  set w : Fin d → K :=
    fun i => θ.symm ((((A'⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) i) with hw
  have hθw : (fun i => θ (w i)) = ((A'⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v := by
    funext i
    simp [hw]
  have hAA : ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((A'⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hv : v = ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (fun i => θ (w i)) := by
    rw [hθw, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hlin : glin X' v = ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
      (fun i => θ (((X : Matrix (Fin d) (Fin d) K) *ᵥ w) i)) := by
    rw [glin_apply, hX', Units.val_mul, Units.val_mul, coe_glFieldAut_apply,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hθw]
    congr 1
    funext i
    exact (RingHom.map_mulVec (θ : K →+* K) _ _ i).symm
  have hinjA : Function.Injective fun x : Fin d → K =>
      ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x := by
    intro x y hxy
    have h1 := congrArg (fun z => ((A'⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ z) hxy
    simp only [Matrix.mulVec_mulVec] at h1
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.one_mulVec] at h1
  rw [hlin, glin_apply]
  constructor
  · intro h1
    conv_rhs at h1 => rw [hv]
    have h2 := hinjA h1
    funext i
    exact θ.injective (congrFun h2 i)
  · intro h1
    conv_rhs => rw [hv]
    rw [h1]

theorem exists_conjField_preimage (A' : GL (Fin d) K) (θ : K ≃+* K) (w : Fin d → K) :
    ∃ v, (fun i => θ.symm ((((A'⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) i)) = w := by
  refine ⟨((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ fun i => θ (w i), ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  funext i
  simp

end Fix

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {G : Type} [Group G]

noncomputable abbrev polB (Q : QuadraticForm K (Fin d → K)) :
    (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K :=
  QuadraticMap.polarBilin Q

omit [Finite K] [CharP K 2] in
theorem polB_apply (x y : Fin d → K) : polB Q x y = QuadraticMap.polar Q x y := rfl

omit [Finite K] [CharP K 2] in
theorem polB_isSymm : (polB Q).IsSymm :=
  ⟨fun x y => by rw [RingHom.id_apply, polB_apply, polB_apply, QuadraticMap.polar_comm]⟩

omit [Finite K] [CharP K 2] in
theorem quad_add (x y : Fin d → K) : Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y := by
  rw [QuadraticMap.polar]
  ring

omit [Finite K] [CharP K 2] in
theorem polB_glin_of_mem_isometries {X : GL (Fin d) K} (hX : X ∈ matrixIsometries Q)
    (v w : Fin d → K) : polB Q (glin X v) (glin X w) = polB Q v w := by
  rw [mem_matrixIsometries_iff] at hX
  have h1 := hX v
  have h2 := hX w
  have h3 := hX (v + w)
  rw [matrixLinearEquiv_apply] at h1 h2 h3
  rw [Matrix.mulVec_add] at h3
  rw [polB_apply, polB_apply, glin_apply, glin_apply, QuadraticMap.polar, QuadraticMap.polar, h1,
    h2, h3]

omit [Finite K] [CharP K 2] in
theorem restrictElt_quad {W : Submodule K (Fin d → K)} (hW : NondegOn (polB Q) W)
    {c : Module.End K (Fin d → K)} (hc : ∀ w ∈ W, c w ∈ W) (hcQ : ∀ v, Q (c v) = Q v)
    (v : Fin d → K) : Q (restrictElt hW c hc v) = Q v := by
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth hW v
  rw [map_add, restrictElt_apply_of_mem hW hc hm, restrictElt_apply_of_mem_orth hW hc hz]
  have hpol : ∀ a ∈ W, QuadraticMap.polar Q a z = 0 := fun a ha =>
    (Submodule.mem_orthogonalBilin.mp hz) a ha
  rw [quad_add, quad_add, hpol _ (hc m hm), hpol m hm, hcQ]

omit [Finite K] [CharP K 2] in
theorem mem_comap_map_iff {Bs : Subgroup G} {φ : matrixDerived Q →* G} {X : GL (Fin d) K} :
    X ∈ (Bs.comap φ).map (matrixDerived Q).subtype ↔
      ∃ Y : matrixDerived Q, φ Y ∈ Bs ∧ (Y : GL (Fin d) K) = X := Iff.rfl

omit [CharP K 2] in
theorem genMax_of_orth (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G} (hBs : CFSG.Assembly.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (φ : matrixDerived Q →* G) (hφ : Function.Injective φ) (hBφ : Bs ≤ φ.range) :
    GenMax (polB Q) (matrixDerived Q) p ((Bs.comap φ).map (matrixDerived Q).subtype) := by
  have hpowA : ∀ X ∈ (Bs.comap φ).map (matrixDerived Q).subtype, X ^ p = 1 := by
    rintro _ ⟨Y, hY, rfl⟩
    have h1 : φ (Y ^ p) = 1 := by rw [map_pow]; exact hBs.2 _ hY
    have h2 : Y ^ p = 1 := hφ (h1.trans (map_one φ).symm)
    rw [← map_pow, h2, map_one]
  refine
    { symm := polB_isSymm
      sep := hnd.1
      prime := hp
      ne_two := hp2
      le := Subgroup.map_subtype_le _
      pow := hpowA
      comm := ?_
      max := ?_
      iso := ?_
      restr := ?_ }
  · rintro _ ⟨Y, hY, rfl⟩ _ ⟨Y', hY', rfl⟩
    have h1 : φ (Y * Y') = φ (Y' * Y) := by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hBs hY hY'
    exact congrArg Subtype.val (hφ h1)
  · intro g hg hgp hcomm
    refine ⟨⟨g, hg⟩, hSC _ ?_ ?_, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨Y, rfl⟩ := hBφ hb
      have h1 := hcomm (Y : GL (Fin d) K) ⟨Y, hb, rfl⟩
      have h2 : (⟨g, hg⟩ : matrixDerived Q) * Y = Y * ⟨g, hg⟩ := Subtype.ext h1
      rw [← map_mul, ← map_mul, h2]
    · have h1 : (⟨g, hg⟩ : matrixDerived Q) ^ p = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow]
        exact hgp)
      rw [← map_pow, h1, map_one]
  · rintro _ ⟨Y, hY, rfl⟩ v w
    exact polB_glin_of_mem_isometries (matrixDerived_le_isometries Q Y.2) v w
  · intro c hc W hW hWA
    have hcp : glin c ^ p = 1 := by rw [← glin_pow, hpowA c hc, glin_one]
    have hcI : c ∈ matrixIsometries Q := by
      obtain ⟨Y, -, rfl⟩ := hc
      exact matrixDerived_le_isometries Q Y.2
    have hcQ : ∀ v, Q (glin c v) = Q v := fun v => by
      rw [glin_apply, ← matrixLinearEquiv_apply]
      exact (mem_matrixIsometries_iff Q c).mp hcI v
    set u := restrictElt hW (glin c) (hWA c hc) with hu
    have hup : u ^ p = 1 := restrictElt_pow_eq_one hW _ hcp
    set M := LinearMap.toMatrixAlgEquiv' u with hM
    have hMv : ∀ v, M *ᵥ v = u v := by
      intro v
      rw [← Matrix.toLinAlgEquiv'_apply, hM, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
    have hMp : M ^ p = 1 := by rw [hM, ← map_pow, hup, map_one]
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hMM : M * M ^ (p - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hp1, hMp]
    have hMM' : M ^ (p - 1) * M = 1 := by rw [← pow_succ, Nat.sub_add_cancel hp1, hMp]
    let g₀ : GL (Fin d) K := ⟨M, M ^ (p - 1), hMM, hMM'⟩
    have hg₀ : glin g₀ = u := LinearMap.ext fun v => by rw [glin_apply]; exact hMv v
    have hiso : g₀ ∈ matrixIsometries Q := (mem_matrixIsometries_iff Q g₀).mpr fun v => by
      rw [matrixLinearEquiv_apply]
      change Q (M *ᵥ v) = Q v
      rw [hMv]
      exact restrictElt_quad hW (hWA c hc) hcQ v
    have hg₀p : g₀ ^ p = 1 := glin_injective (by rw [glin_pow, hg₀, hup, glin_one])
    have hodd : Odd (orderOf g₀) := Odd.of_dvd_nat (hp.odd_of_ne_two hp2)
      (orderOf_dvd_of_pow_eq_one hg₀p)
    exact ⟨g₀, CFSG.ComponentClassification.HarrisLit.T1.P58b3D4.mem_matrixDerived_of_odd hnd hT
      hiso hodd, hg₀⟩

theorem exists_monoFrame_of_orthModel (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs M : Subgroup G}
    (hBs : CFSG.Assembly.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (φ : matrixDerived Q →* G) (hφ : Function.Injective φ) (hBφ : Bs ≤ φ.range)
    (haut : ∀ g ∈ M, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
      ∃ g' : similarityPairs Q, ∀ X : matrixDerived Q,
        φ (CFSG.RankThree.PartOne.AUTSL.conjAct Q g' X) = g⁻¹ * φ X * g) :
    ∃ (r : ℕ) (ι : Multiplicative (Fin r → ZMod p) →* G), Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ M, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 → NoOffUO.GGMonoAct ι g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hA := genMax_of_orth hnd hT hp hp2 hBs hSC φ hφ hBφ
  obtain ⟨r, ι₀, hinj₀, hrange₀, hsupp₀⟩ := exists_genPieceFrame hA
  have hι₀A : ∀ s, ι₀ s ∈ (Bs.comap φ).map (matrixDerived Q).subtype := fun s =>
    hrange₀ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hι₀Γ : ∀ s, ι₀ s ∈ matrixDerived Q := fun s => hA.le (hι₀A s)
  let ι₁ : Multiplicative (Fin r → ZMod p) →* matrixDerived Q := ι₀.codRestrict _ hι₀Γ
  have hι₁ : ∀ s, ((ι₁ s : matrixDerived Q) : GL (Fin d) K) = ι₀ s := fun s => rfl
  have hinj : Function.Injective (φ.comp ι₁) := fun s t hst =>
    hinj₀ (by rw [← hι₁, ← hι₁, hφ hst])
  have hrange : (φ.comp ι₁).range = Bs := by
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨Y, hY, hYs⟩ := hι₀A s
      have hYι : Y = ι₁ s := Subtype.ext hYs
      rw [MonoidHom.comp_apply, ← hYι]
      exact hY
    · intro hb
      obtain ⟨Y, rfl⟩ := hBφ hb
      have hYA : (Y : GL (Fin d) K) ∈ ι₀.range := by rw [hrange₀]; exact ⟨Y, hb, rfl⟩
      obtain ⟨s, hs⟩ := hYA
      exact ⟨s, by rw [MonoidHom.comp_apply]; exact congrArg φ (Subtype.ext hs)⟩
  refine ⟨r, φ.comp ι₁, hinj, hrange, fun g hgM hgB hgp => ?_⟩
  obtain ⟨g', hg'⟩ := haut g hgM hgB hgp
  have hc : ∀ X : matrixDerived Q,
      ((CFSG.RankThree.PartOne.AUTSL.conjAct Q g' X : matrixDerived Q) : GL (Fin d) K) =
        g'.val.left * glFieldAut (Fin d) K g'.val.right (X : GL (Fin d) K) * g'.val.left⁻¹ :=
    fun X => matrixDerivedConjugation_val Q g' X
  set R : G → G → Prop := fun b b' => ∀ X X' : matrixDerived Q, φ X = b → φ X' = b' →
    ∀ v, glin (X' : GL (Fin d) K) v = v → glin (X : GL (Fin d) K) v = v with hR
  have hRiff : ∀ X X' : matrixDerived Q, R (φ X) (φ X') ↔
      ∀ v, glin (X' : GL (Fin d) K) v = v → glin (X : GL (Fin d) K) v = v := by
    intro X X'
    constructor
    · intro h v hv
      exact h X X' rfl rfl v hv
    · intro h Y Y' hY hY' v hv
      rw [hφ hY]
      rw [hφ hY'] at hv
      exact h v hv
  have hRι : ∀ s s', R (φ.comp ι₁ (ofAdd s)) (φ.comp ι₁ (ofAdd s')) ↔ SuppLE s s' :=
    fun s s' => (hRiff _ _).trans (hsupp₀ s s')
  have hRg : ∀ s s', R (g⁻¹ * φ.comp ι₁ (ofAdd s) * g) (g⁻¹ * φ.comp ι₁ (ofAdd s') * g) ↔
      R (φ.comp ι₁ (ofAdd s)) (φ.comp ι₁ (ofAdd s')) := by
    intro s s'
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hg', ← hg', hRiff, hRiff]
    constructor
    · intro himp w hw
      obtain ⟨v, rfl⟩ := exists_conjField_preimage g'.val.left g'.val.right w
      exact (glin_eq_self_iff_of_conjField (hc _) v).mp
        (himp v ((glin_eq_self_iff_of_conjField (hc _) v).mpr hw))
    · intro himp v hv
      exact (glin_eq_self_iff_of_conjField (hc _) v).mpr
        (himp _ ((glin_eq_self_iff_of_conjField (hc _) v).mp hv))
  exact monoAct_of_suppRel hinj (hrange ▸ hgB) R hRι hRg

end Model

end NoOffOm

end CFSG.StandardType
