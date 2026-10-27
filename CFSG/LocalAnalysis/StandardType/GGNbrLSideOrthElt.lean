module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitElt
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitExcl
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockModels
import CFSG.LocalAnalysis.StandardType.GGNbrLSideTransport
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourTrans
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitQuot
import CFSG.LocalAnalysis.StandardType.GGNbrLSideUniType
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitSL3
import CFSG.LocalAnalysis.StandardType.GGNbrLSideOrthSelfDual
import CFSG.LocalAnalysis.StandardType.GGNbrLSideOrthFixed
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthPairBlock
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsOrthBlock
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualEichler
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Defs
import CFSG.Quasithin.Vol2.Ch12Sec6P31Lie

public section

namespace CFSG.StandardType

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG CFSG.Open CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
  (orthPairedStatedSL orthPairedStatedSL_conj orthPairedMatrix)

theorem ggNbrLSideDichElt_of_mulEquiv {lab : LargeEvenLabel} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGNbrLSideDichElt lab R') : GGNbrLSideDichElt lab R := by
  intro a b ha1 ha3 hb3 hab J hJ q hq4 hq3 hF α hα
  have hJ' : CFSG.Open.IsComponentOf (J.map e.toMonoidHom)
      (Subgroup.centralizer ({e a} : Set R')) := by
    rw [← SpFour.map_centralizer_singleton e a]
    exact CFSG.Assembly.isComponentOf_iff_open.1
      ((SpFour.isComponentOf_map_iff e).2 (CFSG.Assembly.isComponentOf_iff_open.2 hJ))
  let eJ : ↥J ≃* ↥(J.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  let ε : ↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom) :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  have hε : ∀ j : ↥J, ε (QuotientGroup.mk j) = QuotientGroup.mk (eJ j) := fun j => by
    change QuotientGroup.congr _ _ eJ _ (QuotientGroup.mk' _ j) = _
    rw [QuotientGroup.congr_mk']
    rfl
  obtain ⟨F, hFf, hFfin, hFq, ⟨eF⟩⟩ := hF
  have hα' : GGNbrLSideInduces (MulAut.conj (e b)) (J.map e.toMonoidHom) (MulAut.congr ε α) := by
    intro j'
    obtain ⟨j, rfl⟩ := eJ.surjective j'
    obtain ⟨j₂, hj₂, hj₂α⟩ := hα j
    refine ⟨eJ j₂, ?_, ?_⟩
    · change e (j₂ : R) = (MulAut.conj (e b)) (e (j : R))
      rw [hj₂, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    · have h1 : ε.symm (QuotientGroup.mk (eJ j)) = QuotientGroup.mk j := by
        rw [← hε j, MulEquiv.symm_apply_apply]
      show ε (α (ε.symm (QuotientGroup.mk (eJ j)))) = QuotientGroup.mk (eJ j₂)
      rw [h1, hj₂α, hε j₂]
  rcases h (e a) (e b) (fun h1 => ha1 (e.injective (by rw [h1, map_one])))
      (by rw [← map_pow, ha3, map_one]) (by rw [← map_pow, hb3, map_one])
      (by rw [← map_mul, ← map_mul, hab]) (J.map e.toMonoidHom) hJ' q hq4 hq3
      ⟨F, hFf, hFfin, hFq, ⟨ε.symm.trans eF⟩⟩ (MulAut.congr ε α) hα' with hinn | hlr
  · exact Or.inl (ggInnDiagPSL3_of_congr ε hinn)
  · exact Or.inr hlr

private theorem ggNbrLSideOrth_exists_ne_zero {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) : ∃ v, Q v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨U, hU3, -⟩ := hT
  have hpos : 0 < finrank K V := lt_of_lt_of_le (by omega) (hU3 ▸ Submodule.finrank_le U)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine hv (hQ.1 v fun w => ?_)
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hcon, hcon, hcon]
  simp

private theorem ggNbrLSideOrth_one_le {K : Type} [Field K] [Finite K] {f : ℕ}
    (hcard : Nat.card K = 2 ^ f) : 1 ≤ f := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · rw [h0, pow_zero] at hcard
    omega
  · exact h0

private theorem ggNbrLSideOrth_elt_T {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (hDet : GGNbrLSideClsDet) (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (lab : LargeEvenLabel) : GGNbrLSideDichElt lab (ProjOrthDerived Q) := by
  classical
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hcard
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hf : 1 ≤ f := ggNbrLSideOrth_one_le hcard
  have hinj := CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_mk'_injective
    (ggNbrLSideOrth_exists_ne_zero hQ hT) (Q := Q)
  intro a b ha1 ha3 hb3 hab J hJ q hq4 hq3 hF α hα
  obtain ⟨x, hxa, hx, hcases⟩ := CFSG.LocalAnalysis.GLTheoremA.K1419.orth_component_named
    Nat.prime_three (by norm_num) hQ hT (by rw [hchar]; norm_num) a ha3 J hJ
  obtain ⟨y, hyb⟩ := QuotientGroup.mk_surjective b
  have hxa' : (QuotientGroup.mk x : ProjOrthDerived Q) = a := hxa
  have hxy : x * y = y * x := by
    apply hinj
    show (QuotientGroup.mk (x * y) : ProjOrthDerived Q) = QuotientGroup.mk (y * x)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hxa', hyb, hab]
  obtain ⟨F', _, _, hF'q, ⟨eF⟩⟩ := hF
  have hF4 : 4 ≤ Nat.card F' := by omega
  rcases hcases with ⟨h, hh, hne1, hq, hJeq⟩ | ⟨F, hFq, hFle, hFn, hJeq⟩
  · haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    have hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) := by
      refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val hxy).symm
    rw [componentImage] at hJeq
    subst hJeq
    obtain ⟨e₂⟩ := ggNbrLSideQuot_map_equiv _ hinj
      ((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q))
    let eSB : ↥((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)) ≃*
        ↥(specialBlock Q (x : V ≃ₗ[K] V) h) := Subgroup.subgroupOfEquivOfLe hspecΩ
    let e₃ := e₂.trans (QuotientGroup.congr _ _ eSB (Subgroup.map_center_eq eSB))
    by_cases hself : h = reciprocalPolynomial h
    ·
      exfalso
      obtain ⟨t, m, k, hcs, hmodel⟩ :=
        ggNbrLSideOrth_selfDual_type hx hchar hh hne1 hself hq
      have hmodelJ := hmodel.of_mulEquiv e₃.symm
      obtain ⟨h1, h2, -⟩ := ggNbrLSideExcl hDet hO hF4 eF hmodelJ
      rcases hcs with ⟨h3, -⟩ | ⟨-, h3⟩
      · exact absurd (h3.symm.trans h1) (by decide)
      · omega
    ·
      have hne : h ≠ reciprocalPolynomial h := hself
      have hE : Nat.card (AdjoinRoot h) = 2 ^ (f * h.natDegree) := by
        rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hcard, pow_mul]
      have hdeg : 1 ≤ f * h.natDegree :=
        Nat.mul_pos hf (Fact.out : Irreducible h).natDegree_pos
      have hmodel := ggNbrLSideUni_typeSL hdeg hE (orthPairedStatedSL hx hh hne) hq
      have hmodelJ := hmodel.of_mulEquiv e₃.symm
      obtain ⟨-, hn3, hFcard⟩ := ggNbrLSideExcl hDet hO hF4 eF hmodelJ
      have hycen : (y : V ≃ₗ[K] V) ∈
          Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) :=
        (Subgroup.mem_inf.mp hyc).2
      have hc : ∀ s ∈ (specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q),
          y * s * y⁻¹ ∈ (specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q) :=
        fun s hs => conj_mem_specialBlock hyc (Subgroup.mem_subgroupOf.mp hs)
      have hsub0 : ∀ s : ↥((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)),
          (y : V ≃ₗ[K] V)⁻¹ * (eSB ⟨y * s * y⁻¹, hc s s.2⟩).1 * (y : V ≃ₗ[K] V) =
            (eSB s).1 := fun s => by
        show (y : V ≃ₗ[K] V)⁻¹ * ((y : V ≃ₗ[K] V) * ((s : ↥(orthDerived Q)) : V ≃ₗ[K] V) *
          (y : V ≃ₗ[K] V)⁻¹) * (y : V ≃ₗ[K] V) = ((s : ↥(orthDerived Q)) : V ≃ₗ[K] V)
        group
      have hconj : ∀ s : ↥((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)),
          (((orthPairedStatedSL hx hh hne (eSB ⟨y * s * y⁻¹, hc s s.2⟩) :
            ↥(StatedSL _ (AdjoinRoot h))) : Matrix.GeneralLinearGroup _ (AdjoinRoot h))) =
            orthPairedMatrix (x := x) (h := h) hycen *
              (((orthPairedStatedSL hx hh hne (eSB s) : ↥(StatedSL _ (AdjoinRoot h))) :
                Matrix.GeneralLinearGroup _ (AdjoinRoot h))) *
              (orthPairedMatrix (x := x) (h := h) hycen)⁻¹ := fun s => by
        have hd : (y : V ≃ₗ[K] V)⁻¹ * (eSB ⟨y * s * y⁻¹, hc s s.2⟩).1 * (y : V ≃ₗ[K] V) ∈
            specialBlock Q (x : V ≃ₗ[K] V) h := by
          rw [hsub0 s]
          exact (eSB s).2
        have key := orthPairedStatedSL_conj hx hh hne hycen
          (d := eSB ⟨y * s * y⁻¹, hc s s.2⟩) hd
        have hsub : (⟨(y : V ≃ₗ[K] V)⁻¹ * (eSB ⟨y * s * y⁻¹, hc s s.2⟩).1 * (y : V ≃ₗ[K] V), hd⟩ :
            ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) = eSB s := Subtype.ext (hsub0 s)
        rw [hsub] at key
        rw [key]
        group
      have hQK : q = Nat.card (AdjoinRoot h) := by rw [← hF'q, hFcard, hE]
      subst hyb
      rw [hQK]
      left
      exact ggNbrLSideSL3Witness _ hinj hn3 _ ((eSB).trans (orthPairedStatedSL hx hh hne)) y hc
        (orthPairedMatrix (x := x) (h := h) hycen) hconj α hα
  ·
    exfalso
    have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
    obtain ⟨t, m, k, hnot, hmodel⟩ := ggNbrLSideOrth_fixed_type hx hchar hFq hFle hFn
    subst hJeq
    obtain ⟨e₂⟩ := ggNbrLSideQuot_map_equiv _ hinj (F.subgroupOf (orthDerived Q))
    let eFB : ↥(F.subgroupOf (orthDerived Q)) ≃* ↥F := Subgroup.subgroupOfEquivOfLe hFΩ
    let e₃ := e₂.trans (QuotientGroup.congr _ _ eFB (Subgroup.map_center_eq eFB))
    have hmodelJ := hmodel.of_mulEquiv e₃.symm
    obtain ⟨h1, h2, -⟩ := ggNbrLSideExcl hDet hO hF4 eF hmodelJ
    exact hnot ⟨h1, h2⟩

theorem ggNbrLSideOrth_elt {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {f : ℕ} (hcard : Nat.card K = 2 ^ f) {R : Type} [Group R] (e : R ≃* ProjOrthDerived Q)
    (hDet : GGNbrLSideClsDet) (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (lab : LargeEvenLabel) : GGNbrLSideDichElt lab R :=
  ggNbrLSideDichElt_of_mulEquiv e (ggNbrLSideOrth_elt_T hQ hT hcard hDet hO lab)

end CFSG.StandardType

end
