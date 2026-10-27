module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTPNI1TypeAHelp
public import CFSG.LocalAnalysis.StandardType.GGTPNI1TypeADvd
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndNode
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.Models
public import CFSG.LargeExtraspecial.DWFldLinear
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompModel
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallALinearBlock
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarRealize
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLin
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.RankThree.CALinearPlane
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Blueprint CFSG.SeitzReduction.LinearPilot

private theorem tptc_linear_of_typeA_rawDatum {lab : LargeEvenLabel} {r f : ℕ}
    (h : lab = ⟨.A, r, f⟩ ∨ (r = 3 ∧ lab = ⟨.D, 3, f⟩)) {Q : LargeEvenRawCont}
    (hraw : LargeEvenRawDatum lab Q) :
    LargeEvenRecipeLinear (r + 1) (2 ^ f) Q := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · dsimp only [LargeEvenRawDatum] at hraw
    exact hraw
  · dsimp only [LargeEvenRawDatum] at hraw
    rw [if_pos rfl] at hraw
    simpa using hraw

private theorem tptc_ggDiagUnit_eq_toGL {K : Type} [Field K] {m : ℕ}
    {D : SpecialLinearGroup (Fin (m + 1)) K} {t : Fin (m + 1) → K}
    (hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = diagonal t) {e : Fin (m + 1) → Kˣ}
    (he : ∀ i, (e i : K) = t i) :
    ggDiagUnit e = SpecialLinearGroup.toGL D := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hD]
  change diagonal (fun i => (e i : K)) = diagonal t
  rw [show (fun i => (e i : K)) = t from funext he]

private theorem tptc_ggDiagConj_eq {K : Type} [Field K] {m : ℕ}
    {D : SpecialLinearGroup (Fin (m + 1)) K} {t : Fin (m + 1) → K}
    (hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = diagonal t) {e : Fin (m + 1) → Kˣ}
    (he : ∀ i, (e i : K) = t i) (s : SpecialLinearGroup (Fin (m + 1)) K) :
    ggDiagConj e s = D * s * D⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  show Matrix.SpecialLinearGroup.toGL
      (CatalogueBHigherLinearAction.slConjugation (m + 1) K (ggDiagUnit e) s) =
    Matrix.SpecialLinearGroup.toGL (D * s * D⁻¹)
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, tptc_ggDiagUnit_eq_toGL hD he]
  simp only [map_mul, map_inv]

private theorem tptc_lieModel_block {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {L : Type} [Group L] {φ' : SpecialLinearGroup (Fin (m + 1)) K →* L}
    (hker : φ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K))
    {f : ℕ} (hKcard : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {I : Finset (Fin (m + 1))} (hI2 : 2 ≤ I.card) :
    LieModel (↥((blockSpecialLinear I).map φ') ⧸ Subgroup.center _) .PSL I.card 2 f := by
  rcases (show I.card = 2 ∨ 3 ≤ I.card by omega) with h2 | h3
  · rw [h2]
    exact LinTypeAk.lieModel_map_blockSpecialLinear_of_card_two hKcard hf hker h2
  · exact LinTorus.lieModel_map_blockSpecialLinear hKcard (by omega) hker h3

private theorem tptc_hasLabel_of_lieModel {X : Type} [Group X] {n f : ℕ} (hn : n ≠ 0)
    (h : LieModel X .PSL n 2 f) : GGHasLabel ⟨.A, n - 1, f⟩ X := by
  have hcls := h.statedClassicalModel (by decide)
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
  exact ggHasLabel_typeA (n := n - 1) (f := f) (hn1 ▸ hcls)

theorem ggI1PairRankOn_TypeA_cop
    : GGI1PairRankOn fun p labL labJ => GGPairTypeA p labL labJ ∧ ¬ p ∣ labL.rank + 1 := by
  intro p hp hp2 L _ _ J y E labL labJ hL hJ hP hhL hhJ hy hyE hE hcomp hfix hmark
  classical
  obtain ⟨hAtag, hr3, hn2, hpdvd, hlabJeq⟩ := hP.1
  have hnotdvd : ¬ p ∣ labL.rank + 1 := hP.2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperfL, lab, hlab, hraw⟩ := hmark
  have hhasLab : GGHasLabel lab (L ⧸ Subgroup.center L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hlabL_eq : labL = ⟨.A, labL.rank, labL.n⟩ := by
    obtain ⟨tag, r, f⟩ := labL
    simp only [LargeEvenLabel.mk.injEq] at hAtag
    subst hAtag
    rfl
  have hhL' : GGHasLabel ⟨.A, labL.rank, labL.n⟩ (L ⧸ Subgroup.center L) := hlabL_eq ▸ hhL
  have hLΛ : LargeEvenInLambda2 ⟨.A, labL.rank, labL.n⟩ := hlabL_eq ▸ hL
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hcases : lab = ⟨.A, labL.rank, labL.n⟩ ∨ (labL.rank = 3 ∧ lab = ⟨.D, 3, labL.n⟩) :=
    ggLabelIso_typeA_cases hrig (r := labL.rank) (f := labL.n) (by omega) hlab hLΛ hhasLab hhL'
  have hrawLin := tptc_linear_of_typeA_rawDatum hcases hraw
  obtain ⟨K, _, _, hKcard, hQR⟩ := hrawLin
  obtain ⟨-, -, θ, hIndInn⟩ := hQR
  haveI : CharP K 2 := CFSG.LargeExtraspecial.DW.charP_two_of_card_eq hKcard
  let ψbar : L ⧸ Subgroup.center L ≃* projectiveSL (labL.rank + 1) K :=
    θ.trans (TypeA.recipeEquiv (labL.rank + 1) K)
  let ψ : L →* projectiveSL (labL.rank + 1) K :=
    ψbar.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hAI : ∀ a ∈ E, ∃ φa ∈ Set.range (conjAut (labL.rank + 1) K),
      ∀ l : L, φa (ψ l) = ψ (a l) := by
    intro a ha
    have hmem : ggInducedAut θ a ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin (labL.rank + 1)) K)) Set.univ := hIndInn a ha
    refine ⟨MulAut.congr (TypeA.recipeEquiv (labL.rank + 1) K) (ggInducedAut θ a),
      TypeA.congr_recipeEquiv_mem hmem, fun l => ?_⟩
    simp only [ψ, ψbar, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, ggInducedAut_apply, QuotientGroup.mk'_apply]
  have hperfSL : commutator (SpecialLinearGroup (Fin (labL.rank + 1)) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := labL.rank + 1) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hψs : Function.Surjective ψ := ψbar.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerψ : ψ.ker ≤ Subgroup.center L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    change ψbar (QuotientGroup.mk l) = 1 at hl
    have h2 : QuotientGroup.mk l = 1 := ψbar.injective (by rw [hl, map_one])
    exact (QuotientGroup.eq_one_iff l).mp h2
  have hpK : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpdvd
  have hpd : Nat.Coprime p (labL.rank + 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnotdvd
  have hpow4 : 4 ≤ 2 ^ labL.n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ labL.n := Nat.pow_le_pow_right (by norm_num) hn2
  have hsec : TypeA.SLHasSections (labL.rank + 1) K := by
    refine TypeA.slHasSections_of_card (by omega) ?_ ?_ ?_
    · intro h2; rw [hKcard] at h2; omega
    · rintro ⟨h3, -⟩; omega
    · rintro ⟨-, h3⟩; rw [hKcard] at h3; omega
  obtain ⟨φ, hφs, hφ⟩ := TypeA.exists_sl_cover hsec ψ hψs hkerψ hperfL
  obtain ⟨φ', hφ's, hφ'ker, hdiag, hle, hfull⟩ :=
    TypeA.exists_diagonal_model hp hpK (by omega) hpd hperfSL hψs hkerψ hperfL hφs hφ hE hAI
  have hφ'kerC : φ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (labL.rank + 1)) K) :=
    fun g hg => scalars_le_center (labL.rank + 1) K (hφ'ker g (MonoidHom.mem_ker.mp hg))
  obtain ⟨D_y, ⟨t, hD_y⟩, hD_yp, hy_act⟩ := hdiag y hyE
  have ht'p : ∀ i, t i ^ p = 1 := by
    intro i
    have h1 : (D_y : Matrix (Fin (labL.rank + 1)) (Fin (labL.rank + 1)) K) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hD_yp]; rfl
    rw [hD_y, Matrix.diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2
  have ht_ne : ∀ i, t i ≠ 0 := fun i h0 => by
    have h1 := ht'p i
    rw [h0, zero_pow hp.ne_zero] at h1
    exact zero_ne_one h1
  let e : Fin (labL.rank + 1) → Kˣ := fun i => Units.mk0 (t i) (ht_ne i)
  have he : ∀ i, (e i : K) = t i := fun _ => rfl
  let b : L := φ' D_y
  have hy_conj : y = MulAut.conj b := by
    ext l
    obtain ⟨s, rfl⟩ := hφ's l
    rw [hy_act s, MulAut.conj_apply]
    change φ' (D_y * s * D_y⁻¹) = φ' D_y * φ' s * (φ' D_y)⁻¹
    simp only [map_mul, map_inv]
  have hcent : ggAutFixedSubgroup y = Subgroup.centralizer ({b} : Set L) := by
    ext l
    rw [mem_ggAutFixedSubgroup, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [hy_conj, MulAut.conj_apply] at h
      calc l * b = (b * l * b⁻¹) * b := by rw [h]
        _ = b * l := by group
    · intro h
      rw [hy_conj, MulAut.conj_apply]
      calc b * l * b⁻¹ = l * b * b⁻¹ := by rw [h]
        _ = l := by group
  have hrange_top : φ'.range = ⊤ := MonoidHom.range_eq_top.mpr hφ's
  have hL' : IsComponentOf J (φ'.range ⊓ Subgroup.centralizer (Set.range (fun _ : Unit => b))) := by
    rw [hrange_top, Set.range_const, top_inf_eq, ← hcent]
    exact hcomp
  have hacts : GGActsVec φ' b e := by
    intro s
    rw [tptc_ggDiagConj_eq hD_y he s]
    change φ' D_y * φ' s * (φ' D_y)⁻¹ = φ' (D_y * s * D_y⁻¹)
    simp only [map_mul, map_inv]
  have hb_mem : ∀ _ : Unit, (b, InnerDiagA.diagGL e) ∈ LinFusion.ggInducedPairs φ' :=
    fun _ => ggActsVec_iff_mem_ggInducedPairs.mp hacts
  obtain ⟨i, hJi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf hφ'kerC
    (d := fun _ : Unit => e) (b := fun _ : Unit => b) hb_mem hL'
  set I : Finset (Fin (labL.rank + 1)) := LinSemisimple.eigClass (fun _ : Unit => e) i with hIdef
  have hI2 : 2 ≤ I.card := (LinSemisimple.two_le_card_of_isQuasisimple_le hL'.2.2 hJi.le).1
  have hIeq : I.card = labL.rank := by
    have hLie : LieModel (↥((blockSpecialLinear I).map φ') ⧸ Subgroup.center _) .PSL I.card 2 labL.n :=
      tptc_lieModel_block hφ'kerC hKcard hn2 hI2
    have hhasBlock : GGHasLabel ⟨.A, I.card - 1, labL.n⟩
        (↥((blockSpecialLinear I).map φ') ⧸ Subgroup.center _) :=
      tptc_hasLabel_of_lieModel (by omega) hLie
    have hhasJ : GGHasLabel ⟨.A, I.card - 1, labL.n⟩ (J ⧸ Subgroup.center J) := by
      rw [hJi]; exact hhasBlock
    have hcls := hLie.statedClassicalModel (by decide)
    have hΛblock : LargeEvenInLambda2 ⟨.A, I.card - 1, labL.n⟩ := by
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ I.card)] at hcls
      exact largeEvenInLambda2_typeA hcls
    have hΛJ : LargeEvenInLambda2 ⟨.A, labL.rank - 1, labL.n⟩ := by
      rw [← hlabJeq]; exact hJ
    have hJ' : GGHasLabel ⟨.A, labL.rank - 1, labL.n⟩ (J ⧸ Subgroup.center J) := by
      rw [← hlabJeq]; exact hhJ
    rcases ggLabelIso_typeA_cases hrig (r := labL.rank - 1) (f := labL.n) (by omega) hΛblock hΛJ
      hhasJ hJ' with heq | ⟨h3, hcontra⟩
    · rw [LargeEvenLabel.mk.injEq] at heq
      omega
    · rw [LargeEvenLabel.mk.injEq] at hcontra
      exact absurd hcontra.1 (by decide)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin (labL.rank + 1), i₀ ∉ I := by
    by_contra hcon
    rw [not_exists] at hcon
    have hIuniv : I = Finset.univ := Finset.eq_univ_of_forall (fun x => by
      by_contra hx
      exact hcon x hx)
    rw [hIuniv, Finset.card_univ, Fintype.card_fin] at hIeq
    omega
  have hIcompl : I = ({i₀}ᶜ : Finset (Fin (labL.rank + 1))) := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      simp only [Finset.mem_compl, Finset.mem_singleton]
      rintro rfl
      exact hi₀ hj
    · rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin, hIeq]
      omega
  have hii₀ : i ≠ i₀ := fun hh => hi₀ (hIdef ▸ (hh ▸ LinSemisimple.self_mem_eigClass _ i))
  have ht1 : ∀ a c, a ≠ i₀ → c ≠ i₀ → t a = t c := by
    intro a c ha hc
    have haI : a ∈ I := by rw [hIcompl]; simpa using ha
    have hcI : c ∈ I := by rw [hIcompl]; simpa using hc
    have h1 : e a = e i := (LinSemisimple.mem_eigClass.mp (hIdef ▸ haI)) ()
    have h2 : e c = e i := (LinSemisimple.mem_eigClass.mp (hIdef ▸ hcI)) ()
    have h3 := congrArg (fun u : Kˣ => (u : K)) (h1.trans h2.symm)
    rw [he a, he c] at h3
    exact h3
  have hti₀ : t i₀ ≠ t i := by
    intro h
    apply hi₀
    have hei : e i₀ = e i := by
      apply Units.ext
      rw [he i₀, he i, h]
    exact hIdef ▸ (LinSemisimple.mem_eigClass.mpr (fun _ => hei))
  have ht0 : ∀ j, j ≠ i₀ → t j ≠ t i₀ := by
    intro j hj h
    exact hti₀ (((ht1 j i hj hii₀).symm.trans h).symm)
  have hJeq : (coordBlockSL K ({i₀}ᶜ : Finset (Fin (labL.rank + 1)))).map φ' = J := by
    rw [blockSpecialLinear_eq_coordBlockSL, ← hIcompl, ← hJi]
  have hfixblock : ∀ a' ∈ E,
      (∀ j ∈ (coordBlockSL K ({i₀}ᶜ : Finset (Fin (labL.rank + 1)))).map φ', a' j = j) := by
    intro a' ha' j hj
    rw [hJeq] at hj
    exact hfix a' ha' j hj
  have hInonempty : I.Nonempty := Finset.card_pos.mp (by rw [hIeq]; omega)
  obtain ⟨j₁, hj₁I⟩ := hInonempty
  have hj₁ : j₁ ≠ i₀ := fun h => hi₀ (h ▸ hj₁I)
  have hj₁t : t j₁ = t i := by
    have h1 : e j₁ = e i := (LinSemisimple.mem_eigClass.mp (hIdef ▸ hj₁I)) ()
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    rw [he j₁, he i] at h2
    exact h2
  have hratio_ne : t i₀ / t j₁ ≠ 1 := by
    intro h
    apply hti₀
    rw [div_eq_one_iff_eq (ht_ne j₁)] at h
    exact h.trans hj₁t
  have hprim : IsPrimitiveRoot (t i₀ / t j₁) p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (by rw [div_pow, ht'p, ht'p, div_one]) hratio_ne)
  have hfinal := tpta_fixing_coordBlockSL_le_zpowers hp (by omega : 4 ≤ labL.rank + 1) hpd
    hφ's hφ'ker hE hyE ht0 ht1 hD_y hD_yp hy_act hdiag j₁ hj₁ hprim
  intro e' he'
  exact hfinal e' he' (hfixblock e' he')

theorem ggI1PairRankOn_TypeA
    : GGI1PairRankOn GGPairTypeA := by
  intro p hp hp2 L _ _ J y E labL labJ hL hJ hP hhL hhJ hy hyE hE hcomp hfix hmark
  by_cases hd : p ∣ labL.rank + 1
  · exact ggI1PairRankOn_TypeA_dvd p hp hp2 L J y E labL labJ hL hJ ⟨hP, hd⟩ hhL hhJ hy hyE hE
      hcomp hfix hmark
  · exact ggI1PairRankOn_TypeA_cop p hp hp2 L J y E labL labJ hL hJ ⟨hP, hd⟩ hhL hhJ hy hyE hE
      hcomp hfix hmark

end CFSG.StandardType

end
