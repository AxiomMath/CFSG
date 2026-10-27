module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthMinusShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTAOne
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTATwo
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTTwATwo
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTDFour
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOrthTransModel
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusModel

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

section OrthMinusShapeRHelpers

private theorem orthMinusShapeR_ggAutFixedSubgroup_map {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (f : MulAut X) :
    (ggAutFixedSubgroup f).map e.toMonoidHom = ggAutFixedSubgroup (MulAut.congr e f) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ggAutFixedSubgroup] at hx ⊢
    simp [MulAut.congr_apply, hx]
  · intro hy
    rw [mem_ggAutFixedSubgroup] at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_ggAutFixedSubgroup]
    have h := congrArg e.symm hy
    simpa [MulAut.congr_apply] using h

private theorem orthMinusShapeR_congr_symm_congr {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (f : MulAut X) : MulAut.congr e.symm (MulAut.congr e f) = f := by
  ext x
  simp [MulAut.congr_apply]

private theorem orthMinusShapeR_rdatum_map {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (h : RDatum A δ J) :
    RDatum (A.map (MulAut.congr e).toMonoidHom) (MulAut.congr e δ) (J.map e.toMonoidHom) where
  elem := CFSG.SectionRank.isElemAbelian_map h.elem _
  mem := Subgroup.mem_map_of_mem _ h.mem
  ne_one := fun h1 => h.ne_one ((MulAut.congr e).injective (by rw [h1, map_one]))
  comp := by
    have h1 := CFSG.StandardType.isComponentOf_map_mulEquiv' e h.comp
    rwa [orthMinusShapeR_ggAutFixedSubgroup_map e δ] at h1
  uniq := by
    intro Q hQ
    have hQ' : IsComponentOf (Q.map e.symm.toMonoidHom) (ggAutFixedSubgroup δ) := by
      have h1 := CFSG.StandardType.isComponentOf_map_mulEquiv' e.symm hQ
      rw [orthMinusShapeR_ggAutFixedSubgroup_map e.symm (MulAut.congr e δ)] at h1
      rwa [orthMinusShapeR_congr_symm_congr e δ] at h1
    have hJ := h.uniq (Q.map e.symm.toMonoidHom) hQ'
    have hmap : (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
        ext x; simp
      rw [hcomp, Subgroup.map_id]
    rw [← hmap, hJ]
  norm := by
    intro a ha j hj
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
    change (MulAut.congr e a₀) (e j₀) ∈ J.map e.toMonoidHom
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.norm a₀ ha₀ j₀ hj₀)
  ker := by
    intro a ha hfix
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have hfix₀ : ∀ j ∈ J, a₀ j = j := by
      intro j hj
      have h1 := hfix (e j) (Subgroup.mem_map_of_mem e.toMonoidHom hj)
      change (MulAut.congr e a₀) (e j) = e j at h1
      rw [MulAut.congr_apply] at h1
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
      exact e.injective h1
    have hker := h.ker a₀ ha₀ hfix₀
    change (MulAut.congr e).toMonoidHom a₀ ∈
      Subgroup.zpowers ((MulAut.congr e).toMonoidHom δ)
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hker
  card := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
    exact h.card

private theorem orthMinusShapeR_congr_mem_innSet {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {φ : MulAut X} (h : φ ∈ LargeEvenInnSet X) :
    MulAut.congr e φ ∈ LargeEvenInnSet Y := by
  simp only [LargeEvenInnSet, Set.mem_range] at h ⊢
  obtain ⟨x, rfl⟩ := h
  exact ⟨e x, by ext y; simp [MulAut.congr_apply, MulAut.conj_apply]⟩

private theorem orthMinusShapeR_ggHasLabel_congr {lab : LargeEvenLabel} {R R' : Type}
    [Group R] [Group R'] (h : GGHasLabel lab R) (e : R ≃* R') : GGHasLabel lab R' :=
  CFSG.StandardType.largeEvenRawDatum_mono (fun _ _ _ _ hQ => ⟨e.symm.trans hQ.some⟩) h

private noncomputable def orthMinusShapeR_quotientCenterMapEquiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (K : Subgroup X) :
    (K.map e.toMonoidHom) ⧸ Subgroup.center (K.map e.toMonoidHom) ≃* K ⧸ Subgroup.center K :=
  (QuotientGroup.congr (Subgroup.center K) (Subgroup.center (K.map e.toMonoidHom))
    (e.subgroupMap K) (Subgroup.map_center_eq (e.subgroupMap K))).symm

private theorem orthMinusShapeR_center_map_ne_bot {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (K : Subgroup X) :
    Subgroup.center (K.map e.toMonoidHom) ≠ ⊥ → Subgroup.center K ≠ ⊥ := by
  intro hne hbot
  apply hne
  have h : (Subgroup.center K).map (e.subgroupMap K).toMonoidHom =
      Subgroup.center (K.map e.toMonoidHom) := Subgroup.map_center_eq (e.subgroupMap K)
  rw [← h, hbot]
  exact Subgroup.map_bot _

private theorem orthMinusShapeR_D4_numerics {r n : ℕ} (h5 : 5 ≤ r) (h7 : r ≤ 7)
    (hn3 : 3 ≤ n → r ≤ 5) (hodd4 : Odd (r - 4)) (hno : Odd n) :
    r = 5 ∨ (r = 7 ∧ n = 1) := by
  have hro : Odd r := by
    have h := hodd4.add_even (show Even 4 by norm_num)
    rwa [Nat.sub_add_cancel (by omega : 4 ≤ r)] at h
  have hr : r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases hr with h | h | h
  · exact Or.inl h
  · rw [h] at hro
    obtain ⟨k, hk⟩ := hro
    omega
  · refine Or.inr ⟨h, ?_⟩
    have hnlt : n < 3 := by
      by_contra hge
      exact absurd (hn3 (Nat.le_of_not_lt hge)) (by omega)
    obtain ⟨k, hk⟩ := hno
    omega

end OrthMinusShapeRHelpers

theorem orthMinusR_shape
    {K : Type} [Field K] [Finite K] [CharP K 2] {n r : ℕ} (hK : Nat.card K = 2 ^ n)
    (hr : 4 ≤ r) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {Ā : Subgroup (MulAut (POmMinusG (r - 1) K b c))} {δ' : MulAut (POmMinusG (r - 1) K b c)}
    {J' : Subgroup (POmMinusG (r - 1) K b c)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (POmMinusG (r - 1) K b c)) :
    OrthMinusShapeConcl n r Ā J' := by
  let e := CFSG.LocalAnalysis.GLTheoremA.T171Sh.orthModelEquivMinus r K b c
  let Ā' : Subgroup (MulAut (ProjOrthDerived (CFSG.LieType.Universal.Spin.quadMinus r K b c))) :=
    Ā.map (MulAut.congr e).toMonoidHom
  let δ'' : MulAut (ProjOrthDerived (CFSG.LieType.Universal.Spin.quadMinus r K b c)) :=
    MulAut.congr e δ'
  let J'' : Subgroup (ProjOrthDerived (CFSG.LieType.Universal.Spin.quadMinus r K b c)) :=
    J'.map e.toMonoidHom
  have hR' : RDatum Ā' δ'' J'' := orthMinusShapeR_rdatum_map e hR
  have hĀI' : ∀ a ∈ Ā', a ∈ LargeEvenInnSet
      (ProjOrthDerived (CFSG.LieType.Universal.Spin.quadMinus r K b c)) := by
    rintro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    exact orthMinusShapeR_congr_mem_innSet e (hĀI a₀ ha₀)
  have hQ : (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus r K b c)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite r K hbc
  have hT : ∃ U : Submodule K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K),
      Module.finrank K U = 3 ∧ ∀ u ∈ U, CFSG.LieType.Universal.Spin.quadMinus r K b c u = 0 :=
    CFSG.StandardType.GGOppRadOmega.exists_finrank_three_quadMinus (n := r) hr
  have hdim : Module.finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) = 2 * r :=
    CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (K := K) (m := r) (by omega)
  obtain ⟨lab, hlab2, hlab, hdisj⟩ := orthT_label hK hQ hT hR' hĀI'
  rcases lab with ⟨ltag, lrank, ln⟩
  have hlabJ' : GGHasLabel ⟨ltag, lrank, ln⟩ (J' ⧸ Subgroup.center J') :=
    orthMinusShapeR_ggHasLabel_congr hlab (orthMinusShapeR_quotientCenterMapEquiv e J')
  refine ⟨⟨ltag, lrank, ln⟩, hlab2, hlabJ', ?_⟩
  rcases hdisj with hA | htwA | hB | hC | hD
  ·
    subst hA
    refine Or.inl ⟨rfl, ?_, ?_⟩
    · intro hrank1
      subst hrank1
      have h1 := orthT_A1 hK hQ hT hR' hĀI' hlab
      rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at h1
    · intro hrank2
      subst hrank2
      have h1 := orthT_A2 hK hQ hT hR' hĀI' hlab
      exact orthMinusShapeR_center_map_ne_bot e J' h1
  ·
    obtain ⟨htag, hrank⟩ := htwA
    subst htag
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    intro hrank2
    subst hrank2
    have h1 := orthT_twA2 hK hQ hT hR' hĀI' (r := r) hdim hlab
    exact ⟨orthMinusShapeR_center_map_ne_bot e J' h1.1, h1.2⟩
  ·
    subst hB
    exact Or.inr (Or.inr (Or.inl rfl))
  ·
    subst hC
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  ·
    obtain ⟨hDor, hrank4, hln⟩ := hD
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hDor, hrank4, hln, ?_⟩)))
    intro hDtag hrank4' hnodd
    subst hDtag
    subst hrank4'
    subst hln
    have h1 := orthT_D4 hK hQ hT hR' hĀI' (r := r) hdim hnodd hlab
    have hne : ¬ Even (r - 4) := fun he =>
      CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := r) (by omega) hbc (h1.2.1.mpr he)
    exact orthMinusShapeR_D4_numerics h1.1 h1.2.2.2 h1.2.2.1 (Nat.not_even_iff_odd.mp hne) hnodd

end CFSG.StandardType.TablePThreeKG

end
