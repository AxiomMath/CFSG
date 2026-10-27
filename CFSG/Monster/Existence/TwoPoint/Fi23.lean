
module

public import CFSG.Monster.Existence.TwoPoint.Fi23Base
import all CFSG.Monster.Existence.TwoPoint.Fi23Base

public import CFSG.Monster.Existence.TwoPoint.Fi23Rels0
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels1
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels2
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels3
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels4
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels5
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongAD
public import CFSG.Monster.Existence.TwoPoint.Fi23Misc
public import CFSG.Monster.Existence.TwoPoint.Fi23Conj
public import CFSG.Sporadic.Bridge.Fi23Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate16009

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem fiMiscCheck_parts :
    (∀ i, i < 10 → wordLin fiWU[i]! * wordLin fiWAlpha = wordLin fiWAlpha * wordLin fiWU[i]!) ∧
      (∀ i, i < 10 → wordLin fiWU[i]! * wordLin fiWBeta = wordLin fiWBeta * wordLin fiWU[i]!) ∧
      wordLin fiWAlpha * wordLin fiWAlpha = 1 ∧ wordLin fiWBeta * wordLin fiWBeta = 1 ∧
      wordLin fiWAB ^ 3 = 1 ∧ wordLin fiWAB ≠ 1 ∧ wordLin fiWU[3]! ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := fiMiscCheck_ok
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, h6, h7⟩
  · have h := h1 i (List.mem_range.2 hi)
    rwa [wordLin_append, wordLin_append] at h
  · have h := h2 i (List.mem_range.2 hi)
    rwa [wordLin_append, wordLin_append] at h
  · rwa [wordLin_append] at h3
  · rwa [wordLin_append] at h4
  · rw [wordLin_append, wordLin_append] at h5
    rw [← h5]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem fiAlpha_mul_self :
    fiAlpha * fiAlpha = 1 :=
  Subtype.ext fiMiscCheck_parts.2.2.1

theorem fiBeta_mul_self :
    fiBeta * fiBeta = 1 :=
  Subtype.ext fiMiscCheck_parts.2.2.2.1

theorem fiAlpha_mul_fiBeta_pow_three :
    (fiAlpha * fiBeta) ^ 3 = 1 := by
  rw [fiAlpha_mul_fiBeta]
  exact Subtype.ext fiMiscCheck_parts.2.2.2.2.1

theorem fiAlpha_mul_fiBeta_ne_one :
    fiAlpha * fiBeta ≠ 1 := by
  rw [fiAlpha_mul_fiBeta]
  intro h
  exact fiMiscCheck_parts.2.2.2.2.2.1 (fiMkW_eq_one_iff.1 h)

theorem orderOf_fiAlpha_mul_fiBeta :
    orderOf (fiAlpha * fiBeta) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime fiAlpha_mul_fiBeta_pow_three fiAlpha_mul_fiBeta_ne_one

theorem fi_conj_alpha :
    fiMkW fiCAlpha * tGriess * (fiMkW fiCAlpha)⁻¹ = fiAlpha := by
  have h := (fiConjCheck_parts fiConjCheck_ok).1
  have h' : fiMkW fiCAlpha * tGriess = fiAlpha * fiMkW fiCAlpha := by
    rw [← fiMkW_fiRhoT]
    exact Subtype.ext h
  rw [h', mul_inv_cancel_right]

theorem isConj_fiAlpha :
    IsConj tGriess fiAlpha := isConj_iff.2 ⟨_, fi_conj_alpha⟩

theorem isConj_fiBeta :
    IsConj tGriess fiBeta :=
  isConj_fiAlpha.trans
    (fi_isConj_of_dihedral fiAlpha_mul_self fiBeta_mul_self fiAlpha_mul_fiBeta_pow_three)

theorem isConj_fiAlpha_mul_fiBeta :
    IsConj (fiAlpha * fiBeta) threeARep := by
  have h := (fiConjCheck_parts fiConjCheck_ok).2
  have h' : fiMkW fiCThreeA * (fiAlpha * fiBeta) = threeARep * fiMkW fiCThreeA := by
    rw [fiAlpha_mul_fiBeta]
    exact Subtype.ext h
  exact isConj_iff.2 ⟨fiMkW fiCThreeA, by rw [h', mul_inv_cancel_right]⟩

theorem fiRels_lt : ∀ v ∈ rels, ∀ l ∈ v, l.1 < 10 :=
  Certificates.certificate16009.1

theorem fiRels_pos : ∀ v ∈ rels, ∀ l ∈ v, l.2 = true :=
  Certificates.certificate16009.2

theorem fiRelCheck_all :
    ∀ v ∈ rels, wordLin (fiRelW v) = 1 := by
  intro v hv
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
  have hi57 : i < 57 := by rw [← fiRels_length]; exact hi
  have e : rels[i]! = v := by rw [getElem!_pos rels i hi, hiv]
  rw [← e]
  have hcases : i ∈ [0, 7, 9, 17, 21, 26, 41, 47, 48, 52] ∨
      i ∈ [4, 11, 14, 22, 29, 35, 38, 45, 53] ∨
      i ∈ [5, 13, 24, 27, 31, 37, 39, 40, 49] ∨
      i ∈ [1, 3, 16, 20, 28, 32, 46, 51] ∨
      i ∈ [10, 12, 15, 25, 33, 34, 36, 42, 50, 54] ∨
      i ∈ [2, 6, 8, 18, 19, 23, 30, 43, 44] ∨ i = 55 ∨ i = 56 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases hcases with h | h | h | h | h | h | h55 | h56
  · exact fiRelsCheck_ok_0 i h
  · exact fiRelsCheck_ok_1 i h
  · exact fiRelsCheck_ok_2 i h
  · exact fiRelsCheck_ok_3 i h
  · exact fiRelsCheck_ok_4 i h
  · exact fiRelsCheck_ok_5 i h
  · rw [h55]
    exact fiRelFixes_ok_AD.1
  · rw [h56]
    exact fiRelFixes_ok_AD.2

theorem fiE_rel
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = rels) :
    ∀ v ∈ P.relatorLetters, wordProd fiE v = 1 := by
  intro v hv
  rw [hP] at hv
  rw [wordProd_fiE (fiRels_lt v hv) (fiRels_pos v hv), fiMkW_eq_one_iff]
  exact fiRelCheck_all v hv

noncomputable def fiHom
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = rels) :
    P.Group →* MGriess :=
  PresentedGroup.toGroup (CFSG.Sporadic.Bridge.lift_relator P fiE (fiE_rel P hP))

theorem fiHom_of
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = rels)
    (i : Fin P.generatorCount) : fiHom P hP (PresentedGroup.of i) = fiE i :=
  PresentedGroup.toGroup.of ..

theorem fiE_commute_alpha
    {i : ℕ} (hi : i < 10) : fiE i * fiAlpha = fiAlpha * fiE i :=
  Subtype.ext (fiMiscCheck_parts.1 i hi)

theorem fiE_commute_beta
    {i : ℕ} (hi : i < 10) : fiE i * fiBeta = fiBeta * fiE i :=
  Subtype.ext (fiMiscCheck_parts.2.1 i hi)

theorem fiE_mem_cent2
    {i : ℕ} (hi : i < 10) : fiE i ∈ cent2 fiAlpha fiBeta := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact fiE_commute_alpha hi
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact fiE_commute_beta hi

theorem range_fiHom_le
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = rels)
    (hgen : P.generatorCount = 10) : (fiHom P hP).range ≤ cent2 fiAlpha fiBeta := by
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Subgroup.closure
      (Set.range (PresentedGroup.of : Fin P.generatorCount → P.Group)) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hi : (i : ℕ) < 10 := hgen ▸ i.2
    rw [fiHom_of P hP i]
    exact fiE_mem_cent2 hi
  | one => rw [map_one]; exact (cent2 fiAlpha fiBeta).one_mem
  | mul y z _ _ hy hz => rw [map_mul]; exact (cent2 fiAlpha fiBeta).mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact (cent2 fiAlpha fiBeta).inv_mem hy

theorem fiHom_injective
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = rels)
    (hgen : P.generatorCount = 10) [IsSimpleGroup P.Group] : Function.Injective (fiHom P hP) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases Subgroup.Normal.eq_bot_or_eq_top (fiHom P hP).ker with h | h
  · exact h
  · exfalso
    have hmem : PresentedGroup.of (⟨3, by omega⟩ : Fin P.generatorCount) ∈ (fiHom P hP).ker := by
      rw [h]
      exact Subgroup.mem_top _
    have h3 : fiE 3 = 1 := by
      rw [← fiHom_of P hP ⟨3, by omega⟩]
      exact MonoidHom.mem_ker.1 hmem
    exact fiMiscCheck_parts.2.2.2.2.2.2 (fiMkW_eq_one_iff.1 h3)

theorem exists_fi23_two_point :
    ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 3 ∧
      IsConj (α * β) threeARep ∧ IsConj xGriess w ∧ w ∈ cent2 α β ∧
      ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
        Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Fi23) := by
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  have hP : TauCeti.SporadicName.Fi23.presentation = TauCeti.Sporadic.fi23Presentation := rfl
  have hrel : TauCeti.SporadicName.Fi23.presentation.relatorLetters = rels := by
    rw [hP]
    exact CFSG.Sporadic.Bridge.Fi23.relatorLetters_eq
  have hgen : TauCeti.SporadicName.Fi23.presentation.generatorCount = 10 := by
    rw [hP]
    exact CFSG.Sporadic.Bridge.Fi23.generatorCount_eq
  have : IsSimpleGroup TauCeti.SporadicName.Fi23.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 ψ.symm
  exact ⟨fiAlpha, fiBeta, xGriess, isConj_fiAlpha, isConj_fiBeta, orderOf_fiAlpha_mul_fiBeta,
    isConj_fiAlpha_mul_fiBeta, IsConj.refl _, xGriess_mem_cent2, (fiHom _ hrel).range,
    range_fiHom_le _ hrel hgen,
    ⟨(MonoidHom.ofInjective (fiHom_injective _ hrel hgen)).symm.trans ψ.symm⟩⟩

end CFSG.Monster.Existence
