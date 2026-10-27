module

public import CFSG.Monster.Existence.TwoPoint.HNRels0
public import CFSG.Monster.Existence.TwoPoint.HNRels1
public import CFSG.Monster.Existence.TwoPoint.HNRels2
public import CFSG.Monster.Existence.TwoPoint.HNRels3
public import CFSG.Monster.Existence.TwoPoint.HNMisc
public import CFSG.Monster.Existence.TwoPoint.HNConj
public import CFSG.Monster.Existence.TwoA
public import CFSG.Sporadic.Bridge.HNSurj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

@[expose] noncomputable def hnMkW (w : List Native.Gen) : MGriess :=
  ⟨wordLin w, Gmat_le_AutO (wordLin_mem_Gmat w)⟩

theorem hnMkW_append (w₁ w₂ : List Native.Gen) : hnMkW (w₁ ++ w₂) = hnMkW w₂ * hnMkW w₁ :=
  Subtype.ext (wordLin_append w₁ w₂)

theorem hnMkW_nil : hnMkW [] = 1 := Subtype.ext wordLin_nil

theorem hnMkW_eq_one_iff {w : List Native.Gen} : hnMkW w = 1 ↔ wordLin w = 1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem wordLin_hnRhoT : wordLin hnRhoT = tStar := by
  have h1 : Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((1 : Fin 24) : ℕ)) = 191 := by decide
  have h2 := Rep4371.pauliQ_minus (i := 0) (j := 1) (by decide)
  rw [h1] at h2
  show wordLin [Native.Gen.rho (false, 0, 191)] = tStar
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho]
  unfold tStar
  rw [rStar_eq_rMinus, ← h2]

theorem hnMkW_hnRhoT : hnMkW hnRhoT = tGriess := Subtype.ext wordLin_hnRhoT

theorem hn_commute_of_fix_conj {c e α : MGriess} (hα : c * tGriess * c⁻¹ = α)
    (h : (e : SpaceB ≃ₗ[ℚ] SpaceB) ((c : SpaceB ≃ₗ[ℚ] SpaceB) aStar) =
      (c : SpaceB ≃ₗ[ℚ] SpaceB) aStar) : e * α = α * e := by
  have hc : (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ AutO := c.2
  have hαv : (α : SpaceB ≃ₗ[ℚ] SpaceB) =
      (c : SpaceB ≃ₗ[ℚ] SpaceB) * tStar * (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by
    rw [← hα]
    rfl
  have ht : ((α : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      tAxis ((c : SpaceB ≃ₗ[ℚ] SpaceB) aStar) := by
    rw [tAxis_apply_aStar hc, hαv]
    rfl
  exact Subtype.ext (commute_of_fix_of_eq_tAxis e.2 ht h)

theorem hn_conj_of_conjCheck
    {c w : List Native.Gen} (h : wordLin (hnRhoT ++ c) = wordLin (c ++ w)) :
    hnMkW c * tGriess * (hnMkW c)⁻¹ = hnMkW w := by
  have h1 := h
  rw [wordLin_append, wordLin_append] at h1
  rw [mul_inv_eq_iff_eq_mul, ← hnMkW_hnRhoT]
  exact Subtype.ext h1

theorem hnMiscCheck_parts :
    (∀ i, i < 5 → wordLin hnWV[i]! * wordLin hnWU[i]! = 1) ∧
      (∀ i, i < 5 → wordLin hnWU[i]! * wordLin hnWAlpha = wordLin hnWAlpha * wordLin hnWU[i]!) ∧
      (∀ i, i < 5 → wordLin hnWU[i]! * wordLin hnWBeta = wordLin hnWBeta * wordLin hnWU[i]!) ∧
      wordLin hnWAB ≠ 1 ∧ wordLin hnWU[4]! ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hnMiscCheck_ok
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, h4, h5⟩
  · have h := h1 i (List.mem_range.2 hi)
    rwa [wordLin_append] at h
  · have h := h2 i (List.mem_range.2 hi)
    rwa [wordLin_append, wordLin_append] at h
  · have h := h3 i (List.mem_range.2 hi)
    rwa [wordLin_append, wordLin_append] at h

theorem hnConjOrdCheck_parts :
    wordLin (hnRhoT ++ hnCAlpha) = wordLin (hnCAlpha ++ hnWAlpha) ∧
      wordLin (hnRhoT ++ hnCBeta) = wordLin (hnCBeta ++ hnWBeta) ∧ wordLin hnWAB ^ 5 = 1 := by
  obtain ⟨h1, h2, h3⟩ := hnConjOrdCheck_ok
  refine ⟨h1, h2, ?_⟩
  rw [← h3]
  simp only [hnWAB5, wordLin_append]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

@[expose] noncomputable def hnAlpha : MGriess := hnMkW hnWAlpha

@[expose] noncomputable def hnBeta : MGriess := hnMkW hnWBeta

theorem isConj_alpha :
    IsConj tGriess hnAlpha :=
  isConj_iff.2 ⟨hnMkW hnCAlpha, hn_conj_of_conjCheck hnConjOrdCheck_parts.1⟩

theorem isConj_beta :
    IsConj tGriess hnBeta :=
  isConj_iff.2 ⟨hnMkW hnCBeta, hn_conj_of_conjCheck hnConjOrdCheck_parts.2.1⟩

theorem orderOf_alpha_mul_beta :
    orderOf (hnAlpha * hnBeta) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have e : hnAlpha * hnBeta = hnMkW hnWAB := (hnMkW_append hnWBeta hnWAlpha).symm
  rw [e]
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    exact hnConjOrdCheck_parts.2.2
  · intro h
    exact hnMiscCheck_parts.2.2.2.1 (hnMkW_eq_one_iff.1 h)

@[expose] noncomputable def hnE (i : ℕ) : MGriess := hnMkW hnWU[i]!

theorem hnE_inv
    {i : ℕ} (hi : i < 5) : (hnE i)⁻¹ = hnMkW hnWV[i]! := by
  have h := hnMiscCheck_parts.1 i hi
  have h' : hnMkW hnWV[i]! * hnE i = 1 := Subtype.ext h
  exact (eq_inv_of_mul_eq_one_left h').symm

theorem hnMkW_letterW
    {l : ℕ × Bool} (hl : l.1 < 5) :
    hnMkW (hnLetterW l) = if l.2 then hnE l.1 else (hnE l.1)⁻¹ := by
  unfold hnLetterW
  cases h : l.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hnE_inv hl]
  · simp only [↓reduceIte]
    rfl

theorem wordProd_hnE
    {R : List (ℕ × Bool)} (hR : ∀ l ∈ R, l.1 < 5) :
    wordProd hnE R = hnMkW (hnRelW R) := by
  induction R with
  | nil => simp [wordProd, hnRelW, hnMkW_nil]
  | cons l R ih =>
    have hl : l.1 < 5 := hR l List.mem_cons_self
    have hR' : ∀ l' ∈ R, l'.1 < 5 := fun l' hl' => hR l' (List.mem_cons_of_mem _ hl')
    have e : hnRelW (l :: R) = hnRelW R ++ hnLetterW l := by
      simp [hnRelW]
    rw [e, hnMkW_append, hnMkW_letterW hl, ← ih hR']
    simp only [wordProd, List.map_cons, List.prod_cons]

theorem hnRels_lt : ∀ v ∈ hnRels, ∀ l ∈ v, l.1 < 5 := by decide

theorem hnRels_length : hnRels.length = 19 := rfl

theorem hnRelCheck_all :
    ∀ v ∈ hnRels, wordLin (hnRelW v) = 1 := by
  intro v hv
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
  have hi19 : i < 19 := by rw [← hnRels_length]; exact hi
  have e : hnRels[i]! = v := by rw [getElem!_pos hnRels i hi, hiv]
  rw [← e]
  have hcases : i ∈ [4, 5, 6, 7, 10, 11, 12] ∨ i ∈ [0, 1, 2, 3, 8, 9] ∨ i ∈ [13, 14, 15] ∨
      i ∈ [16, 17, 18] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases hcases with h | h | h | h
  · exact hnRelsCheck_ok_0 i h
  · exact hnRelsCheck_ok_1 i h
  · exact hnRelsCheck_ok_2 i h
  · exact hnRelsCheck_ok_3 i h

theorem hnE_rel
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = hnRels) :
    ∀ v ∈ P.relatorLetters, wordProd hnE v = 1 := by
  intro v hv
  rw [hP] at hv
  rw [wordProd_hnE (hnRels_lt v hv), hnMkW_eq_one_iff]
  exact hnRelCheck_all v hv

noncomputable def hnHom
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = hnRels) :
    P.Group →* MGriess :=
  PresentedGroup.toGroup (CFSG.Sporadic.Bridge.lift_relator P hnE (hnE_rel P hP))

theorem hnHom_of
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = hnRels)
    (i : Fin P.generatorCount) : hnHom P hP (PresentedGroup.of i) = hnE i :=
  PresentedGroup.toGroup.of ..

theorem hnE_commute_alpha
    {i : ℕ} (hi : i < 5) : hnE i * hnAlpha = hnAlpha * hnE i :=
  Subtype.ext (hnMiscCheck_parts.2.1 i hi)

theorem hnE_commute_beta
    {i : ℕ} (hi : i < 5) : hnE i * hnBeta = hnBeta * hnE i :=
  Subtype.ext (hnMiscCheck_parts.2.2.1 i hi)

theorem hnE_mem_cent2
    {i : ℕ} (hi : i < 5) : hnE i ∈ cent2 hnAlpha hnBeta := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hnE_commute_alpha hi
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hnE_commute_beta hi

theorem range_hnHom_le
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = hnRels)
    (hgen : P.generatorCount = 5) : (hnHom P hP).range ≤ cent2 hnAlpha hnBeta := by
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Subgroup.closure
      (Set.range (PresentedGroup.of : Fin P.generatorCount → P.Group)) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hi : (i : ℕ) < 5 := hgen ▸ i.2
    rw [hnHom_of P hP i]
    exact hnE_mem_cent2 hi
  | one => rw [map_one]; exact (cent2 hnAlpha hnBeta).one_mem
  | mul y z _ _ hy hz => rw [map_mul]; exact (cent2 hnAlpha hnBeta).mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact (cent2 hnAlpha hnBeta).inv_mem hy

theorem hnHom_injective
    (P : TauCeti.GroupPresentation) (hP : P.relatorLetters = hnRels)
    (hgen : P.generatorCount = 5) [IsSimpleGroup P.Group] : Function.Injective (hnHom P hP) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases Subgroup.Normal.eq_bot_or_eq_top (hnHom P hP).ker with h | h
  · exact h
  · exfalso
    have hmem : PresentedGroup.of (⟨4, by omega⟩ : Fin P.generatorCount) ∈ (hnHom P hP).ker := by
      rw [h]
      exact Subgroup.mem_top _
    have h4 : hnE 4 = 1 := by
      rw [← hnHom_of P hP ⟨4, by omega⟩]
      exact MonoidHom.mem_ker.1 hmem
    exact hnMiscCheck_parts.2.2.2.2 (hnMkW_eq_one_iff.1 h4)

theorem exists_hn_two_point :
    ∃ α β : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧
    orderOf (α * β) = 5 ∧ ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
      Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.HN) := by
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have hP : TauCeti.SporadicName.HN.presentation = TauCeti.Sporadic.hnPresentation := rfl
  have hrel : TauCeti.SporadicName.HN.presentation.relatorLetters = hnRels := by
    rw [hP]
    exact CFSG.Sporadic.Bridge.HN.relatorLetters_eq
  have hgen : TauCeti.SporadicName.HN.presentation.generatorCount = 5 := by
    rw [hP]
    simp [TauCeti.GroupPresentation.generatorCount]
  have : IsSimpleGroup TauCeti.SporadicName.HN.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HN.isSimpleGroup_HN ψ.symm
  exact ⟨hnAlpha, hnBeta, isConj_alpha, isConj_beta, orderOf_alpha_mul_beta,
    (hnHom _ hrel).range, range_hnHom_le _ hrel hgen,
    ⟨(MonoidHom.ofInjective (hnHom_injective _ hrel hgen)).symm.trans ψ.symm⟩⟩

end CFSG.Monster.Existence
