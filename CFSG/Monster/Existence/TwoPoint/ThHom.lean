module

public import CFSG.Monster.Existence.TwoPoint.ThRels0
public import CFSG.Monster.Existence.TwoPoint.ThRels1
public import CFSG.Monster.Existence.TwoPoint.ThRels2
public import CFSG.Monster.Existence.TwoPoint.ThRels3
public import CFSG.Monster.Existence.TwoPoint.ThRels4
public import CFSG.Monster.Existence.TwoPoint.ThRels5
public import CFSG.Monster.Existence.TwoPoint.ThRels6
public import CFSG.Monster.Existence.TwoPoint.ThMisc
public import CFSG.Monster.Existence.TwoPoint.ThCommAlpha
public import CFSG.Monster.Existence.TwoPoint.ThCommBeta
public import CFSG.Monster.Existence.TwoPoint.ThConj
public import CFSG.Monster.Existence.TwoA
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Monster.Existence.Simple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Spin CFSG.Monster.Visible
open CFSG.Sporadic.Bridge (wordProd)

abbrev thP : TauCeti.GroupPresentation := TauCeti.Sporadic.Thompson.presentation

@[expose] noncomputable def thMkW (w : List Native.Gen) : MGriess :=
  ⟨wordLin w, Gmat_le_AutO (wordLin_mem_Gmat w)⟩

theorem thMkW_append (w₁ w₂ : List Native.Gen) : thMkW (w₁ ++ w₂) = thMkW w₂ * thMkW w₁ :=
  Subtype.ext (wordLin_append w₁ w₂)

theorem thMkW_nil : thMkW [] = 1 := Subtype.ext wordLin_nil

theorem thMkW_eq_one_iff {w : List Native.Gen} : thMkW w = 1 ↔ wordLin w = 1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem wordLin_thRhoT : wordLin thRhoT = tStar := by
  have h1 : Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((1 : Fin 24) : ℕ)) = 191 := by decide
  have h2 := Rep4371.pauliQ_minus (i := 0) (j := 1) (by decide)
  rw [h1] at h2
  show wordLin [Native.Gen.rho (false, 0, 191)] = tStar
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho]
  unfold tStar
  rw [rStar_eq_rMinus, ← h2]

theorem thMkW_thRhoT : thMkW thRhoT = tGriess := Subtype.ext wordLin_thRhoT

theorem wordLin_rho_z : wordLin [Native.Gen.rho (true, 0, 0)] = xmat := by
  have h : Rep4371.pauliQ (true, 0, 0) = zQ := by
    unfold Rep4371.pauliQ zQ
    congr 1
    simp [Rep4371.toSC, SpinCoord.z, Rep4371.boolZ, Rep4371.toC_zero, Rep4371.toD_zero]
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho, h, rhoEquiv_zQ, xmat_eq_xB]

theorem thMkW_mem_cent_xGriess {w : List Native.Gen} (hw : w.all thNotTau = true) :
    thMkW w ∈ cent xGriess := by
  have h := wordLin_mem_Gvis w fun g hg => thNotTau_spec (List.all_eq_true.1 hw g hg)
  rw [← map_cent_xGriess] at h
  obtain ⟨u, hu, hu'⟩ := h
  have e : u = thMkW w := Subtype.ext hu'
  rw [← e]
  exact hu

@[expose] noncomputable def thAlpha : MGriess := thMkW thWAlpha

@[expose] noncomputable def thBeta : MGriess := thMkW thWBeta

theorem th_conj_of_conjCheck
    {c w : List Native.Gen} (h : wordLin (thRhoT ++ c) = wordLin (c ++ w)) :
    thMkW c * tGriess * (thMkW c)⁻¹ = thMkW w := by
  have h1 := h
  rw [wordLin_append, wordLin_append] at h1
  rw [mul_inv_eq_iff_eq_mul, ← thMkW_thRhoT]
  exact Subtype.ext h1

theorem thConjOrdCheck_parts :
    wordLin (thRhoT ++ thCAlpha) = wordLin (thCAlpha ++ thWAlpha) ∧
      wordLin (thRhoT ++ thCBeta) = wordLin (thCBeta ++ thWBeta) :=
  thConjOrdCheck_ok

theorem thMiscCheck_parts :
    (∀ i, i < 8 → wordLin thWV[i]! * wordLin thWU[i]! = 1) ∧ wordLin thWAB ^ 3 = 1 ∧
      wordLin thWAB ≠ 1 ∧ wordLin thWU[5]! ^ 7 = 1 ∧ wordLin thWU[5]! ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := thMiscCheck_ok
  refine ⟨fun i hi => ?_, ?_, h3, ?_, h5⟩
  · have h := h1 i (List.mem_range.2 hi)
    rwa [wordLin_append] at h
  · rw [← h2]
    simp only [thWAB3, wordLin_append]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  · rw [← h4]
    simp only [thWS7, wordLin_append]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem isConj_thAlpha :
    IsConj tGriess thAlpha :=
  isConj_iff.2 ⟨thMkW thCAlpha, th_conj_of_conjCheck thConjOrdCheck_parts.1⟩

theorem isConj_thBeta :
    IsConj tGriess thBeta :=
  isConj_iff.2 ⟨thMkW thCBeta, th_conj_of_conjCheck thConjOrdCheck_parts.2⟩

theorem thMkW_thWAB : thMkW thWAB = thAlpha * thBeta := (thMkW_append thWBeta thWAlpha)

theorem orderOf_thAlpha_mul_thBeta :
    orderOf (thAlpha * thBeta) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [← thMkW_thWAB]
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    exact thMiscCheck_parts.2.1
  · intro h
    exact thMiscCheck_parts.2.2.1 (thMkW_eq_one_iff.1 h)

theorem isConj_thAlpha_mul_thBeta_threeCRep :
    IsConj (thAlpha * thBeta) threeCRep := by
  have h := thThreeCCheck_ok
  rw [wordLin_append, wordLin_append] at h
  have h' : thMkW thWG * threeCRep = thAlpha * thBeta * thMkW thWG := by
    rw [← thMkW_thWAB]
    exact Subtype.ext h
  refine isConj_iff.2 ⟨(thMkW thWG)⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, ← h', inv_mul_cancel_left]

@[expose] noncomputable def thE (i : ℕ) : MGriess := thMkW thWU[i]!

theorem thE_inv
    {i : ℕ} (hi : i < 8) : (thE i)⁻¹ = thMkW thWV[i]! := by
  have h := thMiscCheck_parts.1 i hi
  have h' : thMkW thWV[i]! * thE i = 1 := Subtype.ext h
  exact (eq_inv_of_mul_eq_one_left h').symm

theorem thMkW_letterW
    {l : ℕ × Bool} (hl : l.1 < 8) :
    thMkW (thLetterW l) = if l.2 then thE l.1 else (thE l.1)⁻¹ := by
  unfold thLetterW
  cases h : l.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [thE_inv hl]
  · simp only [↓reduceIte]
    rfl

theorem wordProd_thE
    {R : List (ℕ × Bool)} (hR : ∀ l ∈ R, l.1 < 8) :
    wordProd thE R = thMkW (thRelW R) := by
  induction R with
  | nil => simp [wordProd, thRelW, thMkW_nil]
  | cons l R ih =>
    have hl : l.1 < 8 := hR l List.mem_cons_self
    have hR' : ∀ l' ∈ R, l'.1 < 8 := fun l' hl' => hR l' (List.mem_cons_of_mem _ hl')
    have e : thRelW (l :: R) = thRelW R ++ thLetterW l := by
      simp [thRelW]
    rw [e, thMkW_append, thMkW_letterW hl, ← ih hR']
    simp only [wordProd, List.map_cons, List.prod_cons]

theorem thRels_length : thP.relatorLetters.length = 39 := by
  have h := TauCeti.GroupPresentation.map_length_relatorLetters thP
  rw [TauCeti.Sporadic.Thompson.map_length_relators_presentation] at h
  simpa using congrArg List.length h

theorem thP_generatorCount : thP.generatorCount = 8 := rfl

theorem thRelCheck_all :
    ∀ v ∈ thP.relatorLetters, wordLin (thRelW v) = 1 := by
  intro v hv
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
  have hi39 : i < 39 := by rw [← thRels_length]; exact hi
  have e : thP.relatorLetters[i]! = v := by rw [getElem!_pos thP.relatorLetters i hi, hiv]
  rw [← e]
  have hcases : i ∈ [13] ∨ i ∈ [0, 2, 33, 35] ∨ i ∈ [7, 14, 38] ∨ i ∈ [5, 32, 37] ∨
      i ∈ [3, 8, 9, 16, 19, 22] ∨ i ∈ [1, 10, 12, 18, 24, 25, 26, 28, 30, 31, 34, 36] ∨
      i ∈ [4, 6, 11, 15, 17, 20, 21, 23, 27, 29] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases hcases with h | h | h | h | h | h | h
  · exact thRelsCheck_ok_0 i h
  · exact thRelsCheck_ok_1 i h
  · exact thRelsCheck_ok_2 i h
  · exact thRelsCheck_ok_3 i h
  · exact thRelsCheck_ok_4 i h
  · exact thRelsCheck_ok_5 i h
  · exact thRelsCheck_ok_6 i h

theorem thRels_lt :
    ∀ v ∈ thP.relatorLetters, ∀ l ∈ v, l.1 < 8 := by
  intro v hv l hl
  rw [TauCeti.GroupPresentation.relatorLetters_def] at hv
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hv
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
  exact x.1.2

theorem thE_rel :
    ∀ v ∈ thP.relatorLetters, wordProd thE v = 1 := by
  intro v hv
  rw [wordProd_thE (thRels_lt v hv), thMkW_eq_one_iff]
  exact thRelCheck_all v hv

noncomputable def thHom :
    thP.Group →* MGriess :=
  PresentedGroup.toGroup (CFSG.Sporadic.Bridge.lift_relator thP thE thE_rel)

theorem thHom_of
    (i : Fin thP.generatorCount) : thHom (PresentedGroup.of i) = thE i :=
  PresentedGroup.toGroup.of ..

theorem thE_commute_alpha
    {i : ℕ} (hi : i < 8) : thE i * thAlpha = thAlpha * thE i := by
  have h := thCommAlphaCheck_ok i (List.mem_range.2 hi)
  rw [wordLin_append, wordLin_append] at h
  exact Subtype.ext h

theorem thE_commute_beta
    {i : ℕ} (hi : i < 8) : thE i * thBeta = thBeta * thE i := by
  have h := thCommBetaCheck_ok i (List.mem_range.2 hi)
  rw [wordLin_append, wordLin_append] at h
  exact Subtype.ext h

theorem thE_mem_cent2
    {i : ℕ} (hi : i < 8) : thE i ∈ cent2 thAlpha thBeta := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact thE_commute_alpha hi
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact thE_commute_beta hi

theorem range_thHom_le :
    thHom.range ≤ cent2 thAlpha thBeta := by
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Subgroup.closure
      (Set.range (PresentedGroup.of : Fin thP.generatorCount → thP.Group)) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hi : (i : ℕ) < 8 := by
      have h1 : (i : ℕ) < thP.generatorCount := i.2
      have h2 := thP_generatorCount
      omega
    rw [thHom_of i]
    exact thE_mem_cent2 hi
  | one => rw [map_one]; exact (cent2 thAlpha thBeta).one_mem
  | mul y z _ _ hy hz => rw [map_mul]; exact (cent2 thAlpha thBeta).mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact (cent2 thAlpha thBeta).inv_mem hy

theorem thE_zero : thE 0 = xGriess := by
  refine Subtype.ext ?_
  show wordLin thWU[0]! = xmat
  exact wordLin_rho_z

theorem thHom_injective
    [IsSimpleGroup thP.Group] : Function.Injective thHom := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases Subgroup.Normal.eq_bot_or_eq_top thHom.ker with h | h
  · exact h
  · exfalso
    have hmem : PresentedGroup.of (⟨0, by rw [thP_generatorCount]; omega⟩ :
        Fin thP.generatorCount) ∈ thHom.ker := by
      rw [h]
      exact Subgroup.mem_top _
    have h0 : thE 0 = 1 := by
      rw [← thHom_of ⟨0, by rw [thP_generatorCount]; omega⟩]
      exact MonoidHom.mem_ker.1 hmem
    rw [thE_zero] at h0
    have h2 := orderOf_xGriess
    rw [h0, orderOf_one] at h2
    exact absurd h2 (by norm_num)

theorem orderOf_thE_five :
    orderOf (thE 5) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · exact Subtype.ext thMiscCheck_parts.2.2.2.1
  · intro h
    exact thMiscCheck_parts.2.2.2.2 (thMkW_eq_one_iff.1 h)

theorem notTau_words : thWAlpha.all thNotTau = true ∧ thWBeta.all thNotTau = true ∧
    thWU[5]!.all thNotTau = true := by
  decide

theorem exists_th_two_point_of_equiv
    (ψ : CFSG.Blueprint.NativeSporadic.Th ≃* thP.Group)
    (hs : IsSimpleGroup thP.Group) :
    ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 3 ∧
      IsConj (α * β) threeCRep ∧ IsConj xGriess w ∧ w ∈ cent2 α β ∧
      (∃ e : MGriess, orderOf e = 7 ∧ e ∈ cent2 α β ⊓ cent w) ∧
      ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
        Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Th) := by
  haveI := hs
  have hinj := thHom_injective
  have hw : xGriess ∈ cent2 thAlpha thBeta := by
    obtain ⟨hA, hB, -⟩ := notTau_words
    have h1 := thMkW_mem_cent_xGriess hA
    have h2 := thMkW_mem_cent_xGriess hB
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
      exact h1.symm
    · rw [Subgroup.mem_centralizer_singleton_iff] at h2 ⊢
      exact h2.symm
  refine ⟨thAlpha, thBeta, xGriess, isConj_thAlpha, isConj_thBeta, orderOf_thAlpha_mul_thBeta,
    isConj_thAlpha_mul_thBeta_threeCRep, IsConj.refl _, hw, ⟨thE 5, orderOf_thE_five,
    thE_mem_cent2 (by norm_num), ?_⟩, thHom.range, range_thHom_le,
    ⟨(MonoidHom.ofInjective hinj).symm.trans ψ.symm⟩⟩
  obtain ⟨-, -, hS⟩ := notTau_words
  exact thMkW_mem_cent_xGriess hS

end CFSG.Monster.Existence
