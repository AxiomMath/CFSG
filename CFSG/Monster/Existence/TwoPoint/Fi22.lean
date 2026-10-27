module

public import CFSG.Monster.Existence.TwoPoint.Fi22Iso
public import CFSG.Monster.Existence.InvolutionClasses
public import CFSG.Monster.GMS.S342
public import CFSG.Sporadic.Fi23.Centralizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.GMS
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels imgWords)
open CFSG.Sporadic.Fi23.Native (dLetters)

theorem fi_tGriess_ne_one : tGriess ≠ 1 := by
  intro h
  have := orderOf_tGriess
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

@[expose] noncomputable def fiDelta : MGriess := fiMkW fiWDelta

theorem fiDelta_eq : fiDelta = fiE 0 * fiBeta := fiMkW_append fiWBeta fiWU[0]!

theorem fiE_zero_mul_self :
    fiE 0 * fiE 0 = 1 := by
  have hmem : ([(0, true), (0, true)] : List (ℕ × Bool)) ∈
      TauCeti.Sporadic.fi23Presentation.relatorLetters := by
    rw [fiRelEq]
    exact List.mem_of_getElem? (i := 0) (by decide +kernel)
  have h := fiE_rel _ fiRelEq _ hmem
  simpa [wordProd] using h

theorem isConj_fiE_zero :
    IsConj tGriess (fiE 0) := by
  have h := (fiConj22Check_parts fi22Check_parts.1).1
  have h' : fiMkW fiCGamma * tGriess = fiE 0 * fiMkW fiCGamma := by
    rw [← fiMkW_fiRhoT]
    exact Subtype.ext h
  exact isConj_iff.2 ⟨fiMkW fiCGamma, by rw [h', mul_inv_cancel_right]⟩

theorem isConj_fiDelta :
    IsConj tGriess fiDelta := by
  have h := (fiConj22Check_parts fi22Check_parts.1).2
  have h' : fiMkW fiCDelta * tGriess = fiDelta * fiMkW fiCDelta := by
    rw [← fiMkW_fiRhoT]
    exact Subtype.ext h
  exact isConj_iff.2 ⟨fiMkW fiCDelta, by rw [h', mul_inv_cancel_right]⟩

theorem fiE_zero_ne_one :
    fiE 0 ≠ 1 := by
  intro h
  have := isConj_fiE_zero
  rw [h, isConj_one_left] at this
  exact fi_tGriess_ne_one this

theorem orderOf_fiE_zero :
    orderOf (fiE 0) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact fiE_zero_mul_self) fiE_zero_ne_one

theorem fiE_zero_commute :
    Commute (fiAlpha * fiBeta) (fiE 0) :=
  Commute.mul_left (show Commute (fiE 0) fiAlpha from fiE_commute_alpha (by norm_num)).symm
    (show Commute (fiE 0) fiBeta from fiE_commute_beta (by norm_num)).symm

theorem fiAlpha_mul_fiDelta :
    fiAlpha * fiDelta = (fiAlpha * fiBeta) * fiE 0 := by
  have h2 : fiE 0 * fiBeta = fiBeta * fiE 0 := fiE_commute_beta (by norm_num)
  rw [fiDelta_eq, h2, ← mul_assoc]

theorem orderOf_fiAlpha_mul_fiDelta :
    orderOf (fiAlpha * fiDelta) = 6 := by
  rw [fiAlpha_mul_fiDelta, fiE_zero_commute.orderOf_mul_eq_mul_orderOf_of_coprime
    (by rw [orderOf_fiAlpha_mul_fiBeta, orderOf_fiE_zero]; decide), orderOf_fiAlpha_mul_fiBeta,
    orderOf_fiE_zero]

theorem fiAlpha_mul_fiDelta_pow_three :
    (fiAlpha * fiDelta) ^ 3 = fiE 0 := by
  rw [fiAlpha_mul_fiDelta, fiE_zero_commute.mul_pow, fiAlpha_mul_fiBeta_pow_three, one_mul,
    pow_succ, pow_two, fiE_zero_mul_self, one_mul]

theorem fiDelta_mem_sixANbr :
    fiDelta ∈ sixANbr tGriess fiAlpha :=
  ⟨isConj_fiDelta, orderOf_fiAlpha_mul_fiDelta, by
    rw [fiAlpha_mul_fiDelta_pow_three]; exact isConj_fiE_zero⟩

theorem fi_map_centralizer_singleton {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e g} : Set H) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy

noncomputable def fiCentralizerEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    Subgroup.centralizer ({g} : Set G) ≃* Subgroup.centralizer ({e g} : Set H) :=
  (e.subgroupMap (Subgroup.centralizer ({g} : Set G))).trans
    (MulEquiv.subgroupCongr (fi_map_centralizer_singleton e g))

@[expose] noncomputable def fiGammaK :
    fiK := ⟨fiE 0, fiE_mem_fiK (by norm_num)⟩

@[expose] noncomputable def fiL :
    Subgroup MGriess :=
  fiK ⊓ Subgroup.centralizer ({fiE 0} : Set MGriess)

theorem fiL_le :
    fiL ≤ cent2 fiAlpha fiDelta := by
  intro x hx
  obtain ⟨hxK, hxγ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxα, hxβ⟩ := Subgroup.mem_inf.1 (fiK_le hxK)
  rw [Subgroup.mem_centralizer_singleton_iff] at hxα hxβ hxγ
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxα
  · rw [Subgroup.mem_centralizer_singleton_iff, fiDelta_eq]
    calc x * (fiE 0 * fiBeta) = (x * fiE 0) * fiBeta := by rw [mul_assoc]
      _ = (fiE 0 * x) * fiBeta := by rw [hxγ]
      _ = fiE 0 * (x * fiBeta) := by rw [mul_assoc]
      _ = fiE 0 * (fiBeta * x) := by rw [hxβ]
      _ = fiE 0 * fiBeta * x := by rw [mul_assoc]

theorem fiL_subgroupOf :

    fiL.subgroupOf fiK = Subgroup.centralizer ({fiGammaK} : Set fiK) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  show (x : MGriess) ∈ fiK ⊓ Subgroup.centralizer ({fiE 0} : Set MGriess) ↔ x * fiGammaK =
    fiGammaK * x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨x.2, congrArg Subtype.val h⟩

noncomputable def fiConjEquiv :
    Subgroup.centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J) ≃*
      Subgroup.centralizer ({CFSG.Sporadic.Bridge.Fi23.img 0} : Set CFSG.Sporadic.Fi23.J) :=
  (fiCentralizerEquiv (MulAut.conj fiU) CFSG.Sporadic.Fi23.d).trans
    (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, fiU_conj]))

noncomputable def fiLEquiv :
    fiL ≃* Subgroup.centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J) :=
  ((Subgroup.subgroupOfEquivOfLe (inf_le_left : fiL ≤ fiK)).symm.trans
    ((MulEquiv.subgroupCongr fiL_subgroupOf).trans
      ((@fiCentralizerEquiv fiK CFSG.Sporadic.Fi23.J inferInstance inferInstance fiPhi
        fiGammaK).trans
        (MulEquiv.subgroupCongr (by rw [fiGammaK, fiPhi_fiE (by norm_num)]))))).trans
    fiConjEquiv.symm

theorem card_fiL :
    Nat.card fiL = 129123503308800 := by
  rw [Nat.card_congr fiLEquiv.toEquiv]
  exact CFSG.Sporadic.Fi23.card_centralizer_d

theorem fi_hasTwoShape_of_equiv {G : Type} [Group G] {L : Subgroup G} {C : Type} [Group C]
    (e : L ≃* C) (h2 : Nat.card (Subgroup.center C) = 2)
    (hq : Nonempty (C ⧸ Subgroup.center C ≃* CFSG.Blueprint.NativeSporadic.Fi22)) :
    HasTwoShape L 1 (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Fi22)) := by
  refine ⟨Subgroup.center L, inferInstance, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, h2]
    norm_num
  · obtain ⟨q⟩ := hq
    exact ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans q⟩

theorem hasTwoShape_fiL :
    HasTwoShape fiL 1 (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Fi22)) :=
  @fi_hasTwoShape_of_equiv MGriess _ fiL
    (↥(Subgroup.centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J))) inferInstance
    fiLEquiv CFSG.Sporadic.Fi23.card_center_C
    ⟨CFSG.Sporadic.Fi23.quotCenterEquiv.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm⟩

theorem exists_fi22_two_point :
    ∃ α δ : MGriess, IsConj tGriess α ∧ δ ∈ sixANbr tGriess α ∧
    ∃ L : Subgroup MGriess, L ≤ cent2 α δ ∧ Nat.card L = tableVIIStab TableVIIClass.six_A ∧
      HasTwoShape L 1 (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Fi22)) :=
  ⟨fiAlpha, fiDelta, isConj_fiAlpha, fiDelta_mem_sixANbr, fiL, fiL_le, by
    rw [card_fiL]; norm_num [tableVIIStab], hasTwoShape_fiL⟩

end CFSG.Monster.Existence
