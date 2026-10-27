module

public import CFSG.Sporadic.Recognition.RuMultiplierTables
public import CFSG.Sporadic.Recognition.CoverTransfer
public import CFSG.LieType.Multipliers.Tits
public import CFSG.Certificates.Kernel.CosetJ.GenSub
public import CFSG.Sporadic.Recognition.RuMultiplierIndex
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis

public section

namespace CFSG.Sporadic.Recognition.RuMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact CFSG.Open
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.VecSurj
  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.LieType.Multipliers.Tits Subgroup

theorem card_PG_W0_le :
    Finite (PG gc W0) ∧ Nat.card (PG gc W0) ≤ 145926144000 := by
  have h : Finite TauCeti.SporadicName.Ru.presentation.Group ∧
      Nat.card TauCeti.SporadicName.Ru.presentation.Group ≤ 145926144000 :=
    CFSG.Sporadic.Presentation.Ru.finite_card_le
  rw [TauCeti.GroupPresentation.Group, CFSG.Sporadic.Presentation.relatorSet_eq] at h
  exact h

theorem lift_ruGen_W0 :
    ∀ r ∈ wordSet W0, FreeGroup.lift ruGen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [show ruGen = fun i : Fin gc => img ruSpec (seedG ruVec) i.val from rfl,
    lift_mk_eq_wordProd]
  refine CFSG.Sporadic.Bridge.Ru.bridge_facts.1 _ ?_
  rw [TauCeti.GroupPresentation.relatorLetters_def]
  exact List.mem_map_of_mem hw

theorem closure_ruGen :
    Subgroup.closure (Set.range ruGen) = ⊤ := by
  have hmem : ∀ w : List (Fin gc × Bool),
      FreeGroup.lift ruGen (FreeGroup.mk w) ∈ Subgroup.closure (Set.range ruGen) := fun w =>
    lift_mk_mem fun l _ => Subgroup.subset_closure (Set.mem_range_self l.1)
  rw [eq_top_iff, ← closure_ab ruVec, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [← lift_ruGen_surjA]; exact hmem _
  · rw [← lift_ruGen_surjB]; exact hmem _

theorem isPresentation_ruGen :
    IsPresentation ruGen (wordSet W0) := by
  obtain ⟨hfin, hle⟩ := card_PG_W0_le
  have : Finite (PresentedGroup (wordSet W0)) := hfin
  exact IsPresentation.of_card_le lift_ruGen_W0 closure_ruGen
    (by rw [CFSG.Sporadic.Bridge.Ru.card_J]; exact hle)

@[expose] def ruCommW (i : Fin gc) : FreeGroup (Fin gc) := FreeGroup.mk (ruCommWord i)

theorem ruCommW_mem_commutator (i : Fin gc) : ruCommW i ∈ commutator (FreeGroup (Fin gc)) :=
  mk_commWords_mem_commutator _

abbrev RuCover : Type := PresentedCover (wordSet W0) ruCommW

theorem coverRelators_ruCommW : coverRelators (wordSet W0) ruCommW = wordSet ruCover :=
  coverRelators_wordSet W0 ruCommWord

@[expose] def ruU : Fin gc := ⟨0, by decide⟩

@[expose] def ruT : Fin gc := ⟨2, by decide⟩

abbrev ruK : Subgroup RuCover :=
  Subgroup.closure {PresentedGroup.of ruU, PresentedGroup.of ruT}

theorem index_ruK_le (hL0 : RuIndexK) :
    ruK.FiniteIndex ∧ ruK.index ≤ 16240 := by
  have key : ∀ rels : Set (FreeGroup (Fin gc)), rels = wordSet ruCover →
      (Subgroup.closure {PresentedGroup.of ruU, PresentedGroup.of ruT} :
        Subgroup (PresentedGroup rels)).FiniteIndex ∧
      (Subgroup.closure {PresentedGroup.of ruU, PresentedGroup.of ruT} :
        Subgroup (PresentedGroup rels)).index ≤ 16240 := by
    rintro rels rfl
    refine index_le_of_genSub hL0 _ fun i hi => ?_
    have hS : subsetOf gc [0, 2] = [ruU, ruT] := by decide
    rw [hS, List.mem_pair] at hi
    rcases hi with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact key _ coverRelators_ruCommW

section Tits

theorem lift_ruCommW
    (hTab : RuTabFact) (i : Fin gc) : FreeGroup.lift ruGen (ruCommW i) = ruGen i :=
  lift_ruCommWord hTab i

noncomputable abbrev ruπ
    (hTab : RuTabFact) : RuCover →* J ruVec :=
  coverMap isPresentation_ruGen (lift_ruCommW hTab)

theorem ruπ_mk
    (hTab : RuTabFact) (x : FreeGroup (Fin gc)) :
    ruπ hTab (PresentedGroup.mk _ x) = FreeGroup.lift ruGen x :=
  coverMap_mk _ _ x

theorem ruπ_of
    (hTab : RuTabFact) (i : Fin gc) :
    ruπ hTab (PresentedGroup.of i) = ruGen i :=
  coverMap_of _ _ i

theorem ruπ_ker_le_center
    (hTab : RuTabFact) :
    (ruπ hTab).ker ≤ center RuCover :=
  coverMap_ker_le_center _ _

@[expose] noncomputable def ruAbcP (k : Fin 3) : RuCover :=
  PresentedGroup.mk _ (FreeGroup.mk (ruAbc.getD k []))

@[expose] noncomputable def ruTitsGen (k : Fin 3) : RuCover := FreeGroup.lift ruAbcP (titsW k)

abbrev ruTits : Subgroup RuCover := Subgroup.closure (Set.range ruTitsGen)

theorem ruπ_ruAbcP
    (hTab : RuTabFact) :
    ruπ hTab ∘ ruAbcP = ruAbcJ :=
  funext fun _ => ruπ_mk hTab _

theorem ruπ_comp_lift_ruAbcP
    (hTab : RuTabFact) :
    (ruπ hTab).comp (FreeGroup.lift ruAbcP) = FreeGroup.lift ruAbcJ :=
  FreeGroup.ext_hom _ _ fun j => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    exact congrFun (ruπ_ruAbcP hTab) j

theorem lift_ruAbcJ_titsW
    (hTab : RuTabFact) (k : Fin 3) : FreeGroup.lift ruAbcJ (titsW k) = ruAbcJ k := by
  have h1 := lift_ruAbcJ_titsOneWords hTab (r := [(k, false)] ++ titsCommWord k)
    (List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩))
  rw [← FreeGroup.mul_mk, map_mul, show FreeGroup.mk [(k, false)] = (FreeGroup.of k)⁻¹ from rfl,
    map_inv, FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem ruTits_coverRelators
    (hTab : RuTabFact) :
    ∀ r ∈ coverRelators titsRelSet titsW, FreeGroup.lift ruTitsGen r = 1 := by
  refine coverRelators_lift_comm (ruπ hTab) (ruπ_ker_le_center hTab) titsW_mem_commutator
    (fun r hr => ?_) (fun k => ?_)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [ruπ_ruAbcP]
    exact lift_ruAbcJ_titsOneWords hTab (List.mem_append_left _ hw)
  · rw [ruπ_ruAbcP, lift_ruAbcJ_titsW hTab]
    exact (congrFun (ruπ_ruAbcP hTab) k).symm

theorem ruπ_ruTitsGen
    (hTab : RuTabFact) (k : Fin 3) :
    ruπ hTab (ruTitsGen k) = ruAbcJ k := by
  rw [ruTitsGen, ← MonoidHom.comp_apply, ruπ_comp_lift_ruAbcP, lift_ruAbcJ_titsW hTab]

theorem ruπ_comp_lift_ruTitsGen
    (hTab : RuTabFact) :
    (ruπ hTab).comp (FreeGroup.lift ruTitsGen) = FreeGroup.lift ruAbcJ :=
  FreeGroup.ext_hom _ _ fun j => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    exact ruπ_ruTitsGen hTab j

theorem finite_ruTits
    (hTab : RuTabFact) :
    Finite ruTits := by
  have : Finite (PresentedCover titsRelSet titsW) := card_presentedCover_le.1
  have hrange : (PresentedGroup.toGroup (ruTits_coverRelators hTab)).range = ruTits := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext k
    exact PresentedGroup.toGroup.of _
  rw [← hrange]
  exact Finite.of_surjective _
    (PresentedGroup.toGroup (ruTits_coverRelators hTab)).rangeRestrict_surjective

theorem card_ruTits_le
    (hTab : RuTabFact) :
    Nat.card ruTits ≤ 17971200 := by
  have : Finite (PresentedCover titsRelSet titsW) := card_presentedCover_le.1
  exact (card_closure_range_le (ruTits_coverRelators hTab)).trans card_presentedCover_le.2

theorem of_mem_ruTits
    (hTab : RuTabFact) {i : Fin gc}
    (hi : ∀ l ∈ ruCommWord i, l.1 = ruU ∨ l.1 = ruT) :
    (PresentedGroup.of i : RuCover) ∈ ruTits := by
  let U' : RuCover := FreeGroup.lift ruTitsGen (FreeGroup.mk ruUInAbc)
  let T' : RuCover := FreeGroup.lift ruTitsGen (FreeGroup.mk ruTInAbc)
  let f' : Fin gc → RuCover := fun j =>
    if j = ruU then U' else if j = ruT then T' else PresentedGroup.of j
  have htu : ruT ≠ ruU := by decide
  have hfu : f' ruU = U' := by simp [f']
  have hft : f' ruT = T' := by simp [f', htu]
  have hTmem : ∀ w : List (Fin 3 × Bool), FreeGroup.lift ruTitsGen (FreeGroup.mk w) ∈ ruTits :=
    fun w => lift_mk_mem fun l _ => Subgroup.subset_closure (Set.mem_range_self l.1)
  have hπT : ∀ w : List (Fin 3 × Bool), ruπ hTab (FreeGroup.lift ruTitsGen (FreeGroup.mk w)) =
      FreeGroup.lift ruAbcJ (FreeGroup.mk w) := fun w => by
    rw [← MonoidHom.comp_apply, ruπ_comp_lift_ruTitsGen]
  have hU : ruπ hTab U' = ruGen ruU := (hπT _).trans (lift_ruAbcJ_U hTab)
  have hT : ruπ hTab T' = ruGen ruT := (hπT _).trans (lift_ruAbcJ_T hTab)
  have hc : ∀ j, (PresentedGroup.of j : RuCover)⁻¹ * f' j ∈ center RuCover := fun j => by
    by_cases hu : j = ruU
    · subst hu
      refine ruπ_ker_le_center hTab ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfu, hU, ruπ_of, inv_mul_cancel]
    by_cases ht : j = ruT
    · subst ht
      refine ruπ_ker_le_center hTab ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hft, hT, ruπ_of, inv_mul_cancel]
    · have hfj : f' j = PresentedGroup.of j := by
        simp only [f']
        rw [ite_eq_right hu, ite_eq_right ht]
      rw [hfj, inv_mul_cancel]
      exact one_mem _
  have hx : (PresentedGroup.of i : RuCover) = FreeGroup.lift PresentedGroup.of (ruCommW i) := by
    rw [← mk_eq_lift_of]
    exact PresentedGroup.mk_eq_mk_of_inv_mul_mem (inv_of_mul_mem_coverRelators _ ruCommW i)
  rw [hx, ← lift_eq_lift_of_mem_commutator hc (ruCommW_mem_commutator i)]
  refine lift_mk_mem fun l hl => ?_
  rcases hi l hl with h | h
  · rw [h, hfu]; exact hTmem _
  · rw [h, hft]; exact hTmem _

theorem ruK_le_ruTits
    (hTab : RuTabFact) : ruK ≤ ruTits := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact of_mem_ruTits hTab (by decide)
  · exact of_mem_ruTits hTab (by decide)

theorem card_ruCover_le
    (hTab : RuTabFact)
    (hL0 : RuIndexK) :
    Finite RuCover ∧ Nat.card RuCover ≤ 291852288000 := by
  obtain ⟨hfi, hidx⟩ := index_ruK_le hL0
  have := finite_ruTits hTab
  have hcard : Nat.card ruK ≤ 17971200 :=
    (Subgroup.card_le_of_le (ruK_le_ruTits hTab)).trans (card_ruTits_le hTab)
  have : Finite ruK := Finite.of_injective _ (Subgroup.inclusion_injective (ruK_le_ruTits hTab))
  have : Finite (RuCover ⧸ ruK) := Subgroup.finite_quotient_of_finiteIndex
  have hfin : Finite RuCover := Finite.of_subgroup_quotient ruK
  refine ⟨hfin, ?_⟩
  rw [← ruK.index_mul_card]
  calc ruK.index * Nat.card ruK ≤ 16240 * 17971200 := Nat.mul_le_mul hidx hcard
    _ = 291852288000 := by norm_num

theorem card_griessHopfMultiplier_J_le
    (hTab : RuTabFact)
    (hL0 : RuIndexK) :
    0 < Nat.card (griessHopfMultiplier (J ruVec)) ∧
      Nat.card (griessHopfMultiplier (J ruVec)) ≤ 2 := by
  obtain ⟨hfin, hle⟩ := card_ruCover_le hTab hL0
  have hc := card_presentedCover isPresentation_ruGen ruCommW_mem_commutator (lift_ruCommW hTab)
  rw [CFSG.Sporadic.Bridge.Ru.card_J] at hc
  have hpos : 0 < Nat.card RuCover := Nat.card_pos
  rw [hc] at hle hpos
  exact ⟨Nat.pos_of_mul_pos_left hpos, by omega⟩

end Tits

section Rho

@[expose] noncomputable def ruRhoGen (i : ℕ) : Equiv.Perm (Fin 16240) :=
  permOfArr 16240 ruRhoArrs[i]!

theorem rho_facts (h : ruRhoCheck = true) :
    allPermsOK 16240 ruRhoArrs = true ∧
      (∀ w ∈ ruCover, lettersOK gc (zword w) = true ∧
        eqA 16240 (wordArr 16240 ruRhoArrs (zword w)) (idA 16240) = true) ∧
      lettersOK gc (zword (ruP0 ++ ruP0)) = true ∧
      eqA 16240 (wordArr 16240 ruRhoArrs (zword (ruP0 ++ ruP0))) (idA 16240) = false := by
  unfold ruRhoCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rep_ruRho (h : ruRhoCheck = true) {w : List ℤ} (hw : lettersOK gc w = true) :
    Rep 16240 (wordArr 16240 ruRhoArrs w) (wordIn gc ruRhoGen w) :=
  rep_wordArr (by decide) (fun i hi => rep_of_allPermsOK (rho_facts h).1 (by
      have : ruRhoArrs.size = 3 := rfl
      have h3 : gc = 3 := rfl
      omega))
    (fun i hi => isInvA_of_allPermsOK (rho_facts h).1 (by
      have : ruRhoArrs.size = 3 := rfl
      have h3 : gc = 3 := rfl
      omega)) hw

theorem ruRho_rels (h : ruRhoCheck = true) :
    ∀ r ∈ coverRelators (wordSet W0) ruCommW,
      FreeGroup.lift (fun i : Fin gc => ruRhoGen i) r = 1 := by
  rw [coverRelators_ruCommW]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hl, he⟩ := (rho_facts h).2.1 w hw
  rw [lift_mk_eq_wordIn]
  exact eq_of_eqA (rep_ruRho h hl) rep_idA he

noncomputable def ruRho (h : ruRhoCheck = true) : RuCover →* Equiv.Perm (Fin 16240) :=
  PresentedGroup.toGroup (ruRho_rels h)

@[expose] noncomputable def ruP0E : RuCover := PresentedGroup.mk _ (FreeGroup.mk ruP0)

theorem ruP0E_sq_ne_one (h : ruRhoCheck = true) : ruP0E ^ 2 ≠ 1 := by
  intro h1
  have hsq : ruP0E ^ 2 = PresentedGroup.mk _ (FreeGroup.mk (ruP0 ++ ruP0)) := by
    rw [pow_two, ruP0E, ← map_mul, FreeGroup.mul_mk]
  have hρ := congrArg (ruRho h) h1
  rw [hsq, map_one, ruRho, mk_eq_lift_of, ← MonoidHom.comp_apply,
    show (PresentedGroup.toGroup (ruRho_rels h)).comp (FreeGroup.lift PresentedGroup.of) =
      FreeGroup.lift (fun i : Fin gc => ruRhoGen i) from
      FreeGroup.ext_hom _ _ fun j => by
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
        exact PresentedGroup.toGroup.of _,
    lift_mk_eq_wordIn] at hρ
  have hne := (rho_facts h).2.2.2
  rw [(eqA_iff (rep_ruRho h (rho_facts h).2.2.1) rep_idA).2 hρ] at hne
  exact absurd hne (by decide)

end Rho

section Multiplier

theorem ruπ_ruP0E
    (hTab : RuTabFact) : ruπ hTab ruP0E = a ruVec := by
  rw [ruP0E, ruπ_mk]
  exact lift_ruGen_surjA

theorem card_griessHopfMultiplier_J
    (hTab : RuTabFact)
    (hRho : ruRhoCheck = true)
    (hL0 : RuIndexK) :
    Nat.card (griessHopfMultiplier (J ruVec)) = 2 := by
  obtain ⟨-, hle⟩ := card_griessHopfMultiplier_J_le hTab hL0
  obtain ⟨hfin, -⟩ := card_ruCover_le hTab hL0
  have hmem : ruP0E ^ 2 ∈ (ruπ hTab).ker := by
    rw [MonoidHom.mem_ker, map_pow, ruπ_ruP0E, a_sq]
  have hne : (ruπ hTab).ker ≠ ⊥ := fun hb => ruP0E_sq_ne_one hRho (by
    rw [hb] at hmem; exact (Subgroup.mem_bot).1 hmem)
  have h1 : 1 < Nat.card (ruπ hTab).ker := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  rw [← Nat.card_congr (griessHopfMultiplierEquivKer isPresentation_ruGen
    ruCommW_mem_commutator (lift_ruCommW hTab)).toEquiv] at h1
  omega

theorem card_griessHopfMultiplier_of_mulEquiv
    (hTab : RuTabFact) {Y : Type} [Group Y] (e : Y ≃* J ruVec)
    (hL0 : RuIndexK) :
    Nat.card (griessHopfMultiplier Y) = Nat.card (griessHopfMultiplier (J ruVec)) := by
  have hP' := isPresentation_ruGen.mulEquiv e.symm
  have hwg' : ∀ i, FreeGroup.lift (fun i => e.symm (ruGen i)) (ruCommW i) = e.symm (ruGen i) :=
    fun i => by rw [lift_mulEquiv, lift_ruCommW hTab]
  have hc := card_presentedCover hP' ruCommW_mem_commutator hwg'
  have hc' := card_presentedCover isPresentation_ruGen ruCommW_mem_commutator
    (lift_ruCommW hTab)
  obtain ⟨hfin, -⟩ := card_ruCover_le hTab hL0
  rw [Nat.card_congr e.toEquiv, hc'] at hc
  have : Finite (J ruVec) := Finite.of_surjective _
    (coverMap_surjective isPresentation_ruGen (lift_ruCommW hTab))
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hc).symm

theorem card_griessHopfMultiplier_Ru
    (hTab : RuTabFact)
    (hRho : ruRhoCheck = true)
    (hL0 : RuIndexK) :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.Ru) = 2 := by
  have e := CFSG.Sporadic.Bridge.Ru.nativeEquiv
  have h1 : Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.Ru) =
      Nat.card (griessHopfMultiplier (J ruVec)) :=
    card_griessHopfMultiplier_of_mulEquiv hTab e hL0
  rw [h1]
  exact card_griessHopfMultiplier_J hTab hRho hL0

theorem sq_eq_of_lift_conj_a
    (hTab : RuTabFact)
    (hRho : ruRhoCheck = true)
    (hL0 : RuIndexK) {L : Type} [Group L]
    [Finite L] [Group.IsPerfect L] (q : L →* J ruVec) (hq : Function.Surjective q) {t : L}
    (ht : orderOf t = 2) (hker : q.ker = zpowers t) (hcen : zpowers t ≤ center L) {v : L}
    {h : J ruVec} (hv : q v = h * a ruVec * h⁻¹) : v ^ 2 = t := by
  obtain ⟨hfin, hle⟩ := card_ruCover_le hTab hL0
  have hkerc : q.ker ≤ center L := hker ▸ hcen
  have hcardL : Nat.card L = 291852288000 := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hq).toEquiv,
      CFSG.Sporadic.Bridge.Ru.card_J, hker, Nat.card_zpowers, ht]
  obtain ⟨φ, hφ, hcomp⟩ := exists_bijective_of_card_le isPresentation_ruGen ruCommW_mem_commutator
    (lift_ruCommW hTab) q hq hkerc (hcardL ▸ hle)
  have hqφ : q (φ ruP0E) = a ruVec := by
    rw [← MonoidHom.comp_apply, hcomp]
    exact ruπ_ruP0E hTab
  have hexp : ∀ c ∈ q.ker, c ^ 2 = 1 := by
    intro c hc
    rw [hker] at hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht, pow_orderOf_eq_one,
      one_zpow]
  have hv' : q v = h * q (φ ruP0E) * h⁻¹ := by rw [hqφ]; exact hv
  have hp' : q (φ ruP0E) ^ 2 = 1 := by rw [hqφ]; exact a_sq
  have hsq := sq_eq_sq_of_conj q hq hkerc hexp hv' hp'
  rw [hsq, ← map_pow]
  refine eq_of_mem_zpowers_of_ne_one ht ?_ ?_
  · rw [← hker, MonoidHom.mem_ker]
    simp only [map_pow, hqφ, a_sq]
  · intro h1
    exact ruP0E_sq_ne_one hRho (hφ.1 (h1.trans (map_one φ).symm))

end Multiplier

end CFSG.Sporadic.Recognition.RuMultiplier
