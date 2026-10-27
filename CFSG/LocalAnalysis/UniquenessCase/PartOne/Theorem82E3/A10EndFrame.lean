module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs
public import CFSG.RankThree.PartTwo.Sec15.ThmDA10Core
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLie
import CFSG.GH74.Orders.LieType
import CFSG.Sporadic.SchreierLemmas.OrderThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open Equiv
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsAlt IsSpor)
open CFSG.Blueprint (LieModel)
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem isElemAbelian_Ebar : CFSG.Open.IsElemAbelian 3 Ebar :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
    (CFSG.IsElementaryAbelian.of_forall (fun x hx y hy => (Ebar_comm x hx y hy).eq)
      (fun x hx => by
        obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
        exact Subtype.ext (CFSG.RankThree.PartTwo.Sec15.ThmD.toP_pow_three i j k)))

private theorem exists_conj_mem_Ebar_of_cycleType_three {x : alternatingGroup (Fin 10)}
    (hcyc : (x : Perm (Fin 10)).cycleType = {3}) :
    ∃ g : alternatingGroup (Fin 10), g * x * g⁻¹ ∈ Ebar := by
  have hsupp : (x : Perm (Fin 10)).support.card + 2 ≤ Fintype.card (Fin 10) := by
    rw [Fintype.card_fin, ← Equiv.Perm.sum_cycleType, hcyc]
    decide
  have hconj : IsConj (x : Perm (Fin 10)) (ec : Perm (Fin 10)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (hcyc.trans cycleType_ec.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp (alternatingGroup.isConj_of hconj hsupp)
  exact ⟨g, by rw [hg]; exact ec_mem_Ebar⟩

private theorem exists_conj_mem_Ebar_of_cycleType_three_three {x : alternatingGroup (Fin 10)}
    (hcyc : (x : Perm (Fin 10)).cycleType = {3, 3}) :
    ∃ g : alternatingGroup (Fin 10), g * x * g⁻¹ ∈ Ebar := by
  have hsupp : (x : Perm (Fin 10)).support.card + 2 ≤ Fintype.card (Fin 10) := by
    rw [Fintype.card_fin, ← Equiv.Perm.sum_cycleType, hcyc]
    decide
  have hconj : IsConj (x : Perm (Fin 10))
      ((ea * eb : alternatingGroup (Fin 10)) : Perm (Fin 10)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (hcyc.trans cycleType_ea_mul_eb.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp (alternatingGroup.isConj_of hconj hsupp)
  refine ⟨g, ?_⟩
  rw [hg]
  exact Ebar.mul_mem ea_mem_Ebar eb_mem_Ebar

private theorem exists_conj_mem_Ebar_of_cycleType_three_three_three
    {x : alternatingGroup (Fin 10)} (hcyc : (x : Perm (Fin 10)).cycleType = {3, 3, 3}) :
    ∃ g : alternatingGroup (Fin 10), g * x * g⁻¹ ∈ Ebar := by
  have hconj : IsConj (x : Perm (Fin 10))
      ((ea * eb * ec : alternatingGroup (Fin 10)) : Perm (Fin 10)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (hcyc.trans cycleType_ea_mul_eb_mul_ec.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let h : Perm (Fin 10) := swap 0 3 * swap 1 4 * swap 2 5
  have hodd : Perm.sign h = -1 := by decide
  have hc : Commute h ((ea * eb * ec : alternatingGroup (Fin 10)) : Perm (Fin 10)) := by
    exact commute_oddThree_pa_mul_pb_mul_pc
  have hsign : Perm.sign g = 1 ∨ Perm.sign g = -1 := Int.units_eq_one_or (Perm.sign g)
  rcases hsign with h1 | h1
  · refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr h1⟩, ?_⟩
    have hgoal : (⟨g, Equiv.Perm.mem_alternatingGroup.mpr h1⟩ : alternatingGroup (Fin 10)) *
        x * ⟨g, Equiv.Perm.mem_alternatingGroup.mpr h1⟩⁻¹ = ea * eb * ec :=
      Subtype.ext hg
    rw [hgoal]
    exact Ebar.mul_mem (Ebar.mul_mem ea_mem_Ebar eb_mem_Ebar) ec_mem_Ebar
  · have hg' : Perm.sign (h * g) = 1 := by rw [map_mul, hodd, h1]; decide
    refine ⟨⟨h * g, Equiv.Perm.mem_alternatingGroup.mpr hg'⟩, ?_⟩
    have hgoal : (⟨h * g, Equiv.Perm.mem_alternatingGroup.mpr hg'⟩ :
        alternatingGroup (Fin 10)) * x *
        ⟨h * g, Equiv.Perm.mem_alternatingGroup.mpr hg'⟩⁻¹ = ea * eb * ec := by
      apply Subtype.ext
      show h * g * (x : Perm (Fin 10)) * (h * g)⁻¹ =
        ((ea * eb * ec : alternatingGroup (Fin 10)) : Perm (Fin 10))
      calc h * g * (x : Perm (Fin 10)) * (h * g)⁻¹
          = h * (g * (x : Perm (Fin 10)) * g⁻¹) * h⁻¹ := by group
        _ = h * ((ea * eb * ec : alternatingGroup (Fin 10)) : Perm (Fin 10)) * h⁻¹ := by rw [hg]
        _ = ((ea * eb * ec : alternatingGroup (Fin 10)) : Perm (Fin 10)) := by
            rw [hc.eq]; group
    rw [hgoal]
    exact Ebar.mul_mem (Ebar.mul_mem ea_mem_Ebar eb_mem_Ebar) ec_mem_Ebar

theorem exists_conj_mem_Ebar_of_orderOf_eq_three {x : alternatingGroup (Fin 10)}
    (hx : orderOf x = 3) : ∃ g : alternatingGroup (Fin 10), g * x * g⁻¹ ∈ Ebar := by
  classical
  have hx' : orderOf (x : Perm (Fin 10)) = 3 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨k, hk1, hk3, hcyc, -, -, -⟩ :=
    CFSG.Sporadic.SchreierLemmas.order_three_permutation_shape (Ω := Fin 10) hx'
  have hk_le : k ≤ 3 := by
    have := hk3
    rw [Fintype.card_fin] at this
    omega
  interval_cases k
  · exact exists_conj_mem_Ebar_of_cycleType_three (by simpa using hcyc)
  · exact exists_conj_mem_Ebar_of_cycleType_three_three (by simpa using hcyc)
  · exact exists_conj_mem_Ebar_of_cycleType_three_three_three (by simpa using hcyc)

private theorem factorization_alternatingGroup_fin_ten :
    (Nat.card (alternatingGroup (Fin 10))).factorization 3 = 4 := by
  rw [nat_card_alternatingGroup, Nat.card_fin,
    show (10 : ℕ).factorial / 2 = 3 ^ 4 * 22400 by norm_num]
  exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)

private noncomputable def sylowPstA10 : Sylow 3 (alternatingGroup (Fin 10)) :=
  Sylow.ofCard Pst (by rw [card_Pst, factorization_alternatingGroup_fin_ten]; norm_num)

private theorem coe_sylowPstA10 :
    (sylowPstA10 : Subgroup (alternatingGroup (Fin 10))) = Pst :=
  Sylow.coe_ofCard Pst _

private theorem exists_sylow_conj_Pst_of_card_eq_81
    {Q : Subgroup (alternatingGroup (Fin 10))} (hQ : Nat.card Q = 81) :
    ∃ (S : Sylow 3 (alternatingGroup (Fin 10))) (g : alternatingGroup (Fin 10)),
      (S : Subgroup (alternatingGroup (Fin 10))) = Q ∧
      (S : Subgroup (alternatingGroup (Fin 10))) =
        (g • sylowPstA10 : Sylow 3 (alternatingGroup (Fin 10))) ∧
      (∀ x, x ∈ (S : Subgroup (alternatingGroup (Fin 10))) ↔
        ∃ s ∈ Pst, g * s * g⁻¹ = x) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := 4) (by rw [hQ]; norm_num)
  obtain ⟨S, hQS⟩ := hQ3.exists_le_sylow
  have hS81 : Nat.card (S : Subgroup (alternatingGroup (Fin 10))) = 81 := by
    rw [S.card_eq_multiplicity, factorization_alternatingGroup_fin_ten]
    norm_num
  have hQeqS : Q = S := Subgroup.eq_of_le_of_card_ge hQS (by rw [hS81, hQ])
  subst hQeqS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 10)) sylowPstA10 S
  have hS_eq : (S : Subgroup (alternatingGroup (Fin 10))) =
      ((g • sylowPstA10 : Sylow 3 (alternatingGroup (Fin 10))) :
        Subgroup (alternatingGroup (Fin 10))) :=
    congrArg (fun P : Sylow 3 (alternatingGroup (Fin 10)) =>
      (P : Subgroup (alternatingGroup (Fin 10)))) hg.symm
  refine ⟨S, g, rfl, hS_eq, ?_⟩
  intro x
  rw [hS_eq, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hgs⟩
    refine ⟨s, ?_, by simpa [MulAut.smul_def, MulAut.conj_apply] using hgs⟩
    rwa [coe_sylowPstA10] at hs
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, ?_, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rwa [coe_sylowPstA10]

private theorem existsUnique_elemAbelian_card_27_of_sylow_conj
    {S : Sylow 3 (alternatingGroup (Fin 10))} {g : alternatingGroup (Fin 10)}
    (hS : (S : Subgroup (alternatingGroup (Fin 10))) =
      (g • sylowPstA10 : Sylow 3 (alternatingGroup (Fin 10))))
    (hpoint : ∀ x, x ∈ (S : Subgroup (alternatingGroup (Fin 10))) ↔
      ∃ s ∈ Pst, g * s * g⁻¹ = x) :
    ∃! E : Subgroup (alternatingGroup (Fin 10)),
      E ≤ S ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  let E : Subgroup (alternatingGroup (Fin 10)) := Ebar.map (MulAut.conj g).toMonoidHom
  have hE_le_S : E ≤ S := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have hbS₀ : b ∈ (sylowPstA10 : Subgroup (alternatingGroup (Fin 10))) := by
      rw [coe_sylowPstA10]
      exact Ebar_le_Pst hb
    have hbS : MulAut.conj g b ∈ ((g • sylowPstA10 : Sylow 3 (alternatingGroup (Fin 10))) :
        Subgroup (alternatingGroup (Fin 10))) := by
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨b, hbS₀, rfl⟩
    rwa [← hS] at hbS
  have hE_ab : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_Ebar.map _
  have hE_card : Nat.card E = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_Ebar]
  refine ⟨E, ⟨hE_le_S, hE_ab, hE_card⟩, ?_⟩
  intro E' hE'
  obtain ⟨hE'_le_S, hE'_ab, hE'_card⟩ := hE'
  have hE'_conj_le : E'.map (MulAut.conj g⁻¹).toMonoidHom ≤ Pst := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨s, hs, hgs⟩ := (hpoint e).mp (hE'_le_S he)
    have hxe : (MulAut.conj g⁻¹).toMonoidHom e = s := by
      rw [← hgs]; simp [MulAut.conj_apply]; group
    rw [hxe]
    exact hs
  have hE'_conj_ab : CFSG.Open.IsElemAbelian 3 (E'.map (MulAut.conj g⁻¹).toMonoidHom) :=
    hE'_ab.map _
  have hE'_conj_card : Nat.card (E'.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE'_card]
  have hE'_conj_eq : E'.map (MulAut.conj g⁻¹).toMonoidHom = Ebar :=
    eq_Ebar_of_abelian_card_27 hE'_conj_le
      (fun x hx y hy => hE'_conj_ab.comm hx hy) hE'_conj_card
  have hE'_le_E : E' ≤ E := by
    intro e he
    obtain ⟨s, hs, hgs⟩ := (hpoint e).mp (hE'_le_S he)
    have hsEbar : s ∈ Ebar := by
      have hmem : s ∈ E'.map (MulAut.conj g⁻¹).toMonoidHom := by
        refine Subgroup.mem_map.mpr ⟨e, he, ?_⟩
        rw [← hgs]; simp [MulAut.conj_apply]; group
      rwa [hE'_conj_eq] at hmem
    rw [← hgs]
    exact Subgroup.mem_map.mpr ⟨s, hsEbar, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hE'_le_E (by rw [hE_card, hE'_card])

theorem existsUnique_elemAbelian_card_27_of_card_eq_81
    {Q : Subgroup (alternatingGroup (Fin 10))} (hQ : Nat.card Q = 81) :
    ∃! E : Subgroup (alternatingGroup (Fin 10)),
      E ≤ Q ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨S, g, hS_Q, hS_conj, hpoint⟩ := exists_sylow_conj_Pst_of_card_eq_81 hQ
  obtain ⟨E, hE, hEuniq⟩ := existsUnique_elemAbelian_card_27_of_sylow_conj hS_conj hpoint
  refine ⟨E, hS_Q ▸ hE, ?_⟩
  intro E' hE'
  exact hEuniq E' (hS_Q.symm ▸ hE')

section Quotient

variable {X : Type} [Group X] [Finite X] {Z : Subgroup X} [Z.Normal]

private theorem factorization_card_of_quotient_eq_four
    (hZ3 : ¬ 3 ∣ Nat.card Z) (e : X ⧸ Z ≃* alternatingGroup (Fin 10)) :
    (Nat.card X).factorization 3 = 4 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z,
    Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hZ3, add_zero, Nat.card_congr e.toEquiv]
  exact factorization_alternatingGroup_fin_ten

private theorem card_sylow_eq_81_of_quotient
    (hZ3 : ¬ 3 ∣ Nat.card Z) (e : X ⧸ Z ≃* alternatingGroup (Fin 10))
    (P : Sylow 3 X) : Nat.card (P : Subgroup X) = 81 := by
  rw [P.card_eq_multiplicity, factorization_card_of_quotient_eq_four hZ3 e]
  norm_num

private theorem exists_map_sylow_data
    (hZ3 : ¬ 3 ∣ Nat.card Z) (e : X ⧸ Z ≃* alternatingGroup (Fin 10)) (P : Sylow 3 X) :
    ∃ (Φ : X →* alternatingGroup (Fin 10)) (E : Subgroup (alternatingGroup (Fin 10))),
      Φ = e.toMonoidHom.comp (QuotientGroup.mk' Z) ∧
      Function.Injective (Φ.comp (P : Subgroup X).subtype) ∧
      E ≤ (P : Subgroup X).map Φ ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      (∀ E' : Subgroup (alternatingGroup (Fin 10)),
        E' ≤ (P : Subgroup X).map Φ → CFSG.Open.IsElemAbelian 3 E' →
        Nat.card E' = 27 → E' = E) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Φ : X →* alternatingGroup (Fin 10) := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hinjP : Function.Injective (Φ.comp (P : Subgroup X).subtype) := by
    have h1 : Function.Injective ((QuotientGroup.mk' Z).comp (P : Subgroup X).subtype) :=
      CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := Z)
        (Q := (P : Subgroup X)) hZ3 P.isPGroup'
    exact e.injective.comp h1
  have hPcard : Nat.card (P : Subgroup X) = 81 := card_sylow_eq_81_of_quotient hZ3 e P
  have hrange : (Φ.comp (P : Subgroup X).subtype).range = (P : Subgroup X).map Φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hP'card : Nat.card ((P : Subgroup X).map Φ) = 81 := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjP).toEquiv).symm.trans hPcard
  obtain ⟨E, hE, hEuniq⟩ := existsUnique_elemAbelian_card_27_of_card_eq_81 hP'card
  refine ⟨Φ, E, rfl, hinjP, hE.1, hE.2.1, hE.2.2, ?_⟩
  intro E' hE'_le hE'_ab hE'_card
  exact hEuniq E' ⟨hE'_le, hE'_ab, hE'_card⟩

theorem existsUnique_elemAbelian_card_27_of_sylow_of_quotient
    (hZ3 : ¬ 3 ∣ Nat.card Z)
    (e : X ⧸ Z ≃* alternatingGroup (Fin 10)) (P : Sylow 3 X) :
    ∃! A : Subgroup X, A ≤ P ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Φ, E, hΦ, hinjP, hE_le, hE_ab, hE_card, hEuniq⟩ := exists_map_sylow_data hZ3 e P
  let f : ↥P →* alternatingGroup (Fin 10) := Φ.comp (P : Subgroup X).subtype
  let E' : Subgroup ↥P := E.comap f
  let A : Subgroup X := E'.map (P : Subgroup X).subtype
  have hE_le_range : E ≤ f.range := by
    rw [show f.range = (P : Subgroup X).map Φ from by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact hE_le
  have hmapE : E'.map f = E := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hE_le_range]
  have hE'_ab : CFSG.Open.IsElemAbelian 3 E' := hE_ab.comap hinjP
  have hE'_card : Nat.card E' = 27 := by
    calc Nat.card E' = Nat.card (E'.map f) :=
          (Subgroup.card_map_of_injective hinjP).symm
      _ = Nat.card E := by rw [hmapE]
      _ = 27 := hE_card
  have hA_le_P : A ≤ P := Subgroup.map_subtype_le E'
  have hA_ab : CFSG.Open.IsElemAbelian 3 A := hE'_ab.map (P : Subgroup X).subtype
  have hA_card : Nat.card A = 27 :=
    (Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective).trans hE'_card
  refine ⟨A, ⟨hA_le_P, hA_ab, hA_card⟩, ?_⟩
  intro B hB
  obtain ⟨hB_le_P, hB_ab, hB_card⟩ := hB
  have hB'card : Nat.card (B.map Φ) = 27 := by
    have hBrange : (Φ.comp B.subtype).range = B.map Φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hinjB : Function.Injective (Φ.comp B.subtype) := by
      rw [hΦ]
      have h1 : Function.Injective ((QuotientGroup.mk' Z).comp B.subtype) :=
        CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := Z)
          (Q := B) hZ3 hB_ab.isPGroup
      exact e.injective.comp h1
    rw [← hBrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjB).toEquiv).symm.trans hB_card
  have hB'props : B.map Φ ≤ (P : Subgroup X).map Φ ∧
      CFSG.Open.IsElemAbelian 3 (B.map Φ) ∧ Nat.card (B.map Φ) = 27 :=
    ⟨Subgroup.map_mono hB_le_P, hB_ab.map Φ, hB'card⟩
  have hB'eq : B.map Φ = E := hEuniq (B.map Φ) hB'props.1 hB'props.2.1 hB'props.2.2
  have hB_le_A : B ≤ A := by
    intro b hb
    have hbP : b ∈ P := hB_le_P hb
    have hbE : Φ b ∈ E := by
      rw [← hB'eq]
      exact Subgroup.mem_map_of_mem Φ hb
    exact Subgroup.mem_map.mpr ⟨⟨b, hbP⟩, Subgroup.mem_comap.mpr hbE, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hB_le_A (by rw [hA_card, hB_card])

private theorem orderOf_map_quotient_eq_three
    (hZ3 : ¬ 3 ∣ Nat.card Z) (e : X ⧸ Z ≃* alternatingGroup (Fin 10))
    {x : X} (hx : orderOf x = 3) : orderOf (e (QuotientGroup.mk' Z x)) = 3 := by
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxbar_ne : QuotientGroup.mk' Z x ≠ 1 := by
    intro h1
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff (N := Z) x).mp h1
    have h3dvd : 3 ∣ Nat.card Z := by
      have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxZ)
    exact hZ3 h3dvd
  have hxbar3 : orderOf (QuotientGroup.mk' Z x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hxbar_ne
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, show (QuotientGroup.mk' Z x) ^ 3 = 1 from by
      rw [← hxbar3]; exact pow_orderOf_eq_one _, map_one]
  · intro h1
    exact hxbar_ne (e.injective (by simpa using h1))

private theorem exists_conj_map_of_map_conj_eq_Ebar
    {Ā' : Subgroup (alternatingGroup (Fin 10))} {h : alternatingGroup (Fin 10)}
    (hh : Ā'.map (MulAut.conj h⁻¹).toMonoidHom = Ebar)
    {y : alternatingGroup (Fin 10)} (hy : orderOf y = 3) :
    ∃ k' : alternatingGroup (Fin 10), k' * y * k'⁻¹ ∈ Ā' := by
  obtain ⟨k, hk⟩ := exists_conj_mem_Ebar_of_orderOf_eq_three hy
  let k' : alternatingGroup (Fin 10) := h * k
  refine ⟨k', ?_⟩
  rw [← hh] at hk
  obtain ⟨a', ha', ha'eq⟩ := Subgroup.mem_map.mp hk
  have hEq : k' * y * k'⁻¹ = a' := by
    have hstep := congrArg (MulAut.conj h) ha'eq
    change (MulAut.conj h) ((MulAut.conj h⁻¹) a') =
      (MulAut.conj h) (k * y * k⁻¹) at hstep
    simp only [MulAut.conj_apply] at hstep
    rw [inv_inv] at hstep
    have hL : h * (h⁻¹ * a' * h) * h⁻¹ = a' := by group
    rw [hL] at hstep
    rw [hstep]
    dsimp [k']
    group
  rw [hEq]
  exact ha'

private theorem mem_of_mul_inv_mem_center_of_pow_three
    (hZc : Z ≤ Subgroup.center X) (hZ3 : ¬ 3 ∣ Nat.card Z)
    {A : Subgroup X} (hA_ab : CFSG.Open.IsElemAbelian 3 A)
    {y a : X} (ha : a ∈ A) (hy3 : y ^ 3 = 1) (hz : y * a⁻¹ ∈ Z) : y ∈ A := by
  let z : X := y * a⁻¹
  have hz_central : z ∈ Subgroup.center X := hZc hz
  have hza : z * a = y := by dsimp [z]; group
  have hz3 : z ^ 3 = 1 := by
    have hcomm : Commute z a := (Subgroup.mem_center_iff.mp hz_central a).symm
    have hpow : y ^ 3 = z ^ 3 * a ^ 3 := by rw [← hza, hcomm.mul_pow]
    rw [hpow, hA_ab.2 a ha, mul_one] at hy3
    exact hy3
  have hz1 : z = 1 := by
    have hcop : Nat.Coprime 3 (Nat.card Z) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3
    have hz3dvd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hzZcard : orderOf z ∣ Nat.card Z := by
      have hcard : Nat.card (Subgroup.zpowers z) = orderOf z := Nat.card_zpowers z
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hz3dvd hzZcard)
  rw [← hza, hz1, one_mul]
  exact ha

theorem exists_conj_mem_of_elemAbelian_card_27_of_quotient
    (hZc : Z ≤ Subgroup.center X) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (e : X ⧸ Z ≃* alternatingGroup (Fin 10))
    {A : Subgroup X} (hA_ab : CFSG.Open.IsElemAbelian 3 A) (hA_card : Nat.card A = 27)
    {x : X} (hx : orderOf x = 3) : ∃ g : X, g * x * g⁻¹ ∈ A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hinjA : Function.Injective (π.comp A.subtype) := by
    simpa only [π] using
      CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := Z)
        (Q := A) hZ3 hA_ab.isPGroup
  let Ā : Subgroup (X ⧸ Z) := A.map π
  have hĀ_card : Nat.card Ā = 27 := by
    have hrange : (π.comp A.subtype).range = Ā := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjA).toEquiv).symm.trans hA_card
  have hĀ_ab : CFSG.Open.IsElemAbelian 3 Ā := hA_ab.map π
  let Ā' : Subgroup (alternatingGroup (Fin 10)) := Ā.map e.toMonoidHom
  have hĀ'_card : Nat.card Ā' = 27 := by
    rw [Subgroup.card_map_of_injective e.injective, hĀ_card]
  have hĀ'_ab : CFSG.Open.IsElemAbelian 3 Ā' := hĀ_ab.map e.toMonoidHom
  obtain ⟨h, hh⟩ := CFSG.RankThree.PartTwo.Sec15.ThmD.exists_conj_eq_Ebar hĀ'_card
    (fun y hy z hz => hĀ'_ab.comm hy hz)
  obtain ⟨k', hk'⟩ := exists_conj_map_of_map_conj_eq_Ebar hh
    (orderOf_map_quotient_eq_three hZ3 e hx)
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective Z (e.symm k')
  have hg₀' : e (π g₀) = k' := by rw [hg₀, MulEquiv.apply_symm_apply]
  let y : X := g₀ * x * g₀⁻¹
  have hπy : π y ∈ Ā := by
    have h1 : e (π y) ∈ Ā' := by
      have hπy_eq : π y = (e.symm k') * π x * (e.symm k')⁻¹ := by
        dsimp [y]
        rw [map_mul, map_mul, map_inv, show π g₀ = e.symm k' from hg₀]
      rw [hπy_eq, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hk'
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp h1
    have : a = π y := e.injective hae
    rwa [this] at ha
  obtain ⟨a, haA, haπ⟩ := Subgroup.mem_map.mp hπy
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy3 : y ^ 3 = 1 := by
    dsimp [y]
    rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hz : y * a⁻¹ ∈ Z := by
    rw [← QuotientGroup.ker_mk' (N := Z), MonoidHom.mem_ker, map_mul, map_inv, haπ,
      mul_inv_cancel]
  exact ⟨g₀, by simpa [y] using
    mem_of_mul_inv_mem_center_of_pow_three hZc hZ3 hA_ab haA hy3 hz⟩

end Quotient

namespace Ctx82E3

theorem nonempty_a10Frame (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L)
    (hK2 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar))
    (hA : CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 10)
    (hsig : D.sig = {5}) : Nonempty (A10Frame c) := by
  classical
  have hON : ¬ CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Y _ => IsSpor Y .ONan) c.Lbar := by
    rintro ⟨-, hZcard, -⟩
    exact hZ (by rw [hZcard])
  have h227 : ¬ LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3 := by
    intro hLie
    obtain ⟨e⟩ := hA
    have h1 : Nat.card (c.Lbar ⧸ Subgroup.center c.Lbar) = 1814400 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.RankThree.PartTwo.Sec15.ThmD.card_alternatingGroup_fin_ten]
    have h2 : Nat.card (c.Lbar ⧸ Subgroup.center c.Lbar) = 9828 := by
      rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hLie]
      norm_num [CFSG.Open.ordA]
    omega
  have hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M → P ≤ c.L :=
    fun P hP => Ctx82E3.le_L_of_K2 c h811 hK2 hZ hON h227 hP
  have ha : ∀ P : Sylow 3 c.Lbar, ∃! A : Subgroup c.Lbar,
      A ≤ P ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 :=
    fun P => existsUnique_elemAbelian_card_27_of_sylow_of_quotient
      (Z := Subgroup.center c.Lbar) hZ hA.some P
  have hb : ∀ A : Subgroup c.Lbar, CFSG.Open.IsElemAbelian 3 A → Nat.card A = 27 →
      ∀ x : c.Lbar, orderOf x = 3 → ∃ g, g * x * g⁻¹ ∈ A :=
    fun A hAab hAcard x hx => exists_conj_mem_of_elemAbelian_card_27_of_quotient
      (Z := Subgroup.center c.Lbar) le_rfl hZ hA.some hAab hAcard hx
  obtain ⟨S⟩ := Ctx82E3.exists_case811Sylow c ha hb hPL
  exact ⟨{ S with qs := h811, center := hZ, iso := hA.some, sig := hsig }⟩

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
