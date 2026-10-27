module

public import CFSG.RankThree.GF2n.Parrott.QA45ListGroups
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.GroupTheory.ConjActionPerm
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups
open CFSG.Open
open CFSG.Sporadic.Schreier (tab tab_eq)

local notation "P45" => Equiv.Perm (Fin 45)

private theorem mem_conjOrbit {N : List P45} {g x : P45} :
    x ∈ conjOrbit N g ↔ ∃ c ∈ N, c * g * c⁻¹ = x := by
  simp [conjOrbit, tab_eq, List.mem_dedup, List.mem_map]

private theorem centralizerSCheck_spec (h : centralizerSCheck () = true) :
    ∀ c ∈ elemsT QA45, (∀ x ∈ Sgens, c * x = x * c) → c ∈ Slist () := by
  intro c hc hx
  have h1 := List.all_eq_true.1 h c hc
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, tabList_eq] at h1
  rcases h1 with h1 | h1
  · exfalso
    have hall : Sgens.all (fun x => decide (c * x = x * c)) = true :=
      List.all_eq_true.2 fun x hxm => decide_eq_true (hx x hxm)
    rw [hall] at h1
    exact Bool.noConfusion h1
  · exact h1

private theorem sOrbitCheck_spec {N : List P45} (h : sOrbitCheck N = true) :
    (conjOrbit N t).length = 5 ∧
    (∀ g ∈ elemsT QA45, (∀ o ∈ conjOrbit N t, g * o = o * g) → g ∈ Slist ()) ∧
    (∀ s ∈ Slist (), s ≠ 1 → s ∈ conjOrbit N t ∨ s ∈ conjOrbit N (u * t)) ∧
    u * t ∉ conjOrbit N t := by
  simp only [sOrbitCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.mem_filter, tab_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun g hg hc => ?_, fun s hs hs1 => ?_, by simpa using h4⟩
  · rcases h2 g hg with h | h
    · exfalso
      have hall : (conjOrbit N t).all (fun o => decide (g * o = o * g)) = true :=
        List.all_eq_true.2 fun o hom => decide_eq_true (hc o hom)
      rw [hall] at h
      exact Bool.noConfusion h
    · exact h
  · have := h3 s ⟨hs, by simpa using hs1⟩
    simpa using this


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)

theorem exists_map_conj_le_sylowTwo {P : Subgroup A45}
    (hP : IsPGroup 2 P) : ∃ g : A45, P.map (MulAut.conj g).toMonoidHom ≤ sylowTwoQA45 := by
  obtain ⟨P₀, hP₀⟩ := isSylow_sylowTwoQA45
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.exists_map_conj_le_sylow P₀ hP
  rw [hP₀] at hg
  exact ⟨g, hg⟩

private theorem eq_four_of_le_sylowTwo {E : Subgroup A45}
    (hE : IsElemAbelian 2 E) (hc : Nat.card E = 16) (hle : E ≤ sylowTwoQA45) :
    E = sQA45 ∨ E = eUVQA45 ∨ E = eVQA45 ∨ E = eVAQA45 := by
  classical
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => hE.mul_self_eq_one hx
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => hE.comm hx hy
  obtain ⟨l, hl4, hlnd, hlmem, hlcl⟩ := CFSG.GroupTheory.exists_closure_four_eq E hsq hcomm hc
  let lp : List P45 := l.map Subtype.val
  have hlp_mem : ∀ x ∈ lp, x ∈ T0list () ∧ x * x = 1 ∧ x ≠ 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hyE, hy1⟩ := hlmem y hy
    refine ⟨(mem_sylowTwoQA45_iff y).1 (hle hyE), ?_, fun h => hy1 (Subtype.ext h)⟩
    have := congrArg Subtype.val (hsq y hyE)
    simpa using this
  have hlp_nd : lp.Nodup := hlnd.map Subtype.val_injective
  have hlp_sub : lp ⊆ involutionsOf (T0list ()) := fun x hx =>
    List.mem_filter.2 ⟨(hlp_mem x hx).1, decide_eq_true ⟨(hlp_mem x hx).2.1, (hlp_mem x hx).2.2⟩⟩
  obtain ⟨l', hperm, hsub⟩ := List.subperm_of_subset hlp_nd hlp_sub
  have hl'len : l'.length = 4 := by rw [hperm.length_eq]; simp [lp, hl4]
  have hl'mem : l' ∈ (involutionsOf (T0list ())).sublistsLen 4 :=
    List.mem_sublistsLen.2 ⟨hsub, hl'len⟩
  have hl'E : ∀ x ∈ l', ∃ y ∈ E, (y : P45) = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 hx)
    exact ⟨y, (hlmem y hy).1, rfl⟩
  have hcommL : ∀ a ∈ l', ∀ b ∈ l', a * b = b * a := by
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := hl'E a ha
    obtain ⟨z, hz, rfl⟩ := hl'E b hb
    have := congrArg Subtype.val (hcomm y hy z hz)
    simpa using this
  have hsqL : ∀ x ∈ l', x * x = 1 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := hl'E a ha
    have := congrArg Subtype.val (hsq y hy)
    simpa using this
  have hclosure : E.map QA45.originalSubgroup.subtype = Subgroup.closure {x | x ∈ l'} := by
    rw [← hlcl, MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Subgroup.coe_subtype]
    rw [hperm.mem_iff]
    simp [lp]
  have hspan : ∀ y ∈ E, (y : P45) ∈ prodSpan l' := fun y hy =>
    mem_prodSpan_of_mem_closure l' hsqL hcommL _
      (hclosure ▸ Subgroup.mem_map_of_mem _ hy)
  have hnd : (prodSpan l').Nodup := by
    have hlen : (prodSpan l').length = 16 := by
      rw [length_prodSpan, hl'len]
      norm_num
    have h16 : 16 ≤ (prodSpan l').toFinset.card := by
      have := Nat.card_le_card_of_injective (α := E) (β := (prodSpan l').toFinset)
        (fun y => ⟨(y : P45), List.mem_toFinset.2 (hspan y y.2)⟩)
        (fun a b h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
      rw [hc, Nat.card_eq_fintype_card (α := (prodSpan l').toFinset), Fintype.card_coe] at this
      exact this
    refine List.nodup_iff_le_length_dedup.2 ?_
    rw [← List.card_toFinset]
    omega
  have hcheck := e16Check_spec qa45L1Facts.e16_in_t0 l' hl'mem (pairwiseCommB_of_forall hcommL) hnd
  have conclude : ∀ (L «gens» : List P45) (hX : ListGroupFacts L «gens»),
      subsetB (prodSpan l') L = true → L.length = 16 → E = listSubgroup hX := by
    intro L «gens» hX hsubset hL
    refine eq_listSubgroup_of_card hX (fun y hy => ?_) (by rw [hc, hL])
    exact (mem_listSubgroup hX y).2
      (of_decide_eq_true (List.all_eq_true.1 hsubset _ (hspan y hy)))
  rcases hcheck with h | h | h | h
  · exact Or.inl ((conclude _ _ _ h (by rw [length_Slist]; norm_num)).trans
      sQA45_eq_listSubgroup.symm)
  · exact Or.inr (Or.inl ((conclude _ _ _ h (by rw [length_E3list]; norm_num)).trans
      eUVQA45_eq_listSubgroup.symm))
  · exact Or.inr (Or.inr (Or.inl ((conclude _ _ _ h (by rw [length_E1list]; norm_num)).trans
      eVQA45_eq_listSubgroup.symm)))
  · exact Or.inr (Or.inr (Or.inr ((conclude _ _ _ h (by rw [length_E2list]; norm_num)).trans
      eVAQA45_eq_listSubgroup.symm)))

private theorem exists_conj_four (E : Subgroup A45)
    (hE : IsElemAbelian 2 E) (hc : Nat.card E = 16) :
    ∃ E' : Subgroup A45, QA45SubgroupConj E E' ∧
      (E' = sQA45 ∨ E' = eUVQA45 ∨ E' = eVQA45 ∨ E' = eVAQA45) := by
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylowTwo hE.isPGroup
  exact ⟨_, ⟨g, rfl⟩, eq_four_of_le_sylowTwo (hE.map (MulAut.conj g).toMonoidHom)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]) hg⟩

private theorem qa45SubgroupConj_eVA_eV : QA45SubgroupConj eVAQA45 eVQA45 := by
  refine ⟨b1A⁻¹, ?_⟩
  rw [← map_conj_eVQA45]
  exact CFSG.GroupTheory.map_conj_map_conj_inv b1A eVQA45

private theorem eq_sQA45_of_le_Q {E : Subgroup A45}
    (h : E = sQA45 ∨ E = eUVQA45 ∨ E = eVQA45 ∨ E = eVAQA45)
    (hEQ : E ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) : E = sQA45 := by
  have huQ : uA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := u_mem_Q
  have hvQ : vA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := v_not_mem_Q
  have ha1Q : a1A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := alpha1_mem_Q
  rcases h with h | rfl | rfl | rfl
  · exact h
  · exfalso
    have h1 : uA * vA ∈ eUVQA45 := Subgroup.subset_closure (Set.mem_insert _ _)
    have h2 := hEQ h1
    have h3 := mul_mem (inv_mem huQ) h2
    rw [inv_mul_cancel_left] at h3
    exact hvQ h3
  · exfalso
    have h1 : vA ∈ eVQA45 := Subgroup.subset_closure (Set.mem_insert _ _)
    exact hvQ (hEQ h1)
  · exfalso
    have h1 : vA * a1A ∈ eVAQA45 := Subgroup.subset_closure (Set.mem_insert _ _)
    have h2 := hEQ h1
    have h3 := mul_mem h2 (inv_mem ha1Q)
    rw [mul_inv_cancel_right] at h3
    exact hvQ h3

theorem qa45_elemAbelian_sixteen :
    (∀ E : Subgroup A45, IsElemAbelian 2 E → Nat.card E = 16 →
      QA45SubgroupConj E sQA45 ∨ QA45SubgroupConj E eUVQA45 ∨ QA45SubgroupConj E eVQA45) ∧
    (∀ E : Subgroup A45, IsElemAbelian 2 E → Nat.card E = 16 →
      E ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup → QA45SubgroupConj E sQA45) := by
  constructor
  · intro E hE hc
    obtain ⟨E', hconj, h | h | h | h⟩ := exists_conj_four E hE hc
    · exact Or.inl (h ▸ hconj)
    · exact Or.inr (Or.inl (h ▸ hconj))
    · exact Or.inr (Or.inr (h ▸ hconj))
    · exact Or.inr (Or.inr (hconj.trans (h ▸ qa45SubgroupConj_eVA_eV)))
  · intro E hE hc hEQ
    obtain ⟨E', hconj, hE'⟩ := exists_conj_four E hE hc
    obtain ⟨g, hg⟩ := hconj
    have hQnorm : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
      Subgroup.normal_of_index_eq_two index_QP45
    have hE'Q : E' ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [← hg]
      rintro _ ⟨x, hx, rfl⟩
      exact hQnorm.conj_mem x (hEQ hx) g
    exact ⟨g, hg.trans (eq_sQA45_of_le_Q hE' hE'Q)⟩

private theorem le_listSubgroup_of_inv_centralizer
    {L «gens» : List P45} (hL : ListGroupFacts L «gens») {E : Subgroup A45} (hE : IsElemAbelian 2 E)
    (hEle : E ≤ sylowTwoQA45) (hXE : listSubgroup hL ≤ E)
    (hspec : ∀ c ∈ T0list (), c * c = 1 → (∀ x ∈ «gens», c * x = x * c) → c ∈ L) :
    E ≤ listSubgroup hL := by
  intro c hcE
  have hcT : (c : P45) ∈ T0list () := (mem_sylowTwoQA45_iff c).1 (hEle hcE)
  have hsq : (c : P45) * c = 1 := by
    have := congrArg Subtype.val (hE.mul_self_eq_one hcE)
    simpa using this
  refine (mem_listSubgroup hL c).2 (hspec _ hcT hsq fun x hx => ?_)
  have hxL : x ∈ L := of_decide_eq_true (List.all_eq_true.1 hL.gens_mem x hx)
  have hxX : (⟨x, hL.mem_A hxL⟩ : A45) ∈ listSubgroup hL := (mem_listSubgroup hL _).2 hxL
  exact congrArg Subtype.val (hE.comm hcE (hXE hxX))

theorem qa45_elemAbelian_card_le_sixteen :
    ∀ E : Subgroup A45, IsElemAbelian 2 E → Nat.card E ≤ 16 := by
  intro E hE
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylowTwo hE.isPGroup
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup A45, E' = E.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  rw [← hE'] at hg
  have hE'ea : IsElemAbelian 2 E' := hE' ▸ hE.map _
  have hE'c : Nat.card E' = Nat.card E := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hsq : ∀ x ∈ E', x * x = 1 := fun x hx => hE'ea.mul_self_eq_one hx
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := fun x hx y hy => hE'ea.comm hx hy
  obtain ⟨l, -, -, hlmem, hlcard⟩ :=
    CFSG.GroupTheory.exists_list_closure_card E' hsq hcomm 4 (by rw [hE'c]; omega)
  obtain ⟨X, hX⟩ : ∃ X : Subgroup A45, X = Subgroup.closure {x | x ∈ l} := ⟨_, rfl⟩
  rw [← hX] at hlcard
  have hXE : X ≤ E' := by
    rw [hX, Subgroup.closure_le]
    intro x hx
    exact (hlmem x hx).1
  have hXc : Nat.card X = 16 := by rw [hlcard]; norm_num
  have hbound : ∀ {L «gens» : List P45} (hL : ListGroupFacts L «gens»), L.length = 16 →
      X = listSubgroup hL →
      (∀ c ∈ T0list (), c * c = 1 → (∀ x ∈ «gens», c * x = x * c) → c ∈ L) → False := by
    intro L «gens» hL hlen hXL hspec
    have h1 := le_listSubgroup_of_inv_centralizer hL hE'ea hg (hXL ▸ hXE) hspec
    have h2 := Subgroup.card_le_of_le h1
    rw [card_listSubgroup, hlen, hE'c] at h2
    omega
  obtain ⟨hs1, hs2, hs3, hs4⟩ := e16CentralizerCheck_spec qa45L1Facts.e16_centralizer
  rcases eq_four_of_le_sylowTwo (hE'ea.mono hXE) hXc (hXE.trans hg) with h | h | h | h
  · exact hbound qa45L1Facts.s_group (by rw [length_Slist]; norm_num)
      (h.trans sQA45_eq_listSubgroup) hs1
  · exact hbound qa45L1Facts.e3_group (by rw [length_E3list]; norm_num)
      (h.trans eUVQA45_eq_listSubgroup) hs2
  · exact hbound qa45L1Facts.e1_group (by rw [length_E1list]; norm_num)
      (h.trans eVQA45_eq_listSubgroup) hs3
  · exact hbound qa45L1Facts.e2_group (by rw [length_E2list]; norm_num)
      (h.trans eVAQA45_eq_listSubgroup) hs4

private theorem exists_meet_of_list {L «gens» : List P45}
    (hL : ListGroupFacts L «gens») (X' : Subgroup A45) (hX' : X' = listSubgroup hL)
    (hmeet : ∃ z ∈ L, z ≠ 1 ∧ z ∈ Slist () ∧ ∃ c ∈ elemsT QA45, c * z * c⁻¹ = u * t) :
    ∃ z : A45, z ∈ X' ∧ z ∈ sQA45 ∧ z ≠ 1 ∧ IsConj z (uA * tA) := by
  obtain ⟨z, hzL, hz1, hzS, c, hcA, hcz⟩ := hmeet
  have hzA : z ∈ QA45.originalSubgroup := hL.mem_A hzL
  have hcA' : c ∈ QA45.originalSubgroup := (mem_elemsT QA45 QA45_ok c).1 hcA
  refine ⟨⟨z, hzA⟩, ?_, (mem_sQA45_iff _).2 hzS, fun h => hz1 (congrArg Subtype.val h), ?_⟩
  · rw [hX']
    exact (mem_listSubgroup hL _).2 hzL
  · refine isConj_iff.2 ⟨⟨c, hcA'⟩, Subtype.ext ?_⟩
    simpa using hcz

theorem qa45_elemAbelian_pair_inf :
    ∀ P X Y : Subgroup A45, IsPGroup 2 P → X ≤ P → Y ≤ P →
      IsElemAbelian 2 X → Nat.card X = 16 → IsElemAbelian 2 Y → Nat.card Y = 16 →
      Y ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup →
      ∃ g ∈ X ⊓ Y, g ≠ 1 ∧ IsConj g (uA * tA) := by
  intro P X Y hP hXP hYP hX hXc hY hYc hYQ
  obtain ⟨g₀, hg₀⟩ := exists_map_conj_le_sylowTwo hP
  have hinj := (MulAut.conj g₀).injective
  have hX' := eq_four_of_le_sylowTwo (hX.map (MulAut.conj g₀).toMonoidHom)
    (by rw [Subgroup.card_map_of_injective hinj, hXc]) ((Subgroup.map_mono hXP).trans hg₀)
  have hY' := eq_four_of_le_sylowTwo (hY.map (MulAut.conj g₀).toMonoidHom)
    (by rw [Subgroup.card_map_of_injective hinj, hYc]) ((Subgroup.map_mono hYP).trans hg₀)
  have hQnorm : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two index_QP45
  have hY'Q : Y.map (MulAut.conj g₀).toMonoidHom ≤
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hQnorm.conj_mem y (hYQ hy) g₀
  have hY'S := eq_sQA45_of_le_Q hY' hY'Q
  obtain ⟨m1, m2, m3, m4⟩ := e16MeetCheck_spec qa45L1Facts.e16_meet_s
  obtain ⟨z, hzX, hzS, hz1, hzc⟩ : ∃ z : A45, z ∈ X.map (MulAut.conj g₀).toMonoidHom ∧
      z ∈ sQA45 ∧ z ≠ 1 ∧ IsConj z (uA * tA) := by
    rcases hX' with h | h | h | h
    · exact exists_meet_of_list qa45L1Facts.s_group _ (h.trans sQA45_eq_listSubgroup) m1
    · exact exists_meet_of_list qa45L1Facts.e3_group _ (h.trans eUVQA45_eq_listSubgroup) m2
    · exact exists_meet_of_list qa45L1Facts.e1_group _ (h.trans eVQA45_eq_listSubgroup) m3
    · exact exists_meet_of_list qa45L1Facts.e2_group _ (h.trans eVAQA45_eq_listSubgroup) m4
  obtain ⟨x, hxX, hxz⟩ := Subgroup.mem_map.1 hzX
  obtain ⟨y, hyY, hyz⟩ := Subgroup.mem_map.1 (by rw [hY'S]; exact hzS)
  have hxy : x = y := hinj (hxz.trans hyz.symm)
  refine ⟨x, Subgroup.mem_inf.2 ⟨hxX, hxy ▸ hyY⟩, ?_, ?_⟩
  · rintro rfl
    exact hz1 (by rw [← hxz]; exact map_one _)
  · exact (isConj_iff.2 ⟨g₀, (MulAut.conj_apply g₀ x).symm.trans hxz⟩).trans hzc


section NormalizerS


private theorem mem_Slist_of_mem_Sgens {x : P45} (hx : x ∈ Sgens) : x ∈ Slist () :=
  of_decide_eq_true (List.all_eq_true.1 qa45L1Facts.s_group.gens_mem x hx)

theorem mem_NSlist_iff (c : A45) :
    (c : P45) ∈ NSlist () ↔ c ∈ Subgroup.normalizer (sQA45 : Set A45) := by
  have hunpack : (c : P45) ∈ NSlist () ↔
      ((c : P45) ∈ elemsT QA45 ∧ ∀ x ∈ Sgens, (c : P45) * x * (c : P45)⁻¹ ∈ Slist ()) := by
    simp [NSlist, List.mem_filter, List.all_eq_true, tabList_eq]
  rw [hunpack]
  constructor
  · rintro ⟨-, h⟩
    show c ∈ Subgroup.normalizer ((Subgroup.closure {uA, a1A * a2A, b1A * b2A, tA} :
      Subgroup A45) : Set A45)
    refine CFSG.GroupTheory.mem_normalizer_closure fun x hx => ?_
    have hx' : (x : P45) ∈ Sgens := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [Sgens]
    have := h _ hx'
    exact (mem_sQA45_iff (c * x * c⁻¹)).2 (by simpa using this)
  · intro hc
    refine ⟨(mem_elemsT QA45 QA45_ok _).2 c.2, fun x hx => ?_⟩
    have hxL := mem_Slist_of_mem_Sgens hx
    have hxA : x ∈ QA45.originalSubgroup := qa45L1Facts.s_group.mem_A hxL
    have hxS : (⟨x, hxA⟩ : A45) ∈ sQA45 := (mem_sQA45_iff _).2 hxL
    have := (mem_sQA45_iff _).1 ((Subgroup.mem_normalizer_iff.1 hc _).1 hxS)
    simpa using this

private theorem nodup_NSlist : (NSlist ()).Nodup := by
  unfold NSlist
  exact (nodup_elemsT QA45 QA45_ok).filter _

theorem card_normalizer_sQA45 :
    Nat.card (Subgroup.normalizer (sQA45 : Set A45)) = 1920 := by
  have h := CFSG.Sporadic.Schreier.card_eq_length
    (fun c : A45 => c ∈ Subgroup.normalizer (sQA45 : Set A45)) (fun c => (c : P45))
    Subtype.val_injective (NSlist ()) nodup_NSlist (by
      intro b
      constructor
      · intro hb
        have hbA : b ∈ QA45.originalSubgroup :=
          (mem_elemsT QA45 QA45_ok b).1 (List.mem_filter.1 hb).1
        exact ⟨⟨b, hbA⟩, (mem_NSlist_iff ⟨b, hbA⟩).1 hb, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact (mem_NSlist_iff a).2 ha)
  rw [← qa45L1Facts.s_normalizer_card]
  exact h

theorem centralizer_sQA45 : Subgroup.centralizer (sQA45 : Set A45) = sQA45 := by
  apply le_antisymm
  · intro c hc
    rw [mem_sQA45_iff]
    refine centralizerSCheck_spec qa45L1Facts.s_centralizer _
      ((mem_elemsT QA45 QA45_ok _).2 c.2) fun x hx => ?_
    have hxL := mem_Slist_of_mem_Sgens hx
    have hxA : x ∈ QA45.originalSubgroup := qa45L1Facts.s_group.mem_A hxL
    have := Subgroup.mem_centralizer_iff.1 hc ⟨x, hxA⟩ ((mem_sQA45_iff _).2 hxL)
    have h2 := congrArg Subtype.val this
    simpa using h2.symm
  · have : IsMulCommutative sQA45 := isElemAbelian_sQA45.1
    exact Subgroup.le_centralizer _


theorem qa45_normalizer_sQA45 :
    Subgroup.centralizer (sQA45 : Set A45) = sQA45 ∧
    Nat.card (Subgroup.normalizer (sQA45 : Set A45)) = 1920 ∧
    (∃ (_ : (sQA45.subgroupOf (Subgroup.normalizer (sQA45 : Set A45))).Normal),
      Nonempty (↥(Subgroup.normalizer (sQA45 : Set A45)) ⧸
        sQA45.subgroupOf (Subgroup.normalizer (sQA45 : Set A45)) ≃* Equiv.Perm (Fin 5))) ∧
    (∀ s ∈ sQA45, s ≠ 1 → (∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), g * tA * g⁻¹ = s) ∨
      ∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), g * (uA * tA) * g⁻¹ = s) ∧
    (¬ ∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), g * tA * g⁻¹ = uA * tA) := by
  obtain ⟨ho1, ho2, ho3, ho4⟩ := sOrbitCheck_spec qa45L1Facts.s_orbits
  have horb : ∀ (a x : A45), (x : P45) ∈ conjOrbit (NSlist ()) (a : P45) ↔
      ∃ c ∈ Subgroup.normalizer (sQA45 : Set A45), c * a * c⁻¹ = x := by
    intro a x
    rw [mem_conjOrbit]
    constructor
    · rintro ⟨c, hc, hcx⟩
      have hcA : c ∈ QA45.originalSubgroup :=
        (mem_elemsT QA45 QA45_ok c).1 (List.mem_filter.1 hc).1
      refine ⟨⟨c, hcA⟩, (mem_NSlist_iff ⟨c, hcA⟩).1 hc, Subtype.ext ?_⟩
      simpa using hcx
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, (mem_NSlist_iff c).2 hc, by simp⟩
  have hot : ∀ x : A45, (x : P45) ∈ conjOrbit (NSlist ()) t ↔
      ∃ c ∈ Subgroup.normalizer (sQA45 : Set A45), c * tA * c⁻¹ = x := fun x => horb tA x
  have hou : ∀ x : A45, (x : P45) ∈ conjOrbit (NSlist ()) (u * t) ↔
      ∃ c ∈ Subgroup.normalizer (sQA45 : Set A45), c * (uA * tA) * c⁻¹ = x := fun x =>
    horb (uA * tA) x
  have hotA : ∀ b ∈ conjOrbit (NSlist ()) t, b ∈ QA45.originalSubgroup := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := mem_conjOrbit.1 hb
    have hcA : c ∈ QA45.originalSubgroup :=
      (mem_elemsT QA45 QA45_ok c).1 (List.mem_filter.1 hc).1
    exact QA45.originalSubgroup.mul_mem (QA45.originalSubgroup.mul_mem hcA t_mem_A)
      (QA45.originalSubgroup.inv_mem hcA)
  have hnd : (conjOrbit (NSlist ()) t).Nodup := List.nodup_dedup _
  generalize conjOrbit (NSlist ()) t = ot at ho1 ho2 ho3 ho4 hot hotA hnd
  generalize conjOrbit (NSlist ()) (u * t) = ou at ho3 hou
  have htS : tA ∈ sQA45 := Subgroup.subset_closure (by simp)
  have hcommS : ∀ a ∈ sQA45, ∀ b ∈ sQA45, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.1 isElemAbelian_sQA45.1 ⟨a, ha⟩ ⟨b, hb⟩)
  let O : Set A45 := {x | (x : P45) ∈ ot}
  have hO : ∀ n ∈ Subgroup.normalizer (sQA45 : Set A45), ∀ x ∈ O,
      n * x * n⁻¹ ∈ O := by
    intro n hn x hx
    obtain ⟨c, hc, rfl⟩ := (hot x).1 hx
    exact (hot _).2 ⟨n * c, mul_mem hn hc, CFSG.GroupTheory.conj_mul_conj n c tA⟩
  have hcard : Nat.card O = 5 := by
    have h := CFSG.Sporadic.Schreier.card_eq_length
      (fun x : A45 => (x : P45) ∈ ot) (fun x => (x : P45)) Subtype.val_injective ot hnd (by
        intro b
        constructor
        · intro hb
          exact ⟨⟨b, hotA b hb⟩, hb, rfl⟩
        · rintro ⟨a, ha, rfl⟩
          exact ha)
    exact h.trans ho1
  have hker : ∀ n ∈ Subgroup.normalizer (sQA45 : Set A45),
      (∀ x ∈ O, n * x * n⁻¹ = x) ↔ n ∈ sQA45 := by
    intro n hn
    constructor
    · intro h
      refine (mem_sQA45_iff n).2 (ho2 (n : P45) ((mem_elemsT QA45 QA45_ok _).2 n.2) ?_)
      intro o ho
      have h2 := h ⟨o, hotA o ho⟩ ho
      have h3 : n * ⟨o, hotA o ho⟩ = ⟨o, hotA o ho⟩ * n := by rwa [mul_inv_eq_iff_eq_mul] at h2
      simpa using congrArg Subtype.val h3
    · intro hnS x hx
      obtain ⟨c, hc, rfl⟩ := (hot x).1 hx
      have hxS : c * tA * c⁻¹ ∈ sQA45 := (Subgroup.mem_normalizer_iff.1 hc tA).1 htS
      rw [mul_inv_eq_iff_eq_mul]
      exact hcommS _ hnS _ hxS
  have hord : Nat.card (Subgroup.normalizer (sQA45 : Set A45)) =
      Nat.card sQA45 * Nat.factorial 5 := by
    rw [card_normalizer_sQA45, card_sQA45]
    norm_num [Nat.factorial]
  refine ⟨centralizer_sQA45, card_normalizer_sQA45,
    CFSG.GroupTheory.exists_quotient_mulEquiv_perm _ sQA45 Subgroup.le_normalizer O 5 hO hcard
      hker hord, ?_, ?_⟩
  · intro s hs hs1
    have hsL : (s : P45) ∈ Slist () := (mem_sQA45_iff s).1 hs
    have hs1' : (s : P45) ≠ 1 := fun h => hs1 (Subtype.ext h)
    rcases ho3 _ hsL hs1' with h | h
    · exact Or.inl (by simpa using (hot s).1 h)
    · exact Or.inr (by simpa using (hou s).1 h)
  · rintro ⟨g, hg, hgt⟩
    apply ho4
    have := (hot (uA * tA)).2 ⟨g, hg, hgt⟩
    simpa using this

end NormalizerS

end CFSG.RankThree.GF2n.Parrott
