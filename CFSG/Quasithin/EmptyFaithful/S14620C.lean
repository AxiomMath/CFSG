module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Concrete

private abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

private def sl3P0 : Subgroup SL3 where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0}
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  one_mem' := by decide +kernel
  inv_mem' := by
    intro a ha
    revert a
    decide +kernel

private def sl3E1 : Subgroup SL3 where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0}
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  one_mem' := by decide +kernel
  inv_mem' := by
    intro a ha
    revert a
    decide +kernel

private def sl3E2 : Subgroup SL3 where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0}
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  one_mem' := by decide +kernel
  inv_mem' := by
    intro a ha
    revert a
    decide +kernel

private instance : DecidablePred (· ∈ sl3P0) := fun A =>
  inferInstanceAs (Decidable ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0))

private instance : DecidablePred (· ∈ sl3E1) := fun A =>
  inferInstanceAs (Decidable ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0))

private instance : DecidablePred (· ∈ sl3E2) := fun A =>
  inferInstanceAs (Decidable ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0))

set_option maxRecDepth 100000 in
private theorem card_sl3P0 : Nat.card sl3P0 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
private theorem card_sl3E1 : Nat.card sl3E1 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
private theorem card_sl3E2 : Nat.card sl3E2 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
private theorem card_sl3 : Nat.card SL3 = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
private theorem sl3P0_le_E1 : sl3P0 ≤ sl3E1 := by
  intro A hA
  revert A
  decide +kernel

set_option maxRecDepth 100000 in
private theorem sl3P0_le_E2 : sl3P0 ≤ sl3E2 := by
  intro A hA
  revert A
  decide +kernel

set_option maxRecDepth 100000 in
private theorem not_sl3E2_le_E1 : ¬ sl3E2 ≤ sl3E1 := by
  intro h
  have h' : ∀ A : SL3, A ∈ sl3E2 → A ∈ sl3E1 := fun A hA => h hA
  revert h'
  decide +kernel

set_option maxRecDepth 100000 in
private theorem sl3P0_selfNormalizing :
    ∀ x : SL3, (∀ y ∈ sl3P0, x * y * x⁻¹ ∈ sl3P0) → x ∈ sl3P0 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem sl3P0_pow_four : ∀ x ∈ sl3P0, x ^ 4 = 1 := by
  decide +kernel

private theorem isSylowTwoOf_sl3P0 : IsSylowTwoOf sl3P0 ⊤ := by
  refine ⟨le_top, fun g => ⟨2, Subtype.ext (by simpa using sl3P0_pow_four g.1 g.2)⟩, ?_⟩
  have h1 : (sl3P0.subgroupOf ⊤).index = sl3P0.index := Subgroup.relIndex_top_right sl3P0
  have h2 := Subgroup.card_mul_index sl3P0
  rw [card_sl3P0, card_sl3] at h2
  intro hdvd
  rw [h1] at hdvd
  omega

private theorem isSolvable_sl3E1 : Group.IsSolvable ↥sl3E1 := by
  have : Finite ↥sl3E1 := inferInstance
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (by rw [card_sl3E1]; norm_num [Nat.primeFactors])

private theorem isSolvable_sl3E2 : Group.IsSolvable ↥sl3E2 := by
  have : Finite ↥sl3E2 := inferInstance
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (by rw [card_sl3E2]; norm_num [Nat.primeFactors])

private theorem sl3E1_sup_E2 : sl3E1 ⊔ sl3E2 = ⊤ := by
  have h1 : Nat.card ↥sl3E1 ∣ Nat.card ↥(sl3E1 ⊔ sl3E2) := Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card ↥(sl3E1 ⊔ sl3E2) ∣ Nat.card SL3 := Subgroup.card_subgroup_dvd_card _
  rw [card_sl3E1] at h1
  rw [card_sl3] at h2
  have hdiv : ∀ n ∈ Nat.divisors 168, 24 ∣ n → n = 24 ∨ n = 168 := by decide
  have hn := hdiv _ (Nat.mem_divisors.mpr ⟨h2, by norm_num⟩) h1
  rcases hn with hn | hn
  · exfalso
    have heq : sl3E1 = sl3E1 ⊔ sl3E2 :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hn, card_sl3E1])
    exact not_sl3E2_le_E1 (heq ▸ le_sup_right)
  · exact Subgroup.eq_top_of_card_eq _ (by rw [hn, card_sl3])

end Concrete

section Transfer

private theorem isSolvable_map_mulEquiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) (F : Subgroup A)
    (hF : Group.IsSolvable ↥F) : Group.IsSolvable ↥(F.map f.toMonoidHom) :=
  Group.isSolvable_of_surjective (f := (f.subgroupMap F).toMonoidHom) (f.subgroupMap F).surjective

private theorem isSolvable_map_subtype {Y : Type*} [Group Y] (L : Subgroup Y) (F : Subgroup ↥L)
    (hF : Group.IsSolvable ↥F) : Group.IsSolvable ↥(F.map L.subtype) :=
  Group.isSolvable_of_surjective (f := L.subtype.subgroupMap F) (L.subtype.subgroupMap_surjective F)

variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
private theorem l32_type (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) {P : Subgroup L}
    (hP : IsSylowTwoOf P ⊤) :
    (∀ x : L, (∀ y ∈ P, x * y * x⁻¹ ∈ P) → x ∈ P) ∧
      ∃ E₁ E₂ : Subgroup L, P ≤ E₁ ∧ P ≤ E₂ ∧ Group.IsSolvable ↥E₁ ∧ Group.IsSolvable ↥E₂ ∧
        E₁ ⊔ E₂ = ⊤ := by
  set Pa : Subgroup SL3 := P.map e.toMonoidHom with hPa
  have hPaS : IsSylowTwoOf Pa ⊤ := by
    refine ⟨le_top, hP.2.1.map e.toMonoidHom, ?_⟩
    have h1 : (Pa.subgroupOf ⊤).index = Pa.relIndex ⊤ := rfl
    have htop : (⊤ : Subgroup L).map e.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e.surjective
    have h2 : Pa.relIndex ⊤ = P.relIndex ⊤ := by
      have := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) P ⊤ e.injective
      rwa [htop] at this
    rw [h1, h2]
    exact hP.2.2
  obtain ⟨h, -, hh⟩ := CFSG.Quasithin.A4.exists_conj_of_isSylowTwoOf isSylowTwoOf_sl3P0 hPaS
  have hmem : ∀ x : L, x ∈ P → h⁻¹ * e x * h ∈ sl3P0 := fun x hx =>
    (hh _).mp (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hcj1 : Group.IsSolvable ↥(conjSub h sl3E1) :=
    isSolvable_map_mulEquiv (MulAut.conj h) sl3E1 isSolvable_sl3E1
  have hcj2 : Group.IsSolvable ↥(conjSub h sl3E2) :=
    isSolvable_map_mulEquiv (MulAut.conj h) sl3E2 isSolvable_sl3E2
  have hcjtop : conjSub h sl3E1 ⊔ conjSub h sl3E2 = ⊤ := by
    unfold conjSub
    rw [← Subgroup.map_sup, sl3E1_sup_E2]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  refine ⟨?_, (conjSub h sl3E1).map e.symm.toMonoidHom, (conjSub h sl3E2).map e.symm.toMonoidHom,
    ?_, ?_, isSolvable_map_mulEquiv e.symm _ hcj1, isSolvable_map_mulEquiv e.symm _ hcj2, ?_⟩
  · intro x hx
    have hx' : ∀ y ∈ sl3P0, (h⁻¹ * e x * h) * y * (h⁻¹ * e x * h)⁻¹ ∈ sl3P0 := by
      intro y hy
      have hyPa : h * y * h⁻¹ ∈ Pa := (hh _).mpr (by simpa [mul_assoc] using hy)
      obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hyPa
      have hxp : x * p * x⁻¹ ∈ P := hx p hp
      have hmem2 : e x * (h * y * h⁻¹) * (e x)⁻¹ ∈ Pa := by
        refine Subgroup.mem_map.mpr ⟨x * p * x⁻¹, hxp, ?_⟩
        have hpy' : e p = h * y * h⁻¹ := hpy
        show e (x * p * x⁻¹) = _
        rw [map_mul, map_mul, map_inv, hpy']
      have h3 := (hh _).mp hmem2
      have e1 : h⁻¹ * (e x * (h * y * h⁻¹) * (e x)⁻¹) * h =
          (h⁻¹ * e x * h) * y * (h⁻¹ * e x * h)⁻¹ := by group
      rwa [e1] at h3
    have hz := sl3P0_selfNormalizing _ hx'
    have hxPa : e x ∈ Pa := (hh _).mpr hz
    obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hxPa
    have hpx' : p = x := e.injective hpx
    rwa [← hpx']
  · intro x hxP
    rw [Subgroup.mem_map_equiv]
    exact mem_conjSub.mpr (sl3P0_le_E1 (hmem x hxP))
  · intro x hxP
    rw [Subgroup.mem_map_equiv]
    exact mem_conjSub.mpr (sl3P0_le_E2 (hmem x hxP))
  · rw [← Subgroup.map_sup, hcjtop]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective

variable {Y : Type*} [Group Y]

theorem exists_solvable_overgroups_of_mulEquiv_sl3 {L P : Subgroup Y}
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hP : IsSylowTwoOf P L) :
    (∀ x ∈ L, (∀ y ∈ P, x * y * x⁻¹ ∈ P) → x ∈ P) ∧
      ∃ E₁ E₂ : Subgroup Y, P ≤ E₁ ∧ P ≤ E₂ ∧ E₁ ≤ L ∧ E₂ ≤ L ∧ Group.IsSolvable ↥E₁ ∧
        Group.IsSolvable ↥E₂ ∧ E₁ ⊔ E₂ = L := by
  have hPs : IsSylowTwoOf (P.subgroupOf L) ⊤ := by
    refine ⟨le_top, CFSG.Quasithin.A4.isPGroup_subgroupOf_of_le hP.1 hP.2.1, ?_⟩
    have h1 : ((P.subgroupOf L).subgroupOf ⊤).index = (P.subgroupOf L).relIndex ⊤ := rfl
    rw [h1, Subgroup.relIndex_top_right]
    exact hP.2.2
  obtain ⟨hnorm, E₁, E₂, hP1, hP2, hs1, hs2, hsup⟩ := l32_type e hPs
  refine ⟨?_, E₁.map L.subtype, E₂.map L.subtype, ?_, ?_, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, isSolvable_map_subtype L E₁ hs1, isSolvable_map_subtype L E₂ hs2, ?_⟩
  · intro x hx hxy
    have := hnorm ⟨x, hx⟩ fun y hy => by
      have hy' : (y : Y) ∈ P := hy
      exact hxy y hy'
    exact this
  · intro y hy
    exact ⟨⟨y, hP.1 hy⟩, hP1 (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · intro y hy
    exact ⟨⟨y, hP.1 hy⟩, hP2 (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]

end Transfer

end CFSG.Quasithin
