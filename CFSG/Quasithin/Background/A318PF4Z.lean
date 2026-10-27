module

public import CFSG.Quasithin.Background.A318PRW
public import CFSG.Quasithin.Background.A318PCRank
public import CFSG.LieType.Ree.ReeHolds
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem eltElement_neg_simpleRoot
    {τ : Tag} {K : Type} [Field K] (j : Fin τ.rank) (c : K) :
    (rootOperatorFamily τ).eltElement (-simpleRoot τ j) c = yElement j c :=
  Subtype.ext ((rootOperatorFamily τ).eltUnit_neg_simple j c)

section Dual

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {n : ℕ}

@[expose] def dualWitness
    (W : RootWitness t.tag n) : RootWitness t.tag n where
  word i := (W.word i).map t.perm
  simple i := t.perm (W.simple i)

variable (a : ℕ)

theorem reeAut_elemA
    (W : RootWitness t.tag n) (i : Fin n) :
    t.reeAut K a (W.elemA K i) = (dualWitness W).elemA K i := by
  simp only [RootWitness.elemA, dualWitness, map_mul, map_inv, reeAut_nrep, weylPerm_wordProd,
    eltElement_simpleRoot, reeAut_xElement, one_pow]

theorem reeAut_elemB
    (W : RootWitness t.tag n) (i : Fin n) :
    t.reeAut K a (W.elemB K i) = (dualWitness W).elemB K i := by
  simp only [RootWitness.elemB, dualWitness, map_mul, map_inv, reeAut_nrep, weylPerm_wordProd,
    eltElement_neg_simpleRoot, reeAut_yElement, one_pow]

theorem reeAut_elemZ
    (W : RootWitness t.tag n) (i : Fin n) :
    t.reeAut K a (W.elemZ K i) = (dualWitness W).elemZ K i := by
  rw [RootWitness.elemZ_eq, RootWitness.elemZ_eq, map_mul, reeAut_elemA, reeAut_elemB]

end Dual

section Entrywise

variable {τ : Tag} {K : Type} [Field K] {n : ℕ}

theorem entrywise_elemZ
    (σ : K ≃+* K) (W : RootWitness τ n) (i : Fin n) :
    Units.map (entrywiseHom σ.toRingHom) ((W.elemZ K i : adjointGroup τ K) : ModGL τ K) =
      ((W.elemZ K i : adjointGroup τ K) : ModGL τ K) := by
  have hN : Units.map (entrywiseHom σ.toRingHom)
      ((nrep τ K ((coxeterSystem τ).wordProd (W.word i)) : adjointGroup τ K) : ModGL τ K) =
      ((nrep τ K ((coxeterSystem τ).wordProd (W.word i)) : adjointGroup τ K) : ModGL τ K) :=
    entrywise_canonicalRep σ _
  have hX : Units.map (entrywiseHom σ.toRingHom)
      (((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1 :
        adjointGroup τ K) : ModGL τ K) =
      (((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1 :
        adjointGroup τ K) : ModGL τ K) := by
    rw [eltElement_simpleRoot]
    exact (units_map_entrywiseHom_xUnit σ.toRingHom (W.simple i) 1).trans (by rw [map_one]; rfl)
  have hY : Units.map (entrywiseHom σ.toRingHom)
      (((rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) 1 :
        adjointGroup τ K) : ModGL τ K) =
      (((rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) 1 :
        adjointGroup τ K) : ModGL τ K) := by
    rw [eltElement_neg_simpleRoot]
    exact (units_map_entrywiseHom_yUnit σ.toRingHom (W.simple i) 1).trans (by rw [map_one]; rfl)
  simp only [RootWitness.elemZ, rankOneZ, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
    hN, hX, hY]

end Entrywise

section Abstract

variable {G : Type*} [Group G]

theorem exists_nine_of_pairs (Za Za' Zb Zb' Aa Ab : G)
    (h3a : Za ^ 3 = 1) (h3a' : Za' ^ 3 = 1) (h3b : Zb ^ 3 = 1) (h3b' : Zb' ^ 3 = 1)
    (hna : ¬ Commute Za Aa) (hna2 : ¬ Commute (Za ^ 2) Aa)
    (hnb : ¬ Commute Zb Ab) (hnb2 : ¬ Commute (Zb ^ 2) Ab)
    (c_aa' : Commute Za Za') (c_bb' : Commute Zb Zb') (c_ab : Commute Za Zb)
    (c_ab' : Commute Za Zb') (c_a'b : Commute Za' Zb) (c_a'b' : Commute Za' Zb')
    (cA_a' : Commute Za' Aa) (cA_b : Commute Zb Aa) (cA_b' : Commute Zb' Aa)
    (cB_a : Commute Za Ab) (cB_a' : Commute Za' Ab) (cB_b' : Commute Zb' Ab)
    {H : Subgroup G} (hH1 : Za * Za' ∈ H) (hH2 : Zb * Zb' ∈ H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  have hsq : ∀ (z z' : G), Commute z z' → (z * z') ^ 2 = z ^ 2 * z' ^ 2 := fun z z' h =>
    h.mul_pow 2
  have hcu : ∀ (z z' : G), Commute z z' → z ^ 3 = 1 → z' ^ 3 = 1 → (z * z') ^ 3 = 1 :=
    fun z z' h h1 h2 => by rw [h.mul_pow, h1, h2, mul_one]
  have hnc : ∀ (z z' A : G), Commute z z' → Commute z' A → ¬ Commute z A →
      ¬ Commute (z * z') A := fun z z' A hzz hz'A hn hc => hn (by
    have h1 : Commute ((z * z') * z'⁻¹) A := hc.mul_left (hz'A.inv_left)
    rwa [mul_inv_cancel_right] at h1)
  have hnc2 : ∀ (z z' A : G), Commute z z' → Commute z' A → ¬ Commute (z ^ 2) A →
      ¬ Commute ((z * z') ^ 2) A := fun z z' A hzz hz'A hn hc => hn (by
    rw [hsq z z' hzz] at hc
    have h1 : Commute (z ^ 2 * z' ^ 2 * (z' ^ 2)⁻¹) A := hc.mul_left ((hz'A.pow_left 2).inv_left)
    rwa [mul_inv_cancel_right] at h1)
  refine exists_elemAbelian_three (n := 2) ![Za * Za', Zb * Zb'] ![Aa, Ab] ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hcu _ _ c_aa' h3a h3a'
    · exact hcu _ _ c_bb' h3b h3b'
  · intro i
    fin_cases i
    · exact hnc _ _ _ c_aa' cA_a' hna
    · exact hnc _ _ _ c_bb' cB_b' hnb
  · intro i
    fin_cases i
    · exact hnc2 _ _ _ c_aa' cA_a' hna2
    · exact hnc2 _ _ _ c_bb' cB_b' hnb2
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact cA_b.mul_left cA_b'
    · exact cB_a.mul_left cB_a'
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact (c_ab.mul_right c_ab').mul_left (c_a'b.mul_right c_a'b')
    · exact ((c_ab.mul_right c_ab').mul_left (c_a'b.mul_right c_a'b')).symm
    · exact absurd rfl hij
  · intro i
    fin_cases i
    · exact hH1
    · exact hH2

end Abstract

section F4Frame

@[expose] def f4Long : RootWitness ReeTag.F4.tag 2 where
  word := ![([] : List (Fin 4)), ([2, 3, 1, 2, 1] : List (Fin 4))]
  simple := ![(0 : Fin 4), (0 : Fin 4)]

@[expose] def f4W13 : RootWitness ReeTag.F4.tag 2 where
  word := ![([] : List (Fin 4)), ([] : List (Fin 4))]
  simple := ![(0 : Fin 4), (3 : Fin 4)]

@[expose] def f4W14 : RootWitness ReeTag.F4.tag 2 where
  word := ![([] : List (Fin 4)), ([1, 0, 2, 1, 2] : List (Fin 4))]
  simple := ![(0 : Fin 4), (3 : Fin 4)]

@[expose] def f4W23 : RootWitness ReeTag.F4.tag 2 where
  word := ![([2, 3, 1, 2, 1] : List (Fin 4)), ([] : List (Fin 4))]
  simple := ![(0 : Fin 4), (3 : Fin 4)]

@[expose] def f4W24 : RootWitness ReeTag.F4.tag 2 where
  word := ![([2, 3, 1, 2, 1] : List (Fin 4)), ([1, 0, 2, 1, 2] : List (Fin 4))]
  simple := ![(0 : Fin 4), (3 : Fin 4)]

theorem f4Long_check : f4Long.check = true := by decide +kernel
theorem f4Long_orthoCheck : f4Long.orthoCheck = true := by decide +kernel
theorem f4W13_check : f4W13.check = true := by decide +kernel
theorem f4W13_orthoCheck : f4W13.orthoCheck = true := by decide +kernel
theorem f4W14_check : f4W14.check = true := by decide +kernel
theorem f4W14_orthoCheck : f4W14.orthoCheck = true := by decide +kernel
theorem f4W23_check : f4W23.check = true := by decide +kernel
theorem f4W23_orthoCheck : f4W23.orthoCheck = true := by decide +kernel
theorem f4W24_check : f4W24.check = true := by decide +kernel
theorem f4W24_orthoCheck : f4W24.orthoCheck = true := by decide +kernel

end F4Frame

section Nine

variable {K : Type} [Field K]

@[expose] def entrywiseFixed (τ : Tag) (σ : K ≃+* K) : Subgroup (adjointGroup τ K) where
  carrier := {g | Units.map (entrywiseHom σ.toRingHom) (g : ModGL τ K) = g}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, map_mul] at hx hy ⊢
    rw [hx, hy]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, OneMemClass.coe_one, map_one]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_inv, map_inv] at hx ⊢
    rw [hx]

theorem mem_entrywiseFixed {τ : Tag} {σ : K ≃+* K} {g : adjointGroup τ K} :
    g ∈ entrywiseFixed τ σ ↔ Units.map (entrywiseHom σ.toRingHom) (g : ModGL τ K) = g :=
  Iff.rfl

theorem rankOneZ_facts_f4
    [CharP K 2] (j : Fin ReeTag.F4.tag.rank) :
    rankOneZ (τ := ReeTag.F4.tag) (K := K) j ^ 3 = 1 ∧
      ¬ Commute (rankOneZ (K := K) j) ((rootOperatorFamily ReeTag.F4.tag).eltElement
        (simpleRoot ReeTag.F4.tag j) 1) ∧
      ¬ Commute (rankOneZ (K := K) j ^ 2) ((rootOperatorFamily ReeTag.F4.tag).eltElement
        (simpleRoot ReeTag.F4.tag j) 1) := by
  have h2 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharP.cast_eq_zero K 2
  fin_cases j
  · exact rankOneZ_facts (k := (1 : Fin 4)) (by decide) h2
  · exact rankOneZ_facts (k := (0 : Fin 4)) (by decide) h2
  · exact rankOneZ_facts (k := (3 : Fin 4)) (by decide) h2
  · exact rankOneZ_facts (k := (2 : Fin 4)) (by decide) h2

variable [Finite K] [CharP K ReeTag.F4.prime]

omit [Finite K] in
theorem f4_pair_facts
    (W : RootWitness ReeTag.F4.tag 2) (hW : W.check = true)
    (hO : W.orthoCheck = true) :
    (∀ i, W.elemZ K i ^ 3 = 1 ∧ ¬ Commute (W.elemZ K i) (W.elemA K i) ∧
      ¬ Commute (W.elemZ K i ^ 2) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (W.elemZ K j) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (W.elemZ K i) (W.elemZ K j)) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨h1, h2, h3, -⟩ := charTwo_facts_of_rankOne W hW hO (K := K)
    (fun i => rankOneZ_facts_f4 _)
  exact ⟨h1, h2, h3⟩

theorem exists_nine_f4
    (a : ℕ) (σ : K ≃+* K) :
    ∃ E : Subgroup (adjointGroup ReeTag.F4.tag K), Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
      (∀ y ∈ E, ReeTag.F4.reeAut K a y = y) ∧
      ∀ y ∈ E, Units.map (entrywiseHom σ.toRingHom) (y : ModGL ReeTag.F4.tag K) = y := by
  obtain ⟨hn12, hZA12, hZZ12⟩ := f4_pair_facts (K := K) f4Long f4Long_check f4Long_orthoCheck
  obtain ⟨hn13, hZA13, hZZ13⟩ := f4_pair_facts (K := K) f4W13 f4W13_check f4W13_orthoCheck
  obtain ⟨hn14, hZA14, hZZ14⟩ := f4_pair_facts (K := K) f4W14 f4W14_check f4W14_orthoCheck
  obtain ⟨hn23, hZA23, hZZ23⟩ := f4_pair_facts (K := K) f4W23 f4W23_check f4W23_orthoCheck
  obtain ⟨hn24, hZA24, hZZ24⟩ := f4_pair_facts (K := K) f4W24 f4W24_check f4W24_orthoCheck
  set Za := f4Long.elemZ K 0 with hZa
  set Zb := f4Long.elemZ K 1 with hZb
  set Za' := f4W13.elemZ K 1 with hZa'
  set Zb' := f4W14.elemZ K 1 with hZb'
  set Aa := f4Long.elemA K 0 with hAa
  set Ab := f4Long.elemA K 1 with hAb
  have hFa : ReeTag.F4.reeAut K a Za = Za' := by
    rw [hZa, reeAut_elemZ]; rfl
  have hFb : ReeTag.F4.reeAut K a Zb = Zb' := by
    rw [hZb, reeAut_elemZ]; rfl
  have hFa' : ReeTag.F4.reeAut K a Za' = Za := by
    rw [hZa', reeAut_elemZ]; rfl
  have hFb' : ReeTag.F4.reeAut K a Zb' = Zb := by
    rw [hZb', reeAut_elemZ]; rfl
  have c_ab : Commute Za Zb := hZZ12 0 1 (by decide)
  have c_aa' : Commute Za Za' := hZZ13 0 1 (by decide)
  have c_ab' : Commute Za Zb' := hZZ14 0 1 (by decide)
  have c_a'b : Commute Za' Zb := (hZZ23 0 1 (by decide)).symm
  have c_bb' : Commute Zb Zb' := hZZ24 0 1 (by decide)
  have c_a'b' : Commute Za' Zb' := by
    have := c_ab.map (ReeTag.F4.reeAut K a)
    rwa [hFa, hFb] at this
  obtain ⟨E, hEH, hEel, hEcard⟩ := exists_nine_of_pairs Za Za' Zb Zb' Aa Ab
    (hn12 0).1 (hn13 1).1 (hn12 1).1 (hn14 1).1 (hn12 0).2.1 (hn12 0).2.2 (hn12 1).2.1
    (hn12 1).2.2 c_aa' c_bb' c_ab c_ab' c_a'b c_a'b'
    (hZA13 0 1 (by decide)) (hZA12 0 1 (by decide)) (hZA14 0 1 (by decide))
    (hZA12 1 0 (by decide)) (hZA23 0 1 (by decide)) (hZA24 0 1 (by decide))
    (H := reeFixed ReeTag.F4 K a ⊓ entrywiseFixed ReeTag.F4.tag σ)
    (by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_reeFixed, map_mul, hFa, hFa']
        exact c_aa'.symm.eq
      · rw [mem_entrywiseFixed, Subgroup.coe_mul, map_mul]
        exact congrArg₂ (· * ·) (entrywise_elemZ σ f4Long 0) (entrywise_elemZ σ f4W13 1))
    (by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_reeFixed, map_mul, hFb, hFb']
        exact c_bb'.symm.eq
      · rw [mem_entrywiseFixed, Subgroup.coe_mul, map_mul]
        exact congrArg₂ (· * ·) (entrywise_elemZ σ f4Long 1) (entrywise_elemZ σ f4W14 1))
  refine ⟨E, by rw [hEcard]; norm_num, hEel, fun y hy => (Subgroup.mem_inf.1 (hEH hy)).1,
    fun y hy => (Subgroup.mem_inf.1 (hEH hy)).2⟩

end Nine


end A318P

end CFSG.Quasithin
