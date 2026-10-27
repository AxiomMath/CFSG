module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11Data
import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open Equiv
open CFSG.RankThree.PartTwo.Sec4.Ronan148R (a11A0 a11P0 a11c1 a11c2 a11c3)

private theorem factorization_card_a11 :
    (Nat.card (alternatingGroup (Fin 11))).factorization 3 = 4 := by
  rw [show Nat.card (alternatingGroup (Fin 11)) = 19958400 from
    CFSG.RankThree.PartTwo.Sec4.Ronan148R.card_a11]
  exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
    (show (19958400 : ℕ) = 3 ^ 4 * 246400 by norm_num) (by norm_num)

private theorem exists_le_map_conj_a11P0 {Q : Subgroup (alternatingGroup (Fin 11))}
    (hQ : IsPGroup 3 Q) :
    ∃ g : alternatingGroup (Fin 11), Q ≤ a11P0.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (by rw [CFSG.RankThree.PartTwo.Sec4.Ronan148R.a11P0_spec.1, factorization_card_a11]; norm_num)
    hQ

private theorem eq_map_conj_a11A0_of_le {E : Subgroup (alternatingGroup (Fin 11))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {g : alternatingGroup (Fin 11)}
    (hEg : E ≤ a11P0.map (MulAut.conj g).toMonoidHom) :
    E = a11A0.map (MulAut.conj g).toMonoidHom := by
  have hE' : E.map (MulAut.conj g⁻¹).toMonoidHom = a11A0 :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148R.eq_a11A0_of_le (hE.map _)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE27])
      (CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hEg)
  rw [← hE', CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_map_conj_inv]

theorem exists_conj_eq_a11A0 {A : Subgroup (alternatingGroup (Fin 11))}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) :
    ∃ g : alternatingGroup (Fin 11), A = a11A0.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_le_map_conj_a11P0 hA.isPGroup
  exact ⟨g, eq_map_conj_a11A0_of_le hA hA27 hg⟩

theorem existsUnique_elemAbelian_card_27_of_card_eq_81_a11
    {Q : Subgroup (alternatingGroup (Fin 11))} (hQ : Nat.card Q = 81) :
    ∃! E : Subgroup (alternatingGroup (Fin 11)),
      E ≤ Q ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := 4) (by rw [hQ]; norm_num)
  obtain ⟨g, hg⟩ := exists_le_map_conj_a11P0 hQ3
  have hQeq : Q = a11P0.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hg (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        CFSG.RankThree.PartTwo.Sec4.Ronan148R.a11P0_spec.1, hQ])
  obtain ⟨hA0, hA027⟩ := CFSG.RankThree.PartTwo.Sec4.Ronan148R.a11A0_e27
  refine ⟨a11A0.map (MulAut.conj g).toMonoidHom, ⟨?_, hA0.map _, ?_⟩, ?_⟩
  · rw [hQeq]
    exact Subgroup.map_mono le_sup_left
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA027]
  · rintro E ⟨hEQ, hE, hE27⟩
    exact eq_map_conj_a11A0_of_le hE hE27 (hEQ.trans hQeq.le)

private theorem a11c_mem_a11A0 :
    a11c1 ∈ a11A0 ∧ a11c1 * a11c2 ∈ a11A0 ∧ a11c1 * a11c2 * a11c3 ∈ a11A0 := by
  have h1 : a11c1 ∈ a11A0 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers a11c1))
  have h2 : a11c2 ∈ a11A0 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers a11c2))
  have h3 : a11c3 ∈ a11A0 := Subgroup.mem_sup_right (Subgroup.mem_zpowers a11c3)
  exact ⟨h1, mul_mem h1 h2, mul_mem (mul_mem h1 h2) h3⟩

theorem exists_conj_mem_a11A0_of_orderOf_eq_three {x : alternatingGroup (Fin 11)}
    (hx : orderOf x = 3) : ∃ g : alternatingGroup (Fin 11), g * x * g⁻¹ ∈ a11A0 := by
  have hx3 : (x : Perm (Fin 11)) ^ 3 = 1 := by
    have h := congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
    simpa using h
  have hx1 : (x : Perm (Fin 11)) ≠ 1 := by
    intro h
    rw [show x = 1 from Subtype.ext h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have key : ∀ r : alternatingGroup (Fin 11), r ∈ a11A0 →
      (x : Perm (Fin 11)).cycleType = (r : Perm (Fin 11)).cycleType →
      ∃ g : alternatingGroup (Fin 11), g * x * g⁻¹ ∈ a11A0 := by
    intro r hr hcyc
    obtain ⟨g, hg1, hg⟩ :=
      CFSG.Sporadic.Recognition.LyonsSims.exists_even_conj_of_cycleType_eq hx3 hcyc
    refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg1⟩, ?_⟩
    have hconj : (⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg1⟩ : alternatingGroup (Fin 11)) * x *
        (⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg1⟩ : alternatingGroup (Fin 11))⁻¹ = r :=
      Subtype.ext hg
    rw [hconj]
    exact hr
  obtain ⟨h1, h12, h123⟩ := a11c_mem_a11A0
  have e1 : (a11c1 : Perm (Fin 11)) = CFSG.Sporadic.Recognition.LyonsSims.x1p := by decide
  have e12 : ((a11c1 * a11c2 : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
      CFSG.Sporadic.Recognition.LyonsSims.y12p := by decide
  have e123 : ((a11c1 * a11c2 * a11c3 : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
      CFSG.Sporadic.Recognition.LyonsSims.u123p := by decide
  rcases CFSG.Sporadic.Recognition.LyonsSims.cycleType_of_pow_three hx3 hx1 with h | h | h
  · exact key a11c1 h1
      (h.trans (by rw [e1, CFSG.Sporadic.Recognition.LyonsSims.cycleType_x1p]))
  · exact key (a11c1 * a11c2) h12
      (h.trans (by rw [e12, CFSG.Sporadic.Recognition.LyonsSims.cycleType_y12p]))
  · exact key (a11c1 * a11c2 * a11c3) h123
      (h.trans (by rw [e123, CFSG.Sporadic.Recognition.LyonsSims.cycleType_u123p]))

theorem exists_conj_mem_of_elemAbelian_card_27_a11 {E : Subgroup (alternatingGroup (Fin 11))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    {x : alternatingGroup (Fin 11)} (hx : orderOf x = 3) :
    ∃ g : alternatingGroup (Fin 11), g * x * g⁻¹ ∈ E := by
  obtain ⟨h, rfl⟩ := exists_conj_eq_a11A0 hE hE27
  obtain ⟨g, hg⟩ := exists_conj_mem_a11A0_of_orderOf_eq_three hx
  refine ⟨h * g, Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hg, ?_⟩⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem existsUnique_elemAbelian_card_27_of_mulEquiv_a11 {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 11)) (P : Sylow 3 X) :
    ∃! A : Subgroup X, A ≤ P ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hP : Nat.card ((P : Subgroup X).map e.toMonoidHom) = 81 := by
    rw [Subgroup.card_map_of_injective e.injective, P.card_eq_multiplicity,
      Nat.card_congr e.toEquiv, factorization_card_a11]
    norm_num
  obtain ⟨E, ⟨hEP, hE, hE27⟩, hEu⟩ := existsUnique_elemAbelian_card_27_of_card_eq_81_a11 hP
  have hmap : (E.comap e.toMonoidHom).map e.toMonoidHom = E :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective E
  refine ⟨E.comap e.toMonoidHom, ⟨?_, hE.comap e.injective, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hEP hx)
    rw [← e.injective hyx]
    exact hy
  · have h := Subgroup.card_map_of_injective (K := E.comap e.toMonoidHom) (f := e.toMonoidHom)
      e.injective
    rw [hmap, hE27] at h
    exact h.symm
  · rintro A ⟨hAP, hA, hA27⟩
    have h := hEu (A.map e.toMonoidHom) ⟨Subgroup.map_mono hAP, hA.map _,
      by rw [Subgroup.card_map_of_injective e.injective, hA27]⟩
    rw [← h, Subgroup.comap_map_eq_self_of_injective e.injective]

theorem exists_conj_mem_of_elemAbelian_card_27_of_mulEquiv_a11 {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 11)) {A : Subgroup X} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) {x : X} (hx : orderOf x = 3) : ∃ g : X, g * x * g⁻¹ ∈ A := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_elemAbelian_card_27_a11 (E := A.map e.toMonoidHom)
    (hA.map _) (by rw [Subgroup.card_map_of_injective e.injective, hA27])
    (x := e x) (by rw [MulEquiv.orderOf_eq, hx])
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hg
  refine ⟨e.symm g, ?_⟩
  have hae' : a = e.symm g * x * (e.symm g)⁻¹ := e.injective (by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hae)
  rw [← hae']
  exact ha

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
