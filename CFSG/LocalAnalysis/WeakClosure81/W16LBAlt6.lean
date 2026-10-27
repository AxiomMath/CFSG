module

public import CFSG.LocalAnalysis.WeakClosure81.W16LBDesc
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapBase
public import CFSG.Quasithin.EmptyFaithful.R3c13A6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open
open scoped Pointwise

private theorem w16l_mem_normalizer_closure_of_gen {G : Type*} [Group G] [Finite G]
    {x : G} {s : Set G} (h : ∀ g ∈ s, x * g * x⁻¹ ∈ Subgroup.closure s) :
    x ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Subgroup.closure s).map (MulAut.conj x).toMonoidHom ≤ Subgroup.closure s := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    simpa [MulAut.conj_apply] using h g hg
  have hcard : Nat.card ((Subgroup.closure s).map (MulAut.conj x).toMonoidHom) =
      Nat.card (Subgroup.closure s) :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

private theorem w16l_conjSubgroup_closure_pair {G : Type*} [Group G] (x y g : G) :
    CFSG.Quasithin.conjSubgroup (Subgroup.closure ({x, y} : Set G)) g =
      Subgroup.closure ({g⁻¹ * x * g, g⁻¹ * y * g} : Set G) := by
  rw [CFSG.Quasithin.conjSubgroup, MonoidHom.map_closure]
  congr 1
  ext z
  simp [MulAut.conj_apply]

private theorem w16l_conj_mem_normalizer {G : Type*} [Group G] {A : Subgroup G} {δ v : G}
    (h : v ∈ Subgroup.normalizer (A : Set G)) :
    δ * v * δ⁻¹ ∈ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup A δ⁻¹ : Subgroup G) : Set G) := by
  have hmap := Subgroup.map_equiv_normalizer_eq A (MulAut.conj δ)
  have hv : δ * v * δ⁻¹ ∈ Subgroup.normalizer
      ((A.map (MulAut.conj δ).toMonoidHom : Subgroup G) : Set G) := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨v, h, by simp [MulAut.conj_apply]⟩
  simpa [CFSG.Quasithin.conjSubgroup, MulAut.conj_apply] using hv

private theorem w16l_witness_of_conj {G : Type*} [Group G] {V W : Subgroup G} {δ γ : G}
    (hW : W = CFSG.Quasithin.conjSubgroup V δ)
    (h : (∃ a ∈ W, ∃ b ∈ CFSG.Quasithin.conjSubgroup W γ, a * b ≠ b * a) ∧
      ∃ v ∈ W, v ≠ 1 ∧ v ∈ Subgroup.normalizer
        ((CFSG.Quasithin.conjSubgroup W γ : Subgroup G) : Set G)) :
    ∃ γ' : G, (∃ a ∈ V, ∃ b ∈ CFSG.Quasithin.conjSubgroup V γ', a * b ≠ b * a) ∧
      ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.normalizer
        ((CFSG.Quasithin.conjSubgroup V γ' : Subgroup G) : Set G) := by
  let γ' : G := δ * γ * δ⁻¹
  have hVeq : CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup W γ) δ⁻¹ =
      CFSG.Quasithin.conjSubgroup V γ' := by
    rw [hW, CFSG.Quasithin.conjSubgroup_conjSubgroup,
      CFSG.Quasithin.conjSubgroup_conjSubgroup]
    congr 1
    simp [γ']
    group
  refine ⟨γ', ?_, ?_⟩
  · obtain ⟨⟨a, haW, b, hbW, hne⟩, -⟩ := h
    have haV : δ * a * δ⁻¹ ∈ V := by
      rw [hW, CFSG.Quasithin.mem_conjSubgroup_iff] at haW
      exact haW
    have hbW' : γ * b * γ⁻¹ ∈ W := CFSG.Quasithin.mem_conjSubgroup_iff.mp hbW
    have hbV : δ * b * δ⁻¹ ∈ CFSG.Quasithin.conjSubgroup V γ' := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      rw [hW, CFSG.Quasithin.mem_conjSubgroup_iff] at hbW'
      convert hbW' using 1
      simp [γ']
      group
    refine ⟨δ * a * δ⁻¹, haV, δ * b * δ⁻¹, hbV, ?_⟩
    intro hconj
    apply hne
    have := congrArg (fun x => δ⁻¹ * x * δ) hconj
    simpa [mul_assoc] using this
  · obtain ⟨-, v, hvW, hv1, hnorm⟩ := h
    have hvV : δ * v * δ⁻¹ ∈ V := by
      rw [hW, CFSG.Quasithin.mem_conjSubgroup_iff] at hvW
      exact hvW
    have hnorm' : δ * v * δ⁻¹ ∈ Subgroup.normalizer
        ((CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup W γ) δ⁻¹ :
          Subgroup G) : Set G) :=
      w16l_conj_mem_normalizer hnorm
    refine ⟨δ * v * δ⁻¹, hvV, ?_, ?_⟩
    · intro h
      apply hv1
      have := congrArg (fun x => δ⁻¹ * x * δ) h
      simpa [mul_assoc] using this
    · rwa [hVeq] at hnorm'

private def w16l_s : alternatingGroup (Fin 6) :=
  ⟨CFSG.Quasithin.R3c13.a6x0, CFSG.Quasithin.R3c13.a6x0_mem⟩

private def w16l_K1 : Subgroup (alternatingGroup (Fin 6)) :=
  Subgroup.closure ({w16l_s, CFSG.Quasithin.R3c13.a6c1} : Set (alternatingGroup (Fin 6)))

private def w16l_K2 : Subgroup (alternatingGroup (Fin 6)) :=
  Subgroup.closure ({w16l_s, CFSG.Quasithin.R3c13.a6c3} : Set (alternatingGroup (Fin 6)))

private theorem w16l_s_sq : w16l_s * w16l_s = 1 := by
  apply Subtype.ext
  unfold w16l_s CFSG.Quasithin.R3c13.a6x0
  decide +kernel

private theorem w16l_s_ne_one : w16l_s ≠ 1 := by
  intro h
  have h' : (CFSG.Quasithin.R3c13.a6x0 : Equiv.Perm (Fin 6)) = 1 := congrArg Subtype.val h
  revert h'
  unfold CFSG.Quasithin.R3c13.a6x0
  decide +kernel

private theorem w16l_closure_mul_right {x y : alternatingGroup (Fin 6)} (hx : x * x = 1) :
    Subgroup.closure ({x, x * y} : Set (alternatingGroup (Fin 6))) =
      Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 6))) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hzx | hzy
    · rw [hzx]
      exact Subgroup.subset_closure (by simp)
    · rw [hzy]
      have hxmem : x ∈ Subgroup.closure ({x, x * y} : Set (alternatingGroup (Fin 6))) :=
        Subgroup.subset_closure (by simp)
      have hxymem : x * y ∈ Subgroup.closure ({x, x * y} : Set (alternatingGroup (Fin 6))) :=
        Subgroup.subset_closure (by simp)
      have hmul : x * (x * y) ∈
          Subgroup.closure ({x, x * y} : Set (alternatingGroup (Fin 6))) :=
        mul_mem hxmem hxymem
      have hy : y = x * (x * y) := by rw [← mul_assoc, hx, one_mul]
      exact (congrArg (fun z => z ∈ Subgroup.closure
        ({x, x * y} : Set (alternatingGroup (Fin 6)))) hy).mpr hmul

private theorem w16l_closure_pair_eq {G : Type*} [Group G] [Finite G] [DecidableEq G]
    {W : Subgroup G} (hcard : Nat.card W = 4)
    {s q : G} (hs : s ∈ W) (hq : q ∈ W)
    (hs2 : s * s = 1) (hq2 : q * q = 1) (hcomm : q * s = s * q)
    (hne : s ≠ q) (hs1 : s ≠ 1) (hq1 : q ≠ 1) :
    Subgroup.closure ({s, q} : Set G) = W := by
  have hsq1 : s * q ≠ 1 := by
    intro h
    have h' := congrArg (fun x => x * q) h
    simp only [mul_assoc, hq2, mul_one, one_mul] at h'
    exact hne h'
  have hsqs : s * q ≠ s := by
    intro h
    have h' := congrArg (fun x => s * x) h
    rw [← mul_assoc, hs2, one_mul] at h'
    exact hq1 h'
  have hsq_q : s * q ≠ q := by
    intro h
    have h' := congrArg (fun x => x * q) h
    rw [mul_assoc, hq2, mul_one] at h'
    exact hs1 h'
  have hTcard : ({1, s, q, s * q} : Finset G).card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨1, s, q, s * q, hs1.symm, hq1.symm, hsq1.symm, hne, hsqs.symm,
      hsq_q.symm, rfl⟩
  have hWncard : (W : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hTsub : (({1, s, q, s * q} : Finset G) : Set G) ⊆ (W : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem W
    · exact hs
    · exact hq
    · exact mul_mem hs hq
  have hTeq : (({1, s, q, s * q} : Finset G) : Set G) = (W : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hTsub
    rw [Set.ncard_coe_finset, hTcard, hWncard]
  have hWle : W ≤ Subgroup.closure ({s, q} : Set G) := by
    intro x hx
    have hx' : x ∈ (({1, s, q, s * q} : Finset G) : Set G) := by
      rw [hTeq]
      exact hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hle : Subgroup.closure ({s, q} : Set G) ≤ W := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hs
    · exact hq
  exact le_antisymm hle hWle

set_option maxRecDepth 100000 in
private theorem w16l_klein_eq_K1_or_K2 {W : Subgroup (alternatingGroup (Fin 6))}
    (hW4 : Nat.card W = 4) (hs : w16l_s ∈ W) (hWcomm : IsMulCommutative W)
    (hWexp : ∀ x ∈ W, x * x = 1) :
    W = w16l_K1 ∨ W = w16l_K2 := by
  classical
  have hWcard' : Fintype.card W = 4 := by
    rwa [Nat.card_eq_fintype_card] at hW4
  let e1 : W := ⟨1, one_mem W⟩
  let e2 : W := ⟨w16l_s, hs⟩
  have he12 : e1 ≠ e2 := by
    intro h
    exact w16l_s_ne_one (congrArg Subtype.val h).symm
  have he21 : e2 ≠ e1 := he12.symm
  let T : Finset W := ((Finset.univ : Finset W).erase e1).erase e2
  have he2mem : e2 ∈ (Finset.univ : Finset W).erase e1 := by
    rw [Finset.mem_erase]
    exact ⟨he21, Finset.mem_univ _⟩
  have hTcard : T.card = 2 := by
    rw [Finset.card_erase_of_mem he2mem, Finset.card_erase_of_mem (Finset.mem_univ e1)]
    rw [Finset.card_univ, hWcard']
  obtain ⟨qW, hqT⟩ := Finset.card_pos.mp (by rw [hTcard]; norm_num)
  rw [Finset.mem_erase, Finset.mem_erase] at hqT
  obtain ⟨hq_ne_e2, hq_ne_e1, -⟩ := hqT
  let q : alternatingGroup (Fin 6) := qW.val
  have hqW : q ∈ W := qW.2
  have hq_ne_s : q ≠ w16l_s := by
    intro h
    apply hq_ne_e2
    apply Subtype.ext
    exact h
  have hq_ne_one : q ≠ 1 := by
    intro h
    apply hq_ne_e1
    apply Subtype.ext
    exact h
  have hq2 : q * q = 1 := hWexp q hqW
  have hcommW : qW * e2 = e2 * qW := IsMulCommutative.is_comm.comm qW e2
  have hcomm : q * w16l_s = w16l_s * q := by
    have h' := congrArg Subtype.val hcommW
    simpa [q, e2] using h'
  have hq_perm_ne : (q : Equiv.Perm (Fin 6)) ≠ 1 := by
    intro h
    exact hq_ne_one (Subtype.ext h)
  have hq_perm_sq : (q : Equiv.Perm (Fin 6)) * (q : Equiv.Perm (Fin 6)) = 1 := by
    have h' := congrArg Subtype.val hq2
    simpa using h'
  have hq_perm_ne_s : (q : Equiv.Perm (Fin 6)) ≠ CFSG.Quasithin.R3c13.a6x0 := by
    intro h
    exact hq_ne_s (Subtype.ext h)
  have hq_sign : Equiv.Perm.sign (q : Equiv.Perm (Fin 6)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp q.2
  have hq_comm_perm : (q : Equiv.Perm (Fin 6)) * CFSG.Quasithin.R3c13.a6x0 =
      CFSG.Quasithin.R3c13.a6x0 * (q : Equiv.Perm (Fin 6)) := by
    have h' := congrArg Subtype.val hcomm
    simpa [w16l_s] using h'
  have hcase := CFSG.Quasithin.R3c13.a6_comm_x0 (q : Equiv.Perm (Fin 6)) hq_sign
    hq_perm_sq hq_perm_ne hq_perm_ne_s hq_comm_perm
  have hpair := w16l_closure_pair_eq hW4 hs hqW w16l_s_sq hq2 hcomm hq_ne_s.symm
    w16l_s_ne_one hq_ne_one
  rcases hcase with h | h | h | h
  · left
    have hq1 : q = CFSG.Quasithin.R3c13.a6c1 := Subtype.ext h
    rw [← hpair, hq1]
    rfl
  · left
    have hq2' : q = CFSG.Quasithin.R3c13.a6c2 := Subtype.ext h
    have hc2 : CFSG.Quasithin.R3c13.a6c2 =
        w16l_s * CFSG.Quasithin.R3c13.a6c1 := by
      apply Subtype.ext
      unfold w16l_s CFSG.Quasithin.R3c13.a6c2 CFSG.Quasithin.R3c13.a6c1
      decide +kernel
    rw [← hpair, hq2', hc2]
    change Subgroup.closure ({w16l_s, w16l_s * CFSG.Quasithin.R3c13.a6c1} :
      Set (alternatingGroup (Fin 6))) = Subgroup.closure ({w16l_s,
        CFSG.Quasithin.R3c13.a6c1} : Set (alternatingGroup (Fin 6)))
    exact (w16l_closure_mul_right (x := w16l_s) (y := CFSG.Quasithin.R3c13.a6c1) w16l_s_sq)
  · right
    have hq3 : q = CFSG.Quasithin.R3c13.a6c3 := Subtype.ext h
    rw [← hpair, hq3]
    rfl
  · right
    have hq4 : q = CFSG.Quasithin.R3c13.a6c4 := Subtype.ext h
    have hc4 : CFSG.Quasithin.R3c13.a6c4 =
        w16l_s * CFSG.Quasithin.R3c13.a6c3 := by
      apply Subtype.ext
      unfold w16l_s CFSG.Quasithin.R3c13.a6c4 CFSG.Quasithin.R3c13.a6c3
      decide +kernel
    rw [← hpair, hq4, hc4]
    change Subgroup.closure ({w16l_s, w16l_s * CFSG.Quasithin.R3c13.a6c3} :
      Set (alternatingGroup (Fin 6))) = Subgroup.closure ({w16l_s,
        CFSG.Quasithin.R3c13.a6c3} : Set (alternatingGroup (Fin 6)))
    exact (w16l_closure_mul_right (x := w16l_s) (y := CFSG.Quasithin.R3c13.a6c3) w16l_s_sq)

private def w16l_g1 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def w16l_g2 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def w16l_s1 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def w16l_a1 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def w16l_t2 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 4 * Equiv.swap 1 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def w16l_v1 : alternatingGroup (Fin 6) :=
  w16l_s * CFSG.Quasithin.R3c13.a6c1

set_option maxRecDepth 100000 in
private theorem w16l_g1_s1 : w16l_g1 * w16l_s1 * w16l_g1⁻¹ = w16l_s := by
  apply Subtype.ext
  unfold w16l_g1 w16l_s1 w16l_s CFSG.Quasithin.R3c13.a6x0
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_s1_conj : w16l_s1 = w16l_g1⁻¹ * w16l_s * w16l_g1 := by
  apply Subtype.ext
  unfold w16l_g1 w16l_s1 w16l_s CFSG.Quasithin.R3c13.a6x0
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_a1_conj : w16l_a1 = w16l_g1⁻¹ * CFSG.Quasithin.R3c13.a6c1 * w16l_g1 := by
  apply Subtype.ext
  unfold w16l_g1 w16l_a1 CFSG.Quasithin.R3c13.a6c1
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_s_s1_ne : w16l_s * w16l_s1 ≠ w16l_s1 * w16l_s := by
  intro h
  have h' := congrArg Subtype.val h
  revert h'
  unfold w16l_s w16l_s1 CFSG.Quasithin.R3c13.a6x0
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_v1_s1 : w16l_v1 * w16l_s1 * w16l_v1⁻¹ = w16l_a1 := by
  apply Subtype.ext
  unfold w16l_v1 w16l_s1 w16l_a1 w16l_s CFSG.Quasithin.R3c13.a6x0 CFSG.Quasithin.R3c13.a6c1
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_v1_a1 : w16l_v1 * w16l_a1 * w16l_v1⁻¹ = w16l_s1 := by
  apply Subtype.ext
  unfold w16l_v1 w16l_s1 w16l_a1 w16l_s CFSG.Quasithin.R3c13.a6x0 CFSG.Quasithin.R3c13.a6c1
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_v1_ne_one : w16l_v1 ≠ 1 := by
  intro h
  have h' := congrArg Subtype.val h
  revert h'
  unfold w16l_v1 w16l_s CFSG.Quasithin.R3c13.a6x0 CFSG.Quasithin.R3c13.a6c1
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_g2_t2 : w16l_g2 * w16l_t2 * w16l_g2⁻¹ = CFSG.Quasithin.R3c13.a6c3 := by
  apply Subtype.ext
  unfold w16l_g2 w16l_t2 CFSG.Quasithin.R3c13.a6c3
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_s2_conj : CFSG.Quasithin.R3c13.a6c1 = w16l_g2⁻¹ * w16l_s * w16l_g2 := by
  apply Subtype.ext
  unfold w16l_g2 w16l_s CFSG.Quasithin.R3c13.a6c1 CFSG.Quasithin.R3c13.a6x0
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_t2_conj : w16l_t2 = w16l_g2⁻¹ * CFSG.Quasithin.R3c13.a6c3 * w16l_g2 := by
  apply Subtype.ext
  unfold w16l_g2 w16l_t2 CFSG.Quasithin.R3c13.a6c3
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_s_t2_ne : w16l_s * w16l_t2 ≠ w16l_t2 * w16l_s := by
  intro h
  have h' := congrArg Subtype.val h
  revert h'
  unfold w16l_s w16l_t2 CFSG.Quasithin.R3c13.a6x0
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_s_s2 : w16l_s * CFSG.Quasithin.R3c13.a6c1 * w16l_s⁻¹ =
    CFSG.Quasithin.R3c13.a6c1 := by
  apply Subtype.ext
  unfold w16l_s CFSG.Quasithin.R3c13.a6c1 CFSG.Quasithin.R3c13.a6x0
  decide +kernel

set_option maxRecDepth 100000 in
private theorem w16l_s_t2 : w16l_s * w16l_t2 * w16l_s⁻¹ =
    CFSG.Quasithin.R3c13.a6c1 * w16l_t2 := by
  apply Subtype.ext
  unfold w16l_s w16l_t2 CFSG.Quasithin.R3c13.a6c1 CFSG.Quasithin.R3c13.a6x0
  decide +kernel

private theorem w16l_K1_witness :
    ∃ γ : alternatingGroup (Fin 6),
      (∃ a ∈ w16l_K1, ∃ b ∈ CFSG.Quasithin.conjSubgroup w16l_K1 γ, a * b ≠ b * a) ∧
        ∃ v ∈ w16l_K1, v ≠ 1 ∧ v ∈ Subgroup.normalizer
          ((CFSG.Quasithin.conjSubgroup w16l_K1 γ : Subgroup (alternatingGroup (Fin 6))) :
            Set (alternatingGroup (Fin 6))) := by
  refine ⟨w16l_g1, ?_, ?_⟩
  · refine ⟨w16l_s, ?_, w16l_s1, ?_, w16l_s_s1_ne⟩
    · exact Subgroup.subset_closure (by simp)
    · rw [CFSG.Quasithin.mem_conjSubgroup_iff, w16l_g1_s1]
      exact Subgroup.subset_closure (by simp)
  · refine ⟨w16l_v1, ?_, w16l_v1_ne_one, ?_⟩
    · exact mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · have hW1 : CFSG.Quasithin.conjSubgroup w16l_K1 w16l_g1 =
          Subgroup.closure ({w16l_s1, w16l_a1} : Set (alternatingGroup (Fin 6))) := by
        unfold w16l_K1
        rw [w16l_conjSubgroup_closure_pair]
        rw [← w16l_s1_conj, ← w16l_a1_conj]
      rw [hW1]
      apply w16l_mem_normalizer_closure_of_gen
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · rw [w16l_v1_s1]
        exact Subgroup.subset_closure (by simp)
      · rw [w16l_v1_a1]
        exact Subgroup.subset_closure (by simp)

private theorem w16l_K2_witness :
    ∃ γ : alternatingGroup (Fin 6),
      (∃ a ∈ w16l_K2, ∃ b ∈ CFSG.Quasithin.conjSubgroup w16l_K2 γ, a * b ≠ b * a) ∧
        ∃ v ∈ w16l_K2, v ≠ 1 ∧ v ∈ Subgroup.normalizer
          ((CFSG.Quasithin.conjSubgroup w16l_K2 γ : Subgroup (alternatingGroup (Fin 6))) :
            Set (alternatingGroup (Fin 6))) := by
  refine ⟨w16l_g2, ?_, ?_⟩
  · refine ⟨w16l_s, ?_, w16l_t2, ?_, w16l_s_t2_ne⟩
    · exact Subgroup.subset_closure (by simp)
    · rw [CFSG.Quasithin.mem_conjSubgroup_iff, w16l_g2_t2]
      exact Subgroup.subset_closure (by simp)
  · refine ⟨w16l_s, ?_, w16l_s_ne_one, ?_⟩
    · exact Subgroup.subset_closure (by simp)
    · have hW2 : CFSG.Quasithin.conjSubgroup w16l_K2 w16l_g2 =
          Subgroup.closure ({CFSG.Quasithin.R3c13.a6c1, w16l_t2} :
            Set (alternatingGroup (Fin 6))) := by
        unfold w16l_K2
        rw [w16l_conjSubgroup_closure_pair]
        rw [← w16l_s2_conj, ← w16l_t2_conj]
      rw [hW2]
      apply w16l_mem_normalizer_closure_of_gen
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · rw [w16l_s_s2]
        exact Subgroup.subset_closure (by simp)
      · rw [w16l_s_t2]
        exact mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))

set_option maxRecDepth 100000 in
theorem w16l_alt6_witness (V : Subgroup (alternatingGroup (Fin 6))) (hV : IsElemAbelian 2 V)
    (hcard : Nat.card V = 4) :
    ∃ γ : alternatingGroup (Fin 6),
      (∃ a ∈ V, ∃ b ∈ CFSG.Quasithin.conjSubgroup V γ, a * b ≠ b * a) ∧
        ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.normalizer
          ((CFSG.Quasithin.conjSubgroup V γ : Subgroup (alternatingGroup (Fin 6))) :
            Set (alternatingGroup (Fin 6))) := by
  obtain ⟨p, hpV, -, -, hpo, -, -⟩ :=
    CFSG.ComponentClassification.AS76b.exists_two_involutions hV hcard
  have hp2 : p * p = 1 := by
    have h := pow_orderOf_eq_one p
    simpa [hpo, pow_two] using h
  have hp1 : p ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hpo
    norm_num at hpo
  obtain ⟨ρ, hρA, hρ⟩ := CFSG.Quasithin.S143.alt6_invol_conj
    (p : Equiv.Perm (Fin 6)) CFSG.Quasithin.R3c13.a6x0 p.2
    CFSG.Quasithin.R3c13.a6x0_mem
    (by intro h; exact hp1 (Subtype.ext h))
    (by intro h; exact w16l_s_ne_one (Subtype.ext h))
    (by simpa using congrArg Subtype.val hp2)
    (by simpa [w16l_s] using congrArg Subtype.val w16l_s_sq)
  let ρA : alternatingGroup (Fin 6) := ⟨ρ, hρA⟩
  let δ : alternatingGroup (Fin 6) := ρA⁻¹
  have hρG : ρA * p * ρA⁻¹ = w16l_s := Subtype.ext hρ
  have hp_eq : p = δ * w16l_s * δ⁻¹ := by
    have h := congrArg (fun x => ρA⁻¹ * x * ρA) hρG
    simpa [δ, mul_assoc] using h
  let W : Subgroup (alternatingGroup (Fin 6)) := CFSG.Quasithin.conjSubgroup V δ
  have hWconj : W = CFSG.Quasithin.conjSubgroup V δ := rfl
  have hsW : w16l_s ∈ W := by
    rw [hWconj, CFSG.Quasithin.mem_conjSubgroup_iff, ← hp_eq]
    exact hpV
  have hW4 : Nat.card W = 4 := by
    rw [hWconj, CFSG.Quasithin.conjSubgroup]
    rw [Subgroup.card_map_of_injective (MulAut.conj δ⁻¹).injective, hcard]
  have hWcomm : IsMulCommutative W := by
    haveI : IsMulCommutative V := hV.1
    rw [hWconj, CFSG.Quasithin.conjSubgroup]
    exact Subgroup.map_isMulCommutative V (MulAut.conj δ⁻¹).toMonoidHom
  have hWexp : ∀ x ∈ W, x * x = 1 := by
    intro x hx
    rw [hWconj, CFSG.Quasithin.conjSubgroup] at hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul, show v * v = 1 by simpa [pow_two] using hV.2 v hv, map_one]
  have hWcase := w16l_klein_eq_K1_or_K2 hW4 hsW hWcomm hWexp
  rcases hWcase with hWK1 | hWK2
  · have hw := w16l_K1_witness
    rw [← hWK1] at hw
    obtain ⟨γ, hγ⟩ := hw
    exact w16l_witness_of_conj hWconj (γ := γ) hγ
  · have hw := w16l_K2_witness
    rw [← hWK2] at hw
    obtain ⟨γ, hγ⟩ := hw
    exact w16l_witness_of_conj hWconj (γ := γ) hγ

set_option maxRecDepth 100000 in
theorem w16l_false_of_alt6 {X : Type} [Group X] [Finite X] {B : Subgroup X}
    (hsh : Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)))
    (hcard : Nat.card B = 4) (hel : IsElemAbelian 2 B) (hcore : CFSG.pCore 2 X = ⊥)
    (hP : ∀ x : X, (∃ a ∈ B, ∃ b ∈ CFSG.Quasithin.conjSubgroup B x, a * b ≠ b * a) →
      ∀ a ∈ B, a ∈ Subgroup.normalizer ((CFSG.Quasithin.conjSubgroup B x : Subgroup X) : Set X) →
        a = 1) :
    False := by
  classical
  let Z := Subgroup.center X
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  let e : X ⧸ Z ≃* alternatingGroup (Fin 6) := hsh.some
  let f : X →* alternatingGroup (Fin 6) := e.toMonoidHom.comp π
  have hZo : Odd (Nat.card Z) := odd_card_center_of_pCore_eq_bot hcore
  have hB2 : IsPGroup 2 B := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro b
    refine ⟨1, ?_⟩
    show b ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa [pow_two] using hel.2 (b : X) b.2)
  have hBZ : B ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbB, hbZ⟩ := Subgroup.mem_inf.mp hb
    have hb2 : b * b = 1 := by
      have := hel.2 b hbB
      simpa [pow_two] using this
    have hdvd2 : orderOf b ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rwa [pow_two]
    have hdvdZ : orderOf b ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hbZ
    have hodd : Odd (orderOf b) := hZo.of_dvd_nat hdvdZ
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
    · rw [h2] at hodd
      exact absurd hodd (by norm_num)
  have hinj : Set.InjOn π (B : Set X) := by
    intro b1 hb1 b2 hb2 heq
    have hker : b1⁻¹ * b2 ∈ Z := by
      have h1 : π (b1⁻¹ * b2) = 1 := by
        rw [map_mul, map_inv, heq, inv_mul_cancel]
      have hmem : b1⁻¹ * b2 ∈ (QuotientGroup.mk' Z).ker := MonoidHom.mem_ker.mp h1
      rwa [QuotientGroup.ker_mk'] at hmem
    have hmemB : b1⁻¹ * b2 ∈ B := mul_mem (inv_mem hb1) hb2
    have hmem : b1⁻¹ * b2 ∈ B ⊓ Z := Subgroup.mem_inf.mpr ⟨hmemB, hker⟩
    rw [hBZ] at hmem
    exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem)
  have hcardMap : Nat.card (B.map π) = 4 := by
    change Nat.card (π '' (B : Set X)) = 4
    rw [Nat.card_image_of_injOn hinj]
    exact hcard
  let V : Subgroup (alternatingGroup (Fin 6)) := B.map f
  have hVcard : Nat.card V = 4 := by
    change Nat.card (B.map (e.toMonoidHom.comp π)) = 4
    rw [← Subgroup.map_map (K := B) (f := π) (g := e.toMonoidHom)]
    rw [Subgroup.card_map_of_injective e.injective, hcardMap]
  have hVel : IsElemAbelian 2 V := by
    constructor
    · haveI : IsMulCommutative B := hel.1
      exact Subgroup.map_isMulCommutative B f
    · intro x hx
      change x ∈ B.map f at hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
      rw [pow_two, ← map_mul,
        show b * b = 1 by simpa [pow_two] using hel.2 b hb, map_one]
  obtain ⟨γ, ⟨a, haV, b, hbV, hab⟩, v, hvV, hv1, hvnorm⟩ :=
    w16l_alt6_witness V hVel hVcard
  obtain ⟨y, hy⟩ := e.surjective γ
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z y
  have hfx : f x = γ := by
    change e (π x) = γ
    rw [hx, hy]
  have hVf : V = B.map f := rfl
  obtain ⟨a₀, ha₀B, ha_eq⟩ := by
    rw [hVf] at haV
    exact Subgroup.mem_map.mp haV
  have hVconj : CFSG.Quasithin.conjSubgroup V γ =
      (CFSG.Quasithin.conjSubgroup B x).map f := by
    rw [hVf, ← hfx, map_conjSubgroup_hom]
  obtain ⟨b₀, hb₀, hb_eq⟩ := by
    rw [hVconj] at hbV
    exact Subgroup.mem_map.mp hbV
  have hnoncomm : ∃ a ∈ B, ∃ b ∈ CFSG.Quasithin.conjSubgroup B x, a * b ≠ b * a := by
    refine ⟨a₀, ha₀B, b₀, hb₀, ?_⟩
    intro h
    apply hab
    rw [← ha_eq, ← hb_eq, ← map_mul, ← map_mul, h]
  have hfree : ∀ b ∈ B, b ∈ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup B x : Subgroup X) : Set X) → b = 1 :=
    hP x hnoncomm
  have hdesc := w16l_descent_free hZo hB2 x hfree
  obtain ⟨v₀, hv₀B, hv_eq⟩ := by
    rw [hVf] at hvV
    exact Subgroup.mem_map.mp hvV
  have hπv₀ : π v₀ ∈ B.map π := Subgroup.mem_map.mpr ⟨v₀, hv₀B, rfl⟩
  have hVconjE : CFSG.Quasithin.conjSubgroup V γ =
      ((CFSG.Quasithin.conjSubgroup B x).map π).map e.toMonoidHom := by
    rw [hVconj]
    change (CFSG.Quasithin.conjSubgroup B x).map (e.toMonoidHom.comp π) =
      ((CFSG.Quasithin.conjSubgroup B x).map π).map e.toMonoidHom
    rw [← Subgroup.map_map (K := CFSG.Quasithin.conjSubgroup B x) (f := π)
      (g := e.toMonoidHom)]
  have hvnorm' : e.symm v ∈ Subgroup.normalizer
      (((CFSG.Quasithin.conjSubgroup B x).map π : Subgroup (X ⧸ Z)) :
        Set (X ⧸ Z)) := by
    have hmap := Subgroup.map_equiv_normalizer_eq
      ((CFSG.Quasithin.conjSubgroup B x).map π) e
    rw [hVconjE] at hvnorm
    rw [← hmap] at hvnorm
    obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp hvnorm
    have hye : y = e.symm v := by
      apply e.injective
      simpa using hyv
    simpa [hye] using hy
  have hsymm : e.symm v = π v₀ := by
    apply e.injective
    rw [e.apply_symm_apply]
    rw [← hv_eq]
    rfl
  have hπnorm : π v₀ ∈ Subgroup.normalizer
      (((CFSG.Quasithin.conjSubgroup B x).map π : Subgroup (X ⧸ Z)) :
        Set (X ⧸ Z)) := by
    rw [← hsymm]
    exact hvnorm'
  have hH : ((CFSG.Quasithin.conjSubgroup B x).map π : Subgroup (X ⧸ Z)) =
      CFSG.Quasithin.conjSubgroup (B.map π) (π x) :=
    (map_conjSubgroup_hom π B x).symm
  have hπnorm' : π v₀ ∈ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup (B.map π) (π x) : Subgroup (X ⧸ Z)) :
        Set (X ⧸ Z)) := by
    rw [← hH]
    exact hπnorm
  have hπv₀_one : π v₀ = 1 := hdesc (π v₀) hπv₀ hπnorm'
  have hv_one : v = 1 := by
    have hvE : v = e (π v₀) := by
      rw [← hv_eq]
      rfl
    rw [hvE, hπv₀_one, map_one]
  exact hv1 hv_one

end CFSG.LocalAnalysis.WeakClosure81

end
