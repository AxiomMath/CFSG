module

public import CFSG.Sporadic.SchreierLemmas.MoorePresentation
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.H13.HSLocR
public import Certificates.Certificate589207

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native CFSG.Open CFSG.Sporadic.SchreierLemmas

theorem not_perfect_of_index_two' {H : Type*} [Group H] {N : Subgroup H} (hN : N.index = 2) :
    ¬ Group.IsPerfect H := by
  intro hH
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (H ⧸ N) = 2 := by rw [← Subgroup.index_eq_card]; exact hN
  haveI : IsCyclic (H ⧸ N) := isCyclic_of_prime_card hcard
  haveI : IsMulCommutative (H ⧸ N) := IsCyclic.isMulCommutative
  have hc : commutator H ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rw [hH.commutator_eq_top, top_le_iff] at hc
  rw [hc, Subgroup.index_top] at hN
  omega

theorem card_alt8 {G : Type*} [Group G] {Q : Subgroup G} :
    Nonempty (alternatingGroup (Fin 8) ≃* Q) → Nat.card Q = 20160 := by
  rintro ⟨e⟩
  rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem perfectCore_eq_of_a8 {G : Type*} [Group G] [Finite G] {C Q : Subgroup G} (hQC : Q ≤ C)
    (hQ : Nonempty (alternatingGroup (Fin 8) ≃* Q)) (hC : Nat.card C ≤ 40320) :
    perfectCore C = Q := by
  obtain ⟨e⟩ := hQ
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup Q := e.symm.isSimpleGroup
  have hcard : Nat.card Q = 20160 := by
    rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hperfQ : Group.IsPerfect Q := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      haveI : IsMulCommutative Q := (commutator_eq_bot_iff Q).mp h
      have := (Group.is_simple_iff_prime_card (α := Q)).mp inferInstance
      rw [hcard] at this
      exact absurd this (by norm_num)
    · exact h
  have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hperfQ
  have hQle : Q ≤ perfectCore C := le_perfectCore_of_perfect hQC hperf
  have hS : ⁅perfectCore C, perfectCore C⁆ = perfectCore C := perfectCore_perfect C
  have hSC : perfectCore C ≤ C := perfectCore_le C
  have hcardS : Nat.card (perfectCore C) ≤ 40320 := (Subgroup.card_le_of_le hSC).trans hC
  by_contra hne
  have hlt : Nat.card Q < Nat.card (perfectCore C) := by
    rcases (Subgroup.card_le_of_le hQle).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hQle h.symm.le).symm hne
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hQle
  rw [hcard] at hk hlt
  have hk2 : k = 2 := by
    rcases k with _ | _ | _ | k
    · have := Nat.card_pos (α := perfectCore C); omega
    · omega
    · rfl
    · omega
  subst hk2
  have hQ' : Nat.card (Q.subgroupOf (perfectCore C)) = Nat.card Q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv]
  have hidx : (Q.subgroupOf (perfectCore C)).index = 2 := by
    have hm := (Q.subgroupOf (perfectCore C)).card_mul_index
    rw [hQ', hcard, hk] at hm
    omega
  have hperfS : Group.IsPerfect (perfectCore C) := Subgroup.isPerfect_iff.mpr hS
  exact not_perfect_of_index_two' hidx hperfS

@[expose] def CPG (r : Equiv.Perm (Fin 100)) : Subgroup PG where
  carrier := {p | (p : Equiv.Perm (Fin 100)) * r = r * (p : Equiv.Perm (Fin 100))}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at ha ⊢
    calc (a : Equiv.Perm (Fin 100))⁻¹ * r = (a : Equiv.Perm (Fin 100))⁻¹ * (r * (a : Equiv.Perm (Fin 100))) *
          (a : Equiv.Perm (Fin 100))⁻¹ := by group
      _ = (a : Equiv.Perm (Fin 100))⁻¹ * ((a : Equiv.Perm (Fin 100)) * r) *
          (a : Equiv.Perm (Fin 100))⁻¹ := by rw [ha]
      _ = r * (a : Equiv.Perm (Fin 100))⁻¹ := by group

theorem mooreWords_lt : ∀ w ∈ mooreWords, ∀ l ∈ w, l < 4 := by decide +kernel

@[expose] noncomputable def xe (i : ℕ) : PG := wAB ga gb (mooreWords.getD (i - 1) [])

theorem T_xe {i : ℕ} (h1 : 1 ≤ i) (h6 : i ≤ 6) : T (xe i) = mooreX i := by
  have hlen : mooreWords.length = 6 := rfl
  have hlt : i - 1 < mooreWords.length := by omega
  have hmem : mooreWords.getD (i - 1) [] ∈ mooreWords := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  rw [xe, T_wAB (mooreWords_lt _ hmem), mooreX, mooreTabs]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hlt]

theorem sq_one_of_T {g : PG} (h : compT (T g) (T g) = idT 100) : g ^ 2 = 1 := by
  apply eq_of_T
  rw [pow_two, T_mul, h, T_one]

theorem cube_one_of_T {g : PG} (h : compT (T g) (compT (T g) (T g)) = idT 100) : g ^ 3 = 1 := by
  apply eq_of_T
  rw [pow_three, T_mul, T_mul, h, T_one]

theorem mooreOK_parts :
    (compT (mooreX 1) (compT (mooreX 1) (mooreX 1)) = idT 100) ∧ mooreX 1 ≠ idT 100 ∧
      (∀ j, 2 ≤ j → j ≤ 6 → compT (mooreX j) (mooreX j) = idT 100 ∧
        compT (compT (mooreX (j - 1)) (mooreX j))
          (compT (compT (mooreX (j - 1)) (mooreX j)) (compT (mooreX (j - 1)) (mooreX j))) =
            idT 100) ∧
      (∀ i j, 1 ≤ i → i + 2 ≤ j → j ≤ 6 →
        compT (compT (mooreX i) (mooreX j)) (compT (mooreX i) (mooreX j)) = idT 100) ∧
      (∀ t ∈ mooreTabs, commT t r0Tab = true) := by
  have h := Certificates.certificate589207.2.2.1
  simp only [mooreOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    List.mem_range'_1, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun j hj1 hj6 => ?_, fun i j hi hij hj => ?_, h5⟩
  · exact h3 j ⟨hj1, by omega⟩
  · exact h4 i ⟨hi, by omega⟩ j ⟨hij, by omega⟩

theorem isMooreFamily_xe : IsMooreFamily 6 xe := by
  obtain ⟨h1, -, h3, h4, -⟩ := mooreOK_parts
  refine ⟨?_, fun j hj1 hj6 => ?_, fun j hj1 hj6 => ?_, fun i j hi hij hj => ?_⟩
  · refine cube_one_of_T ?_
    rw [T_xe le_rfl (by norm_num)]
    exact h1
  · refine sq_one_of_T ?_
    rw [T_xe (by omega) hj6]
    exact (h3 j hj1 hj6).1
  · refine cube_one_of_T ?_
    rw [T_mul, T_xe (by omega) (by omega), T_xe (by omega) hj6]
    exact (h3 j hj1 hj6).2
  · refine sq_one_of_T ?_
    rw [T_mul, T_xe hi (by omega), T_xe (by omega) hj]
    exact h4 i j hi hij hj

theorem moore_K {r₀ : Equiv.Perm (Fin 100)} (hr₀ : T r₀ = r0Tab) :
    ∃ K : Subgroup PG, Nonempty (alternatingGroup (Fin 8) ≃* K) ∧ K ≤ CPG r₀ := by
  obtain ⟨-, h2, -, -, h5⟩ := mooreOK_parts
  have hne : ∃ i ∈ Set.Icc 1 (8 - 2), xe i ≠ 1 := by
    refine ⟨1, ⟨le_rfl, by norm_num⟩, fun h => h2 ?_⟩
    rw [← T_xe le_rfl (by norm_num), h, T_one]
  obtain ⟨e⟩ := ((moore_alternating_presentation (by norm_num : 3 ≤ 8) xe isMooreFamily_xe).2.2.2.2.2
    (by norm_num) hne).2
  refine ⟨Subgroup.closure (xe '' Set.Icc 1 (8 - 2)), ⟨e⟩, ?_⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨i, ⟨hi1, hi6⟩, rfl⟩
  have hi6' : i ≤ 6 := by simpa using hi6
  have hmem : mooreX i ∈ mooreTabs := by
    have hlen : mooreTabs.length = 6 := by simp [mooreTabs]; rfl
    have hlt : i - 1 < mooreTabs.length := by omega
    rw [mooreX, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  have hc := h5 _ hmem
  show ((xe i : PG) : Equiv.Perm (Fin 100)) * r₀ = r₀ * ((xe i : PG) : Equiv.Perm (Fin 100))
  refine commT_iff.mp ?_
  rw [T_coe, T_xe hi1 hi6', hr₀]
  exact hc

@[expose] noncomputable def cjElt (k : ℕ) : PG := enumElt [ga, gb, ga⁻¹, gb⁻¹] cjTree.1 cjTree.2 k

theorem cj_enumOK : enumOK 1100 AB cjTree.1 cjTree.2 = true := by
  have h := Certificates.certificate589207.2.2.2
  simp only [cjOK, Bool.and_eq_true] at h
  exact h.1

theorem cjConjs_nodup : cjConjs.Nodup := by
  have h := Certificates.certificate589207.2.2.2
  simp only [cjOK, Bool.and_eq_true] at h
  exact (pwDistinct_iff _).mp h.2

theorem cjElems_size : cjElems.size = 1100 := by simp [cjElems, enumTabs]

theorem T_cjElt {k : ℕ} (hk : k < 1100) : T (cjElt k) = cjElems.getD k #[] := by
  have h := enumTabs_getD AB_hG cj_enumOK hk
  rw [Prod.mk.eta] at h
  exact h.symm

theorem getD_map_toList {α β : Type} (A : Array α) (f : α → β) {k : ℕ} (hk : k < A.size)
    (d : β) (d' : α) : (A.toList.map f).getD k d = f (A.getD k d') := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hk]

theorem T_cjElt_conj {r₀ : Equiv.Perm (Fin 100)} (hr₀ : T r₀ = r0Tab) {k : ℕ} (hk : k < 1100) :
    T ((cjElt k : Equiv.Perm (Fin 100)) * r₀ * (cjElt k : Equiv.Perm (Fin 100))⁻¹) =
      cjConjs.getD k #[] := by
  rw [T_conj, T_coe, T_cjElt hk, hr₀, cjConjs,
    getD_map_toList cjElems _ (by rw [cjElems_size]; exact hk) _ #[]]

theorem card_CPG_le {r₀ : Equiv.Perm (Fin 100)} (hr₀ : T r₀ = r0Tab) (h : PG) :
    Nat.card (CPG ((h : Equiv.Perm (Fin 100)) * r₀ * (h : Equiv.Perm (Fin 100))⁻¹)) ≤ 40320 := by
  classical
  set r : Equiv.Perm (Fin 100) := (h : Equiv.Perm (Fin 100)) * r₀ * (h : Equiv.Perm (Fin 100))⁻¹
    with hr
  have hlen : cjConjs.length = 1100 := by simp [cjConjs, cjElems_size]
  have hinj : Function.Injective fun k : Fin 1100 =>
      (QuotientGroup.mk (cjElt k * h⁻¹) : PG ⧸ CPG r) := by
    intro k l hkl
    have hmem := QuotientGroup.eq.mp hkl
    have hc : (((cjElt k * h⁻¹)⁻¹ * (cjElt l * h⁻¹) : PG) : Equiv.Perm (Fin 100)) * r =
        r * (((cjElt k * h⁻¹)⁻¹ * (cjElt l * h⁻¹) : PG) : Equiv.Perm (Fin 100)) := hmem
    have e : (((cjElt k * h⁻¹)⁻¹ * (cjElt l * h⁻¹) : PG) : Equiv.Perm (Fin 100)) =
        (h : Equiv.Perm (Fin 100)) * (cjElt k : Equiv.Perm (Fin 100))⁻¹ *
          ((cjElt l : Equiv.Perm (Fin 100)) * (h : Equiv.Perm (Fin 100))⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, hr] at hc
    have h1 : (cjElt k : Equiv.Perm (Fin 100))⁻¹ * (cjElt l : Equiv.Perm (Fin 100)) * r₀ =
        r₀ * ((cjElt k : Equiv.Perm (Fin 100))⁻¹ * (cjElt l : Equiv.Perm (Fin 100))) := by
      calc _ = (h : Equiv.Perm (Fin 100))⁻¹ * ((h : Equiv.Perm (Fin 100)) *
              (cjElt k : Equiv.Perm (Fin 100))⁻¹ *
              ((cjElt l : Equiv.Perm (Fin 100)) * (h : Equiv.Perm (Fin 100))⁻¹) *
              ((h : Equiv.Perm (Fin 100)) * r₀ * (h : Equiv.Perm (Fin 100))⁻¹)) *
              (h : Equiv.Perm (Fin 100)) := by group
        _ = (h : Equiv.Perm (Fin 100))⁻¹ * (((h : Equiv.Perm (Fin 100)) * r₀ *
              (h : Equiv.Perm (Fin 100))⁻¹) * ((h : Equiv.Perm (Fin 100)) *
              (cjElt k : Equiv.Perm (Fin 100))⁻¹ *
              ((cjElt l : Equiv.Perm (Fin 100)) * (h : Equiv.Perm (Fin 100))⁻¹))) *
              (h : Equiv.Perm (Fin 100)) := by rw [hc]
        _ = _ := by group
    have h2 : (cjElt l : Equiv.Perm (Fin 100)) * r₀ * (cjElt l : Equiv.Perm (Fin 100))⁻¹ =
        (cjElt k : Equiv.Perm (Fin 100)) * r₀ * (cjElt k : Equiv.Perm (Fin 100))⁻¹ := by
      calc _ = (cjElt k : Equiv.Perm (Fin 100)) * ((cjElt k : Equiv.Perm (Fin 100))⁻¹ *
              (cjElt l : Equiv.Perm (Fin 100)) * r₀) * (cjElt l : Equiv.Perm (Fin 100))⁻¹ := by group
        _ = (cjElt k : Equiv.Perm (Fin 100)) * (r₀ * ((cjElt k : Equiv.Perm (Fin 100))⁻¹ *
              (cjElt l : Equiv.Perm (Fin 100)))) * (cjElt l : Equiv.Perm (Fin 100))⁻¹ := by rw [h1]
        _ = _ := by group
    have h3 := congrArg T h2
    rw [T_cjElt_conj hr₀ l.2, T_cjElt_conj hr₀ k.2] at h3
    have hkl' : (k : ℕ) < cjConjs.length := by rw [hlen]; exact k.2
    have hll' : (l : ℕ) < cjConjs.length := by rw [hlen]; exact l.2
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hll',
      List.getElem?_eq_getElem hkl', Option.getD_some, Option.getD_some] at h3
    exact Fin.ext (cjConjs_nodup.getElem_inj_iff.mp h3).symm
  have hcard : 1100 ≤ Nat.card (PG ⧸ CPG r) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hmul := (CPG r).card_mul_index
  rw [Subgroup.index_eq_card, show Nat.card PG = 44352000 from card_hs100P] at hmul
  nlinarith [Nat.card_pos (α := ↥(CPG r))]

theorem a8_centralizer {r₀ : Equiv.Perm (Fin 100)} (hr₀ : T r₀ = r0Tab) (h : PG) :
    IsSimpleGroup ↥(perfectCore
        (CPG ((h : Equiv.Perm (Fin 100)) * r₀ * (h : Equiv.Perm (Fin 100))⁻¹))) ∧
      Nat.card ↥(perfectCore
        (CPG ((h : Equiv.Perm (Fin 100)) * r₀ * (h : Equiv.Perm (Fin 100))⁻¹))) = 20160 := by
  obtain ⟨K, hK, hKC⟩ := moore_K hr₀
  set r : Equiv.Perm (Fin 100) := (h : Equiv.Perm (Fin 100)) * r₀ * (h : Equiv.Perm (Fin 100))⁻¹
    with hr
  let f : PG →* PG := (MulAut.conj h).toMonoidHom
  let Q : Subgroup PG := K.map f
  have hQ : Nonempty (alternatingGroup (Fin 8) ≃* Q) := by
    obtain ⟨e⟩ := hK
    exact ⟨e.trans (K.equivMapOfInjective f (MulAut.conj h).injective)⟩
  have hQC : Q ≤ CPG r := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' := hKC hk
    have hk'' : (k : Equiv.Perm (Fin 100)) * r₀ = r₀ * (k : Equiv.Perm (Fin 100)) := hk'
    show ((f k : PG) : Equiv.Perm (Fin 100)) * r = r * ((f k : PG) : Equiv.Perm (Fin 100))
    have e : (f k : PG) = h * k * h⁻¹ := by simp [f, MulAut.conj_apply]
    rw [e, hr]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc _ = (h : Equiv.Perm (Fin 100)) * ((k : Equiv.Perm (Fin 100)) * r₀) *
          (h : Equiv.Perm (Fin 100))⁻¹ := by group
      _ = (h : Equiv.Perm (Fin 100)) * (r₀ * (k : Equiv.Perm (Fin 100))) *
          (h : Equiv.Perm (Fin 100))⁻¹ := by rw [hk'']
      _ = _ := by group
  have hpc := perfectCore_eq_of_a8 hQC hQ (card_CPG_le hr₀ h)
  rw [hpc]
  obtain ⟨e⟩ := hQ
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨e.symm.isSimpleGroup, card_alt8 ⟨e⟩⟩

end CFSG.Quasithin.H13.LocDbl.HSLoc
