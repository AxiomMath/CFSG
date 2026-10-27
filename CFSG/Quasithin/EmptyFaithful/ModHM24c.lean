module

public import CFSG.Quasithin.EmptyFaithful.ModHM24b

public section

namespace CFSG.Quasithin.ModH.M24c

open CFSG.Quasithin.ModH.S24 CFSG.Quasithin.ModH.M24b CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.ModG (ev ev_mem ev_append ev_invW ev_nil ev_cons invW)
open CFSG.Quasithin

theorem map_c_inv_evg {H : Type*} [Group H] (c : H → ℕ) (comp : ℕ → ℕ → ℕ) (kId : ℕ)
    (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId) (A : List H) (r : ℕ)
    (hA : ∀ l < r, A.getD (l + r) 1 = (A.getD l 1)⁻¹) (ws : List (List ℕ))
    (hw : ∀ w ∈ ws, ∀ l ∈ w, l < 2 * r) :
    ((ws.map (ev A)).map fun x => x⁻¹).map c = ws.map fun w => evcg comp kId (A.map c) (invW r w) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro w hw'
  simp only [Function.comp]
  rw [← ev_invW hA w (hw w hw')]
  exact c_evg c comp kId hmul hone A _

theorem alph_inv : ∀ l < 2, alph.getD (l + 2) 1 = (alph.getD l 1)⁻¹ := by
  intro l hl
  interval_cases l <;> rfl

theorem cd_ev_alph (w : List ℕ) : cd (ev alph w) = evcg (compn 24) (kIdn 24) aC w := by
  rw [c_evg cd (compn 24) (kIdn 24) cd_mul cd_one, alph_codes]

theorem gW_letters : ∀ v ∈ gW, ∀ l ∈ v, l < 4 := by decide +kernel

@[expose] def gCinv : List ℕ := gW.map fun v => evcg (compn 24) (kIdn 24) aC (invW 2 v)

theorem tg_inv_codes : (tg.map fun x => x⁻¹).map cd = gCinv := by
  have := map_c_inv_evg cd (compn 24) (kIdn 24) cd_mul cd_one alph 2 alph_inv gW
    (fun w hw l hl => by have := gW_letters w hw l hl; omega)
  rw [alph_codes] at this
  exact this

theorem mem_normalizer_of_gens {H : Type} [Group H] [Finite H] {N : Subgroup H} (ngens : List H)
    (hN : N = Subgroup.closure {x | x ∈ ngens}) {g : H} (hg : ∀ n ∈ ngens, g * n * g⁻¹ ∈ N) :
    g ∈ Subgroup.normalizer (N : Set H) := by
  have hle : N ≤ N.comap (MulAut.conj g).toMonoidHom := by
    have h2 : Subgroup.closure {x | x ∈ ngens} ≤ N.comap (MulAut.conj g).toMonoidHom :=
      (Subgroup.closure_le _).2 fun n hn => hg n hn
    exact hN.le.trans h2
  have hmap : N.map (MulAut.conj g).toMonoidHom ≤ N := Subgroup.map_le_iff_le_comap.2 hle
  have hcard : Nat.card ↥N ≤ Nat.card ↥(N.map (MulAut.conj g).toMonoidHom) :=
    (Nat.card_congr (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).le
  have heq : N.map (MulAut.conj g).toMonoidHom = N := Subgroup.eq_of_le_of_card_ge hmap hcard
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hmap ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨n, hn, hnx⟩ := hx
    have : n = x := (MulAut.conj g).injective hnx
    rw [← this]
    exact hn

structure ZData where
  zW : List ℕ
  repW : List (List ℕ)
  ngW : List (List ℕ)
  nW : List (List ℕ)
  nK : List ℕ
  wW : List ℕ
  yW : List ℕ

namespace ZData

variable (d : ZData)

@[expose] def z : G := ev alph d.zW

@[expose] def gens : List G := d.z :: tg

@[expose] def A10 : List G := d.gens ++ d.gens.map fun x => x⁻¹

@[expose] def Zg : Subgroup G := Subgroup.closure {x | x ∈ d.gens}

@[expose] def rep : List G := d.repW.map (ev d.A10)

@[expose] def ng : List G := d.ngW.map (ev tg)

@[expose] def Ng : Subgroup G := Subgroup.closure {x | x ∈ d.ng}

@[expose] def w : G := ev alph d.wW

@[expose] def y : G := ev d.A10 d.yW

@[expose] def cz : ℕ := evcg (compn 24) (kIdn 24) aC d.zW

@[expose] def czi : ℕ := evcg (compn 24) (kIdn 24) aC (invW 2 d.zW)

@[expose] def codes10 : List ℕ := (d.cz :: gC) ++ (d.czi :: gCinv)

@[expose] def repC : List ℕ := d.repW.map (evcg (compn 24) (kIdn 24) d.codes10)

@[expose] def repCi : List ℕ :=
  d.repW.map fun u => evcg (compn 24) (kIdn 24) d.codes10 (invW 5 u)

@[expose] def ngC : List ℕ := d.ngW.map (evcg (compn 24) (kIdn 24) gC)

@[expose] def cw : ℕ := evcg (compn 24) (kIdn 24) aC d.wW

@[expose] def cwi : ℕ := evcg (compn 24) (kIdn 24) aC (invW 2 d.wW)

@[expose] def cy : ℕ := evcg (compn 24) (kIdn 24) d.codes10 d.yW

abbrev Check : Prop :=
  (∀ l ∈ d.zW, l < 4) ∧ (∀ l ∈ d.wW, l < 4) ∧
  d.repW.length = 9 ∧ d.repW.head? = some [] ∧ (∀ u ∈ d.repW, ∀ l ∈ u, l < 10) ∧
  (∀ i < 9, ∀ l < 5, ∃ j < 9,
    compn 24 (compn 24 (d.repC.getD i 0) (d.codes10.getD l 0)) (d.repCi.getD j 0) ∈ tK) ∧
  (∀ i < 9, ∀ j < 9, i ≠ j → compn 24 (d.repC.getD i 0) (d.repCi.getD j 0) ∉ tK) ∧
  (∀ u ∈ d.ngW, ∀ l ∈ u, l < 4) ∧ (∀ c ∈ d.ngC, c ∈ tK) ∧
  d.nW.map (evcg (compn 24) (kIdn 24) d.ngC) = d.nK ∧ kIdn 24 ∈ d.nK ∧
  (∀ k ∈ d.nK, ∀ g ∈ d.ngC, compn 24 k g ∈ d.nK) ∧ d.nK.Nodup ∧ (∃ c ∈ d.ngC, c ≠ kIdn 24) ∧
  (∀ l < 5, ∀ c ∈ d.ngC, compn 24 (compn 24 (d.codes10.getD l 0) c) (d.codes10.getD (l + 5) 0) ∈ d.nK) ∧
  (∀ c ∈ d.ngC, compn 24 (compn 24 d.cw c) d.cwi ∈ d.nK) ∧
  (∀ l ∈ d.yW, l < 5) ∧ compn 24 (compn 24 d.cy d.cy) d.cy = kIdn 24 ∧ d.cy ≠ kIdn 24 ∧
  (∀ i < 9, compn 24 (compn 24 (compn 24 d.cw d.cy) d.cwi) (d.repCi.getD i 0) ∉ tK)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (d : ZData) : Decidable d.Check := by
  unfold Check
  infer_instance

structure CheckF (d : ZData) : Prop where
  zlet : ∀ l ∈ d.zW, l < 4
  wlet : ∀ l ∈ d.wW, l < 4
  replen : d.repW.length = 9
  repnil : d.repW.head? = some []
  replet : ∀ u ∈ d.repW, ∀ l ∈ u, l < 10
  hstep : ∀ i < 9, ∀ l < 5, ∃ j < 9,
    compn 24 (compn 24 (d.repC.getD i 0) (d.codes10.getD l 0)) (d.repCi.getD j 0) ∈ tK
  hdist : ∀ i < 9, ∀ j < 9, i ≠ j → compn 24 (d.repC.getD i 0) (d.repCi.getD j 0) ∉ tK
  nglet : ∀ u ∈ d.ngW, ∀ l ∈ u, l < 4
  ngsg : ∀ c ∈ d.ngC, c ∈ tK
  nKeq : d.nW.map (evcg (compn 24) (kIdn 24) d.ngC) = d.nK
  nK1 : kIdn 24 ∈ d.nK
  nKcl : ∀ k ∈ d.nK, ∀ g ∈ d.ngC, compn 24 k g ∈ d.nK
  nKnd : d.nK.Nodup
  ngne : ∃ c ∈ d.ngC, c ≠ kIdn 24
  nnorm : ∀ l < 5, ∀ c ∈ d.ngC,
    compn 24 (compn 24 (d.codes10.getD l 0) c) (d.codes10.getD (l + 5) 0) ∈ d.nK
  wnorm : ∀ c ∈ d.ngC, compn 24 (compn 24 d.cw c) d.cwi ∈ d.nK
  ylet : ∀ l ∈ d.yW, l < 5
  y3 : compn 24 (compn 24 d.cy d.cy) d.cy = kIdn 24
  y1 : d.cy ≠ kIdn 24
  wy : ∀ i < 9, compn 24 (compn 24 (compn 24 d.cw d.cy) d.cwi) (d.repCi.getD i 0) ∉ tK

theorem Check.toF {d : ZData} (h : d.Check) : d.CheckF := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩

variable {d}

theorem cd_z : cd d.z = d.cz := cd_ev_alph _

theorem cd_zi (h : d.Check) : cd d.z⁻¹ = d.czi := by
  have hz : (d.z)⁻¹ = ev alph (invW 2 d.zW) :=
    (ev_invW alph_inv d.zW (fun l hl => by have := h.1 l hl; omega)).symm
  rw [hz]
  exact cd_ev_alph _

theorem gens_length : d.gens.length = 5 := by
  have : tg.length = 4 := by simp [tg, gW]
  simp only [gens, List.length_cons]
  omega

theorem A10_codes (h : d.Check) : d.A10.map cd = d.codes10 := by
  have e1 : (d.z :: tg).map cd = d.cz :: gC := by rw [List.map_cons, cd_z, tg_codes]
  have e2 : ((d.z :: tg).map fun x => x⁻¹).map cd = d.czi :: gCinv := by
    rw [List.map_cons, List.map_cons, cd_zi h, tg_inv_codes]
  show ((d.z :: tg) ++ (d.z :: tg).map fun x => x⁻¹).map cd = (d.cz :: gC) ++ (d.czi :: gCinv)
  rw [List.map_append, e1, e2]

theorem A10_inv : ∀ l < 5, d.A10.getD (l + 5) 1 = (d.A10.getD l 1)⁻¹ := by
  intro l hl
  have hlen : d.gens.length = 5 := gens_length
  have h1 : d.A10.getD (l + 5) 1 = (d.gens.map fun x => x⁻¹).getD l 1 := by
    have := List.getD_append_right d.gens (d.gens.map fun x => x⁻¹) 1 (l + 5) (by omega)
    rw [show d.A10 = d.gens ++ (d.gens.map fun x => x⁻¹) from rfl, this, hlen]
    simp
  have h2 : d.A10.getD l 1 = d.gens.getD l 1 :=
    List.getD_append d.gens (d.gens.map fun x => x⁻¹) 1 l (by omega)
  have h3 : (d.gens.map fun x => x⁻¹).getD l 1 = (d.gens.getD l 1)⁻¹ := by
    have := List.getD_map (fun x : G => x⁻¹) (l := d.gens) (d := (1 : G)) (n := l)
    simpa using this
  rw [h1, h2, h3]

theorem cd_ev_A10 (h : d.Check) (u : List ℕ) :
    cd (ev d.A10 u) = evcg (compn 24) (kIdn 24) d.codes10 u := by
  rw [c_evg cd (compn 24) (kIdn 24) cd_mul cd_one, A10_codes h]

theorem ev_A10_inv {u : List ℕ} (hu : ∀ l ∈ u, l < 10) : (ev d.A10 u)⁻¹ = ev d.A10 (invW 5 u) :=
  (ev_invW A10_inv u (fun l hl => by have := hu l hl; omega)).symm

theorem mem_Zg_of_A10 : ∀ x ∈ d.A10, x ∈ d.Zg := by
  intro x hx
  simp only [A10, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨g, hg, rfl⟩
  · exact Subgroup.subset_closure hx
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure hg)

theorem cd_rep (h : d.Check) {i : ℕ} (hi : i < 9) : cd (d.rep.getD i 1) = d.repC.getD i 0 := by
  have hi' : i < d.repW.length := by rw [h.2.2.1]; exact hi
  rw [rep, repC, List.getD_eq_getElem _ _ (by simpa using hi'),
    List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_map, cd_ev_A10 h]

theorem cd_rep_inv (h : d.Check) {i : ℕ} (hi : i < 9) :
    cd (d.rep.getD i 1)⁻¹ = d.repCi.getD i 0 := by
  have hi' : i < d.repW.length := by rw [h.2.2.1]; exact hi
  have hl : ∀ l ∈ d.repW[i], l < 10 := h.2.2.2.2.1 _ (List.getElem_mem hi')
  rw [rep, repCi, List.getD_eq_getElem _ _ (by simpa using hi'),
    List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_map,
    ev_A10_inv hl, cd_ev_A10 h]

theorem sg_le_Zg : Sg ≤ d.Zg := by
  apply Subgroup.closure_mono
  intro x hx
  exact List.mem_cons_of_mem _ hx

theorem rep_mem : ∀ w ∈ d.rep, w ∈ d.Zg := by
  intro w hw
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hw
  exact ev_mem mem_Zg_of_A10 u

theorem one_mem_rep (h : d.Check) : (1 : G) ∈ d.rep := by
  have hh : d.repW.head? = some [] := h.2.2.2.1
  have hmem : ([] : List ℕ) ∈ d.repW := by
    cases hrep : d.repW with
    | nil => rw [hrep] at hh; simp at hh
    | cons u us =>
      rw [hrep] at hh
      simp only [List.head?_cons, Option.some.injEq] at hh
      rw [← hh]
      exact List.mem_cons_self
  exact List.mem_map.2 ⟨[], hmem, ev_nil _⟩

theorem codes10_length : d.codes10.length = 10 := by
  have h1 : gC.length = 4 := by simp [gC]
  have h2 : gCinv.length = 4 := by simp [gCinv, gW]
  simp [codes10, h1, h2]

theorem cd_A10_getD (h : d.Check) {l : ℕ} (hl : l < 10) :
    cd (d.A10.getD l 1) = d.codes10.getD l 0 := by
  have h1 := List.getD_map cd (l := d.A10) (d := (1 : G)) (n := l)
  rw [A10_codes h, cd_one] at h1
  rw [← h1]
  have hl' : l < d.codes10.length := by rw [codes10_length]; exact hl
  rw [List.getD_eq_getElem _ _ hl', List.getD_eq_getElem _ _ hl']

theorem rep_step (h : d.Check) : ∀ w ∈ d.rep, ∀ g ∈ d.gens, ∃ w' ∈ d.rep, w * g * w'⁻¹ ∈ Sg := by
  intro w hw g hg
  have hlen : d.repW.length = 9 := h.2.2.1
  have hrep : d.rep.length = 9 := by simp [rep, hlen]
  obtain ⟨i, hi, hwi⟩ := List.mem_iff_getElem.1 hw
  have hwi' : w = d.rep.getD i 1 := by rw [List.getD_eq_getElem _ _ hi, hwi]
  obtain ⟨l, hl, hgl⟩ := List.mem_iff_getElem.1 hg
  have hgl' : g = d.gens.getD l 1 := by rw [List.getD_eq_getElem _ _ hl, hgl]
  have hi9 : i < 9 := by omega
  have hl5 : l < 5 := by have := gens_length (d := d); omega
  obtain ⟨j, hj, hjt⟩ := h.2.2.2.2.2.1 i hi9 l hl5
  have hj' : j < d.rep.length := by omega
  refine ⟨d.rep.getD j 1, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  · rw [mem_Sg_iff, cd_mul, cd_mul, hwi', hgl', cd_rep h hi9, cd_rep_inv h hj]
    have hA : d.A10.getD l 1 = d.gens.getD l 1 :=
      List.getD_append d.gens (d.gens.map fun x => x⁻¹) 1 l hl
    rw [← hA, cd_A10_getD h (by omega)]
    exact hjt

theorem rep_dist (h : d.Check) (i j : Fin d.rep.length) (hij : i ≠ j) :
    d.rep[i] * (d.rep[j])⁻¹ ∉ Sg := by
  have hlen : d.repW.length = 9 := h.2.2.1
  have hrep : d.rep.length = 9 := by simp [rep, hlen]
  have hi9 : (i : ℕ) < 9 := by have := i.2; omega
  have hj9 : (j : ℕ) < 9 := by have := j.2; omega
  have hne : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
  rw [mem_Sg_iff, cd_mul]
  have e1 : cd (d.rep[i]) = d.repC.getD i 0 := by
    rw [← cd_rep h hi9, List.getD_eq_getElem _ _ i.2]
    rfl
  have e2 : cd (d.rep[j])⁻¹ = d.repCi.getD j 0 := by
    rw [← cd_rep_inv h hj9, List.getD_eq_getElem _ _ j.2]
    rfl
  rw [e1, e2]
  exact h.2.2.2.2.2.2.1 i hi9 j hj9 hne

theorem mem_Zg_iff (h : d.Check) (x : G) :
    x ∈ d.Zg ↔ ∃ i < 9, compn 24 (cd x) (d.repCi.getD i 0) ∈ tK := by
  have hlen : d.repW.length = 9 := h.2.2.1
  have hrep : d.rep.length = 9 := by simp [rep, hlen]
  have hcos := mem_closure_iff_cosets d.gens d.rep sg_le_Zg rep_mem ⟨1, one_mem_rep h, Subgroup.one_mem _⟩
    (rep_step h) x
  refine hcos.trans ⟨?_, ?_⟩
  · rintro ⟨w, hw, hxw⟩
    obtain ⟨i, hi, hwi⟩ := List.mem_iff_getElem.1 hw
    have hwi' : w = d.rep.getD i 1 := by rw [List.getD_eq_getElem _ _ hi, hwi]
    refine ⟨i, by omega, ?_⟩
    rw [hwi', mem_Sg_iff, cd_mul, cd_rep_inv h (by omega)] at hxw
    exact hxw
  · rintro ⟨i, hi, hxi⟩
    refine ⟨d.rep.getD i 1, ?_, ?_⟩
    · have hi' : i < d.rep.length := by omega
      rw [List.getD_eq_getElem _ _ hi']
      exact List.getElem_mem hi'
    · rw [mem_Sg_iff, cd_mul, cd_rep_inv h hi]
      exact hxi

theorem card_Zg (h : d.Check) : Nat.card ↥d.Zg = 9216 := by
  have hlen : d.repW.length = 9 := h.2.2.1
  have hrep : d.rep.length = 9 := by simp [rep, hlen]
  have := card_closure_cosets d.gens d.rep sg_le_Zg rep_mem ⟨1, one_mem_rep h, Subgroup.one_mem _⟩
    (rep_step h) (rep_dist h)
  rw [show Subgroup.closure {y | y ∈ d.gens} = d.Zg from rfl, card_Sg, hrep] at this
  exact this

theorem ng_codes : d.ng.map cd = d.ngC := by
  have := map_c_evg cd (compn 24) (kIdn 24) cd_mul cd_one tg d.ngW
  rw [tg_codes] at this
  exact this

theorem mem_Ng_iff (h : d.Check) (x : G) : x ∈ d.Ng ↔ cd x ∈ d.nK := by
  have hF := h.toF
  refine mem_closure_iff_code cd (compn 24) (kIdn 24) cd_mul cd_one cd_injective d.ng d.nW d.nK ?_
    hF.nK1 ?_ x
  · rw [ng_codes]
    exact hF.nKeq
  · intro k hk g hg
    have : cd g ∈ d.ngC := by
      rw [← ng_codes]
      exact List.mem_map_of_mem hg
    exact hF.nKcl k hk _ this

theorem ng_mem_Sg (h : d.Check) : ∀ n ∈ d.ng, n ∈ Sg := by
  intro n hn
  rw [mem_Sg_iff]
  apply h.toF.ngsg
  rw [← ng_codes]
  exact List.mem_map_of_mem hn

theorem Ng_le_Sg (h : d.Check) : d.Ng ≤ Sg := (Subgroup.closure_le _).2 fun n hn => ng_mem_Sg h n hn

theorem Ng_isPGroup (h : d.Check) : IsPGroup 2 ↥d.Ng := Sg_isPGroup.to_le (Ng_le_Sg h)

theorem Ng_ne_bot (h : d.Check) : d.Ng ≠ ⊥ := by
  obtain ⟨c, hc, hc1⟩ := h.toF.ngne
  rw [← ng_codes] at hc
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hc
  intro hbot
  have : n ∈ d.Ng := Subgroup.subset_closure hn
  rw [hbot, Subgroup.mem_bot] at this
  apply hc1
  rw [this, cd_one]

theorem cd_w : cd d.w = d.cw := cd_ev_alph _

theorem cd_wi (h : d.Check) : cd d.w⁻¹ = d.cwi := by
  have hw : (d.w)⁻¹ = ev alph (invW 2 d.wW) :=
    (ev_invW alph_inv d.wW (fun l hl => by have := h.toF.wlet l hl; omega)).symm
  rw [hw]
  exact cd_ev_alph _

theorem Zg_le_normalizer (h : d.Check) : d.Zg ≤ Subgroup.normalizer (d.Ng : Set G) := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  obtain ⟨l, hl, hgl⟩ := List.mem_iff_getElem.1 hg
  have hl5 : l < 5 := by have := gens_length (d := d); omega
  have hgl' : g = d.gens.getD l 1 := by rw [List.getD_eq_getElem _ _ hl, hgl]
  have hA : d.A10.getD l 1 = d.gens.getD l 1 :=
    List.getD_append d.gens (d.gens.map fun x => x⁻¹) 1 l hl
  apply mem_normalizer_of_gens d.ng rfl
  intro n hn
  show g * n * g⁻¹ ∈ d.Ng
  rw [mem_Ng_iff h, cd_mul, cd_mul, hgl', ← hA]
  have hcn : cd n ∈ d.ngC := by
    rw [← ng_codes]
    exact List.mem_map_of_mem hn
  have e1 : cd (d.A10.getD l 1) = d.codes10.getD l 0 := cd_A10_getD h (by omega)
  have e2 : cd ((d.A10.getD l 1)⁻¹) = d.codes10.getD (l + 5) 0 := by
    rw [← A10_inv l hl5]
    exact cd_A10_getD h (by omega)
  rw [e1, e2]
  exact h.toF.nnorm l hl5 _ hcn

theorem w_mem_normalizer (h : d.Check) : d.w ∈ Subgroup.normalizer (d.Ng : Set G) := by
  apply mem_normalizer_of_gens d.ng rfl
  intro n hn
  show d.w * n * d.w⁻¹ ∈ d.Ng
  rw [mem_Ng_iff h, cd_mul, cd_mul, cd_w, cd_wi h]
  have hcn : cd n ∈ d.ngC := by
    rw [← ng_codes]
    exact List.mem_map_of_mem hn
  exact h.toF.wnorm _ hcn

theorem cd_y (h : d.Check) : cd d.y = d.cy := cd_ev_A10 h _

theorem y_mem : d.y ∈ d.Zg := ev_mem mem_Zg_of_A10 d.yW

theorem y_odd (h : d.Check) : Odd (orderOf d.y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : d.y ^ 3 = 1 := by
    apply cd_injective
    rw [cd_one, pow_three', cd_mul, cd_mul, cd_y h]
    exact h.toF.y3
  have h1 : d.y ≠ 1 := fun e => h.toF.y1 (by rw [← cd_y h, e, cd_one])
  rw [orderOf_eq_prime h3 h1]
  decide

theorem wy_not_mem (h : d.Check) : d.w * d.y * d.w⁻¹ ∉ d.Zg := by
  rw [mem_Zg_iff h]
  rintro ⟨i, hi, hmem⟩
  rw [cd_mul, cd_mul, cd_w, cd_wi h, cd_y h] at hmem
  exact h.toF.wy i hi hmem

structure Facts (d : ZData) : Prop where
  card : Nat.card ↥d.Zg = 9216
  sg_le : Sg ≤ d.Zg
  z_mem : d.z ∈ d.Zg
  mem : ∀ x : G, x ∈ d.Zg ↔ ∃ i < 9, compn 24 (cd x) (d.repCi.getD i 0) ∈ tK
  normalizes : d.Zg ≤ Subgroup.normalizer (d.Ng : Set G)
  ngp : IsPGroup 2 ↥d.Ng
  ng_ne : d.Ng ≠ ⊥
  w_norm : d.w ∈ Subgroup.normalizer (d.Ng : Set G)
  y_mem : d.y ∈ d.Zg
  y_odd : Odd (orderOf d.y)
  wy : d.w * d.y * d.w⁻¹ ∉ d.Zg

theorem Check.facts (h : d.Check) : d.Facts :=
  ⟨card_Zg h, sg_le_Zg, Subgroup.subset_closure List.mem_cons_self, mem_Zg_iff h,
    Zg_le_normalizer h, Ng_isPGroup h, Ng_ne_bot h, w_mem_normalizer h, y_mem, y_odd h, wy_not_mem h⟩

end ZData

end CFSG.Quasithin.ModH.M24c
