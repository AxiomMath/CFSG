module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Str
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Sylow3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocInter
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM3Orb

public section

namespace CFSG.Quasithin.J4M2

open scoped commutatorElement

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.J4Rad

theorem le_Hj_of_stab0
    (hF : J4Facts) {Y : Subgroup J} (hYM : Y ≤ M2)
    (hY : ∀ (y : J) (hy : y ∈ Y), rho hF ⟨y, hYM hy⟩ ∈ Stab0) : Y ≤ Hj :=
  fun y hy => (rho_zero_iff hF ⟨y, hYM hy⟩).1 (Stab0_iff.1 (hY y hy))

theorem ptElt_inv_mul_mem_Hj
    (hF : J4Facts) (y : ↥M2) (i j : Fin 77) (h : rho hF y i = j) :
    (ptElt j)⁻¹ * ((y : J) * ptElt i) ∈ Hj := by
  have h1 := (rho_spec hF y i j).1 h
  have h2 : (y : J) • pt i = (((y : J) * ptElt i : J) : J ⧸ Hj) := rfl
  rw [h2] at h1
  exact QuotientGroup.eq.1 h1.symm

theorem V0_le_conjSub_of_mem
    (hM : MatFacts) {i : ℕ} (hi : i < 77) (h : i ∈ i5List) :
    V0 ≤ conjSub (ptElt i) (Eg uJ 11) :=
  (v0_le_conj_iff hM ⟨i, hi⟩).2 h

theorem Ig_ptElt_29
    (hF : J4Facts) : Ig (ptElt 29) = (V0 : Set J) := by
  have hM := hF.mat
  have h29 : V0 ≤ conjSub (ptElt 29) (Eg uJ 11) :=
    V0_le_conjSub_of_mem hM (by norm_num) (by simp [i5List])
  have h0 : V0 ≤ conjSub (ptElt 0) (Eg uJ 11) :=
    V0_le_conjSub_of_mem hM (by norm_num) (by simp [i5List])
  rw [ptElt_zero, conjSub_one] at h0
  have hsub : (V0 : Set J) ⊆ Ig (ptElt 29) := by
    intro x hx
    exact ⟨h0 hx, mem_conjSub.1 (h29 hx)⟩
  have hng : ptElt 29 ∉ Hj := by
    rw [ptElt_mem_Hj_iff hF (by norm_num)]
    norm_num
  have hc8 : (Ig (ptElt 29)).ncard ≤ 8 := CFSG.Sporadic.J4.QT2.card_inter_le hF hng
  have hn : (V0 : Set J).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact card_V0 hM
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hn]; exact hc8) (Set.toFinite _)).symm

theorem mem_i5Fin_iff : ∀ j : Fin 77, j ∈ i5Fin ↔ j.val ∈ i5List := by decide +kernel

theorem le_normalizer_V0
    (hF : J4Facts)
    {Y : Subgroup J} (hYM : Y ≤ M2)
    (hY : ∀ (y : J) (hy : y ∈ Y), rho hF ⟨y, hYM hy⟩ ∈ StabI5) :
    Y ≤ Subgroup.normalizer (V0 : Set J) := by
  have hM := hF.mat
  have key : ∀ y ∈ Y, ∀ x ∈ V0, y * x * y⁻¹ ∈ V0 := by
    intro y hy x hx
    have hconj : ∀ j : ℕ, ∀ hj : j < 77, j ∈ i5List →
        y * x * y⁻¹ ∈ conjSub (ptElt j) (Eg uJ 11) := by
      intro j hj hjI
      have hyinv : y⁻¹ ∈ Y := Y.inv_mem hy
      have hjF : (⟨j, hj⟩ : Fin 77) ∈ i5Fin := (mem_i5Fin_iff ⟨j, hj⟩).2 hjI
      obtain ⟨i, hiI, hyi⟩ : ∃ i : Fin 77, i ∈ i5Fin ∧ rho hF ⟨y, hYM hy⟩ i = ⟨j, hj⟩ := by
        refine ⟨rho hF ⟨y⁻¹, hYM hyinv⟩ ⟨j, hj⟩, (mem_StabI5_iff.1 (hY y⁻¹ hyinv)) _ hjF, ?_⟩
        rw [← Equiv.Perm.mul_apply, ← map_mul]
        have : (⟨y, hYM hy⟩ : ↥M2) * ⟨y⁻¹, hYM hyinv⟩ = 1 := Subtype.ext (mul_inv_cancel y)
        rw [this, map_one, Equiv.Perm.one_apply]
      have hmem := ptElt_inv_mul_mem_Hj hF ⟨y, hYM hy⟩ i ⟨j, hj⟩ hyi
      have hxi : (ptElt i.val)⁻¹ * x * ptElt i.val ∈ Eg uJ 11 :=
        mem_conjSub.1 (V0_le_conjSub_of_mem hM i.2 ((mem_i5Fin_iff i).1 hiI) hx)
      refine mem_conjSub.2 ?_
      have e : (ptElt j)⁻¹ * (y * x * y⁻¹) * ptElt j =
          ((ptElt j)⁻¹ * (y * ptElt i.val)) * ((ptElt i.val)⁻¹ * x * ptElt i.val) *
            ((ptElt j)⁻¹ * (y * ptElt i.val))⁻¹ := by group
      rw [e]
      exact Hj_normalizes_Eg hM _ hmem _ hxi
    have h0 := hconj 0 (by norm_num) (by simp [i5List])
    have h29 := hconj 29 (by norm_num) (by simp [i5List])
    rw [ptElt_zero, conjSub_one] at h0
    have hmem : y * x * y⁻¹ ∈ Ig (ptElt 29) := ⟨h0, mem_conjSub.1 h29⟩
    rw [Ig_ptElt_29 hF] at hmem
    exact hmem
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key y hy h hh
  · intro hh
    have h1 := key y⁻¹ (Y.inv_mem hy) _ hh
    have e : y⁻¹ * (y * h * y⁻¹) * (y⁻¹)⁻¹ = h := by group
    rw [e] at h1
    exact h1

theorem eq_top_of_sup_ker {M : Type*} [Group M] [Finite M] (K Y Q : Subgroup M) [K.Normal]
    (hYK : Y ⊔ K = ⊤) {m : ℕ} (hM : Nat.card M = 27 * m) (hm : ¬ 3 ∣ m)
    (hK : Nat.card K = 3 * 2 ^ 13) (hQK : Q ≤ K) (hQcard : Nat.card Q = 2 ^ 13)
    (hQY : Q ≤ Y)
    (hnab : ∃ R : Subgroup M, Nat.card R = 27 ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) : Y = ⊤ := by
  have h3 : 3 ∣ Nat.card (Y ⊓ K : Subgroup M) :=
    three_dvd_card_inf K Y hYK hM hm (k := 2 ^ 13) hK (by norm_num) hnab
  have h2 : 2 ^ 13 ∣ Nat.card (Y ⊓ K : Subgroup M) := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le (le_inf hQY hQK)
  have hcop : Nat.Coprime 3 (2 ^ 13) := by norm_num
  have hdvd : 3 * 2 ^ 13 ∣ Nat.card (Y ⊓ K : Subgroup M) := hcop.mul_dvd_of_dvd_of_dvd h3 h2
  have hle : Nat.card (Y ⊓ K : Subgroup M) ≤ Nat.card K :=
    Subgroup.card_le_of_le inf_le_right
  have hpos : 0 < Nat.card (Y ⊓ K : Subgroup M) := Nat.card_pos
  have heq : Nat.card (Y ⊓ K : Subgroup M) = Nat.card K := by
    have := Nat.le_of_dvd hpos hdvd
    rw [hK] at hle ⊢
    omega
  have hKY : K ≤ Y := by
    have := Subgroup.eq_of_le_of_card_ge (inf_le_right : Y ⊓ K ≤ K) heq.ge
    rw [← this]
    exact inf_le_left
  rw [← hYK]
  exact (sup_eq_left.2 hKY).symm

theorem gE_twelve : gE 12 = aY := by
  have h : genWord 12 = aDw := by simp [genWord]
  unfold gE
  rw [h]
  rfl

theorem gE_thirteen : gE 13 = bY := by
  have h : genWord 13 = bDw := by simp [genWord]
  unfold gE
  rw [h]
  rfl

theorem exists_nonabelian_27
    (hF : J4Facts) :
    ∃ R : Subgroup ↥M2, Nat.card R = 27 ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
  have hM := hF.mat
  have hCz : Cz = M2 := by
    unfold Cz M2
    rw [zJ_eq]
  have hYM : Ycl ≤ M2 := hCz ▸ QT2A.Ycl_le_Cz hM
  have hcard : Nat.card (Ycl.subgroupOf M2) = 27 := by
    rw [← QT2A.card_Ycl hM]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv
  refine ⟨Ycl.subgroupOf M2, hcard, ⟨aY, hYM QT2A.aY_mem⟩, Subgroup.mem_subgroupOf.2 QT2A.aY_mem,
    ⟨bY, hYM QT2A.bY_mem⟩, Subgroup.mem_subgroupOf.2 QT2A.bY_mem, fun h => ?_⟩
  have h1 : aY * bY = bY * aY := by
    have h2 := congrArg Subtype.val h
    simpa only [Subgroup.coe_mul] using h2
  apply cE_ne_one hM
  rw [cE, gE_twelve, gE_thirteen, commutatorElement_eq_one_iff_mul_comm]
  exact h1

theorem eq_M2_of_map_eq
    (hF : J4Facts)
    {Y : Subgroup J} (hPY : P0 ≤ Y) (hYM : Y ≤ M2)
    (hY : (Y.subgroupOf M2).map (rho hF) = (rho hF).range) : Y = M2 := by
  have hsup := sup_eq_top_of_map_eq_range (rho hF) (Y.subgroupOf M2) hY
  have hQK : Qgrp.subgroupOf M2 ≤ (rho hF).ker := by
    intro q hq
    exact (rho_eq_one_iff hF q).2 (Qgrp_le_Kgrp (Subgroup.mem_subgroupOf.1 hq))
  have hQcard : Nat.card (Qgrp.subgroupOf M2) = 2 ^ 13 := by
    rw [← card_Qgrp hF.mat]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Qgrp_le_M2 hF.mat)).toEquiv
  have hQY : Qgrp.subgroupOf M2 ≤ Y.subgroupOf M2 :=
    fun x hx => Subgroup.mem_subgroupOf.2
      (((Qgrp_le_P0 hF).trans hPY) (Subgroup.mem_subgroupOf.1 hx))
  have htop : Y.subgroupOf M2 = ⊤ :=
    eq_top_of_sup_ker (rho hF).ker (Y.subgroupOf M2) (Qgrp.subgroupOf M2) hsup (m := 807403520)
      (by rw [card_M2 hF]) (by norm_num)
      (by rw [(card_range_ker_rho hF).2]; norm_num) hQK hQcard hQY (exists_nonabelian_27 hF)
  refine le_antisymm hYM fun m hm => ?_
  have : (⟨m, hm⟩ : ↥M2) ∈ Y.subgroupOf M2 := by
    rw [htop]
    trivial
  exact this

theorem mem_map_of_gE
    (hF : J4Facts) {n : ℕ} (hn : n < 32) {Y : Subgroup J}
    (hY : gE n ∈ Y) {x : Equiv.Perm (Fin 77)} (h : x = sigPerm n) :
    x ∈ (Y.subgroupOf M2).map (rho hF) := by
  refine ⟨⟨gE n, gE_mem_M2 hF.mat hn⟩, Subgroup.mem_subgroupOf.2 hY, ?_⟩
  rw [rho_gE_perm hF hn]
  exact h.symm

theorem gE_k_mem_P0 {i : ℕ} (hi : i < 4) : gE (28 + i) ∈ P0 := by
  rw [gE_k hi]
  exact kJ_mem_P0 hi

theorem gE_u_mem_P0 {j : ℕ} (hj : j < 11) :
    gE (17 + j) ∈ P0 := by
  rw [gE_u hj]
  exact Subgroup.subset_closure (Or.inl ⟨j, hj, rfl⟩)

theorem J4M2Lattice
    (hF : J4Facts)
    {Y : Subgroup J} (hPY : P0 ≤ Y) (hYM : Y ≤ M2) :
    Y ≤ Hj ∨ Y ≤ Subgroup.normalizer (V0 : Set J) ∨ Y = M2 := by
  have hT : Tbar ≤ (Y.subgroupOf M2).map (rho hF) := by
    rw [Tbar, Subgroup.closure_le]
    intro x hx
    simp only [tPerms, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hx
    rcases hx with h | h | h | h
    · exact mem_map_of_gE hF (n := 28) (by norm_num) (hPY (gE_k_mem_P0 (i := 0) (by norm_num))) h
    · exact mem_map_of_gE hF (n := 29) (by norm_num) (hPY (gE_k_mem_P0 (i := 1) (by norm_num))) h
    · exact mem_map_of_gE hF (n := 30) (by norm_num) (hPY (gE_k_mem_P0 (i := 2) (by norm_num))) h
    · exact mem_map_of_gE hF (n := 17) (by norm_num) (hPY (gE_u_mem_P0 (j := 0) (by norm_num))) h
  have hMb : (Y.subgroupOf M2).map (rho hF) ≤ Mbar := by
    rw [← range_rho_eq hF]
    exact Subgroup.map_le_range _ _
  rcases lattice_classification (card_Mbar hF) hT hMb with h | h | h
  · right
    right
    refine eq_M2_of_map_eq hF hPY hYM ?_
    rw [range_rho_eq hF]
    exact h
  · left
    exact le_Hj_of_stab0 hF hYM fun y hy => h ⟨⟨y, hYM hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  · right
    left
    exact le_normalizer_V0 hF hYM fun y hy => h ⟨⟨y, hYM hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩

end CFSG.Quasithin.J4M2
