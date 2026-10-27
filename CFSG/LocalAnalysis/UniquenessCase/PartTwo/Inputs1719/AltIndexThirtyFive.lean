module

public import CFSG.Quasithin.H13.L32AM50i
public import CFSG.Quasithin.H13.L32AC50e
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
public import CFSG.Literature.GL52Transport
public import CFSG.GroupTheory.PCore.PCoreOfIndex
public import CFSG.Quasithin.Vol2.Ch7Bridge326
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MaxParabolicTransport
import CFSG.GroupTheory.PElementSubgroupSubgroupOf

public section

open Equiv Equiv.Perm
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.H13.L32A.C.Alt7

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

private abbrev K5Perm := Equiv.Perm (Fin 7)
private abbrev K5Alt := alternatingGroup (Fin 7)

private def k5c123 : K5Perm := swap (1 : Fin 7) 2 * swap 2 3

private def e9v4List : List K5Perm := e9List.flatMap fun a => v4List.map fun b => a * b

private theorem e9v4_nodup : e9v4List.Nodup := by decide +kernel

private theorem e9v4_card : e9v4List.length = 36 := by decide +kernel

private theorem e9v4_closed : (1 : K5Perm) ∈ e9v4List ∧
    (∀ a ∈ e9v4List, ∀ b ∈ e9v4List, a * b ∈ e9v4List) ∧
      ∀ a ∈ e9v4List, a⁻¹ ∈ e9v4List := by
  have h : decide ((1 : K5Perm) ∈ e9v4List) = true ∧
      e9v4List.all (fun a => e9v4List.all fun b => decide (a * b ∈ e9v4List)) = true ∧
      e9v4List.all (fun a => decide (a⁻¹ ∈ e9v4List)) = true := by
    decide +kernel
  exact ⟨of_decide_eq_true h.1, of_all₂ h.2.1, of_all h.2.2⟩

private def e9v4Sub : Subgroup K5Perm := listSub e9v4List e9v4_closed

private theorem card_e9v4Sub : Nat.card e9v4Sub = 36 := by
  rw [e9v4Sub, card_listSub _ _ e9v4_nodup, e9v4_card]

private theorem mem_e9v4Sub {x : K5Perm} : x ∈ e9v4Sub ↔ x ∈ e9v4List := mem_listSub

private theorem card_v4Sub : Nat.card v4Sub = 4 := by
  rw [v4Sub, card_listSub _ _ v4_nodup.1, v4_nodup.2]

private theorem mem_v4Sub {x : K5Perm} : x ∈ v4Sub ↔ x ∈ v4List := mem_listSub

private theorem v4Sub_le_e9v4Sub : v4Sub ≤ e9v4Sub := by
  intro x hx
  rw [mem_e9v4Sub]
  rw [e9v4List, List.mem_flatMap]
  refine ⟨1, e9_closed.1, ?_⟩
  exact List.mem_map.mpr ⟨x, mem_listSub.mp hx, by simp⟩

private theorem mem_opp_two_of_sq {x : K5Perm} (hx : x ∈ stabSub) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    x ∈ Opp 2 stabSub := by
  rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup]
  refine Subgroup.subset_closure ⟨hx, 1, ?_⟩
  rw [orderOf_eq_prime hx2 hx1]
  norm_num

private theorem e9v4Sub_le_of_le (H : Subgroup K5Perm) (he : e9Sub ≤ H) (hv : v4Sub ≤ H) :
    e9v4Sub ≤ H := by
  intro x hx
  rw [mem_e9v4Sub, e9v4List, List.mem_flatMap] at hx
  obtain ⟨a, ha, hb⟩ := hx
  obtain ⟨b0, hb0, hbeq⟩ := List.mem_map.mp hb
  rw [← hbeq]
  exact H.mul_mem (he (mem_listSub.mpr ha)) (hv (mem_listSub.mpr hb0))

private def k5v1 : K5Perm := swap (0 : Fin 7) 1 * swap 2 3

private def k5v2 : K5Perm := swap (0 : Fin 7) 2 * swap 1 3

private def k5v3 : K5Perm := swap (0 : Fin 7) 3 * swap 1 2

private theorem v4List_eq : v4List = [1, k5v1, k5v2, k5v3] := by decide +kernel

private theorem k5v1_eq : k5v1 = c012 * k5c123 := by decide +kernel

private theorem k5v2_eq : k5v2 = k5c123 * c012 := by decide +kernel

private theorem k5v3_eq : k5v3 = k5v1 * k5v2 := by decide +kernel

private def oddList : List K5Perm := stabList.filter (fun x => decide (x ^ 3 = 1))

private theorem oddList_mem_stab : ∀ x ∈ oddList, x ∈ stabSub := by
  have h : oddList.all (fun x => decide (x ∈ stabList)) = true := by decide +kernel
  intro x hx
  exact mem_stabSub_iff.mpr (of_all h x hx)

private theorem c456_mem_oddList : c456 ∈ oddList := by
  rw [oddList, List.mem_filter]
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem c012_mem_oddList : c012 ∈ oddList := by
  rw [oddList, List.mem_filter]
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem c123_mem_oddList : k5c123 ∈ oddList := by
  rw [oddList, List.mem_filter]
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem odd_iff_cube {x : K5Perm} (hx : x ∈ stabSub) : Odd (orderOf x) ↔ x ^ 3 = 1 := by
  constructor
  · intro hodd
    have hdvd : orderOf x ∣ 12 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact stab_exp x (mem_stabSub_iff.mp hx)
    have hcop2 : Nat.Coprime (orderOf x) 2 := (Nat.coprime_two_left.mpr hodd).symm
    have hcop : Nat.Coprime (orderOf x) 4 := by
      simpa using Nat.Coprime.pow_right 2 hcop2
    have h12 : 12 = 4 * 3 := by norm_num
    rw [h12] at hdvd
    have hdvd3 : orderOf x ∣ 3 := hcop.dvd_of_dvd_mul_right hdvd
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd3
  · intro h3
    have hdvd : orderOf x ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact h3
    exact Odd.of_dvd_nat (by norm_num : Odd 3) hdvd

private theorem oddSet_eq_oddList :
    {x : K5Perm | x ∈ stabSub ∧ Odd (orderOf x)} =
      ((oddList.toFinset : Finset K5Perm) : Set K5Perm) := by
  ext x
  constructor
  · rintro ⟨hx, hodd⟩
    have hxlist : x ∈ stabList := mem_stabSub_iff.mp hx
    have h3 : x ^ 3 = 1 := (odd_iff_cube hx).mp hodd
    have hxL : x ∈ oddList := by
      rw [oddList, List.mem_filter]
      exact ⟨hxlist, by simpa using h3⟩
    simpa [Finset.mem_coe, List.mem_toFinset] using hxL
  · intro hx
    have hxL : x ∈ oddList := by
      simpa [Finset.mem_coe, List.mem_toFinset] using hx
    have hx3 : x ^ 3 = 1 := by
      have hxL' : x ∈ List.filter (fun x => decide (x ^ 3 = 1)) stabList := by
        simpa [oddList] using hxL
      exact of_decide_eq_true (List.mem_filter.mp hxL').2
    exact ⟨oddList_mem_stab x hxL, (odd_iff_cube (oddList_mem_stab x hxL)).mpr hx3⟩

private theorem oUpperTwo_eq_closure_odd :
    S17.oUpperTwo stabSub = Subgroup.closure ((oddList.toFinset : Finset K5Perm) : Set K5Perm) := by
  rw [S17.oUpperTwo_eq_closure, oddSet_eq_oddList]

private theorem oddList_subset_e9v4Sub : ∀ x ∈ oddList, x ∈ e9v4Sub := by
  have h : oddList.all (fun x => decide (x ∈ e9v4List)) = true := by decide +kernel
  intro x hx
  exact mem_e9v4Sub.mpr (of_all h x hx)

private theorem e9Sub_le_closure_odd :
    e9Sub ≤ Subgroup.closure ((oddList.toFinset : Finset K5Perm) : Set K5Perm) := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := mem_e9Sub.mp hx
  refine Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ i) (Subgroup.pow_mem _ ?_ j)
  · exact Subgroup.subset_closure (by simp [c012_mem_oddList])
  · exact Subgroup.subset_closure (by simp [c456_mem_oddList])

private theorem v4Sub_le_closure_odd :
    v4Sub ≤ Subgroup.closure ((oddList.toFinset : Finset K5Perm) : Set K5Perm) := by
  have h1 : k5v1 ∈ Subgroup.closure ((oddList.toFinset : Finset K5Perm) : Set K5Perm) := by
    rw [k5v1_eq]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp [c012_mem_oddList]))
      (Subgroup.subset_closure (by simp [c123_mem_oddList]))
  have h2 : k5v2 ∈ Subgroup.closure ((oddList.toFinset : Finset K5Perm) : Set K5Perm) := by
    rw [k5v2_eq]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp [c123_mem_oddList]))
      (Subgroup.subset_closure (by simp [c012_mem_oddList]))
  have h3 : k5v3 ∈ Subgroup.closure ((oddList.toFinset : Finset K5Perm) : Set K5Perm) := by
    rw [k5v3_eq]
    exact Subgroup.mul_mem _ h1 h2
  intro x hx
  rw [mem_v4Sub, v4List_eq] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact h1
  · exact h2
  · exact h3

private theorem oUpperTwo_stabSub_eq_e9v4Sub : S17.oUpperTwo stabSub = e9v4Sub := by
  rw [oUpperTwo_eq_closure_odd]
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le (K := e9v4Sub)).mpr ?_
    intro x hx
    exact oddList_subset_e9v4Sub x (by simpa using hx)
  · exact e9v4Sub_le_of_le _ e9Sub_le_closure_odd v4Sub_le_closure_odd

private theorem e9v4Sub_le_oUpperTwo_opp : e9v4Sub ≤ S17.oUpperTwo (Opp 2 stabSub) := by
  have hx1 : (swap (4 : Fin 7) 5 * swap 0 1) ∈ Opp 2 stabSub := by
    refine mem_opp_two_of_sq ?_ ?_ ?_
    · rw [mem_stabSub]; decide +kernel
    · decide +kernel
    · decide +kernel
  have hy1 : (swap (0 : Fin 7) 1 * swap 5 6) ∈ Opp 2 stabSub := by
    refine mem_opp_two_of_sq ?_ ?_ ?_
    · rw [mem_stabSub]; decide +kernel
    · decide +kernel
    · decide +kernel
  have hx2 : (swap (0 : Fin 7) 1 * swap 4 5) ∈ Opp 2 stabSub := by
    refine mem_opp_two_of_sq ?_ ?_ ?_
    · rw [mem_stabSub]; decide +kernel
    · decide +kernel
    · decide +kernel
  have hy2 : (swap (1 : Fin 7) 2 * swap 4 5) ∈ Opp 2 stabSub := by
    refine mem_opp_two_of_sq ?_ ?_ ?_
    · rw [mem_stabSub]; decide +kernel
    · decide +kernel
    · decide +kernel
  have hy3 : (swap (2 : Fin 7) 3 * swap 4 5) ∈ Opp 2 stabSub := by
    refine mem_opp_two_of_sq ?_ ?_ ?_
    · rw [mem_stabSub]; decide +kernel
    · decide +kernel
    · decide +kernel
  have hc456o : c456 ∈ Opp 2 stabSub := by
    have e : (swap (4 : Fin 7) 5 * swap 0 1) * (swap 0 1 * swap 5 6) = c456 := by
      decide +kernel
    rw [← e]
    exact (Opp 2 stabSub).mul_mem hx1 hy1
  have hc012o : c012 ∈ Opp 2 stabSub := by
    have e : (swap (0 : Fin 7) 1 * swap 4 5) * (swap 1 2 * swap 4 5) = c012 := by
      decide +kernel
    rw [← e]
    exact (Opp 2 stabSub).mul_mem hx2 hy2
  have hc123o : k5c123 ∈ Opp 2 stabSub := by
    have e : (swap (1 : Fin 7) 2 * swap 4 5) * (swap 2 3 * swap 4 5) = k5c123 := by
      decide +kernel
    rw [← e]
    exact (Opp 2 stabSub).mul_mem hy2 hy3
  have hc456 : c456 ∈ S17.oUpperTwo (Opp 2 stabSub) :=
    CFSG.Quasithin.mem_oTwoUpper_of_odd hc456o (by
      rw [orderOf_eq_prime (p := 3) (by decide +kernel) (by decide +kernel)]
      norm_num)
  have hc012 : c012 ∈ S17.oUpperTwo (Opp 2 stabSub) :=
    CFSG.Quasithin.mem_oTwoUpper_of_odd hc012o (by
      rw [orderOf_eq_prime (p := 3) (by decide +kernel) (by decide +kernel)]
      norm_num)
  have hc123 : k5c123 ∈ S17.oUpperTwo (Opp 2 stabSub) :=
    CFSG.Quasithin.mem_oTwoUpper_of_odd hc123o (by
      rw [orderOf_eq_prime (p := 3) (by decide +kernel) (by decide +kernel)]
      norm_num)
  have hv1 : k5v1 ∈ S17.oUpperTwo (Opp 2 stabSub) := by
    rw [k5v1_eq]; exact (S17.oUpperTwo (Opp 2 stabSub)).mul_mem hc012 hc123
  have hv2 : k5v2 ∈ S17.oUpperTwo (Opp 2 stabSub) := by
    rw [k5v2_eq]; exact (S17.oUpperTwo (Opp 2 stabSub)).mul_mem hc123 hc012
  have hv3 : k5v3 ∈ S17.oUpperTwo (Opp 2 stabSub) := by
    rw [k5v3_eq]; exact (S17.oUpperTwo (Opp 2 stabSub)).mul_mem hv1 hv2
  refine e9v4Sub_le_of_le _ ?_ ?_
  · intro x hx
    obtain ⟨i, j, rfl⟩ := mem_e9Sub.mp hx
    exact (S17.oUpperTwo (Opp 2 stabSub)).mul_mem
      ((S17.oUpperTwo (Opp 2 stabSub)).pow_mem hc012 i)
      ((S17.oUpperTwo (Opp 2 stabSub)).pow_mem hc456 j)
  · intro x hx
    rw [mem_v4Sub, v4List_eq] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hv1
    · exact hv2
    · exact hv3

private theorem oUpperTwo_opp_eq_e9v4Sub :
    S17.oUpperTwo (Opp 2 stabSub) = e9v4Sub := by
  refine le_antisymm ?_ e9v4Sub_le_oUpperTwo_opp
  rw [← oUpperTwo_stabSub_eq_e9v4Sub]
  exact CFSG.Quasithin.oTwoUpper_mono (F09.opp_le_self 2 stabSub)

private theorem card_v4Sub_subgroupOf :
    Nat.card ↥(v4Sub.subgroupOf e9v4Sub) = 4 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe v4Sub_le_e9v4Sub).toEquiv, card_v4Sub]

private instance v4Sub_subgroupOf_normal : (v4Sub.subgroupOf e9v4Sub).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : ((n : ↥e9v4Sub) : K5Perm) ∈ v4List := mem_listSub.mp hn
  have hg' : ((g : ↥e9v4Sub) : K5Perm) ∈ e9v4List := mem_listSub.mp g.2
  have h : e9v4List.all (fun a => v4List.all fun b =>
      decide (a * b * a⁻¹ ∈ v4List)) = true := by decide +kernel
  exact mem_listSub.mpr (of_all₂ h _ hg' _ hn')

private theorem relIndex_v4Sub_e9v4Sub : v4Sub.relIndex e9v4Sub = 9 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (v4Sub.subgroupOf e9v4Sub)
  rw [card_e9v4Sub, card_v4Sub_subgroupOf] at h
  have hq : Nat.card (↥e9v4Sub ⧸ v4Sub.subgroupOf e9v4Sub) = 9 := by
    have h' : Nat.card (↥e9v4Sub ⧸ v4Sub.subgroupOf e9v4Sub) * 4 = 9 * 4 := by
      rw [← h]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  exact hq

private theorem pCore_e9v4Sub_eq :
    CFSG.pCore 2 ↥e9v4Sub = v4Sub.subgroupOf e9v4Sub := by
  have hLK : v4Sub ≤ e9v4Sub := v4Sub_le_e9v4Sub
  have hKL : e9v4Sub ≤ Subgroup.normalizer (v4Sub : Set K5Perm) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mp v4Sub_subgroupOf_normal
  have hp : ¬ 2 ∣ v4Sub.relIndex e9v4Sub := by
    rw [relIndex_v4Sub_e9v4Sub]; norm_num
  have hcore : CFSG.Open.pCoreOf 2 e9v4Sub ≤ v4Sub :=
    CFSG.GroupTheory.pCoreOf_le_of_not_dvd_relIndex hLK hKL hp
  have hPle : CFSG.pCore 2 ↥e9v4Sub ≤ v4Sub.subgroupOf e9v4Sub := by
    intro x hx
    have hx' : ((x : ↥e9v4Sub) : K5Perm) ∈ CFSG.Open.pCoreOf 2 e9v4Sub :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (hcore hx')
  have hVJp : IsPGroup 2 (v4Sub.subgroupOf e9v4Sub) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [card_v4Sub_subgroupOf]
    norm_num
  have hVJle : v4Sub.subgroupOf e9v4Sub ≤ CFSG.pCore 2 ↥e9v4Sub := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (v4Sub.subgroupOf e9v4Sub)
      (le_iSup_of_le v4Sub_subgroupOf_normal (le_iSup_of_le hVJp le_rfl))
  exact le_antisymm hPle hVJle

private theorem e9v4Sub_quotient_exp_three :
    ∀ y : ↥e9v4Sub ⧸ v4Sub.subgroupOf e9v4Sub, y ^ 3 = 1 := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  have hx : ((x : ↥e9v4Sub) : K5Perm) ∈ e9v4List := mem_listSub.mp x.2
  have h3 : ((x : ↥e9v4Sub) : K5Perm) ^ 3 ∈ v4List := by
    have h : e9v4List.all (fun z => decide (z ^ 3 ∈ v4List)) = true := by decide +kernel
    exact of_all h _ hx
  exact Subgroup.mem_subgroupOf.mpr (mem_listSub.mpr h3)

private theorem stabSub_jzero :
    Nonempty (Bar2 (S17.oUpperTwo (Opp 2 stabSub)) ≃*
      Multiplicative (ZMod 3 × ZMod 3)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.H13.nonempty_mulEquiv_zmod_prod (p := 3)
    relIndex_v4Sub_e9v4Sub e9v4Sub_quotient_exp_three
  rw [oUpperTwo_opp_eq_e9v4Sub]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq pCore_e9v4Sub_eq).trans e⟩

private theorem taSub_le_alt : taSub ≤ K5Alt := by
  intro x hx
  rw [Equiv.Perm.mem_alternatingGroup]
  exact ta_sign x (mem_listSub.mp hx)

private theorem stabSub_le_alt : stabSub ≤ K5Alt := by
  intro x hx
  rw [Equiv.Perm.mem_alternatingGroup]
  exact (mem_stabSub.mp hx).1

private theorem exists_conj_map_eq_stabSub (Y' : Subgroup K5Alt) (hY' : Y'.index = 35) :
    ∃ g : K5Alt, Y'.map (MulAut.conj g).toMonoidHom = stabSub.subgroupOf K5Alt := by
  have hY'card : Nat.card Y' = 72 := by
    have h := Subgroup.card_mul_index Y'
    rw [hY', CFSG.ABGDGroups.card_alternatingGroup_fin_seven] at h
    omega
  let Q : Sylow 2 ↥Y' := Classical.choice (Sylow.nonempty (p := 2) (G := ↥Y'))
  let P : Subgroup K5Alt := (Q : Subgroup ↥Y').map Y'.subtype
  have hPle : P ≤ Y' := by
    intro x hx
    obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact q.2
  have hP2 : IsPGroup 2 P := Q.isPGroup'.map Y'.subtype
  have hPcard : Nat.card P = Nat.card (Q : Subgroup ↥Y') :=
    Subgroup.card_map_of_injective Y'.subtype_injective
  have hPindex : ¬ 2 ∣ P.index := by
    have h1 : Nat.card P * P.index = 2520 := by
      have := Subgroup.card_mul_index P
      rwa [CFSG.ABGDGroups.card_alternatingGroup_fin_seven] at this
    have h2 : Nat.card (Q : Subgroup ↥Y') * (Q : Subgroup ↥Y').index = 72 := by
      have := Subgroup.card_mul_index (Q : Subgroup ↥Y')
      rwa [hY'card] at this
    have h5 : Nat.card (Q : Subgroup ↥Y') * P.index =
        Nat.card (Q : Subgroup ↥Y') * (35 * (Q : Subgroup ↥Y').index) := by
      calc Nat.card (Q : Subgroup ↥Y') * P.index = Nat.card P * P.index := by rw [hPcard]
        _ = 2520 := h1
        _ = 35 * 72 := by norm_num
        _ = 35 * (Nat.card (Q : Subgroup ↥Y') * (Q : Subgroup ↥Y').index) := by rw [h2]
        _ = Nat.card (Q : Subgroup ↥Y') * (35 * (Q : Subgroup ↥Y').index) := by ring
    have hpos : 0 < Nat.card (Q : Subgroup ↥Y') := Nat.card_pos
    have hPidx : P.index = 35 * (Q : Subgroup ↥Y').index :=
      Nat.eq_of_mul_eq_mul_left hpos h5
    rw [hPidx]
    exact fun h => (Nat.prime_two.dvd_mul.mp h).elim (by norm_num) Q.not_dvd_index
  let Pobj : Sylow 2 K5Alt := hP2.toSylow hPindex
  have hT2 : IsPGroup 2 (taSub.subgroupOf K5Alt) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe taSub_le_alt).toEquiv, card_taSub]
    norm_num
  have hTindex : ¬ 2 ∣ (taSub.subgroupOf K5Alt).index := by
    have h := Subgroup.card_mul_index (taSub.subgroupOf K5Alt)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe taSub_le_alt).toEquiv, card_taSub,
      CFSG.ABGDGroups.card_alternatingGroup_fin_seven] at h
    omega
  let Tobj : Sylow 2 K5Alt := hT2.toSylow hTindex
  obtain ⟨g, hg⟩ := CFSG.Literature.GL52.sylow_eq_map_conj Pobj Tobj
  have hg' : taSub.subgroupOf K5Alt = P.map (MulAut.conj g).toMonoidHom := by
    rw [← IsPGroup.toSylow_coe hT2 hTindex, ← IsPGroup.toSylow_coe hP2 hPindex]
    exact hg
  have hTle : taSub.subgroupOf K5Alt ≤ Y'.map (MulAut.conj g).toMonoidHom := by
    rw [hg']
    exact Subgroup.map_mono hPle
  have hNle : (Y'.map (MulAut.conj g).toMonoidHom).map K5Alt.subtype ≤ K5Alt :=
    Subgroup.map_subtype_le _
  have hTA : taSub ≤ (Y'.map (MulAut.conj g).toMonoidHom).map K5Alt.subtype := by
    have h := Subgroup.map_mono (f := K5Alt.subtype) hTle
    rwa [Subgroup.map_subgroupOf_eq_of_le taSub_le_alt] at h
  have hNcard : Nat.card ((Y'.map (MulAut.conj g).toMonoidHom).map K5Alt.subtype) = 72 := by
    rw [Subgroup.card_map_of_injective K5Alt.subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hY'card]
  have hN := eq_stabSub_of_card hNle hTA hNcard
  refine ⟨g, ?_⟩
  apply Subgroup.map_injective K5Alt.subtype_injective
  rw [hN, Subgroup.map_subgroupOf_eq_of_le stabSub_le_alt]

private theorem bar2_oUpperTwo_opp_congr {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    {L : Subgroup G} {M : Subgroup H} (e : ↥L ≃* ↥M) :
    Nonempty (Bar2 (S17.oUpperTwo (Opp 2 L)) ≃*
      Bar2 (S17.oUpperTwo (Opp 2 M))) := by
  have hOppL : (Opp 2 L).subgroupOf L = Opp 2 (⊤ : Subgroup ↥L) :=
    CFSG.pElementSubgroup_subgroupOf_self 2 L
  have hOppM : (Opp 2 M).subgroupOf M = Opp 2 (⊤ : Subgroup ↥M) :=
    CFSG.pElementSubgroup_subgroupOf_self 2 M
  have hOppmap : (Opp 2 (⊤ : Subgroup ↥L)).map e.toMonoidHom =
      Opp 2 (⊤ : Subgroup ↥M) := by
    rw [← S17.opp_map e 2 ⊤, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective]
  have hUL : (S17.oUpperTwo (Opp 2 L)).subgroupOf L = S17.oUpperTwo (Opp 2 (⊤ : Subgroup ↥L)) := by
    have h := CFSG.Quasithin.A4.oTwoUpper_subgroupOf (F09.opp_le_self 2 L)
    rw [hOppL] at h
    exact h.symm
  have hUM : (S17.oUpperTwo (Opp 2 M)).subgroupOf M = S17.oUpperTwo (Opp 2 (⊤ : Subgroup ↥M)) := by
    have h := CFSG.Quasithin.A4.oTwoUpper_subgroupOf (F09.opp_le_self 2 M)
    rw [hOppM] at h
    exact h.symm
  have hULmap : ((S17.oUpperTwo (Opp 2 L)).subgroupOf L).map e.toMonoidHom =
      (S17.oUpperTwo (Opp 2 M)).subgroupOf M := by
    rw [hUL, hUM]
    change (CFSG.ComponentClassification.AS76b.oUpperTwo
      (Opp 2 (⊤ : Subgroup ↥L))).map e.toMonoidHom =
      CFSG.ComponentClassification.AS76b.oUpperTwo (Opp 2 (⊤ : Subgroup ↥M))
    rw [CFSG.AGLEmbedding.SUPair.map_oUpperTwo, hOppmap]
  let φ : ↥(S17.oUpperTwo (Opp 2 L)) ≃* ↥(S17.oUpperTwo (Opp 2 M)) :=
    (Subgroup.subgroupOfEquivOfLe
      ((S17.oUpperTwo_le (Opp 2 L)).trans (F09.opp_le_self 2 L))).symm.trans
      ((Subgroup.equivMapOfInjective ((S17.oUpperTwo (Opp 2 L)).subgroupOf L) e.toMonoidHom
        e.injective).trans
        ((MulEquiv.subgroupCongr hULmap).trans
          (Subgroup.subgroupOfEquivOfLe
            ((S17.oUpperTwo_le (Opp 2 M)).trans (F09.opp_le_self 2 M)))))
  exact ⟨UC6S846.bar2Equiv φ⟩

theorem a7_index35_jzero {X : Type} [Group X] [Finite X]
    (hX : IsAlt X 7) (Y : Subgroup X) (hY : Y.index = 35) :
    Nonempty (Bar2 (S17.oUpperTwo (Opp 2 Y)) ≃*
      Multiplicative (ZMod 3 × ZMod 3)) := by
  obtain ⟨e⟩ := hX
  let Y' : Subgroup K5Alt := Y.map e.toMonoidHom
  have hY'index : Y'.index = 35 := by
    show (Y.map e.toMonoidHom).index = 35
    rw [Subgroup.index_map_eq Y e.surjective (by
      have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
      rw [hker]
      exact bot_le), hY]
  have hY'card : Nat.card Y' = 72 := by
    have h := Subgroup.card_mul_index Y'
    rw [hY'index, CFSG.ABGDGroups.card_alternatingGroup_fin_seven] at h
    omega
  obtain ⟨g, hg⟩ := exists_conj_map_eq_stabSub Y' hY'index
  have h1 : Nonempty (Bar2 (S17.oUpperTwo (Opp 2 Y)) ≃*
      Bar2 (S17.oUpperTwo (Opp 2 Y'))) :=
    bar2_oUpperTwo_opp_congr (Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective)
  have h2 : Nonempty (Bar2 (S17.oUpperTwo (Opp 2 Y')) ≃*
      Bar2 (S17.oUpperTwo (Opp 2 (Y'.map (MulAut.conj g).toMonoidHom)))) :=
    bar2_oUpperTwo_opp_congr
      (Subgroup.equivMapOfInjective Y' (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  have h2' : Nonempty (Bar2 (S17.oUpperTwo (Opp 2 Y')) ≃*
      Bar2 (S17.oUpperTwo (Opp 2 (stabSub.subgroupOf K5Alt)))) := by
    rw [hg] at h2
    exact h2
  have h3 : Nonempty (Bar2 (S17.oUpperTwo (Opp 2 (stabSub.subgroupOf K5Alt))) ≃*
      Bar2 (S17.oUpperTwo (Opp 2 stabSub))) :=
    bar2_oUpperTwo_opp_congr (Subgroup.subgroupOfEquivOfLe stabSub_le_alt)
  obtain ⟨i1⟩ := h1
  obtain ⟨i2⟩ := h2'
  obtain ⟨i3⟩ := h3
  obtain ⟨i4⟩ := stabSub_jzero
  exact ⟨i1.trans (i2.trans (i3.trans i4))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
