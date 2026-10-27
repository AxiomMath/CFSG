module

public import CFSG.Quasithin.H13.KGFact68Spor
public import CFSG.Quasithin.H13.KGFact68CSLin
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.QuasithinUnique.K1.SporadicPerm

section BaseCert

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem isCyclic_center_sylow_of_baseCert [Finite Γ] (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (qs : List (Γ × Γ))
    (z g gi h hi : Γ) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ)
    (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m)
    (hcert : BaseCert n B (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray))
      (tab n z).toArray (tab n g).toArray (tab n gi).toArray (tab n h).toArray
      (tab n hi).toArray Ts par cl k) :
    ∀ T : Sylow 2 Γ, IsCyclic (Subgroup.center ↥(T : Subgroup Γ)) := by
  obtain ⟨hinv, -, -, hEnum, hsize, hcen, -, -, -⟩ := hcert
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  have hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹ := fun p hp =>
    hinv_of p.1 p.2 (hinv _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  let gens : List Γ := qs.map Prod.fst
  have hG : (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray)).map Prod.fst =
      genTabs n gens := by
    simp only [genTabs, gens, List.map_map, Function.comp_def]
  have hGi : (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray)).map Prod.snd =
      genTabsInv n gens := by
    simp only [genTabsInv, gens, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    rw [hqsinv p hp]
  rw [hG, hGi] at hEnum
  rw [hG] at hcen
  have hP : ∀ p ∈ ptsOf B (genTabs n gens), p < n := ptsOf_lt hB gens
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  let Q : Subgroup Γ := Subgroup.closure {x | x ∈ gens}
  have hQmem : ∀ x : Γ, x ∈ Q ↔ rt n (ptsOf B (genTabs n gens)) x ∈ Ts.toList := by
    intro x
    refine ⟨benum_closed hB gens Ts par cl hEnum x, fun hx => ?_⟩
    obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hx
    have hiT' : i < Ts.size := by simpa using hi
    obtain ⟨y, hy, hyT⟩ := benum_reach hB gens Ts par cl hEnum i hiT'
    have : rt n (ptsOf B (genTabs n gens)) y = rt n (ptsOf B (genTabs n gens)) x := by
      rw [hyT, getElem!_pos Ts i hiT']
      simpa using hiT
    rwa [← rt_injective hB hBP hbase this]
  have hcardQ : Nat.card Q = 2 ^ k := by
    rw [benum_card hB hbase gens Ts par cl hEnum, hsize]
  have hcen' : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z := by
    intro c hcQ hcc
    have hcT : rt n (ptsOf B (genTabs n gens)) c ∈ Ts.toList := (hQmem c).mp hcQ
    have hcomm := rt_comm_clause hB gens c fun s hs =>
      hcc s (Subgroup.subset_closure hs)
    rcases hcen _ hcT hcomm with h1 | h1
    · left
      exact rt_injective hB hBP hbase (by rw [h1, rt_one hP])
    · right
      exact rt_injective hB hBP hbase (by rw [h1, rt_one_mul hP])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm2 : ¬ 2 ∣ m := fun h2 => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  let U : Sylow 2 Γ := Sylow.ofCard Q (by rw [hcardQ, hcard, factorization_two_pow_mul hm2])
  have hU : (U : Subgroup Γ) = Q := Sylow.coe_ofCard _ _
  refine isCyclic_center_sylow U ?_
  have hmem : ∀ c : Subgroup.center ↥(U : Subgroup Γ),
      ((c : ↥(U : Subgroup Γ)) : Γ) ∈ ({1, z} : Set Γ) := by
    intro c
    have hcQ : ((c : ↥(U : Subgroup Γ)) : Γ) ∈ Q := hU ▸ (c : ↥(U : Subgroup Γ)).2
    have hc := hcen' _ hcQ fun q hq => by
      have hqU : q ∈ (U : Subgroup Γ) := hU ▸ hq
      have := Subgroup.mem_center_iff.mp c.2 ⟨q, hqU⟩
      exact (congrArg Subtype.val this).symm
    rcases hc with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  calc Nat.card (Subgroup.center ↥(U : Subgroup Γ)) ≤ Nat.card ({1, z} : Set Γ) :=
        Nat.card_le_card_of_injective (fun c => ⟨_, hmem c⟩) fun c d hcd => by
          have h1 := congrArg (fun x : ({1, z} : Set Γ) => (x : Γ)) hcd
          exact Subtype.ext (Subtype.ext h1)
    _ = Set.ncard ({1, z} : Set Γ) := Nat.card_coe_set_eq _
    _ ≤ Set.ncard ({z} : Set Γ) + 1 := Set.ncard_insert_le 1 {z}
    _ = 2 := by rw [Set.ncard_singleton]

theorem isCyclic_center_sylow_of_baseCertS [Finite Γ] (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (zn gn gin hn hin : ℕ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ) (hcard : Nat.card Γ = 2 ^ k * m)
    (hm : Odd m)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k) :
    ∀ T : Sylow 2 Γ, IsCyclic (Subgroup.center ↥(T : Subgroup Γ)) := by
  obtain ⟨hqp, hz, hg, hgi, hh, hhi, hc⟩ := hcert
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  refine isCyclic_center_sylow_of_baseCert B hB hbase
    (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1))
    ((slpElts a b prog).getD zn 1) ((slpElts a b prog).getD gn 1) ((slpElts a b prog).getD gin 1)
    ((slpElts a b prog).getD hn 1) ((slpElts a b prog).getD hin 1) Ts par cl k m hcard hm ?_
  rw [hE' zn hz, hE' gn hg, hE' gin hgi, hE' hn hh, hE' hin hhi]
  have : (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1)).map
      (fun p => ((tab n p.1).toArray, (tab n p.2).toArray)) =
        qp.map fun p => (T[p.1]!, T[p.2]!) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    rw [hE' p.1 (hqp p hp).1, hE' p.2 (hqp p hp).2]
  rw [this]
  exact hc

end BaseCert

section Mathieu

open CFSG.Sporadic.Mathieu (m11a m11b m12a m12b m22a m22b m24a m24b card_M11 card_M12 card_M22
  card_M24)
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card)

theorem isCyclic_center_sylow_m11 :
    ∀ T : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M11,
      IsCyclic (Subgroup.center ↥(T : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11)) := by
  refine isCyclic_center_sylow_of_baseCertS (n := 11) (List.range 11)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m11a m11b m11Prog m11_valid m11Qp
    159 189 193 191 195 m11Enum.1 m11Enum.2.1 m11Enum.2.2 4 495
    (by rw [card_M11]; norm_num) (by decide) ?_
  rw [m11_tab_a, m11_tab_b]
  exact m11_cert

theorem isCyclic_center_sylow_m12 :
    ∀ T : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M12,
      IsCyclic (Subgroup.center ↥(T : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12)) := by
  refine isCyclic_center_sylow_of_baseCertS (n := 12) (List.range 12)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m12a m12b m12Prog m12_valid m12Qp
    153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 1485
    (by rw [card_M12]; norm_num) (by decide) ?_
  rw [m12_tab_a, m12_tab_b]
  exact m12_cert

theorem isCyclic_center_sylow_m22 :
    ∀ T : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M22,
      IsCyclic (Subgroup.center ↥(T : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22)) := by
  refine isCyclic_center_sylow_of_baseCertS (n := 22) (List.range 22)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m22a m22b m22Prog m22_valid m22Qp
    163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 3465
    (by rw [card_M22]; norm_num) (by decide) ?_
  rw [m22_tab_a, m22_tab_b]
  exact m22_cert

theorem isCyclic_center_sylow_m23 :
    ∀ T : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M23,
      IsCyclic (Subgroup.center ↥(T : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23)) := by
  refine isCyclic_center_sylow_of_baseCertS (n := 23) (List.range 23)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m23GenA m23GenB m23Prog m23_valid m23Qp
    159 199 203 201 205 m23Enum.1 m23Enum.2.1 m23Enum.2.2 7 79695
    (by rw [m23_card]; norm_num) (by decide) ?_
  rw [m23_tab_a, m23_tab_b]
  exact m23_cert

theorem isCyclic_center_sylow_m24 :
    ∀ T : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M24,
      IsCyclic (Subgroup.center ↥(T : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24)) := by
  refine isCyclic_center_sylow_of_baseCertS (n := 24) (List.range 24)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m24a m24b m24Prog m24_valid m24Qp
    162 213 216 214 217 m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 239085
    (by rw [card_M24]; norm_num) (by decide) ?_
  rw [m24_tab_a, m24_tab_b]
  exact m24_cert

end Mathieu

section Matrix

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem isCyclic_center_sylow_j2 :
    ∀ T : Sylow 2 CFSG.Blueprint.NativeSporadic.J2,
      IsCyclic (Subgroup.center ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2)) := by
  have hJ : ∀ T : Sylow 2 ↥CFSG.Sporadic.J2.J,
      IsCyclic (Subgroup.center ↥(T : Subgroup ↥CFSG.Sporadic.J2.J)) := by
    refine isCyclic_center_sylow_of_baseCertS (n := 315) (List.range 315)
      (fun b hb => List.mem_range.mp hb) base_of_faithful (CFSG.Sporadic.J2.a : CFSG.Sporadic.J2.J)
      (CFSG.Sporadic.J2.b : CFSG.Sporadic.J2.J) j2Prog j2_valid j2Qp
      143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 4725
      (by rw [CFSG.Sporadic.J2.card_J]; norm_num) (by decide) ?_
    rw [j2_tab_a, j2_tab_b]
    exact j2_cert
  have hfin : Finite CFSG.Blueprint.NativeSporadic.J2 :=
    Finite.of_equiv _ CFSG.Sporadic.J2.nativeEquiv.symm.toEquiv
  exact @isCyclic_center_sylow_of_mulEquiv CFSG.Blueprint.NativeSporadic.J2 ↥CFSG.Sporadic.J2.J _ _
    hfin CFSG.Sporadic.J2.nativeEquiv hJ

end Matrix

section HS

open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)

theorem isCyclic_center_sylow_hs :
    ∀ T : Sylow 2 CFSG.Blueprint.NativeSporadic.HS,
      IsCyclic (Subgroup.center ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.HS)) := by
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  have hJ : ∀ T : Sylow 2 ↥(J hsData),
      IsCyclic (Subgroup.center ↥(T : Subgroup ↥(J hsData))) := by
    have ha : tab hsData.n (a hsData) = hsTa.toList := by
      rw [tab_eq_of_rep (n := hsData.n) _ (a hsData) (rep_a hF.toBaseFacts)]
      simp [hsTa]
    have hb : tab hsData.n (b hsData) = hsTb.toList := by
      rw [tab_eq_of_rep (n := hsData.n) _ (b hsData) (rep_b hF.toBaseFacts)]
      simp [hsTb]
    have hcard0 : Nat.card (J hsData) = 44352000 :=
      (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.HS.card_HS
    have hcard : Nat.card (J hsData) = 2 ^ 9 * 86625 := by
      rw [hcard0]; norm_num
    refine isCyclic_center_sylow_of_baseCertS (n := hsData.n) hsB
      (base_lt hF) (base_property hF) (a hsData) (b hsData) hsProg hs_valid hsQp
      164 202 206 204 208 hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 86625 hcard
      (by decide) ?_
    rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
    exact hs_cert
  have hfin : Finite CFSG.Blueprint.NativeSporadic.HS :=
    Finite.of_equiv _ (seedEquiv hF.toBaseFacts).symm.toEquiv
  exact @isCyclic_center_sylow_of_mulEquiv CFSG.Blueprint.NativeSporadic.HS ↥(J hsData) _ _
    hfin (seedEquiv hF.toBaseFacts) hJ

end HS

section Ru

open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

theorem isCyclic_center_sylow_ru :
    ∀ T : Sylow 2 CFSG.Blueprint.NativeSporadic.Ru,
      IsCyclic (Subgroup.center ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.Ru)) := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have hJ : ∀ T : Sylow 2 ↥(J ruData),
      IsCyclic (Subgroup.center ↥(T : Subgroup ↥(J ruData))) := by
    have ha : tab ruData.n (a ruData) = ruTa.toList := by
      rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a hF.toBaseFacts)]
      simp [ruTa]
    have hb : tab ruData.n (b ruData) = ruTb.toList := by
      rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b hF.toBaseFacts)]
      simp [ruTb]
    have hcard0 : Nat.card (J ruData) = 145926144000 :=
      (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
    have hcard : Nat.card (J ruData) = 2 ^ 14 * 8906625 := by
      rw [hcard0]; norm_num
    refine isCyclic_center_sylow_of_baseCertS (n := ruData.n) ruB
      (base_lt hF) (base_property hF) (a ruData) (b ruData) ruProg ru_valid ruQp
      154 187 191 189 193 ruEnum.1 ruEnum.2.1 ruEnum.2.2 14 8906625 hcard
      (by decide) ?_
    rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
    exact ru_cert
  have hfin : Finite CFSG.Blueprint.NativeSporadic.Ru :=
    Finite.of_equiv _ (seedEquiv hF.toBaseFacts).symm.toEquiv
  exact @isCyclic_center_sylow_of_mulEquiv CFSG.Blueprint.NativeSporadic.Ru ↥(J ruData) _ _
    hfin (seedEquiv hF.toBaseFacts) hJ

end Ru

section He

open CFSG.Sporadic.He

theorem isCyclic_center_sylow_he :
    ∀ T : Sylow 2 CFSG.Blueprint.NativeSporadic.He,
      IsCyclic (Subgroup.center ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.He)) := by
  have hJ : ∀ T : Sylow 2 ↥J, IsCyclic (Subgroup.center ↥(T : Subgroup ↥J)) := by
    have ha : tab 8330 (a : J) = heTa.toList := by
      rw [tab_eq_of_rep (n := 8330) _ (a : J) rep_alpha]
      simp [heTa, orb]
    have hb : tab 8330 (b : J) = heTb.toList := by
      rw [tab_eq_of_rep (n := 8330) _ (b : J) rep_beta]
      simp [heTb, orb]
    refine isCyclic_center_sylow_of_baseCertS (n := 8330) heB he_base_lt he_base_property
      (a : J) (b : J) heProg he_valid heQp 170 249 253 251 255 heEnum.1 heEnum.2.1
      heEnum.2.2 10 3935925 (by rw [card_J]; norm_num) (by decide) ?_
    rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
    exact he_cert
  have hfin : Finite CFSG.Blueprint.NativeSporadic.He :=
    Finite.of_equiv _ heEquivJ.symm.toEquiv
  exact @isCyclic_center_sylow_of_mulEquiv CFSG.Blueprint.NativeSporadic.He ↥J _ _
    hfin heEquivJ hJ

end He

@[expose] def J4SylowCenterCyclic : Prop :=
  ∀ T : Sylow 2 (CFSG.Blueprint.NativeSporadic.Carrier .J4),
    IsCyclic (Subgroup.center ↥(T : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J4)))

theorem sporadicSylowCenterCyclic_of_j4
    (hJ4 : J4SylowCenterCyclic) : SporadicSylowCenterCyclic := by
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isCyclic_center_sylow_m11
  · exact isCyclic_center_sylow_m12
  · exact isCyclic_center_sylow_m22
  · exact isCyclic_center_sylow_m23
  · exact isCyclic_center_sylow_m24
  · exact isCyclic_center_sylow_j2
  · exact hJ4
  · exact isCyclic_center_sylow_hs
  · exact isCyclic_center_sylow_he
  · exact isCyclic_center_sylow_ru

end CFSG.Quasithin.H13.KG68
