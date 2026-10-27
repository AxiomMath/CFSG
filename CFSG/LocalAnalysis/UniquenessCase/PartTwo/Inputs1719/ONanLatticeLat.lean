module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLatticeLatCheck
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLatticeModel

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ONOddCore
open scoped Pointwise

@[expose] def onl_bits (M : ℕ) : Set (Fin 120) := {x | M.testBit x}

theorem onl_chk_spec {A B : ℕ} : ∀ {L : List ℕ} {p : ℕ}, onl_chk A B L p = true →
    ∀ i < L.length, A.testBit (p + i) = B.testBit (L.getD i 0)
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | a :: t, p, h, i, hi => by
    simp only [onl_chk, Bool.and_eq_true, beq_iff_eq] at h
    rcases i with _ | i
    · simpa using h.1
    · have := onl_chk_spec h.2 i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      simpa using this

@[expose] def onl_Img (L : List ℕ) (g : Equiv.Perm (Fin 120)) : Prop :=
  L.length = 120 ∧ ∀ x : Fin 120, L.getD x 0 = g x

theorem onl_smul_bits {A B : ℕ} {L : List ℕ} {g : Equiv.Perm (Fin 120)}
    (hL : onl_Img L g) (h : onl_chk A B L 0 = true) : g • onl_bits A = onl_bits B := by
  have key : ∀ x : Fin 120, A.testBit x = B.testBit (g x) := fun x => by
    have := onl_chk_spec h x (by rw [hL.1]; exact x.isLt)
    rwa [zero_add, hL.2] at this
  rw [← Set.image_smul]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show B.testBit (g x) = true
    rw [← key]
    exact hx
  · intro hy
    refine ⟨g⁻¹ y, ?_, by simp⟩
    show A.testBit (g⁻¹ y) = true
    rw [key, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
    exact hy

theorem onl_bits_inj {A B : ℕ} (hA : A < 2 ^ 120) (hB : B < 2 ^ 120)
    (h : onl_bits A = onl_bits B) : A = B := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 120
  · have := congrArg (fun s : Set (Fin 120) => (⟨i, hi⟩ : Fin 120) ∈ s) h
    simp only [onl_bits, Set.mem_setOf_eq, eq_iff_iff] at this
    exact Bool.eq_iff_iff.2 this
  · have h120 : 2 ^ 120 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hA h120),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hB h120)]

theorem onl_getD_toList {t : Array ℕ} (i : ℕ) : t.toList.getD i 0 = t[i]! := by
  by_cases hi : i < t.size
  · rw [getElem!_pos t i hi, List.getD_eq_getElem _ _ (by simpa using hi), Array.getElem_toList]
  · rw [getElem!_neg t i hi, List.getD_eq_default _ _ (by simpa using hi)]
    rfl

theorem onl_img_of_prep {t : Array ℕ} {g : Equiv.Perm (Fin 120)} (ht : PRep 120 t g)
    (hs : t.size = 120) : onl_Img t.toList g :=
  ⟨by rw [Array.length_toList, hs], fun x => by rw [onl_getD_toList, ht x]⟩

theorem onl_img_comp {t u : List ℕ} {g h : Equiv.Perm (Fin 120)} (ht : onl_Img t g)
    (hu : onl_Img u h) : onl_Img (onl_comp t u) (g * h) := by
  refine ⟨by simp [onl_comp, hu.1], fun x => ?_⟩
  have hx : (x : ℕ) < u.length := by rw [hu.1]; exact x.isLt
  have e1 : u[(x : ℕ)] = h x := by rw [← hu.2 x, List.getD_eq_getElem _ _ hx]
  simp only [onl_comp]
  rw [List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_map, e1, ht.2 (h x)]
  rfl

theorem onl_img_one : onl_Img (List.range 120) 1 :=
  ⟨List.length_range, fun x => by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_range]
    rfl⟩

abbrev onl_r (j : ℕ) : Equiv.Perm (Fin 120) :=
  onu * permOfArr 120 Data.M120Chain.generators[j]! * onu⁻¹

theorem onl_chkConj_spec {r u : List ℕ} : ∀ {L : List ℕ} {p : ℕ},
    onl_chkConj r u L p = true →
      ∀ i < L.length, r.getD (u.getD (p + i) 0) 0 = u.getD (L.getD i 0) 0
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | a :: t, p, h, i, hi => by
    simp only [onl_chkConj, Bool.and_eq_true, beq_iff_eq] at h
    rcases i with _ | i
    · simpa using h.1
    · have := onl_chkConj_spec h.2 i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      simpa using this

theorem onl_r_img {j : ℕ}
    (hj : j < 2) : onl_Img (if j = 0 then onl_r0 else onl_r1) (onl_r j) := by
  have hc := onl_conj_check
  have hu : onl_Img Data.quotientConjugator.toList onu := onl_img_of_prep prep_u hc.2.2.2.2.1
  have hsz : (Data.M120Chain.generators[j]!).size = 120 := by
    interval_cases j
    · exact hc.2.2.2.2.2.1
    · exact hc.2.2.2.2.2.2
  have hg := onl_img_of_prep
    (prep_smallGen small_chain_certs.2.1 j (by rw [m120_gens_size]; exact hj)) hsz
  have hchk : onl_chkConj (if j = 0 then onl_r0 else onl_r1) Data.quotientConjugator.toList
      (Data.M120Chain.generators[j]!).toList 0 = true := by
    interval_cases j
    · exact hc.1
    · exact hc.2.1
  refine ⟨by interval_cases j <;> simp [hc.2.2.1, hc.2.2.2.1], fun y => ?_⟩
  have h1 := onl_chkConj_spec hchk (onu⁻¹ y) (by rw [hg.1]; exact (onu⁻¹ y).isLt)
  rw [zero_add, hu.2, hg.2, hu.2, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h1
  rw [h1]
  rfl

theorem onl_r_mem
    {j : ℕ} (hj : j < 2) : onl_r j ∈ RM := by
  rw [RM_eq_map, rhoM_range, onM120Chain, smallChain_sub]
  exact ⟨_, Subgroup.subset_closure ⟨j, by rw [m120_gens_size]; exact hj, rfl⟩, rfl⟩

theorem onl_psl_mem
    {j : ℕ} (hj : j < 12) :
    permOfArr 120 Data.PSL120Chain.generators[j]! ∈ RM := by
  apply onX_le_RM
  rw [onX, onPSL120Chain, smallChain_sub]
  exact Subgroup.subset_closure ⟨j, by rw [psl120_size]; exact hj, rfl⟩

theorem onl_psl_img {j : ℕ}
    (hj : j < 12) (hs : (Data.PSL120Chain.generators[j]!).size = 120) :
    onl_Img (Data.PSL120Chain.generators[j]!).toList
      (permOfArr 120 Data.PSL120Chain.generators[j]!) :=
  onl_img_of_prep (prep_smallGen small_chain_certs.2.2.2.2.1 j (by rw [psl120_size]; exact hj))
    hs

@[expose] def onl_genP (a : ℕ) : Equiv.Perm (Fin 120) :=
  if a = 0 then onl_r 0 else if a = 1 then onl_r 1
  else permOfArr 120 Data.PSL120Chain.generators[a - 2]!

theorem onl_genP_mem
    {a : ℕ} (ha : a < 14) :
    onl_genP a ∈ RM := by
  unfold onl_genP
  split_ifs with h0 h1
  · exact onl_r_mem (by norm_num)
  · exact onl_r_mem (by norm_num)
  · exact onl_psl_mem (by omega)

theorem onl_genP_img
    {a : ℕ} (ha : a < 14) : onl_Img (onl_genT a) (onl_genP a) := by
  have hlen := List.all_eq_true.1 onl_misc_check.1 a (List.mem_range.2 ha)
  rw [beq_iff_eq] at hlen
  unfold onl_genP onl_genT at *
  split_ifs at * with h0 h1
  · subst h0; simpa using onl_r_img (j := 0) (by norm_num)
  · subst h1; simpa using onl_r_img (j := 1) (by norm_num)
  · refine onl_psl_img (by omega) ?_
    rwa [Array.length_toList] at hlen

@[expose] def onl_wordP : List ℕ → Equiv.Perm (Fin 120)
  | [] => 1
  | a :: w => onl_genP a * onl_wordP w

theorem onl_wordP_mem :
    ∀ w : List ℕ, w.all (· < 14) = true → onl_wordP w ∈ RM
  | [], _ => one_mem _
  | a :: w, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    exact mul_mem (onl_genP_mem h.1) (onl_wordP_mem w h.2)

theorem onl_wordP_img :
    ∀ w : List ℕ, w.all (· < 14) = true → onl_Img (onl_wordT w) (onl_wordP w)
  | [], _ => onl_img_one
  | a :: w, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    exact onl_img_comp (onl_genP_img h.1) (onl_wordP_img w h.2)

@[expose] def onl_tauP : Equiv.Perm (Fin 120) :=
  onl_wordP onl_tauW

@[expose] def onl_gP (i : ℕ) : Equiv.Perm (Fin 120) :=
  onl_wordP (onl_gW.getD i [])

theorem onl_tauP_img :
    onl_Img onl_tauT onl_tauP := by
  rw [← onl_word_check.1]
  exact onl_wordP_img _ onl_word_check.2.2.1

theorem onl_tauP_mem :
    onl_tauP ∈ RM :=
  onl_wordP_mem _ onl_word_check.2.2.1

theorem onl_gW_ok {i : ℕ} (hi : i < 8) : (onl_gW.getD i []).all (· < 14) = true := by
  have h := List.all_eq_true.1 onl_word_check.2.2.2.1 (onl_gW.getD i [])
  apply h
  rw [List.getD_eq_getElem _ _ (by rw [onl_word_check.2.2.2.2.1]; exact hi)]
  exact List.getElem_mem _

theorem onl_gP_img
    {i : ℕ} (hi : i < 8) :
    onl_Img (onl_gT.getD i []) (onl_gP i) := by
  have h := List.all_eq_true.1 onl_word_check.2.1 i (List.mem_range.2 hi)
  rw [beq_iff_eq] at h
  rw [← h]
  exact onl_wordP_img _ (onl_gW_ok hi)

theorem onl_gP_mem
    {i : ℕ} (hi : i < 8) :
    onl_gP i ∈ RM :=
  onl_wordP_mem _ (onl_gW_ok hi)

@[expose] def onl_tgenP (j : ℕ) : Equiv.Perm (Fin 120) :=
  if j < 6 then permOfArr 120 Data.PSL120Chain.generators[onl_J.getD j 0]! else onl_tauP

theorem onl_J_lt {j : ℕ} (hj : j < 6) : onl_J.getD j 0 < 12 := by
  interval_cases j <;> decide

theorem onl_tgenP_mem
    (j : ℕ) : onl_tgenP j ∈ RM := by
  unfold onl_tgenP
  split_ifs with h
  · exact onl_psl_mem (onl_J_lt h)
  · exact onl_tauP_mem

theorem onl_tgenP_img
    {j : ℕ} (hj : j < 7) : onl_Img (onl_tgenT j) (onl_tgenP j) := by
  have hlen := List.all_eq_true.1 onl_forest_check.2.2.2.2.2.2.2.2.1 j (List.mem_range.2 hj)
  rw [beq_iff_eq] at hlen
  unfold onl_tgenP onl_tgenT at *
  split_ifs at * with h
  · refine onl_psl_img (onl_J_lt h) ?_
    rwa [Array.length_toList] at hlen
  · exact onl_tauP_img

@[expose] def onl_kgenP (i j : ℕ) : Equiv.Perm (Fin 120) :=
  if j < 7 then onl_tgenP j else onl_gP i

theorem onl_kgenP_img
    {i j : ℕ} (hi : i < 8) (_hj : j < 8) :
    onl_Img (onl_kgenT i j) (onl_kgenP i j) := by
  unfold onl_kgenP onl_kgenT
  split_ifs with h
  · exact onl_tgenP_img h
  · exact onl_gP_img hi

theorem onl_r0_img :
    onl_Img onl_r0 (onl_r 0) := by simpa using onl_r_img (j := 0) (by norm_num)

theorem onl_r1_img :
    onl_Img onl_r1 (onl_r 1) := by simpa using onl_r_img (j := 1) (by norm_num)

@[expose] def onl_om (k : ℕ) : Set (Fin 120) × Set (Fin 120) :=
  (onl_bits (onl_A k), onl_bits (onl_B k))

@[expose] def onl_Om : Set (Set (Fin 120) × Set (Fin 120)) := onl_om '' {k | k < 315}

theorem onl_smul_om {t : List ℕ} {g : Equiv.Perm (Fin 120)} (ht : onl_Img t g) {k l : ℕ}
    (h : onl_mapsTo t k l = true) : g • onl_om k = onl_om l := by
  simp only [onl_mapsTo, onl_chk2, Bool.and_eq_true] at h
  simp only [onl_om, Prod.smul_mk, onl_smul_bits ht h.1, onl_smul_bits ht h.2]

theorem onl_smul_RM
    (n : RM)
    (p : Set (Fin 120) × Set (Fin 120)) : n • p = (n : Equiv.Perm (Fin 120)) • p := rfl

theorem onl_om_mem
    (k : ℕ) (hk : k < 315) : onl_om k ∈ MulAction.orbit RM (onl_om 0) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk0 : k = 0
    · subst hk0; exact MulAction.mem_orbit_self _
    · have hc := List.all_eq_true.1 onl_tree_check.2.2.2.2.2.2.2 k (List.mem_range.2 hk)
      rw [Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with hc | hc
      · exact absurd hc hk0
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hpk, hlab⟩, hmap⟩ := hc
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (ih _ hpk (lt_trans hpk hk))
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨onl_r (onl_Lt.getD k (0, 0)).2, onl_r_mem hlab⟩ * g, ?_⟩
      rw [mul_smul, hg, onl_smul_RM]
      exact onl_smul_om (onl_r_img hlab) hmap

theorem onl_closure_RM :
    Subgroup.closure ({⟨onl_r 0, onl_r_mem (by norm_num)⟩, ⟨onl_r 1, onl_r_mem (by norm_num)⟩} :
      Set RM) = ⊤ := by
  apply Subgroup.map_injective RM.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_pair]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact onl_r_mem (by norm_num)
    · exact onl_r_mem (by norm_num)
  · show (RM : Subgroup (Equiv.Perm (Fin 120))) ≤ Subgroup.closure {onl_r 0, onl_r 1}
    rw [RM_eq_map, rhoM_range, onM120Chain, smallChain_sub, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    rw [m120_gens_size] at hj
    have hj' : j < 2 := hj
    apply Subgroup.subset_closure
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem onl_Om_inv
    (g : RM) : ∀ y ∈ onl_Om, g • y ∈ onl_Om := by
  refine CFSG.Sporadic.Th.smul_mem_of_closure onl_closure_RM
    ((Set.finite_lt_nat 315).image _) ?_ ?_ g
  · rintro _ ⟨k, hk, rfl⟩
    have hc := List.all_eq_true.1 onl_closure_check k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨_, hc.1.1.1, (onl_smul_om onl_r0_img hc.1.2).symm⟩
  · rintro _ ⟨k, hk, rfl⟩
    have hc := List.all_eq_true.1 onl_closure_check k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨_, hc.1.1.2, (onl_smul_om onl_r1_img hc.2).symm⟩

theorem onl_orbit_eq :
    MulAction.orbit RM (onl_om 0) = onl_Om := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact onl_Om_inv g _ ⟨0, by norm_num, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact onl_om_mem k hk

theorem onl_om_inj {k l : ℕ} (hk : k < 315) (hl : l < 315) (h : onl_om k = onl_om l) :
    k = l := by
  have hlt := onl_tree_check.2.2.2.2.2.2.1
  have hk' := List.all_eq_true.1 hlt k (List.mem_range.2 hk)
  have hl' := List.all_eq_true.1 hlt l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk' hl'
  have hA := onl_bits_inj hk'.1 hl'.1 (congrArg Prod.fst h)
  have hB := onl_bits_inj hk'.2 hl'.2 (congrArg Prod.snd h)
  exact List.inj_on_of_nodup_map onl_nodup_check (List.mem_range.2 hk) (List.mem_range.2 hl)
    (by rw [hA, hB])

theorem onl_ncard_Om : onl_Om.ncard = 315 := by
  rw [onl_Om, Set.InjOn.ncard_image (f := onl_om) (s := {k : ℕ | k < 315})
    (fun k hk l hl h => onl_om_inj hk hl h)]
  rw [show {k : ℕ | k < 315} = ↑(Finset.range 315) by ext; simp, Set.ncard_coe_finset,
    Finset.card_range]

abbrev onl_Tb :
    Subgroup RM :=
  MulAction.stabilizer RM (onl_om 0)

abbrev onl_Bb :
    Subgroup RM :=
  MulAction.stabilizer RM (onl_bits onl_mO)

theorem onl_card_Tb :
    Nat.card onl_Tb = 128 := by
  have h1 := onl_Tb.card_mul_index
  rw [MulAction.index_stabilizer, onl_orbit_eq, onl_ncard_Om, card_RM] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h1.trans (by norm_num))

theorem onl_A0 : onl_A 0 = onl_mO := onl_tree_check.2.2.2.2.1

theorem onl_Tb_le_Bb :
    onl_Tb ≤ onl_Bb := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  have h := congrArg Prod.fst hg
  rw [Prod.smul_fst] at h
  simpa [onl_om, onl_A0] using h

theorem onl_first_O {k : ℕ} (hk : k < 315) (h : onl_A k = onl_mO) : k = 0 ∨ k = 48 ∨ k = 122 := by
  have hmem : k ∈ (List.range 315).filter (fun k => onl_A k == onl_mO) :=
    List.mem_filter.2 ⟨List.mem_range.2 hk, by rw [h]; exact beq_self_eq_true _⟩
  rw [onl_misc_check.2] at hmem
  simpa using hmem

theorem onl_A_lt {k : ℕ} (hk : k < 315) : onl_A k < 2 ^ 120 := by
  have hk' := List.all_eq_true.1 onl_tree_check.2.2.2.2.2.2.1 k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk'
  exact hk'.1

theorem onl_mO_lt : onl_mO < 2 ^ 120 := by
  rw [← onl_A0]; exact onl_A_lt (by norm_num)

theorem onl_card_Bb :
    Nat.card onl_Bb = 384 := by
  have hst : MulAction.stabilizer onl_Bb (onl_om 0) = onl_Tb.subgroupOf onl_Bb := by
    ext b
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rfl
  have horb : MulAction.orbit onl_Bb (onl_om 0) = onl_om '' {0, 48, 122} := by
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩
      have hb : (b : RM) • onl_om 0 ∈ onl_Om := by
        rw [← onl_orbit_eq]; exact MulAction.mem_orbit _ _
      obtain ⟨k, hk, hkb⟩ := hb
      refine ⟨k, ?_, hkb⟩
      have h1 := congrArg Prod.fst hkb
      have h2 : ((b : RM) • onl_om 0).1 = onl_bits onl_mO := by
        have hb2 : (b : RM) • onl_bits onl_mO = onl_bits onl_mO :=
          MulAction.mem_stabilizer_iff.1 b.2
        rw [Prod.smul_fst]
        show (b : RM) • onl_bits (onl_A 0) = _
        rw [onl_A0]
        exact hb2
      rw [h2] at h1
      have := onl_first_O hk (onl_bits_inj (onl_A_lt hk) onl_mO_lt h1)
      simpa using this
    · rintro _ ⟨k, hk, rfl⟩
      have hk315 : k < 315 := by simp at hk; omega
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (onl_om_mem k hk315)
      have hgB : g ∈ onl_Bb := by
        rw [MulAction.mem_stabilizer_iff]
        have h1 := congrArg Prod.fst hg
        rw [Prod.smul_fst] at h1
        have hAk : onl_A k = onl_mO := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
          rcases hk with rfl | rfl | rfl
          · exact onl_A0
          · exact (List.mem_filter.1 (show 48 ∈ (List.range 315).filter
              (fun k => onl_A k == onl_mO) by rw [onl_misc_check.2]; simp)).2 |> beq_iff_eq.1
          · exact (List.mem_filter.1 (show 122 ∈ (List.range 315).filter
              (fun k => onl_A k == onl_mO) by rw [onl_misc_check.2]; simp)).2 |> beq_iff_eq.1
        simpa [onl_om, onl_A0, hAk] using h1
      exact ⟨⟨g, hgB⟩, hg⟩
  have hn : (MulAction.orbit onl_Bb (onl_om 0)).ncard = 3 := by
    rw [horb, Set.InjOn.ncard_image (fun k hk l hl h => onl_om_inj (by simp at hk; omega)
      (by simp at hl; omega) h)]
    simp
  have h1 := (MulAction.stabilizer onl_Bb (onl_om 0)).card_mul_index
  rw [MulAction.index_stabilizer, hn, hst,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe onl_Tb_le_Bb).toEquiv, onl_card_Tb] at h1
  omega

theorem onl_B0 : onl_B 0 = onl_mD := onl_tree_check.2.2.2.2.2.1

theorem onl_eq_or_eq_of_prime {G : Type*} [Group G] {S X H : Subgroup G} (hSX : S ≤ X)
    (hXH : X ≤ H) {p : ℕ} (hp : p.Prime) (hidx : S.relIndex H = p) : X = S ∨ X = H := by
  have h1 := Subgroup.relIndex_mul_relIndex S X H hSX hXH
  rw [hidx] at h1
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ h1) with h | h
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 h) hSX)
  · right
    rw [h] at h1
    have h2 : X.relIndex H = 1 := by
      have := hp.pos
      nlinarith
    exact le_antisymm hXH (Subgroup.relIndex_eq_one.1 h2)

@[expose] def onl_tgenR
    (j : ℕ) : RM :=
  ⟨onl_tgenP j, onl_tgenP_mem j⟩

@[expose] def onl_Tpp :
    Subgroup RM :=
  Subgroup.closure (onl_tgenR '' {j | j < 7})

theorem onl_tgenR_fix
    {j : ℕ} (hj : j < 7) :
    onl_tgenR j • onl_om 0 = onl_om 0 := by
  have h := List.all_eq_true.1 onl_forest_check.2.2.2.2.2.2.2.1 j (List.mem_range.2 hj)
  rw [onl_smul_RM]
  apply onl_smul_om (onl_tgenP_img hj)
  show onl_chk2 (onl_A 0) (onl_B 0) (onl_A 0) (onl_B 0) _ = true
  rw [onl_A0, onl_B0]
  exact h

theorem onl_Tpp_le_Tb :
    onl_Tpp ≤ onl_Tb := by
  rw [onl_Tpp, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact MulAction.mem_stabilizer_iff.2 (onl_tgenR_fix hj)

theorem onl_forest
    (k : ℕ) (hk : k < 315) :
    ∃ i < 10, ∃ t ∈ onl_Tpp, t • onl_om (onl_reps.getD i 0) = onl_om k := by
  suffices h : ∀ d k, (onl_F.getD k (0, 0, 0)).2.2 = d → k < 315 →
      ∃ i < 10, ∃ t ∈ onl_Tpp, t • onl_om (onl_reps.getD i 0) = onl_om k from h _ k rfl hk
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hd hk
    have hc := List.all_eq_true.1 onl_forest_check.2.2.2.2.2.1 k (List.mem_range.2 hk)
    by_cases hr : onl_reps.contains k = true
    · rw [List.contains_iff_mem] at hr
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem hr
      refine ⟨i, by rw [onl_forest_check.2.1] at hi; exact hi, 1, one_mem _, ?_⟩
      rw [one_smul, List.getD_eq_getElem _ _ hi, he]
    · rw [if_neg hr] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hp, hdp⟩, hj⟩, hmap⟩ := hc
      rw [hd] at hdp
      obtain ⟨i, hi, t, ht, hti⟩ := ih _ hdp _ rfl hp
      refine ⟨i, hi, onl_tgenR (onl_F.getD k (0, 0, 0)).2.1 * t,
        mul_mem (Subgroup.subset_closure ⟨_, hj, rfl⟩) ht, ?_⟩
      rw [mul_smul, hti, onl_smul_RM]
      exact onl_smul_om (onl_tgenP_img hj) hmap

@[expose] def onl_gR
    (i : ℕ) : RM :=
  if h : i < 8 then ⟨onl_gP i, onl_gP_mem h⟩ else 1

@[expose] def onl_kgenR
    (i j : ℕ) : RM :=
  if j < 7 then onl_tgenR j else onl_gR i

theorem onl_kgenR_val
    {i j : ℕ} (hi : i < 8) :
    (onl_kgenR i j : Equiv.Perm (Fin 120)) = onl_kgenP i j := by
  unfold onl_kgenR onl_kgenP onl_gR
  split_ifs <;> rfl

theorem onl_gR_rep
    {i : ℕ} (hi : i < 8) :
    onl_gR i • onl_om 0 = onl_om (onl_reps.getD (i + 1) 0) := by
  have h := List.all_eq_true.1 onl_forest_check.2.2.2.2.2.2.1 i (List.mem_range.2 hi)
  rw [onl_smul_RM]
  have hv : (onl_gR i : Equiv.Perm (Fin 120)) = onl_gP i := by
    unfold onl_gR; rw [dif_pos hi]
  rw [hv]
  apply onl_smul_om (onl_gP_img hi)
  show onl_chk2 (onl_A 0) (onl_B 0) _ _ _ = true
  rw [onl_A0, onl_B0]
  exact h

theorem onl_K5_reach
    {i : ℕ} (hi : i < 8) (t : ℕ)
    (ht : t < 315) : ∃ h ∈ Subgroup.closure (Set.range (onl_kgenR i)),
      h • onl_om 0 = onl_om ((onl_K5.getD i []).getD t (0, 0, 0)).1 := by
  have hc := List.all_eq_true.1 onl_k5_check.2 i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨-, h0⟩, -⟩, htree⟩ := hc
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht0 : t = 0
    · subst ht0
      exact ⟨1, one_mem _, by rw [one_smul, h0]⟩
    · have he := List.all_eq_true.1 htree t (List.mem_range.2 ht)
      rw [Bool.or_eq_true, beq_iff_eq] at he
      rcases he with he | he
      · exact absurd he ht0
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he
      obtain ⟨⟨⟨hp, hj⟩, -⟩, hmap⟩ := he
      obtain ⟨h, hh, hh0⟩ := ih _ hp (lt_trans hp ht)
      refine ⟨onl_kgenR i ((onl_K5.getD i []).getD t (0, 0, 0)).2.2 * h,
        mul_mem (Subgroup.subset_closure ⟨_, rfl⟩) hh, ?_⟩
      rw [mul_smul, hh0, onl_smul_RM, onl_kgenR_val hi]
      exact onl_smul_om (onl_kgenP_img hi hj) hmap

theorem onl_K5_trans
    {i : ℕ} (hi : i < 8) {k : ℕ}
    (hk : k < 315) : ∃ h ∈ Subgroup.closure (Set.range (onl_kgenR i)),
      h • onl_om 0 = onl_om k := by
  have hc := List.all_eq_true.1 onl_k5_check.2 i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  have hmem := List.all_eq_true.1 hc.1.2 k (List.mem_range.2 hk)
  rw [List.contains_iff_mem, List.mem_map] at hmem
  obtain ⟨e, he, hek⟩ := hmem
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
  have ht' : t < 315 := by rw [hc.1.1.1] at ht; exact ht
  obtain ⟨h, hh, hh0⟩ := onl_K5_reach hi t ht'
  refine ⟨h, hh, ?_⟩
  rw [hh0, List.getD_eq_getElem _ _ ht, hek]

theorem onl_lat_RM
    (X : Subgroup RM)
    (hX : onl_Tb ≤ X) : X = onl_Tb ∨ X = onl_Bb ∨ X = ⊤ := by
  by_cases hA : X ≤ onl_Bb
  · have hidx : onl_Tb.relIndex onl_Bb = 3 := by
      have h1 := Subgroup.relIndex_mul_card (H := onl_Tb) (K := onl_Bb)
      rw [inf_of_le_left onl_Tb_le_Bb, onl_card_Tb, onl_card_Bb] at h1
      omega
    rcases onl_eq_or_eq_of_prime hX hA Nat.prime_three hidx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · right; right
    obtain ⟨x, hxX, hxB⟩ := SetLike.not_le_iff_exists.1 hA
    have hxO : x • onl_bits onl_mO ≠ onl_bits onl_mO := fun h =>
      hxB (MulAction.mem_stabilizer_iff.2 h)
    obtain ⟨k, hk, hkx⟩ : x • onl_om 0 ∈ onl_Om := by
      rw [← onl_orbit_eq]; exact MulAction.mem_orbit _ x
    obtain ⟨i, hi, t, ht, hti⟩ := onl_forest k hk
    have htT : t ∈ onl_Tb := onl_Tpp_le_Tb ht
    have htB : t • onl_bits onl_mO = onl_bits onl_mO :=
      MulAction.mem_stabilizer_iff.1 (onl_Tb_le_Bb htT)
    have hrep : onl_A (onl_reps.getD i 0) ≠ onl_mO := by
      intro h
      apply hxO
      have h1 := congrArg Prod.fst hti
      have h2 := congrArg Prod.fst hkx
      rw [Prod.smul_fst] at h1 h2
      have h3 : (onl_om (onl_reps.getD i 0)).1 = onl_bits onl_mO := by
        show onl_bits (onl_A _) = _
        rw [h]
      rw [h3, htB] at h1
      have h4 : (onl_om 0).1 = onl_bits onl_mO := by
        show onl_bits (onl_A 0) = _
        rw [onl_A0]
      rw [h4] at h2
      exact h2.symm.trans h1.symm
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hrep
      rw [onl_forest_check.2.2.1, onl_A0]
    have hi9 : i ≠ 9 := by
      rintro rfl
      exact hrep onl_forest_check.2.2.2.1
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hi' : i' < 8 := by omega
    have hg := onl_gR_rep hi'
    have hgX : onl_gR i' ∈ X := by
      have hst : (t * onl_gR i')⁻¹ * x ∈ onl_Tb := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, ← hkx, ← hti, ← hg, smul_smul t,
          inv_smul_smul]
      have htX : t ∈ X := hX htT
      have h1 : t * onl_gR i' ∈ X := by
        have := X.mul_mem hxX (X.inv_mem (hX hst))
        simpa using this
      have := X.mul_mem (X.inv_mem htX) h1
      simpa using this
    have hle : Subgroup.closure (Set.range (onl_kgenR i')) ≤ X := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      unfold onl_kgenR
      split_ifs with hj
      · exact hX (onl_Tpp_le_Tb (Subgroup.subset_closure ⟨j, hj, rfl⟩))
      · exact hgX
    have horb : onl_Om ⊆ MulAction.orbit X (onl_om 0) := by
      rintro _ ⟨k', hk', rfl⟩
      obtain ⟨h, hh, hh0⟩ := onl_K5_trans hi' hk'
      exact ⟨⟨h, hle hh⟩, hh0⟩
    have hn : 315 ≤ (MulAction.orbit X (onl_om 0)).ncard := by
      rw [← onl_ncard_Om]
      exact Set.ncard_le_ncard horb (Set.toFinite _)
    have hst : MulAction.stabilizer X (onl_om 0) = onl_Tb.subgroupOf X := by
      ext b
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
      rfl
    have h1 := (MulAction.stabilizer X (onl_om 0)).card_mul_index
    rw [MulAction.index_stabilizer, hst, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv,
      onl_card_Tb] at h1
    apply Subgroup.eq_top_of_card_eq
    have hle' : Nat.card X ≤ Nat.card RM := Subgroup.card_le_card_group X
    rw [card_RM] at hle' ⊢
    omega

theorem onl_T_le_M :
    onT ≤ onM := by
  rw [onM_eq_centralizer_z]
  intro t ht
  refine ⟨onT_le ht, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hz : onz ∈ CFSG.centerIn onT := by
    rw [onT_centerIn]
    exact Subgroup.mem_zpowers _
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 t ht)

theorem onl_card_sncon_Tb :
    Nat.card sncon_Tb = 128 := by
  have hT : Nat.card (onT.subgroupOf onM) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onl_T_le_M).toEquiv, card_onT]
  have hp : IsPGroup 2 (onT.subgroupOf onM) := IsPGroup.of_card (n := 9) (by rw [hT]; norm_num)
  have hr : (piR.comp (onT.subgroupOf onM).subtype).range = sncon_Tb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hk : Nat.card (piR.comp (onT.subgroupOf onM).subtype).ker ≤ 4 := by
    have hle : (piR.comp (onT.subgroupOf onM).subtype).ker.map (onT.subgroupOf onM).subtype ≤
        piR.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), ker_piR,
      card_onQ_subgroupOf_M] at h
  have h := card_range_mul_ker (piR.comp (onT.subgroupOf onM).subtype)
  rw [hT, hr] at h
  have h2 : 512 ≤ Nat.card sncon_Tb * 4 :=
    calc 512 = _ := h
      _ ≤ _ := Nat.mul_le_mul_left _ hk
  have hpT : IsPGroup 2 sncon_Tb := hp.map piR
  obtain ⟨k, hk'⟩ := hpT.exists_card_eq
  have hdvd : 2 ^ k ∣ 40320 := by
    rw [← hk', ← card_RM]
    exact Subgroup.card_subgroup_dvd_card _
  have hk7 : k ≤ 7 := by
    by_contra hk8
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 8 ≤ k)).trans hdvd) (by norm_num)
  have hup : 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
  rw [hk'] at h2 ⊢
  have : 2 ^ k ≥ 128 := by omega
  omega

theorem onl_sncon_Tb_le_Pb :
    sncon_Tb ≤ sncon_Pb := by
  intro t ht
  rw [sncon_Pb, Subgroup.mem_normalizer_iff]
  intro h
  rw [sncon_Cb, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_mem (mul_mem ht h1) (inv_mem ht), XR_normal.conj_mem h h2 t⟩
  · rintro ⟨h1, h2⟩
    have e : h = t⁻¹ * (t * h * t⁻¹) * t := by group
    rw [e]
    refine ⟨mul_mem (mul_mem (inv_mem ht) h1) ht, ?_⟩
    have := XR_normal.conj_mem _ h2 t⁻¹
    rwa [inv_inv] at this

theorem onl_exists_conj :
    ∃ r : RM, sncon_Tb = MulAut.conj r • onl_Tb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ H : Subgroup RM, Nat.card H = 128 → ¬ 2 ∣ H.index := fun H hH => by
    have h := H.card_mul_index
    rw [hH, card_RM] at h
    have h315 : H.index = 315 := by omega
    rw [h315]
    decide
  have hp1 : IsPGroup 2 onl_Tb := IsPGroup.of_card (n := 7) (by rw [onl_card_Tb]; norm_num)
  have hp2 : IsPGroup 2 sncon_Tb := IsPGroup.of_card (n := 7) (by rw [onl_card_sncon_Tb]; norm_num)
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq RM (hp1.toSylow (hidx _ onl_card_Tb))
    (hp2.toSylow (hidx _ onl_card_sncon_Tb))
  refine ⟨r, ?_⟩
  have := congrArg (fun P : Sylow 2 RM => (P : Subgroup RM)) hr
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
  exact this.symm

theorem onl_lat_conj
    {r : RM}
    (hr : sncon_Tb = MulAut.conj r • onl_Tb) (X : Subgroup RM) (hX : sncon_Tb ≤ X) :
    X = sncon_Tb ∨ X = MulAut.conj r • onl_Bb ∨ X = ⊤ := by
  set X' := (MulAut.conj r)⁻¹ • X with hX'def
  have hXX : X = MulAut.conj r • X' := (smul_inv_smul _ _).symm
  have hX' : onl_Tb ≤ X' := by
    rw [← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj r), ← hr, ← hXX]
    exact hX
  rcases onl_lat_RM X' hX' with h | h | h
  · left; rw [hXX, h, ← hr]
  · right; left; rw [hXX, h]
  · right; right
    apply Subgroup.eq_top_of_card_eq
    rw [hXX, ← Nat.card_congr (Subgroup.equivSMul (MulAut.conj r) X').toEquiv, h,
      Subgroup.card_top]

theorem onl_lat_sncon
    (X : Subgroup RM)
    (hX : sncon_Tb ≤ X) : X = sncon_Tb ∨ X = sncon_Pb ∨ X = ⊤ := by
  obtain ⟨r, hr⟩ := onl_exists_conj
  have hP : sncon_Pb = MulAut.conj r • onl_Bb := by
    rcases onl_lat_conj hr sncon_Pb onl_sncon_Tb_le_Pb with h | h | h
    · exfalso
      have := sncon_card_Pb
      rw [h, onl_card_sncon_Tb] at this
      omega
    · exact h
    · exfalso
      have := sncon_card_Pb
      rw [h, Subgroup.card_top, card_RM] at this
      omega
  rw [hP]
  exact onl_lat_conj hr X hX

theorem onl_Q_le_T :
    onQ ≤ onT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (onQ.subgroupOf onM).Normal := ker_piR ▸ piR.normal_ker
  have hQ : IsPGroup 2 (onQ.subgroupOf onM) :=
    IsPGroup.of_card (n := 2) (by rw [card_onQ_subgroupOf_M]; norm_num)
  have hTc : Nat.card (onT.subgroupOf onM) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onl_T_le_M).toEquiv, card_onT]
  have hT : IsPGroup 2 (onT.subgroupOf onM) := IsPGroup.of_card (n := 9) (by rw [hTc]; norm_num)
  have hsup : IsPGroup 2 ↥(onT.subgroupOf onM ⊔ onQ.subgroupOf onM) :=
    hT.to_sup_of_normal_right hQ
  obtain ⟨k, hk⟩ := hsup.exists_card_eq
  have hdvd : 2 ^ k ∣ 161280 := by
    rw [← hk, ← card_onM]
    exact Subgroup.card_subgroup_dvd_card _
  have hk9 : k ≤ 9 := by
    by_contra hk10
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 10 ≤ k)).trans hdvd) (by norm_num)
  have heq : onT.subgroupOf onM = onT.subgroupOf onM ⊔ onQ.subgroupOf onM :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by
      rw [hk, hTc]
      calc 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk9
        _ = 512 := by norm_num)
  intro q hq
  have h1 : (⟨q, onQ_le_M hq⟩ : onM) ∈ onT.subgroupOf onM := by
    rw [heq]
    exact (le_sup_right : onQ.subgroupOf onM ≤ _) (Subgroup.mem_subgroupOf.2 hq)
  exact Subgroup.mem_subgroupOf.1 h1

abbrev onl_toPv
    (W : Subgroup onM) :
    Subgroup Pv :=
  (W.map onM.subtype).subgroupOf Pv

theorem onl_latFact :
    onl_LatFact := by
  intro X hUX hXC
  set XM : Subgroup onM := (X.map Pv.subtype).subgroupOf onM with hXMdef
  have hle : X.map Pv.subtype ≤ onM := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hXC hx)
  have hXeq : X = onl_toPv XM := by
    rw [onl_toPv, hXMdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hle]
    exact (Subgroup.comap_map_eq_self_of_injective Pv.subtype_injective X).symm
  have hTM : onT.subgroupOf onM ≤ XM := by
    intro m hm
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact ⟨⟨m, onM_le m.2⟩, hUX (Subgroup.mem_subgroupOf.2 hm), rfl⟩
  have hker : piR.ker ≤ onT.subgroupOf onM := by
    rw [ker_piR]
    intro m hm
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact onl_Q_le_T hm
  have hXM : XM = (XM.map piR).comap piR := by
    rw [Subgroup.comap_map_eq, sup_eq_left.2 (hker.trans hTM)]
  have hTb : sncon_Tb ≤ XM.map piR := Subgroup.map_mono hTM
  have hT : onl_toPv (onT.subgroupOf onM) = onT.subgroupOf Pv := by
    rw [onl_toPv, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 onl_T_le_M]
  rcases onl_lat_sncon _ hTb with h | h | h
  · left
    rw [hXeq, hXM, h, sncon_Tb, Subgroup.comap_map_eq, sup_eq_left.2 hker, hT]
  · right; left
    rw [hXeq, hXM, h]
    rfl
  · right; right
    rw [hXeq, hXM, h, Subgroup.comap_top, onl_toPv, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

theorem onl_kONanLattice_of_par
    (hP : onl_ParFact) : K_ONanLattice :=
  onl_kONanLattice_of_facts onl_latFact hP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
