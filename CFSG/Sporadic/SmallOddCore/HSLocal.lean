module

public import CFSG.Sporadic.SmallOddCore.HS
public import CFSG.Sporadic.SmallOddCore.HSLocalCheck
public import CFSG.Sporadic.SmallOddCore.CentCoset
public import CFSG.Sporadic.SmallOddCore.LocalTransport

public noncomputable section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Blueprint
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LocalAnalysis.ComponentInitial CFSG.Sporadic.SmallOddCore.Native

theorem tabRep_natArr {n : ℕ} {T : Table} (hp : permOK n T = true) (hs : (natArr T).size = n) :
    TabRep (natArr T) (tp n T) :=
  ⟨hs, co2Rep_natArr_iff.2 (rep_tp hp)⟩

abbrev hsT1 : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl 5)

abbrev hsT2 : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl 12)

abbrev hsC1 : Subgroup (Equiv.Perm (Fin 3850)) := hsP ⊓ centralizer ({hsT1} : Set _)

abbrev hsC2 : Subgroup (Equiv.Perm (Fin 3850)) := hsP ⊓ centralizer ({hsT2} : Set _)

theorem hs_reps :
    closure (tp 3850 '' {x | x ∈ [hsCentTbl 6, hsCentTbl 7].toArray}) = hsC1 ∧
    closure (tp 3850 '' {x | x ∈ [hsCentTbl 13, hsCentTbl 14, hsCentTbl 15,
      hsCentTbl 16].toArray}) = hsC2 ∧ Nat.card hsC1 = 7680 ∧ Nat.card hsC2 = 2880 ∧
    ∀ τ ∈ hsP, orderOf τ = 2 →
      ∃ r ∈ ({hsT1, hsT2} : Set (Equiv.Perm (Fin 3850))), ∃ g ∈ hsP, τ = g * r * g⁻¹ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨-, -, -, h4, h5, -⟩ := hrows _ List.mem_cons_self
  obtain ⟨-, -, -, h4', h5', -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only [hsC] at h4 h4' h5 h5'
  refine ⟨h4, h4', h5, h5', fun τ hτ hτ2 => ?_⟩
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ (Subgroup.mem_sup_left hτ) hτ2
  have key : ∀ x : Equiv.Perm (Fin 3850), g * x * g⁻¹ ∈ hsP → x ∈ hsP := fun x hx => by
    have := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) hx) hg
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨hsT1, Or.inl rfl, g, hg, ?_⟩
    dsimp only
  · refine ⟨hsT2, Or.inr rfl, g, hg, ?_⟩
    dsimp only
  · exfalso
    obtain ⟨-, -, h3, -⟩ := hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))
    dsimp only at h3 hτ
    exact h3.1 rfl (key _ hτ)
  · exfalso
    obtain ⟨-, -, h3, -⟩ := hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
    dsimp only at h3 hτ
    exact h3.1 rfl (key _ hτ)

@[expose] def hsC1Perm (k : ℕ) : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl (k + 6))

@[expose] def hsC2Perm (k : ℕ) : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl (k + 13))

theorem tabRep_hsC1Tabs :
    ∀ k < hsC1Tabs.size, TabRep hsC1Tabs[k]! (hsC1Perm k) := by
  intro k hk
  have hk2 : k < 2 := by simpa [hsC1Tabs] using hk
  rw [hsC1Tabs, getElem!_pos _ k (by simpa using hk2), Array.getElem_ofFn]
  exact tabRep_natArr (hs_local_basic.1 k hk2).1 (hs_local_basic.1 k hk2).2

theorem tabRep_hsC2Tabs :
    ∀ k < hsC2Tabs.size, TabRep hsC2Tabs[k]! (hsC2Perm k) := by
  intro k hk
  have hk4 : k < 4 := by simpa [hsC2Tabs] using hk
  rw [hsC2Tabs, getElem!_pos _ k (by simpa using hk4), Array.getElem_ofFn]
  exact tabRep_natArr (hs_local_basic.2.1 k hk4).1 (hs_local_basic.2.1 k hk4).2

theorem hsC1_enumerates :
    Enumerates (genGroup 3850 hsC1Tabs hsC1Perm) hsC1Enum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_hsC1Tabs) (genGroup_hgens tabRep_hsC1Tabs) hs_local_C1.1

theorem hsC1_eq :
    genGroup 3850 hsC1Tabs hsC1Perm = hsC1 := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [genGroup, closure_le, ← hs_reps.1]
    rintro _ ⟨j, hj, rfl⟩
    have hj2 : j < 2 := by simpa [hsC1Tabs] using hj
    refine subset_closure ⟨hsCentTbl (j + 6), ?_, rfl⟩
    interval_cases j <;> simp
  · rw [hs_reps.2.2.1, hsC1_enumerates.card, Array.length_toList, hs_local_C1.2.1]

theorem hsC2_eq :
    genGroup 3850 hsC2Tabs hsC2Perm = hsC2 := by
  rw [← hs_reps.2.1]
  refine le_antisymm ?_ ?_
  · rw [genGroup, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj4 : j < 4 := by simpa [hsC2Tabs] using hj
    refine subset_closure ⟨hsCentTbl (j + 13), ?_, rfl⟩
    interval_cases j <;> simp
  · rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x = hsCentTbl 13 ∨ x = hsCentTbl 14 ∨ x = hsCentTbl 15 ∨ x = hsCentTbl 16 := by
      simpa using hx
    have hmem : ∀ j < 4, tp 3850 (hsCentTbl (j + 13)) ∈
        genGroup 3850 hsC2Tabs hsC2Perm := fun j hj =>
      subset_closure ⟨j, by simpa [hsC2Tabs] using hj, rfl⟩
    obtain h | h | h | h := hx'
    · rw [h]
      exact hmem 0 (by norm_num)
    · rw [h]
      exact hmem 1 (by norm_num)
    · rw [h]
      exact hmem 2 (by norm_num)
    · rw [h]
      exact hmem 3 (by norm_num)

@[expose] def hsQPerm (j : ℕ) : Equiv.Perm (Fin 3850) := ((hsQWords.getD j []).map hsC1Perm).prod

theorem tabRep_hsQGens :
    ∀ j < hsQGens.size, TabRep hsQGens[j]! (hsQPerm j) := by
  intro j hj
  have hj6 : j < 6 := by simpa [hsQGens] using hj
  rw [hsQGens, getElem!_pos _ j (by simpa using hj6), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_hsC1Tabs _ fun i hi => by
    have := hs_local_basic.2.2.1 j hj6 i hi
    simpa [hsC1Tabs] using this

theorem hsQ_enumerates :
    Enumerates (genGroup 3850 hsQGens hsQPerm) hsQEnum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_hsQGens) (genGroup_hgens tabRep_hsQGens) hs_local_Q.1

theorem hsQPerm_mem
    (j : ℕ) : hsQPerm j ∈ genGroup 3850 hsC1Tabs hsC1Perm := by
  refine (genGroup 3850 hsC1Tabs hsC1Perm).list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  by_cases hi2 : i < 2
  · exact subset_closure ⟨i, by simpa [hsC1Tabs] using hi2, rfl⟩
  · have hq : ∀ j, ∀ i ∈ hsQWords.getD j [], i < 2 := by
      intro j i hi
      by_cases hj : j < 6
      · exact hs_local_basic.2.2.1 j hj i hi
      · rw [List.getD_eq_default _ _ (by simp [hsQWords]; omega)] at hi
        exact absurd hi (List.not_mem_nil)
    exact absurd (hq j i hi) hi2

theorem hs_Q_facts :
    Nat.card (genGroup 3850 hsQGens hsQPerm) = 64 ∧ genGroup 3850 hsQGens hsQPerm ≤ hsC1 ∧
      hsC1 ≤ normalizer (genGroup 3850 hsQGens hsQPerm : Set (Equiv.Perm (Fin 3850))) ∧
      Nat.card ↥(hsC1 ⊓ centralizer
        (genGroup 3850 hsQGens hsQPerm : Set (Equiv.Perm (Fin 3850)))) = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsQ_enumerates.card, Array.length_toList, hs_local_Q.2.1]
  · rw [← hsC1_eq, genGroup, closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact hsQPerm_mem j
  · rw [← hsC1_eq]
    exact le_normalizer_of_normalOK tabRep_hsC1Tabs tabRep_hsQGens hsQ_enumerates hs_local_Q.2.2
  · rw [← hsC1_eq, card_inf_centralizer_of_enum hsC1_enumerates tabRep_hsQGens,
      hs_local_C1.2.2]

theorem hsC1_no_component
    {B : Subgroup (Equiv.Perm (Fin 3850))}
    (hB : CFSG.Assembly.IsComponentOf B hsC1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQcard, hQC1, hC1Q, hC1cent⟩ := hs_Q_facts
  rcases isComponentOf_le_or_commute hB hQC1 hC1Q with hle | hcomm
  · exact not_le_of_isPGroup hB.2.2 (isPGroup_two_of_card (k := 6) (by rw [hQcard]; norm_num)) hle
  · have hle : B ≤ hsC1 ⊓ centralizer
        (genGroup 3850 hsQGens hsQPerm : Set (Equiv.Perm (Fin 3850))) := by
      intro x hx
      refine mem_inf.mpr ⟨hB.1 hx, ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
      rw [mem_centralizer_iff] at this
      exact this y hy
    exact not_le_of_isPGroup hB.2.2
      (isPGroup_two_of_card (k := 2) (by rw [hC1cent]; norm_num)) hle

@[expose] def hsDPerm (j : ℕ) : Equiv.Perm (Fin 3850) := ((hsDWords.getD j []).map hsC2Perm).prod

theorem tabRep_hsDGens :
    ∀ j < hsDGens.size, TabRep hsDGens[j]! (hsDPerm j) := by
  intro j hj
  have hj2 : j < 2 := by simpa [hsDGens] using hj
  rw [hsDGens, getElem!_pos _ j (by simpa using hj2), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_hsC2Tabs _ fun i hi => by
    have := hs_local_basic.2.2.2 j hj2 i hi
    simpa [hsC2Tabs] using this

theorem hsD_enumerates :
    Enumerates (genGroup 3850 hsDGens hsDPerm) hsDEnum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_hsDGens) (genGroup_hgens tabRep_hsDGens) hs_local_D.1

theorem hsDPerm_mem
    (j : ℕ) : hsDPerm j ∈ genGroup 3850 hsC2Tabs hsC2Perm := by
  refine (genGroup 3850 hsC2Tabs hsC2Perm).list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  by_cases hi4 : i < 4
  · exact subset_closure ⟨i, by simpa [hsC2Tabs] using hi4, rfl⟩
  · have hq : ∀ j, ∀ i ∈ hsDWords.getD j [], i < 4 := by
      intro j i hi
      by_cases hj : j < 2
      · exact hs_local_basic.2.2.2 j hj i hi
      · rw [List.getD_eq_default _ _ (by simp [hsDWords]; omega)] at hi
        exact absurd hi (List.not_mem_nil)
    exact absurd (hq j i hi) hi4

theorem hsD_cert :
    ClassCert 3850 hsDGens hsDInvs hsDEnum 7 hsDClassWords hsDClassSizes
    hsDOrbits where
  enum := hs_local_D.1
  words_lt := hs_local_classes.2.2.2.2.1
  rep0 := hs_local_classes.2.2.2.2.2
  orbit := hs_local_classes.2.2.1
  notIn := hs_local_classes.2.2.2.1
  cover := by
    intro k hk
    obtain ⟨l, hl, hf⟩ := cover_of_coverAllOK hs_local_cover k hk
    exact ⟨l, by rw [hs_local_classes.1] at hl; exact hl, hf⟩

@[expose] def hsCosPerm (i : ℕ) : Equiv.Perm (Fin 3850) :=
  ((hsCosWords.getD i []).map hsC2Perm).prod

theorem tabRep_hsCosTabs {i : ℕ} (hi : i < 8) :
    TabRep hsCosTabs[i]! (hsCosPerm i) := by
  rw [hsCosTabs, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_hsC2Tabs _ fun j hj => by
    have := hs_local_cosets.1 i hi j hj
    simpa [hsC2Tabs] using this

theorem tabRep_hsCosInvs {i : ℕ} (hi : i < 8) :
    TabRep hsCosInvs[i]! (hsCosPerm i)⁻¹ :=
  invsOK_spec hs_local_cosets.2.1 (by simpa [hsCosTabs] using hi) (tabRep_hsCosTabs hi)

theorem hsCosPerm_mem {i : ℕ} (hi : i < 8) :
    hsCosPerm i ∈ genGroup 3850 hsC2Tabs hsC2Perm := by
  refine (genGroup 3850 hsC2Tabs hsC2Perm).list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact subset_closure ⟨j, by simpa [hsC2Tabs] using hs_local_cosets.1 i hi j hj, rfl⟩

theorem not_mem_toList_of_notInOK {T : Array Tab} {x : Tab} (h : notInOK T x = true) :
    x ∉ T.toList := by
  intro hx
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem hx
  simp only [notInOK, allBelow_eq_true] at h
  have := h k hk
  simp at this

theorem hsCos_dist {i j : ℕ} (hi : i < 8) (hj : j < 8)
    (hij : i ≠ j) : (hsCosPerm i)⁻¹ * hsCosPerm j ∉ genGroup 3850 hsDGens hsDPerm := by
  intro hm
  obtain ⟨t, ht, hrep⟩ := hsD_enumerates.complete _ hm
  have e := hrep.tab_eq ((tabRep_hsCosInvs hi).comp (tabRep_hsCosTabs hj))
  exact not_mem_toList_of_notInOK (hs_local_cosets.2.2.1 i hi j hj hij) (e ▸ ht)

theorem hsCos_one_mem :
    hsCosPerm 1 ∈ centralizer (genGroup 3850 hsDGens hsDPerm : Set (Equiv.Perm (Fin 3850))) := by
  have hle : genGroup 3850 hsDGens hsDPerm ≤ centralizer ({hsCosPerm 1} : Set _) := by
    rw [genGroup, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hc := hs_local_cosets.2.2.2.1
    simp only [commAll, allBelow_eq_true] at hc
    have e := ((tabRep_hsCosTabs (i := 1) (by norm_num)).comp (tabRep_hsDGens j hj)).beq_iff
      ((tabRep_hsDGens j hj).comp (tabRep_hsCosTabs (i := 1) (by norm_num)))
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (e.1 (hc j hj)).symm
  rw [mem_centralizer_iff]
  intro h hh
  exact mem_centralizer_singleton_iff.1 (hle hh)

theorem hsCos_bad {i : ℕ} (hi : i < 6) :
    ∃ x ∈ genGroup 3850 hsDGens hsDPerm, ∀ d ∈ genGroup 3850 hsDGens hsDPerm,
      d * x * d⁻¹ ≠ (hsCosPerm (i + 2))⁻¹ * x * hsCosPerm (i + 2) := by
  have hl : hsCosCls.getD i 0 < 7 := by interval_cases i <;> decide
  refine ⟨classRepPerm hsDPerm hsDClassWords (hsCosCls.getD i 0), classRep_mem hsD_cert hl,
    fun d hd he => ?_⟩
  obtain ⟨t, ht, hrep⟩ := (class_orbit' tabRep_hsDGens hsD_cert hl).2.1 d hd
  have hx := tabRep_classRep tabRep_hsDGens hsD_cert hl
  have hg : TabRep hsCosTabs[i + 2]! (hsCosPerm (i + 2))⁻¹⁻¹ := by
    rw [inv_inv]
    exact tabRep_hsCosTabs (by omega)
  have hc := (tabRep_hsCosInvs (i := i + 2) (by omega)).conjTab hx hg
  rw [inv_inv, ← he] at hc
  exact not_mem_toList_of_notInOK (hs_local_cosets.2.2.2.2 i hi) (hrep.tab_eq hc ▸ ht)

theorem hsC2_cent_card
    (hs : IsSimpleGroup (genGroup 3850 hsDGens hsDPerm))
    (hnab : ∃ a b : genGroup 3850 hsDGens hsDPerm, a * b ≠ b * a)
    (hDC : genGroup 3850 hsDGens hsDPerm ≤ genGroup 3850 hsC2Tabs hsC2Perm) :
    Nat.card ↥(genGroup 3850 hsC2Tabs hsC2Perm ⊓ centralizer
      (genGroup 3850 hsDGens hsDPerm : Set (Equiv.Perm (Fin 3850)))) = 2 := by
  refine le_antisymm ?_ ?_
  · have h := card_inf_centralizer_le_of_cosets hDC hs hnab (k := 8)
      (fun i => hsCosPerm i.val) (fun i => hsCosPerm_mem i.2)
      (fun i j hij => hsCos_dist i.2 j.2 (fun e => hij (Fin.ext e)))
      (by rw [hsC2_eq, hs_reps.2.2.2.1, hsD_enumerates.card, Array.length_toList, hs_local_D.2.1])
      {0, 1} (fun i hi => by
        have h2 : 2 ≤ i.val := by
          by_contra hlt
          interval_cases h : i.val <;> simp [Fin.ext_iff, h] at hi
        obtain ⟨x, hx, hne⟩ := hsCos_bad (i := i.val - 2) (by omega)
        rw [Nat.sub_add_cancel h2] at hne
        exact ⟨x, hx, hne⟩)
    simpa using h
  · have h1 : hsCosPerm 1 ∈ genGroup 3850 hsC2Tabs hsC2Perm ⊓ centralizer
        (genGroup 3850 hsDGens hsDPerm : Set (Equiv.Perm (Fin 3850))) :=
      mem_inf.2 ⟨hsCosPerm_mem (by norm_num), hsCos_one_mem⟩
    have hne : hsCosPerm 1 ≠ 1 := by
      intro e
      apply hsCos_dist (i := 0) (j := 1) (by norm_num) (by norm_num) (by norm_num)
      rw [e, mul_one]
      exact inv_mem (one_mem _)
    have hlt := (Subgroup.one_lt_card_iff_ne_bot _).2
      ((Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨_, h1⟩, fun e => hne (congrArg Subtype.val e)⟩)
    omega

theorem hs_D_facts :
    (IsSimpleGroup (genGroup 3850 hsDGens hsDPerm) ∧
      ∃ a b : genGroup 3850 hsDGens hsDPerm, a * b ≠ b * a) ∧
    Nat.card (genGroup 3850 hsDGens hsDPerm) = 360 ∧ genGroup 3850 hsDGens hsDPerm ≤ hsC2 ∧
      hsC2 ≤ normalizer (genGroup 3850 hsDGens hsDPerm : Set (Equiv.Perm (Fin 3850))) ∧
      Nat.card ↥(hsC2 ⊓ centralizer
        (genGroup 3850 hsDGens hsDPerm : Set (Equiv.Perm (Fin 3850)))) = 2 := by
  have hsim := isSimpleGroup_of_classCert tabRep_hsDGens hsD_cert (by norm_num)
    (by rw [hs_local_D.2.1]; norm_num) (by rw [hs_local_D.2.1]; exact hs_local_sums)
    ⟨1, by decide⟩
  have hDC : genGroup 3850 hsDGens hsDPerm ≤ genGroup 3850 hsC2Tabs hsC2Perm := by
    rw [genGroup, closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact hsDPerm_mem j
  refine ⟨hsim, ?_, ?_, ?_, ?_⟩
  · rw [hsD_enumerates.card, Array.length_toList, hs_local_D.2.1]
  · rw [← hsC2_eq]
    exact hDC
  · rw [← hsC2_eq]
    exact le_normalizer_of_normalOK tabRep_hsC2Tabs tabRep_hsDGens hsD_enumerates hs_local_D.2.2
  · rw [← hsC2_eq]
    exact hsC2_cent_card hsim.1 hsim.2 hDC

theorem hsC2_component
    {B : Subgroup (Equiv.Perm (Fin 3850))}
    (hB : CFSG.Assembly.IsComponentOf B hsC2) : B = genGroup 3850 hsDGens hsDPerm := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hDs, hDnab⟩, -, hDC2, hC2D, hC2cent⟩ := hs_D_facts
  rcases isComponentOf_le_or_commute hB hDC2 hC2D with hle | hcomm
  · obtain ⟨hDq, hDZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDnab
    exact isComponentOf_eq_of_isQuasisimple (isComponentOf_of_le hB hle hDC2) hDq (p := 2)
      (by rw [hDZ]; exact IsPGroup.of_bot)
  · exfalso
    have hle : B ≤ hsC2 ⊓ centralizer
        (genGroup 3850 hsDGens hsDPerm : Set (Equiv.Perm (Fin 3850))) := by
      intro x hx
      refine mem_inf.mpr ⟨hB.1 hx, ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
      rw [mem_centralizer_iff] at this
      exact this y hy
    exact not_le_of_isPGroup hB.2.2
      (isPGroup_two_of_card (k := 1) (by rw [hC2cent]; norm_num)) hle

abbrev SimpleOfOrder360 {G : Type*} [Group G] (B : Subgroup G) : Prop :=
  IsSimpleGroup B ∧ (∃ a b : B, a * b ≠ b * a) ∧ Nat.card B = 360

theorem simpleOfOrder360_congr {G H : Type*} [Group G] [Group H] {B : Subgroup G}
    {B' : Subgroup H} (e : B ≃* B') (h : SimpleOfOrder360 B) : SimpleOfOrder360 B' := by
  obtain ⟨hs, ⟨a, b, hab⟩, hc⟩ := h
  refine ⟨e.symm.isSimpleGroup, ⟨e a, e b, fun h' => hab ?_⟩, by rw [← Nat.card_congr e.toEquiv,
    hc]⟩
  have := congrArg e.symm h'
  simpa only [map_mul, MulEquiv.symm_apply_apply] using this

theorem hsP_local_components
    {τ : Equiv.Perm (Fin 3850)} (hτP : τ ∈ hsP) (hτ : orderOf τ = 2)
    {B : Subgroup (Equiv.Perm (Fin 3850))}
    (hB : CFSG.Assembly.IsComponentOf B (hsP ⊓ centralizer ({τ} : Set _))) :
    SimpleOfOrder360 B := by
  obtain ⟨r, hr, g, hg, rfl⟩ := hs_reps.2.2.2.2 τ hτP hτ
  have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hgr : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
  have hBr : CFSG.Assembly.IsComponentOf (B.map (MulAut.conj g⁻¹).toMonoidHom)
      (hsP ⊓ centralizer ({r} : Set _)) := by
    have h := (isComponentOf_map_iff hfinj).2 hB
    rwa [Subgroup.map_inf _ _ _ hfinj, map_conj_self (hsP.inv_mem hg), map_conj_centralizer,
      Set.image_singleton, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgr] at h
  refine simpleOfOrder360_congr (B.equivMapOfInjective _ hfinj).symm ?_
  rcases hr with rfl | rfl
  · exact (hsC1_no_component hBr).elim
  · rw [hsC2_component hBr]
    obtain ⟨⟨hDs, hDnab⟩, hDcard, -⟩ := hs_D_facts
    exact ⟨hDs, hDnab, hDcard⟩

theorem cti_hs_involution_local_components_simple_order_360
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.HS)) {t : T} (ht : orderOf t = 2) {B : Subgroup T}
    (hB : CFSG.Assembly.IsComponentOf B (centralizer ({t} : Set T))) :
    IsSimpleGroup B ∧ (∃ a b : B, a * b ≠ b * a) ∧ Nat.card B = 360 := by
  obtain ⟨e⟩ := hT
  set ι : T →* Equiv.Perm (Fin 3850) := hsP.subtype.comp (e.trans hsPermEquiv).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (e.trans hsPermEquiv).injective
  have hrange : ι.range = hsP := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (e.trans hsPermEquiv).surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hτP : ι t ∈ hsP := hrange ▸ ⟨t, rfl⟩
  have hτ : orderOf (ι t) = 2 := by rw [orderOf_injective ι hι, ht]
  have hB' : CFSG.Assembly.IsComponentOf (B.map ι)
      (hsP ⊓ centralizer ({ι t} : Set (Equiv.Perm (Fin 3850)))) := by
    have := (isComponentOf_map_iff hι).2 hB
    rwa [map_centralizer_eq_inf hι, hrange, Set.image_singleton] at this
  exact simpleOfOrder360_congr (B.equivMapOfInjective ι hι).symm (hsP_local_components hτP hτ hB')

end CFSG.Sporadic.SmallOddCore
