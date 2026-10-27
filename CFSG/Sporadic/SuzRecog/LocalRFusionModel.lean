module

public import CFSG.Sporadic.SuzRecog.LocalRFusionCert
public import CFSG.Sporadic.SuzRecog.Cover
public import CFSG.Sporadic.HN.Local.ClassCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2.Native
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.SuzRecog

section Model


theorem sizes_facts :
    (∀ k < 10, (cTab k).size = 1782) ∧ (∀ i < 4, (lambdaTab i).size = 1782) ∧
      (∀ j < 13, (sylowGenTab j).size = 1782) ∧ (qProds[4]!).size = 1782 ∧
      (qProds[8]!).size = 1782 := by
  have h := fusionSizes_check
  simp only [sizesCheck, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem gen_facts {k : ℕ} (hk : k < 10) :
    (∀ a ∈ cBackWords.getD k [], a < 2) ∧ orbWord (cBackWords.getD k []) = cTab k := by
  have h := fusionGen_check
  simp only [genCheck, allBelow_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  exact h k hk

theorem orbit_facts {i : ℕ} (hi : i < 4) :
    orbitOK 1782 orbGens orbInvs (lambdaTab i) (lambdaOrbit2 i) = true ∧
      (lambdaOrbit2 i).tabs.size = lambdaSizes[i]! := by
  have h := fusionOrbits_check
  simp only [orbits2Check, allBelow_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact h i hi

theorem sylow_facts :
    enumOK 1782 s1Gens s1Enum = true ∧ s1Enum.tabs.size = 8192 ∧
      coverOK 1782 s1Enum.tabs lambdaOrbitTabs2 = true := by
  have h := fusionSylow_check
  simp only [sylow2Check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem v0_facts :
    s1V0.size = 512 ∧
      (∀ j < 512, pow4Tab s1V0[j]! = idTab 1782 ∨ pow4Tab s1V0[j]! = tTab) ∧
      ∃ j < 512, pow4Tab s1V0[j]! = tTab := by
  have h := fusionV0_check
  simp only [v02Check, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, allBelow_eq_true,
    anyBelow_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem reps_facts :
    (∀ i < 4, comp 1782 (lambdaTab i) (lambdaTab i) = idTab 1782 ∧
      ¬ lambdaTab i = idTab 1782 ∧ fixedCount (lambdaTab i) = lambdaFixed[i]!) ∧
    comp 1782 qProds[4]! qProds[4]! = idTab 1782 ∧ comp 1782 qProds[8]! qProds[8]! = idTab 1782 ∧
    comp 1782 qProds[4]! (lambdaTab 1) = comp 1782 (lambdaTab 1) qProds[4]! ∧
    comp 1782 qProds[8]! (lambdaTab 1) = comp 1782 (lambdaTab 1) qProds[8]! ∧
    comp 1782 (comp 1782 (comp 1782 qProds[4]! qProds[8]!) qProds[4]!) qProds[8]! = tTab := by
  have h := fusionReps_check
  simp only [repsCheck, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne,
    allBelow_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨fun i hi => ⟨(h1 i hi).1.1, (h1 i hi).1.2, (h1 i hi).2⟩, h2, h3, h4, h5, h6⟩

@[expose] def cGens : Set (Equiv.Perm (Fin 1782)) := {g | ∃ k < 10, cPerm k = g}

@[expose] def cGens2 : Set (Equiv.Perm (Fin 1782)) := {g | ∃ j < 2, cPerm (2 + 2 * j) = g}

theorem fusionGens_size : fusionGens.size = 10 := Array.size_ofFn

theorem fusionGens_get {k : ℕ} (hk : k < 10) : fusionGens[k]! = cTab k := by
  rw [fusionGens, getElem!_ofFn' _ hk]

theorem closure_cGens : closure cGens = invE 1 := by
  refine le_antisymm ((closure_le _).mpr ?_) ?_
  · rintro _ ⟨k, hk, rfl⟩
    exact cPerm_mem hk
  · rw [invE, CFSG.Certificates.RawSchreierDatum.originalSubgroup, closure_le]
    intro g hg
    obtain ⟨k, hk, hrep⟩ := gen_rep hg
    exact subset_closure ⟨k, hk, (rep_cPerm hk).unique hrep⟩

theorem orbGens_size : orbGens.size = 2 := rfl

theorem getElem!_pair_literal {α : Type*} [Inhabited α] (a b : α) :
    (#[a, b] : Array α)[0]! = a ∧ (#[a, b] : Array α)[1]! = b := ⟨rfl, rfl⟩

theorem orbGens_get {j : ℕ} (hj : j < 2) : orbGens[j]! = cTab (2 + 2 * j) := by
  interval_cases j
  · exact (getElem!_pair_literal _ _).1
  · exact (getElem!_pair_literal _ _).2

theorem tabRep_cPerm {k : ℕ} (hk : k < 10) : TabRep (cTab k) (cPerm k) :=
  ⟨sizes_facts.1 k hk, rep_cPerm hk⟩

theorem cGens2_hA : ∀ a ∈ cGens2, ∃ j < orbGens.size, TabRep orbGens[j]! a := by
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, by rw [orbGens_size]; exact hj, by
    rw [orbGens_get hj]; exact tabRep_cPerm (by omega)⟩

theorem cGens2_hgens : ∀ j < orbGens.size, ∃ a ∈ cGens2, TabRep orbGens[j]! a := by
  intro j hj
  rw [orbGens_size] at hj
  exact ⟨cPerm (2 + 2 * j), ⟨j, hj, rfl⟩, by
    rw [orbGens_get hj]; exact tabRep_cPerm (by omega)⟩

theorem tabRep_orbWord {w : List ℕ} (hw : ∀ a ∈ w, a < 2) :
    ∃ g ∈ closure cGens2, TabRep (orbWord w) g := by
  induction w with
  | nil =>
    have e : orbWord [] = idTab 1782 := by
      unfold orbWord
      rw [List.foldr_nil]
    rw [e]
    exact ⟨1, one_mem _, TabRep.idTab⟩
  | cons a w ih =>
    obtain ⟨g, hg, hr⟩ := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
    have ha : a < 2 := hw a List.mem_cons_self
    have e : orbWord (a :: w) = comp 1782 orbGens[a]! (orbWord w) := by
      unfold orbWord
      rw [List.foldr_cons]
    have hk : 2 + 2 * a < 10 := by omega
    rw [e, orbGens_get ha]
    exact ⟨cPerm (2 + 2 * a) * g, mul_mem (subset_closure ⟨a, ha, rfl⟩) hg,
      (tabRep_cPerm hk).comp hr⟩

theorem closure_cGens2 : closure cGens2 = invE 1 := by
  refine le_antisymm ((closure_le _).mpr ?_) ?_
  · rintro _ ⟨j, hj, rfl⟩
    exact cPerm_mem (by omega)
  · rw [invE, CFSG.Certificates.RawSchreierDatum.originalSubgroup, closure_le]
    intro g hg
    obtain ⟨k, hk, hrep⟩ := gen_rep hg
    obtain ⟨hw, he⟩ := gen_facts hk
    obtain ⟨g', hg', hr⟩ := tabRep_orbWord hw
    rw [he] at hr
    rw [← (rep_cPerm hk).unique hrep, (tabRep_cPerm hk).perm_eq hr]
    exact hg'

@[expose] noncomputable def t1Elt : ↥(invE 1) := ⟨suzInv 1, suzInv_mem_invE⟩

@[expose] noncomputable def lambda2 : ↥(invE 1) := ⟨qVec 1, qVec_mem_invE 1⟩

@[expose] noncomputable def lambda3 : ↥(invE 1) := wElt lambda3Word (by decide)

@[expose] noncomputable def lambda4 : ↥(invE 1) := wElt lambda4Word (by decide)

@[expose] noncomputable def lambdaElt (i : ℕ) : ↥(invE 1) :=
  if i = 0 then t1Elt else if i = 1 then lambda2 else if i = 2 then lambda3 else lambda4

theorem rep_lambda4 :
    CFSG.Monster.B.Co2.Rep 1782 (cWord lambda4Word) (lambda4 : Equiv.Perm (Fin 1782)) :=
  rep_cWord (by decide)

theorem tabRep_lambda {i : ℕ} (hi : i < 4) :
    TabRep (lambdaTab i) (lambdaElt i : Equiv.Perm (Fin 1782)) := by
  refine ⟨sizes_facts.2.1 i hi, ?_⟩
  interval_cases i
  · exact rep_tTab
  · exact rep_qProds (by norm_num)
  · exact rep_cWord (by decide)
  · exact rep_cWord (by decide)

theorem orderOf_lambdaElt {i : ℕ} (hi : i < 4) : orderOf (lambdaElt i) = 2 := by
  obtain ⟨h1, h2, -⟩ := reps_facts.1 i hi
  have hr := tabRep_lambda hi
  have hsq : (lambdaElt i : Equiv.Perm (Fin 1782)) * (lambdaElt i : Equiv.Perm (Fin 1782)) = 1 :=
    (hr.comp hr).perm_eq (h1 ▸ TabRep.idTab)
  have hne : (lambdaElt i : Equiv.Perm (Fin 1782)) ≠ 1 := fun h =>
    h2 (hr.tab_eq (by rw [h]; exact TabRep.idTab))
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne

theorem conj_lambdaOrbit {i : ℕ} (hi : i < 4) :
    (∀ t ∈ (lambdaOrbit2 i).tabs.toList, ∃ c ∈ invE 1,
      TabRep t (c * (lambdaElt i : Equiv.Perm (Fin 1782)) * c⁻¹)) ∧
    (∀ c ∈ invE 1, ∃ t ∈ (lambdaOrbit2 i).tabs.toList,
      TabRep t (c * (lambdaElt i : Equiv.Perm (Fin 1782)) * c⁻¹)) ∧
    (lambdaOrbit2 i).tabs.toList.Nodup := by
  have h := conj_orbit cGens2_hA cGens2_hgens (tabRep_lambda hi) (orbit_facts hi).1
  rwa [closure_cGens2] at h

theorem card_isConj_lambda {i : ℕ} (hi : i < 4) :
    Nat.card {s : ↥(invE 1) // IsConj (lambdaElt i) s} = lambdaSizes[i]! := by
  obtain ⟨h1, h2, h3⟩ := conj_lambdaOrbit hi
  set x : Equiv.Perm (Fin 1782) := ((lambdaElt i : ↥(invE 1)) : Equiv.Perm (Fin 1782)) with hx
  set X : Set (Equiv.Perm (Fin 1782)) := {g | ∃ c ∈ invE 1, g = c * x * c⁻¹} with hX
  have hcard : Nat.card X = (lambdaOrbit2 i).tabs.toList.length := by
    refine card_set_of_tabs (fun t ht => ?_) (fun g hg => ?_) h3
    · obtain ⟨c, hc, hr⟩ := h1 t ht
      exact ⟨_, ⟨c, hc, rfl⟩, hr⟩
    · obtain ⟨c, hc, rfl⟩ := hg
      exact h2 c hc
  rw [Array.length_toList, (orbit_facts hi).2] at hcard
  rw [← hcard]
  refine Nat.card_congr
    { toFun := fun s => ⟨(s.1 : Equiv.Perm (Fin 1782)), ?_⟩
      invFun := fun g => ⟨⟨g.1, ?_⟩, ?_⟩
      left_inv := fun s => rfl
      right_inv := fun g => rfl }
  · obtain ⟨c, hc⟩ := isConj_iff.mp s.2
    exact ⟨c, c.2, by rw [← hc]; rfl⟩
  · obtain ⟨c, hc, he⟩ := g.2
    rw [he]
    exact mul_mem (mul_mem hc (lambdaElt i).2) (inv_mem hc)
  · obtain ⟨c, hc, he⟩ := g.2
    refine isConj_iff.mpr ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact he.symm

theorem card_centralizer_lambda {i : ℕ} (hi : i < 4) :
    Nat.card (centralizer ({lambdaElt i} : Set ↥(invE 1))) * lambdaSizes[i]! = 3317760 := by
  have h := CFSG.Sporadic.HN.Local.card_conj_mul_card_centralizer (lambdaElt i)
  rw [card_isConj_lambda hi, card_invE (i := 1) (by norm_num)] at h
  rw [mul_comm]
  exact h

theorem card_centralizer_lambda4 :
    Nat.card (centralizer ({lambda4} : Set ↥(invE 1))) = 512 := by
  have h := card_centralizer_lambda (i := 3) (by norm_num)
  have e : lambdaSizes[3]! = 6480 := rfl
  have e' : lambdaElt 3 = lambda4 := rfl
  rw [e, e'] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6480) (h.trans (by norm_num))

theorem card_centralizer_lambda2 :
    Nat.card (centralizer ({lambda2} : Set ↥(invE 1))) = 61440 := by
  have h := card_centralizer_lambda (i := 1) (by norm_num)
  have e : lambdaSizes[1]! = 54 := rfl
  have e' : lambdaElt 1 = lambda2 := rfl
  rw [e, e'] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 54) (h.trans (by norm_num))

@[expose] noncomputable def sylowGenPerm (j : ℕ) : Equiv.Perm (Fin 1782) :=
  if j < 6 then qGen j else if j = 6 then suzInv 1 else wPerm (sylowLiftWords.getD (j - 7) [])

@[expose] noncomputable def fusionSylow : Subgroup (Equiv.Perm (Fin 1782)) :=
  closure {g | ∃ j < 4, sylowGenPerm (s1Idx.getD j 0) = g}

theorem sylowLiftWords_lt {j : ℕ} : ∀ k ∈ sylowLiftWords.getD (j - 7) [], k < 10 := by
  have h : ∀ m : ℕ, ∀ k ∈ sylowLiftWords.getD m [], k < 10 := by
    intro m
    rcases Nat.lt_or_ge m 6 with hm | hm
    · interval_cases m <;> decide
    · rw [List.getD_eq_default _ _ (by simpa [sylowLiftWords] using hm)]
      simp
  exact h _

theorem tabRep_sylowGen {j : ℕ} (hj : j < 13) : TabRep (sylowGenTab j) (sylowGenPerm j) := by
  refine ⟨sizes_facts.2.2.1 j hj, ?_⟩
  unfold sylowGenTab sylowGenPerm
  split_ifs with h1 h2
  · exact rep_qArr h1
  · exact rep_tTab
  · exact rep_cWord sylowLiftWords_lt

theorem sylowGenPerm_mem {j : ℕ} : sylowGenPerm j ∈ invE 1 := by
  unfold sylowGenPerm
  split_ifs with h1 h2
  · exact qGen_mem_invE h1
  · exact suzInv_mem_invE
  · exact wPerm_mem sylowLiftWords_lt

theorem s1Gens_get {j : ℕ} (hj : j < 4) : s1Gens[j]! = sylowGenTab (s1Idx.getD j 0) := by
  rw [s1Gens, getElem!_ofFn' _ hj]

theorem s1Idx_lt {j : ℕ} (hj : j < 4) : s1Idx.getD j 0 < 13 := by
  interval_cases j <;> decide

theorem fusionSylow_enumerates : Enumerates fusionSylow s1Enum.tabs.toList := by
  have hsize : s1Gens.size = 4 := Array.size_ofFn
  refine enumerates_closure (fun a ha => ?_) (fun j hj => ?_) sylow_facts.1
  · obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨j, by rw [hsize]; exact hj, by
      rw [s1Gens_get hj]; exact tabRep_sylowGen (s1Idx_lt hj)⟩
  · rw [hsize] at hj
    exact ⟨_, ⟨j, hj, rfl⟩, by rw [s1Gens_get hj]; exact tabRep_sylowGen (s1Idx_lt hj)⟩

theorem card_fusionSylow : Nat.card fusionSylow = 8192 := by
  rw [fusionSylow_enumerates.card, Array.length_toList, sylow_facts.2.1]

theorem fusionSylow_le : fusionSylow ≤ invE 1 := by
  rw [fusionSylow, closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact sylowGenPerm_mem

theorem exists_conj_lambda {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invE 1) (hg2 : orderOf g = 2) :
    ∃ i < 4, ∃ c ∈ invE 1, c * g * c⁻¹ = (lambdaElt i : Equiv.Perm (Fin 1782)) := by
  have hle := fusionSylow_le
  have hcardT : Nat.card ↥(fusionSylow.subgroupOf (invE 1)) =
      2 ^ (Nat.card ↥(invE 1)).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, card_fusionSylow,
      card_invE (i := 1) (by norm_num)]
    rw [show (CFSG.Sporadic.SuzOddCore.invInnerOrders.getD 1 0) = 2 ^ 13 * 405 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  obtain ⟨c₀, hc₀, hmem⟩ :=
    exists_conj_mem_sylow (Sylow.ofCard _ hcardT) (Sylow.coe_ofCard _ _) hg hg2
  set h := c₀ * g * c₀⁻¹ with hh
  have hh1 : h ≠ 1 := by
    intro h1
    have : g = 1 := by
      calc g = c₀⁻¹ * h * c₀ := by rw [hh]; group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hg2
    omega
  have hh2 : h * h = 1 := by
    rw [hh, show c₀ * g * c₀⁻¹ * (c₀ * g * c₀⁻¹) = c₀ * (g * g) * c₀⁻¹ by group, ← pow_two,
      ← hg2, pow_orderOf_eq_one]
    group
  obtain ⟨i, hi, t, ht, hrep⟩ :=
    exists_of_coverOK fusionSylow_enumerates sylow_facts.2.2 hmem hh1 hh2
  have hi4 : i < 4 := by simpa [lambdaOrbitTabs2] using hi
  have hti : t ∈ (lambdaOrbit2 i).tabs.toList := by
    rwa [lambdaOrbitTabs2, getElem!_ofFn' _ hi4] at ht
  obtain ⟨d, hd, hdrep⟩ := (conj_lambdaOrbit hi4).1 t hti
  have heq : h = d * (lambdaElt i : Equiv.Perm (Fin 1782)) * d⁻¹ := hrep.perm_eq hdrep
  refine ⟨i, hi4, d⁻¹ * c₀, mul_mem (inv_mem hd) hc₀, ?_⟩
  calc d⁻¹ * c₀ * g * (d⁻¹ * c₀)⁻¹ = d⁻¹ * h * d := by rw [hh]; group
    _ = (lambdaElt i : Equiv.Perm (Fin 1782)) := by rw [heq]; group

theorem exists_isConj_lambda (y : ↥(invE 1)) (hy : orderOf y = 2) :
    ∃ i < 4, IsConj y (lambdaElt i) := by
  have hy2 : orderOf (y : Equiv.Perm (Fin 1782)) = 2 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨i, hi, c, hc, he⟩ := exists_conj_lambda y.2 hy2
  exact ⟨i, hi, isConj_iff.mpr ⟨⟨c, hc⟩, Subtype.ext he⟩⟩

theorem card_centralizer_coe {G : Type*} [Group G] (H : Subgroup G) (x : H) :
    Nat.card (centralizer ({x} : Set H)) = Nat.card ↥(H ⊓ centralizer ({(x : G)} : Set G)) := by
  have h : (centralizer ({x} : Set H)).map H.subtype = H ⊓ centralizer ({(x : G)} : Set G) := by
    ext g
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hgH, hg⟩
      exact ⟨⟨g, hgH⟩, Subtype.ext hg, rfl⟩
  rw [← h, card_map_of_injective H.subtype_injective]

theorem enumerates_centralizer_lambda4 :
    Enumerates (centralizer ({(lambda4 : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) ⊓
      fusionSylow) s1V0.toList ∧
    centralizer ({(lambda4 : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) ⊓
      fusionSylow = invE 1 ⊓
        centralizer ({(lambda4 : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) := by
  set x : Equiv.Perm (Fin 1782) := ((lambda4 : ↥(invE 1)) : Equiv.Perm (Fin 1782)) with hx
  have hrep : TabRep (lambdaTab 3) x := tabRep_lambda (i := 3) (by norm_num)
  have hE := fusionSylow_enumerates.filter (K := centralizer ({x} : Set (Equiv.Perm (Fin 1782))))
    (fun t => comp 1782 t (lambdaTab 3) == comp 1782 (lambdaTab 3) t) (fun t g ht => by
      rw [mem_centralizer_singleton_iff]
      exact (ht.comp hrep).beq_iff (hrep.comp ht))
  have hV : s1V0.toList = s1Enum.tabs.toList.filter
      (fun t => comp 1782 t (lambdaTab 3) == comp 1782 (lambdaTab 3) t) := by
    rw [s1V0, centTabs, Array.toList_filter]
  rw [← hV] at hE
  refine ⟨hE, ?_⟩
  have hcard1 :
      Nat.card ↥(centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ fusionSylow) = 512 := by
    rw [hE.card, Array.length_toList, v0_facts.1]
  have hcard2 : Nat.card ↥(invE 1 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1782)))) = 512 := by
    rw [← card_centralizer_coe, card_centralizer_lambda4]
  have hle : centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ fusionSylow ≤
      invE 1 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1782))) :=
    fun g hg => ⟨fusionSylow_le hg.2, hg.1⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])

theorem tabRep_pow4 {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g) :
    TabRep (pow4Tab t) (g ^ 4) := by
  have h := (ht.comp ht).comp (ht.comp ht)
  rw [show g ^ 4 = g * g * (g * g) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
  exact h

theorem pow_four_of_commute_lambda4 {v : Equiv.Perm (Fin 1782)} (hv : v ∈ invE 1)
    (hc : v * (lambda4 : Equiv.Perm (Fin 1782)) = (lambda4 : Equiv.Perm (Fin 1782)) * v) :
    v ^ 4 = 1 ∨ v ^ 4 = suzInv 1 := by
  obtain ⟨hE, heq⟩ := enumerates_centralizer_lambda4
  have hv' : v ∈ centralizer ({(lambda4 : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) ⊓
      fusionSylow := by
    rw [heq]
    exact ⟨hv, mem_centralizer_singleton_iff.mpr hc⟩
  obtain ⟨j, hj, hrep⟩ := hE.exists_pos hv'
  rw [v0_facts.1] at hj
  have htT : TabRep tTab (suzInv 1) := tabRep_lambda (i := 0) (by norm_num)
  rcases v0_facts.2.1 j hj with h | h
  · left
    exact (tabRep_pow4 hrep).perm_eq (h ▸ TabRep.idTab)
  · right
    exact (tabRep_pow4 hrep).perm_eq (h ▸ htT)

theorem exists_pow_four_lambda4 :
    ∃ v ∈ invE 1, v * (lambda4 : Equiv.Perm (Fin 1782)) = (lambda4 : Equiv.Perm (Fin 1782)) * v ∧
      v ^ 4 = suzInv 1 := by
  obtain ⟨hE, heq⟩ := enumerates_centralizer_lambda4
  obtain ⟨j, hj, h⟩ := v0_facts.2.2
  have hj' : j < s1V0.size := by rw [v0_facts.1]; exact hj
  obtain ⟨v, hv, hrep⟩ := hE.exists_elt hj'
  rw [heq] at hv
  have htT : TabRep tTab (suzInv 1) := tabRep_lambda (i := 0) (by norm_num)
  exact ⟨v, hv.1, mem_centralizer_singleton_iff.mp hv.2,
    (tabRep_pow4 hrep).perm_eq (h ▸ htT)⟩

theorem card_fixed_conj_coe (H : Subgroup (Equiv.Perm (Fin 1782))) (a c : H) :
    (Finset.univ.filter fun x : Fin 1782 =>
      ((c * a * c⁻¹ : H) : Equiv.Perm (Fin 1782)) x = x).card =
      (Finset.univ.filter fun x : Fin 1782 => (a : Equiv.Perm (Fin 1782)) x = x).card :=
  conj_fixed_card (c : Equiv.Perm (Fin 1782)) (a : Equiv.Perm (Fin 1782))

theorem card_fixed_lambda {i : ℕ} (hi : i < 4) :
    (Finset.univ.filter fun x : Fin 1782 => (lambdaElt i : Equiv.Perm (Fin 1782)) x = x).card =
      lambdaFixed[i]! := by
  rw [← fixedCount_eq (tabRep_lambda hi).2]
  exact (reps_facts.1 i hi).2.2

theorem isConj_lambda4_iff (u : ↥(invE 1)) (hu : orderOf u = 2) :
    IsConj u lambda4 ↔
      (Finset.univ.filter fun x : Fin 1782 => (u : Equiv.Perm (Fin 1782)) x = x).card = 42 := by
  have hfix : ∀ {a b : ↥(invE 1)}, IsConj a b →
      (Finset.univ.filter fun x : Fin 1782 => (a : Equiv.Perm (Fin 1782)) x = x).card =
        (Finset.univ.filter fun x : Fin 1782 => (b : Equiv.Perm (Fin 1782)) x = x).card := by
    intro a b hab
    obtain ⟨c, rfl⟩ := isConj_iff.mp hab
    exact (card_fixed_conj_coe (invE 1) a c).symm
  constructor
  · intro h
    rw [hfix h]
    have := card_fixed_lambda (i := 3) (by norm_num)
    simpa [lambdaElt, lambdaFixed] using this
  · intro h
    obtain ⟨i, hi, hc⟩ := exists_isConj_lambda u hu
    have h2 := card_fixed_lambda hi
    rw [← hfix hc, h] at h2
    interval_cases i
    · simp [lambdaFixed] at h2
    · simp [lambdaFixed] at h2
    · simp [lambdaFixed] at h2
    · simpa [lambdaElt] using hc

theorem q4_q8_facts :
    qVec 4 * qVec 4 = 1 ∧ qVec 8 * qVec 8 = 1 ∧ qVec 4 * qVec 1 = qVec 1 * qVec 4 ∧
      qVec 8 * qVec 1 = qVec 1 * qVec 8 ∧ qVec 4 * qVec 8 * qVec 4 * qVec 8 = suzInv 1 := by
  have h4 : TabRep qProds[4]! (qVec 4) := ⟨sizes_facts.2.2.2.1, rep_qProds (by norm_num)⟩
  have h8 : TabRep qProds[8]! (qVec 8) := ⟨sizes_facts.2.2.2.2, rep_qProds (by norm_num)⟩
  have h1 : TabRep (lambdaTab 1) (qVec 1) :=
    ⟨sizes_facts.2.1 1 (by norm_num), rep_qProds (by norm_num)⟩
  have ht : TabRep tTab (suzInv 1) := ⟨sizes_facts.2.1 0 (by norm_num), rep_tTab⟩
  obtain ⟨-, e1, e2, e3, e4, e5⟩ := reps_facts
  exact ⟨(h4.comp h4).perm_eq (e1 ▸ TabRep.idTab), (h8.comp h8).perm_eq (e2 ▸ TabRep.idTab),
    ((h4.comp h1).eq_iff (h1.comp h4)).mp e3, ((h8.comp h1).eq_iff (h1.comp h8)).mp e4,
    (((h4.comp h8).comp h4).comp h8).perm_eq (e5 ▸ ht)⟩

end Model

end CFSG.Sporadic.SuzRecog.LocalR
