module

public import CFSG.Sporadic.ONOddCore.InvolutionCheck
public import CFSG.Sporadic.Schreier.ONSylowCenter

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
open CFSG.ComponentClassification.PSL3Four (TabRep conj_orbit exists_of_coverOK)

theorem conj_of_odd_mul {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    {k : ℕ} (h : (x * y) ^ (2 * k + 1) = 1) : y = (x * y) ^ k * x * ((x * y) ^ k)⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxi, hyi, ← mul_assoc, hx, one_mul]
  have h2 : x * (x * y) ^ k * x⁻¹ = ((x * y) ^ k)⁻¹ := by
    rw [← conj_pow, h1, inv_pow]
  have h3 : (x * y) ^ (2 * k) = (x * y)⁻¹ := by
    rw [pow_succ] at h
    exact eq_inv_of_mul_eq_one_left h
  calc y = (x * y)⁻¹ * x := by rw [mul_inv_rev, hxi, hyi, mul_assoc, hx, mul_one]
    _ = (x * y) ^ k * (x * y) ^ k * x := by rw [← pow_add, ← two_mul, h3]
    _ = (x * y) ^ k * x * (x * (x * y) ^ k * x⁻¹) := by
        rw [hxi]
        simp only [mul_assoc]
        rw [← mul_assoc x x, hx, one_mul]
    _ = (x * y) ^ k * x * ((x * y) ^ k)⁻¹ := by rw [h2]

theorem pcomp_size (n : ℕ) (t u : Array ℕ) : (pcomp n t u).size = n := Array.size_ofFn

theorem prodArr_size (n : ℕ) (gs : Array (Array ℕ)) (w : List ℕ) : (prodArr n gs w).size = n := by
  cases w with
  | nil => exact Array.size_ofFn
  | cons j w => exact pcomp_size n _ _

theorem prep_prodArr {n : ℕ} {gs : Array (Array ℕ)} {G : ℕ → Equiv.Perm (Fin n)} :
    ∀ w : List ℕ, (∀ j ∈ w, PRep n gs[j]! (G j)) → PRep n (prodArr n gs w) (w.map G).prod
  | [], _ => by simpa [prodArr] using prep_pid (n := n)
  | j :: w, hw => by
    have ih := prep_prodArr w fun i hi => hw i (List.mem_cons_of_mem _ hi)
    simp only [prodArr, List.foldr_cons, List.map_cons, List.prod_cons] at ih ⊢
    exact prep_pcomp (hw j List.mem_cons_self) ih

theorem prep_repeat {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : PRep n t g) :
    ∀ m : ℕ, PRep n (Nat.repeat (pcomp n t) m (pid n)) (g ^ m)
  | 0 => by
    show PRep n (pid n) (g ^ 0)
    rw [pow_zero]
    exact prep_pid
  | m + 1 => by
    rw [Nat.repeat, pow_succ']
    exact prep_pcomp ht (prep_repeat ht m)

theorem repWords_lt {i : ℕ} (hi : i < 7) : ∀ j ∈ repWords[i]!, j < 6 := by
  interval_cases i <;> decide

@[expose] def repT
    (i : ℕ) : onT := (repWords[i]!.map tGen).prod

theorem repT_val (i : ℕ) :
    ((repT i : onT) : Equiv.Perm (Fin N)) =
      (repWords[i]!.map fun j => (tGen j : Equiv.Perm (Fin N))).prod := by
  rw [repT, ← onT.subtype_apply, map_list_prod, List.map_map]
  rfl

theorem prep_tA
    {j : ℕ} (hj : j < 6) :
    PRep N (wordArrs Data.TWords)[j]! (tGen j : Equiv.Perm (Fin N)) := by
  have hjl : j < onTgens.length := by rw [onTgens_length]; exact hj
  rw [tGen_val hjl]
  exact prep_onTgens j hjl

theorem prep_repT
    {i : ℕ} (hi : i < 7) :
    PRep N (prodArr nPts (wordArrs Data.TWords) repWords[i]!) (repT i : Equiv.Perm (Fin N)) := by
  rw [repT_val]
  exact prep_prodArr _ fun j hj => prep_tA (repWords_lt hi j hj)

theorem fusion_facts :
    (∀ j < 6, peq 32 (rTab (wordArrs Data.TWords)[j]!) Data.T32Chain.generators[j]! = true) ∧
      (∀ j < 4, pisInv nPts (wordArrs Data.MWords ++ #[cArr])[j]!
        (pinvs nPts (wordArrs Data.MWords ++ #[cArr]))[j]! = true) ∧
      peq nPts (prodArr nPts (wordArrs Data.TWords) repWords[3]!) zArr = true ∧
      (∀ i < 7, peq nPts (pcomp nPts (prodArr nPts (wordArrs Data.TWords) repWords[i]!)
        (prodArr nPts (wordArrs Data.TWords) repWords[i]!)) (pid nPts) = true) ∧
      (∀ w ∈ vWords, plettersOK 4 w = true) ∧
      (∀ w ∈ vWords, pisInv nPts (pword nPts (wordArrs Data.MWords ++ #[cArr])
        (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) w)
        (pinvCand nPts (pword nPts (wordArrs Data.MWords ++ #[cArr])
          (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) w)) = true) ∧
      ∀ i k m, (i, k, m) ∈ oddTests → peq nPts (Nat.repeat (pcomp nPts (oddArr
        (wordArrs Data.TWords) (wordArrs Data.MWords ++ #[cArr])
          (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) zArr i k)) m (pid nPts)) (pid nPts) =
            true := by
  have h := inv_fusion_cert
  simp only [fusionCheck, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨fun j hj => allBelowN_spec h1 hj, fun j hj => allBelowN_spec h2 hj, h3,
    fun i hi => (Bool.and_eq_true _ _ ▸ allBelowN_spec h4 hi).1, h5, h6,
    fun i k m hmem => h7 (i, k, m) hmem⟩

theorem rhoT_tGen
    {j : ℕ} (hj : j < 6) :
    rhoT (tGen j) = permOfArr 32 Data.T32Chain.generators[j]! := by
  have h6 : (evalList Data.TWords).length = 6 := onTgens_length
  have hjs : j < ((wordArrs Data.TWords).map rTab).size := by
    rw [Array.size_map, wordArrs_size, h6]; exact hj
  have h1 := prep_rhoT_gen j hjs
  have hjs' : j < (wordArrs Data.TWords).size := by simpa using hjs
  rw [getElem!_map' _ _ hjs'] at h1
  have h2 : PRep 32 Data.T32Chain.generators[j]! (rhoT (tGen j)) := by
    intro x
    have := (peq_iff (n := 32) (t := rTab (wordArrs Data.TWords)[j]!)
      (u := Data.T32Chain.generators[j]!) h1 (prep_t32_gens j
        (by rw [t32_gens_size]; exact hj))).1 (fusion_facts.1 j hj)
    rw [this]
    exact prep_t32_gens j (by rw [t32_gens_size]; exact hj) x
  exact h2.unique (prep_t32_gens j (by rw [t32_gens_size]; exact hj))

theorem repTabs32_get {i : ℕ} (hi : i < 7) :
    repTabs32[i]! = prodArr 32 Data.T32Chain.generators repWords[i]! := by
  have hi' : i < repWords.size := by simpa [repWords] using hi
  rw [repTabs32, getElem!_map' _ _ hi']

theorem tabRep_repT
    {i : ℕ} (hi : i < 7) : TabRep repTabs32[i]! (rhoT (repT i)) := by
  rw [repTabs32_get hi]
  refine ⟨prodArr_size _ _ _, fun x => ?_⟩
  have h := prep_prodArr (n := 32) (gs := Data.T32Chain.generators)
    (G := fun j => permOfArr 32 Data.T32Chain.generators[j]!) repWords[i]! fun j hj =>
      prep_t32_gens j (by rw [t32_gens_size]; exact repWords_lt hi j hj)
  have e : rhoT (repT i) = (repWords[i]!.map fun j => permOfArr 32
      Data.T32Chain.generators[j]!).prod := by
    rw [repT, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    exact rhoT_tGen (repWords_lt hi j hj)
  rw [e]
  exact h x

theorem t32_gens_tabRep
    {j : ℕ} (hj : j < Data.T32Chain.generators.size) :
    TabRep Data.T32Chain.generators[j]! (permOfArr 32 Data.T32Chain.generators[j]!) :=
  tabRep_of_prep (t32_gen_size hj) (prep_t32_gens j hj)

theorem exists_conj_rep
    {t : onT} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ c : onT, ∃ i < 7, t = c * repT i * c⁻¹ := by
  obtain ⟨hinv, hsize, horb, hcover⟩ := inv_classes_cert
  have hy : rhoT t ∈ onT32Chain.originalSubgroup := rhoT_range ▸ ⟨t, rfl⟩
  have h1 : rhoT t ≠ 1 := fun h => ht1 (rhoT_injective (h.trans (map_one _).symm))
  have h2 : rhoT t * rhoT t = 1 := by rw [← map_mul, ht2, map_one]
  obtain ⟨i, hi, tab, htab, hrep⟩ := exists_of_coverOK t32_enumerates hcover hy h1 h2
  have hi7 : i < 7 := by simpa [hsize] using hi
  have hi' : i < repOrbits32.size := by rw [hsize]; exact hi7
  have htab' : tab ∈ repOrbits32[i]!.tabs.toList := by
    rwa [getElem!_map' _ _ hi'] at htab
  have hA : ∀ a ∈ (fun j => permOfArr 32 Data.T32Chain.generators[j]!) '' {j | j < 6},
      ∃ j < Data.T32Chain.generators.size, TabRep Data.T32Chain.generators[j]! a := by
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j < Data.T32Chain.generators.size := by rw [t32_gens_size]; exact hj
    exact ⟨j, hj', t32_gens_tabRep hj'⟩
  have hgens : ∀ j < Data.T32Chain.generators.size, ∃ a ∈ (fun j => permOfArr 32
      Data.T32Chain.generators[j]!) '' {j | j < 6}, TabRep Data.T32Chain.generators[j]! a :=
    fun j hj => ⟨_, ⟨j, by rw [t32_gens_size] at hj; exact hj, rfl⟩, t32_gens_tabRep hj⟩
  obtain ⟨c, hc, hrep'⟩ := (conj_orbit hA hgens (tabRep_repT hi7)
    (allBelowN_spec horb hi7)).1 tab htab'
  have e : rhoT t = c * rhoT (repT i) * c⁻¹ := hrep.perm_eq hrep'
  rw [← onT32_sub, ← rhoT_range] at hc
  obtain ⟨c', rfl⟩ := hc
  refine ⟨c', i, hi7, rhoT_injective ?_⟩
  rw [e, map_mul, map_mul, map_inv]

@[expose] def bPerm
    (h : ℕ) : Equiv.Perm (Fin N) := (onMgens ++ [onc]).getD h 1

theorem prep_bA
    {h : ℕ} (hh : h < 4) : PRep N (wordArrs Data.MWords ++ #[cArr])[h]! (bPerm h) := by
  have hl : h < (onMgens ++ [onc]).length := by simp [onMgens_length]; omega
  have := prep_append (la := onMgens) (lb := [onc]) (wordArrs_size Data.MWords) prep_onMgens
    (fun j hj => by
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      have e : (#[cArr] : Array (Array ℕ))[0]! = cArr := by simp
      rw [e, List.getElem_singleton]
      exact prep_onc) h hl
  rw [bPerm, List.getD_eq_getElem _ _ hl]
  exact this

theorem prep_bI
    {h : ℕ} (hh : h < 4) :
    PRep N (pinvs nPts (wordArrs Data.MWords ++ #[cArr]))[h]! (bPerm h)⁻¹ :=
  prep_inv_of_pisInv (prep_bA hh) (fusion_facts.2.1 h hh)

theorem bPerm_mem_P
    (h : ℕ) : bPerm h ∈ Pv := by
  rw [bPerm]
  by_cases hl : h < (onMgens ++ [onc]).length
  · rw [List.getD_eq_getElem _ _ hl]
    rcases List.mem_append.1 (List.getElem_mem hl) with hm | hm
    · exact onM_le (Subgroup.subset_closure hm)
    · rw [List.mem_singleton] at hm
      rw [hm]
      exact onc_mem
  · rw [List.getD_eq_default _ _ (not_lt.1 hl)]
    exact one_mem _

@[expose] def vPerm
    (k : ℕ) : Equiv.Perm (Fin N) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 4 => bPerm h) (ptoLetters 4 vWords[k]!)

theorem vWords_mem {k : ℕ} (hk : k < 3) : vWords[k]! ∈ vWords := by
  rw [getElem!_pos vWords k (by simpa [vWords] using hk)]
  exact Array.getElem_mem _

theorem prep_v
    {k : ℕ} (hk : k < 3) :
    PRep N (pword nPts (wordArrs Data.MWords ++ #[cArr])
      (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) vWords[k]!) (vPerm k) :=
  prep_pword (gs := bPerm) (fun _ hh => prep_bA hh) (fun _ hh => prep_bI hh) _
    (fusion_facts.2.2.2.2.1 _ (vWords_mem hk))

theorem vPerm_mem_P
    (k : ℕ) : vPerm k ∈ Pv := by
  apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact bPerm_mem_P h

theorem prep_oddArr
    {i k : ℕ} (hi : i < 7) (hk : k < 3) :
    PRep N (oddArr (wordArrs Data.TWords) (wordArrs Data.MWords ++ #[cArr])
      (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) zArr i k)
      ((repT i : Equiv.Perm (Fin N)) * (vPerm k * onz * (vPerm k)⁻¹)) := by
  have hv := prep_v hk
  have hvi := prep_inv_of_pisInv hv (fusion_facts.2.2.2.2.2.1 _ (vWords_mem hk))
  have := prep_pcomp (prep_repT hi) (prep_conj hv hvi prep_z)
  exact this

theorem repT_sq
    {i : ℕ} (hi : i < 7) :
    (repT i : Equiv.Perm (Fin N)) * (repT i : Equiv.Perm (Fin N)) = 1 :=
  eq_of_peq (prep_pcomp (prep_repT hi) (prep_repT hi)) prep_pid (fusion_facts.2.2.2.1 i hi)

theorem odd_test
    {i k m : ℕ} (hmem : (i, k, m) ∈ oddTests) :
    ((repT i : Equiv.Perm (Fin N)) * (vPerm k * onz * (vPerm k)⁻¹)) ^ m = 1 := by
  have hi : i < 7 := by simp [oddTests] at hmem; omega
  have hk : k < 3 := by simp [oddTests] at hmem; omega
  exact eq_of_peq (prep_repeat (prep_oddArr hi hk) m) prep_pid
    (fusion_facts.2.2.2.2.2.2 i k m hmem)

theorem repT_conj_z
    {i : ℕ} (hi : i < 7) :
    ∃ g ∈ Pv, (repT i : Equiv.Perm (Fin N)) = g * onz * g⁻¹ := by
  have hfuse : ∀ k m, (i, k, 2 * m + 1) ∈ oddTests →
      ∃ g ∈ Pv, (repT i : Equiv.Perm (Fin N)) = g * onz * g⁻¹ := by
    intro k m hmem
    have hk : k < 3 := by simp [oddTests] at hmem; omega
    set y := vPerm k * onz * (vPerm k)⁻¹ with hy
    have hy2 : y * y = 1 := by
      rw [hy, show vPerm k * onz * (vPerm k)⁻¹ * (vPerm k * onz * (vPerm k)⁻¹) =
        vPerm k * (onz * onz) * (vPerm k)⁻¹ by group, onz_sq, mul_one, mul_inv_cancel]
    have hcj := conj_of_odd_mul (repT_sq hi) hy2 (odd_test hmem)
    set r := (repT i : Equiv.Perm (Fin N)) * y
    have hrP : r ∈ Pv := mul_mem (onT_le (repT i).2)
      (mul_mem (mul_mem (vPerm_mem_P k) (evalS_mem _)) (inv_mem (vPerm_mem_P k)))
    refine ⟨(r ^ m)⁻¹ * vPerm k, mul_mem (inv_mem (pow_mem hrP m)) (vPerm_mem_P k), ?_⟩
    have e : (repT i : Equiv.Perm (Fin N)) = (r ^ m)⁻¹ * y * r ^ m := by
      rw [hcj]
      group
    rw [e, hy]
    group
  interval_cases i
  · exact hfuse 0 7 (by decide)
  · exact hfuse 1 7 (by decide)
  · exact hfuse 2 9 (by decide)
  · refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact eq_of_peq (prep_repT (by norm_num)) prep_z fusion_facts.2.2.1
  · exact hfuse 2 9 (by decide)
  · exact hfuse 0 9 (by decide)
  · exact hfuse 2 7 (by decide)

theorem exists_conj_mem_T
    {x : Pv} (hx : orderOf x = 2) :
    ∃ g : Pv, (g : Equiv.Perm (Fin N))⁻¹ * x * g ∈ onT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Pv onTSylow S
  have hxS : x ∈ (S : Subgroup Pv) := hS (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  refine ⟨g, ?_⟩
  rw [onTSylow_coe, Subgroup.mem_subgroupOf] at hxS
  have e : (((MulAut.conj g)⁻¹ • x : Pv) : Equiv.Perm (Fin N)) =
      (g : Equiv.Perm (Fin N))⁻¹ * x * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    rfl
  rwa [e] at hxS

theorem cti_on_all_involutions_conjugate :
    ∀ x ∈ Pv, orderOf x = 2 → ∃ g ∈ Pv, x = g * onz * g⁻¹ := by
  intro x hxP hx
  set xP : Pv := ⟨x, hxP⟩
  have hxP2 : orderOf xP = 2 := by rw [← Subgroup.orderOf_coe]; exact hx
  obtain ⟨g, hg⟩ := exists_conj_mem_T hxP2
  set t : onT := ⟨_, hg⟩
  have hx2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have ht2 : t * t = 1 := by
    apply Subtype.ext
    show ((g : Equiv.Perm (Fin N))⁻¹ * x * g) * ((g : Equiv.Perm (Fin N))⁻¹ * x * g) = 1
    rw [show ((g : Equiv.Perm (Fin N))⁻¹ * x * g) * ((g : Equiv.Perm (Fin N))⁻¹ * x * g) =
      (g : Equiv.Perm (Fin N))⁻¹ * (x * x) * g by group, hx2, mul_one, inv_mul_cancel]
  have ht1 : t ≠ 1 := by
    intro h
    apply hx1
    have h' := congrArg Subtype.val h
    change (g : Equiv.Perm (Fin N))⁻¹ * x * g = 1 at h'
    calc x = (g : Equiv.Perm (Fin N)) * ((g : Equiv.Perm (Fin N))⁻¹ * x * g) *
          (g : Equiv.Perm (Fin N))⁻¹ := by group
      _ = 1 := by rw [h']; group
  obtain ⟨c, i, hi, hct⟩ := exists_conj_rep ht1 ht2
  obtain ⟨h, hhP, hR⟩ := repT_conj_z hi
  have hcP : (c : Equiv.Perm (Fin N)) ∈ Pv := onT_le c.2
  set gp : Equiv.Perm (Fin N) := (g : Equiv.Perm (Fin N))
  set cp : Equiv.Perm (Fin N) := (c : Equiv.Perm (Fin N))
  refine ⟨gp * cp * h, mul_mem (mul_mem g.2 hcP) hhP, ?_⟩
  have e1 : gp⁻¹ * x * gp = cp * (repT i : Equiv.Perm (Fin N)) * cp⁻¹ := by
    have := congrArg Subtype.val hct
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  calc x = gp * (gp⁻¹ * x * gp) * gp⁻¹ := by group
    _ = gp * (cp * (h * onz * h⁻¹) * cp⁻¹) * gp⁻¹ := by rw [e1, hR]
    _ = gp * cp * h * onz * (gp * cp * h)⁻¹ := by group

end CFSG.Sporadic.ONOddCore
