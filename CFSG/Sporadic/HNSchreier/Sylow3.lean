module

public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.Sporadic.HNSchreier.SylowCheck
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.He.Native (getElem!_ofFn)
open Equiv

theorem eq_of_base
    {g h : JH} (hb : ∀ k : Fin 22, g • baseX k = h • baseX k) : g = h := by
  have h1 : permJ (g⁻¹ * h) = 1 := by
    refine eq_one_of_fix_base (permJ_mem _) fun k => ?_
    rw [map_mul, Perm.mul_apply, permJ_apply, permJ_apply, ← hb k, inv_smul_smul]
  have := permJ_injective (h1.trans (map_one permJ).symm)
  rw [inv_mul_eq_one] at this
  exact this

theorem baseList_get (k : Fin 22) : Data.baseList[k.val]! = (baseX k).val := by
  show Data.baseList[k.val]! = baseIndex k.val
  rw [baseIndex, List.getD_eq_getElem _ _ (by rw [base_facts.1]; exact k.isLt),
    getElem!_pos _ _ (by rw [base_facts.1]; exact k.isLt)]

theorem base_of_map_eq {f₁ f₂ : ℕ → ℕ} (h : Data.baseList.map f₁ = Data.baseList.map f₂)
    (k : Fin 22) : f₁ (baseX k).val = f₂ (baseX k).val := by
  have hk : k.val < Data.baseList.length := by rw [base_facts.1]; exact k.isLt
  have := congrArg (fun l => l[k.val]!) h
  rw [getElem!_pos _ _ (by simpa using hk), getElem!_pos _ _ (by simpa using hk),
    List.getElem_map, List.getElem_map] at this
  rw [← baseList_get, getElem!_pos Data.baseList k.val hk]
  exact this

@[irreducible] def pGArrs : Array (Array ℕ) :=
  (FAData.pLift.map fun lw => lw.foldl (fun acc l => pcomp hnsData.n acc c3Arrs[l - 1]!)
    (pid hnsData.n)).push (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) FAData.pKernel)

theorem pGArrs_eq : pGArrs =
    (FAData.pLift.map fun lw => lw.foldl (fun acc l => pcomp hnsData.n acc c3Arrs[l - 1]!)
      (pid hnsData.n)).push
      (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) FAData.pKernel) := by
  unfold pGArrs; rfl

@[irreducible] def bimgArr : Array (List ℕ) :=
  Array.ofFn (n := 729) fun i => Data.baseList.map fun b => pev pGArrs FAData.pParents 729 i.val b

theorem bimgArr_eq : bimgArr = Array.ofFn (n := 729) fun i =>
    Data.baseList.map fun b => pev pGArrs FAData.pParents 729 i.val b := by
  unfold bimgArr; rfl

@[irreducible] def markArr : Array Bool :=
  Array.ofFn (n := 729) fun i => SylowData.order3.contains i.val

theorem markArr_eq : markArr = Array.ofFn (n := 729) fun i => SylowData.order3.contains i.val := by
  unfold markArr; rfl

@[irreducible] def labArr : Array ℕ := classLabels FAData.wClass

theorem labArr_eq : labArr = classLabels FAData.wClass := by unfold labArr; rfl

abbrev a0Arr : Array ℕ := natTab (hnsData.orbit ()).alpha

abbrev a1Arr : Array ℕ := natTab (hnsData.orbit ()).beta

theorem sylow_parts :
    ((pinvs hnsData.n #[a0Arr, a1Arr]).size = 2 ∧
      pisInv hnsData.n a0Arr (pinvs hnsData.n #[a0Arr, a1Arr])[0]! = true ∧
      pisInv hnsData.n a1Arr (pinvs hnsData.n #[a0Arr, a1Arr])[1]! = true) ∧
    (plettersOK 17 FAData.pKernel = true ∧ FAData.pLift.size = 5 ∧
      FAData.pLift.all (fun lw => lw.all fun l => decide (1 ≤ l) && decide (l ≤ 7)) = true) ∧
    (pGArrs.size = 6 ∧ ∀ j < 6, pisInv hnsData.n pGArrs[j]! (pinvs hnsData.n pGArrs)[j]! = true) ∧
    (FAData.pParents.size = 729 ∧ FAData.pParents[0]! = (0, 0) ∧
      ∀ i < 729, i ≠ 0 → (FAData.pParents[i]!).1 < i ∧ (FAData.pParents[i]!).2 < 6) ∧
    (∀ j < 6, ∀ i < 729, (FAData.pLeft[j]!)[i]! < 729 ∧
      bimgArr[(FAData.pLeft[j]!)[i]!]! = Data.baseList.map fun b =>
        (pGArrs[j]!)[pev pGArrs FAData.pParents 729 i b]!) ∧
    (∀ i < 729, ∀ k < 729, i < k → bimgArr[i]! ≠ bimgArr[k]!) ∧
    (SylowData.order3.length = 512 ∧ ∀ i < 729, markArr[i]! = (i != 0 && Data.baseList.all fun b =>
      pev pGArrs FAData.pParents 729 i (pev pGArrs FAData.pParents 729 i
        (pev pGArrs FAData.pParents 729 i b)) == b)) ∧
    (∀ j < 6, ∀ i < 729, (SylowData.conj[j]!)[i]! < 729 ∧
      bimgArr[(SylowData.conj[j]!)[i]!]! = Data.baseList.map fun b =>
        (pGArrs[j]!)[pev pGArrs FAData.pParents 729 i ((pinvs hnsData.n pGArrs)[j]!)[b]!]!) ∧
    (∀ c < 48, ∀ i ∈ FAData.wClass[c]!, i < 729 ∧ markArr[i]! = true ∧ labArr[i]! = c ∧
      ∀ j < 6, labArr[(SylowData.conj[j]!)[i]!]! = c) ∧
    (∀ i < 729, markArr[i]! = true → labArr[i]! < 48 ∧ i ∈ FAData.wClass[labArr[i]!]!) ∧
    (∀ i < 729, markArr[i]! = true → treeReach SylowData.tree 729 i = true ∧
      ((SylowData.tree[i]!).2 = 0 → i = FAData.wRep[labArr[i]!]!) ∧
      ((SylowData.tree[i]!).2 ≠ 0 → (SylowData.tree[i]!).1 < 729 ∧ (SylowData.tree[i]!).2 ≤ 6 ∧
        markArr[(SylowData.tree[i]!).1]! = true ∧ labArr[(SylowData.tree[i]!).1]! = labArr[i]! ∧
        (SylowData.conj[(SylowData.tree[i]!).2 - 1]!)[(SylowData.tree[i]!).1]! = i)) ∧
    (∀ c < 48, FAData.wRep[c]! < 729 ∧ labArr[FAData.wRep[c]!]! = c ∧
      (FAData.wRoot[c]!).all (fun l => l == 1 || l == 2) = true ∧
      plettersOK 17 FAData.wHWord[c]! = true ∧ 1 ≤ FAData.wCycles[c]! ∧ FAData.wCycles[c]! ≤ 4 ∧
      Data.baseList.all (fun b => seedWordInvIdx (pinvs hnsData.n #[a0Arr, a1Arr])[0]!
        (pinvs hnsData.n #[a0Arr, a1Arr])[1]! FAData.wRoot[c]!
        (pev pGArrs FAData.pParents 729 FAData.wRep[c]!
          (seedWordIdx a0Arr a1Arr FAData.wRoot[c]! b)) ==
          (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) FAData.wHWord[c]!)[b]!) = true ∧
      peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) FAData.wHWord[c]!)
        (natArr FAData.wNat[c]!) = true ∧
      pisInv 12 (natArr SylowData.rho[c]!) (pinvCand 12 (natArr SylowData.rho[c]!)) = true ∧
      peq 12 (pcomp 12 (pcomp 12 (natArr SylowData.rho[c]!) (tripleArr FAData.wCycles[c]!))
        (pinvCand 12 (natArr SylowData.rho[c]!))) (natArr FAData.wNat[c]!) = true) := by
  have h := sylow_cert
  unfold sylowChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← hRegs_eq, ← hStrongArr_eq, ← g3Arr_eq, ← c3Arrs_eq, ← pGArrs_eq, ← bimgArr_eq,
    ← markArr_eq, ← labArr_eq, ← natStrongArr_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩,
    h26⟩, h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩, h35⟩, h36⟩, h37⟩ := h
  refine ⟨⟨h3, h4, h5⟩, ⟨h10, h11, h12⟩, ⟨h13, fun j hj => allBelowN_spec h14 hj⟩,
    ⟨h15, h16, fun i hi hi0 => ?_⟩, fun j hj i hi => ?_, fun i hi k hk hik => ?_,
    ⟨h21, fun i hi => ?_⟩, fun j hj i hi => ?_, fun c hc i hic => ?_, fun i hi hm => ?_,
    fun i hi hm => ?_, fun c hc => ?_⟩
  · have := allBelowN_spec h17 hi
    simp only [Bool.or_eq_true, beq_iff_eq, hi0, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at this
    exact this
  · have := allBelowN_spec h19 hj
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    have := allBelowN_spec this.2 hi
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  · have := allBelowN_spec (allBelowN_spec h20 hi) hk
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
    rcases this with h | h
    · omega
    · exact h
  · have := allBelowN_spec h22 hi
    simp only [beq_iff_eq] at this
    exact this
  · have := allBelowN_spec h24 hj
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    have := allBelowN_spec this.2 hi
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  · have := List.all_eq_true.1 (allBelowN_spec h27 hc) i hic
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, fun j hj => by
      have := allBelowN_spec this.2 hj
      simpa only [beq_iff_eq] using this⟩
  · have := allBelowN_spec h28 hi
    rw [hm, Bool.not_true, Bool.false_or] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at this
    exact this
  · have := allBelowN_spec h30 hi
    rw [hm, Bool.not_true, Bool.false_or] at this
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1, fun h0 => ?_, fun h0 => ?_⟩
    · have := this.2
      rw [ite_eq_left h0] at this
      simpa using this
    · have := this.2
      rw [ite_eq_right h0] at this
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
  · have := allBelowN_spec h37 hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := this
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

theorem prep_lift_foldl :
    ∀ (lw : List ℕ), (∀ l ∈ lw, 1 ≤ l ∧ l ≤ 7) →
    ∀ {acc : Array ℕ} {g : Perm X}, PRep hnsData.n acc g →
      PRep hnsData.n (lw.foldl (fun acc l => pcomp hnsData.n acc c3Arrs[l - 1]!) acc)
        (g * (lw.map fun l => permJ (c3J (l - 1))).prod)
  | [], _, _, _, h => by simpa using h
  | l :: lw, hlw, acc, g, h => by
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    obtain ⟨hl1, hl7⟩ := hlw l (List.mem_cons_self ..)
    exact prep_lift_foldl lw (fun l' hl' => hlw l' (List.mem_cons_of_mem _ hl'))
      (prep_pcomp h (c3J_rep (by omega)))

theorem pLift_letters
    {j : ℕ} (hj : j < 5) : ∀ l ∈ FAData.pLift[j]!, 1 ≤ l ∧ l ≤ 7 := by
  obtain ⟨-, ⟨-, hsz, hall⟩, -⟩ := sylow_parts
  intro l hl
  rw [Array.all_eq_true] at hall
  have := hall j (by rw [hsz]; exact hj)
  rw [← getElem!_pos FAData.pLift j (by rw [hsz]; exact hj)] at this
  have := List.all_eq_true.1 this l hl
  simpa using this

theorem pGArr_rep
    {j : ℕ} (hj : j < 6) : PRep hnsData.n pGArrs[j]! (permJ (pGenJ j)) := by
  obtain ⟨-, ⟨hk, hsz, -⟩, -⟩ := sylow_parts
  have hmsz : (FAData.pLift.map fun lw => lw.foldl (fun acc l => pcomp hnsData.n acc c3Arrs[l - 1]!)
      (pid hnsData.n)).size = 5 := by simp [hsz]
  rcases Nat.lt_or_ge j 5 with h5 | h5
  · rw [pGArrs_eq, getElem!_pos _ j (by simp [hsz]; omega), Array.getElem_push_lt (by omega),
      ← getElem!_pos _ j (by omega), getElem!_map_lt _ _ (by rw [hsz]; exact h5), pGenJ,
      ite_eq_left h5, map_list_prod, List.map_map]
    have := prep_lift_foldl _ (pLift_letters h5) (prep_pid (n := hnsData.n))
    rw [one_mul] at this
    exact this
  · have hj5 : j = 5 := by omega
    subst hj5
    have e := getElem!_push_size (FAData.pLift.map fun lw =>
      lw.foldl (fun acc l => pcomp hnsData.n acc c3Arrs[l - 1]!) (pid hnsData.n))
      (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) FAData.pKernel)
    rw [hmsz] at e
    rw [pGArrs_eq, e, pGenJ, ite_eq_right (by norm_num)]
    exact prep_hWord hk

theorem pGArrInv_rep
    {j : ℕ} (hj : j < 6) :
    PRep hnsData.n (pinvs hnsData.n pGArrs)[j]! (permJ (pGenJ j))⁻¹ :=
  prep_inv_of_pisInv (pGArr_rep hj) (sylow_parts.2.2.1.2 j hj)

@[expose] def eAux : ℕ → ℕ → JH
  | 0, _ => 1
  | f + 1, i => if i = 0 then 1 else pGenJ (FAData.pParents[i]!).2 * eAux f (FAData.pParents[i]!).1

abbrev eJ (i : ℕ) : JH := eAux 729 i

theorem par_gen_lt
    {i : ℕ} (hi0 : i ≠ 0) : (FAData.pParents[i]!).2 < 6 := by
  rcases Nat.lt_or_ge i 729 with hi | hi
  · exact (sylow_parts.2.2.2.1.2.2 i hi hi0).2
  · rw [getElem!_neg _ i (by rw [sylow_parts.2.2.2.1.1]; omega)]
    decide

theorem prep_apply {t : Array ℕ} {g : Perm X} (h : PRep hnsData.n t g) (y : X) :
    t[y.val]! = (g y).val := h y

theorem pev_spec :
    ∀ (f i : ℕ) (y : X),
    pev pGArrs FAData.pParents f i y.val = ((eAux f i • y : X) : ℕ)
  | 0, i, y => by rw [pev, eAux, one_smul]
  | f + 1, i, y => by
    rw [pev, eAux]
    by_cases hi0 : i = 0
    · rw [ite_eq_left hi0, ite_eq_left hi0, one_smul]
    · rw [ite_eq_right hi0, ite_eq_right hi0, mul_smul, pev_spec f _ y]
      have := prep_apply (pGArr_rep (par_gen_lt hi0)) (eAux f (FAData.pParents[i]!).1 • y)
      rw [this, permJ_apply]

theorem eAux_stable : ∀ i < 729, ∀ f, i < f → eAux f i = eJ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [show eJ i = eAux (728 + 1) i from rfl, eAux, eAux]
    by_cases hi0 : i = 0
    · rw [ite_eq_left hi0, ite_eq_left hi0]
    · rw [ite_eq_right hi0, ite_eq_right hi0]
      have hp := (sylow_parts.2.2.2.1.2.2 i hi hi0).1
      rw [ih _ hp (by omega) f' (by omega), ih _ hp (by omega) 728 (by omega)]

theorem eJ_zero : eJ 0 = 1 := by
  show eAux (728 + 1) 0 = 1
  rw [eAux, ite_eq_left rfl]

theorem eJ_succ {i : ℕ} (hi : i < 729) (hi0 : i ≠ 0) :
    eJ i = pGenJ (FAData.pParents[i]!).2 * eJ (FAData.pParents[i]!).1 := by
  rw [show eJ i = eAux (728 + 1) i from rfl, eAux, ite_eq_right hi0,
    eAux_stable _ (by have := (sylow_parts.2.2.2.1.2.2 i hi hi0).1; omega) 728
      (by have := (sylow_parts.2.2.2.1.2.2 i hi hi0).1; omega)]

theorem bimgArr_get {i : ℕ} (hi : i < 729) :
    bimgArr[i]! = Data.baseList.map fun b => pev pGArrs FAData.pParents 729 i b := by
  rw [bimgArr_eq, getElem!_ofFn _ hi]

theorem pev_base
    (i : ℕ) (k : Fin 22) :
    pev pGArrs FAData.pParents 729 i (baseX k).val = ((eJ i • baseX k : X) : ℕ) :=
  pev_spec 729 i (baseX k)

theorem base_mem {b : ℕ} (hb : b ∈ Data.baseList) : ∃ k : Fin 22, b = (baseX k).val := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
  have hk22 : k < 22 := by rw [base_facts.1] at hk; exact hk
  refine ⟨⟨k, hk22⟩, ?_⟩
  rw [← baseList_get, getElem!_pos Data.baseList k hk]

theorem eJ_inj
    {i k : ℕ} (hi : i < 729) (hk : k < 729) (h : eJ i = eJ k) : i = k := by
  by_contra hne
  have hb : bimgArr[i]! = bimgArr[k]! := by
    rw [bimgArr_get hi, bimgArr_get hk]
    apply List.map_congr_left
    intro b hb
    obtain ⟨m, rfl⟩ := base_mem hb
    rw [pev_base, pev_base, h]
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact sylow_parts.2.2.2.2.2.1 i hi k hk h' hb
  · exact sylow_parts.2.2.2.2.2.1 k hk i hi h' hb.symm

theorem pev_mul_base
    {j : ℕ} (hj : j < 6) (i : ℕ) (k : Fin 22) :
    (pGArrs[j]!)[pev pGArrs FAData.pParents 729 i (baseX k).val]! =
      (((pGenJ j * eJ i) • baseX k : X) : ℕ) := by
  rw [pev_base, prep_apply (pGArr_rep hj), permJ_apply, mul_smul]

theorem left_action
    {j i : ℕ} (hj : j < 6) (hi : i < 729) :
    pGenJ j * eJ i = eJ (FAData.pLeft[j]!)[i]! := by
  obtain ⟨hlt, hb⟩ := sylow_parts.2.2.2.2.1 j hj i hi
  apply eq_of_base
  intro k
  apply Fin.ext
  have := base_of_map_eq (hb.symm.trans (bimgArr_get hlt)) k
  rw [pev_mul_base hj, pev_base] at this
  exact this

theorem pGen_mem_PJ {j : ℕ} (hj : j < 6) : pGenJ j ∈ PJ :=
  Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem eJ_mem_PJ {i : ℕ} (hi : i < 729) : eJ i ∈ PJ := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi0 : i = 0
    · subst hi0; rw [eJ_zero]; exact one_mem _
    · have hp := sylow_parts.2.2.2.1.2.2 i hi hi0
      rw [eJ_succ hi hi0]
      exact mul_mem (pGen_mem_PJ hp.2) (ih _ hp.1 (by omega))

theorem mul_eJ_mem
    {x : JH} (hx : x ∈ PJ) : ∀ i < 729, ∃ k < 729, x * eJ i = eJ k := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨j, hj⟩, rfl⟩ := hx
    intro i hi
    exact ⟨_, (sylow_parts.2.2.2.2.1 j hj i hi).1, left_action hj hi⟩
  | one => exact fun i hi => ⟨i, hi, one_mul _⟩
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨k, hk, hyk⟩ := hy i hi
    obtain ⟨m, hm, hxm⟩ := hx k hk
    exact ⟨m, hm, by rw [mul_assoc, hyk, hxm]⟩
  | inv x _ hx =>
    choose f hf hfe using hx
    let F : Fin 729 → Fin 729 := fun i => ⟨f i.val i.isLt, hf _ _⟩
    have hinj : Function.Injective F := by
      intro a b hab
      have e1 := hfe a.val a.isLt
      have e2 := hfe b.val b.isLt
      have : eJ a.val = eJ b.val := by
        apply mul_left_cancel (a := x)
        rw [e1, e2]
        exact congrArg (fun t : Fin 729 => eJ t.val) hab
      exact Fin.ext (eJ_inj a.isLt b.isLt this)
    have hsurj := Finite.injective_iff_surjective.1 hinj
    intro i hi
    obtain ⟨a, ha⟩ := hsurj ⟨i, hi⟩
    refine ⟨a.val, a.isLt, ?_⟩
    have e := hfe a.val a.isLt
    have hfa : f a.val a.isLt = i := congrArg Fin.val ha
    rw [hfa] at e
    rw [← e, inv_mul_cancel_left]

theorem PJ_eq_range :
    (PJ : Set JH) = Set.range fun i : Fin 729 => eJ i.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, hxk⟩ := mul_eJ_mem hx 0 (by norm_num)
    rw [eJ_zero, mul_one] at hxk
    exact ⟨⟨k, hk⟩, hxk.symm⟩
  · rintro ⟨i, rfl⟩
    exact eJ_mem_PJ i.isLt

theorem eJ_injective :
    Function.Injective fun i : Fin 729 => eJ i.val :=
  fun a b h => Fin.ext (eJ_inj a.isLt b.isLt h)

theorem card_PJ :
    Nat.card PJ = 729 := by
  rw [← SetLike.coe_sort_coe, PJ_eq_range, Nat.card_range_of_injective eJ_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem PJ_isPGroup :
    IsPGroup 3 PJ := IsPGroup.of_card (n := 6) (by rw [card_PJ]; norm_num)

theorem PJ_index :
    PJ.index = 374528000000 := by
  have h := Subgroup.card_mul_index PJ
  rw [card_PJ, card_JH] at h
  omega

theorem not_three_dvd_index :
    ¬ 3 ∣ PJ.index := by rw [PJ_index]; norm_num

@[expose] def PSylow :
    Sylow 3 JH := PJ_isPGroup.toSylow not_three_dvd_index

theorem PSylow_coe :
    (PSylow : Subgroup JH) = PJ := IsPGroup.toSylow_coe _ _

theorem baseX_mem (k : Fin 22) : (baseX k).val ∈ Data.baseList := by
  have hk : k.val < Data.baseList.length := by rw [base_facts.1]; exact k.isLt
  rw [← baseList_get, getElem!_pos Data.baseList k.val hk]
  exact List.getElem_mem hk

theorem pev_val
    (i : ℕ) (y : X) :
    pev pGArrs FAData.pParents 729 i y.val = ((eJ i • y : X) : ℕ) :=
  pev_spec 729 i y

theorem eJ_ne_one
    {i : ℕ} (hi : i < 729) (hi0 : i ≠ 0) : eJ i ≠ 1 := by
  intro h
  rw [← eJ_zero] at h
  exact hi0 (eJ_inj hi (by norm_num) h)

theorem pev_cube
    (i : ℕ) (k : Fin 22) :
    pev pGArrs FAData.pParents 729 i (pev pGArrs FAData.pParents 729 i
      (pev pGArrs FAData.pParents 729 i (baseX k).val)) = ((eJ i ^ 3 • baseX k : X) : ℕ) := by
  rw [pev_val i (baseX k), pev_val i (eJ i • baseX k), pev_val i (eJ i • eJ i • baseX k),
    pow_three, mul_smul, mul_smul]

theorem mark_iff
    {i : ℕ} (hi : i < 729) : markArr[i]! = true ↔ orderOf (eJ i) = 3 := by
  obtain ⟨-, -, -, -, -, -, ⟨-, hm⟩, -⟩ := sylow_parts
  rw [hm i hi]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hi0, hb⟩
    refine orderOf_eq_prime ?_ (eJ_ne_one hi hi0)
    apply eq_of_base
    intro k
    apply Fin.ext
    rw [← pev_cube, hb _ (baseX_mem k), one_smul]
  · intro h3
    have hp : eJ i ^ 3 = 1 := h3 ▸ pow_orderOf_eq_one (eJ i)
    refine ⟨fun hi0 => ?_, fun b hb => ?_⟩
    · subst hi0
      rw [eJ_zero, orderOf_one] at h3
      exact absurd h3 (by norm_num)
    · obtain ⟨k, rfl⟩ := base_mem hb
      rw [pev_cube, hp, one_smul]

theorem markArr_get {i : ℕ} (hi : i < 729) : markArr[i]! = SylowData.order3.contains i := by
  rw [markArr_eq, getElem!_ofFn _ hi]

theorem order3_chain : SylowData.order3.IsChain (· < ·) := by decide +kernel

theorem order3_lt : ∀ i ∈ SylowData.order3, i < 729 := by decide +kernel

theorem order3_nodup : SylowData.order3.Nodup := order3_chain.pairwise.imp Nat.ne_of_lt

theorem order3_length :
    SylowData.order3.length = 512 := sylow_parts.2.2.2.2.2.2.1.1

theorem order3_set_eq :
    {y : JH | y ∈ PJ ∧ orderOf y = 3} =
    Set.range fun j : Fin 512 => eJ SylowData.order3[j.val]! := by
  ext y
  constructor
  · rintro ⟨hy, h3⟩
    have hy' : y ∈ (PJ : Set JH) := hy
    rw [PJ_eq_range] at hy'
    obtain ⟨⟨i, hi⟩, rfl⟩ := hy'
    have hm := (mark_iff hi).2 h3
    rw [markArr_get hi, List.contains_iff_mem] at hm
    obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hm
    refine ⟨⟨j, by rw [← order3_length]; exact hj⟩, ?_⟩
    show eJ SylowData.order3[j]! = eJ i
    rw [getElem!_pos SylowData.order3 j hj, e]
  · rintro ⟨⟨j, hj⟩, rfl⟩
    have hj' : j < SylowData.order3.length := by rw [order3_length]; exact hj
    have hmem : SylowData.order3[j]! ∈ SylowData.order3 := by
      rw [getElem!_pos _ j hj']; exact List.getElem_mem hj'
    have hlt := order3_lt _ hmem
    refine ⟨eJ_mem_PJ hlt, (mark_iff hlt).1 ?_⟩
    rw [markArr_get hlt, List.contains_iff_mem]
    exact hmem

theorem order3_inj :
    Function.Injective fun j : Fin 512 => eJ SylowData.order3[j.val]! := by
  intro a b hab
  have ha : a.val < SylowData.order3.length := by rw [order3_length]; exact a.isLt
  have hb : b.val < SylowData.order3.length := by rw [order3_length]; exact b.isLt
  have e : eJ SylowData.order3[a.val]! = eJ SylowData.order3[b.val]! := hab
  rw [getElem!_pos SylowData.order3 a.val ha, getElem!_pos SylowData.order3 b.val hb] at e
  have := eJ_inj (order3_lt _ (List.getElem_mem ha)) (order3_lt _ (List.getElem_mem hb)) e
  exact Fin.ext ((order3_nodup.getElem_inj_iff).1 this)

theorem ncard_order3 :
    {y : JH | y ∈ PJ ∧ orderOf y = 3}.ncard = 512 := by
  rw [order3_set_eq, Set.ncard_range_of_injective order3_inj, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem orderOf_conj_JH (g x : JH) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem conj_table
    {j i : ℕ} (hj : j < 6) (hi : i < 729) :
    pGenJ j * eJ i * (pGenJ j)⁻¹ = eJ (SylowData.conj[j]!)[i]! := by
  obtain ⟨-, -, -, -, -, -, -, hc, -⟩ := sylow_parts
  obtain ⟨hlt, hb⟩ := hc j hj i hi
  apply eq_of_base
  intro k
  apply Fin.ext
  have := base_of_map_eq (hb.symm.trans (bimgArr_get hlt)) k
  rw [prep_apply (pGArrInv_rep hj) (baseX k), ← map_inv permJ (pGenJ j), permJ_apply,
    pev_val i ((pGenJ j)⁻¹ • baseX k), prep_apply (pGArr_rep hj), permJ_apply, pev_base] at this
  rw [mul_smul, mul_smul]
  exact this

theorem conj_mark
    {j i : ℕ} (hj : j < 6) (hi : i < 729) (hm : markArr[i]! = true) :
    (SylowData.conj[j]!)[i]! < 729 ∧ markArr[(SylowData.conj[j]!)[i]!]! = true ∧
      labArr[(SylowData.conj[j]!)[i]!]! = labArr[i]! := by
  obtain ⟨-, -, -, -, -, -, -, hc, hcl, hcov, -⟩ := sylow_parts
  have hlt := (hc j hj i hi).1
  refine ⟨hlt, ?_, ?_⟩
  · rw [mark_iff hlt, ← conj_table hj hi, orderOf_conj_JH]
    exact (mark_iff hi).1 hm
  · obtain ⟨hl48, hmem⟩ := hcov i hi hm
    exact (hcl _ hl48 i hmem).2.2.2 j hj

def LabConj (p : JH) : Prop := ∀ i < 729, markArr[i]! = true →
  ∃ i' < 729, markArr[i']! = true ∧ labArr[i']! = labArr[i]! ∧ p * eJ i * p⁻¹ = eJ i'

theorem labConj_one : LabConj 1 := fun i hi hm => ⟨i, hi, hm, rfl, by group⟩

theorem labConj_mul {p q : JH} (hp : LabConj p) (hq : LabConj q) : LabConj (p * q) := by
  intro i hi hm
  obtain ⟨i', hi', hm', hl', he'⟩ := hq i hi hm
  obtain ⟨i'', hi'', hm'', hl'', he''⟩ := hp i' hi' hm'
  refine ⟨i'', hi'', hm'', hl''.trans hl', ?_⟩
  rw [← he'', ← he']
  group

theorem labConj_gen
    {j : ℕ} (hj : j < 6) : LabConj (pGenJ j) := fun _ hi hm =>
  ⟨_, (conj_mark hj hi hm).1, (conj_mark hj hi hm).2.1, (conj_mark hj hi hm).2.2,
    conj_table hj hi⟩

theorem labConj_pow {p : JH} (hp : LabConj p) : ∀ n : ℕ, LabConj (p ^ n)
  | 0 => by rw [pow_zero]; exact labConj_one
  | n + 1 => by rw [pow_succ]; exact labConj_mul (labConj_pow hp n) hp

theorem labConj_inv {p : JH} (hp : LabConj p) : LabConj p⁻¹ := by
  have e : p ^ (orderOf p - 1) = p⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos p), pow_orderOf_eq_one]
  rw [← e]
  exact labConj_pow hp _

theorem labConj_of_mem
    {p : JH} (hp : p ∈ PJ) : LabConj p := by
  induction hp using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨j, hj⟩, rfl⟩ := hx
    exact labConj_gen hj
  | one => exact labConj_one
  | mul x y _ _ hx hy => exact labConj_mul hx hy
  | inv x _ hx => exact labConj_inv hx

theorem tree_conj :
    ∀ f i, i < 729 → markArr[i]! = true → treeReach SylowData.tree f i = true →
    ∃ p ∈ PJ, p * eJ FAData.wRep[labArr[i]!]! * p⁻¹ = eJ i
  | 0, i, _, _, h => by simp [treeReach] at h
  | f + 1, i, hi, hm, h => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, ht, -⟩ := sylow_parts
    obtain ⟨-, h0, hne⟩ := ht i hi hm
    by_cases hz : (SylowData.tree[i]!).2 = 0
    · refine ⟨1, one_mem _, ?_⟩
      rw [← h0 hz]
      group
    · obtain ⟨hq, hj6, hmq, hlq, hci⟩ := hne hz
      have hr : treeReach SylowData.tree f (SylowData.tree[i]!).1 = true := by
        simp only [treeReach, Bool.or_eq_true, beq_iff_eq, hz, false_or] at h
        exact h
      obtain ⟨p, hp, he⟩ := tree_conj f _ hq hmq hr
      have e1 := conj_table (j := (SylowData.tree[i]!).2 - 1) (by omega) hq
      rw [hci] at e1
      refine ⟨pGenJ ((SylowData.tree[i]!).2 - 1) * p, mul_mem (pGen_mem_PJ (by omega)) hp, ?_⟩
      rw [← hlq, ← e1, ← he]
      group

@[expose] def classSet (c : ℕ) : Set JH := {y | ∃ i ∈ FAData.wClass[c]!, eJ i = y}

theorem seedWordIdx_val
    (w : List ℕ) (hw : ∀ l ∈ w, l = 1 ∨ l = 2) (y : X) :
    seedWordIdx a0Arr a1Arr w y.val = ((seedWordJ w • y : X) : ℕ) := by
  induction w with
  | nil => rw [seedWordIdx, List.foldr_nil, seedWordJ, List.map_nil, List.prod_nil, one_smul]
  | cons l w ih =>
    have ih' := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    rw [seedWordJ_cons, smul_mul_val, seedWordIdx_cons]
    rcases hw l (List.mem_cons_self ..) with rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_left rfl, smul_val_aJ, ih']
    · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num), smul_val_bJ, ih']

theorem ai_rep :
    PRep hnsData.n (pinvs hnsData.n #[a0Arr, a1Arr])[0]! a0⁻¹ ∧
    PRep hnsData.n (pinvs hnsData.n #[a0Arr, a1Arr])[1]! a1⁻¹ := by
  obtain ⟨⟨-, h0, h1⟩, -⟩ := sylow_parts
  exact ⟨prep_inv_of_pisInv prep_a0 h0, prep_inv_of_pisInv prep_a1 h1⟩

theorem seedWordInvIdx_cons (a0i a1i : Array ℕ) (l : ℕ) (w : List ℕ) (y : ℕ) :
    seedWordInvIdx a0i a1i (l :: w) y =
      seedWordInvIdx a0i a1i w ((if l = 1 then a0i else a1i)[y]!) := by
  unfold seedWordInvIdx
  exact List.foldl_cons ..

theorem seedWordInvIdx_val
    (w : List ℕ) (hw : ∀ l ∈ w, l = 1 ∨ l = 2) (y : X) :
    seedWordInvIdx (pinvs hnsData.n #[a0Arr, a1Arr])[0]! (pinvs hnsData.n #[a0Arr, a1Arr])[1]! w
      y.val = (((seedWordJ w)⁻¹ • y : X) : ℕ) := by
  induction w generalizing y with
  | nil =>
    rw [seedWordInvIdx, List.foldl_nil, seedWordJ, List.map_nil, List.prod_nil, inv_one,
      one_smul]
  | cons l w ih =>
    have ih' := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    rw [seedWordInvIdx_cons, seedWordJ_cons, mul_inv_rev, mul_smul]
    rcases hw l (List.mem_cons_self ..) with rfl | rfl
    · have e : ((pinvs hnsData.n #[a0Arr, a1Arr])[0]!)[y.val]! = ((aJ⁻¹ • y : X) : ℕ) := by
        rw [prep_apply ai_rep.1 y, ← permJ_apply, map_inv, permJ_aJ]
      rw [ite_eq_left rfl, ite_eq_left rfl, e, ih']
    · have e : ((pinvs hnsData.n #[a0Arr, a1Arr])[1]!)[y.val]! = ((bJ⁻¹ • y : X) : ℕ) := by
        rw [prep_apply ai_rep.2 y, ← permJ_apply, map_inv, permJ_bJ]
      rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num), e, ih']

theorem rep_conj
    {c : ℕ} (hc : c < 48) :
    (seedWordJ FAData.wRoot[c]!)⁻¹ * eJ FAData.wRep[c]! * seedWordJ FAData.wRoot[c]! =
      hWordJ FAData.wHWord[c]! := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hw⟩ := sylow_parts
  obtain ⟨-, -, hroot, hlet, -, -, hbase, -⟩ := hw c hc
  have hroot' : ∀ l ∈ FAData.wRoot[c]!, l = 1 ∨ l = 2 := by
    intro l hl
    have := List.all_eq_true.1 hroot l hl
    simpa using this
  apply eq_of_base
  intro k
  apply Fin.ext
  have := List.all_eq_true.1 hbase _ (baseX_mem k)
  rw [beq_iff_eq, seedWordIdx_val _ hroot' (baseX k),
    pev_val FAData.wRep[c]! (seedWordJ FAData.wRoot[c]! • baseX k),
    seedWordInvIdx_val _ hroot' (eJ FAData.wRep[c]! • seedWordJ FAData.wRoot[c]! • baseX k),
    prep_apply (prep_hWord hlet) (baseX k), permJ_apply] at this
  rw [mul_smul, mul_smul]
  exact this

theorem prep_of_peq_left {n : ℕ} {t u : Array ℕ} {g : Perm (Fin n)} (h : peq n t u = true)
    (ht : PRep n t g) : PRep n u g := fun x => by
  have := allBelowN_spec h x.2
  rw [beq_iff_eq] at this
  rw [← this, ht x]

theorem natWord_witness
    {hw : List ℤ} {k : ℕ} {ρa νa : List ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hlet : plettersOK 17 hw = true)
    (h1 : peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) hw) (natArr νa) = true)
    (h2 : pisInv 12 (natArr ρa) (pinvCand 12 (natArr ρa)) = true)
    (h3 : peq 12 (pcomp 12 (pcomp 12 (natArr ρa) (tripleArr k)) (pinvCand 12 (natArr ρa)))
      (natArr νa) = true) :
    natWord hw = permOfArr 12 (natArr ρa) * tripleNat k * (permOfArr 12 (natArr ρa))⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hρ := prep_permOfArr h2
  have hA := prep_of_peq_left h1 (prep_natWord hlet)
  have hB := prep_of_peq_left h3
    (prep_pcomp (prep_pcomp hρ.1 (prep_tripleArr ⟨m, by omega⟩)) hρ.2)
  exact PRep.unique hA hB

theorem tripleNat_two : tripleNat 2 = tri 0 1 2 * tri 3 4 5 := by decide

theorem tripleNat_four : tripleNat 4 = tri 0 1 2 * tri 3 4 5 * tri 6 7 8 * tri 9 10 11 := by
  decide

theorem cycleType_tri2 : (tri 0 1 2 * tri 3 4 5).cycleType = {3, 3} := by
  rw [Equiv.Perm.Disjoint.cycleType_mul (by show ∀ x, _ ∨ _; unfold tri; decide),
    isThreeCycle_tri (by decide) (by decide) (by decide),
    isThreeCycle_tri (by decide) (by decide) (by decide)]
  rfl

theorem cycleType_tri4 :
    (tri 0 1 2 * tri 3 4 5 * tri 6 7 8 * tri 9 10 11).cycleType = {3, 3, 3, 3} := by
  rw [Equiv.Perm.Disjoint.cycleType_mul (by show ∀ x, _ ∨ _; unfold tri; decide),
    Equiv.Perm.Disjoint.cycleType_mul (by show ∀ x, _ ∨ _; unfold tri; decide),
    Equiv.Perm.Disjoint.cycleType_mul (by show ∀ x, _ ∨ _; unfold tri; decide),
    isThreeCycle_tri (by decide) (by decide) (by decide),
    isThreeCycle_tri (by decide) (by decide) (by decide),
    isThreeCycle_tri (by decide) (by decide) (by decide),
    isThreeCycle_tri (by decide) (by decide) (by decide)]
  rfl

theorem cycleType_tripleNat {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (tripleNat k).cycleType = Multiset.replicate k 3 := by
  interval_cases k
  · rw [tripleNat_one, cycleType_tri012]; rfl
  · rw [tripleNat_two, cycleType_tri2]; rfl
  · rw [tripleNat_three, cycleType_tri3]; rfl
  · rw [tripleNat_four, cycleType_tri4]; rfl

theorem orderOf_tripleNat {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) : orderOf (tripleNat k) = 3 := by
  apply orderOf_eq_prime
  · interval_cases k <;> decide
  · interval_cases k <;> decide

theorem exists_odd_comm {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    ∃ τ : Perm (Fin 12), Equiv.Perm.sign τ = -1 ∧ τ * tripleNat k = tripleNat k * τ := by
  interval_cases k
  · exact ⟨swap 9 10, Equiv.Perm.sign_swap (by decide), by decide⟩
  · exact ⟨swap 9 10, Equiv.Perm.sign_swap (by decide), by decide⟩
  · exact ⟨swap 9 10, Equiv.Perm.sign_swap (by decide), by decide⟩
  · refine ⟨swap 0 3 * swap 1 4 * swap 2 5, ?_, by decide⟩
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide

theorem exists_even_conj_tripleNat {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (ρ : Perm (Fin 12)) :
    ∃ σ : alternatingGroup (Fin 12),
      (σ : Perm (Fin 12)) * tripleNat k * (σ : Perm (Fin 12))⁻¹ = ρ * tripleNat k * ρ⁻¹ := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h
  · exact ⟨⟨ρ, h⟩, rfl⟩
  · obtain ⟨τ, hτ, hc⟩ := exists_odd_comm hk1 hk4
    refine ⟨⟨ρ * τ, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, h, hτ]; decide⟩, ?_⟩
    show ρ * τ * tripleNat k * (ρ * τ)⁻¹ = ρ * tripleNat k * ρ⁻¹
    rw [mul_inv_rev, mul_assoc ρ τ, hc]
    group

theorem iotaA_mem
    (σ : alternatingGroup (Fin 12)) : iotaA σ ∈ HJ := (thetaJ.symm σ).2

theorem witness_isConj
    {c : ℕ} (hc : c < 48) :
    1 ≤ FAData.wCycles[c]! ∧ FAData.wCycles[c]! ≤ 4 ∧
      (thetaJ (hWordH FAData.wHWord[c]!) : Perm (Fin 12)).cycleType =
        Multiset.replicate FAData.wCycles[c]! 3 ∧
      ∃ g ∈ HJ, g * sJ (FAData.wCycles[c]! - 1) * g⁻¹ = hWordJ FAData.wHWord[c]! := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hw⟩ := sylow_parts
  obtain ⟨-, -, -, hlet, hk1, hk4, -, h1, h2, h3⟩ := hw c hc
  have hθ := (thetaJ_hWord FAData.wHWord[c]!).trans (natWord_witness hk1 hk4 hlet h1 h2 h3)
  refine ⟨hk1, hk4, by rw [hθ, Equiv.Perm.cycleType_conj, cycleType_tripleNat hk1 hk4], ?_⟩
  obtain ⟨σ, hσ⟩ := exists_even_conj_tripleNat hk1 hk4 (permOfArr 12 (natArr SylowData.rho[c]!))
  have hs := thetaJ_sJ (k := FAData.wCycles[c]! - 1) (by omega)
  rw [Nat.sub_add_cancel hk1] at hs
  have he : thetaJ (hWordH FAData.wHWord[c]!) =
      σ * thetaJ ⟨sJ (FAData.wCycles[c]! - 1), sJ_mem _⟩ * σ⁻¹ := by
    apply Subtype.ext
    rw [hθ, ← hσ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs]
  refine ⟨iotaA σ, iotaA_mem σ, ?_⟩
  have := congrArg iotaA he
  rw [map_mul, map_mul, map_inv, iotaA_theta, iotaA_theta] at this
  exact this.symm

theorem orderOf_sJ
    {m : ℕ} (hm : m < 4) : orderOf (sJ m) = 3 := by
  have h1 : orderOf (iotaA (thetaJ ⟨sJ m, sJ_mem m⟩)) = orderOf (thetaJ ⟨sJ m, sJ_mem m⟩) :=
    orderOf_injective iotaA iotaA_injective _
  have h3 : orderOf (thetaJ ⟨sJ m, sJ_mem m⟩ : Perm (Fin 12)) =
      orderOf (thetaJ ⟨sJ m, sJ_mem m⟩) := Subgroup.orderOf_coe _
  rw [iotaA_theta] at h1
  rw [thetaJ_sJ hm] at h3
  rw [h1, ← h3]
  exact orderOf_tripleNat (by omega) (by omega)

theorem isConj_rep
    {c : ℕ} (hc : c < 48) :
    IsConj (sJ (FAData.wCycles[c]! - 1)) (eJ FAData.wRep[c]!) := by
  obtain ⟨-, -, -, g, -, hg⟩ := witness_isConj hc
  have h1 : IsConj (sJ (FAData.wCycles[c]! - 1)) (hWordJ FAData.wHWord[c]!) :=
    isConj_iff.2 ⟨g, hg⟩
  have h2 : IsConj (hWordJ FAData.wHWord[c]!) (eJ FAData.wRep[c]!) :=
    isConj_iff.2 ⟨seedWordJ FAData.wRoot[c]!, by rw [← rep_conj hc]; group⟩
  exact h1.trans h2

theorem rep_mark
    {c : ℕ} (hc : c < 48) : markArr[FAData.wRep[c]!]! = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hw⟩ := sylow_parts
  obtain ⟨hr, -⟩ := hw c hc
  obtain ⟨hk1, hk4, -⟩ := witness_isConj hc
  rw [mark_iff hr]
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_rep hc)
  rw [← hg, orderOf_conj_JH]
  exact orderOf_sJ (by omega)

theorem classSet_eq
    {c : ℕ} (hc : c < 48) :
    classSet c = {y | ∃ p ∈ PJ, p * eJ FAData.wRep[c]! * p⁻¹ = y} := by
  obtain ⟨-, -, -, -, -, -, -, -, hcl, hcov, ht, hw⟩ := sylow_parts
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hi7, hm, hl, -⟩ := hcl c hc i hi
    obtain ⟨hreach, -⟩ := ht i hi7 hm
    obtain ⟨p, hp, he⟩ := tree_conj 729 i hi7 hm hreach
    rw [hl] at he
    exact ⟨p, hp, he⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hr, hlr, -⟩ := hw c hc
    obtain ⟨i', hi', hm', hl', he'⟩ := labConj_of_mem hp _ hr (rep_mark hc)
    obtain ⟨-, hmem⟩ := hcov i' hi' hm'
    rw [hl', hlr] at hmem
    exact ⟨i', hmem, he'.symm⟩

theorem classSet_disjoint
    {c c' : ℕ} (hc : c < 48) (hc' : c' < 48) (hne : c ≠ c') :
    Disjoint (classSet c) (classSet c') := by
  obtain ⟨-, -, -, -, -, -, -, -, hcl, -⟩ := sylow_parts
  rw [Set.disjoint_left]
  rintro y ⟨i, hi, rfl⟩ ⟨i', hi', he⟩
  obtain ⟨hi7, -, hl, -⟩ := hcl c hc i hi
  obtain ⟨hi7', -, hl', -⟩ := hcl c' hc' i' hi'
  have := eJ_inj hi7' hi7 he
  subst this
  exact hne (hl.symm.trans hl')

theorem mem_order3_iff
    (y : JH) : (y ∈ PJ ∧ orderOf y = 3) ↔ ∃ c < 48, y ∈ classSet c := by
  obtain ⟨-, -, -, -, -, -, -, -, hcl, hcov, -⟩ := sylow_parts
  constructor
  · rintro ⟨hy, h3⟩
    have hy' : y ∈ (PJ : Set JH) := hy
    rw [PJ_eq_range] at hy'
    obtain ⟨⟨i, hi⟩, rfl⟩ := hy'
    obtain ⟨hl, hmem⟩ := hcov i hi ((mark_iff hi).2 h3)
    exact ⟨_, hl, i, hmem, rfl⟩
  · rintro ⟨c, hc, i, hi, rfl⟩
    obtain ⟨hi7, hm, -⟩ := hcl c hc i hi
    exact ⟨eJ_mem_PJ hi7, (mark_iff hi7).1 hm⟩

theorem exists_conj_mem_PJ
    {x : JH} (hx : orderOf x = 3) : ∃ g : JH, g * x * g⁻¹ ∈ PJ := by
  have hp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq JH Q PSylow
  refine ⟨g, ?_⟩
  rw [← PSylow_coe, ← hg, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers x))

theorem order_three_isConj
    {x : JH} (hx : orderOf x = 3) : ∃ k < 4, IsConj (sJ k) x := by
  obtain ⟨g, hg⟩ := exists_conj_mem_PJ hx
  have h3 : orderOf (g * x * g⁻¹) = 3 := by rw [orderOf_conj_JH, hx]
  obtain ⟨c, hc, i, hi, he⟩ := (mem_order3_iff _).1 ⟨hg, h3⟩
  have hrep : IsConj (eJ FAData.wRep[c]!) (eJ i) := by
    have hmem : eJ i ∈ classSet c := ⟨i, hi, rfl⟩
    rw [classSet_eq hc] at hmem
    obtain ⟨p, -, hp⟩ := hmem
    exact isConj_iff.2 ⟨p, hp⟩
  obtain ⟨hk1, hk4, -⟩ := witness_isConj hc
  refine ⟨FAData.wCycles[c]! - 1, by omega, ((isConj_rep hc).trans hrep).trans ?_⟩
  rw [he]
  exact isConj_iff.2 ⟨g⁻¹, by group⟩


theorem ctuc_hn_Sylow_three_complete_element_coverage :
    (∃ S : Sylow 3 JH, (S : Subgroup JH) = PJ) ∧ Nat.card PJ = 729 ∧
    (PJ : Set JH) = Set.range (fun i : Fin 729 => eJ i.val) ∧
    Function.Injective (fun i : Fin 729 => eJ i.val) ∧
    {y : JH | y ∈ PJ ∧ orderOf y = 3}.ncard = 512 ∧
    (∀ c < 48, classSet c = {y | ∃ p ∈ PJ, p * eJ FAData.wRep[c]! * p⁻¹ = y}) ∧
    (∀ c < 48, ∀ c' < 48, c ≠ c' → Disjoint (classSet c) (classSet c')) ∧
    (∀ y : JH, y ∈ PJ ∧ orderOf y = 3 ↔ ∃ c < 48, y ∈ classSet c) ∧
    (∀ c < 48, 1 ≤ FAData.wCycles[c]! ∧ FAData.wCycles[c]! ≤ 4 ∧
      (seedWordJ FAData.wRoot[c]!)⁻¹ * eJ FAData.wRep[c]! * seedWordJ FAData.wRoot[c]! =
        hWordJ FAData.wHWord[c]! ∧ hWordJ FAData.wHWord[c]! ∈ HJ ∧
      (thetaJ (hWordH FAData.wHWord[c]!) : Perm (Fin 12)).cycleType =
        Multiset.replicate FAData.wCycles[c]! 3 ∧
      ∃ g ∈ HJ, g * sJ (FAData.wCycles[c]! - 1) * g⁻¹ = hWordJ FAData.wHWord[c]!) ∧
    ∀ x : JH, orderOf x = 3 → ∃ k < 4, IsConj (sJ k) x := by
  refine ⟨⟨PSylow, PSylow_coe⟩, card_PJ, PJ_eq_range, eJ_injective, ncard_order3,
    fun c hc => classSet_eq hc, fun c hc c' hc' hne => classSet_disjoint hc hc' hne,
    mem_order3_iff, fun c hc => ?_, fun x hx => order_three_isConj hx⟩
  obtain ⟨hk1, hk4, hcyc, hconj⟩ := witness_isConj hc
  exact ⟨hk1, hk4, rep_conj hc, hWordJ_mem _, hcyc, hconj⟩

end CFSG.Sporadic.HNSchreier
