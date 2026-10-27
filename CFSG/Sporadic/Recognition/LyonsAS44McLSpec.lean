module

public import CFSG.Sporadic.Recognition.LyonsAS44McLInputs
public import CFSG.Sporadic.Recognition.LyonsAS44Count
public import CFSG.Sporadic.Recognition.McLASThreeLocal

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.LyonsSims

section Counting

variable {M : Type*} [Group M] [Finite M]

theorem card_le_mul_card_centralizer (N : Subgroup M) (x : M) (T : Finset M)
    (hT : ∀ n ∈ N, n * x * n⁻¹ ∈ T) :
    Nat.card N ≤ T.card * Nat.card ↥(N ⊓ centralizer ({x} : Set M)) := by
  classical
  set C : Subgroup M := N ⊓ centralizer ({x} : Set M) with hC
  have hCN : C ≤ N := inf_le_left
  set C' : Subgroup ↥N := C.subgroupOf N with hC'
  have hmemC : ∀ n : ↥N, n ∈ C' ↔ (n : M) * x = x * (n : M) := by
    intro n
    rw [hC', mem_subgroupOf, hC, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨n.2, h⟩⟩
  let F : ↥N ⧸ C' → M :=
    Quotient.lift (fun n : ↥N => (n : M) * x * (n : M)⁻¹) (by
      intro n n' h
      have h' : n⁻¹ * n' ∈ C' := QuotientGroup.leftRel_apply.1 h
      have hc := (hmemC _).1 h'
      have hc' : (n : M)⁻¹ * (n' : M) * x = x * ((n : M)⁻¹ * (n' : M)) := by simpa using hc
      calc (n : M) * x * (n : M)⁻¹
          = (n : M) * (x * ((n : M)⁻¹ * (n' : M))) * (n' : M)⁻¹ := by group
        _ = (n : M) * ((n : M)⁻¹ * (n' : M) * x) * (n' : M)⁻¹ := by rw [hc']
        _ = (n' : M) * x * (n' : M)⁻¹ := by group)
  have hFinj : Function.Injective F := by
    intro q q' h
    induction q using QuotientGroup.induction_on with
    | H n =>
      induction q' using QuotientGroup.induction_on with
      | H n' =>
        apply QuotientGroup.eq.2
        rw [hmemC]
        change (n : M) * x * (n : M)⁻¹ = (n' : M) * x * (n' : M)⁻¹ at h
        calc (n : M)⁻¹ * (n' : M) * x
            = (n : M)⁻¹ * ((n' : M) * x * (n' : M)⁻¹) * (n' : M) := by group
          _ = (n : M)⁻¹ * ((n : M) * x * (n : M)⁻¹) * (n' : M) := by rw [h]
          _ = x * ((n : M)⁻¹ * (n' : M)) := by group
          _ = _ := by simp
  have hindex : Nat.card (↥N ⧸ C') ≤ T.card := by
    let g : (↥N ⧸ C') → T := fun q => ⟨F q, by
      induction q using QuotientGroup.induction_on with
      | H n => exact hT n n.2⟩
    have hg : Function.Injective g := fun q q' h => hFinj (congrArg Subtype.val h)
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C'
  rw [hC', Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] at h1
  rw [h1]
  exact Nat.mul_le_mul_right _ hindex

theorem ten_mul_card_inf_normalizer_le (H A : Subgroup M) (c : Fin 10 → M) (hc : ∀ i, c i ∈ H)
    (hne : ∀ i j, i ≠ j → (c j)⁻¹ * c i ∉ normalizer (A : Set M)) :
    10 * Nat.card ↥(H ⊓ normalizer (A : Set M)) ≤ Nat.card H := by
  classical
  set L : Subgroup M := H ⊓ normalizer (A : Set M) with hL
  have hLH : L ≤ H := inf_le_left
  set L' : Subgroup ↥H := L.subgroupOf H with hL'
  let g : Fin 10 → ↥H ⧸ L' := fun i => QuotientGroup.mk ⟨c i, hc i⟩
  have hg : Function.Injective g := by
    intro i j h
    by_contra hij
    have h' : (⟨c i, hc i⟩ : ↥H)⁻¹ * ⟨c j, hc j⟩ ∈ L' := QuotientGroup.eq.1 h
    rw [hL', mem_subgroupOf, hL, mem_inf] at h'
    exact hne j i (Ne.symm hij) h'.2
  have h10 : 10 ≤ Nat.card (↥H ⧸ L') := by
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup L'
  rw [hL', Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv] at h1
  rw [h1]
  exact Nat.mul_le_mul_right _ h10

end Counting

noncomputable def Yp (i : Fin 10) : Equiv.Perm (Fin 275) := tp 275 nrmY[i.val]!

theorem nrmY_getElem_mem (i : Fin 10) : nrmY[i.val]! ∈ nrmY :=
  getElem!_mem_array (by simp [nrmY])

theorem nrmY_facts
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (h : nrmYCheck = true) :
    Yp 0 = three₁ ∧ (∀ i, Rep 275 nrmY[i.val]! (Yp i) ∧ Rep 275 (invT 275 nrmY[i.val]!) (Yp i)⁻¹) ∧
      (∀ i, Yp i ∈ subA3) ∧ (∀ i, Yp i ∈ conjClass mclP three₁) ∧
      (∀ i j, (Yp i = Yp j ∨ Yp i = (Yp j)⁻¹) → i = j) ∧
      (∀ z ∈ subA3, z ∈ conjClass mclP three₁ → ∃ i, z = Yp i ∨ z = (Yp i)⁻¹) := by
  obtain ⟨-, -, hA, hx, -, hclass⟩ := threeEnumCheck_spec hrows he
  simp only [nrmYCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hsize, h0⟩, hall⟩, hdist⟩, hcover⟩ := h
  have hrepY : ∀ i : Fin 10, Rep 275 nrmY[i.val]! (Yp i) ∧
      Rep 275 (invT 275 nrmY[i.val]!) (Yp i)⁻¹ ∧ memT 275 enumA3.1 nrmY[i.val]! = true ∧
      memT 275 enumClass.1 nrmY[i.val]! = true := by
    intro i
    have h1 := Array.all_eq_true'.1 hall nrmY[i.val]! (nrmY_getElem_mem i)
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨⟨hp, hi⟩, hmA⟩, hmC⟩ := h1
    have hr : Rep 275 nrmY[i.val]! (Yp i) := rep_tp hp
    exact ⟨hr, Rep.inv_of_invOK hr hi, hmA, hmC⟩
  have hY0 : Yp 0 = three₁ := by
    have hr := (hrepY 0).1
    exact (tblEq_iff_eq hr hx).1 h0
  refine ⟨hY0, fun i => ⟨(hrepY i).1, (hrepY i).2.1⟩, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · exact hA.enum.mem_of_memT (hrepY i).1 (hrepY i).2.2.1
  · exact (hclass _ _ (hrepY i).1).1 (hrepY i).2.2.2
  · intro i j hij
    by_contra hne
    have h1 := (List.all_eq_true.1 hdist) i.val (List.mem_range.2 i.2)
    have h2 := (List.all_eq_true.1 h1) j.val (List.mem_range.2 j.2)
    have hne' : (i.val == j.val) = false := by
      simpa using fun h => hne (Fin.ext h)
    rw [hne', Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h2
    rcases hij with hij | hij
    · have := (tblEq_iff_eq (hrepY i).1 (hrepY j).1).2 hij
      rw [h2.1] at this
      exact Bool.false_ne_true this
    · have := (tblEq_iff_eq (hrepY i).1 (hrepY j).2.1).2 hij
      rw [h2.2] at this
      exact Bool.false_ne_true this
  · intro z hz hzc
    obtain ⟨k, hk, hkrep⟩ := hA.enum.cover z hz
    have hmc : memT 275 enumClass.1 enumA3.1[k]! = true := (hclass _ _ hkrep).2 hzc
    have h1 := Array.all_eq_true'.1 hcover enumA3.1[k]! (getElem!_mem_array hk)
    rw [hmc, Bool.not_true, Bool.false_or, Array.any_eq_true] at h1
    obtain ⟨j, hj, hjeq⟩ := h1
    have hjy : j < 10 := by simpa [nrmY] using hj
    refine ⟨⟨j, hjy⟩, ?_⟩
    have hrj := hrepY ⟨j, hjy⟩
    rw [getElem!_pos nrmY j hj] at hrj
    simp only [Bool.or_eq_true] at hjeq
    rcases hjeq with hjeq | hjeq
    · exact Or.inl ((tblEq_iff_eq hkrep hrj.1).1 hjeq)
    · exact Or.inr ((tblEq_iff_eq hkrep hrj.2.1).1 hjeq)

theorem nrmPt_le (z : Table) : nrmPt z ≤ 10 := by
  unfold nrmPt
  cases hf : (List.range 10).find? fun j =>
      tblEq 275 z nrmY[j]! || tblEq 275 z (invT 275 nrmY[j]!) with
  | none => simp
  | some j =>
    have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    simp only [Option.getD_some]
    omega

theorem nrmPt_spec {z : Table} (h : nrmPt z < 10) :
    ∃ p : Fin 10, nrmPt z = p.val ∧
      (tblEq 275 z nrmY[p.val]! = true ∨ tblEq 275 z (invT 275 nrmY[p.val]!) = true) := by
  unfold nrmPt at h ⊢
  cases hf : (List.range 10).find? fun j =>
      tblEq 275 z nrmY[j]! || tblEq 275 z (invT 275 nrmY[j]!) with
  | none => rw [hf] at h; simp at h
  | some j =>
    rw [hf] at h
    have hj := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    have hp := List.find?_some hf
    refine ⟨⟨j, hj⟩, by simp, ?_⟩
    simpa [Bool.or_eq_true] using hp

theorem ap_nrmAct (n : Table) (i : Fin 10) :
    ap (nrmAct n) i.val = nrmPt (conjT 275 n (invT 275 n) nrmY[i.val]!) := by
  unfold nrmAct
  rw [ap_ofFn _ i.isLt, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (nrmPt_le _) (by norm_num))

theorem rep_apply {n : ℕ} {T : Table} {g : Equiv.Perm (Fin n)} (h : Rep n T g) (i : Fin n) :
    ap T i.val = (g i).val := by
  rw [h i.val i.isLt, idx_of_lt g i.isLt]
  rfl

noncomputable def Np (j : Fin 2) : Equiv.Perm (Fin 275) := tp 275 nrmN[j.val]!

noncomputable def Wp (j : Fin 2) : Equiv.Perm (Fin 10) := tp 10 nrmW[j.val]!

theorem nrmN_size : nrmN.size = 2 := rfl

theorem nrmW_getElem (j : Fin 2) : nrmW[j.val]! = nrmAct nrmN[j.val]! := by
  have hj : j.val < nrmN.size := by rw [nrmN_size]; exact j.isLt
  unfold nrmW
  rw [getElem!_pos (nrmN.map nrmAct) j.val (by simpa using hj), Array.getElem_map,
    getElem!_pos nrmN j.val hj]

theorem nrmN_getElem_mem (j : Fin 2) : nrmN[j.val]! ∈ nrmN :=
  getElem!_mem_array (by rw [nrmN_size]; exact j.isLt)

theorem nrmN_facts
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (hy : nrmYCheck = true)
    (hn : nrmNormCheck = true) (ht : nrmTransCheck = true) (j : Fin 2) :
    Np j ∈ mclP ∧ Np j ∈ normalizer (subA3 : Set (Equiv.Perm (Fin 275))) ∧
      ∀ i : Fin 10, Np j * Yp i * (Np j)⁻¹ = Yp (Wp j i) ∨
        Np j * Yp i * (Np j)⁻¹ = (Yp (Wp j i))⁻¹ := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  obtain ⟨-, -, hA, -, -, -⟩ := threeEnumCheck_spec hrows he
  obtain ⟨-, hrepY, -, -, -, -⟩ := nrmY_facts hrows he hy
  simp only [nrmNormCheck, Bool.and_eq_true, beq_iff_eq] at hn
  obtain ⟨⟨-, hN1⟩, hN2⟩ := hn
  simp only [nrmTransCheck, Bool.and_eq_true] at ht
  obtain ⟨⟨hWperm, -⟩, -⟩ := ht
  have h1 := Array.all_eq_true'.1 hN1 nrmN[j.val]! (nrmN_getElem_mem j)
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨hp, hs⟩, hi⟩, hgen⟩ := h1
  have hrN : Rep 275 nrmN[j.val]! (Np j) := rep_tp hp
  have hriN : Rep 275 (invT 275 nrmN[j.val]!) (Np j)⁻¹ := Rep.inv_of_invOK hrN hi
  have hmP : Np j ∈ mclP := (hD.sift _ _ hrN).1 hs
  have hnorm : Np j ∈ normalizer (subA3 : Set (Equiv.Perm (Fin 275))) := by
    apply mem_normalizer_closure
    rintro _ ⟨a, ha, rfl⟩
    have h2 := Array.all_eq_true'.1 hgen a ha
    exact hA.enum.mem_of_memT (rep_conjT hrN hriN (hA.rep a ha)) h2
  refine ⟨hmP, hnorm, fun i => ?_⟩
  have h3 := Array.all_eq_true'.1 (Array.all_eq_true'.1 hN2 nrmN[j.val]! (nrmN_getElem_mem j))
    nrmY[i.val]! (nrmY_getElem_mem i)
  have h3' : nrmPt (conjT 275 nrmN[j.val]! (invT 275 nrmN[j.val]!) nrmY[i.val]!) < 10 := by
    simpa using h3
  obtain ⟨p, hpp, hpeq⟩ := nrmPt_spec h3'
  have hrz : Rep 275 (conjT 275 nrmN[j.val]! (invT 275 nrmN[j.val]!) nrmY[i.val]!)
      (Np j * Yp i * (Np j)⁻¹) := rep_conjT hrN hriN (hrepY i).1
  have hWj : (Wp j i).val = p.val := by
    have hW : Rep 10 nrmW[j.val]! (Wp j) := by
      apply rep_tp
      exact Array.all_eq_true'.1 hWperm nrmW[j.val]! (getElem!_mem_array (by
        have : nrmW.size = 2 := by simp [nrmW, nrmN_size]
        rw [this]; exact j.isLt))
    rw [← rep_apply hW i, nrmW_getElem, ap_nrmAct, hpp]
  have hWj' : Wp j i = p := Fin.ext hWj
  rw [hWj']
  rcases hpeq with hpeq | hpeq
  · exact Or.inl ((tblEq_iff_eq hrz (hrepY p).1).1 hpeq)
  · exact Or.inr ((tblEq_iff_eq hrz (hrepY p).2).1 hpeq)

theorem lift_closure {K : Type*} [Group K] (N : Subgroup K) (Y : Fin 10 → K)
    (gens : Set (Equiv.Perm (Fin 10)))
    (hgen : ∀ w ∈ gens, ∃ g ∈ N, ∀ i, g * Y i * g⁻¹ = Y (w i) ∨ g * Y i * g⁻¹ = (Y (w i))⁻¹)
    {w : Equiv.Perm (Fin 10)} (hw : w ∈ Subgroup.closure gens) :
    ∃ g ∈ N, ∀ i, g * Y i * g⁻¹ = Y (w i) ∨ g * Y i * g⁻¹ = (Y (w i))⁻¹ := by
  induction hw using Subgroup.closure_induction with
  | mem w hw => exact hgen w hw
  | one => exact ⟨1, N.one_mem, fun i => Or.inl (by simp)⟩
  | mul w w' _ _ ih ih' =>
    obtain ⟨g, hg, hgw⟩ := ih
    obtain ⟨g', hg', hgw'⟩ := ih'
    refine ⟨g * g', N.mul_mem hg hg', fun i => ?_⟩
    have e : g * g' * Y i * (g * g')⁻¹ = g * (g' * Y i * g'⁻¹) * g⁻¹ := by group
    rw [e, Equiv.Perm.mul_apply]
    rcases hgw' i with h1 | h1 <;> rcases hgw (w' i) with h2 | h2 <;> rw [h1]
    · exact Or.inl h2
    · exact Or.inr h2
    · right
      rw [show g * (Y (w' i))⁻¹ * g⁻¹ = (g * Y (w' i) * g⁻¹)⁻¹ by group, h2]
    · left
      rw [show g * (Y (w' i))⁻¹ * g⁻¹ = (g * Y (w' i) * g⁻¹)⁻¹ by group, h2, inv_inv]
  | inv w _ ih =>
    obtain ⟨g, hg, hgw⟩ := ih
    refine ⟨g⁻¹, N.inv_mem hg, fun i => ?_⟩
    have hwj : w (w⁻¹ i) = i := by simp
    have key := hgw (w⁻¹ i)
    rw [hwj] at key
    have e : g⁻¹ * Y i * g⁻¹⁻¹ = g⁻¹ * Y i * g := by group
    rw [e]
    rcases key with h | h
    · left
      rw [← h]
      group
    · right
      have h' : Y i = (g * Y (w⁻¹ i) * g⁻¹)⁻¹ := by rw [h, inv_inv]
      rw [h']
      group

noncomputable def W10 : Subgroup (Equiv.Perm (Fin 10)) := Subgroup.closure (Set.range Wp)

theorem nrmW_size : nrmW.size = 2 := by simp [nrmW, nrmN_size]

theorem W10_triples (ht : nrmTransCheck = true) :
    ∀ a b c : Fin 10, a ≠ b → a ≠ c → b ≠ c → ∃ w ∈ W10, w 0 = a ∧ w 1 = b ∧ w 2 = c := by
  simp only [nrmTransCheck, Bool.and_eq_true] at ht
  obtain ⟨⟨hWperm, htree⟩, htriple⟩ := ht
  have hWrep : ∀ l < nrmW.size, Rep 10 nrmW[l]! (tp 10 nrmW[l]!) := fun l hl =>
    rep_tp (Array.all_eq_true'.1 hWperm _ (getElem!_mem_array hl))
  have hgen : ∀ l < nrmW.size, Rep 10 nrmW[l]! ((fun l => tp 10 nrmW[l]!) l) ∧
      (fun l => tp 10 nrmW[l]!) l ∈ W10 := by
    intro l hl
    refine ⟨hWrep l hl, ?_⟩
    have hl2 : l < 2 := by rw [nrmW_size] at hl; exact hl
    exact Subgroup.subset_closure ⟨⟨l, hl2⟩, rfl⟩
  have hE := mulTreeOK_spec (by norm_num : 10 < 2 ^ 32) W10 (gg := fun l => tp 10 nrmW[l]!)
    hgen htree
  intro a b c hab hac hbc
  have h1 := (List.all_eq_true.1 htriple) a.val (List.mem_range.2 a.2)
  have h2 := (List.all_eq_true.1 h1) b.val (List.mem_range.2 b.2)
  have h3 := (List.all_eq_true.1 h2) c.val (List.mem_range.2 c.2)
  have hab' : (a.val == b.val) = false := by simpa using fun h => hab (Fin.ext h)
  have hac' : (a.val == c.val) = false := by simpa using fun h => hac (Fin.ext h)
  have hbc' : (b.val == c.val) = false := by simpa using fun h => hbc (Fin.ext h)
  rw [hab', hac', hbc', Bool.false_or, Bool.false_or, Bool.false_or, Array.any_eq_true] at h3
  obtain ⟨k, hk, hkeq⟩ := h3
  simp only [Bool.and_eq_true, beq_iff_eq] at hkeq
  obtain ⟨c', hc', hrep⟩ := hE k hk
  rw [getElem!_pos nrmClosure.1 k hk] at hrep
  refine ⟨c', hc', ?_, ?_, ?_⟩
  · apply Fin.ext
    have := rep_apply hrep 0
    simp only [Fin.val_zero] at this
    rw [← this]
    exact hkeq.1.1
  · apply Fin.ext
    have := rep_apply hrep 1
    simp only [Fin.val_one] at this
    rw [← this]
    exact hkeq.1.2
  · apply Fin.ext
    have := rep_apply hrep 2
    simp only [Fin.val_two] at this
    rw [← this]
    exact hkeq.2

theorem W10_trans3 (ht : nrmTransCheck = true) (a b : Fin 3 → Fin 10) (ha : Function.Injective a)
    (hb : Function.Injective b) : ∃ w ∈ W10, ∀ i, w (a i) = b i := by
  have hd : ∀ f : Fin 3 → Fin 10, Function.Injective f → f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2 := by
    intro f hf
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact absurd (hf h) (by decide)
    · exact absurd (hf h) (by decide)
    · exact absurd (hf h) (by decide)
  obtain ⟨hab, hac, hbc⟩ := hd a ha
  obtain ⟨hab', hac', hbc'⟩ := hd b hb
  obtain ⟨wa, hwa, hwa0, hwa1, hwa2⟩ := W10_triples ht _ _ _ hab hac hbc
  obtain ⟨wb, hwb, hwb0, hwb1, hwb2⟩ := W10_triples ht _ _ _ hab' hac' hbc'
  refine ⟨wb * wa⁻¹, W10.mul_mem hwb (W10.inv_mem hwa), fun i => ?_⟩
  rw [Equiv.Perm.mul_apply]
  fin_cases i
  · have : wa⁻¹ (a 0) = 0 := Equiv.Perm.inv_eq_iff_eq.2 hwa0.symm
    simp [this, hwb0]
  · have : wa⁻¹ (a 1) = 1 := Equiv.Perm.inv_eq_iff_eq.2 hwa1.symm
    simp [this, hwb1]
  · have : wa⁻¹ (a 2) = 2 := Equiv.Perm.inv_eq_iff_eq.2 hwa2.symm
    simp [this, hwb2]

noncomputable def Cp (i : Fin 10) : Equiv.Perm (Fin 275) := tp 275 nrmC[i.val]!

theorem nrmC_getElem_mem (i : Fin 10) : nrmC[i.val]! ∈ nrmC :=
  getElem!_mem_array (by simp [nrmC])

theorem nrmC_facts
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (hc : nrmConjCheck = true) :
    (∀ i, Cp i ∈ mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275)))) ∧
      ∀ i j, i ≠ j → (Cp j)⁻¹ * Cp i ∉ normalizer (subA3 : Set (Equiv.Perm (Fin 275))) := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  obtain ⟨-, -, hA, hx, -, -⟩ := threeEnumCheck_spec hrows he
  simp only [nrmConjCheck, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨-, hall⟩, hdist⟩ := hc
  have hrep : ∀ i : Fin 10, Rep 275 nrmC[i.val]! (Cp i) ∧
      Rep 275 (invT 275 nrmC[i.val]!) (Cp i)⁻¹ ∧ Cp i ∈ mclP ∧ Cp i * three₁ = three₁ * Cp i := by
    intro i
    have h1 := Array.all_eq_true'.1 hall nrmC[i.val]! (nrmC_getElem_mem i)
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨⟨hp, hs⟩, hi⟩, hcomm⟩ := h1
    have hr : Rep 275 nrmC[i.val]! (Cp i) := rep_tp hp
    exact ⟨hr, Rep.inv_of_invOK hr hi, (hD.sift _ _ hr).1 hs, (commTT_iff hr hx).1 hcomm⟩
  refine ⟨fun i => mem_inf.2 ⟨(hrep i).2.2.1, mem_centralizer_singleton_iff.2 (hrep i).2.2.2⟩,
    fun i j hij hnorm => ?_⟩
  have h1 := (List.all_eq_true.1 hdist) i.val (List.mem_range.2 i.2)
  have h2 := (List.all_eq_true.1 h1) j.val (List.mem_range.2 j.2)
  have hne' : (i.val == j.val) = false := by simpa using fun h => hij (Fin.ext h)
  rw [hne', Bool.false_or, Array.any_eq_true] at h2
  obtain ⟨k, hk, hkeq⟩ := h2
  have hkA : k < aGens3.size := hk
  have hka : aGens3[k] ∈ aGens3 := Array.getElem_mem hk
  have hmem : (Cp j)⁻¹ * Cp i * tp 275 aGens3[k] * ((Cp j)⁻¹ * Cp i)⁻¹ ∈ subA3 :=
    (mem_normalizer_iff.1 hnorm _).1 (Subgroup.subset_closure ⟨_, hka, rfl⟩)
  have hrj := hrep j
  have hri := hrep i
  have hrk : Rep 275 aGens3[k] (tp 275 aGens3[k]) := hA.rep _ hka
  have hrz : Rep 275 (conjT 275 (invT 275 nrmC[j.val]!) nrmC[j.val]!
      (conjT 275 nrmC[i.val]! (invT 275 nrmC[i.val]!) aGens3[k]))
      ((Cp j)⁻¹ * (Cp i * tp 275 aGens3[k] * (Cp i)⁻¹) * ((Cp j)⁻¹)⁻¹) :=
    rep_conjT hrj.2.1 (by rw [inv_inv]; exact hrj.1) (rep_conjT hri.1 hri.2.1 hrk)
  have e : (Cp j)⁻¹ * (Cp i * tp 275 aGens3[k] * (Cp i)⁻¹) * ((Cp j)⁻¹)⁻¹ =
      (Cp j)⁻¹ * Cp i * tp 275 aGens3[k] * ((Cp j)⁻¹ * Cp i)⁻¹ := by group
  rw [e] at hrz
  have := hA.enum.memT_of_mem hrz hmem
  rw [Bool.not_eq_true'] at hkeq
  rw [this] at hkeq
  exact Bool.false_ne_true hkeq.symm

structure PinnedNorm (Y : Fin 10 → Equiv.Perm (Fin 275)) : Prop where
  le : subA3 ≤ mclP
  zero : Y 0 = three₁
  mem_A : ∀ i, Y i ∈ subA3
  conj : ∀ i, Y i ∈ conjClass mclP three₁
  distinct : ∀ i j, (Y i = Y j ∨ Y i = (Y j)⁻¹) → i = j
  cover : ∀ z ∈ subA3, z ∈ conjClass mclP three₁ → ∃ i, z = Y i ∨ z = (Y i)⁻¹
  trans3 : ∀ a b : Fin 3 → Fin 10, Function.Injective a → Function.Injective b →
    ∃ g ∈ mclP ⊓ normalizer (subA3 : Set (Equiv.Perm (Fin 275))),
      ∀ i, g * Y (a i) * g⁻¹ = Y (b i) ∨ g * Y (a i) * g⁻¹ = (Y (b i))⁻¹
  sharp3 : ∀ g ∈ mclP ⊓ normalizer (subA3 : Set (Equiv.Perm (Fin 275))),
    ∀ a : Fin 3 → Fin 10, Function.Injective a →
      (∀ i, g * Y (a i) * g⁻¹ = Y (a i) ∨ g * Y (a i) * g⁻¹ = (Y (a i))⁻¹) → g ∈ subA3

theorem nrmCheck_spec
    (hrows : ThreeFacts) (hloc : threeLocalCheck = true) (h : nrmCheck = true) :
    ∃ Y : Fin 10 → Equiv.Perm (Fin 275), PinnedNorm Y := by
  simp only [threeLocalCheck, Bool.and_eq_true] at hloc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨he, -⟩, hin⟩, -⟩, -⟩, -⟩, hAs⟩, -⟩, -⟩, -⟩ := hloc
  simp only [nrmCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hy, hn⟩, ht⟩, hc⟩ := h
  obtain ⟨hY0, hrepY, hYA, hYc, hYd, hYcov⟩ := nrmY_facts hrows he hy
  obtain ⟨-, -, hA, -, -, -⟩ := threeEnumCheck_spec hrows he
  obtain ⟨hAel, -⟩ := aStructCheck_spec hrows he hin hAs
  have hAcomm : ∀ a ∈ subA3, ∀ b ∈ subA3, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥subA3)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hCmem, hCne⟩ := nrmC_facts hrows he hc
  obtain ⟨-, -, hCx, -⟩ := three₁_facts hrows
  set N : Subgroup (Equiv.Perm (Fin 275)) :=
    mclP ⊓ normalizer (subA3 : Set (Equiv.Perm (Fin 275))) with hNdef
  have hperm : ∀ g ∈ N, ∀ i, ∃ j, g * Yp i * g⁻¹ = Yp j ∨ g * Yp i * g⁻¹ = (Yp j)⁻¹ := by
    intro g hg i
    apply hYcov
    · exact (mem_normalizer_iff.1 (mem_inf.1 hg).2 _).1 (hYA i)
    · obtain ⟨c, hc, hci⟩ := hYc i
      exact ⟨g * c, mclP.mul_mem (mem_inf.1 hg).1 hc, by rw [hci]; group⟩
  have hcard : Nat.card N ≤ 58320 := by
    let T : Finset (Equiv.Perm (Fin 275)) :=
      Finset.univ.image Yp ∪ Finset.univ.image fun i => (Yp i)⁻¹
    have hT : ∀ n ∈ N, n * three₁ * n⁻¹ ∈ T := by
      intro n hn
      obtain ⟨j, hj⟩ := hperm n hn 0
      rw [hY0] at hj
      simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      rcases hj with hj | hj
      · exact Or.inl ⟨j, hj.symm⟩
      · exact Or.inr ⟨j, hj.symm⟩
    have h1 := card_le_mul_card_centralizer N three₁ T hT
    have hTc : T.card ≤ 20 := by
      calc T.card ≤ (Finset.univ.image Yp).card + (Finset.univ.image fun i => (Yp i)⁻¹).card :=
            Finset.card_union_le _ _
        _ ≤ 10 + 10 := by
            apply add_le_add
            · calc _ ≤ (Finset.univ : Finset (Fin 10)).card := Finset.card_image_le
                _ = 10 := by simp
            · calc _ ≤ (Finset.univ : Finset (Fin 10)).card := Finset.card_image_le
                _ = 10 := by simp
        _ = 20 := by norm_num
    have hinf : N ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) =
        (mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275)))) ⊓
          normalizer (subA3 : Set (Equiv.Perm (Fin 275))) := by
      ext g
      simp only [hNdef, mem_inf]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩⟩
    have h2 := ten_mul_card_inf_normalizer_le (mclP ⊓ centralizer ({three₁} :
      Set (Equiv.Perm (Fin 275)))) subA3 Cp hCmem hCne
    rw [hCx] at h2
    rw [hinf] at h1
    calc Nat.card N ≤ T.card * Nat.card ↥((mclP ⊓ centralizer ({three₁} :
          Set (Equiv.Perm (Fin 275)))) ⊓ normalizer (subA3 : Set (Equiv.Perm (Fin 275)))) := h1
      _ ≤ 20 * 2916 := Nat.mul_le_mul hTc (by omega)
      _ = 58320 := by norm_num
  have htrans : ∀ a b : Fin 3 → Fin 10, Function.Injective a → Function.Injective b →
      ∃ g ∈ N, ∀ i, g * Yp (a i) * g⁻¹ = Yp (b i) ∨ g * Yp (a i) * g⁻¹ = (Yp (b i))⁻¹ := by
    intro a b ha hb
    obtain ⟨w, hw, hwab⟩ := W10_trans3 ht a b ha hb
    obtain ⟨g, hg, hgw⟩ := lift_closure N Yp (Set.range Wp) (by
      rintro _ ⟨j, rfl⟩
      obtain ⟨hmP, hnorm, hact⟩ := nrmN_facts hrows he hy hn ht j
      exact ⟨Np j, mem_inf.2 ⟨hmP, hnorm⟩, hact⟩) hw
    refine ⟨g, hg, fun i => ?_⟩
    have := hgw (a i)
    rwa [hwab i] at this
  refine ⟨Yp, ⟨hA.le, hY0, hYA, hYc, hYd, hYcov, htrans, ?_⟩⟩
  intro g hg a ha hga
  exact mem_of_fixes_three_points (N := N) (A := subA3)
    (fun x hx => mem_inf.2 ⟨hA.le hx, Subgroup.le_normalizer hx⟩)
    hA.card hcard Yp hYd hperm
    (fun x hx i => hAcomm x hx _ (hYA i)) htrans hg ha hga

end CFSG.Sporadic.Recognition.McLAS
