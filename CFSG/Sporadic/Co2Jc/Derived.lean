module

public import CFSG.Sporadic.Co2Jc.Omega
public import CFSG.Sporadic.Co2Jc.Linear
public import Certificates.Certificate719010

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open scoped commutatorElement

theorem derived_check : Native.derivedOK = true := Certificates.certificate719010

theorem sameOnBasis_spec {w w' : List ℕ} (h : Native.sameOnBasis w w' = true) :
    ∀ i < 10, wordAct w (2 ^ i) = wordAct w' (2 ^ i) := by
  simp only [Native.sameOnBasis, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem wordOK_spec {w w' : List ℕ} (h : Native.wordOK w w' = true) :
    (∀ i < 10, wordAct w (2 ^ i) = wordAct w' (2 ^ i)) ∧ (∀ l ∈ w, l < 3) ∧
      ∀ l ∈ w', l < 3 := by
  simp only [Native.wordOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨sameOnBasis_spec h.1.1, h.1.2, h.2⟩

theorem order_check : Native.orderOK = true := by
  have h := derived_check
  simp only [Native.derivedOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.1

theorem conj_check : Native.conjOK = true := by
  have h := derived_check
  simp only [Native.derivedOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem elem_check : Native.elemOK = true := by
  have h := derived_check
  simp only [Native.derivedOK, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem pull_check : Native.pullOK = true := by
  have h := derived_check
  simp only [Native.derivedOK, Bool.and_eq_true] at h
  exact h.1.1.2

theorem sign_check : Native.signOK = true := by
  have h := derived_check
  simp only [Native.derivedOK, Bool.and_eq_true] at h
  exact h.1.2

theorem mask_check : Native.maskOK = true := by
  have h := derived_check
  simp only [Native.derivedOK, Bool.and_eq_true] at h
  exact h.2

theorem conj_spec {k i : ℕ} (hk : k < 3) (hi : i < 2) :
    (∀ j < 10, wordAct ([k] ++ Native.gwList[i]! ++ Native.invW[k]!) (2 ^ j) =
      wordAct (dWord ((Data.conjD[k]!)[i]!)) (2 ^ j)) ∧
      (∀ l ∈ [k] ++ Native.gwList[i]! ++ Native.invW[k]!, l < 3) ∧
      ∀ l ∈ dWord ((Data.conjD[k]!)[i]!), l < 3 := by
  have h := conj_check
  simp only [Native.conjOK, List.all_eq_true, List.mem_range] at h
  exact wordOK_spec (h k hk i hi)

theorem pullK_spec {k i : ℕ} (hk : k < 3) (hi : i < 22) :
    (Native.pullList[k]!)[i]! < 22 ∧ ∀ j < 10,
      Co2Smith.Native.glNJT k (2 ^ j) < 1024 ∧
        Native.phi (Data.d22[(Native.pullList[k]!)[i]!]!) (2 ^ j) =
          Native.phi (Data.d22[i]!) (Co2Smith.Native.glNJT k (2 ^ j)) := by
  have h := pull_check
  simp only [Native.pullOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have h2 := h.2 k hk i hi
  simp only [Native.pullK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq] at h2
  exact h2

theorem sign_spec :
    Data.swapsA.length = 19 ∧
      (∀ p ∈ Data.swapsA, p.length = 2 ∧ (∀ l ∈ p, l < 22) ∧ p[0]! ≠ p[1]!) ∧
      ∀ i < 22, Native.prodSwaps Data.swapsA i = Data.pullA[i]! := by
  have h := sign_check
  simp only [Native.signOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne] at h
  exact ⟨h.1.1, fun p hp => ⟨(h.1.2 p hp).1.1, (h.1.2 p hp).1.2, (h.1.2 p hp).2⟩, h.2⟩

theorem qWord_singleton (k : ℕ) : qWord [k] = qA k := by
  simp [qWord]

theorem qWord_two (a b : ℕ) : qWord [a, b] = qA a * qA b := by
  simp [qWord]

theorem qWord_three (a b c : ℕ) : qWord [a, b, c] = qA a * qA b * qA c := by
  simp [qWord, mul_assoc]

theorem qWord_replicate (n k : ℕ) : qWord (List.replicate n k) = (qA k) ^ n := by
  rw [qWord, List.map_replicate, List.prod_replicate]

theorem qA_zero_pow_twelve : (qA 0) ^ 12 = 1 := by
  have h := order_check
  simp only [Native.orderOK, Bool.and_eq_true] at h
  have h0 : ∀ i < 10, wordAct (List.replicate 12 0) (2 ^ i) = wordAct [] (2 ^ i) :=
    sameOnBasis_spec h.1.1
  rw [← qWord_replicate 12 0, ← qWord_nil]
  exact qWord_eq_qWord (fun k hk => by
    simp only [List.mem_replicate] at hk
    omega) (by simp) h0

theorem qA_one_pow_three : (qA 1) ^ 3 = 1 := by
  have h := order_check
  simp only [Native.orderOK, Bool.and_eq_true] at h
  have h0 : ∀ i < 10, wordAct (List.replicate 3 1) (2 ^ i) = wordAct [] (2 ^ i) :=
    sameOnBasis_spec h.1.2
  rw [← qWord_replicate 3 1, ← qWord_nil]
  exact qWord_eq_qWord (fun k hk => by
    simp only [List.mem_replicate] at hk
    omega) (by simp) h0

theorem qA_two_pow_two : (qA 2) ^ 2 = 1 := by
  have h := order_check
  simp only [Native.orderOK, Bool.and_eq_true] at h
  have h0 : ∀ i < 10, wordAct (List.replicate 2 2) (2 ^ i) = wordAct [] (2 ^ i) :=
    sameOnBasis_spec h.2
  rw [← qWord_replicate 2 2, ← qWord_nil]
  exact qWord_eq_qWord (fun k hk => by
    simp only [List.mem_replicate] at hk
    omega) (by simp) h0

theorem qA_zero_inv : (qA 0)⁻¹ = (qA 0) ^ 11 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ', show (11 + 1 : ℕ) = 12 from rfl, qA_zero_pow_twelve]

theorem qA_one_inv : (qA 1)⁻¹ = (qA 1) ^ 2 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ', show (2 + 1 : ℕ) = 3 from rfl, qA_one_pow_three]

theorem qA_two_inv : (qA 2)⁻¹ = qA 2 := by
  refine inv_eq_of_mul_eq_one_right ?_
  simpa [pow_two] using qA_two_pow_two

theorem qA_zero_sq_inv : (qA 0 * qA 0)⁻¹ = (qA 0) ^ 22 := by
  rw [mul_inv_rev, qA_zero_inv, ← pow_add]

theorem qWord_invW (k : ℕ) (hk : k < 3) : qWord (Native.invW[k]!) = (qA k)⁻¹ := by
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk3 with rfl | rfl | rfl
  · show qWord (List.replicate 11 0) = (qA 0)⁻¹
    rw [qWord_replicate, qA_zero_inv]
  · show qWord (List.replicate 2 1) = (qA 1)⁻¹
    rw [qWord_replicate, qA_one_inv]
  · show qWord (List.replicate 1 2) = (qA 2)⁻¹
    rw [qWord_replicate, pow_one, qA_two_inv]

@[expose] noncomputable def dVal (w : List ℕ) : MulAut ↥Jc :=
  (w.map fun l => if l = 0 then qWord g1w else qWord g2w).prod

theorem qWord_flatMap (w : List ℕ) (f : ℕ → List ℕ) :
    qWord (w.flatMap f) = (w.map fun l => qWord (f l)).prod := by
  induction w with
  | nil => simp [qWord_nil]
  | cons a t ih => simp [List.flatMap_cons, qWord_append, qWord_cons, ih]

theorem qWord_dWord (w : List ℕ) : qWord (dWord w) = dVal w := by
  rw [dWord, qWord_flatMap, dVal]
  congr 1
  exact List.map_congr_left fun l _ => by by_cases h : l = 0 <;> simp [h]

@[expose] noncomputable def Dg : Subgroup (MulAut ↥Jc) := Subgroup.closure {qWord g1w, qWord g2w}

theorem dVal_mem (w : List ℕ) : dVal w ∈ Dg := by
  induction w with
  | nil => exact Dg.one_mem
  | cons a t ih =>
    rw [dVal, List.map_cons, List.prod_cons]
    refine Dg.mul_mem ?_ ih
    by_cases h : a = 0
    · rw [if_pos h]
      exact Subgroup.subset_closure (by simp)
    · rw [if_neg h]
      exact Subgroup.subset_closure (by simp)

theorem qWord_g1w_eq : qWord g1w = ⁅qA 0, qA 1⁆ := by
  rw [g1w, qWord_append, qWord_append, qWord_two, qWord_replicate, qWord_two,
    commutatorElement_def, ← pow_two, ← qA_one_inv, ← qA_zero_inv]

theorem qWord_g2w_eq : qWord g2w = ⁅qA 0 * qA 0, qA 2⁆ := by
  rw [g2w, qWord_append, qWord_append, qWord_three, qWord_replicate, qWord_singleton,
    commutatorElement_def, qA_two_inv, qA_zero_sq_inv]

theorem qWord_g1w_mem : qWord g1w ∈ ⁅Qj, Qj⁆ := by
  rw [qWord_g1w_eq]
  exact Subgroup.commutator_mem_commutator (qA_mem (by norm_num)) (qA_mem (by norm_num))

theorem qWord_g2w_mem : qWord g2w ∈ ⁅Qj, Qj⁆ := by
  rw [qWord_g2w_eq]
  exact Subgroup.commutator_mem_commutator
    (Qj.mul_mem (qA_mem (by norm_num)) (qA_mem (by norm_num))) (qA_mem (by norm_num))

theorem Dg_le_commutator : Dg ≤ ⁅Qj, Qj⁆ := by
  rw [Dg, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact qWord_g1w_mem
  · exact qWord_g2w_mem

theorem Dg_le_Qj : Dg ≤ Qj := by
  simpa using Dg_le_commutator.trans (Subgroup.commutator_le_sup (H₁ := Qj) (H₂ := Qj))

theorem qWord_conjD (k : ℕ) (hk : k < 3) (i : ℕ) (hi : i < 2) :
    qA k * qWord (Native.gwList[i]!) * (qA k)⁻¹ = dVal ((Data.conjD[k]!)[i]!) := by
  obtain ⟨hb, hletters, hletters'⟩ := conj_spec hk hi
  have hword : qWord ([k] ++ Native.gwList[i]! ++ Native.invW[k]!) =
      qWord (dWord ((Data.conjD[k]!)[i]!)) :=
    qWord_eq_qWord hletters hletters' hb
  have hw : qWord ([k] ++ Native.gwList[i]! ++ Native.invW[k]!) =
      qA k * qWord (Native.gwList[i]!) * (qA k)⁻¹ := by
    rw [qWord_append, qWord_append, qWord_singleton, qWord_invW k hk]
  rw [← hw, hword, qWord_dWord]

theorem qA_conj_g1w {k : ℕ} (hk : k < 3) :
    qA k * qWord g1w * (qA k)⁻¹ ∈ Dg := by
  have h := qWord_conjD k hk 0 (by norm_num)
  rw [show Native.gwList[0]! = g1w from rfl] at h
  rw [h]
  exact dVal_mem _

theorem qA_conj_g2w {k : ℕ} (hk : k < 3) :
    qA k * qWord g2w * (qA k)⁻¹ ∈ Dg := by
  have h := qWord_conjD k hk 1 (by norm_num)
  rw [show Native.gwList[1]! = g2w from rfl] at h
  rw [h]
  exact dVal_mem _

theorem conj_mem_Dg_of_gen {n : ℕ} (hn : n < 3) {d : MulAut ↥Jc} (hd : d ∈ Dg) :
    qA n * d * (qA n)⁻¹ ∈ Dg := by
  have h1 : qA n * qWord g1w * (qA n)⁻¹ ∈ Dg := qA_conj_g1w hn
  have h2 : qA n * qWord g2w * (qA n)⁻¹ ∈ Dg := qA_conj_g2w hn
  clear hn
  refine Subgroup.closure_induction
    (k := ({qWord g1w, qWord g2w} : Set (MulAut ↥Jc)))
    (p := fun d _ => qA n * d * (qA n)⁻¹ ∈ Dg) ?_ ?_ ?_ ?_ hd
  · rintro x (rfl | rfl)
    · exact h1
    · exact h2
  · simpa using Dg.one_mem
  · intro a b ha hb iha ihb
    have e : qA n * (a * b) * (qA n)⁻¹ =
        (qA n * a * (qA n)⁻¹) * (qA n * b * (qA n)⁻¹) := by group
    rw [e]
    exact Dg.mul_mem iha ihb
  · intro a ha iha
    have e : qA n * a⁻¹ * (qA n)⁻¹ = (qA n * a * (qA n)⁻¹)⁻¹ := by group
    rw [e]
    exact Dg.inv_mem iha

theorem conj_mem_Dg {g : MulAut ↥Jc} (hg : g ∈ Qj) :
    ∀ d ∈ Dg, g * d * g⁻¹ ∈ Dg := by
  refine Qj_induction (P := fun g => ∀ d ∈ Dg, g * d * g⁻¹ ∈ Dg) ?_ ?_ hg
  · intro d hd
    simpa using hd
  · intro k hk g hg ih d hd
    have h1 : g * d * g⁻¹ ∈ Dg := ih d hd
    have h2 : qA k * (g * d * g⁻¹) * (qA k)⁻¹ ∈ Dg := conj_mem_Dg_of_gen hk h1
    have hgoal : (qA k * g) * d * (qA k * g)⁻¹ = qA k * (g * d * g⁻¹) * (qA k)⁻¹ := by
      group
    rw [hgoal]
    exact h2

instance subgroupOf_Dg_normal : (Dg.subgroupOf Qj).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_Dg g.2 n.1 hn⟩

theorem qA_one_mem_Dg : qA 1 ∈ Dg := by
  have h := elem_check
  simp only [Native.elemOK, Bool.and_eq_true] at h
  obtain ⟨hb, hletters, hletters'⟩ := wordOK_spec h.1.1
  have hw : qWord [1] = qWord (dWord Data.bD) := qWord_eq_qWord hletters hletters' hb
  rw [qWord_singleton] at hw
  rw [hw, qWord_dWord]
  exact dVal_mem _

theorem ca_inv_mem_Dg : qA 2 * (qA 0)⁻¹ ∈ Dg := by
  have h := elem_check
  simp only [Native.elemOK, Bool.and_eq_true] at h
  obtain ⟨hc, hletters, hletters'⟩ := wordOK_spec h.1.2
  have hw : qWord ([2] ++ List.replicate 11 0) = qWord (dWord Data.caD) :=
    qWord_eq_qWord hletters hletters' hc
  rw [qWord_append, qWord_singleton, qWord_replicate, ← qA_zero_inv] at hw
  rw [hw, qWord_dWord]
  exact dVal_mem _

theorem qA_zero_sq_mem_Dg : qA 0 * qA 0 ∈ Dg := by
  have h := elem_check
  simp only [Native.elemOK, Bool.and_eq_true] at h
  obtain ⟨ha, hletters, hletters'⟩ := wordOK_spec h.2
  have hw : qWord [0, 0] = qWord (dWord Data.a2D) := qWord_eq_qWord hletters hletters' ha
  rw [qWord_two] at hw
  rw [hw, qWord_dWord]
  exact dVal_mem _

@[expose] noncomputable def Dj : Subgroup Qj := Dg.subgroupOf Qj

instance Dj_normal : Dj.Normal := subgroupOf_Dg_normal

@[expose] noncomputable def qD : Qj →* Qj ⧸ Dj := QuotientGroup.mk' Dj

theorem qD_eq_one_iff {x : Qj} : qD x = 1 ↔ x ∈ Dj := by
  have h : qD.ker = Dj := QuotientGroup.ker_mk' (N := Dj)
  rw [← MonoidHom.mem_ker, h]

theorem qD_qA_one (h : qA 1 ∈ Qj) : qD ⟨qA 1, h⟩ = 1 := by
  rw [qD_eq_one_iff, Dj, Subgroup.mem_subgroupOf]
  exact qA_one_mem_Dg

theorem qD_qA_two (h : qA 2 ∈ Qj) (h' : qA 0 ∈ Qj) :
    qD ⟨qA 2, h⟩ = qD ⟨qA 0, h'⟩ := by
  have h2 : qD (⟨qA 2, h⟩ * (⟨qA 0, h'⟩)⁻¹) = 1 := by
    rw [qD_eq_one_iff, Dj, Subgroup.mem_subgroupOf]
    simpa using ca_inv_mem_Dg
  rw [map_mul, map_inv] at h2
  exact mul_inv_eq_one.mp h2

theorem qD_qA_zero_sq (h : qA 0 ∈ Qj) : qD ⟨qA 0, h⟩ ^ 2 = 1 := by
  rw [pow_two, ← map_mul, qD_eq_one_iff, Dj, Subgroup.mem_subgroupOf]
  simpa using qA_zero_sq_mem_Dg

@[expose] noncomputable def Sg : Subgroup Qj :=
  Subgroup.closure (Set.range fun k : Fin 3 => (⟨qA k, qA_mem k.2⟩ : Qj))

theorem top_map_subtype : (⊤ : Subgroup Qj).map Qj.subtype = Qj := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem Sg_map : Sg.map Qj.subtype = Qj := by
  refine le_antisymm ?_ ?_
  · calc Sg.map Qj.subtype ≤ (⊤ : Subgroup Qj).map Qj.subtype := Subgroup.map_mono le_top
      _ = Qj := top_map_subtype
  · intro x hx
    have h2 : x ∈ Subgroup.closure (Set.range fun k : Fin 3 => qA k) := by
      rw [← Qj_eq_closure]
      exact hx
    rw [Sg, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_ h2
    rintro y ⟨k, rfl⟩
    exact ⟨⟨qA k, qA_mem k.2⟩, Set.mem_range_self k, rfl⟩

theorem Sg_eq_top : Sg = ⊤ := by
  refine Subgroup.map_injective Qj.subtype_injective ?_
  calc Sg.map Qj.subtype = Qj := Sg_map
    _ = (⊤ : Subgroup Qj).map Qj.subtype := top_map_subtype.symm

theorem qD_mem_Sg {x : Qj} (hx : x ∈ Sg) : qD x = 1 ∨ qD x = qD ⟨qA 0, qA_mem (by norm_num)⟩ := by
  refine Subgroup.closure_induction
    (p := fun x _ => qD x = 1 ∨ qD x = qD ⟨qA 0, qA_mem (by norm_num)⟩) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨k, rfl⟩
    show qD ⟨qA (k : ℕ), qA_mem k.2⟩ = 1 ∨
      qD ⟨qA (k : ℕ), qA_mem k.2⟩ = qD ⟨qA 0, qA_mem (by norm_num)⟩
    have hk : (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2 := by
      have := k.2; omega
    rcases hk with hk | hk | hk
    · refine Or.inr (congrArg qD (Subtype.ext ?_))
      show qA (k : ℕ) = qA 0
      rw [hk]
    · refine Or.inl ?_
      rw [show (⟨qA (k : ℕ), qA_mem k.2⟩ : Qj) = ⟨qA 1, qA_mem (by norm_num)⟩
        from Subtype.ext (by show qA (k : ℕ) = qA 1; rw [hk])]
      exact qD_qA_one _
    · refine Or.inr ?_
      rw [show (⟨qA (k : ℕ), qA_mem k.2⟩ : Qj) = ⟨qA 2, qA_mem (by norm_num)⟩
        from Subtype.ext (by show qA (k : ℕ) = qA 2; rw [hk])]
      exact qD_qA_two _ _
  · exact Or.inl (map_one qD)
  · intro a b ha hb iha ihb
    rcases iha with h | h <;> rcases ihb with h' | h'
    · exact Or.inl (by rw [map_mul, h, h', one_mul])
    · exact Or.inr (by rw [map_mul, h, h', one_mul])
    · exact Or.inr (by rw [map_mul, h, h', mul_one])
    · refine Or.inl ?_
      rw [map_mul, h, h', ← pow_two]
      exact qD_qA_zero_sq _
  · intro a ha iha
    rcases iha with h | h
    · exact Or.inl (by rw [map_inv, h, inv_one])
    · have hinv : (qD ⟨qA 0, qA_mem (by norm_num)⟩)⁻¹ = qD ⟨qA 0, qA_mem (by norm_num)⟩ :=
        inv_eq_of_mul_eq_one_right (qD_qA_zero_sq _)
      exact Or.inr (by rw [map_inv, h, hinv])

theorem qD_cases (z : Qj ⧸ Dj) : z = 1 ∨ z = qD ⟨qA 0, qA_mem (by norm_num)⟩ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Dj z
  exact qD_mem_Sg (by rw [Sg_eq_top]; exact Subgroup.mem_top x)

theorem qD_qA_zero_ne_one (hna : qA 0 ∉ Dg) :
    qD ⟨qA 0, qA_mem (by norm_num)⟩ ≠ 1 := by
  change QuotientGroup.mk' Dj ⟨qA 0, qA_mem (by norm_num)⟩ ≠ 1
  intro h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Dj, Subgroup.mem_subgroupOf] at h
  exact hna h

theorem quotient_card (hna : qA 0 ∉ Dg) : Nat.card (Qj ⧸ Dj) = 2 := by
  rw [Nat.card_eq_two_iff' 1]
  refine ⟨qD ⟨qA 0, qA_mem (by norm_num)⟩, qD_qA_zero_ne_one hna, ?_⟩
  intro z hz
  rcases qD_cases z with h | h
  · exact absurd h hz
  · exact h

@[expose] def phiM (f m : ℕ) : ZMod 2 := bsum 10 m fun l => if f.testBit l then 1 else 0

@[expose] def maskD (i : Fin 22) : ℕ := Data.d22[i.val]!

@[expose] noncomputable def Phi (i : Fin 22) (x : ↥Jc) : ZMod 2 := phiM (maskD i) (coord x)

theorem maskOK_spec : (∀ i : Fin 22, Data.d22[i.val]! < 1024) ∧
    ∀ i j : Fin 22, Data.d22[i.val]! = Data.d22[j.val]! → i = j := by
  have h := mask_check
  simp only [Native.maskOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    bne_iff_ne, decide_eq_true_eq, Bool.or_eq_true] at h
  refine ⟨fun i => h.1.2 _ ?_, fun i j hij => ?_⟩
  · rw [getElem!_pos Data.d22 i.val (by rw [h.1.1]; exact i.isLt)]
    exact List.getElem_mem _
  · by_contra hne
    have hne' : i.val ≠ j.val := fun e => hne (Fin.ext e)
    rcases h.2 i i.isLt j j.isLt with e | e
    · exact hne' e
    · exact e hij

theorem maskD_lt (i : Fin 22) : maskD i < 1024 := maskOK_spec.1 i

theorem maskD_inj : Function.Injective maskD := maskOK_spec.2

theorem phiM_xor (f a b : ℕ) : phiM f (a ^^^ b) = phiM f a + phiM f b :=
  bsum_xor 10 a b _

theorem phiM_two_pow (f : ℕ) {l : ℕ} (hl : l < 10) :
    phiM f (2 ^ l) = if f.testBit l then 1 else 0 :=
  bsum_two_pow hl _

theorem Phi_jcA (i : Fin 22) {l : ℕ} (hl : l < 10) :
    Phi i (jcA (2 ^ l)) = if (maskD i).testBit l then 1 else 0 := by
  rw [Phi, coord_jcA (two_pow_lt_1024 hl), phiM_two_pow _ hl]

theorem Phi_inj {i j : Fin 22} (h : ∀ x, Phi i x = Phi j x) : i = j := by
  have hbit : ∀ l < 10, (maskD i).testBit l = (maskD j).testBit l := by
    intro l hl
    have hh := h (jcA (2 ^ l))
    rw [Phi_jcA i hl, Phi_jcA j hl] at hh
    by_cases hi : (maskD i).testBit l
    · by_cases hj : (maskD j).testBit l
      · rw [hi, hj]
      · rw [if_pos hi, if_neg hj] at hh
        exact absurd hh (by decide)
    · by_cases hj : (maskD j).testBit l
      · rw [if_neg hi, if_pos hj] at hh
        exact absurd hh.symm (by decide)
      · rw [Bool.eq_false_iff.mpr hi, Bool.eq_false_iff.mpr hj]
  refine maskD_inj (Nat.eq_of_testBit_eq fun l => ?_)
  by_cases hl : l < 10
  · exact hbit l hl
  · have hge : 10 ≤ l := by omega
    have hi : maskD i < 2 ^ l := by
      calc maskD i < 1024 := maskD_lt i
        _ = 2 ^ 10 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hge
    have hj : maskD j < 2 ^ l := by
      calc maskD j < 1024 := maskD_lt j
        _ = 2 ^ 10 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hge
    rw [Nat.testBit_eq_false_of_lt (n := maskD i) (i := l) hi,
      Nat.testBit_eq_false_of_lt (n := maskD j) (i := l) hj]

@[expose] def pullIndex (k : ℕ) (i : Fin 22) : Fin 22 :=
  ⟨(Native.pullList[k]!)[i.val]! % 22, Nat.mod_lt _ (by norm_num)⟩

theorem pullIndex_val (k : ℕ) (hk : k < 3) (i : Fin 22) :
    (pullIndex k i).val = (Native.pullList[k]!)[i.val]! := by
  have h : (Native.pullList[k]!)[i.val]! < 22 := (pullK_spec hk i.isLt).1
  exact Nat.mod_eq_of_lt h

theorem maskD_pullIndex (k : ℕ) (hk : k < 3) (i : Fin 22) :
    maskD (pullIndex k i) = Data.d22[(Native.pullList[k]!)[i.val]!]! := by
  rw [maskD, pullIndex_val k hk i]

theorem phiM_pullIndex (k : ℕ) (hk : k < 3) (i : Fin 22) {l : ℕ} (hl : l < 10) :
    phiM (maskD (pullIndex k i)) (2 ^ l) =
      phiM (maskD i) (Co2Smith.Native.glNJT k (2 ^ l)) := by
  have hp := (pullK_spec hk i.isLt).2 l hl
  rw [maskD_pullIndex k hk i]
  exact hp.2

theorem glNJT_two_pow_lt (k : ℕ) (hk : k < 3) {l : ℕ} (hl : l < 10) :
    Co2Smith.Native.glNJT k (2 ^ l) < 1024 :=
  ((pullK_spec hk (by norm_num : (0 : ℕ) < 22)).2 l hl).1

theorem Phi_pullIndex (k : ℕ) (hk : k < 3) (i : Fin 22) (x : ↥Jc) :
    Phi (pullIndex k i) x = Phi i (qA k x) := by
  have hf : ∀ a b : ↥Jc,
      phiM (maskD (pullIndex k i)) (coord (a * b)) -
          phiM (maskD i) (coord (qA k (a * b))) =
        (phiM (maskD (pullIndex k i)) (coord a) - phiM (maskD i) (coord (qA k a))) +
          (phiM (maskD (pullIndex k i)) (coord b) - phiM (maskD i) (coord (qA k b))) := by
    intro a b
    rw [coord_mul, map_mul, coord_mul, phiM_xor, phiM_xor]
    ring
  have h0 : ∀ l < 10,
      phiM (maskD (pullIndex k i)) (coord (jcA (2 ^ l))) -
          phiM (maskD i) (coord (qA k (jcA (2 ^ l)))) = 0 := by
    intro l hl
    rw [coord_jcA (two_pow_lt_1024 hl), qA_jcA hk, coord_jcA (glNJT_two_pow_lt k hk hl),
      phiM_pullIndex k hk i hl, sub_self]
  have hx := additive_eq_zero (f := fun y => phiM (maskD (pullIndex k i)) (coord y) -
    phiM (maskD i) (coord (qA k y))) hf h0 x
  simp only [Phi]
  exact sub_eq_zero.mp hx

theorem exists_pull_gen (k : ℕ) (hk : k < 3) (i : Fin 22) :
    ∃ j : Fin 22, ∀ x : ↥Jc, Phi j x = Phi i (qA k x) :=
  ⟨pullIndex k i, Phi_pullIndex k hk i⟩

theorem exists_pull {g : MulAut ↥Jc} (hg : g ∈ Qj) :
    ∀ i : Fin 22, ∃ j : Fin 22, ∀ x : ↥Jc, Phi j x = Phi i (g x) :=
  Qj_induction
    (P := fun g => ∀ i : Fin 22, ∃ j : Fin 22, ∀ x : ↥Jc, Phi j x = Phi i (g x))
    (fun i => ⟨i, fun _ => rfl⟩)
    (fun k hk g hg ih i => by
      obtain ⟨j, hj⟩ := exists_pull_gen k hk i
      obtain ⟨l, hl⟩ := ih j
      exact ⟨l, fun x => by rw [hl x, hj (g x), MulAut.mul_apply]⟩) hg

@[expose] noncomputable def sigmaFun (g : Qj) (i : Fin 22) : Fin 22 :=
  Classical.choose (exists_pull g.2 i)

theorem sigmaFun_spec (g : Qj) (i : Fin 22) (x : ↥Jc) :
    Phi (sigmaFun g i) x = Phi i ((g : MulAut ↥Jc) x) :=
  Classical.choose_spec (exists_pull g.2 i) x

theorem sigmaFun_inj (g : Qj) : Function.Injective (sigmaFun g) := by
  intro i j h
  refine Phi_inj fun x => ?_
  obtain ⟨y, rfl⟩ := (g : MulAut ↥Jc).surjective x
  rw [← sigmaFun_spec g i y, ← sigmaFun_spec g j y, h]

@[expose] noncomputable def sigmaEquiv (g : Qj) : Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (sigmaFun g)
    ⟨sigmaFun_inj g, (Finite.injective_iff_surjective).mp (sigmaFun_inj g)⟩

theorem sigmaEquiv_apply (g : Qj) (i : Fin 22) : sigmaEquiv g i = sigmaFun g i := rfl

theorem sigmaFun_mul (g h : Qj) : sigmaFun (g * h) = sigmaFun h ∘ sigmaFun g := by
  funext i
  refine Phi_inj fun x => ?_
  rw [Function.comp_apply, sigmaFun_spec (g * h) i x, sigmaFun_spec h (sigmaFun g i) x,
    sigmaFun_spec g i ((h : MulAut ↥Jc) x)]
  rfl

theorem sigmaEquiv_mul (g h : Qj) : sigmaEquiv (g * h) = sigmaEquiv h * sigmaEquiv g := by
  apply Equiv.ext
  intro i
  rw [sigmaEquiv_apply, Equiv.Perm.mul_apply, sigmaEquiv_apply, sigmaEquiv_apply]
  exact congrFun (sigmaFun_mul g h) i

theorem sigmaFun_one (i : Fin 22) : sigmaFun (1 : Qj) i = i := by
  refine Phi_inj fun x => ?_
  rw [sigmaFun_spec]
  rfl

@[expose] noncomputable def thetaHom : Qj →* ℤˣ where
  toFun g := (sigmaEquiv g).sign
  map_one' := by
    have h : sigmaEquiv 1 = 1 := by
      apply Equiv.ext
      intro i
      rw [sigmaEquiv_apply, Equiv.Perm.one_apply]
      exact sigmaFun_one i
    rw [h, Equiv.Perm.sign_one]
  map_mul' g h := by
    rw [sigmaEquiv_mul, Equiv.Perm.sign_mul, mul_comm]

@[expose] def swapPair (p : List ℕ) : Equiv.Perm (Fin 22) :=
  Equiv.swap ⟨p[0]! % 22, Nat.mod_lt _ (by norm_num)⟩ ⟨p[1]! % 22, Nat.mod_lt _ (by norm_num)⟩

@[expose] def swapsPerm : List (Equiv.Perm (Fin 22)) := Data.swapsA.map swapPair

@[expose] def permA : Equiv.Perm (Fin 22) := swapsPerm.prod

theorem swapsPerm_length : swapsPerm.length = 19 := by
  rw [swapsPerm, List.length_map]
  exact sign_spec.1

theorem getElem!_mem {l : List ℕ} {k : ℕ} (hk : k < l.length) : l[k]! ∈ l := by
  rw [getElem!_pos l k hk]
  exact List.getElem_mem hk

theorem swapsPerm_isSwap : ∀ g ∈ swapsPerm, Equiv.Perm.IsSwap g := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
  obtain ⟨hlen, hlt, hne⟩ := sign_spec.2.1 p hp
  have h0 : p[0]! < 22 := hlt p[0]! (getElem!_mem (by rw [hlen]; omega))
  have h1 : p[1]! < 22 := hlt p[1]! (getElem!_mem (by rw [hlen]; omega))
  refine ⟨_, _, ?_, rfl⟩
  intro heq
  apply hne
  have h2 := congrArg Fin.val heq
  calc p[0]! = p[0]! % 22 := (Nat.mod_eq_of_lt h0).symm
    _ = p[1]! % 22 := h2
    _ = p[1]! := Nat.mod_eq_of_lt h1

theorem sign_permA : permA.sign = -1 := by
  rw [permA, Equiv.Perm.sign_prod_list_swap (l := swapsPerm) swapsPerm_isSwap,
    swapsPerm_length]
  norm_num

theorem sigmaFun_qA_zero (i : Fin 22) :
    sigmaFun ⟨qA 0, qA_mem (by norm_num)⟩ i = pullIndex 0 i := by
  refine Phi_inj fun x => ?_
  rw [sigmaFun_spec, Phi_pullIndex 0 (by norm_num : (0 : ℕ) < 3) i x]

theorem sigmaFun_qA_zero_val (i : Fin 22) :
    (sigmaFun ⟨qA 0, qA_mem (by norm_num)⟩ i).val = (Native.pullList[0]!)[i.val]! := by
  rw [sigmaFun_qA_zero, pullIndex_val 0 (by norm_num : (0 : ℕ) < 3) i]

theorem permA_val (i : Fin 22) :
    (permA i).val = (Native.pullList[0]!)[i.val]! := by
  have h : ∀ i : Fin 22, (permA i).val = (Native.pullList[0]!)[i.val]! := by decide
  exact h i

theorem sigmaEquiv_qA_zero :
    sigmaEquiv ⟨qA 0, qA_mem (by norm_num)⟩ = permA := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [sigmaEquiv_apply]
  exact (sigmaFun_qA_zero_val i).trans (permA_val i).symm

theorem theta_qA_zero : thetaHom ⟨qA 0, qA_mem (by norm_num)⟩ = -1 := by
  show (sigmaEquiv ⟨qA 0, qA_mem (by norm_num)⟩).sign = -1
  rw [sigmaEquiv_qA_zero]
  exact sign_permA

theorem g1w_letters : ∀ k ∈ g1w, k < 3 := by
  intro k hk
  rw [g1w] at hk
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.mem_replicate,
    List.not_mem_nil, or_false, false_or] at hk
  omega

theorem g2w_letters : ∀ k ∈ g2w, k < 3 := by
  intro k hk
  rw [g2w] at hk
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.mem_replicate,
    List.not_mem_nil, or_false, false_or] at hk
  omega

theorem theta_commutator_eq_one (x y : Qj) : thetaHom ⁅x, y⁆ = 1 := by
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

theorem theta_qWord_g1w : thetaHom (⟨qWord g1w, qWord_mem g1w_letters⟩ : Qj) = 1 := by
  have h : (⟨qWord g1w, qWord_mem g1w_letters⟩ : Qj) =
      ⁅(⟨qA 0, qA_mem (by norm_num)⟩ : Qj), (⟨qA 1, qA_mem (by norm_num)⟩ : Qj)⁆ :=
    Subtype.ext qWord_g1w_eq
  rw [h]
  exact theta_commutator_eq_one _ _

theorem theta_qWord_g2w : thetaHom (⟨qWord g2w, qWord_mem g2w_letters⟩ : Qj) = 1 := by
  have h : (⟨qWord g2w, qWord_mem g2w_letters⟩ : Qj) =
      ⁅(⟨qA 0 * qA 0, Qj.mul_mem (qA_mem (by norm_num)) (qA_mem (by norm_num))⟩ : Qj),
        (⟨qA 2, qA_mem (by norm_num)⟩ : Qj)⁆ :=
    Subtype.ext qWord_g2w_eq
  rw [h]
  exact theta_commutator_eq_one _ _

theorem theta_eq_one_of_mem_Dg {y : MulAut ↥Jc} :
    ∀ (hy : y ∈ Dg), ∀ (h : y ∈ Qj), thetaHom ⟨y, h⟩ = 1 := by
  refine Subgroup.closure_induction
    (k := ({qWord g1w, qWord g2w} : Set (MulAut ↥Jc)))
    (p := fun y _ => ∀ (h : y ∈ Qj), thetaHom ⟨y, h⟩ = 1) ?_ ?_ ?_ ?_
  · rintro x (rfl | rfl) h
    · rw [show (⟨qWord g1w, h⟩ : Qj) = ⟨qWord g1w, qWord_mem g1w_letters⟩ from Subtype.ext rfl]
      exact theta_qWord_g1w
    · rw [show (⟨qWord g2w, h⟩ : Qj) = ⟨qWord g2w, qWord_mem g2w_letters⟩ from Subtype.ext rfl]
      exact theta_qWord_g2w
  · intro h
    rw [show (⟨1, h⟩ : Qj) = 1 from Subtype.ext rfl, map_one]
  · intro a b ha hb iha ihb h
    have haQ : a ∈ Qj := Dg_le_Qj ha
    have hbQ : b ∈ Qj := Dg_le_Qj hb
    rw [show (⟨a * b, h⟩ : Qj) = ⟨a, haQ⟩ * ⟨b, hbQ⟩ from Subtype.ext rfl, map_mul,
      iha haQ, ihb hbQ, one_mul]
  · intro a ha iha h
    have haQ : a ∈ Qj := Dg_le_Qj ha
    rw [show (⟨a⁻¹, h⟩ : Qj) = (⟨a, haQ⟩ : Qj)⁻¹ from Subtype.ext rfl, map_inv, iha haQ,
      inv_one]

theorem qA_zero_not_mem_Dg : qA 0 ∉ Dg := by
  intro h
  have h1 := theta_eq_one_of_mem_Dg h (qA_mem (by norm_num))
  rw [theta_qA_zero] at h1
  have h2 : ((-1 : ℤˣ) : ℤ) = 1 := by simpa using congrArg Units.val h1
  norm_num at h2

theorem mem_Dg_or_eq_mul (x : Qj) : x.1 ∈ Dg ∨ ∃ d ∈ Dg, x.1 = d * qA 0 := by
  rcases qD_cases (qD x) with h | h
  · exact Or.inl (Subgroup.mem_subgroupOf.mp (qD_eq_one_iff.mp h))
  · refine Or.inr ⟨(x * (⟨qA 0, qA_mem (by norm_num)⟩ : Qj)⁻¹).1, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mp (qD_eq_one_iff.mp ?_)
      rw [map_mul, map_inv, h]
      exact mul_inv_cancel _
    · show x.1 = (x * (⟨qA 0, qA_mem (by norm_num)⟩ : Qj)⁻¹).1 * qA 0
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group

theorem commutator_Dg_left {d : MulAut ↥Jc} (hd : d ∈ Dg) {y : MulAut ↥Jc} (hy : y ∈ Qj) :
    ⁅d, y⁆ ∈ Dg := by
  rcases mem_Dg_or_eq_mul ⟨y, hy⟩ with hy' | ⟨e, he, rfl⟩
  · rw [commutatorElement_def]
    exact Dg.mul_mem (Dg.mul_mem (Dg.mul_mem hd hy') (Dg.inv_mem hd)) (Dg.inv_mem hy')
  · rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅d, e⁆ ∈ Dg := by
      rw [commutatorElement_def]
      exact Dg.mul_mem (Dg.mul_mem (Dg.mul_mem hd he) (Dg.inv_mem hd)) (Dg.inv_mem he)
    have h2 : ⁅d, qA 0⁆ ∈ Dg := by
      have h3 : ⁅qA 0, d⁆ ∈ Dg := by
        rw [commutatorElement_def]
        exact Dg.mul_mem
          (conj_mem_Dg (qA_mem (k := 0) (by norm_num) : qA 0 ∈ Qj) d hd) (Dg.inv_mem hd)
      rw [← commutatorElement_inv]
      exact Dg.inv_mem h3
    have h4 : e * ⁅d, qA 0⁆ * e⁻¹ ∈ Dg := conj_mem_Dg (Dg_le_Qj he) (⁅d, qA 0⁆) h2
    have h5 : ⁅d, e⁆ * e * ⁅d, qA 0⁆ * e⁻¹ = ⁅d, e⁆ * (e * ⁅d, qA 0⁆ * e⁻¹) := by group
    rw [h5]
    exact Dg.mul_mem h1 h4

theorem commutator_qA_zero_right {y : MulAut ↥Jc} (hy : y ∈ Qj) : ⁅qA 0, y⁆ ∈ Dg := by
  rcases mem_Dg_or_eq_mul ⟨y, hy⟩ with hy' | ⟨e, he, rfl⟩
  · rw [commutatorElement_def]
    exact Dg.mul_mem (conj_mem_Dg (qA_mem (k := 0) (by norm_num) : qA 0 ∈ Qj) y hy')
      (Dg.inv_mem hy')
  · have h1 : ⁅qA 0, e⁆ ∈ Dg := by
      rw [commutatorElement_def]
      exact Dg.mul_mem
        (conj_mem_Dg (qA_mem (k := 0) (by norm_num) : qA 0 ∈ Qj) e he) (Dg.inv_mem he)
    rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_self]
    have heq : ⁅qA 0, e⁆ * e * 1 * e⁻¹ = ⁅qA 0, e⁆ := by group
    rw [heq]
    exact h1

theorem commutator_le_Dg : ⁅Qj, Qj⁆ ≤ Dg := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rcases mem_Dg_or_eq_mul ⟨x, hx⟩ with hx' | ⟨d, hd, rfl⟩
  · exact commutator_Dg_left hx' hy
  · rw [commutatorElement_mul_left_eq_conj_mul]
    refine Dg.mul_mem ?_ (commutator_Dg_left hd hy)
    exact conj_mem_Dg (Dg_le_Qj hd) (⁅qA 0, y⁆) (commutator_qA_zero_right hy)

theorem commutator_Qj_eq : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w} :=
  le_antisymm commutator_le_Dg Dg_le_commutator

theorem qA_one_mem_commutator : qA 1 ∈ ⁅Qj, Qj⁆ := by
  rw [commutator_Qj_eq]
  exact qA_one_mem_Dg

theorem qA_zero_mul_self_mem_commutator : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆ := by
  rw [commutator_Qj_eq]
  exact qA_zero_sq_mem_Dg

theorem card_Dg : Nat.card ↥Dg = 443520 := by
  have hrel : Dg.relIndex Qj = 2 := by
    show (Dg.subgroupOf Qj).index = 2
    rw [Subgroup.index_eq_card]
    exact quotient_card qA_zero_not_mem_Dg
  have h := Subgroup.relIndex_mul_card (H := Dg) (K := Qj)
  have hinf : Dg ⊓ Qj = Dg := inf_eq_left.mpr Dg_le_Qj
  rw [hrel, hinf, card_Qj] at h
  omega

theorem card_commutator_Qj : Nat.card ↥⁅Qj, Qj⁆ = 443520 := by
  rw [commutator_Qj_eq]
  exact card_Dg

end CFSG.Sporadic.Co2Jc
