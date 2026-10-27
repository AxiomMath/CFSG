module

public import CFSG.Quasithin.Vol2.Asc94.L52Hstruct

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

@[expose] def patSubT (S : Fin 5 → Fin 5 → Prop) (hlt : ∀ i j, S i j → i < j)
    (htr : ∀ i k j, S i k → S k j → S i j) : Subgroup Hc where
  carrier := {x | SuppIn S (cm x - 1)}
  mul_mem' := fun {x y} hx hy => by
    show SuppIn S (cm (x * y) - 1)
    have e : cm (x * y) - 1 = (cm x - 1) + (cm y - 1) + (cm x - 1) * (cm y - 1) := by
      rw [cm_mul]
      noncomm_ring
    intro i j hij
    rw [e, Matrix.add_apply, Matrix.add_apply, hx i j hij, hy i j hij, zero_add, zero_add,
      Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : S i k
    · by_cases hkj : S k j
      · exact absurd (htr i k j hik hkj) hij
      · rw [hy k j hkj, mul_zero]
    · rw [hx i k hik, zero_mul]
  one_mem' := by
    show SuppIn S (cm 1 - 1)
    rw [cm_one, sub_self]
    intro i j _
    simp
  inv_mem' := fun {x} hx => by
    classical
    have hpow : ∀ n : ℕ, SuppIn S (cm (x ^ n) - 1) := by
      intro n
      induction n with
      | zero =>
        intro i j _
        simp [cm_one]
      | succ n ih =>
        have e : cm (x ^ (n + 1)) - 1 = (cm (x ^ n) - 1) + (cm x - 1) +
            (cm (x ^ n) - 1) * (cm x - 1) := by
          rw [pow_succ, cm_mul]
          noncomm_ring
        intro i j hij
        rw [e, Matrix.add_apply, Matrix.add_apply, ih i j hij, hx i j hij, add_zero, zero_add,
          Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hik : S i k
        · by_cases hkj : S k j
          · exact absurd (htr i k j hik hkj) hij
          · rw [hx k j hkj, mul_zero]
        · rw [ih i k hik, zero_mul]
    have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    show SuppIn S (cm x⁻¹ - 1)
    rw [hinv]
    exact hpow _

theorem mem_patSubT {S : Fin 5 → Fin 5 → Prop} {hlt : ∀ i j, S i j → i < j}
    {htr : ∀ i k j, S i k → S k j → S i j} {x : Hc} :
    x ∈ patSubT S hlt htr ↔ SuppIn S (cm x - 1) := Iff.rfl

theorem patSub_eq_patSubT {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    (hlt : ∀ i j, S i j → i < j) :
    patSub S hS = patSubT S hlt (fun i k j h1 h2 => (hS i k j h1 h2).elim) := by
  ext x
  rfl

section Card

open Classical

variable {S : Fin 5 → Fin 5 → Prop} (hlt : ∀ i j, S i j → i < j)
  (htr : ∀ i k j, S i k → S k j → S i j)

@[expose] noncomputable def patN (f : {p : Fin 5 × Fin 5 // S p.1 p.2} → ZMod 2) : Mt :=
  Matrix.of fun i j => if h : S i j then f ⟨(i, j), h⟩ else 0

include hlt in
theorem patN_up (f : {p : Fin 5 × Fin 5 // S p.1 p.2} → ZMod 2) :
    ∀ i j : Fin 5, j ≤ i → patN f i j = 0 := by
  intro i j hji
  simp only [patN, Matrix.of_apply]
  split_ifs with h
  · exact absurd (hlt i j h) (not_lt.mpr hji)
  · rfl

include hlt in
theorem patN_c0 (f : {p : Fin 5 × Fin 5 // S p.1 p.2} → ZMod 2) :
    ∀ i : Fin 5, patN f i 0 = 0 := by
  intro i
  simp only [patN, Matrix.of_apply]
  split_ifs with h
  · exact absurd (hlt i 0 h) (not_lt_zero' i)
  · rfl

include hlt in
theorem patN_r4 (f : {p : Fin 5 × Fin 5 // S p.1 p.2} → ZMod 2) :
    ∀ j : Fin 5, patN f 4 j = 0 := by
  intro j
  simp only [patN, Matrix.of_apply]
  split_ifs with h
  · exact absurd (hlt 4 j h) (not_gt_four j)
  · rfl

theorem patN_supp (f : {p : Fin 5 × Fin 5 // S p.1 p.2} → ZMod 2) : SuppIn S (patN f) := by
  intro i j hij
  simp [patN, hij]

@[expose] noncomputable def patElt (f : {p : Fin 5 × Fin 5 // S p.1 p.2} → ZMod 2) : ↥(patSubT S hlt htr) :=
  ⟨unipH (patN f) (patN_up hlt f) (patN_c0 hlt f) (patN_r4 hlt f), by
    show SuppIn S (cm (unipH (patN f) (patN_up hlt f) (patN_c0 hlt f) (patN_r4 hlt f)) - 1)
    rw [cm_unipH]
    have : (1 + patN f - 1 : Mt) = patN f := by abel
    rw [this]
    exact patN_supp f⟩

theorem cm_patElt (f : {p : Fin 5 × Fin 5 // S p.1 p.2} → ZMod 2) :
    cm (patElt hlt htr f).1 = 1 + patN f := rfl

theorem patElt_bijective : Function.Bijective (patElt hlt htr) := by
  constructor
  · intro f g hfg
    have h1 : (1 + patN f : Mt) = 1 + patN g := by
      rw [← cm_patElt hlt htr f, ← cm_patElt hlt htr g]
      exact congrArg (fun x => cm x.1) hfg
    have h2 := add_left_cancel h1
    funext p
    have := congrFun (congrFun h2 p.1.1) p.1.2
    simp only [patN, Matrix.of_apply, dif_pos p.2] at this
    exact this
  · rintro ⟨x, hx⟩
    set f : {p : Fin 5 × Fin 5 // S p.1 p.2} → ZMod 2 := fun p => cm x p.1.1 p.1.2 with hf
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    show (1 + patN f : Mt) = cm x
    ext i j
    by_cases hij : S i j
    · have hne : i ≠ j := ne_of_lt (hlt i j hij)
      simp [patN, hij, hf, Matrix.one_apply, hne]
    · have h0 := hx i j hij
      rw [Matrix.sub_apply] at h0
      have h1 := sub_eq_zero.1 h0
      simp [patN, hij, h1]

theorem card_patSubT :
    Nat.card (patSubT S hlt htr) = 2 ^ Nat.card {p : Fin 5 × Fin 5 // S p.1 p.2} := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (patElt_bijective hlt htr))]
  have : Finite {p : Fin 5 × Fin 5 // S p.1 p.2} := inferInstance
  rw [Nat.card_fun, Nat.card_zmod]

end Card

abbrev SA2 (i j : Fin 5) : Prop := i.val ≤ 2 ∧ 3 ≤ j.val

abbrev SU (i j : Fin 5) : Prop := i < j

theorem hSA2 : ∀ i k j, SA2 i k → SA2 k j → False := by
  intro i k j h1 h2
  have := h1.2
  have := h2.1
  omega

theorem lt_S1 : ∀ i j, S1 i j → i < j := by decide

theorem lt_S2 : ∀ i j, S2 i j → i < j := by decide

theorem lt_SA : ∀ i j, SA i j → i < j := by decide

theorem lt_SA2 : ∀ i j, SA2 i j → i < j := by decide

theorem trans_SU : ∀ i k j, SU i k → SU k j → SU i j := fun _ _ _ h1 h2 => lt_trans h1 h2

@[expose] def A2 : Subgroup Hc := patSub SA2 hSA2

@[expose] def Tm : Subgroup Hc := patSubT SU (fun _ _ h => h) trans_SU

@[expose] def Jm : Subgroup Hc := A1 ⊔ A2

theorem isElemAbelian_A2 : CFSG.Open.IsElemAbelian 2 A2 := isElemAbelian_patSub hSA2

theorem mem_A2 {x : Hc} : x ∈ A2 ↔ SuppIn SA2 (cm x - 1) := Iff.rfl

theorem mem_Tm {x : Hc} : x ∈ Tm ↔ SuppIn SU (cm x - 1) := Iff.rfl

theorem patSub_card {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    (hlt : ∀ i j, S i j → i < j) :
    Nat.card (patSub S hS) = 2 ^ Nat.card {p : Fin 5 × Fin 5 // S p.1 p.2} := by
  rw [patSub_eq_patSubT hS hlt]
  exact card_patSubT hlt _

theorem card_A1 : Nat.card A1 = 2 ^ 6 := by
  have h := patSub_card hSA lt_SA
  rw [Nat.card_eq_fintype_card (α := {p : Fin 5 × Fin 5 // SA p.1 p.2})] at h
  have h6 : Fintype.card {p : Fin 5 × Fin 5 // SA p.1 p.2} = 6 := by decide
  rw [h6] at h
  exact h

theorem card_A2 : Nat.card A2 = 2 ^ 6 := by
  have h := patSub_card hSA2 lt_SA2
  rw [Nat.card_eq_fintype_card (α := {p : Fin 5 × Fin 5 // SA2 p.1 p.2})] at h
  have h6 : Fintype.card {p : Fin 5 × Fin 5 // SA2 p.1 p.2} = 6 := by decide
  rw [h6] at h
  exact h

theorem card_Tm : Nat.card Tm = 2 ^ 10 := by
  have h := card_patSubT (S := SU) (fun _ _ h => h) trans_SU
  rw [Nat.card_eq_fintype_card (α := {p : Fin 5 × Fin 5 // SU p.1 p.2})] at h
  have h10 : Fintype.card {p : Fin 5 × Fin 5 // SU p.1 p.2} = 10 := by decide
  rw [h10] at h
  exact h

theorem patSub_inf {S₁ S₂ : Fin 5 → Fin 5 → Prop} (h₁ : ∀ i k j, S₁ i k → S₁ k j → False)
    (h₂ : ∀ i k j, S₂ i k → S₂ k j → False) :
    patSub S₁ h₁ ⊓ patSub S₂ h₂ =
      patSub (fun i j => S₁ i j ∧ S₂ i j) (fun i k j a b => h₁ i k j a.1 b.1) := by
  ext x
  simp only [Subgroup.mem_inf, mem_patSub, SuppIn]
  constructor
  · rintro ⟨hx1, hx2⟩ i j hij
    by_cases h : S₁ i j
    · exact hx2 i j (fun h2 => hij ⟨h, h2⟩)
    · exact hx1 i j h
  · intro hx
    refine ⟨fun i j hij => hx i j (fun h => hij h.1), fun i j hij => hx i j (fun h => hij h.2)⟩

theorem card_patSub_inf {S₁ S₂ : Fin 5 → Fin 5 → Prop}
    (h₁ : ∀ i k j, S₁ i k → S₁ k j → False) (h₂ : ∀ i k j, S₂ i k → S₂ k j → False)
    (hlt : ∀ i j, S₁ i j → i < j) :
    Nat.card ↥(patSub S₁ h₁ ⊓ patSub S₂ h₂) =
      2 ^ Nat.card {p : Fin 5 × Fin 5 // S₁ p.1 p.2 ∧ S₂ p.1 p.2} := by
  rw [patSub_inf h₁ h₂]
  exact patSub_card (fun i k j a b => h₁ i k j a.1 b.1) (fun i j h => hlt i j h.1)

theorem card_A1_inf_A2 : Nat.card ↥(A1 ⊓ A2) = 2 ^ 4 := by
  have h := card_patSub_inf hSA hSA2 lt_SA
  rw [Nat.card_eq_fintype_card (α := {p : Fin 5 × Fin 5 // SA p.1 p.2 ∧ SA2 p.1 p.2})] at h
  have h4 : Fintype.card {p : Fin 5 × Fin 5 // SA p.1 p.2 ∧ SA2 p.1 p.2} = 4 := by decide
  rw [h4] at h
  exact h

theorem card_A1_inf_U1 : Nat.card ↥(A1 ⊓ U1) = 2 ^ 3 := by
  have h := card_patSub_inf hSA hS1 lt_SA
  rw [Nat.card_eq_fintype_card (α := {p : Fin 5 × Fin 5 // SA p.1 p.2 ∧ S1 p.1 p.2})] at h
  have h4 : Fintype.card {p : Fin 5 × Fin 5 // SA p.1 p.2 ∧ S1 p.1 p.2} = 3 := by decide
  rw [h4] at h
  exact h

theorem card_A2_inf_U1 : Nat.card ↥(A2 ⊓ U1) = 2 ^ 2 := by
  have h := card_patSub_inf hSA2 hS1 lt_SA2
  rw [Nat.card_eq_fintype_card (α := {p : Fin 5 × Fin 5 // SA2 p.1 p.2 ∧ S1 p.1 p.2})] at h
  have h4 : Fintype.card {p : Fin 5 × Fin 5 // SA2 p.1 p.2 ∧ S1 p.1 p.2} = 2 := by decide
  rw [h4] at h
  exact h

theorem patSub_le_Tm {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    (hlt : ∀ i j, S i j → i < j) : patSub S hS ≤ Tm := by
  intro x hx
  rw [mem_patSub] at hx
  rw [mem_Tm]
  intro i j hij
  exact hx i j (fun h => hij (hlt i j h))

theorem U1_le_Tm : U1 ≤ Tm := patSub_le_Tm hS1 lt_S1
theorem U2_le_Tm : U2 ≤ Tm := patSub_le_Tm hS2 lt_S2
theorem A1_le_Tm : A1 ≤ Tm := patSub_le_Tm hSA lt_SA
theorem A2_le_Tm : A2 ≤ Tm := patSub_le_Tm hSA2 lt_SA2
theorem Tm_entry_zero {t : Hc} (ht : t ∈ Tm) {i k : Fin 5} (h : k < i) : cm t i k = 0 := by
  have h1 := (mem_Tm.1 ht) i k (fun h' => absurd h' (not_lt.2 h.le))
  rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt h)] at h1
  exact sub_eq_zero.1 h1

theorem conj_mem_patSub {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    (hcl : ∀ i j i' j', S i j → i' ≤ i → j ≤ j' → S i' j') {t a : Hc} (ht : t ∈ Tm)
    (ha : a ∈ patSub S hS) : t * a * t⁻¹ ∈ patSub S hS := by
  have hti : t⁻¹ ∈ Tm := Tm.inv_mem ht
  rw [mem_patSub] at ha ⊢
  have e : cm (t * a * t⁻¹) - 1 = cm t * (cm a - 1) * cm t⁻¹ := by
    have h1 : cm t * cm t⁻¹ = 1 := cm_mul_inv t
    have h2 : cm t * (cm a - 1) * cm t⁻¹ = cm t * cm a * cm t⁻¹ - cm t * cm t⁻¹ := by
      noncomm_ring
    rw [h2, h1, cm_mul, cm_mul]
  intro i j hij
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hlm : S l m
  · by_cases hil : i ≤ l
    · by_cases hmj : m ≤ j
      · exact absurd (hcl l m i j hlm hil hmj) hij
      · rw [Tm_entry_zero hti (not_le.1 hmj)]
        simp
    · rw [Tm_entry_zero ht (not_le.1 hil)]
      simp
  · rw [ha l m hlm]
    simp

theorem A1_conj_Tm {t a : Hc} (ht : t ∈ Tm) (ha : a ∈ A1) : t * a * t⁻¹ ∈ A1 :=
  conj_mem_patSub hSA (by decide) ht ha

theorem A2_conj_Tm {t a : Hc} (ht : t ∈ Tm) (ha : a ∈ A2) : t * a * t⁻¹ ∈ A2 :=
  conj_mem_patSub hSA2 (by decide) ht ha

theorem unipS_mem_Tm (i j : Fin 5) (hij : i < j) (c : ZMod 2) : unipS i j hij c ∈ Tm := by
  rw [mem_Tm]
  have e : cm (unipS i j hij c) - 1 = Matrix.single i j c := by
    rw [cm_unipS]
    abel
  rw [e]
  intro a b hab
  rw [Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd hij hab
  · rfl

theorem comm_unipS_entries {x : Hc} {i j : Fin 5} (hij : i < j)
    (h : x * unipS i j hij 1 = unipS i j hij 1 * x) (a b : Fin 5) :
    (if b = j then cm x a i else 0) = (if a = i then cm x j b else 0) := by
  have h1 := congrArg cm h
  rw [cm_mul, cm_mul, cm_unipS] at h1
  have h2 := congrFun (congrFun h1 a) b
  rw [mul_add_single_apply, add_single_mul_apply] at h2
  have h3 := add_left_cancel h2
  simpa using h3

theorem center_Tm {x : Hc} (hx : x ∈ Tm) (hc : ∀ y ∈ Tm, x * y = y * x) : x = 1 ∨ x = zt := by
  have key : ∀ (i j : Fin 5) (hij : i < j) (a b : Fin 5),
      (if b = j then cm x a i else 0) = (if a = i then cm x j b else 0) := fun i j hij a b =>
    comm_unipS_entries hij (hc _ (unipS_mem_Tm i j hij 1)) a b
  have k0 := fun a b => key 0 1 (by decide) a b
  have k1 := fun a b => key 1 2 (by decide) a b
  have k2 := fun a b => key 2 3 (by decide) a b
  have k3 := fun a b => key 3 4 (by decide) a b
  have d00 := cm_00 x
  have r1 : ∀ b, cm x 1 b = if b = 1 then cm x 0 0 else 0 := fun b => by
    have := k0 0 b
    simpa using this.symm
  have r2 : ∀ b, cm x 2 b = if b = 2 then cm x 1 1 else 0 := fun b => by
    have := k1 1 b
    simpa using this.symm
  have r3 : ∀ b, cm x 3 b = if b = 3 then cm x 2 2 else 0 := fun b => by
    have := k2 2 b
    simpa using this.symm
  have c1 : ∀ a, cm x a 1 = if a = 1 then cm x 2 2 else 0 := fun a => by
    have := k1 a 2
    simpa using this
  have c2 : ∀ a, cm x a 2 = if a = 2 then cm x 3 3 else 0 := fun a => by
    have := k2 a 3
    simpa using this
  have c3 : ∀ a, cm x a 3 = if a = 3 then cm x 4 4 else 0 := fun a => by
    have := k3 a 4
    simpa using this
  have e11 : cm x 1 1 = 1 := by rw [r1 1]; simp [d00]
  have e22 : cm x 2 2 = 1 := by rw [r2 2]; simp [e11]
  have e33 : cm x 3 3 = 1 := by rw [r3 3]; simp [e22]
  have hxe : cm x = 1 + Matrix.single 0 4 (cm x 0 4) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.one_apply, Matrix.single_apply, e11, e22, e33, d00, cm_44, cm_col0 x,
        cm_row4 x, r1, r2, r3, c1, c2, c3]
  exact eq_one_or_zt x _ hxe

theorem card_Hc : Nat.card Hc = 21504 := by
  have h1 := Subgroup.card_mul_index Qh
  have h2 : Qh.index = Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
    show piHom.ker.index = _
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 piHom_surjective, Subgroup.card_top]
  rw [← h1, card_Qh, h2, card_GL3]

theorem zt_mem_A1 : zt ∈ A1 := by
  rw [zt_eq_unipS]
  exact unipS_mem_patSub hSA _ 1 ⟨by decide, by decide⟩

theorem zt_mem_A2 : zt ∈ A2 := by
  rw [zt_eq_unipS]
  exact unipS_mem_patSub hSA2 _ 1 ⟨by decide, by decide⟩

@[expose] def mkH (M : Mt) (hdet : M.det = 1) (hc : ∀ i : Fin 5, M i 0 = (1 : Mt) i 0)
    (hr : ∀ j : Fin 5, M 4 j = (1 : Mt) 4 j) : Hc :=
  ⟨⟨M, hdet⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (tt_comm_of M hc hr))⟩

theorem cm_mkH (M : Mt) (hdet : M.det = 1) (hc : ∀ i : Fin 5, M i 0 = (1 : Mt) i 0)
    (hr : ∀ j : Fin 5, M 4 j = (1 : Mt) 4 j) : cm (mkH M hdet hc hr) = M := rfl

end CFSG.Quasithin.A94.L52
