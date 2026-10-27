module

public import CFSG.Sporadic.Co2Smith.GlDataRootFacts
public import CFSG.Sporadic.Co2Smith.GlDataF0Check
public import CFSG.Sporadic.Co2Smith.QEnum
public import CFSG.Sporadic.Co2Smith.SmithCo2

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def hK (k : ℕ) : K :=
  if k == 1 then δ1hK else if k == 2 then δ0hK * δ1hK
  else if k == 4 then δ1hK * w1K else δ0hK * δ1hK * w1K

@[expose] noncomputable def RK (k : ℕ) : Subgroup K :=
  Qsub.map (MulAut.conj (hK k)).toMonoidHom

@[expose] noncomputable def F0c (k : ℕ) : Subgroup K :=
  Cz ⊓ RK k

theorem hK_val (k : ℕ) :
    (hK k).val.val = rowsMatrix 22 (Native.glHRows k) := by
  unfold hK Native.glHRows
  split_ifs
  · exact δ1hK_val
  · rw [val_val_mul, δ0hK_val, δ1hK_val, rowsMatrix_mulRows]
  · rw [val_val_mul, δ1hK_val, w1K_val, rowsMatrix_mulRows]
  · rw [val_mul3 δ0hK_val δ1hK_val w1K_val]

theorem glF0k_spec {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) :
    Native.validM (Native.subId Native.glZ) = true ∧
    ((List.range 512).filter fun e => Native.commRows
      (Native.glF0Conj (Native.glHRows k) (Native.glFrameConjRows k) e) Native.glZ).length =
        128 ∧
    ((List.range 512).filter fun e => Native.commRows
        (Native.glF0Conj (Native.glHRows k) (Native.glFrameConjRows k) e) Native.glZ &&
      Native.glFixZ (Native.glF0Conj (Native.glHRows k) (Native.glFrameConjRows k) e)).length =
        4 ∧
    (∀ e < 512, Native.glF0Valid
      (Native.glF0Conj (Native.glHRows k) (Native.glFrameConjRows k) e) = true) ∧
    mulRows 22 (Native.glHRows k) (Native.glFrameConjRows k) = idRows 22 ∧
    (∀ t ∈ [1, 2, 3], Native.commRows (mulRows 22 (mulRows 22 (Native.glFrameConjRows k)
        (Native.glRootRows (Native.glF0Root k) t)) (Native.glHRows k)) Native.glZ = true ∧
      Native.glFixZ (mulRows 22 (mulRows 22 (Native.glFrameConjRows k)
        (Native.glRootRows (Native.glF0Root k) t)) (Native.glHRows k)) = true) ∧
    ∀ s ∈ [0, 1, 2, 3], Native.validM (Native.glRootRows (Native.glF0Root k) s) = true ∧
      ∀ t ∈ [0, 1, 2, 3], s = t ∨
        Native.glRootRows (Native.glF0Root k) s ≠ Native.glRootRows (Native.glF0Root k) t := by
  have h := glF0_check
  simp only [Native.glF0OK, Bool.and_eq_true, List.all_eq_true] at h
  have hk' := h.2 k hk
  simp only [Native.glF0kOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at hk'
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hk'
  exact ⟨h.1, h1, h2, h3, h4, h5, h6⟩

theorem commRows_iff {g h : K} {X Y : Array ℕ} (hg : g.val.val = rowsMatrix 22 X)
    (hh : h.val.val = rowsMatrix 22 Y) (h1 : Native.validM (mulRows 22 X Y) = true)
    (h2 : Native.validM (mulRows 22 Y X) = true) :
    Native.commRows X Y = true ↔ g * h = h * g := by
  refine ⟨comm_of_commRows hg hh, fun hc => ?_⟩
  have e : rowsMatrix 22 (mulRows 22 X Y) = rowsMatrix 22 (mulRows 22 Y X) := by
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hg, ← hh, ← val_val_mul, ← val_val_mul, hc]
  rw [Native.commRows, beq_iff_eq]
  exact eq_of_rowsMatrix_eq h1 h2 e

theorem subId_glZ_val :
    rowsMatrix 22 (Native.subId Native.glZ) = z0.val.val - 1 := by
  rw [rowsMatrix_subId, ← z0_val']

theorem fixZ_iff {g : K} {X : Array ℕ}
    (hg : g.val.val = rowsMatrix 22 X)
    (h1 : Native.validM (mulRows 22 X (Native.subId Native.glZ)) = true)
    (h2 : Native.validM (Native.subId Native.glZ) = true) :
    Native.glFixZ X = true ↔ g ∈ Zfix := by
  have key : g.val.val * (z0.val.val - 1) = z0.val.val - 1 ↔ Native.glFixZ X = true := by
    rw [Native.glFixZ, beq_iff_eq]
    constructor
    · intro h
      apply eq_of_rowsMatrix_eq h1 h2
      rw [rowsMatrix_mulRows, ← hg, subId_glZ_val, h]
    · intro h
      have := congrArg (rowsMatrix 22) h
      rwa [rowsMatrix_mulRows, ← hg, subId_glZ_val] at this
  rw [← key, mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    obtain ⟨u, rfl⟩ := hy
    show g.val.val *ᵥ ((z0.val.val - 1) *ᵥ u) = (z0.val.val - 1) *ᵥ u
    rw [Matrix.mulVec_mulVec, h]
  · intro h
    refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    exact h _ ⟨u, rfl⟩

theorem mem_Cz_iff_rows {g : K} {X : Array ℕ}
    (hg : g.val.val = rowsMatrix 22 X) (hv : Native.glF0Valid X = true) :
    g ∈ Cz ↔ Native.commRows X Native.glZ = true := by
  simp only [Native.glF0Valid, Bool.and_eq_true] at hv
  rw [commRows_iff hg z0_val' hv.1.1 hv.1.2]
  exact ⟨comm_of_mem_Cz, mem_Cz_of_comm⟩

theorem mem_Qsub_iff_rows
    {g : K} {X : Array ℕ}
    (hg : g.val.val = rowsMatrix 22 X) (hv : Native.glF0Valid X = true)
    (h2 : Native.validM (Native.subId Native.glZ) = true) :
    g ∈ Qsub ↔ Native.commRows X Native.glZ = true ∧ Native.glFixZ X = true := by
  rw [← mem_Cz_iff_rows hg hv]
  simp only [Native.glF0Valid, Bool.and_eq_true] at hv
  rw [← Zfix_inf_Cz, Subgroup.mem_inf, fixZ_iff hg hv.2 h2]
  exact And.comm

theorem hK_mul_frameConjK
    {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) : hK k * frameConjK k = 1 := by
  apply eq_of_val_eq
  rw [val_val_mul, hK_val, frameConjK_val, ← rowsMatrix_mulRows, (glF0k_spec hk).2.2.2.2.1,
    rowsMatrix_idRows]
  rfl

theorem frameConjK_eq_inv
    {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) : frameConjK k = (hK k)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (hK_mul_frameConjK hk)).symm

theorem conjQ_val {k : ℕ}
    (hk : k ∈ [1, 2, 4, 5]) {e : ℕ} (he : e < 512) :
    (hK k * qElt e * (hK k)⁻¹).val.val =
      rowsMatrix 22 (Native.glF0Conj (Native.glHRows k) (Native.glFrameConjRows k) e) := by
  rw [← frameConjK_eq_inv hk, val_mul3 (hK_val k) (qElt_val he) (frameConjK_val k)]
  rfl

theorem mem_RK_iff {k : ℕ}
    {g : K} : g ∈ RK k ↔ ∃ e < 512, hK k * qElt e * (hK k)⁻¹ = g := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨e, he, rfl⟩ := exists_qElt hq
    exact ⟨e, he, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨qElt e, qElt_mem e, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

theorem card_inf_RK
    {S : Subgroup K} {k : ℕ} {P : ℕ → Bool}
    (hP : ∀ e < 512, P e = true ↔ hK k * qElt e * (hK k)⁻¹ ∈ S) :
    Nat.card (S ⊓ RK k : Subgroup K) = ((List.range 512).filter P).length := by
  have hset : ((S ⊓ RK k : Subgroup K) : Set K) =
      (fun e => hK k * qElt e * (hK k)⁻¹) '' (((List.range 512).filter P).toFinset : Set ℕ) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_image, List.mem_toFinset,
      List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hgS, hgR⟩
      obtain ⟨e, he, rfl⟩ := mem_RK_iff.1 hgR
      exact ⟨e, ⟨he, (hP e he).2 hgS⟩, rfl⟩
    · rintro ⟨e, ⟨he, hPe⟩, rfl⟩
      exact ⟨(hP e he).1 hPe, mem_RK_iff.2 ⟨e, he, rfl⟩⟩
  have hinj : Set.InjOn (fun e => hK k * qElt e * (hK k)⁻¹)
      (((List.range 512).filter P).toFinset : Set ℕ) := by
    intro e he e' he' h
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at he he'
    exact qElt_injOn he.1 he'.1 (mul_left_cancel (mul_right_cancel h))
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, hinj.ncard_image,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup (List.nodup_range.filter _)]

theorem card_F0c
    {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) :
    Nat.card (F0c k) = 128 := by
  rw [F0c, card_inf_RK fun e he =>
    (mem_Cz_iff_rows (conjQ_val hk he) ((glF0k_spec hk).2.2.2.1 e he)).symm]
  exact (glF0k_spec hk).2.1

theorem card_Qsub_inf_RK
    {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) :
    Nat.card (Qsub ⊓ RK k : Subgroup K) = 4 := by
  rw [card_inf_RK (P := fun e => Native.commRows
      (Native.glF0Conj (Native.glHRows k) (Native.glFrameConjRows k) e) Native.glZ &&
    Native.glFixZ (Native.glF0Conj (Native.glHRows k) (Native.glFrameConjRows k) e))
    fun e he => by
      rw [Bool.and_eq_true]
      exact (mem_Qsub_iff_rows (conjQ_val hk he) ((glF0k_spec hk).2.2.2.1 e he)
        (glF0k_spec hk).1).symm]
  exact (glF0k_spec hk).2.2.1

theorem xLongK_eq_conj
    {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) :
    xLongK k = hK k * z0 * (hK k)⁻¹ := by
  have hk6 : k < 6 := by simp at hk; omega
  have h := frameConjK_conj hk6
  rw [frameConjK_eq_inv hk] at h
  calc xLongK k = hK k * ((hK k)⁻¹ * xLongK k) := by group
    _ = hK k * (z0 * (hK k)⁻¹) := by rw [h]
    _ = hK k * z0 * (hK k)⁻¹ := by group

theorem xLongK_zero : xLongK 0 = z0 := by
  rw [← x16K_eq]
  rfl

theorem xLongK_mem_F0c
    {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) : xLongK k ∈ F0c k := by
  have hk6 : k < 6 := by simp at hk; omega
  have hk3 : k % 3 ≠ 0 % 3 := by simp at hk; omega
  refine ⟨mem_Cz_of_comm ?_, ⟨z0, Subgroup.subset_closure (Set.mem_insert _ _), ?_⟩⟩
  · rw [← xLongK_zero]
    exact xLongK_comm hk6 (by norm_num) hk3
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, xLongK_eq_conj hk]

theorem conj_mem_F0c
    {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) {g : K} (hg : g ∈ Cz)
    (hgx : g * xLongK k = xLongK k * g) {y : K} (hy : y ∈ F0c k) : g * y * g⁻¹ ∈ F0c k := by
  obtain ⟨hyC, q, hq, rfl⟩ := hy
  refine ⟨Cz.mul_mem (Cz.mul_mem hg hyC) (Cz.inv_mem hg), ?_⟩
  set c := (hK k)⁻¹ * g * hK k with hc
  have hcz : c ∈ Cz := by
    apply mem_Cz_of_comm
    rw [xLongK_eq_conj hk] at hgx
    calc c * z0 = (hK k)⁻¹ * (g * (hK k * z0 * (hK k)⁻¹)) * hK k := by rw [hc]; group
      _ = (hK k)⁻¹ * (hK k * z0 * (hK k)⁻¹ * g) * hK k := by rw [hgx]
      _ = z0 * c := by rw [hc]; group
  have hcq : c * q * c⁻¹ ∈ Qsub := by
    have := (Qsub_subgroupOf_normal).conj_mem ⟨q, Qsub_le_Cz hq⟩ hq ⟨c, hcz⟩
    exact this
  refine ⟨c * q * c⁻¹, hcq, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc]
  group

theorem glLetterWords_hWords : ∀ j < 8, Native.glLetterWords[j + 1]! = Native.hWords[j]! := by
  decide +kernel

theorem glElt_mem_Qsub {j : ℕ} (hj : j < 9) : glElt j ∈ Qsub := by
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · have h : glElt 0 * 1 = z0 := x16K_eq
    rw [mul_one] at h
    rw [h]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h : glElt (i + 1) = hE ⟨i, by omega⟩ := by
      change mWord Native.glLetterWords[i + 1]! = mWord Native.hWords[i]!
      rw [glLetterWords_hWords i (by omega)]
    rw [h]
    exact hE_mem_Qsub _

theorem glPosNF_lt9 : ∀ i < 4, ∀ t < 4, ∀ k ∈ (Native.glPosNF[i]!)[t]!, k < 9 := by
  decide

theorem xRootK_eq_glE {r t : ℕ} (hr : r < 4) (ht : t ≠ 0) :
    xRootK r t = glE (Native.glPosNF[r]!)[t]! := by
  have ht' : (t == 0) = false := by simpa using ht
  have hr6 : r < 6 := by omega
  simp only [xRootK, xPosK, ht', hr6, hr, ite_true, Bool.false_eq_true, ite_false]

theorem xRootK_mem_Qsub {r t : ℕ} (hr : r < 4) (ht : t < 4) :
    xRootK r t ∈ Qsub := by
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · exact Qsub.one_mem
  · rw [xRootK_eq_glE hr (by omega)]
    exact glE_mem_of_letters (L := List.range 9) (fun j hj => glElt_mem_Qsub
      (List.mem_range.1 hj)) fun j hj => List.mem_range.2 (glPosNF_lt9 r hr t ht j hj)

theorem glF0Root_lt (k : ℕ) : Native.glF0Root k < 4 := by
  unfold Native.glF0Root
  split_ifs <;> norm_num

theorem xRootK_mem_RK
    {k t : ℕ} (hk : k ∈ [1, 2, 4, 5]) (ht : t < 4) :
    xRootK (Native.glF0Root k) t ∈ RK k := by
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · exact (RK k).one_mem
  have ht3 : t ∈ [1, 2, 3] := by simp; omega
  have hq : (hK k)⁻¹ * xRootK (Native.glF0Root k) t * hK k ∈ Qsub := by
    have hv : ((hK k)⁻¹ * xRootK (Native.glF0Root k) t * hK k).val.val =
        rowsMatrix 22 (mulRows 22 (mulRows 22 (Native.glFrameConjRows k)
          (Native.glRootRows (Native.glF0Root k) t)) (Native.glHRows k)) := by
      rw [← frameConjK_eq_inv hk, val_mul3 (frameConjK_val k) (xRootK_val _ _) (hK_val k)]
    rw [← Zfix_inf_Cz]
    obtain ⟨h1, h2⟩ := (glF0k_spec hk).2.2.2.2.2.1 t ht3
    refine Subgroup.mem_inf.2 ⟨?_, mem_Cz_of_comm (comm_of_commRows hv z0_val' h1)⟩
    rw [mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    have hm : ((hK k)⁻¹ * xRootK (Native.glF0Root k) t * hK k).val.val *
        (z0.val.val - 1) = z0.val.val - 1 := by
      have := congrArg (rowsMatrix 22) (beq_iff_eq.1 h2)
      rwa [rowsMatrix_mulRows, ← hv, subId_glZ_val] at this
    show ((hK k)⁻¹ * xRootK (Native.glF0Root k) t * hK k).val.val *ᵥ
      ((z0.val.val - 1) *ᵥ u) = (z0.val.val - 1) *ᵥ u
    rw [Matrix.mulVec_mulVec, hm]
  refine ⟨_, hq, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem mem_Qsub_inf_RK_iff
    {k : ℕ} (hk : k ∈ [1, 2, 4, 5]) {g : K} :
    g ∈ Qsub ⊓ RK k ↔ ∃ t < 4, xRootK (Native.glF0Root k) t = g := by
  set B : Set K := xRootK (Native.glF0Root k) '' {t | t < 4} with hB
  have hBA : B ⊆ ((Qsub ⊓ RK k : Subgroup K) : Set K) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨xRootK_mem_Qsub (glF0Root_lt k) ht, xRootK_mem_RK hk ht⟩
  have hinj : Set.InjOn (xRootK (Native.glF0Root k)) {t | t < 4} := by
    intro s hs t ht hst
    have hd := (glF0k_spec hk).2.2.2.2.2.2
    have hs' : s ∈ [0, 1, 2, 3] := by simp at hs ⊢; omega
    have ht' : t ∈ [0, 1, 2, 3] := by simp at ht ⊢; omega
    rcases (hd s hs').2 t ht' with h | h
    · exact h
    · exact absurd (eq_of_rowsMatrix_eq (hd s hs').1 (hd t ht').1
        (by rw [← xRootK_val, ← xRootK_val, hst])) h
  have hBcard : B.ncard = 4 := by
    rw [hB, hinj.ncard_image]
    have : {t : ℕ | t < 4} = ↑(Finset.range 4) := by ext; simp
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  have hAcard : ((Qsub ⊓ RK k : Subgroup K) : Set K).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, card_Qsub_inf_RK hk]
  have hAB := Set.eq_of_subset_of_ncard_le hBA (by rw [hAcard, hBcard])
    (Set.toFinite _)
  constructor
  · intro hg
    have : g ∈ B := by rw [hAB]; exact hg
    obtain ⟨t, ht, rfl⟩ := this
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact hBA ⟨t, ht, rfl⟩

end CFSG.Sporadic.Co2Smith
