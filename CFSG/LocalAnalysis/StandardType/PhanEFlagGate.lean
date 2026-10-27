module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagGateBlk

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n m : ℕ} {d : List ℕ}

private lemma q2cFG_finrank_span_image (b : Fin n → (Fin n → K))
    (hb : LinearIndependent K b) (S : Finset (Fin n)) :
    finrank K (Submodule.span K (b '' (S : Set (Fin n)))) = S.card := by
  have hrange : Set.range (fun x : S => b x.1) = b '' (S : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card]
  · exact Fintype.card_coe S
  · exact hb.comp _ Subtype.val_injective

private lemma q2cFG_card_filter_fin_lt {j : ℕ} (hj : j ≤ n) :
    (Finset.univ.filter fun k : Fin n => k.val < j).card = j := by
  have himage : (Finset.univ.filter fun k : Fin n => k.val < j) =
      Finset.univ.image (fun r : Fin j => (⟨r.val, lt_of_lt_of_le r.isLt hj⟩ : Fin n)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hk; exact ⟨⟨k.val, hk⟩, rfl⟩
    · rintro ⟨r, -, rfl⟩; exact r.isLt
  rw [himage, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Fin.ext (by simpa using congrArg Fin.val h)

private lemma q2cFG_card_filter_perm (τ : Equiv.Perm (Fin n)) {j : ℕ} (hj : j ≤ n) :
    (Finset.univ.filter fun k : Fin n => (τ k).val < j).card = j := by
  have e : {k : Fin n // (τ k).val < j} ≃ {i : Fin n // i.val < j} :=
    { toFun := fun k => ⟨τ k, k.2⟩
      invFun := fun i => ⟨τ.symm i, by rw [τ.apply_symm_apply]; exact i.2⟩
      left_inv := fun k => by ext; simp
      right_inv := fun i => by ext; simp }
  have e2 : {i : Fin n // i.val < j} ≃ Fin j :=
    { toFun := fun i => ⟨i.val.val, i.2⟩
      invFun := fun r => ⟨⟨r.val, lt_of_lt_of_le r.isLt hj⟩, r.isLt⟩
      left_inv := fun i => by ext; simp
      right_inv := fun r => by ext; simp }
  calc (Finset.univ.filter fun k : Fin n => (τ k).val < j).card
      = Fintype.card {k : Fin n // (τ k).val < j} :=
        (Fintype.card_subtype (fun k : Fin n => (τ k).val < j)).symm
    _ = Fintype.card {i : Fin n // i.val < j} := Fintype.card_congr e
    _ = Fintype.card (Fin j) := Fintype.card_congr e2
    _ = j := Fintype.card_fin j

private theorem q2cFG_exists_vec (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    (k : Fin n) :
    ∃ v : Fin n → K, v ∈ E.E (k.val + 1) ∧
      v ∈ Vsub n (d.getD (q2cFG_blkFin hd k + 1) 0) ∧ v ∉ E.E k.val := by
  have hE' := hE
  simp only [farSet, Set.mem_setOf_eq] at hE'
  have hb := q2cFG_blkFin_lt hd k
  have hble := q2cFG_le_n hd hb
  have hbr : q2cFG_r hd k = k.val + 1 + d.getD (q2cFG_blkFin hd k + 1) 0 - n := rfl
  have hwin := (q2cFG_blkFin_window hd k).1
  have hrpos := q2cFG_r_pos hd k
  have hklt := k.isLt
  set A := E.E (k.val + 1) ⊓ Vsub n (d.getD (q2cFG_blkFin hd k + 1) 0) with hA
  set B := E.E k.val ⊓ Vsub n (d.getD (q2cFG_blkFin hd k + 1) 0) with hB
  have hBA : B ≤ A := inf_le_inf_right _ (E.mono (by omega))
  have hdimA : finrank K ↥A = q2cFG_r hd k := by
    rw [hA]
    have h := hE' (q2cFG_blkFin hd k + 1) hb (k.val + 1) (by omega)
    rw [h]
    omega
  have hdimB : finrank K ↥B = q2cFG_r hd k - 1 := by
    rw [hB]
    have h := hE' (q2cFG_blkFin hd k + 1) hb k.val (by omega)
    rw [h]
    omega
  have hex : ∃ v, v ∈ A ∧ v ∉ E.E k.val := by
    by_contra hc
    have hle : A ≤ B := by
      intro v hv
      have hvk : v ∈ E.E k.val := by
        by_contra hvk
        exact hc ⟨v, hv, hvk⟩
      exact ⟨hvk, hv.2⟩
    have heq : A = B := le_antisymm hle hBA
    have h : finrank K ↥A = finrank K ↥B := by rw [heq]
    omega
  obtain ⟨v, hvA, hvk⟩ := hex
  exact ⟨v, hvA.1, hvA.2, hvk⟩

private noncomputable def q2cFG_b (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    (k : Fin n) : Fin n → K :=
  Classical.choose (q2cFG_exists_vec hd hE k)

private theorem q2cFG_b_mem_E_succ (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    (k : Fin n) : q2cFG_b hd hE k ∈ E.E (k.val + 1) :=
  (Classical.choose_spec (q2cFG_exists_vec hd hE k)).1

private theorem q2cFG_b_mem_V (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    (k : Fin n) :
    q2cFG_b hd hE k ∈ Vsub n (d.getD (q2cFG_blkFin hd k + 1) 0) :=
  (Classical.choose_spec (q2cFG_exists_vec hd hE k)).2.1

private theorem q2cFG_b_notMem_E (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    (k : Fin n) : q2cFG_b hd hE k ∉ E.E k.val :=
  (Classical.choose_spec (q2cFG_exists_vec hd hE k)).2.2

private noncomputable def q2cFG_bfin (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    (i : ℕ) (hi : i ≤ n) : Fin i → (Fin n → K) :=
  fun k => q2cFG_b hd hE ⟨k.val, lt_of_lt_of_le k.isLt hi⟩

private theorem q2cFG_linIndep_fin (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) :
    ∀ i (hi : i ≤ n), LinearIndependent K (q2cFG_bfin hd hE i hi) := by
  intro i
  induction i with
  | zero => intro _; exact linearIndependent_empty_type
  | succ i ih =>
      intro hi
      have hik : i ≤ n := by omega
      have hin : i < n := by omega
      have hsnoc : q2cFG_bfin hd hE (i + 1) hi =
          Fin.snoc (q2cFG_bfin hd hE i hik) (q2cFG_b hd hE ⟨i, hin⟩) := by
        funext k
        by_cases hk : k.val < i
        · have hkc : k = Fin.castSucc (⟨k.val, hk⟩ : Fin i) := Fin.ext rfl
          rw [hkc]
          simp only [q2cFG_bfin, Fin.snoc_castSucc]
          rfl
        · have hke : k.val = i := by omega
          have hkl : k = Fin.last i := Fin.ext hke
          rw [hkl]
          simp only [q2cFG_bfin, Fin.snoc_last]
          rfl
      rw [hsnoc]
      apply LinearIndependent.finSnoc (ih hik)
      have hspan_le : Submodule.span K (Set.range (q2cFG_bfin hd hE i hik)) ≤ E.E i := by
        rw [Submodule.span_le]
        rintro v ⟨k, rfl⟩
        have hk := k.isLt
        refine E.mono ?_ (q2cFG_b_mem_E_succ hd hE ⟨k.val, lt_of_lt_of_le k.isLt hik⟩)
        show k.val + 1 ≤ i
        omega
      intro hmem
      exact q2cFG_b_notMem_E hd hE ⟨i, hin⟩ (hspan_le hmem)

private theorem q2cFG_linIndep (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) :
    LinearIndependent K (q2cFG_b hd hE) := by
  have h := q2cFG_linIndep_fin hd hE n le_rfl
  convert h using 1
  funext k
  simp only [q2cFG_bfin]

private theorem q2cFG_E_eq_span (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    {i : ℕ} (hi : i ≤ n) :
    E.E i = Submodule.span K (q2cFG_b hd hE '' {k : Fin n | k.val < i}) := by
  have hle : Submodule.span K (q2cFG_b hd hE '' {k : Fin n | k.val < i}) ≤ E.E i := by
    rw [Submodule.span_le]
    rintro v ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq] at hk
    exact E.mono (by omega) (q2cFG_b_mem_E_succ hd hE k)
  have hdim : finrank K (Submodule.span K (q2cFG_b hd hE '' {k : Fin n | k.val < i})) = i := by
    rw [show {k : Fin n | k.val < i} = ↑(Finset.univ.filter fun k : Fin n => k.val < i) by
      ext k; simp]
    rw [q2cFG_finrank_span_image _ (q2cFG_linIndep hd hE)]
    exact q2cFG_card_filter_fin_lt hi
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, E.dim i hi])).symm

private noncomputable def q2cFG_x (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) :
    FlagK K n where
  E j := Submodule.span K (q2cFG_b hd hE '' {k : Fin n | (q2cFG_tau hd k).val < j})
  mono := by
    intro i j hij
    apply Submodule.span_mono
    rintro v ⟨k, hk, rfl⟩
    exact ⟨k, by simp only [Set.mem_setOf_eq] at hk ⊢; omega, rfl⟩
  dim := by
    intro j hj
    rw [show {k : Fin n | (q2cFG_tau hd k).val < j} =
        ↑(Finset.univ.filter fun k : Fin n => (q2cFG_tau hd k).val < j) by
      ext k; simp]
    rw [q2cFG_finrank_span_image _ (q2cFG_linIndep hd hE)]
    exact q2cFG_card_filter_perm (q2cFG_tau hd) hj
  top := by
    intro j hj
    rw [show {k : Fin n | (q2cFG_tau hd k).val < j} = Set.univ by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le (q2cFG_tau hd k).isLt hj]
    rw [Set.image_univ]
    exact Submodule.eq_top_of_finrank_eq (by
      rw [finrank_span_eq_card (q2cFG_linIndep hd hE), Fintype.card_fin, Module.finrank_fin_fun])

private theorem q2cFG_blockU_last (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    {b : ℕ} (hb : b + 1 < d.length) :
    blockU K n d E.E b (blockSize d b) = Vsub n (d.getD (b + 1) 0) := by
  have hmono := q2cFG_hmono hd b hb
  have hle := q2cFG_le_n hd hb
  have hleb : d.getD b 0 ≤ n := q2cFG_le_n hd (by omega)
  have hE' := hE
  simp only [farSet, Set.mem_setOf_eq] at hE'
  have hfinA : finrank K ↥(E.E (n - d.getD b 0) ⊓ Vsub n (d.getD (b + 1) 0)) =
      blockSize d b := by
    have h := hE' (b + 1) hb (n - d.getD b 0) (by omega)
    rw [h]
    simp only [blockSize]
    omega
  have hbot : E.E (n - d.getD b 0) ⊓ Vsub n (d.getD b 0) = ⊥ := by
    have h0 : finrank K ↥(E.E (n - d.getD b 0) ⊓ Vsub n (d.getD b 0)) = 0 := by
      have h := hE' b (by omega) (n - d.getD b 0) (by omega)
      rw [h]; omega
    exact (Submodule.finrank_eq_zero).mp h0
  have hdisj : Disjoint (E.E (n - d.getD b 0) ⊓ Vsub n (d.getD (b + 1) 0))
      (Vsub n (d.getD b 0)) := by
    rw [disjoint_iff]
    have hle' : (E.E (n - d.getD b 0) ⊓ Vsub n (d.getD (b + 1) 0)) ⊓ Vsub n (d.getD b 0) ≤
        E.E (n - d.getD b 0) ⊓ Vsub n (d.getD b 0) := by
      intro v hv; exact ⟨hv.1.1, hv.2⟩
    exact le_bot_iff.mp (hle'.trans (le_of_eq hbot))
  have hsup : finrank K ↥((E.E (n - d.getD b 0) ⊓ Vsub n (d.getD (b + 1) 0)) ⊔
      Vsub (K := K) n (d.getD b 0)) = d.getD (b + 1) 0 := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (E.E (n - d.getD b 0) ⊓ Vsub n (d.getD (b + 1) 0)) (Vsub (K := K) n (d.getD b 0))
    have hinf : finrank K ↥((E.E (n - d.getD b 0) ⊓ Vsub n (d.getD (b + 1) 0)) ⊓
        Vsub (K := K) n (d.getD b 0)) = 0 := by
      rw [disjoint_iff.mp hdisj, finrank_bot]
    have hbs : d.getD b 0 + blockSize d b = d.getD (b + 1) 0 := by
      rw [blockSize]; exact Nat.add_sub_cancel' hmono
    rw [hfinA, finrank_Vsub hleb, hinf] at hsum
    omega
  have hleV : (E.E (n - d.getD b 0) ⊓ Vsub n (d.getD (b + 1) 0)) ⊔
      Vsub (K := K) n (d.getD b 0) ≤ Vsub n (d.getD (b + 1) 0) :=
    sup_le inf_le_right (Vsub_mono (K := K) hmono)
  have hgoal : (E.E (n - d.getD b 0) ⊓ Vsub n (d.getD (b + 1) 0)) ⊔
      Vsub (K := K) n (d.getD b 0) = Vsub n (d.getD (b + 1) 0) :=
    Submodule.eq_of_le_of_finrank_eq hleV (by rw [hsup, finrank_Vsub hle])
  show (E.E (n - d.getD (b + 1) 0 + blockSize d b) ⊓ Vsub n (d.getD (b + 1) 0)) ⊔
    Vsub n (d.getD b 0) = Vsub n (d.getD (b + 1) 0)
  rw [show n - d.getD (b + 1) 0 + blockSize d b = n - d.getD b 0 by
    simp only [blockSize]; omega]
  exact hgoal

private theorem q2cFG_x_E (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d)
    {b r : ℕ} (hb : b + 1 < d.length) (hr : r ≤ blockSize d b) :
    (q2cFG_x hd hE).E (d.getD b 0 + r) = blockU K n d E.E b r := by
  have hmono := q2cFG_hmono hd b hb
  have hle := q2cFG_le_n hd hb
  have hr' : r ≤ d.getD (b + 1) 0 - d.getD b 0 := by simpa [blockSize] using hr
  have hdr : d.getD b 0 + r ≤ n := by
    have hbs : d.getD b 0 + blockSize d b = d.getD (b + 1) 0 := by
      rw [blockSize]; exact Nat.add_sub_cancel' hmono
    omega
  have hE' := hE
  simp only [farSet, Set.mem_setOf_eq] at hE'
  have hc : n - d.getD (b + 1) 0 + r ≤ n := by omega
  have hU : finrank K ↥(E.E (n - d.getD (b + 1) 0 + r) ⊓ Vsub n (d.getD (b + 1) 0)) = r := by
    have h := hE' (b + 1) hb (n - d.getD (b + 1) 0 + r) hc
    rw [h]; omega
  have hV : finrank K ↥(Vsub (K := K) n (d.getD b 0)) = d.getD b 0 :=
    finrank_Vsub (q2cFG_le_n hd (by omega : b < d.length))
  have hI : finrank K ↥((E.E (n - d.getD (b + 1) 0 + r) ⊓ Vsub n (d.getD (b + 1) 0)) ⊓
      Vsub n (d.getD b 0)) = 0 := by
    have heq : (E.E (n - d.getD (b + 1) 0 + r) ⊓ Vsub n (d.getD (b + 1) 0)) ⊓
        Vsub n (d.getD b 0) = E.E (n - d.getD (b + 1) 0 + r) ⊓ Vsub n (d.getD b 0) := by
      rw [inf_assoc, inf_eq_right.mpr (Vsub_mono (K := K) hmono)]
    rw [heq]
    have h := hE' b (by omega) (n - d.getD (b + 1) 0 + r) (by omega)
    rw [h]
    omega
  have hdimU : finrank K ↥(blockU K n d E.E b r) = d.getD b 0 + r := by
    show finrank K ↥((E.E (n - d.getD (b + 1) 0 + r) ⊓ Vsub n (d.getD (b + 1) 0)) ⊔
      Vsub n (d.getD b 0)) = d.getD b 0 + r
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (E.E (n - d.getD (b + 1) 0 + r) ⊓ Vsub n (d.getD (b + 1) 0)) (Vsub n (d.getD b 0))
    omega
  have hspan_le : (q2cFG_x hd hE).E (d.getD b 0 + r) ≤ blockU K n d E.E b r := by
    show Submodule.span K (q2cFG_b hd hE '' {k : Fin n | (q2cFG_tau hd k).val < d.getD b 0 + r}) ≤
      ((E.E (n - d.getD (b + 1) 0 + r) ⊓ Vsub n (d.getD (b + 1) 0)) ⊔ Vsub n (d.getD b 0))
    rw [Submodule.span_le]
    rintro v ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq] at hk
    have htau := q2cFG_tau_val hd k
    have hspec := q2cFG_r_spec hd k
    have hrp := q2cFG_r_pos hd k
    have hb' := q2cFG_blkFin_lt hd k
    have hle' := q2cFG_le_n hd hb'
    rcases lt_trichotomy (q2cFG_blkFin hd k) b with hlt | heq | hgt
    · refine Submodule.mem_sup_right (Vsub_mono (K := K) ?_ (q2cFG_b_mem_V hd hE k))
      exact q2cFG_mono hd (show q2cFG_blkFin hd k + 1 ≤ b by omega) (by omega)
    · refine Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨?_, ?_⟩)
      · apply E.mono ?_ (q2cFG_b_mem_E_succ hd hE k)
        rw [heq] at htau hspec
        rw [htau] at hk
        omega
      · rw [← heq]; exact q2cFG_b_mem_V hd hE k
    · exfalso
      have hbs : d.getD b 0 + blockSize d b = d.getD (b + 1) 0 := by
        rw [blockSize]; exact Nat.add_sub_cancel' hmono
      have hmono' := q2cFG_mono hd (show b + 1 ≤ q2cFG_blkFin hd k by omega) (by omega)
      rw [htau] at hk
      omega
  have hdimS : finrank K ↥((q2cFG_x hd hE).E (d.getD b 0 + r)) = d.getD b 0 + r := by
    show finrank K (Submodule.span K
      (q2cFG_b hd hE '' {k : Fin n | (q2cFG_tau hd k).val < d.getD b 0 + r})) = _
    rw [show {k : Fin n | (q2cFG_tau hd k).val < d.getD b 0 + r} =
        ↑(Finset.univ.filter fun k : Fin n => (q2cFG_tau hd k).val < d.getD b 0 + r) by
      ext k; simp]
    rw [q2cFG_finrank_span_image _ (q2cFG_linIndep hd hE)]
    exact q2cFG_card_filter_perm (q2cFG_tau hd) hdr
  exact Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hdimS, hdimU])

private theorem q2cFG_x_window (hd : IsCut n d) (k : Fin n) {b : ℕ}
    (hb : b + 1 < d.length) (hk₁ : n - d.getD (b + 1) 0 ≤ k.val)
    (hk₂ : k.val < n - d.getD b 0) :
    (q2cFG_tau hd k).val = k.val + d.getD b 0 + d.getD (b + 1) 0 - n := by
  have hblk := q2cFG_blkFin_unique hd k hb hk₁ hk₂
  rw [q2cFG_tau_val hd k, hblk]
  have hspec := q2cFG_r_spec hd k
  rw [hblk] at hspec
  have hle := q2cFG_le_n hd hb
  omega

theorem exists_gateFlag (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) :
    ∃ x : FlagK K n, ∀ b r, b + 1 < d.length → r ≤ blockSize d b →
      x.E (d.getD b 0 + r) = blockU K n d E.E b r :=
  ⟨q2cFG_x hd hE, fun b r hb hr => q2cFG_x_E hd hE hb hr⟩

@[expose] noncomputable def gateFlag (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) :
    FlagK K n :=
  Classical.choose (exists_gateFlag hd hE)

theorem gateFlag_E (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) {b r : ℕ}
    (hb : b + 1 < d.length) (hr : r ≤ blockSize d b) :
    (gateFlag hd hE).E (d.getD b 0 + r) = blockU K n d E.E b r :=
  Classical.choose_spec (exists_gateFlag hd hE) b r hb hr

private theorem q2cFG_x_eq_gateFlag (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) :
    q2cFG_x hd hE = gateFlag hd hE := by
  apply FlagK.ext_of_mid
  intro j hj1 hjn
  have hb := q2cFG_blk_lt hd j hjn
  have hb₁ := q2cFG_blk_le hd j hjn
  have hb₂ := q2cFG_blk_lt_level hd j hjn
  have hr : j - d.getD (q2cFG_blk hd j hjn) 0 ≤ blockSize d (q2cFG_blk hd j hjn) := by
    rw [blockSize]; omega
  have hjr : d.getD (q2cFG_blk hd j hjn) 0 + (j - d.getD (q2cFG_blk hd j hjn) 0) = j :=
    Nat.add_sub_cancel' hb₁
  have hx := q2cFG_x_E hd hE hb hr
  have hg := gateFlag_E hd hE hb hr
  rw [hjr] at hx hg
  rw [hx, hg]

theorem gateFlag_mem_refSet (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) :
    gateFlag hd hE ∈ refSet K n d := by
  rw [← q2cFG_x_eq_gateFlag hd hE]
  simp only [refSet, Set.mem_setOf_eq]
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [hd.head, Vsub_zero]
    show Submodule.span K (q2cFG_b hd hE '' {k : Fin n | (q2cFG_tau hd k).val < 0}) = ⊥
    rw [show {k : Fin n | (q2cFG_tau hd k).val < 0} = (∅ : Set (Fin n)) by
      ext k; simp, Set.image_empty, Submodule.span_empty]
  · have hb : i - 1 + 1 < d.length := by omega
    have hi_eq : i = (i - 1) + 1 := by omega
    have hbs : d.getD (i - 1) 0 + blockSize d (i - 1) = d.getD ((i - 1) + 1) 0 := by
      rw [blockSize]; exact Nat.add_sub_cancel' (q2cFG_hmono hd (i - 1) hb)
    rw [hi_eq, ← hbs, q2cFG_x_E hd hE hb le_rfl, q2cFG_blockU_last hd hE hb, hbs]

theorem exists_blockRev (hd : IsCut n d) :
    ∃ τ : Equiv.Perm (Fin n), ∀ (k : Fin n) (b : ℕ), b + 1 < d.length →
      n - d.getD (b + 1) 0 ≤ k.val → k.val < n - d.getD b 0 →
        (τ k).val = k.val + d.getD b 0 + d.getD (b + 1) 0 - n :=
  ⟨q2cFG_tau hd, fun k b hb hk₁ hk₂ => q2cFG_x_window hd k hb hk₁ hk₂⟩

@[expose] noncomputable def blockRev (hd : IsCut n d) : Equiv.Perm (Fin n) :=
  Classical.choose (exists_blockRev hd)

theorem blockRev_apply (hd : IsCut n d) (k : Fin n) {b : ℕ} (hb : b + 1 < d.length)
    (hk₁ : n - d.getD (b + 1) 0 ≤ k.val) (hk₂ : k.val < n - d.getD b 0) :
    (blockRev hd k).val = k.val + d.getD b 0 + d.getD (b + 1) 0 - n :=
  Classical.choose_spec (exists_blockRev hd) k b hb hk₁ hk₂

private theorem q2cFG_tau_eq_blockRev (hd : IsCut n d) :
    q2cFG_tau hd = blockRev hd := by
  apply Equiv.ext
  intro k
  apply Fin.ext
  have hwin := q2cFG_blkFin_window hd k
  rw [q2cFG_x_window hd k (q2cFG_blkFin_lt hd k) hwin.1 hwin.2,
    blockRev_apply hd k (q2cFG_blkFin_lt hd k) hwin.1 hwin.2]

theorem hasPos_gateFlag (hd : IsCut n d) {E : FlagK K n} (hE : E ∈ farSet n d) :
    HasPos E (gateFlag hd hE) (blockRev hd) := by
  have hadapt : IsAdapted (q2cFG_b hd hE) (q2cFG_tau hd) E (q2cFG_x hd hE) :=
    ⟨q2cFG_linIndep hd hE, fun i hi => q2cFG_E_eq_span hd hE hi, fun j _ => rfl⟩
  have hpos := hasPos_of_isAdapted hadapt
  rw [q2cFG_x_eq_gateFlag hd hE, q2cFG_tau_eq_blockRev hd] at hpos
  exact hpos

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
