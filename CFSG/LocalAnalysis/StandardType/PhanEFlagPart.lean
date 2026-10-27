module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagCut

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {n m : ℕ} {d : List ℕ}

private lemma q2cFPt_blockRevI_mem_prefixSub {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d) :
    q2cFPt_blockRevI hd ∈ q2cFPt_prefixSub (m + 1) d := by
  intro b hb k
  rw [q2cFPt_blockRevI_apply]
  exact q2cFPt_blockRev_prefix hd hb k

private lemma q2cFPt_isLeftDescent_blockRevI {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {i : Fin m} (hi : i ∈ cutTypes m d) :
    (symCox m).IsLeftDescent (q2cFPt_blockRevI hd) i := by
  rw [CoxeterSystem.isLeftDescent_iff, symCox_length, symCox_length, symCox_simple]
  apply invCount_adjSwap_mul_of_gt
  have hc1 : 1 ≤ q2cFPt_nextCut hd i.castSucc := q2cFPt_nextCut_pos hd _
  have hclt : q2cFPt_nextCut hd i.castSucc < d.length := q2cFPt_nextCut_lt_length hd _
  have hb1 : d.getD (q2cFPt_nextCut hd i.castSucc - 1) 0 ≤ i.castSucc.val :=
    q2cFPt_nextCut_min hd _ (by omega)
  have hb2 : i.castSucc.val < d.getD (q2cFPt_nextCut hd i.castSucc) 0 :=
    q2cFPt_nextCut_spec hd _
  have hb2' : i.succ.val < d.getD (q2cFPt_nextCut hd i.castSucc) 0 := by
    by_contra h
    rw [not_lt] at h
    have hcn := hi _ hclt
    have hspec := q2cFPt_nextCut_spec hd i.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at hcn h hspec
    omega
  have hlt : q2cFPt_blockRevI hd i.succ < q2cFPt_blockRevI hd i.castSucc := by
    rw [q2cFPt_blockRevI_apply, q2cFPt_blockRevI_apply, Fin.lt_def,
      q2cFPt_blockRev_val_of_block hd (b := q2cFPt_nextCut hd i.castSucc - 1)
        (by rw [Nat.sub_add_cancel hc1]; exact hclt)
        (le_trans hb1 (by simp [Fin.val_succ, Fin.val_castSucc]))
        (by rw [Nat.sub_add_cancel hc1]; exact hb2'),
      q2cFPt_blockRev_val_of_block hd (b := q2cFPt_nextCut hd i.castSucc - 1)
        (by rw [Nat.sub_add_cancel hc1]; exact hclt) hb1
        (by rw [Nat.sub_add_cancel hc1]; exact hb2)]
    rw [Nat.sub_add_cancel hc1]
    have hlt2 : i.castSucc.val < i.succ.val := by simp [Fin.val_succ, Fin.val_castSucc]
    omega
  simpa [q2cFPt_blockRevI] using hlt

private lemma q2cFPt_isLongest_blockRevI {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d) :
    IsLongest (symCox m) (cutTypes m d) (q2cFPt_blockRevI hd) := by
  haveI : Finite ((symCox m).parabolic (cutTypes m d)) := Subtype.finite
  apply isLongest_of_forall_isLeftDescent
  · rw [q2cFPt_parabolic_eq_prefixSub hd]
    exact q2cFPt_blockRevI_mem_prefixSub hd
  · intro i hi
    exact q2cFPt_isLeftDescent_blockRevI hd hi

private lemma q2cFPt_longest_eq {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d) :
    longest (symCox m) (cutTypes m d) = q2cFPt_blockRevI hd :=
  (q2cFPt_isLongest_blockRevI hd).eq_longest.symm

theorem longest_cutTypes_apply (hd : IsCut (m + 1) d) (k : Fin (m + 1)) {b : ℕ}
    (hb : b + 1 < d.length) (hk₁ : d.getD b 0 ≤ k.val) (hk₂ : k.val < d.getD (b + 1) 0) :
    (longest (symCox m) (cutTypes m d) k).val = d.getD b 0 + d.getD (b + 1) 0 - 1 - k.val := by
  rw [q2cFPt_longest_eq hd, q2cFPt_blockRevI_apply]
  exact q2cFPt_blockRev_val_of_block hd hb hk₁ hk₂

private lemma q2cFPt_permRk_blockRev_diag {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {b r : ℕ} (hb : b + 1 < d.length) (hr : r ≤ blockSize d b) :
    permRk (q2cFPt_blockRevI hd) (d.getD b 0 + r) (d.getD b 0 + (blockSize d b - r)) =
      d.getD b 0 := by
  have hbs : blockSize d b = d.getD (b + 1) 0 - d.getD b 0 := rfl
  have hble : d.getD b 0 ≤ d.getD (b + 1) 0 := q2cFPt_getD_le hd (by omega) (by omega)
  unfold permRk
  have hset : (Finset.univ.filter fun k : Fin (m + 1) =>
        k.val < d.getD b 0 + r ∧ (q2cFPt_blockRevI hd k).val <
          d.getD b 0 + (blockSize d b - r)) =
      (Finset.univ.filter fun k : Fin (m + 1) => k.val < d.getD b 0) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk1, hk2⟩
      by_contra hkc
      rw [not_lt] at hkc
      have hk3 : k.val < d.getD (b + 1) 0 := by omega
      have hv := q2cFPt_blockRev_val_of_block hd hb hkc hk3
      rw [q2cFPt_blockRevI_apply, hv] at hk2
      omega
    · intro hk
      have h1 := q2cFPt_blockRev_mem hd (by omega : b < d.length) hk
      rw [q2cFPt_blockRevI_apply]
      omega
  rw [hset, q2cFPt_card_fin_lt (q2cFPt_le_last hd (by omega : b < d.length))]

private lemma q2cFPt_ge_of_diag {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ ∈ q2cFPt_prefixSub (m + 1) d)
    {b r : ℕ} (hb : b + 1 < d.length) (hr : r ≤ blockSize d b)
    (h : permRk σ (d.getD b 0 + r) (d.getD b 0 + (blockSize d b - r)) = d.getD b 0)
    {k : Fin (m + 1)} (hk1 : d.getD b 0 ≤ k.val) (hk2 : k.val < d.getD b 0 + r) :
    d.getD b 0 + (blockSize d b - r) ≤ (σ k).val := by
  by_contra hcon
  rw [not_le] at hcon
  have hsub : (Finset.univ.filter fun j : Fin (m + 1) => j.val < d.getD b 0) ⊆
      (Finset.univ.filter fun j : Fin (m + 1) =>
        j.val < d.getD b 0 + r ∧ (σ j).val < d.getD b 0 + (blockSize d b - r)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨by omega, ?_⟩
    have h' := (hσ b (by omega) j).mpr hj
    omega
  unfold permRk at h
  have hcardT : (Finset.univ.filter fun j : Fin (m + 1) => j.val < d.getD b 0).card =
      d.getD b 0 := q2cFPt_card_fin_lt (q2cFPt_le_last hd (by omega))
  have hcardS : (Finset.univ.filter fun j : Fin (m + 1) =>
      j.val < d.getD b 0 + r ∧ (σ j).val < d.getD b 0 + (blockSize d b - r)).card =
      d.getD b 0 := h
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq (hcardS.trans hcardT.symm))
  have hkS : k ∈ Finset.univ.filter (fun j : Fin (m + 1) =>
      j.val < d.getD b 0 + r ∧ (σ j).val < d.getD b 0 + (blockSize d b - r)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk2, hcon⟩
  rw [← heq] at hkS
  exact absurd (Finset.mem_filter.mp hkS).2 (by omega)

private lemma q2cFPt_eq_rev_of_forall_ge {t : ℕ} {π : Fin t → Fin t}
    (hπ : Function.Injective π) (h : ∀ u : Fin t, t - 1 - u.val ≤ (π u).val) :
    ∀ u : Fin t, (π u).val = t - 1 - u.val := by
  intro u
  have H : ∀ n (hn : n < t), (π ⟨n, hn⟩).val = t - 1 - n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hge : t - 1 - n ≤ (π ⟨n, hn⟩).val := h ⟨n, hn⟩
      have hlt : (π ⟨n, hn⟩).val < t := (π ⟨n, hn⟩).isLt
      have hne : ∀ v, v < n → (π ⟨n, hn⟩).val ≠ t - 1 - v := by
        intro v hv hveq
        have hv' : v < t := by omega
        have hih : (π ⟨v, hv'⟩).val = t - 1 - v := ih v hv hv'
        have hfin : (⟨v, hv'⟩ : Fin t) = ⟨n, hn⟩ := hπ (Fin.ext (hih.trans hveq.symm))
        exact (by omega : v ≠ n) (congrArg Fin.val hfin)
      by_contra hne'
      have hgt : t - 1 - n < (π ⟨n, hn⟩).val := lt_of_le_of_ne hge (Ne.symm hne')
      exact hne (t - 1 - (π ⟨n, hn⟩).val) (by omega) (by omega)
  exact H u.val u.isLt

private lemma q2cFPt_block_eq_rev {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ ∈ q2cFPt_prefixSub (m + 1) d)
    {b : ℕ} (hb : b + 1 < d.length)
    (hbound : ∀ k : Fin (m + 1), d.getD b 0 ≤ k.val → k.val < d.getD (b + 1) 0 →
      d.getD b 0 + blockSize d b - 1 - (k.val - d.getD b 0) ≤ (σ k).val) :
    ∀ k : Fin (m + 1), d.getD b 0 ≤ k.val → k.val < d.getD (b + 1) 0 →
      (σ k).val = d.getD b 0 + blockSize d b - 1 - (k.val - d.getD b 0) := by
  have hle := q2cFPt_le_last hd hb
  have hbs : blockSize d b = d.getD (b + 1) 0 - d.getD b 0 := rfl
  let emb : Fin (blockSize d b) → Fin (m + 1) := fun u =>
    ⟨d.getD b 0 + u.val, by have := u.isLt; omega⟩
  have hemb : ∀ u : Fin (blockSize d b), (emb u).val = d.getD b 0 + u.val := fun u => rfl
  have hge_mem : ∀ u : Fin (blockSize d b), d.getD b 0 ≤ (σ (emb u)).val := by
    intro u
    by_contra hlt
    rw [not_le] at hlt
    have h' := (hσ b (by omega : b < d.length) (emb u)).mp hlt
    rw [hemb u] at h'
    omega
  have hlt_mem : ∀ u : Fin (blockSize d b), (σ (emb u)).val < d.getD b 0 + blockSize d b := by
    intro u
    have h' := (hσ (b + 1) hb (emb u)).mpr (by rw [hemb u]; omega)
    omega
  let π : Fin (blockSize d b) → Fin (blockSize d b) := fun u =>
    ⟨(σ (emb u)).val - d.getD b 0, by have := hge_mem u; have := hlt_mem u; omega⟩
  have hπval : ∀ u : Fin (blockSize d b), (π u).val = (σ (emb u)).val - d.getD b 0 :=
    fun u => rfl
  have hπinj : Function.Injective π := by
    intro u v huv
    have h : (π u).val = (π v).val := congrArg Fin.val huv
    rw [hπval u, hπval v] at h
    have hu : (σ (emb u)).val = (σ (emb v)).val := by
      have := hge_mem u; have := hge_mem v; omega
    have hemb' : emb u = emb v := σ.injective (Fin.ext hu)
    have h2 : (emb u).val = (emb v).val := congrArg Fin.val hemb'
    rw [hemb u, hemb v] at h2
    exact Fin.ext (by omega)
  have hπge : ∀ u : Fin (blockSize d b), blockSize d b - 1 - u.val ≤ (π u).val := by
    intro u
    have hbnd := hbound (emb u) (by rw [hemb u]; omega) (by rw [hemb u]; omega)
    rw [hemb u] at hbnd
    rw [hπval u]
    omega
  have hπeq := q2cFPt_eq_rev_of_forall_ge hπinj hπge
  have hpoint : ∀ u : Fin (blockSize d b),
      (σ (emb u)).val = d.getD b 0 + blockSize d b - 1 - u.val := by
    intro u
    have h := hπeq u
    rw [hπval u] at h
    have hge := hge_mem u
    omega
  intro k hk1 hk2
  have hklt : k.val - d.getD b 0 < blockSize d b := by omega
  have hk_eq : emb ⟨k.val - d.getD b 0, hklt⟩ = k := by
    apply Fin.ext
    rw [hemb]
    simp only [Fin.val_mk]
    omega
  rw [← hk_eq]
  have h := hpoint ⟨k.val - d.getD b 0, hklt⟩
  have hembu := hemb ⟨k.val - d.getD b 0, hklt⟩
  have huval : (⟨k.val - d.getD b 0, hklt⟩ : Fin (blockSize d b)).val = k.val - d.getD b 0 := rfl
  omega

private lemma q2cFPt_eq_blockRev_of_diag {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ ∈ q2cFPt_prefixSub (m + 1) d)
    (hdiag : ∀ b r, b + 1 < d.length → r ≤ blockSize d b →
      permRk σ (d.getD b 0 + r) (d.getD b 0 + (blockSize d b - r)) = d.getD b 0) :
    σ = q2cFPt_blockRevI hd := by
  apply Equiv.ext
  intro k
  have hc1 : 1 ≤ q2cFPt_nextCut hd k := q2cFPt_nextCut_pos hd k
  have hb : (q2cFPt_nextCut hd k - 1) + 1 < d.length := by
    rw [Nat.sub_add_cancel hc1]; exact q2cFPt_nextCut_lt_length hd k
  have hk1 : d.getD (q2cFPt_nextCut hd k - 1) 0 ≤ k.val :=
    q2cFPt_nextCut_min hd k (by omega)
  have hk2 : k.val < d.getD ((q2cFPt_nextCut hd k - 1) + 1) 0 := by
    rw [Nat.sub_add_cancel hc1]; exact q2cFPt_nextCut_spec hd k
  have hbound : ∀ j : Fin (m + 1), d.getD (q2cFPt_nextCut hd k - 1) 0 ≤ j.val →
      j.val < d.getD ((q2cFPt_nextCut hd k - 1) + 1) 0 →
      d.getD (q2cFPt_nextCut hd k - 1) 0 + blockSize d (q2cFPt_nextCut hd k - 1) - 1 -
        (j.val - d.getD (q2cFPt_nextCut hd k - 1) 0) ≤ (σ j).val := by
    intro j hj1 hj2
    have hbs' : blockSize d (q2cFPt_nextCut hd k - 1) =
        d.getD ((q2cFPt_nextCut hd k - 1) + 1) 0 - d.getD (q2cFPt_nextCut hd k - 1) 0 := rfl
    have hr : j.val - d.getD (q2cFPt_nextCut hd k - 1) 0 + 1 ≤
        blockSize d (q2cFPt_nextCut hd k - 1) := by omega
    have hj2' : j.val < d.getD (q2cFPt_nextCut hd k - 1) 0 +
        (j.val - d.getD (q2cFPt_nextCut hd k - 1) 0 + 1) := by omega
    have hjg := q2cFPt_ge_of_diag hd hσ hb hr (hdiag _ _ hb hr) hj1 hj2'
    have := hbs'
    omega
  have hkey := q2cFPt_block_eq_rev hd hσ hb hbound k hk1 hk2
  apply Fin.ext
  rw [q2cFPt_blockRevI_apply, q2cFPt_blockRev_val_of_block hd hb hk1 hk2]
  have hbs' : blockSize d (q2cFPt_nextCut hd k - 1) =
      d.getD ((q2cFPt_nextCut hd k - 1) + 1) 0 - d.getD (q2cFPt_nextCut hd k - 1) 0 := rfl
  omega

theorem flagδ_eq_longest_cutTypes_iff (hd : IsCut (m + 1) d) {x y : FlagK K (m + 1)}
    (hx : x ∈ refSet K (m + 1) d) (hy : y ∈ refSet K (m + 1) d) :
    flagδ m x y = longest (symCox m) (cutTypes m d) ↔
      ∀ b r, b + 1 < d.length → r ≤ blockSize d b →
        x.E (d.getD b 0 + r) ⊓ y.E (d.getD b 0 + (blockSize d b - r)) =
          Vsub (m + 1) (d.getD b 0) := by
  constructor
  · intro h
    have hρ : relPos x y = q2cFPt_blockRevI hd := by
      have h2 : (relPos x y)⁻¹ = q2cFPt_blockRevI hd := by
        simpa [flagδ] using h.trans (q2cFPt_longest_eq hd)
      have h3 := congrArg Inv.inv h2
      rw [inv_inv, q2cFPt_blockRevI_inv] at h3
      exact h3
    intro b r hb hr
    have hc : d.getD b 0 ≤ m + 1 := q2cFPt_le_last hd (by omega : b < d.length)
    have hc' : d.getD (b + 1) 0 ≤ m + 1 := q2cFPt_le_last hd hb
    have hbs : blockSize d b = d.getD (b + 1) 0 - d.getD b 0 := rfl
    have hcm : d.getD b 0 + r ≤ m + 1 := by omega
    have hsm : d.getD b 0 + (blockSize d b - r) ≤ m + 1 := by omega
    have h1 : rk x y (d.getD b 0 + r) (d.getD b 0 + (blockSize d b - r)) =
        permRk (relPos x y) (d.getD b 0 + r) (d.getD b 0 + (blockSize d b - r)) :=
      hasPos_relPos x y _ _ hcm hsm
    unfold rk at h1
    rw [hρ, q2cFPt_permRk_blockRev_diag hd hb hr] at h1
    have hVle : Vsub (K := K) (m + 1) (d.getD b 0) ≤
        x.E (d.getD b 0 + r) ⊓ y.E (d.getD b 0 + (blockSize d b - r)) := by
      refine le_inf ?_ ?_
      · rw [← hx b (by omega : b < d.length)]; exact x.mono (by omega)
      · rw [← hy b (by omega : b < d.length)]; exact y.mono (by omega)
    exact (Submodule.eq_of_le_of_finrank_eq hVle (by rw [finrank_Vsub hc, h1])).symm
  · intro hopp
    have hσ : relPos x y ∈ q2cFPt_prefixSub (m + 1) d := by
      have h' := ((symCox m).parabolic (cutTypes m d)).inv_mem
        (flagδ_mem_parabolic_of_mem_refSet hd hx hy)
      rwa [q2cFPt_parabolic_eq_prefixSub hd] at h'
    have hdiag : ∀ b r, b + 1 < d.length → r ≤ blockSize d b →
        permRk (relPos x y) (d.getD b 0 + r) (d.getD b 0 + (blockSize d b - r)) =
          d.getD b 0 := by
      intro b r hb hr
      have hc : d.getD b 0 ≤ m + 1 := q2cFPt_le_last hd (by omega : b < d.length)
      have hc' : d.getD (b + 1) 0 ≤ m + 1 := q2cFPt_le_last hd hb
      have hbs : blockSize d b = d.getD (b + 1) 0 - d.getD b 0 := rfl
      have hcm : d.getD b 0 + r ≤ m + 1 := by omega
      have hsm : d.getD b 0 + (blockSize d b - r) ≤ m + 1 := by omega
      have h1 : rk x y (d.getD b 0 + r) (d.getD b 0 + (blockSize d b - r)) =
          permRk (relPos x y) (d.getD b 0 + r) (d.getD b 0 + (blockSize d b - r)) :=
        hasPos_relPos x y _ _ hcm hsm
      unfold rk at h1
      rw [hopp b r hb hr, finrank_Vsub hc] at h1
      exact h1.symm
    have hσeq : relPos x y = q2cFPt_blockRevI hd := q2cFPt_eq_blockRev_of_diag hd hσ hdiag
    rw [q2cFPt_longest_eq hd]
    have hfin : flagδ m x y = q2cFPt_blockRevI hd := by
      rw [flagδ, hσeq]
      exact q2cFPt_blockRevI_inv hd
    exact hfin
end CFSG.ClassicalInvolution.Phan.PhanE.Flag
