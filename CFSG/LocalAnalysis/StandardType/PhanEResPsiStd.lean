module

public import CFSG.LocalAnalysis.StandardType.PhanEResPsiAct

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
open scoped Matrix

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {d : List ℕ}

private theorem pst_mem_Vsub_iff {c : ℕ} (v : Fin n → K) :
    v ∈ Vsub n c ↔ ∀ i : Fin n, c ≤ i.val → v i = 0 := by
  rfl

private theorem pst_mem_perpB_iff {lo hi : ℕ} (U : Submodule K (Fin n → K)) (v : Fin n → K) :
    v ∈ perpB K f n lo hi U ↔ ∀ u ∈ U, hermLin K f n lo hi u v = 0 := by
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem pst_hermLin_apply (lo hi : ℕ) (u v : Fin n → K) :
    hermLin K f n lo hi u v =
      ∑ i : Fin n, if lo ≤ i.val ∧ i.val < hi then sg K f (u i) * v i else 0 := by
  rw [hermLin, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : lo ≤ i.val ∧ i.val < hi <;> simp [h]

private theorem pst_hermLin_single {lo hi : ℕ} {j : Fin n} (hlj : lo ≤ j.val)
    (hjh : j.val < hi) (v : Fin n → K) :
    hermLin K f n lo hi (Pi.single j (1 : K)) v = v j := by
  rw [pst_hermLin_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp [hlj, hjh]
  · intro i _ hij
    by_cases h : lo ≤ i.val ∧ i.val < hi
    · rw [if_pos h, Pi.single_eq_of_ne' hij.symm]; simp
    · simp [h]

private theorem pst_mem_perpB_Vsub_iff {lo hi k : ℕ} (hlo : lo ≤ k) (hk : k ≤ hi)
    (v : Fin n → K) :
    v ∈ perpB K f n lo hi (Vsub n k) ↔ ∀ i : Fin n, lo ≤ i.val → i.val < k → v i = 0 := by
  rw [pst_mem_perpB_iff]
  constructor
  · intro hv i hli hik
    have hmem : (Pi.single i (1 : K) : Fin n → K) ∈ Vsub n k := by
      intro j hj
      rw [Pi.single_eq_of_ne]
      rintro rfl
      omega
    have h := hv _ hmem
    rwa [pst_hermLin_single hli (lt_of_lt_of_le hik hk)] at h
  · intro hv u hu
    rw [pst_hermLin_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : lo ≤ i.val ∧ i.val < hi
    · rw [if_pos h]
      by_cases hik : i.val < k
      · rw [hv i h.1 hik, mul_zero]
      · rw [hu i (not_lt.1 hik), map_zero, zero_mul]
    · rw [if_neg h]

theorem revBlocks_coe (hd : IsCut n d) :
    ((revBlocks K n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (q2cFPt_blockRevI hd).permMatrix K := by
  rw [revBlocks, dif_pos hd]

private theorem pst_mem_map_glLin_rev_iff (hd : IsCut n d) {j : ℕ} (w : Fin n → K) :
    w ∈ (Vsub n j).map (glLin (revBlocks K n d)).toLinearMap ↔
      ∀ i : Fin n, j ≤ (q2cFPt_blockRevI hd i).val → w i = 0 := by
  have hinv : ∀ k : Fin n, q2cFPt_blockRevI hd (q2cFPt_blockRevI hd k) = k := by
    intro k
    have h := q2cFPt_blockRev_involutive hd k
    simpa [q2cFPt_blockRevI_apply] using h
  constructor
  · rintro ⟨v, hv, rfl⟩ i hi
    change glLin (revBlocks K n d) v i = 0
    simp [glLin_apply, revBlocks_coe hd, Matrix.permMatrix_mulVec]
    exact hv _ hi
  · intro hw
    refine ⟨w ∘ q2cFPt_blockRevI hd, ?_, ?_⟩
    · intro k hk
      exact hw _ (by rw [hinv k]; exact hk)
    · change glLin (revBlocks K n d) (w ∘ q2cFPt_blockRevI hd) = w
      ext i
      simp [glLin_apply, revBlocks_coe hd, Matrix.permMatrix_mulVec]
      show w (q2cFPt_blockRevI hd (q2cFPt_blockRevI hd i)) = w i
      rw [hinv i]

private theorem pst_mem_map_rev_iff (hd : IsCut n d) {b s : ℕ} (hb : b + 1 < d.length)
    (hs : s ≤ blockSize d b) (w : Fin n → K) :
    w ∈ (Vsub n (d.getD b 0 + s)).map (glLin (revBlocks K n d)).toLinearMap ↔
      (∀ i : Fin n, d.getD b 0 ≤ i.val → i.val < d.getD (b + 1) 0 - s → w i = 0) ∧
        (∀ i : Fin n, d.getD (b + 1) 0 ≤ i.val → w i = 0) := by
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := (hd.strict b hb).le
  have hsle : s ≤ d.getD (b + 1) 0 - d.getD b 0 := by simpa only [blockSize] using hs
  rw [pst_mem_map_glLin_rev_iff hd]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hlo hhi
      apply h
      rw [q2cFPt_blockRevI_apply, q2cFPt_blockRev_val_of_block hd hb hlo (by omega)]
      omega
    · intro i hhi
      apply h
      rw [q2cFPt_blockRevI_apply]
      have hge : d.getD (b + 1) 0 ≤ (q2cFPt_blockRev hd i).val := by
        by_contra hlt
        exact (not_lt.2 hhi) ((q2cFPt_blockRev_prefix hd hb i).mp (not_le.1 hlt))
      omega
  · rintro ⟨h1, h2⟩ i hi
    rw [q2cFPt_blockRevI_apply] at hi
    by_cases hilo : i.val < d.getD b 0
    · have hblt : b < d.length := by omega
      have hlt := (q2cFPt_blockRev_prefix hd hblt i).mpr hilo
      omega
    · by_cases hihi : i.val < d.getD (b + 1) 0
      · have hval := q2cFPt_blockRev_val_of_block hd hb (not_lt.1 hilo) hihi
        rw [hval] at hi
        exact h1 i (not_lt.1 hilo) (by omega)
      · exact h2 i (not_lt.1 hihi)

private theorem pst_perpB_Vsub_inf_map_rev (hd : IsCut n d) {b s : ℕ} (hb : b + 1 < d.length)
    (hs : s ≤ blockSize d b) :
    perpB K f n (d.getD b 0) (d.getD (b + 1) 0)
        (Vsub n (d.getD b 0 + (blockSize d b - s))) ⊓ Vsub n (d.getD (b + 1) 0)
      = (Vsub n (d.getD b 0 + s)).map (glLin (revBlocks K n d)).toLinearMap := by
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := (hd.strict b hb).le
  have hsle : s ≤ d.getD (b + 1) 0 - d.getD b 0 := by simpa only [blockSize] using hs
  have harg : d.getD b 0 + (blockSize d b - s) = d.getD (b + 1) 0 - s := by
    simp only [blockSize]; omega
  rw [harg]
  ext v
  rw [Submodule.mem_inf, pst_mem_Vsub_iff, pst_mem_perpB_Vsub_iff (by omega) (by omega),
    pst_mem_map_rev_iff hd hb hs]

private theorem pst_psiSub_size_one_zero (hd : IsCut n d) (pol : List Bool) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {b : ℕ} (hb : b + 1 < d.length) (hbs : blockSize d b = 1) :
    psiSub f n d pol x.E b 0 = Vsub n (d.getD b 0) := by
  have hb' : b < d.length := by omega
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := (hd.strict b hb).le
  rw [psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp]
    have harg : d.getD b 0 + (blockSize d b - 0) = d.getD (b + 1) 0 := by
      simp only [blockSize] at hbs ⊢; omega
    rw [harg, hx (b + 1) hb, inf_comm]
    exact q2cFS_perpB_Vsub_inf hle
  · rw [if_neg hp, Nat.add_zero, hx b hb', sgS_Vsub]

private theorem pst_psiSub_size_one_one (hd : IsCut n d) (pol : List Bool) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {b : ℕ} (hb : b + 1 < d.length) (hbs : blockSize d b = 1) :
    psiSub f n d pol x.E b 1 = Vsub n (d.getD (b + 1) 0) := by
  have hb' : b < d.length := by omega
  rw [psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp]
    have harg : d.getD b 0 + (blockSize d b - 1) = d.getD b 0 := by
      simp only [blockSize] at hbs ⊢; omega
    rw [harg, hx b hb', q2cFS_perpB_Vsub_lo_eq_top, top_inf_eq]
  · rw [if_neg hp]
    have harg : d.getD b 0 + 1 = d.getD (b + 1) 0 := by
      simp only [blockSize] at hbs; omega
    rw [harg, hx (b + 1) hb, sgS_Vsub]

private theorem pst_psiSub_size_one (hd : IsCut n d) (pol pol' : List Bool) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {b s : ℕ} (hb : b + 1 < d.length) (hbs : blockSize d b = 1)
    (hs : s ≤ 1) :
    psiSub f n d pol x.E b s = psiSub f n d pol' x.E b s := by
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0
    rw [pst_psiSub_size_one_zero hd pol hx hb hbs,
      pst_psiSub_size_one_zero hd pol' hx hb hbs]
  · have hs1 : s = 1 := by omega
    subst hs1
    rw [pst_psiSub_size_one_one hd pol hx hb hbs,
      pst_psiSub_size_one_one hd pol' hx hb hbs]

theorem flagPsi_stdFlag_pol (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d) :
    flagPsi hK hd (List.replicate (d.length - 1) true) (stdFlag K n) =
      flagAct (revBlocks K n d) (stdFlag K n) := by
  have hstd_mem : stdFlag K n ∈ refSet K n d := stdFlag_mem_refSet hd
  apply FlagK.ext
  intro j
  by_cases hjn : j < n
  · set b := plr_cutBlock d j with hb_def
    set s := j - d.getD b 0 with hs_def
    have hb : b + 1 < d.length := by
      rw [hb_def]; have := plr_cutBlock_lt_of_lt hd hjn; omega
    have hs : s ≤ blockSize d b := by
      rw [hs_def, hb_def]
      have := plr_lt_cutBlock_succ hd hjn
      simp only [blockSize]; omega
    have hjeq : j = d.getD b 0 + s := by
      rw [hs_def]
      have := plr_cutBlock_le hd j
      rw [← hb_def] at this
      omega
    have hpol : (List.replicate (d.length - 1) true).getD b false = true :=
      List.getD_replicate true (by omega)
    rw [hjeq, flagPsi_E hK hd _ hstd_mem hb hs]
    rw [psiSub, if_pos hpol]
    rw [flagAct, flagMap_E]
    change perpB K f n (d.getD b 0) (d.getD (b + 1) 0)
        (Vsub n (d.getD b 0 + (blockSize d b - s))) ⊓ Vsub n (d.getD (b + 1) 0)
      = (Vsub n (d.getD b 0 + s)).map (glLin (revBlocks K n d)).toLinearMap
    exact pst_perpB_Vsub_inf_map_rev hd hb hs
  · rw [FlagK.top _ j (by omega), FlagK.top _ j (by omega)]

theorem flagPsi_eq_of_pol_eq (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (pol pol' : List Bool) (h : ∀ b, b + 1 < d.length → 2 ≤ blockSize d b →
      pol.getD b false = pol'.getD b false) {x : FlagK K n} (hx : x ∈ refSet K n d) :
    flagPsi hK hd pol x = flagPsi hK hd pol' x := by
  apply FlagK.ext
  intro j
  by_cases hjn : j < n
  · set b := plr_cutBlock d j with hb_def
    set s := j - d.getD b 0 with hs_def
    have hb : b + 1 < d.length := by
      rw [hb_def]; have := plr_cutBlock_lt_of_lt hd hjn; omega
    have hs : s ≤ blockSize d b := by
      rw [hs_def, hb_def]
      have := plr_lt_cutBlock_succ hd hjn
      simp only [blockSize]; omega
    have hjeq : j = d.getD b 0 + s := by
      rw [hs_def]
      have := plr_cutBlock_le hd j
      rw [← hb_def] at this
      omega
    rw [hjeq, flagPsi_E hK hd pol hx hb hs, flagPsi_E hK hd pol' hx hb hs]
    by_cases h2 : 2 ≤ blockSize d b
    · simp only [psiSub, h b hb h2]
    · have hbs : blockSize d b = 1 := by
        have h1 : 1 ≤ blockSize d b := by
          simp only [blockSize]; have := hd.strict b hb; omega
        omega
      exact pst_psiSub_size_one hd pol pol' hx hb hbs (by omega)
  · rw [FlagK.top _ j (by omega), FlagK.top _ j (by omega)]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

end
