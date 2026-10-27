module

public import CFSG.LocalAnalysis.StandardType.PhanEResBlockDiag
public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsi

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
open scoped Matrix

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {d : List ℕ}

private def plr_blockFS (lo hi : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => lo ≤ i.val ∧ i.val < hi

private theorem plr_hermLin_apply (lo hi : ℕ) (u v : Fin n → K) :
    hermLin K f n lo hi u v = ∑ i ∈ plr_blockFS (n := n) lo hi, sg K f (u i) * v i := by
  rw [hermLin, LinearMap.sum_apply]
  rw [show (∑ i : Fin n, (if lo ≤ i.val ∧ i.val < hi then (sg K f (u i)) • LinearMap.proj i
        else 0) v) = ∑ i : Fin n, if lo ≤ i.val ∧ i.val < hi then sg K f (u i) * v i else 0 from
    Finset.sum_congr rfl fun i _ => by by_cases h : lo ≤ i.val ∧ i.val < hi <;> simp [h]]
  rw [plr_blockFS, ← Finset.sum_filter]

private theorem plr_mem_perpB_iff (lo hi : ℕ) (U : Submodule K (Fin n → K)) (v : Fin n → K) :
    v ∈ perpB K f n lo hi U ↔ ∀ u ∈ U, hermLin K f n lo hi u v = 0 := by
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem plr_hermLin_glLin {lo hi : ℕ} {g : GL (Fin n) K}
    (hblock : plr_BlockOne n lo hi (g : Matrix (Fin n) (Fin n) K)) (u v : Fin n → K) :
    hermLin K f n lo hi (glLin g u) v =
      hermLin K f n lo hi u
        (((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose *ᵥ v) := by
  rw [plr_hermLin_apply, plr_hermLin_apply]
  have hL : ∀ i, sg K f ((glLin g u) i) = ∑ k, sg K f ((g : Matrix (Fin n) (Fin n) K) i k) *
      sg K f (u k) := by
    intro i
    rw [glLin_apply, Matrix.mulVec_apply_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul]
  have hR : ∀ k, (((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose *ᵥ v) k =
      ∑ i, sg K f ((g : Matrix (Fin n) (Fin n) K) i k) * v i := by
    intro k
    rw [Matrix.mulVec_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.transpose_apply, Matrix.map_apply]; rfl
  set S := plr_blockFS (n := n) lo hi
  calc ∑ i ∈ S, sg K f ((glLin g u) i) * v i
      = ∑ i ∈ S, (∑ k, sg K f ((g : Matrix (Fin n) (Fin n) K) i k) * sg K f (u k)) * v i :=
        Finset.sum_congr rfl fun i _ => by rw [hL i]
    _ = ∑ i ∈ S, ∑ k, sg K f ((g : Matrix (Fin n) (Fin n) K) i k) * sg K f (u k) * v i :=
        Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ = ∑ i ∈ S, ∑ k ∈ S, sg K f ((g : Matrix (Fin n) (Fin n) K) i k) * sg K f (u k) * v i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        intro k _ hkS
        have hgik : (g : Matrix (Fin n) (Fin n) K) i k = 0 :=
          (hblock i k (by simpa [S, plr_blockFS] using hi)
            (by simpa [S, plr_blockFS] using hkS)).1
        rw [hgik, map_zero, zero_mul, zero_mul]
    _ = ∑ k ∈ S, ∑ i ∈ S, sg K f ((g : Matrix (Fin n) (Fin n) K) i k) * sg K f (u k) * v i :=
        Finset.sum_comm
    _ = ∑ k ∈ S, ∑ i ∈ S, sg K f (u k) * sg K f ((g : Matrix (Fin n) (Fin n) K) i k) * v i :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k ∈ S, sg K f (u k) * (∑ i ∈ S,
          sg K f ((g : Matrix (Fin n) (Fin n) K) i k) * v i) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k ∈ S, sg K f (u k) * (∑ i,
          sg K f ((g : Matrix (Fin n) (Fin n) K) i k) * v i) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        congr 1
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        intro i _ hiS
        have hgik : (g : Matrix (Fin n) (Fin n) K) i k = 0 :=
          (hblock k i (by simpa [S, plr_blockFS] using hk)
            (by
              intro h
              exact hiS (by simpa [S, plr_blockFS] using h))).2
        rw [hgik, map_zero, zero_mul]
    _ = ∑ k ∈ S, sg K f (u k) *
          (((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose *ᵥ v) k :=
        Finset.sum_congr rfl fun k _ => by rw [hR k]

private theorem plr_perpB_map (hK : Nat.card K = (2 ^ f) ^ 2) {lo hi : ℕ} {g g' : GL (Fin n) K}
    (hblock : plr_BlockOne n lo hi (g : Matrix (Fin n) (Fin n) K))
    (hgg' : (g' : Matrix (Fin n) (Fin n) K) *
      ((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose = 1)
    (U : Submodule K (Fin n → K)) :
    perpB K f n lo hi (U.map (glLin g).toLinearMap) =
      (perpB K f n lo hi U).map (glLin g').toLinearMap := by
  have hgg'' : ((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose *
      (g' : Matrix (Fin n) (Fin n) K) = 1 := mul_eq_one_comm.mp hgg'
  ext v
  rw [plr_mem_perpB_iff, Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose *ᵥ v, ?_, ?_⟩
    · rw [plr_mem_perpB_iff]
      intro u hu
      rw [← plr_hermLin_glLin hblock u v]
      exact hv (glLin g u) ⟨u, hu, rfl⟩
    · change glLin g' (((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose *ᵥ v) = v
      rw [glLin_apply, Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  · rintro ⟨w, hw, rfl⟩
    intro u hu
    rw [Submodule.mem_map] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have h2 : (((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose *ᵥ
        glLin g' w) = w := by
      rw [glLin_apply, Matrix.mulVec_mulVec, hgg'', Matrix.one_mulVec]
    change hermLin K f n lo hi (glLin g x) (glLin g' w) = 0
    rw [plr_hermLin_glLin hblock x (glLin g' w), h2]
    exact (plr_mem_perpB_iff lo hi U w).mp hw x hx

private theorem plr_sgv_glLin {g g' : GL (Fin n) K}
    (hgg' : ∀ i j, (g' : Matrix (Fin n) (Fin n) K) i j =
      sg K f ((g : Matrix (Fin n) (Fin n) K) i j)) (u : Fin n → K) :
    sgv K f n (glLin g u) = glLin g' (sgv K f n u) := by
  ext i
  rw [sgv_apply, glLin_apply, glLin_apply, Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum,
    map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hgg', sgv_apply]

private theorem plr_sgS_map (hK : Nat.card K = (2 ^ f) ^ 2) {g g' : GL (Fin n) K}
    (hgg' : ∀ i j, (g' : Matrix (Fin n) (Fin n) K) i j =
      sg K f ((g : Matrix (Fin n) (Fin n) K) i j))
    (U : Submodule K (Fin n → K)) :
    sgS K f n (U.map (glLin g).toLinearMap) = (sgS K f n U).map (glLin g').toLinearMap := by
  ext v
  rw [mem_sgS, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, hgu⟩
    refine ⟨sgv K f n u, ?_, ?_⟩
    · rw [mem_sgS, sgv_sgv hK]; exact hu
    · change glLin g' (sgv K f n u) = v
      rw [← plr_sgv_glLin hgg' u]
      have hgu' : glLin g u = sgv K f n v := hgu
      change (sgv K f n) (glLin g u) = v
      rw [hgu', sgv_sgv hK]
  · rintro ⟨w, hw, hgw⟩
    refine ⟨sgv K f n w, ?_, ?_⟩
    · exact (mem_sgS (U := U) (v := w)).mp hw
    · have h2 : sgv K f n (glLin g (sgv K f n w)) = glLin g' w := by
        rw [plr_sgv_glLin hgg' (sgv K f n w), sgv_sgv hK w]
      have h3 : glLin g (sgv K f n w) = sgv K f n (glLin g' w) := by
        have h4 := congrArg (sgv K f n) h2
        rwa [sgv_sgv hK] at h4
      have hgw' : glLin g' w = v := hgw
      change glLin g (sgv K f n w) = sgv K f n v
      rw [h3]
      change sgv K f n (glLin g' w) = sgv K f n v
      rw [hgw']

theorem flagPsi_flagAct_coll (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (g g' : GL (Fin n) K) (hg : BlockDiag d (g : Matrix (Fin n) (Fin n) K))
    (hgg' : ∀ i j, (g' : Matrix (Fin n) (Fin n) K) i j =
      sg K f ((g : Matrix (Fin n) (Fin n) K) i j))
    {x : FlagK K n} (hx : x ∈ refSet K n d) :
    flagPsi hK hd (List.replicate (d.length - 1) false) (flagAct g x) =
      flagAct g' (flagPsi hK hd (List.replicate (d.length - 1) false) x) := by
  have hmemg : flagAct g x ∈ refSet K n d :=
    flagMap_mem_refSet (glLin g) (fun i hi => BlockDiag.stabV hd hg i hi) hx
  apply FlagK.ext
  intro j
  by_cases hjn : j < n
  · have hb : plr_cutBlock d j + 1 < d.length := by
      have := plr_cutBlock_lt_of_lt hd hjn; omega
    have hs : j - d.getD (plr_cutBlock d j) 0 ≤ blockSize d (plr_cutBlock d j) := by
      have := plr_lt_cutBlock_succ hd hjn; simp only [blockSize]; omega
    have hjeq : j = d.getD (plr_cutBlock d j) 0 + (j - d.getD (plr_cutBlock d j) 0) := by
      have := plr_cutBlock_le hd j; omega
    have hpol : (List.replicate (d.length - 1) false).getD (plr_cutBlock d j) false = false :=
      List.getD_replicate false (by omega)
    have hne : ¬ ((List.replicate (d.length - 1) false).getD (plr_cutBlock d j) false = true) := by
      rw [hpol]; exact Bool.false_ne_true
    rw [hjeq, flagPsi_E hK hd _ hmemg hb hs]
    simp only [flagAct, flagMap_E]
    rw [flagPsi_E hK hd _ hx hb hs]
    rw [psiSub, if_neg hne, psiSub, if_neg hne]
    have hmap : (flagMap (glLin g) x).E
          (d.getD (plr_cutBlock d j) 0 + (j - d.getD (plr_cutBlock d j) 0)) =
        Submodule.map (glLin g).toLinearMap
          (x.E (d.getD (plr_cutBlock d j) 0 + (j - d.getD (plr_cutBlock d j) 0))) :=
      flagMap_E _ _ _
    rw [hmap]
    exact plr_sgS_map hK hgg'
      (x.E (d.getD (plr_cutBlock d j) 0 + (j - d.getD (plr_cutBlock d j) 0)))
  · rw [FlagK.top _ j (by omega), FlagK.top _ j (by omega)]

private theorem plr_BlockDiag_map {A : Matrix (Fin n) (Fin n) K} (hA : BlockDiag d A) :
    BlockDiag d (A.map (sg K f : K →+* K)) := by
  intro b hb i j hi hj
  exact ⟨by rw [Matrix.map_apply, (hA b hb i j hi hj).1, map_zero],
    by rw [Matrix.map_apply, (hA b hb i j hi hj).2, map_zero]⟩

private theorem plr_BlockDiag_transpose {A : Matrix (Fin n) (Fin n) K} (hA : BlockDiag d A) :
    BlockDiag d A.transpose := by
  intro b hb i j hi hj
  exact ⟨(hA b hb i j hi hj).2, (hA b hb i j hi hj).1⟩

theorem flagPsi_flagAct_pol (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (g g' : GL (Fin n) K) (hg : BlockDiag d (g : Matrix (Fin n) (Fin n) K))
    (hgg' : (g' : Matrix (Fin n) (Fin n) K) *
      ((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose = 1)
    {x : FlagK K n} (hx : x ∈ refSet K n d) :
    flagPsi hK hd (List.replicate (d.length - 1) true) (flagAct g x) =
      flagAct g' (flagPsi hK hd (List.replicate (d.length - 1) true) x) := by
  have hmemg : flagAct g x ∈ refSet K n d :=
    flagMap_mem_refSet (glLin g) (fun i hi => BlockDiag.stabV hd hg i hi) hx
  have hAmat : BlockDiag d
      (((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose) :=
    plr_BlockDiag_transpose (plr_BlockDiag_map hg)
  have hgg'' : ((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose *
      (g' : Matrix (Fin n) (Fin n) K) = 1 := mul_eq_one_comm.mp hgg'
  have hg' : BlockDiag d (g' : Matrix (Fin n) (Fin n) K) := by
    let A : GL (Fin n) K :=
      ⟨((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)).transpose,
        (g' : Matrix (Fin n) (Fin n) K), hgg'', hgg'⟩
    simpa [A] using BlockDiag.inv (d := d) (g := A) hAmat
  apply FlagK.ext
  intro j
  by_cases hjn : j < n
  · set b := plr_cutBlock d j with hb_def
    set s := j - d.getD b 0 with hs_def
    have hb : b + 1 < d.length := by
      rw [hb_def]; have := plr_cutBlock_lt_of_lt hd hjn; omega
    have hs : s ≤ blockSize d b := by
      rw [hs_def, hb_def]; have := plr_lt_cutBlock_succ hd hjn; simp only [blockSize]; omega
    have hjeq : j = d.getD b 0 + s := by
      rw [hs_def]
      have := plr_cutBlock_le hd j
      rw [← hb_def] at this
      omega
    have hpol : (List.replicate (d.length - 1) true).getD b false = true :=
      List.getD_replicate true (by omega)
    rw [hjeq, flagPsi_E hK hd _ hmemg hb hs]
    simp only [flagAct, flagMap_E]
    rw [flagPsi_E hK hd _ hx hb hs]
    rw [psiSub, if_pos hpol, psiSub, if_pos hpol]
    have hmap : (flagMap (glLin g) x).E (d.getD b 0 + (blockSize d b - s)) =
        Submodule.map (glLin g).toLinearMap (x.E (d.getD b 0 + (blockSize d b - s))) :=
      flagMap_E _ _ _
    rw [hmap]
    rw [plr_perpB_map hK (hg b hb) hgg' (x.E (d.getD b 0 + (blockSize d b - s)))]
    conv_lhs => rw [← BlockDiag.stabV hd hg' (b + 1) hb]
    rw [← Submodule.map_inf (glLin g').toLinearMap (glLin g').injective]
  · rw [FlagK.top _ j (by omega), FlagK.top _ j (by omega)]

@[expose] noncomputable def revBlocks (K : Type) [Field K] (n : ℕ) (d : List ℕ) :
    GL (Fin n) K := by
  classical
  exact if h : IsCut n d then
    let R : Matrix (Fin n) (Fin n) K := (q2cFPt_blockRevI h).permMatrix K
    have hR : R * R = 1 := by
      have hσσ : (q2cFPt_blockRevI h) * (q2cFPt_blockRevI h) = 1 := by
        ext k
        simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
        simpa [q2cFPt_blockRevI_apply] using congrArg Fin.val (q2cFPt_blockRev_involutive h k)
      rw [show R * R = ((q2cFPt_blockRevI h) * (q2cFPt_blockRevI h)).permMatrix K by
        rw [Matrix.permMatrix_mul]]
      rw [hσσ]
      simp
    ⟨R, R, hR, hR⟩
  else 1

theorem revBlocks_blockDiag (hd : IsCut n d) :
    BlockDiag d ((revBlocks K n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [revBlocks, dif_pos hd]
  intro b hb i j hi hj
  constructor
  · have hrev_mem : d.getD b 0 ≤ (q2cFPt_blockRev hd i).val ∧
        (q2cFPt_blockRev hd i).val < d.getD (b + 1) 0 := by
      constructor
      · by_contra h
        have hlt : (q2cFPt_blockRev hd i).val < d.getD b 0 := not_le.mp h
        have hklt : i.val < d.getD b 0 := (q2cFPt_blockRev_prefix hd (by omega) i).mp hlt
        omega
      · exact (q2cFPt_blockRev_prefix hd hb i).mpr (by omega)
    have h_eq : (q2cFPt_blockRevI hd) i = j → False := by
      intro h
      have hval : (q2cFPt_blockRev hd i).val = j.val := by
        rw [← q2cFPt_blockRevI_apply hd i]
        exact congrArg Fin.val h
      exact hj (by rw [← hval]; exact hrev_mem)
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [if_neg]
    intro h
    exact h_eq (by simpa using h)
  · have hrev_mem : ¬ (d.getD b 0 ≤ (q2cFPt_blockRev hd j).val ∧
        (q2cFPt_blockRev hd j).val < d.getD (b + 1) 0) := by
      intro hmem
      have hjlt : j.val < d.getD b 0 ∨ d.getD (b + 1) 0 ≤ j.val := by
        by_contra h
        push Not at h
        exact hj h
      rcases hjlt with hjlt | hjge
      · have hrevlt : (q2cFPt_blockRev hd j).val < d.getD b 0 :=
          (q2cFPt_blockRev_prefix hd (by omega) j).mpr hjlt
        omega
      · have hrevge : d.getD (b + 1) 0 ≤ (q2cFPt_blockRev hd j).val := by
          by_contra h
          have hlt : (q2cFPt_blockRev hd j).val < d.getD (b + 1) 0 := not_le.mp h
          have hklt : j.val < d.getD (b + 1) 0 :=
            (q2cFPt_blockRev_prefix hd hb j).mp hlt
          omega
        omega
    have h_eq : (q2cFPt_blockRevI hd) j = i → False := by
      intro h
      have hval : (q2cFPt_blockRev hd j).val = i.val := by
        rw [← q2cFPt_blockRevI_apply hd j]
        exact congrArg Fin.val h
      exact hrev_mem ⟨by omega, by omega⟩
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [if_neg]
    intro h
    exact h_eq (by simpa using h)

theorem revBlocks_mul_self (hd : IsCut n d) : revBlocks K n d * revBlocks K n d = 1 := by
  rw [revBlocks, dif_pos hd]
  have hσσ : (q2cFPt_blockRevI hd) * (q2cFPt_blockRevI hd) = 1 := by
    rw [← q2cFPt_blockRevI_inv hd]
    exact mul_inv_cancel _
  have hR : (q2cFPt_blockRevI hd).permMatrix K * (q2cFPt_blockRevI hd).permMatrix K = 1 := by
    rw [← Matrix.permMatrix_mul, hσσ, Matrix.permMatrix_one]
  ext <;> simp [hR, Matrix.GeneralLinearGroup.coe_mul]

theorem flagPsi_stdFlag_coll (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d) :
    flagPsi hK hd (List.replicate (d.length - 1) false) (stdFlag K n) = stdFlag K n := by
  have hstd_mem : stdFlag K n ∈ refSet K n d := by
    intro b hb
    rfl
  apply FlagK.ext
  intro j
  by_cases hjn : j < n
  · have hb : plr_cutBlock d j + 1 < d.length := by
      have := plr_cutBlock_lt_of_lt hd hjn; omega
    have hs : j - d.getD (plr_cutBlock d j) 0 ≤ blockSize d (plr_cutBlock d j) := by
      have := plr_lt_cutBlock_succ hd hjn; simp only [blockSize]; omega
    have hjeq : j = d.getD (plr_cutBlock d j) 0 + (j - d.getD (plr_cutBlock d j) 0) := by
      have := plr_cutBlock_le hd j; omega
    have hpol : (List.replicate (d.length - 1) false).getD (plr_cutBlock d j) false = false :=
      List.getD_replicate false (by omega)
    have hne : ¬ ((List.replicate (d.length - 1) false).getD (plr_cutBlock d j) false = true) := by
      rw [hpol]; exact Bool.false_ne_true
    rw [hjeq, flagPsi_E hK hd _ hstd_mem hb hs]
    rw [psiSub, if_neg hne]
    rw [show (stdFlag K n).E (d.getD (plr_cutBlock d j) 0 + (j - d.getD (plr_cutBlock d j) 0)) =
        Vsub n (d.getD (plr_cutBlock d j) 0 + (j - d.getD (plr_cutBlock d j) 0)) from rfl]
    rw [sgS_Vsub]
  · rw [FlagK.top _ j (by omega), FlagK.top _ j (by omega)]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

end
