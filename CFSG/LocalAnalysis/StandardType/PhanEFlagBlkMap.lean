module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagAct
public import CFSG.LocalAnalysis.StandardType.PhanEFlagAsm
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n : ℕ} {d : List ℕ}

@[expose] def StabV (n : ℕ) (d : List ℕ) (g : GL (Fin n) K) : Prop :=
  ∀ i, i < d.length → (Vsub n (d.getD i 0)).map (glLin g).toLinearMap = Vsub n (d.getD i 0)

private theorem q2cFBM_glLin_mul (g h : GL (Fin n) K) :
    glLin (g * h) = (glLin h).trans (glLin g) := by
  ext v
  rw [glLin_apply, LinearEquiv.trans_apply, glLin_apply, glLin_apply,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

private theorem q2cFBM_glLin_one :
    glLin (1 : GL (Fin n) K) = LinearEquiv.refl K (Fin n → K) := by
  ext v
  rw [glLin_apply]
  simp

private theorem q2cFBM_glLin_inv (g : GL (Fin n) K) : glLin g⁻¹ = (glLin g).symm := by
  have h : (glLin g).trans (glLin g⁻¹) = LinearEquiv.refl K (Fin n → K) := by
    rw [← q2cFBM_glLin_mul, inv_mul_cancel, q2cFBM_glLin_one]
  have hv : ∀ w, glLin g⁻¹ (glLin g w) = w := by
    intro w
    simpa [LinearEquiv.trans_apply] using
      congrArg (fun e : (Fin n → K) ≃ₗ[K] (Fin n → K) => e w) h
  apply LinearEquiv.ext
  intro v
  calc glLin g⁻¹ v = glLin g⁻¹ (glLin g ((glLin g).symm v)) := by
        rw [(glLin g).apply_symm_apply]
    _ = (glLin g).symm v := hv _

theorem StabV.mul {g h : GL (Fin n) K} (hg : StabV n d g) (hh : StabV n d h) :
    StabV n d (g * h) := by
  intro i hi
  rw [q2cFBM_glLin_mul]
  change (Vsub n (d.getD i 0)).map
      ((glLin g).toLinearMap.comp (glLin h).toLinearMap) = Vsub n (d.getD i 0)
  rw [Submodule.map_comp, hh i hi, hg i hi]

theorem StabV.inv {g : GL (Fin n) K} (hg : StabV n d g) : StabV n d g⁻¹ := by
  intro i hi
  rw [q2cFBM_glLin_inv]
  have h := congrArg (Submodule.map (glLin g).symm.toLinearMap) (hg i hi)
  rw [← Submodule.map_comp] at h
  have hcomp : ((glLin g).symm.toLinearMap.comp (glLin g).toLinearMap :
      (Fin n → K) →ₗ[K] (Fin n → K)) = LinearMap.id := by
    ext v; simp
  rw [hcomp, Submodule.map_id] at h
  exact h.symm

theorem StabV.flagAct_mem_refSet {g : GL (Fin n) K} (hg : StabV n d g) {x : FlagK K n}
    (hx : x ∈ refSet K n d) : flagAct g x ∈ refSet K n d := by
  show flagMap (glLin g) x ∈ refSet K n d
  exact flagMap_mem_refSet (glLin g) hg hx

@[expose] def blkOut (n : ℕ) (d : List ℕ) (b : ℕ) :
    (Fin n → K) →ₗ[K] (Fin (blockSize d b) → K) where
  toFun v t := if h : d.getD b 0 + t.val < n then v ⟨d.getD b 0 + t.val, h⟩ else 0
  map_add' v w := by
    ext t
    by_cases h : d.getD b 0 + t.val < n
    · simp only [Pi.add_apply, dif_pos h]
    · simp only [Pi.add_apply, dif_neg h, add_zero]
  map_smul' c v := by
    ext t
    by_cases h : d.getD b 0 + t.val < n
    · simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, dif_pos h]
    · simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, dif_neg h, mul_zero]

@[expose] def blkIn (n : ℕ) (d : List ℕ) (b : ℕ) :
    (Fin (blockSize d b) → K) →ₗ[K] (Fin n → K) where
  toFun w k :=
    if h : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0 then
      w ⟨k.val - d.getD b 0, by simp only [blockSize]; omega⟩
    else 0
  map_add' v w := by
    ext k
    by_cases h : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0
    · simp only [Pi.add_apply, dif_pos h]
    · simp only [Pi.add_apply, dif_neg h, add_zero]
  map_smul' c v := by
    ext k
    by_cases h : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0
    · simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, dif_pos h]
    · simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, dif_neg h, mul_zero]

private theorem q2cFBM_blkOut_apply (n : ℕ) (d : List ℕ) (b : ℕ) (v : Fin n → K)
    (t : Fin (blockSize d b)) :
    blkOut n d b v t =
      if h : d.getD b 0 + t.val < n then v ⟨d.getD b 0 + t.val, h⟩ else 0 := rfl

private theorem q2cFBM_blkIn_apply (n : ℕ) (d : List ℕ) (b : ℕ)
    (w : Fin (blockSize d b) → K) (k : Fin n) :
    blkIn n d b w k =
      if h : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0 then
        w ⟨k.val - d.getD b 0, by simp only [blockSize]; omega⟩ else 0 := rfl

theorem blkOut_blkIn (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (w : Fin (blockSize d b) → K) : blkOut n d b (blkIn n d b w) = w := by
  ext t
  rw [q2cFBM_blkOut_apply]
  have ht : d.getD b 0 + t.val < d.getD (b + 1) 0 := by
    have h := hd.strict b hb
    have := t.isLt
    simp only [blockSize] at this
    omega
  have hn : d.getD b 0 + t.val < n := lt_of_lt_of_le ht (q2cFPt_le_last hd hb)
  rw [dif_pos hn, q2cFBM_blkIn_apply, dif_pos ⟨Nat.le_add_right _ _, ht⟩]
  congr 1
  ext
  simp

theorem blkOut_blkIn_of_ne (hd : IsCut n d) {b b' : ℕ} (hb : b + 1 < d.length)
    (hb' : b' + 1 < d.length) (hne : b ≠ b') (w : Fin (blockSize d b') → K) :
    blkOut n d b (blkIn n d b' w) = 0 := by
  ext t
  rw [q2cFBM_blkOut_apply]
  have ht : d.getD b 0 + t.val < d.getD (b + 1) 0 := by
    have h := hd.strict b hb
    have := t.isLt
    simp only [blockSize] at this
    omega
  by_cases hn : d.getD b 0 + t.val < n
  · rw [dif_pos hn, q2cFBM_blkIn_apply]
    have hnc : ¬ (d.getD b' 0 ≤ (⟨d.getD b 0 + t.val, hn⟩ : Fin n).val ∧
        (⟨d.getD b 0 + t.val, hn⟩ : Fin n).val < d.getD (b' + 1) 0) := by
      rintro ⟨h1, h2⟩
      simp only [Fin.val_mk] at h1 h2
      rcases lt_or_gt_of_ne hne with hbb | hbb
      · have hle := q2cFPt_getD_le hd (i := b + 1) (j := b') (by omega)
          (by omega : b' < d.length)
        omega
      · have hle := q2cFPt_getD_le hd (i := b' + 1) (j := b) (by omega)
          (by omega : b < d.length)
        omega
    rw [dif_neg hnc]
    rfl
  · rw [dif_neg hn]
    rfl

theorem blkOut_of_mem_Vsub {b : ℕ} {v : Fin n → K} (hv : v ∈ Vsub n (d.getD b 0)) :
    blkOut n d b v = 0 := by
  ext t
  rw [q2cFBM_blkOut_apply]
  by_cases hn : d.getD b 0 + t.val < n
  · rw [dif_pos hn, hv ⟨d.getD b 0 + t.val, hn⟩ (Nat.le_add_right _ _)]
    rfl
  · rw [dif_neg hn]
    rfl

theorem blkIn_mem_Vsub {b : ℕ} (w : Fin (blockSize d b) → K) :
    blkIn n d b w ∈ Vsub n (d.getD (b + 1) 0) := by
  intro k hk
  rw [q2cFBM_blkIn_apply]
  exact dif_neg (fun hc => not_lt_of_ge hk hc.2)

theorem sub_blkIn_blkOut_mem_Vsub (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    {v : Fin n → K} (hv : v ∈ Vsub n (d.getD (b + 1) 0)) :
    v - blkIn n d b (blkOut n d b v) ∈ Vsub n (d.getD b 0) := by
  intro k hk
  change v k - blkIn n d b (blkOut n d b v) k = 0
  by_cases hlt : k.val < d.getD (b + 1) 0
  · have hkb : d.getD b 0 + (k.val - d.getD b 0) = k.val := Nat.add_sub_of_le hk
    have hbnd : d.getD b 0 + (k.val - d.getD b 0) < n := by rw [hkb]; exact k.isLt
    have hcond : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0 := ⟨hk, hlt⟩
    rw [q2cFBM_blkIn_apply, dif_pos hcond, q2cFBM_blkOut_apply, dif_pos hbnd]
    have hidx : (⟨d.getD b 0 + (k.val - d.getD b 0), hbnd⟩ : Fin n) = k := by
      apply Fin.ext
      simpa only [Fin.val_mk] using hkb
    rw [hidx, sub_self]
  · rw [q2cFBM_blkIn_apply, dif_neg (fun hc => hlt hc.2), hv k (le_of_not_gt hlt), sub_zero]

theorem sum_blkIn_blkOut (hd : IsCut n d) (v : Fin n → K) :
    ∑ b ∈ Finset.range (d.length - 1), blkIn n d b (blkOut n d b v) = v := by
  ext k
  rw [Finset.sum_apply]
  set c := q2cFPt_nextCut hd k with hc
  have hc1 : 1 ≤ c := q2cFPt_nextCut_pos hd k
  have hcL : c < d.length := q2cFPt_nextCut_lt_length hd k
  obtain ⟨hlo, hhi⟩ := (q2cFPt_nextCut_eq_iff hd k hc1 hcL).mp rfl
  set b := c - 1 with hbdef
  have hbc : b + 1 = c := by omega
  have hbL : b + 1 < d.length := by omega
  have hlo' : d.getD b 0 ≤ k.val := by simpa [hbc] using hlo
  have hhi' : k.val < d.getD (b + 1) 0 := by simpa [hbc] using hhi
  have hbmem : b ∈ Finset.range (d.length - 1) := by
    simp only [Finset.mem_range]; omega
  have hsum : (∑ b' ∈ Finset.range (d.length - 1),
      blkIn n d b' (blkOut n d b' v) k) = blkIn n d b (blkOut n d b v) k := by
    refine Finset.sum_eq_single b ?_ ?_
    · intro b' hb'mem hne
      rw [q2cFBM_blkIn_apply]
      have hb'L : b' + 1 < d.length := by
        have := Finset.mem_range.mp hb'mem; omega
      have hnc : ¬ (d.getD b' 0 ≤ k.val ∧ k.val < d.getD (b' + 1) 0) := by
        rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle := q2cFPt_getD_le hd (i := b' + 1) (j := b) (by omega) (by omega)
          omega
        · have hle := q2cFPt_getD_le hd (i := b + 1) (j := b') (by omega)
            (by omega : b' < d.length)
          omega
      exact dif_neg hnc
    · intro hnot; exact absurd hbmem hnot
  rw [hsum]
  have hkb : d.getD b 0 + (k.val - d.getD b 0) = k.val := Nat.add_sub_of_le hlo'
  have hbnd : d.getD b 0 + (k.val - d.getD b 0) < n := by rw [hkb]; exact k.isLt
  have hcond : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0 := ⟨hlo', hhi'⟩
  rw [q2cFBM_blkIn_apply, dif_pos hcond, q2cFBM_blkOut_apply, dif_pos hbnd]
  have hidx : (⟨d.getD b 0 + (k.val - d.getD b 0), hbnd⟩ : Fin n) = k := by
    apply Fin.ext
    simpa only [Fin.val_mk] using hkb
  rw [hidx]

theorem eq_sup_map_blkIn (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    {X : Submodule K (Fin n → K)} (h₁ : Vsub n (d.getD b 0) ≤ X)
    (h₂ : X ≤ Vsub n (d.getD (b + 1) 0)) :
    X = Vsub n (d.getD b 0) ⊔ (X.map (blkOut n d b)).map (blkIn n d b) := by
  apply le_antisymm
  · intro v hv
    have hmem := sub_blkIn_blkOut_mem_Vsub hd hb (h₂ hv)
    have hblk : blkIn n d b (blkOut n d b v) ∈ (X.map (blkOut n d b)).map (blkIn n d b) :=
      Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hv)
    have hsum : (v - blkIn n d b (blkOut n d b v)) + blkIn n d b (blkOut n d b v) = v :=
      sub_add_cancel _ _
    exact Submodule.mem_sup.mpr
      ⟨v - blkIn n d b (blkOut n d b v), hmem,
        blkIn n d b (blkOut n d b v), hblk, hsum⟩
  · refine sup_le h₁ ?_
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    have hmem := sub_blkIn_blkOut_mem_Vsub hd hb (h₂ hv)
    have hEq : blkIn n d b (blkOut n d b v) = v - (v - blkIn n d b (blkOut n d b v)) := by
      abel
    rw [hEq]
    exact Submodule.sub_mem _ hv (h₁ hmem)

theorem map_blkOut_sup_map_blkIn (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (U : Submodule K (Fin (blockSize d b) → K)) :
    (Vsub n (d.getD b 0) ⊔ U.map (blkIn n d b)).map (blkOut n d b) = U := by
  apply le_antisymm
  · rw [Submodule.map_sup]
    apply sup_le
    · have hbot : (Vsub (K := K) n (d.getD b 0)).map (blkOut (K := K) n d b) = ⊥ := by
        rw [Submodule.eq_bot_iff]
        rintro v hv
        rw [Submodule.mem_map] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        exact blkOut_of_mem_Vsub hw
      rw [hbot]; exact bot_le
    · rw [← Submodule.map_comp]
      have hcomp : (blkOut (K := K) n d b).comp (blkIn (K := K) n d b) =
          (LinearMap.id : (Fin (blockSize d b) → K) →ₗ[K] (Fin (blockSize d b) → K)) := by
        apply LinearMap.ext
        intro w
        exact blkOut_blkIn hd hb w
      rw [hcomp, Submodule.map_id]
  · intro u hu
    rw [Submodule.mem_map]
    exact ⟨blkIn n d b u,
      Submodule.mem_sup_right (Submodule.mem_map_of_mem hu), blkOut_blkIn hd hb u⟩

theorem sup_map_blkIn_le_Vsub (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (U : Submodule K (Fin (blockSize d b) → K)) :
    Vsub n (d.getD b 0) ⊔ U.map (blkIn n d b) ≤ Vsub n (d.getD (b + 1) 0) := by
  apply sup_le
  · exact Vsub_mono (hd.strict b hb).le
  · rintro w ⟨u, _, rfl⟩
    exact blkIn_mem_Vsub u

theorem refSet_E_mem_interval (hd : IsCut n d) {x : FlagK K n} (hx : x ∈ refSet K n d) {b s : ℕ}
    (hb : b + 1 < d.length) (hs : s ≤ blockSize d b) :
    Vsub n (d.getD b 0) ≤ x.E (d.getD b 0 + s) ∧
      x.E (d.getD b 0 + s) ≤ Vsub n (d.getD (b + 1) 0) := by
  have hle : d.getD b 0 + s ≤ d.getD (b + 1) 0 := by
    have h := hd.strict b hb
    have := hs
    simp only [blockSize] at this
    omega
  constructor
  · rw [← hx b (by omega)]
    exact x.mono (Nat.le_add_right _ _)
  · rw [← hx (b + 1) hb]
    exact x.mono hle

theorem flagK_ext_of_blocks (hd : IsCut n d) {x y : FlagK K n}
    (h : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      x.E (d.getD b 0 + s) = y.E (d.getD b 0 + s)) : x = y := by
  apply FlagK.ext
  intro j
  by_cases hjn : j < n
  · set k : Fin n := ⟨j, hjn⟩ with hk
    set c := q2cFPt_nextCut hd k with hc
    have hc1 : 1 ≤ c := q2cFPt_nextCut_pos hd k
    have hcL : c < d.length := q2cFPt_nextCut_lt_length hd k
    obtain ⟨hlo, hhi⟩ := (q2cFPt_nextCut_eq_iff hd k hc1 hcL).mp rfl
    set b := c - 1 with hbdef
    have hbc : b + 1 = c := by omega
    have hbL : b + 1 < d.length := by omega
    have hlo' : d.getD b 0 ≤ j := by simpa [hbc] using hlo
    have hhi' : j < d.getD (b + 1) 0 := by simpa [hbc] using hhi
    have hs : j - d.getD b 0 ≤ blockSize d b := by
      have := hhi'
      simp only [blockSize]
      omega
    have hsum : d.getD b 0 + (j - d.getD b 0) = j := by omega
    have := h b (j - d.getD b 0) hbL hs
    rwa [hsum] at this
  · rw [not_lt] at hjn
    rw [x.top j hjn, y.top j hjn]

theorem exists_mem_refSet_E_eq (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    {X : Submodule K (Fin n → K)} (h₁ : Vsub n (d.getD b 0) ≤ X)
    (h₂ : X ≤ Vsub n (d.getD (b + 1) 0)) :
    ∃ x ∈ refSet K n d, x.E (finrank K X) = X := by
  classical
  have hVa : d.getD b 0 ≤ n := q2cFPt_le_last hd (by omega)
  have hVc : d.getD (b + 1) 0 ≤ n := q2cFPt_le_last hd hb
  have haX : d.getD b 0 ≤ finrank K X := by
    have := Submodule.finrank_mono h₁
    rwa [finrank_Vsub hVa] at this
  have hXc : finrank K X ≤ d.getD (b + 1) 0 := by
    have := Submodule.finrank_mono h₂
    rwa [finrank_Vsub hVc] at this
  obtain ⟨C₁, hC₁m, hC₁b, hC₁d⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_chain_between
      (finrank K X - d.getD b 0) (Vsub n (d.getD b 0)) X h₁
      (by rw [finrank_Vsub hVa]; omega)
  obtain ⟨C₂, hC₂m, hC₂b, hC₂d⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_chain_between
      (d.getD (b + 1) 0 - finrank K X) X (Vsub n (d.getD (b + 1) 0)) h₂
      (by rw [finrank_Vsub hVc]; omega)
  set k₁ := finrank K X - d.getD b 0 with hk₁
  have hC₁k : C₁ k₁ = X := by
    refine Submodule.eq_of_le_of_finrank_eq (hC₁b k₁).2 ?_
    rw [hC₁d k₁ le_rfl, hk₁, finrank_Vsub hVa]
    omega
  have hC₂X : C₂ 0 = X := by
    refine (Submodule.eq_of_le_of_finrank_eq (hC₂b 0).1 ?_).symm
    rw [hC₂d 0 (Nat.zero_le _), add_zero]
  let S : ℕ → ℕ → Submodule K (Fin n → K) := fun b' s =>
    if b' = b then (if s ≤ k₁ then C₁ s else C₂ (s - k₁))
    else Vsub n (d.getD b' 0 + s)
  have hlo : ∀ b' s, b' + 1 < d.length → s ≤ blockSize d b' →
      Vsub n (d.getD b' 0) ≤ S b' s := by
    intro b' s hb' hs
    by_cases hbb : b' = b
    · rw [hbb] at hs ⊢
      dsimp only [S]
      by_cases hs₁ : s ≤ k₁
      · simp only [if_pos rfl, if_pos hs₁]
        exact (hC₁b s).1
      · simp only [if_pos rfl, if_neg hs₁]
        exact le_trans h₁ (hC₂b (s - k₁)).1
    · dsimp only [S]
      simp only [if_neg hbb]
      exact Vsub_mono (Nat.le_add_right _ _)
  have hhi : ∀ b' s, b' + 1 < d.length → s ≤ blockSize d b' →
      S b' s ≤ Vsub n (d.getD (b' + 1) 0) := by
    intro b' s hb' hs
    by_cases hbb : b' = b
    · rw [hbb] at hs ⊢
      dsimp only [S]
      by_cases hs₁ : s ≤ k₁
      · simp only [if_pos rfl, if_pos hs₁]
        exact (hC₁b s).2.trans h₂
      · simp only [if_pos rfl, if_neg hs₁]
        exact (hC₂b (s - k₁)).2
    · dsimp only [S]
      simp only [if_neg hbb]
      apply Vsub_mono
      have hstrict := hd.strict b' hb'
      have := hs; simp only [blockSize] at this; omega
  have hmono : ∀ b' s s', b' + 1 < d.length → s ≤ s' → s' ≤ blockSize d b' →
      S b' s ≤ S b' s' := by
    intro b' s s' hb' hss' hs'
    by_cases hbb : b' = b
    · rw [hbb] at hs' ⊢
      dsimp only [S]
      by_cases hs₁ : s ≤ k₁
      · by_cases hs'₁ : s' ≤ k₁
        · simp only [if_pos rfl, if_pos hs₁, if_pos hs'₁]
          exact hC₁m hss'
        · simp only [if_pos rfl, if_pos hs₁, if_neg hs'₁]
          exact le_trans (hC₁m hs₁) (le_trans (le_of_eq hC₁k)
            (le_trans (le_of_eq hC₂X.symm) (hC₂m (Nat.zero_le (s' - k₁)))))
      · have hs'₁ : ¬ s' ≤ k₁ := fun h => hs₁ (le_trans hss' h)
        simp only [if_pos rfl, if_neg hs₁, if_neg hs'₁]
        exact hC₂m (by omega)
    · dsimp only [S]
      simp only [if_neg hbb]
      exact Vsub_mono (by omega)
  have hdim : ∀ b' s, b' + 1 < d.length → s ≤ blockSize d b' →
      finrank K (S b' s) = d.getD b' 0 + s := by
    intro b' s hb' hs
    by_cases hbb : b' = b
    · rw [hbb] at hs ⊢
      by_cases hs₁ : s ≤ k₁
      · have hSs : S b s = C₁ s := by
          dsimp only [S]; rw [if_pos rfl, if_pos hs₁]
        rw [show finrank K (S b s) = finrank K ↥(C₁ s) from
          congrArg (fun W : Submodule K (Fin n → K) => finrank K W) hSs]
        rw [hC₁d s hs₁, finrank_Vsub hVa]
      · have hSs : S b s = C₂ (s - k₁) := by
          dsimp only [S]; rw [if_pos rfl, if_neg hs₁]
        rw [show finrank K (S b s) = finrank K ↥(C₂ (s - k₁)) from
          congrArg (fun W : Submodule K (Fin n → K) => finrank K W) hSs]
        rw [hC₂d (s - k₁) (by simp only [blockSize] at hs; omega), hk₁]
        omega
    · have hSs : S b' s = Vsub n (d.getD b' 0 + s) := by
        dsimp only [S]; rw [if_neg hbb]
      rw [show finrank K (S b' s) = finrank K ↥(Vsub n (d.getD b' 0 + s)) from
        congrArg (fun W : Submodule K (Fin n → K) => finrank K W) hSs]
      apply finrank_Vsub
      have hstrict := hd.strict b' hb'
      have hlast := q2cFPt_le_last hd hb'
      have := hs; simp only [blockSize] at this; omega
  obtain ⟨z, hzref, hz⟩ := exists_flag_of_blocks hd S hlo hhi hmono hdim
  refine ⟨z, hzref, ?_⟩
  have hfin : d.getD b 0 + k₁ = finrank K X := by rw [hk₁]; omega
  have hk₁m : k₁ ≤ blockSize d b := by rw [hk₁, blockSize]; omega
  have hsz : S b k₁ = X := by
    dsimp only [S]; rw [if_pos rfl, if_pos le_rfl, hC₁k]
  rw [← hfin, hz b k₁ hb hk₁m, hsz]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
