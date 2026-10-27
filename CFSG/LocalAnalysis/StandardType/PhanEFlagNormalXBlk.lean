module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagBlkAct
public import CFSG.LocalAnalysis.StandardType.PhanEFlagExch

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]


private noncomputable def q2cFNX_i0 :
    (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K] (Fin 4 → K) := blkIn 4 [0, 2, 4] 0

private noncomputable def q2cFNX_i1 :
    (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K] (Fin 4 → K) := blkIn 4 [0, 2, 4] 1

private noncomputable def q2cFNX_o0 :
    (Fin 4 → K) →ₗ[K] (Fin (blockSize [0, 2, 4] 0) → K) := blkOut 4 [0, 2, 4] 0

private noncomputable def q2cFNX_o1 :
    (Fin 4 → K) →ₗ[K] (Fin (blockSize [0, 2, 4] 0) → K) := blkOut 4 [0, 2, 4] 1

private noncomputable def q2cFNX_m0 (g : GL (Fin 4) K) :
    (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K] (Fin (blockSize [0, 2, 4] 0) → K) :=
  blkMat [0, 2, 4] 0 g

private noncomputable def q2cFNX_m1 (g : GL (Fin 4) K) :
    (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K] (Fin (blockSize [0, 2, 4] 0) → K) :=
  blkMat [0, 2, 4] 1 g

private noncomputable def q2cFNX_U0 (x : FlagK K 4) :
    Submodule K (Fin (blockSize [0, 2, 4] 0) → K) :=
  (x.E 1).map q2cFNX_o0

private noncomputable def q2cFNX_U1 (x : FlagK K 4) :
    Submodule K (Fin (blockSize [0, 2, 4] 0) → K) :=
  (x.E 3).map q2cFNX_o1

private theorem q2cFNX_o0_i0 (w : Fin (blockSize [0, 2, 4] 0) → K) :
    q2cFNX_o0 (q2cFNX_i0 w) = w := by
  show blkOut 4 [0, 2, 4] 0 (blkIn 4 [0, 2, 4] 0 w) = w
  exact blkOut_blkIn isCut_22 (b := 0) (by decide) w

private theorem q2cFNX_o1_i1 (w : Fin (blockSize [0, 2, 4] 0) → K) :
    q2cFNX_o1 (q2cFNX_i1 w) = w :=
  blkOut_blkIn isCut_22 (b := 1) (by decide)
    (w : Fin (blockSize [0, 2, 4] 1) → K)

private theorem q2cFNX_map_o0_i0 (U : Submodule K (Fin (blockSize [0, 2, 4] 0) → K)) :
    (U.map q2cFNX_i0).map q2cFNX_o0 = U := by
  rw [← Submodule.map_comp]
  have h : q2cFNX_o0.comp q2cFNX_i0 =
      (LinearMap.id : (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K]
        (Fin (blockSize [0, 2, 4] 0) → K)) := by
    apply LinearMap.ext
    intro w
    exact q2cFNX_o0_i0 w
  rw [h, Submodule.map_id]

private theorem q2cFNX_map_o1_i1 (U : Submodule K (Fin (blockSize [0, 2, 4] 0) → K)) :
    (Vsub 4 2 ⊔ U.map q2cFNX_i1).map q2cFNX_o1 = U :=
  map_blkOut_sup_map_blkIn isCut_22 (b := 1) (by decide)
    (U : Submodule K (Fin (blockSize [0, 2, 4] 1) → K))

private theorem q2cFNX_map_sup_i0 {g : GL (Fin 4) K} (hg : StabV 4 [0, 2, 4] g)
    (U : Submodule K (Fin (blockSize [0, 2, 4] 0) → K)) :
    (Vsub 4 0 ⊔ U.map q2cFNX_i0).map (glLin g).toLinearMap =
      Vsub 4 0 ⊔ (U.map (q2cFNX_m0 g)).map q2cFNX_i0 :=
  map_sup_map_blkIn isCut_22 (b := 0) (by decide) hg U

private theorem q2cFNX_map_sup_i1 {g : GL (Fin 4) K} (hg : StabV 4 [0, 2, 4] g)
    (U : Submodule K (Fin (blockSize [0, 2, 4] 0) → K)) :
    (Vsub 4 2 ⊔ U.map q2cFNX_i1).map (glLin g).toLinearMap =
      Vsub 4 2 ⊔ (U.map (q2cFNX_m1 g)).map q2cFNX_i1 :=
  map_sup_map_blkIn isCut_22 (b := 1) (by decide) hg
    (U : Submodule K (Fin (blockSize [0, 2, 4] 1) → K))

private theorem q2cFNX_glLin_inv {n : ℕ} (g : GL (Fin n) K) :
    glLin g⁻¹ = (glLin g).symm := by
  have hmul : ∀ a b : GL (Fin n) K, glLin (a * b) = (glLin b).trans (glLin a) := by
    intro a b
    ext v
    rw [glLin_apply, LinearEquiv.trans_apply, glLin_apply, glLin_apply,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  have hone : glLin (1 : GL (Fin n) K) = LinearEquiv.refl K (Fin n → K) := by
    ext v
    rw [glLin_apply]
    simp
  have h : (glLin g).trans (glLin g⁻¹) = LinearEquiv.refl K (Fin n → K) := by
    rw [← hmul, inv_mul_cancel, hone]
  have hv : ∀ w, glLin g⁻¹ (glLin g w) = w := by
    intro w
    simpa [LinearEquiv.trans_apply] using
      congrArg (fun e : (Fin n → K) ≃ₗ[K] (Fin n → K) => e w) h
  apply LinearEquiv.ext
  intro v
  calc glLin g⁻¹ v = glLin g⁻¹ (glLin g ((glLin g).symm v)) := by
        rw [(glLin g).apply_symm_apply]
    _ = (glLin g).symm v := hv _

theorem q2cFNX_span_sgv (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ}
    (U : Submodule K (Fin n → K)) :
    Submodule.span K (sgv K f n '' (U : Set (Fin n → K))) = sgS K f n U := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨u, hu, rfl⟩
    exact mem_sgS.mpr (by rw [sgv_sgv hK]; exact hu)
  · intro v hv
    have hv' : sgv K f n v ∈ U := mem_sgS.mp (show v ∈ sgS K f n U from hv)
    exact Submodule.subset_span ⟨sgv K f n v, hv', sgv_sgv hK v⟩

private theorem q2cFNX_jShift_eq_nat (v : Fin 4 → K) :
    jShift K f v = blkIn 4 [0, 2, 4] 1 (sgv K f 2 (blkOut 4 [0, 2, 4] 0 v)) := by
  funext k
  fin_cases k <;> simp [jShift, blkIn, blkOut, sgv, sgv_apply] <;> split_ifs <;> simp

private theorem q2cFNX_jShiftInv_eq_nat (v : Fin 4 → K) :
    jShiftInv K f v = blkIn 4 [0, 2, 4] 0 (sgv K f 2 (blkOut 4 [0, 2, 4] 1 v)) := by
  funext k
  fin_cases k <;> simp [jShiftInv, blkIn, blkOut, sgv, sgv_apply] <;> split_ifs <;> simp

private theorem q2cFNX_jShift_eq (v : Fin 4 → K) :
    jShift K f v = q2cFNX_i1 (sgv K f (blockSize [0, 2, 4] 0) (q2cFNX_o0 v)) :=
  q2cFNX_jShift_eq_nat v

private theorem q2cFNX_jShiftInv_eq (v : Fin 4 → K) :
    jShiftInv K f v = q2cFNX_i0 (sgv K f (blockSize [0, 2, 4] 0) (q2cFNX_o1 v)) :=
  q2cFNX_jShiftInv_eq_nat v

private theorem q2cFNX_psiX_E_one (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (flagPsiX hK x).E 1 =
      (sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U1 x)).map q2cFNX_i0 := by
  rw [flagPsiX_E_one hK hx]
  have hset : jShiftInv K f '' (x.E 3 : Set (Fin 4 → K)) =
      q2cFNX_i0 ''
        (sgv K f (blockSize [0, 2, 4] 0) '' (q2cFNX_U1 x : Set _)) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨sgv K f (blockSize [0, 2, 4] 0) (q2cFNX_o1 u),
        ⟨q2cFNX_o1 u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, rfl⟩, ?_⟩
      exact (q2cFNX_jShiftInv_eq u).symm
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
      exact ⟨u, hu, q2cFNX_jShiftInv_eq u⟩
  rw [hset]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hz
    exact Submodule.mem_map.mpr
      ⟨sgv K f (blockSize [0, 2, 4] 0) u,
        mem_sgS.mpr (by rw [sgv_sgv hK]; exact hu), rfl⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
    have hzu : sgv K f (blockSize [0, 2, 4] 0) z ∈ q2cFNX_U1 x :=
      mem_sgS.mp (show z ∈ sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U1 x) from hz)
    rw [← sgv_sgv hK z]
    exact Submodule.subset_span
      ⟨sgv K f (blockSize [0, 2, 4] 0) (sgv K f (blockSize [0, 2, 4] 0) z),
        ⟨sgv K f (blockSize [0, 2, 4] 0) z, hzu, rfl⟩, rfl⟩

private theorem q2cFNX_psiX_E_three (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (flagPsiX hK x).E 3 = Vsub 4 2 ⊔
      (sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U0 x)).map q2cFNX_i1 := by
  rw [flagPsiX_E_three hK hx]
  have hset : jShift K f '' (x.E 1 : Set (Fin 4 → K)) =
      q2cFNX_i1 ''
        (sgv K f (blockSize [0, 2, 4] 0) '' (q2cFNX_U0 x : Set _)) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨sgv K f (blockSize [0, 2, 4] 0) (q2cFNX_o0 u),
        ⟨q2cFNX_o0 u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, rfl⟩, ?_⟩
      exact (q2cFNX_jShift_eq u).symm
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
      exact ⟨u, hu, q2cFNX_jShift_eq u⟩
  rw [hset]
  have hXY : Submodule.span K
      (q2cFNX_i1 '' (sgv K f (blockSize [0, 2, 4] 0) '' (q2cFNX_U0 x : Set _))) =
      (sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U0 x)).map q2cFNX_i1 := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro w ⟨z, hz, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hz
      exact Submodule.mem_map.mpr
        ⟨sgv K f (blockSize [0, 2, 4] 0) u,
          mem_sgS.mpr (by rw [sgv_sgv hK]; exact hu), rfl⟩
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
      have hzu : sgv K f (blockSize [0, 2, 4] 0) z ∈ q2cFNX_U0 x :=
        mem_sgS.mp (show z ∈ sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U0 x) from hz)
      rw [← sgv_sgv hK z]
      exact Submodule.subset_span
        ⟨sgv K f (blockSize [0, 2, 4] 0) (sgv K f (blockSize [0, 2, 4] 0) z),
          ⟨sgv K f (blockSize [0, 2, 4] 0) z, hzu, rfl⟩, rfl⟩
  rw [hXY]

private theorem q2cFNX_U0_flagPsiX (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    q2cFNX_U0 (flagPsiX hK x) = sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U1 x) := by
  rw [q2cFNX_U0, q2cFNX_psiX_E_one hK hx, ← Submodule.map_comp]
  have h : q2cFNX_o0.comp q2cFNX_i0 =
      (LinearMap.id : (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K]
        (Fin (blockSize [0, 2, 4] 0) → K)) := by
    apply LinearMap.ext
    intro w
    exact q2cFNX_o0_i0 w
  rw [h, Submodule.map_id]

private theorem q2cFNX_U1_flagPsiX (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    q2cFNX_U1 (flagPsiX hK x) = sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U0 x) := by
  rw [q2cFNX_U1, q2cFNX_psiX_E_three hK hx]
  exact q2cFNX_map_o1_i1 (sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U0 x))

theorem q2cFNX_flagAct_E {n : ℕ} {d : List ℕ} (hd : IsCut n d) {b : ℕ}
    (hb : b + 1 < d.length) {g : GL (Fin n) K} (hg : StabV n d g) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {s : ℕ} (hs : s ≤ blockSize d b) :
    (flagAct g x).E (d.getD b 0 + s) = Vsub n (d.getD b 0) ⊔
      (((x.E (d.getD b 0 + s)).map (blkOut n d b)).map (blkMat d b g)).map (blkIn n d b) := by
  rw [flagAct, flagMap_E]
  obtain ⟨h1, h2⟩ := refSet_E_mem_interval hd hx hb hs
  conv_lhs => rw [eq_sup_map_blkIn hd hb h1 h2, map_sup_map_blkIn hd hb hg]

private theorem q2cFNX_E1_eq {x : FlagK K 4} (hx : x ∈ refSet K 4 [0, 2, 4]) :
    x.E 1 = (q2cFNX_U0 x).map q2cFNX_i0 := by
  obtain ⟨h1, h2⟩ := refSet_E_mem_interval isCut_22 hx (b := 0) (by decide) (s := 1) (by decide)
  have h := eq_sup_map_blkIn isCut_22 (b := 0) (by decide) h1 h2
  have h0 : ([0, 2, 4] : List ℕ).getD 0 0 = 0 := rfl
  rw [h0, Vsub_zero, bot_sup_eq] at h
  simpa only [q2cFNX_U0, q2cFNX_o0, q2cFNX_i0] using h

private theorem q2cFNX_E3_eq {x : FlagK K 4} (hx : x ∈ refSet K 4 [0, 2, 4]) :
    x.E 3 = Vsub 4 2 ⊔ (q2cFNX_U1 x).map q2cFNX_i1 := by
  obtain ⟨h1, h2⟩ := refSet_E_mem_interval isCut_22 hx (b := 1) (by decide) (s := 1) (by decide)
  have h := eq_sup_map_blkIn isCut_22 (b := 1) (by decide) h1 h2
  have h3 : ([0, 2, 4] : List ℕ).getD 1 0 + 1 = 3 := rfl
  have h2' : ([0, 2, 4] : List ℕ).getD 1 0 = 2 := rfl
  rw [h3, h2'] at h
  exact h

private theorem q2cFNX_flagAct_E1 {g : GL (Fin 4) K} (hg : StabV 4 [0, 2, 4] g)
    {x : FlagK K 4} (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (flagAct g x).E 1 =
      Vsub 4 0 ⊔ ((q2cFNX_U0 x).map (q2cFNX_m0 g)).map q2cFNX_i0 := by
  have h := q2cFNX_flagAct_E isCut_22 (b := 0) (by decide) hg hx (s := 1) (by decide)
  have hgt : ([0, 2, 4] : List ℕ).getD 0 0 + 1 = 1 := rfl
  rw [hgt] at h
  simpa only [q2cFNX_U0, q2cFNX_m0, q2cFNX_o0, q2cFNX_i0, List.getD_cons_zero] using h

private theorem q2cFNX_flagAct_E3 {g : GL (Fin 4) K} (hg : StabV 4 [0, 2, 4] g)
    {x : FlagK K 4} (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (flagAct g x).E 3 =
      Vsub 4 2 ⊔ ((q2cFNX_U1 x).map (q2cFNX_m1 g)).map q2cFNX_i1 := by
  have h := q2cFNX_flagAct_E isCut_22 (b := 1) (by decide) hg hx (s := 1) (by decide)
  have hgt : ([0, 2, 4] : List ℕ).getD 1 0 + 1 = 3 := rfl
  have hgt' : ([0, 2, 4] : List ℕ).getD 1 0 = 2 := rfl
  rw [hgt, hgt'] at h
  exact h

theorem q2cFNX_blkMat_eq_of_act {n : ℕ} {d : List ℕ} (hd : IsCut n d)
    {E : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K)}
    {e : GL (Fin n) K}
    (heAct : ∀ b, b + 1 < d.length → ∀ w, glLin e (blkIn n d b w) = blkIn n d b (E b w))
    {b : ℕ} (hb : b + 1 < d.length) : blkMat d b e = (E b).toLinearMap := by
  apply LinearMap.ext
  intro w
  change blkOut n d b (glLin e (blkIn n d b w)) = E b w
  rw [heAct b hb w, blkOut_blkIn hd hb]

theorem q2cFNX_blockDiag_inv_act {n : ℕ} {d : List ℕ} (hd : IsCut n d)
    {E : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K)}
    {e : GL (Fin n) K}
    (heAct : ∀ b, b + 1 < d.length → ∀ w, glLin e (blkIn n d b w) = blkIn n d b (E b w))
    {b : ℕ} (hb : b + 1 < d.length) (w : Fin (blockSize d b) → K) :
    glLin e⁻¹ (blkIn n d b w) = blkIn n d b ((E b).symm w) := by
  rw [q2cFNX_glLin_inv]
  apply (glLin e).injective
  rw [LinearEquiv.apply_symm_apply, heAct b hb ((E b).symm w), LinearEquiv.apply_symm_apply]

private theorem q2cFNX_U0_flagAct {g : GL (Fin 4) K} (hg : StabV 4 [0, 2, 4] g)
    {x : FlagK K 4} (hx : x ∈ refSet K 4 [0, 2, 4]) :
    q2cFNX_U0 (flagAct g x) = (q2cFNX_U0 x).map (q2cFNX_m0 g) := by
  rw [q2cFNX_U0, q2cFNX_flagAct_E1 hg hx, Vsub_zero, bot_sup_eq]
  exact q2cFNX_map_o0_i0 _

private theorem q2cFNX_U1_flagAct {g : GL (Fin 4) K} (hg : StabV 4 [0, 2, 4] g)
    {x : FlagK K 4} (hx : x ∈ refSet K 4 [0, 2, 4]) :
    q2cFNX_U1 (flagAct g x) = (q2cFNX_U1 x).map (q2cFNX_m1 g) := by
  rw [q2cFNX_U1, q2cFNX_flagAct_E3 hg hx]
  exact q2cFNX_map_o1_i1 _

theorem q2cFNX_map_symm_ofBijective {m : ℕ} (f : (Fin m → K) →ₗ[K] (Fin m → K))
    (hf : Function.Bijective f) (U : Submodule K (Fin m → K)) :
    (U.map f).map (LinearEquiv.ofBijective f hf).symm.toLinearMap = U := by
  rw [← Submodule.map_comp]
  have h : ((LinearEquiv.ofBijective f hf).symm.toLinearMap.comp f) = LinearMap.id := by
    ext u
    simp
  rw [h, Submodule.map_id]

private theorem q2cFNX_U1_flagAct_psiX_flagAct (hK : Nat.card K = (2 ^ f) ^ 2)
    {M : GL (Fin 4) K} (hM : StabV 4 [0, 2, 4] M) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    q2cFNX_U1 (flagAct M (flagPsiX hK (flagAct M x))) =
      (sgS K f (blockSize [0, 2, 4] 0) ((q2cFNX_U0 x).map (q2cFNX_m0 M))).map
        (q2cFNX_m1 M) := by
  rw [q2cFNX_U1_flagAct hM (flagPsiX_mem hK (StabV.flagAct_mem_refSet hM hx))]
  rw [q2cFNX_U1_flagPsiX hK (StabV.flagAct_mem_refSet hM hx)]
  rw [q2cFNX_U0_flagAct hM hx]

private theorem q2cFNX_hinv_U (hK : Nat.card K = (2 ^ f) ^ 2) {M : GL (Fin 4) K}
    (hM : StabV 4 [0, 2, 4] M)
    (hinv : ∀ x ∈ refSet K 4 [0, 2, 4],
      flagAct M (flagPsiX hK (flagAct M (flagPsiX hK x))) = x)
    {x : FlagK K 4} (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (sgS K f (blockSize [0, 2, 4] 0) ((q2cFNX_U0 x).map (q2cFNX_m0 M))).map
        (q2cFNX_m1 M) = sgS K f (blockSize [0, 2, 4] 0) (q2cFNX_U0 x) := by
  have hψR : flagPsiX hK x ∈ refSet K 4 [0, 2, 4] := flagPsiX_mem hK hx
  have h := congrArg (fun F : FlagK K 4 => q2cFNX_U1 F) (hinv (flagPsiX hK x) hψR)
  rw [flagPsiX_flagPsiX hK hx] at h
  rw [q2cFNX_U1_flagAct_psiX_flagAct hK hM hx, q2cFNX_U1_flagPsiX hK hx] at h
  exact h

theorem exists_normalForm_flagPsiX (hK : Nat.card K = (2 ^ f) ^ 2) {M : GL (Fin 4) K}
    (hM : StabV 4 [0, 2, 4] M)
    (hinv : ∀ x ∈ refSet K 4 [0, 2, 4],
      flagAct M (flagPsiX hK (flagAct M (flagPsiX hK x))) = x) :
    ∃ e : GL (Fin 4) K, StabV 4 [0, 2, 4] e ∧ ∀ x ∈ refSet K 4 [0, 2, 4],
      flagAct e (flagAct M (flagPsiX hK (flagAct e⁻¹ x))) = flagPsiX hK x := by
  classical
  have hd : IsCut 4 [0, 2, 4] := isCut_22
  have hb0 : 0 + 1 < ([0, 2, 4] : List ℕ).length := by decide
  have hb1 : 1 + 1 < ([0, 2, 4] : List ℕ).length := by decide
  let A : (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K] (Fin (blockSize [0, 2, 4] 0) → K) :=
    q2cFNX_m0 M
  have hAbij : Function.Bijective A := by
    show Function.Bijective (q2cFNX_m0 M)
    exact blkMat_bijective hd hb0 hM
  let E0 : (Fin (blockSize [0, 2, 4] 0) → K) ≃ₗ[K]
      (Fin (blockSize [0, 2, 4] 0) → K) := (LinearEquiv.ofBijective A hAbij).symm
  let E : ∀ b, (Fin (blockSize [0, 2, 4] b) → K) ≃ₗ[K]
      (Fin (blockSize [0, 2, 4] b) → K) := fun b =>
    if h : b = 0 then h ▸ E0 else LinearEquiv.refl K _
  obtain ⟨e, he, heAct⟩ := exists_blockDiag hd E
  have hE0 : E 0 = E0 := by simp only [E, dif_pos rfl]
  have hE0symm : ((E 0).symm).toLinearMap = A := by rw [hE0]; rfl
  have hE1 : E 1 = LinearEquiv.refl K _ := by
    have h10 : (1 : ℕ) ≠ 0 := by norm_num
    simp only [E, dif_neg h10]
  have hm0e : q2cFNX_m0 e = (E 0).toLinearMap :=
    q2cFNX_blkMat_eq_of_act hd heAct hb0
  have hm1e : q2cFNX_m1 e = (E 1).toLinearMap :=
    q2cFNX_blkMat_eq_of_act hd heAct hb1
  have hm0inv : q2cFNX_m0 e⁻¹ = ((E 0).symm).toLinearMap :=
    q2cFNX_blkMat_eq_of_act hd (E := fun b => (E b).symm) (e := e⁻¹)
      (fun b hb w => q2cFNX_blockDiag_inv_act hd heAct hb w) hb0
  have hm1inv : q2cFNX_m1 e⁻¹ = ((E 1).symm).toLinearMap :=
    q2cFNX_blkMat_eq_of_act hd (E := fun b => (E b).symm) (e := e⁻¹)
      (fun b hb w => q2cFNX_blockDiag_inv_act hd heAct hb w) hb1
  have hm1e_id : q2cFNX_m1 e =
      (LinearMap.id : (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K]
        (Fin (blockSize [0, 2, 4] 0) → K)) := by
    rw [hm1e, hE1]
    ext w
    rfl
  have hm1inv_id : q2cFNX_m1 e⁻¹ =
      (LinearMap.id : (Fin (blockSize [0, 2, 4] 0) → K) →ₗ[K]
        (Fin (blockSize [0, 2, 4] 0) → K)) := by
    rw [hm1inv, hE1]
    ext w
    rfl
  refine ⟨e, he, ?_⟩
  intro x hx
  have hyR : flagAct e⁻¹ x ∈ refSet K 4 [0, 2, 4] :=
    StabV.flagAct_mem_refSet (StabV.inv he) hx
  have hzR : flagPsiX hK (flagAct e⁻¹ x) ∈ refSet K 4 [0, 2, 4] := flagPsiX_mem hK hyR
  have hwR : flagAct M (flagPsiX hK (flagAct e⁻¹ x)) ∈ refSet K 4 [0, 2, 4] :=
    StabV.flagAct_mem_refSet hM hzR
  have hvR : flagAct e (flagAct M (flagPsiX hK (flagAct e⁻¹ x))) ∈ refSet K 4 [0, 2, 4] :=
    StabV.flagAct_mem_refSet he hwR
  have hU0y : q2cFNX_U0 (flagAct e⁻¹ x) = (q2cFNX_U0 x).map A := by
    rw [q2cFNX_U0_flagAct (StabV.inv he) hx, hm0inv, hE0symm]
  have hU0eq : q2cFNX_U0 (flagAct e (flagAct M (flagPsiX hK (flagAct e⁻¹ x)))) =
      q2cFNX_U0 (flagPsiX hK x) := by
    rw [q2cFNX_U0_flagAct he hwR, hm0e, hE0]
    rw [q2cFNX_U0_flagAct hM hzR]
    change ((q2cFNX_U0 (flagPsiX hK (flagAct e⁻¹ x))).map A).map E0.toLinearMap =
      q2cFNX_U0 (flagPsiX hK x)
    rw [q2cFNX_map_symm_ofBijective A hAbij]
    rw [q2cFNX_U0_flagPsiX hK hyR, q2cFNX_U0_flagPsiX hK hx]
    congr 1
    rw [q2cFNX_U1_flagAct (StabV.inv he) hx, hm1inv_id, Submodule.map_id]
  have hU1eq : q2cFNX_U1 (flagAct e (flagAct M (flagPsiX hK (flagAct e⁻¹ x)))) =
      q2cFNX_U1 (flagPsiX hK x) := by
    rw [q2cFNX_U1_flagAct he hwR, hm1e_id, Submodule.map_id]
    rw [q2cFNX_U1_flagAct hM hzR, q2cFNX_U1_flagPsiX hK hyR]
    rw [q2cFNX_U1_flagPsiX hK hx]
    rw [hU0y]
    simpa only [A] using q2cFNX_hinv_U hK hM hinv hx
  refine FlagK.ext4 ?_ ?_ ?_
  · rw [q2cFNX_E1_eq hvR, q2cFNX_E1_eq (flagPsiX_mem hK hx), hU0eq]
  · rw [show (flagAct e (flagAct M (flagPsiX hK (flagAct e⁻¹ x)))).E 2 = Vsub 4 2 from
        by simpa using hvR 1 (by decide),
      show (flagPsiX hK x).E 2 = Vsub 4 2 from
        by simpa using (flagPsiX_mem hK hx) 1 (by decide)]
  · rw [q2cFNX_E3_eq hvR, q2cFNX_E3_eq (flagPsiX_mem hK hx), hU1eq]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
