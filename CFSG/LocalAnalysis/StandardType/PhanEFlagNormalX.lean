module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagNormalXBlk
public import CFSG.LocalAnalysis.StandardType.PhanEFlagA2A1
public import CFSG.LocalAnalysis.StandardType.PhanEFlagProd

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

theorem exists_normalForm_psiA1A1 (hK : Nat.card K = (2 ^ f) ^ 2) (M₁ M₂ : GL (Fin 2) K)
    (hinv : ∀ c : FlagK K 2 × FlagK K 2,
      (flagAct M₁ (flagSg hK (flagAct M₂ (flagSg hK c.1))),
        flagAct M₂ (flagSg hK (flagAct M₁ (flagSg hK c.2)))) = c) :
    ∃ e₁ e₂ : GL (Fin 2) K, ∀ c : FlagK K 2 × FlagK K 2,
      (flagAct e₁ (flagAct M₁ (flagSg hK (flagAct e₂⁻¹ c.2))),
        flagAct e₂ (flagAct M₂ (flagSg hK (flagAct e₁⁻¹ c.1)))) = psiA1A1 hK c := by
  refine ⟨M₁⁻¹, 1, fun c => ?_⟩
  have h : flagAct M₂ (flagSg hK (flagAct M₁ c.1)) = flagSg hK c.1 := by
    have h' := congrArg Prod.snd (hinv (c.1, flagSg hK c.1))
    simpa [flagSg_flagSg hK c.1] using h'
  simp only [psiA1A1, Prod.mk.injEq]
  constructor
  · rw [inv_one, flagAct_one, flagAct_inv_flagAct]
  · rw [inv_inv, flagAct_one]
    exact h

private noncomputable def q2cFNX3_i1 : (Fin 2 → K) →ₗ[K] (Fin 3 → K) :=
  blkIn 3 [0, 1, 3] 1

private noncomputable def q2cFNX3_o1 : (Fin 3 → K) →ₗ[K] (Fin 2 → K) :=
  blkOut 3 [0, 1, 3] 1

private noncomputable def q2cFNX3_m1 (g : GL (Fin 3) K) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) := blkMat [0, 1, 3] 1 g

private noncomputable def q2cFNX3_A2 (x : FlagK K 3) : Submodule K (Fin 2 → K) :=
  (x.E 2).map q2cFNX3_o1

private noncomputable def q2cFNX3_A1 (c : FlagK K 3 × FlagK K 2) :
    Submodule K (Fin 2 → K) := c.2.E 1

private theorem q2cFNX3_jShift21_eq_nat (u : Fin 2 → K) :
    jShift21 K f u = blkIn 3 [0, 1, 3] 1 (sgv K f 2 u) := by
  funext k
  fin_cases k <;> simp [jShift21, blkIn, sgv, sgv_apply, Nat.not_succ_le_zero]
    <;> congr 1

private theorem q2cFNX3_jShift21_eq (u : Fin 2 → K) :
    jShift21 K f u = q2cFNX3_i1 (sgv K f 2 u) :=
  q2cFNX3_jShift21_eq_nat u

private theorem q2cFNX3_jShift21Inv_eq_nat (v : Fin 3 → K) :
    jShift21Inv K f v = sgv K f 2 (blkOut 3 [0, 1, 3] 1 v) := by
  funext k
  fin_cases k <;> simp [jShift21Inv, blkOut, sgv, sgv_apply, Nat.not_succ_le_zero]
    <;> congr 1

private theorem q2cFNX3_jShift21Inv_eq (v : Fin 3 → K) :
    jShift21Inv K f v = sgv K f 2 (q2cFNX3_o1 v) :=
  q2cFNX3_jShift21Inv_eq_nat v

private theorem q2cFNX3_jShift21Inv_i1_nat (w : Fin 2 → K) :
    jShift21Inv K f (blkIn 3 [0, 1, 3] 1 w) = sgv K f 2 w := by
  funext k
  fin_cases k <;>
    simp [jShift21Inv, blkIn, blkOut, sgv, sgv_apply, Nat.not_succ_le_zero]
    <;> congr 1

private theorem q2cFNX3_jShift21Inv_i1 (w : Fin 2 → K) :
    jShift21Inv K f (q2cFNX3_i1 w) = sgv K f 2 w :=
  q2cFNX3_jShift21Inv_i1_nat w

private theorem q2cFNX3_jShift21Inv_add (v v' : Fin 3 → K) :
    jShift21Inv K f (v + v') = jShift21Inv K f v + jShift21Inv K f v' := by
  funext k
  fin_cases k <;> simp [jShift21Inv, map_add]

private theorem q2cFNX3_jShift21Inv_eq_zero {v : Fin 3 → K} (hv : v ∈ Vsub 3 1) :
    jShift21Inv K f v = 0 := by
  funext k
  fin_cases k <;> simp [jShift21Inv, hv 1 (by norm_num), hv 2 (by norm_num)]

private theorem q2cFNX3_E2_eq {x : FlagK K 3} (hx : x ∈ refSet K 3 [0, 1, 3]) :
    x.E 2 = Vsub 3 1 ⊔ (q2cFNX3_A2 x).map q2cFNX3_i1 := by
  obtain ⟨h1, h2⟩ := refSet_E_mem_interval q2cFA2_isCut_013 hx (b := 1) (by decide)
    (s := 1) (by decide)
  have h := eq_sup_map_blkIn q2cFA2_isCut_013 (b := 1) (by decide) h1 h2
  have h2' : ([0, 1, 3] : List ℕ).getD 1 0 = 1 := rfl
  have h2'' : ([0, 1, 3] : List ℕ).getD 1 0 + 1 = 2 := rfl
  rw [h2'', h2'] at h
  exact h

private theorem q2cFNX3_flagAct_E2 {g : GL (Fin 3) K} (hg : StabV 3 [0, 1, 3] g)
    {x : FlagK K 3} (hx : x ∈ refSet K 3 [0, 1, 3]) :
    (flagAct g x).E 2 = Vsub 3 1 ⊔ ((q2cFNX3_A2 x).map (q2cFNX3_m1 g)).map q2cFNX3_i1 := by
  have h := q2cFNX_flagAct_E q2cFA2_isCut_013 (b := 1) (by decide) hg hx (s := 1) (by decide)
  have h2' : ([0, 1, 3] : List ℕ).getD 1 0 = 1 := rfl
  have h2'' : ([0, 1, 3] : List ℕ).getD 1 0 + 1 = 2 := rfl
  rw [h2'', h2'] at h
  exact h

private theorem q2cFNX3_A2_flagAct {g : GL (Fin 3) K} (hg : StabV 3 [0, 1, 3] g)
    {x : FlagK K 3} (hx : x ∈ refSet K 3 [0, 1, 3]) :
    q2cFNX3_A2 (flagAct g x) = (q2cFNX3_A2 x).map (q2cFNX3_m1 g) := by
  rw [q2cFNX3_A2, q2cFNX3_flagAct_E2 hg hx]
  exact map_blkOut_sup_map_blkIn q2cFA2_isCut_013 (b := 1) (by decide) _

private theorem q2cFNX3_psi_mem (hK : Nat.card K = (2 ^ f) ^ 2)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (psiA2A1 hK c).1 ∈ refSet K 3 [0, 1, 3] := by
  unfold psiA2A1
  rw [dif_pos hc]
  exact (Classical.choose_spec (exists_psiA2A1 hK hc)).1

private theorem q2cFNX3_psi_fst_E2 (hK : Nat.card K = (2 ^ f) ^ 2)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (psiA2A1 hK c).1.E 2 = Vsub 3 1 ⊔ (sgS K f 2 (q2cFNX3_A1 c)).map q2cFNX3_i1 := by
  have h := (Classical.choose_spec (exists_psiA2A1 hK hc)).2.1
  unfold psiA2A1
  rw [dif_pos hc, h]
  congr 1
  have hset : jShift21 K f '' (c.2.E 1 : Set (Fin 2 → K)) =
      q2cFNX3_i1 '' (sgv K f 2 '' (c.2.E 1 : Set (Fin 2 → K))) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨sgv K f 2 u, ⟨u, hu, rfl⟩, (q2cFNX3_jShift21_eq u).symm⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, q2cFNX3_jShift21_eq y⟩
  rw [hset]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hz
    exact Submodule.mem_map.mpr
      ⟨sgv K f 2 u, mem_sgS.mpr (by rw [sgv_sgv hK]; exact hu), rfl⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
    have hzu : sgv K f 2 z ∈ q2cFNX3_A1 c := mem_sgS.mp hz
    rw [← sgv_sgv hK z]
    exact Submodule.subset_span
      ⟨sgv K f 2 (sgv K f 2 z), ⟨sgv K f 2 z, hzu, rfl⟩, rfl⟩

private theorem q2cFNX3_psi_snd_E1 (hK : Nat.card K = (2 ^ f) ^ 2)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (psiA2A1 hK c).2.E 1 = sgS K f 2 (q2cFNX3_A2 c.1) := by
  have h := (Classical.choose_spec (exists_psiA2A1 hK hc)).2.2
  unfold psiA2A1
  rw [dif_pos hc, h]
  have hset : jShift21Inv K f '' (c.1.E 2 : Set (Fin 3 → K)) =
      sgv K f 2 '' (q2cFNX3_A2 c.1 : Set (Fin 2 → K)) := by
    rw [q2cFNX3_E2_eq hc]
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases Submodule.mem_sup.mp hu with ⟨a, ha, b, hb, rfl⟩
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hb
      refine ⟨w, hw, ?_⟩
      rw [q2cFNX3_jShift21Inv_add, q2cFNX3_jShift21Inv_eq_zero ha, q2cFNX3_jShift21Inv_i1,
        zero_add]
    · rintro ⟨w, hw, rfl⟩
      exact ⟨q2cFNX3_i1 w, Submodule.mem_sup_right (Submodule.mem_map_of_mem hw),
        q2cFNX3_jShift21Inv_i1 w⟩
  rw [hset, q2cFNX3_A2, q2cFNX_span_sgv hK]

private theorem q2cFNX3_A2_psi (hK : Nat.card K = (2 ^ f) ^ 2)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    q2cFNX3_A2 (psiA2A1 hK c).1 = sgS K f 2 (q2cFNX3_A1 c) := by
  rw [q2cFNX3_A2, q2cFNX3_psi_fst_E2 hK hc]
  exact map_blkOut_sup_map_blkIn q2cFA2_isCut_013 (b := 1) (by decide) _

private theorem q2cFNX3_psiM2_A1 (hK : Nat.card K = (2 ^ f) ^ 2) {M₁ : GL (Fin 3) K}
    (hM₁ : StabV 3 [0, 1, 3] M₁) (M₂ : GL (Fin 2) K) {c : FlagK K 3 × FlagK K 2}
    (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (flagAct M₂ (psiA2A1 hK (flagAct M₁ (psiA2A1 hK c).1,
      flagAct M₂ (psiA2A1 hK c).2)).2).E 1 =
      (sgS K f 2 ((sgS K f 2 (q2cFNX3_A1 c)).map (q2cFNX3_m1 M₁))).map
        (glLin M₂).toLinearMap := by
  have hc1 : flagAct M₁ (psiA2A1 hK c).1 ∈ refSet K 3 [0, 1, 3] :=
    StabV.flagAct_mem_refSet hM₁ (q2cFNX3_psi_mem hK hc)
  rw [flagAct, flagMap_E, q2cFNX3_psi_snd_E1 hK hc1,
    q2cFNX3_A2_flagAct hM₁ (q2cFNX3_psi_mem hK hc), q2cFNX3_A2_psi hK hc]

private theorem q2cFNX3_hinv_A1 (hK : Nat.card K = (2 ^ f) ^ 2) {M₁ : GL (Fin 3) K}
    (hM₁ : StabV 3 [0, 1, 3] M₁) (M₂ : GL (Fin 2) K)
    (hinv : ∀ c : FlagK K 3 × FlagK K 2, c.1 ∈ refSet K 3 [0, 1, 3] →
      (flagAct M₁ (psiA2A1 hK (flagAct M₁ (psiA2A1 hK c).1,
        flagAct M₂ (psiA2A1 hK c).2)).1,
        flagAct M₂ (psiA2A1 hK (flagAct M₁ (psiA2A1 hK c).1,
          flagAct M₂ (psiA2A1 hK c).2)).2) = c)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (sgS K f 2 ((sgS K f 2 (q2cFNX3_A1 c)).map (q2cFNX3_m1 M₁))).map
        (glLin M₂).toLinearMap = q2cFNX3_A1 c := by
  have h := congrArg (fun d : FlagK K 3 × FlagK K 2 => d.2.E 1) (hinv c hc)
  rw [q2cFNX3_psiM2_A1 hK hM₁ M₂ hc] at h
  exact h

private theorem q2cFNX3_hinv_A2 (hK : Nat.card K = (2 ^ f) ^ 2) {M₁ : GL (Fin 3) K}
    (hM₁ : StabV 3 [0, 1, 3] M₁) (M₂ : GL (Fin 2) K)
    (hinv : ∀ c : FlagK K 3 × FlagK K 2, c.1 ∈ refSet K 3 [0, 1, 3] →
      (flagAct M₁ (psiA2A1 hK (flagAct M₁ (psiA2A1 hK c).1,
        flagAct M₂ (psiA2A1 hK c).2)).1,
        flagAct M₂ (psiA2A1 hK (flagAct M₁ (psiA2A1 hK c).1,
          flagAct M₂ (psiA2A1 hK c).2)).2) = c)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (sgS K f 2 ((q2cFNX3_A2 c.1).map (q2cFNX3_m1 M₁))).map
        (glLin M₂).toLinearMap = sgS K f 2 (q2cFNX3_A2 c.1) := by
  have hc'' : (psiA2A1 hK c).1 ∈ refSet K 3 [0, 1, 3] := q2cFNX3_psi_mem hK hc
  have h := q2cFNX3_hinv_A1 hK hM₁ M₂ hinv hc''
  rw [show q2cFNX3_A1 (psiA2A1 hK c) = sgS K f 2 (q2cFNX3_A2 c.1) from
    q2cFNX3_psi_snd_E1 hK hc] at h
  rw [sgS_sgS hK] at h
  exact h

theorem exists_normalForm_psiA2A1 (hK : Nat.card K = (2 ^ f) ^ 2) {M₁ : GL (Fin 3) K}
    (hM₁ : StabV 3 [0, 1, 3] M₁) (M₂ : GL (Fin 2) K)
    (hinv : ∀ c : FlagK K 3 × FlagK K 2, c.1 ∈ refSet K 3 [0, 1, 3] →
      (flagAct M₁ (psiA2A1 hK (flagAct M₁ (psiA2A1 hK c).1, flagAct M₂ (psiA2A1 hK c).2)).1,
        flagAct M₂ (psiA2A1 hK (flagAct M₁ (psiA2A1 hK c).1,
          flagAct M₂ (psiA2A1 hK c).2)).2) = c) :
    ∃ (e₁ : GL (Fin 3) K) (e₂ : GL (Fin 2) K), StabV 3 [0, 1, 3] e₁ ∧
      ∀ c : FlagK K 3 × FlagK K 2, c.1 ∈ refSet K 3 [0, 1, 3] →
        (flagAct e₁ (flagAct M₁ (psiA2A1 hK (flagAct e₁⁻¹ c.1, flagAct e₂⁻¹ c.2)).1),
          flagAct e₂ (flagAct M₂ (psiA2A1 hK (flagAct e₁⁻¹ c.1, flagAct e₂⁻¹ c.2)).2)) =
            psiA2A1 hK c := by
  classical
  have hd : IsCut 3 [0, 1, 3] := q2cFA2_isCut_013
  have hb1 : 1 + 1 < ([0, 1, 3] : List ℕ).length := by decide
  let D : (Fin (blockSize [0, 1, 3] 1) → K) →ₗ[K] (Fin (blockSize [0, 1, 3] 1) → K) :=
    q2cFNX3_m1 M₁
  have hDbij : Function.Bijective D := by
    show Function.Bijective (q2cFNX3_m1 M₁)
    exact blkMat_bijective hd hb1 hM₁
  let Ef : ∀ b, (Fin (blockSize [0, 1, 3] b) → K) ≃ₗ[K]
      (Fin (blockSize [0, 1, 3] b) → K) := fun b =>
    if h : b = 1 then h ▸ (LinearEquiv.ofBijective D hDbij).symm else LinearEquiv.refl K _
  obtain ⟨e₁, he₁, he₁Act⟩ := exists_blockDiag hd Ef
  have hEf1 : Ef 1 = (LinearEquiv.ofBijective D hDbij).symm := by
    simp only [Ef, dif_pos rfl]
  have hm_e : q2cFNX3_m1 e₁ = (Ef 1).toLinearMap :=
    q2cFNX_blkMat_eq_of_act hd he₁Act hb1
  have hm_inv : q2cFNX3_m1 e₁⁻¹ = D := by
    have h := q2cFNX_blkMat_eq_of_act hd (E := fun b => (Ef b).symm) (e := e₁⁻¹)
      (fun b hb w => q2cFNX_blockDiag_inv_act hd he₁Act hb w) hb1
    rw [hEf1] at h
    change blkMat [0, 1, 3] 1 e₁⁻¹ = D
    exact h
  refine ⟨e₁, 1, he₁, ?_⟩
  intro c hc
  simp only [inv_one, flagAct_one]
  have hc' : flagAct e₁⁻¹ c.1 ∈ refSet K 3 [0, 1, 3] :=
    StabV.flagAct_mem_refSet (StabV.inv he₁) hc
  have hA1c' : q2cFNX3_A1 (flagAct e₁⁻¹ c.1, c.2) = q2cFNX3_A1 c := rfl
  refine Prod.ext ?_ ?_
  · have hwR : (psiA2A1 hK (flagAct e₁⁻¹ c.1, c.2)).1 ∈ refSet K 3 [0, 1, 3] :=
      q2cFNX3_psi_mem hK hc'
    have hyR : flagAct M₁ (psiA2A1 hK (flagAct e₁⁻¹ c.1, c.2)).1 ∈ refSet K 3 [0, 1, 3] :=
      StabV.flagAct_mem_refSet hM₁ hwR
    have hvR : flagAct e₁ (flagAct M₁ (psiA2A1 hK (flagAct e₁⁻¹ c.1, c.2)).1) ∈
        refSet K 3 [0, 1, 3] := StabV.flagAct_mem_refSet he₁ hyR
    apply FlagK.ext_of_mid
    intro j hj1 hj3
    interval_cases j
    · rw [show (flagAct e₁ (flagAct M₁ (psiA2A1 hK (flagAct e₁⁻¹ c.1, c.2)).1)).E 1 =
          Vsub 3 1 from by simpa using hvR 1 (by decide),
        show (psiA2A1 hK c).1.E 1 = Vsub 3 1 from
          by simpa using (q2cFNX3_psi_mem hK hc) 1 (by decide)]
    · have hA2mid : q2cFNX3_A2 (flagAct M₁ (psiA2A1 hK (flagAct e₁⁻¹ c.1, c.2)).1) =
          (sgS K f 2 (q2cFNX3_A1 c)).map D := by
        rw [q2cFNX3_A2_flagAct hM₁ hwR, q2cFNX3_A2_psi hK hc', hA1c']
        rfl
      have h_cancel : ((sgS K f 2 (q2cFNX3_A1 c)).map D).map (q2cFNX3_m1 e₁) =
          sgS K f 2 (q2cFNX3_A1 c) := by
        rw [hm_e, hEf1]
        exact q2cFNX_map_symm_ofBijective D hDbij _
      rw [q2cFNX3_flagAct_E2 he₁ hyR, hA2mid, h_cancel, q2cFNX3_psi_fst_E2 hK hc]
  · have hwR : (psiA2A1 hK (flagAct e₁⁻¹ c.1, c.2)).2 ∈ Set.univ := trivial
    apply FlagK.ext_of_mid
    intro j hj1 hj2
    have hj : j = 1 := by omega
    subst hj
    show (flagAct M₂ (psiA2A1 hK (flagAct e₁⁻¹ c.1, c.2)).2).E 1 =
      (psiA2A1 hK c).2.E 1
    rw [flagAct, flagMap_E, q2cFNX3_psi_snd_E1 hK hc',
      q2cFNX3_A2_flagAct (StabV.inv he₁) hc, hm_inv,
      q2cFNX3_hinv_A2 hK hM₁ M₂ hinv hc, q2cFNX3_psi_snd_E1 hK hc]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
