module

public import CFSG.Quasithin.MS93.S46RPhi
public import CFSG.Quasithin.MS93.S46KCF
public import CFSG.Quasithin.MS93.S46I4612K
public import CFSG.Quasithin.MS93.S46KCTwo
public import CFSG.Quasithin.MS93.S46I4612
public import CFSG.Quasithin.MS93.S46KCFGrp

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46.X3
  CFSG.Quasithin.MS93.S46.KC2 CFSG.Quasithin.MS93.S46.KCF
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

theorem exists_sl3_rows_cross {r r' : Fin 3 → F} (h : crossProduct r r' ≠ 0) :
    ∃ A : SL3 F, (A : Matrix (Fin 3) (Fin 3) F) 0 = r ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 = r' ∧
      ((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1 = crossProduct r r' := by
  obtain ⟨j, hj⟩ : ∃ j, crossProduct r r' j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (funext hcon)
  set t : Fin 3 → F := Pi.single j (crossProduct r r' j)⁻¹ with ht
  have hdot : ∀ x : Fin 3 → F, t ⬝ᵥ x = (crossProduct r r' j)⁻¹ * x j := fun x => by
    rw [ht, single_dotProduct]
  have hdet' : Matrix.det (Matrix.of ![r, r', t]) = t ⬝ᵥ crossProduct r r' := by
    rw [Matrix.det_fin_three, cross_apply]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, dotProduct, Fin.sum_univ_three]
    ring
  have hdet : Matrix.det (Matrix.of ![r, r', t]) = 1 := by
    rw [hdet', hdot, inv_mul_cancel₀ hj]
  set A : SL3 F := ⟨Matrix.of ![r, r', t], hdet⟩ with hA
  have hAv : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ crossProduct r r' = Pi.single 2 1 := by
    funext i
    fin_cases i
    · show r ⬝ᵥ crossProduct r r' = _
      rw [dot_self_cross]
      rfl
    · show r' ⬝ᵥ crossProduct r r' = _
      rw [dot_cross_self]
      rfl
    · show t ⬝ᵥ crossProduct r r' = _
      rw [hdot, inv_mul_cancel₀ hj]
      rfl
  refine ⟨A, rfl, rfl, ?_⟩
  rw [← hAv, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem exists_smul_eq_of_cross_eq_zero {r r' : Fin 3 → F} (hr : r ≠ 0)
    (h : crossProduct r r' = 0) : ∃ a : F, r' = a • r := by
  have hli : ¬ LinearIndependent F ![r, r'] := fun hli =>
    (crossProduct_ne_zero_iff_linearIndependent.mpr hli) h
  rw [LinearIndependent.pair_iff] at hli
  push Not at hli
  obtain ⟨s, t, hst, hne⟩ := hli
  have ht : t ≠ 0 := by
    intro ht0
    rw [ht0, zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with hs | hr0
    · exact hne hs ht0
    · exact hr hr0
  refine ⟨-(t⁻¹ * s), ?_⟩
  have h1 : t • r' = -(s • r) := eq_neg_of_add_eq_zero_right hst
  calc r' = t⁻¹ • (t • r') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = -(t⁻¹ * s) • r := by rw [h1, smul_neg, smul_smul, neg_smul]

theorem pencil_sum_eq_zero :
    ((List.finRange 6).map fun i => if pencil i then lv i else 0).sum = 0 := by
  decide

theorem sum_pencil_embv [CharP F 2] :
    ((List.finRange 6).map fun i =>
      (if pencil i then (1 : F) else 0) • embv (F := F) (lv i)).sum = 0 := by
  have key : ∀ xs : List (Fin 6), (xs.map fun i =>
      (if pencil i then (1 : F) else 0) • embv (F := F) (lv i)).sum =
        embv (F := F) ((xs.map fun i => if pencil i then lv i else 0).sum) := by
    intro xs
    induction xs with
    | nil => simp [embv_zero]
    | cons i xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, embv_add]
      by_cases hp : pencil i = true
      · simp [hp]
      · simp [hp, embv_zero]
  rw [key, pencil_sum_eq_zero, embv_zero]

end Lin

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)} {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}

theorem natVecG_commutator_rows (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    {E : ↥(stab (puAmalgam c.pu.le) α)}
    (hE : (toSL3 ψ E : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 1 1)
    (h h' : ↥(stab (puAmalgam c.pu.le) α)) :
    natVecG d.lh.nat ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h,
        (h' : (puAmalgam c.pu.le).Universal)⁻¹ * z * h'⁆ =
      natVecG d.lh.nat ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ 2 •
        crossProduct ((toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0)
          ((toSL3 ψ h' : Matrix (Fin 3) (Fin 3) F) 0) := by
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  by_cases hc : crossProduct ((toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0)
      ((toSL3 ψ h' : Matrix (Fin 3) (Fin 3) F) 0) = 0
  · rw [hc, smul_zero]
    obtain ⟨a, ha⟩ := exists_smul_eq_of_cross_eq_zero (row_ne_zero (toSL3 ψ h)) hc
    have hrow : (toSL3 ψ (h' * h⁻¹) : Matrix (Fin 3) (Fin 3) F) 0 = a • Pi.single 0 1 := by
      rw [map_mul, map_inv, row_mul, ha, Matrix.smul_vecMul]
      have h1 := row_mul (toSL3 ψ h) (toSL3 ψ h)⁻¹ 0
      rw [mul_inv_cancel, row_one] at h1
      rw [← h1]
    have h1 := commutator_eq_one_of_row d h2 hVU hz (h := h' * h⁻¹) hrow
    have e : ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h,
        (h' : (puAmalgam c.pu.le).Universal)⁻¹ * z * h'⁆ =
        (h : (puAmalgam c.pu.le).Universal)⁻¹ *
          ⁅((h' * h⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal)⁻¹ * z *
            ((h' * h⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal), z⁆⁻¹ *
          (h : (puAmalgam c.pu.le).Universal) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e, h1, inv_one, mul_one, inv_mul_cancel, natVecG_one]
  · obtain ⟨A, hA0, hA1, hAinv⟩ := exists_sl3_rows_cross hc
    obtain ⟨K, hK⟩ := toSL3_surjective d.lh.surj A
    have hcU : ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ ∈ Uloc c.pu.le L α :=
      hVU (Subgroup.commutator_mem_commutator hzV (inv_mul_mul_mem_vv d hzV E))
    have hconj := commutator_eq_conj d h2 hz hE (K := K) (h := h) (h' := h')
      (by rw [hK, hA0]) (by rw [hK, hA1])
    have e : (K : (puAmalgam c.pu.le).Universal)⁻¹ *
        ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ * K =
        ((K⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) *
          ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ *
          ((K⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal)⁻¹ := by
      simp
    have hc' := natVecG_commutator_conj_eq d hVU hz hE
    rw [hconj, e, natVecG_conj d.lh.nat K⁻¹ hcU]
    conv_lhs => rw [hc']
    rw [Matrix.mulVec_smul, map_inv, hK, hAinv]

section Prod

variable [CharP F 2]

theorem natVecG_commutator_zprod (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {w : Fin 6 → F → (puAmalgam c.pu.le).Universal}
    (hwV : ∀ i s, w i s ∈ Vv (puAmalgam c.pu.le) α) {v : (puAmalgam c.pu.le).Universal}
    (hv : v ∈ Vv (puAmalgam c.pu.le) α) {b : F} {m : Fin 3 → F}
    (hw : ∀ i t, natVecG d.lh.nat ⁅w i t, v⁆ = (t * b) • crossProduct (embv (lv i)) m)
    (s : Fin 6 → F) (xs : List (Fin 6)) :
    natVecG d.lh.nat ⁅zprod w s xs, v⁆ =
      b • crossProduct ((xs.map fun i => s i • embv (F := F) (lv i)).sum) m := by
  induction xs with
  | nil =>
    rw [zprod_nil, commutatorElement_one_left, natVecG_one, List.map_nil, List.sum_nil,
      map_zero, LinearMap.zero_apply, smul_zero]
  | cons i xs ih =>
    rw [zprod_cons, natVecG_commutator_mul_left d hVU (hwV i (s i)) (zprod_mem hwV s xs) hv, ih,
      hw, List.map_cons, List.sum_cons, map_add, LinearMap.add_apply, smul_add, map_smul,
      LinearMap.smul_apply, smul_smul, mul_comm b (s i)]

theorem natVecG_zprod_sq (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {w : Fin 6 → F → (puAmalgam c.pu.le).Universal}
    (hwV : ∀ i s, w i s ∈ Vv (puAmalgam c.pu.le) α) (hw2 : ∀ i s, w i s ^ 2 = 1) {κ : F}
    (hwc : ∀ i j s t, natVecG d.lh.nat ⁅w i s, w j t⁆ = (s * t * κ) • embv (tab i j))
    (s : Fin 6 → F) (xs : List (Fin 6)) :
    zprod w s xs ^ 2 ∈ Uloc c.pu.le L α ∧
      natVecG d.lh.nat (zprod w s xs ^ 2) = κ • qsumF s xs := by
  have hUQ : ∀ a ∈ Uloc c.pu.le L α, ∀ g ∈ Qv (puAmalgam c.pu.le) α, Commute a g :=
    fun _ ha _ hg => commute_of_mem_zm d (d.lh.uZ ha) hg
  have hbr : ∀ xs j t, ⁅zprod w s xs, w j t⁆ ∈ Uloc c.pu.le L α ∧
      natVecG d.lh.nat ⁅zprod w s xs, w j t⁆ = (t * κ) • bsumF s xs j := by
    intro xs j t
    induction xs with
    | nil =>
      rw [zprod_nil, commutatorElement_one_left, bsumF_nil, smul_zero, natVecG_one]
      exact ⟨Subgroup.one_mem _, rfl⟩
    | cons i xs ih =>
      obtain ⟨ihU, ihv⟩ := ih
      rw [zprod_cons, bsumF_cons]
      have haU : ⁅w i (s i), w j t⁆ ∈ Uloc c.pu.le L α :=
        hVU (Subgroup.commutator_mem_commutator (hwV i (s i)) (hwV j t))
      rw [commutator_mul_of_commute (hUQ _ ihU _ (d.lh.vq (hwV i (s i))))]
      refine ⟨(Uloc c.pu.le L α).mul_mem ihU haU, ?_⟩
      rw [natVecG_mul d.lh.nat ihU haU, ihv, hwc, smul_add, smul_smul, add_comm]
      congr 2
      ring
  induction xs with
  | nil =>
    rw [zprod_nil, one_pow, qsumF_nil, smul_zero, natVecG_one]
    exact ⟨Subgroup.one_mem _, rfl⟩
  | cons i xs ih =>
    obtain ⟨ihU, ihv⟩ := ih
    rw [zprod_cons, qsumF_cons]
    obtain ⟨hcU, hcv⟩ := hbr xs i (s i)
    rw [mul_sq_of_commute (hw2 i (s i)) (hUQ _ hcU _ (d.lh.vq (hwV i (s i))))]
    refine ⟨(Uloc c.pu.le L α).mul_mem hcU ihU, ?_⟩
    rw [natVecG_mul d.lh.nat hcU ihU, hcv, ihv, smul_add, smul_smul, mul_comm (s i) κ]

end Prod

section Orbit

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] noncomputable def vOrb (α γ : Vtx X) : Subgroup X.Universal :=
  ⨆ g ∈ stab X α, ZM X (g • γ)

variable {X}

theorem zm_smul_le_vOrb {α γ : Vtx X} {g : X.Universal} (hg : g ∈ stab X α) :
    ZM X (g • γ) ≤ vOrb X α γ :=
  le_iSup₂_of_le (f := fun g (_ : g ∈ stab X α) => ZM X (g • γ)) g hg le_rfl

theorem conj_mem_vOrb {α γ : Vtx X} {k : X.Universal} (hk : k ∈ stab X α) {x : X.Universal}
    (hx : x ∈ vOrb X α γ) : k * x * k⁻¹ ∈ vOrb X α γ := by
  have hle : (vOrb X α γ).map (MulAut.conj k).toMonoidHom ≤ vOrb X α γ := by
    unfold vOrb
    rw [Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    rw [← zm_smul, smul_smul]
    exact zm_smul_le_vOrb (Subgroup.mul_mem _ hk hg)
  exact hle ⟨x, hx, rfl⟩

theorem vOrb_le_vv {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
    {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)} (d : X3Data c α β γ ψ) :
    vOrb (puAmalgam c.pu.le) α γ ≤ Vv (puAmalgam c.pu.le) α := by
  refine iSup₂_le fun g hg => ?_
  rw [zm_smul]
  rintro _ ⟨z, hz, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (d.lh.vN hg) z).mp (d.zγVα hz)

end Orbit

theorem zm_smul_le_qv_of_row21_cfg (h464 : I464) (h465 : I465) (h466a : I466a) (h467 : I467)
    (h469 : I469Cfg M T L φ) (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α) :
    ∀ g ∈ stab (puAmalgam c.pu.le) α, ZM (puAmalgam c.pu.le) (g • γ) ≤ Qv _ γ := by
  have : CharP F 2 := charP_two_of_isSL3FullVia c.via
  intro g hg
  by_contra hle
  have hb : 2 < critDist (puAmalgam c.pu.le) := critDist_gt_two c
  have hB := h467 G M T L F φ c α d.mα
  have hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α :=
    (h469 c α β d.mα d.adjαβ).2.1.le
  obtain ⟨z₁, hz₁, hz₁α⟩ : ∃ z ∈ ZM (puAmalgam c.pu.le) γ, z ∉ ZM (puAmalgam c.pu.le) α := by
    by_contra hcon
    push Not at hcon
    exact d.zγ (fun y hy => zm_le_bloc c.pu hb d.mα (hcon y hy))
  have hz₁V : z₁ ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz₁
  have he1 : (Pi.single 1 1 : Fin 3 → ZMod 2) ≠ 0 := by decide
  have he0 : (Pi.single 0 1 : Fin 3 → ZMod 2) ≠ 0 := by decide
  have he10 : (Pi.single 1 1 : Fin 3 → ZMod 2) ≠ Pi.single 0 1 := by decide
  obtain ⟨E, hE⟩ := toSL3_surjective d.lh.surj (matF (F := F) he1 he0 he10)
  have hErow : (toSL3 ψ E : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 1 1 := by
    rw [hE, matF_zero, embv_single]
  have hκ := natVecG_commutator_ne_zero h466a h467 d h2 hVU hz₁ hz₁α hErow hg hle
  set κ := natVecG d.lh.nat ⁅z₁, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z₁ * E⁆ 2 with hκdef
  choose zs hzs hzsF using fun s : F =>
    exists_natVecG_commutator_smul h465 h466a h467 d h2 hVU hz₁ hz₁α s
  have hnx : ∀ i : Fin 6, lv i ≠ lv (if i = 0 then 1 else 0) := by decide
  choose P hP using fun i : Fin 6 => toSL3_surjective d.lh.surj
    (matF (F := F) (lv_ne_zero i) (lv_ne_zero _) (hnx i))
  have hProw : ∀ i, (toSL3 ψ (P i) : Matrix (Fin 3) (Fin 3) F) 0 = embv (lv i) :=
    fun i => by rw [hP, matF_zero]
  have hz2 : ∀ s, zs s ^ 2 = 1 := fun s =>
    (isElemAbelian_zm _ c.pu.hyp20 (by have := c.b4; omega) d.mγ).2 _ (hzs s)
  set w : Fin 6 → F → (puAmalgam c.pu.le).Universal :=
    fun i s => (P i : (puAmalgam c.pu.le).Universal)⁻¹ * zs s * P i with hw
  have hwV : ∀ i s, w i s ∈ Vv (puAmalgam c.pu.le) α :=
    fun i s => inv_mul_mul_mem_vv d (d.zγVα (hzs s)) (P i)
  have hwS : ∀ i s, w i s ∈ vStar c.pu.le L α :=
    fun i s => zm_smul_le_vStar d (P i)⁻¹.2 (inv_mul_mul_mem_zm c (hzs s) (P i))
  have hw2 : ∀ i s, w i s ^ 2 = 1 := by
    intro i s
    have e : ((P i : (puAmalgam c.pu.le).Universal)⁻¹ * zs s * P i) ^ 2 =
        (P i : (puAmalgam c.pu.le).Universal)⁻¹ * zs s ^ 2 * P i := by
      simp only [sq]
      group
    rw [hw]
    simp only
    rw [e, hz2, mul_one, inv_mul_cancel]
  have hwc : ∀ i j s t, natVecG d.lh.nat ⁅w i s, w j t⁆ = (s * t * κ) • embv (tab i j) := by
    intro i j s t
    rw [natVecG_commutator_conj_smul_smul d hVU hz₁V (d.zγVα (hzs s)) (d.zγVα (hzs t))
      (hzsF s) (hzsF t) (P i) (P j), natVecG_commutator_points d h2 hVU hz₁ hErow hProw,
      smul_smul]
  set e : Fin 6 → F := fun i => if pencil i then (1 : F) else 0 with he
  set y₀ := zprod w e (List.finRange 6) with hy₀
  have hy₀V : y₀ ∈ Vv (puAmalgam c.pu.le) α := zprod_mem hwV e _
  have hy₀c : ∀ (h : ↥(stab (puAmalgam c.pu.le) α)) (z' : (puAmalgam c.pu.le).Universal),
      z' ∈ ZM (puAmalgam c.pu.le) γ →
        ⁅y₀, (h : (puAmalgam c.pu.le).Universal)⁻¹ * z' * h⁆ = 1 := by
    intro h z' hz'
    obtain ⟨a', ha'⟩ := exists_smul_natVecG_commutator h466a h467 d h2 hVU hz₁ hz₁α hz'
    have hv : (h : (puAmalgam c.pu.le).Universal)⁻¹ * z' * h ∈ Vv (puAmalgam c.pu.le) α :=
      inv_mul_mul_mem_vv d (d.zγVα hz') h
    have hpt : ∀ i t, natVecG d.lh.nat ⁅w i t, (h : (puAmalgam c.pu.le).Universal)⁻¹ * z' * h⁆ =
        (t * (a' * κ)) • crossProduct (embv (lv i))
          ((toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0) := by
      intro i t
      rw [hw]
      simp only
      rw [natVecG_commutator_conj_smul_smul d hVU hz₁V (d.zγVα (hzs t)) (d.zγVα hz') (hzsF t)
        ha' (P i) h, natVecG_commutator_rows d h2 hVU hz₁ hErow (P i) h, hProw, smul_smul,
        ← hκdef]
      ring_nf
    have hc := natVecG_commutator_zprod d hVU hwV hv hpt e (List.finRange 6)
    rw [sum_pencil_embv, map_zero, LinearMap.zero_apply, smul_zero] at hc
    have hcU : ⁅y₀, (h : (puAmalgam c.pu.le).Universal)⁻¹ * z' * h⁆ ∈ Uloc c.pu.le L α :=
      hVU (Subgroup.commutator_mem_commutator hy₀V hv)
    exact natVecG_injective d.lh.nat hcU (Subgroup.one_mem _) (by rw [hc, natVecG_one])
  set V₀ := vOrb (puAmalgam c.pu.le) α γ with hV₀
  have hV₀V : V₀ ≤ Vv (puAmalgam c.pu.le) α := vOrb_le_vv d
  set C : Subgroup (puAmalgam c.pu.le).Universal :=
    V₀ ⊓ Subgroup.centralizer (V₀ : Set (puAmalgam c.pu.le).Universal) with hC
  have hCV : C ≤ Vv (puAmalgam c.pu.le) α := inf_le_left.trans hV₀V
  have hy₀C : y₀ ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨zprod_mem (fun i s => ?_) e _, ?_⟩
    · have := inv_mul_mul_mem_zm c (hzs s) (P i)
      exact zm_smul_le_vOrb ((P i)⁻¹.2) this
    · rw [Subgroup.mem_centralizer_iff]
      have hle' : V₀ ≤ Subgroup.centralizer ({y₀} : Set (puAmalgam c.pu.le).Universal) := by
        refine iSup₂_le fun k hk => ?_
        rw [zm_smul]
        rintro _ ⟨z', hz', rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        have h1 := hy₀c ⟨k, hk⟩⁻¹ z' hz'
        have e1 : (((⟨k, hk⟩ : ↥(stab (puAmalgam c.pu.le) α))⁻¹ :
            ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal)⁻¹ * z' *
            (((⟨k, hk⟩ : ↥(stab (puAmalgam c.pu.le) α))⁻¹ :
              ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) =
            (MulAut.conj k).toMonoidHom z' := by
          simp
        rw [e1] at h1
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (hle' hv) y₀ rfl).symm
  have hCn : stab (puAmalgam c.pu.le) α ≤
      Subgroup.normalizer (C : Set (puAmalgam c.pu.le).Universal) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ k ∈ stab (puAmalgam c.pu.le) α, ∀ x ∈ C, k * x * k⁻¹ ∈ C := by
      intro k hk x hx
      refine Subgroup.mem_inf.mpr ⟨conj_mem_vOrb hk hx.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : k⁻¹ * v * k⁻¹⁻¹ ∈ V₀ := conj_mem_vOrb (Subgroup.inv_mem _ hk) hv
      have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
      calc v * (k * x * k⁻¹) = k * ((k⁻¹ * v * k⁻¹⁻¹) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * v * k⁻¹⁻¹)) * k⁻¹ := by rw [h1]
        _ = k * x * k⁻¹ * v := by group
    intro x
    refine ⟨key k hk x, fun hx => ?_⟩
    have := key k⁻¹ (Subgroup.inv_mem _ hk) _ hx
    simpa [mul_assoc] using this
  obtain ⟨x₀, hx₀, hx₀z⟩ : ∃ x ∈ V₀, ⁅z₁, x⁆ ≠ 1 := by
    obtain ⟨x, hx, hxQ⟩ := Set.not_subset.mp hle
    have hxV₀ : x ∈ V₀ := zm_smul_le_vOrb hg hx
    have hxV : x ∈ Vv (puAmalgam c.pu.le) α := hV₀V hxV₀
    obtain ⟨z, hz, hxz⟩ : ∃ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅x, z⁆ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hxQ (d.mem_qv_of_commute hxV hcon)
    obtain ⟨a, ha⟩ := exists_smul_natVecG_commutator h466a h467 d h2 hVU hz₁ hz₁α hz
    refine ⟨x, hxV₀, fun h1 => hxz ?_⟩
    have hzx : ⁅z, x⁆ = 1 := by
      have hU : ⁅z, x⁆ ∈ Uloc c.pu.le L α :=
        hVU (Subgroup.commutator_mem_commutator (d.zγVα hz) hxV)
      refine natVecG_injective d.lh.nat hU (Subgroup.one_mem _) ?_
      rw [ha x hxV, h1, natVecG_one, smul_zero]
    rw [← commutatorElement_inv, hzx, inv_one]
  have hCQ : C ≤ Qv (puAmalgam c.pu.le) γ := fun x hx => d.mem_qv_of_commute (hCV hx)
    (fun z hz => commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hx.2 z (zm_smul_le_vOrb (Subgroup.one_mem _)
        (by rwa [one_smul]))).symm)
  have hCT : ⁅C, Qv (puAmalgam c.pu.le) β⁆ ≤ Bloc c.pu.le L α := by
    rw [Subgroup.commutator_le]
    intro x hx t ht
    have hxt : ⁅x, t⁆ ∈ C := by
      rw [commutatorElement_def]
      have h1 : t * x⁻¹ * t⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hCn (d.qβK ht)) _).mp (C.inv_mem hx)
      have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
      rw [e]
      exact C.mul_mem hx h1
    have hxtZ := d.commutator_qv_le hCV hCQ (Subgroup.commutator_mem_commutator hx ht)
    obtain ⟨z, hz, a, ha, hza⟩ := exists_mul_eq_of_mem_sup_of_conj
      (A := ZM (puAmalgam c.pu.le) γ) (B := ZM (puAmalgam c.pu.le) α)
      (fun b hb a ha => (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ γ
        (d.qβKγ (d.qαβ (d.lh.zv.trans d.lh.vq hb)))) a).mp ha) hxtZ
    have haB : a ∈ Bloc c.pu.le L α := zm_le_bloc c.pu hb d.mα ha
    have haC : ∀ v ∈ Vv (puAmalgam c.pu.le) α, a * v = v * a := by
      intro v hv
      have := haB
      rw [hB] at this
      exact (Subgroup.mem_centralizer_iff.mp this.2 v hv).symm
    have hzV₀ : ∀ v ∈ V₀, ⁅z, v⁆ = 1 := by
      intro v hv
      have hvV := hV₀V hv
      have hz' : z = ⁅x, t⁆ * a⁻¹ := by rw [← hza, mul_inv_cancel_right]
      rw [commutatorElement_eq_one_iff_mul_comm, hz']
      have h1 := (Subgroup.mem_centralizer_iff.mp hxt.2 v hv)
      have h2 : a⁻¹ * v = v * a⁻¹ := by
        have := haC v hvV
        calc a⁻¹ * v = a⁻¹ * (v * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * v) * a⁻¹ := by rw [this]
          _ = v * a⁻¹ := by group
      calc ⁅x, t⁆ * a⁻¹ * v = ⁅x, t⁆ * (a⁻¹ * v) := by group
        _ = ⁅x, t⁆ * (v * a⁻¹) := by rw [h2]
        _ = (⁅x, t⁆ * v) * a⁻¹ := by group
        _ = (v * ⁅x, t⁆) * a⁻¹ := by rw [h1]
        _ = v * (⁅x, t⁆ * a⁻¹) := by group
    obtain ⟨a', ha'⟩ := exists_smul_natVecG_commutator h466a h467 d h2 hVU hz₁ hz₁α hz
    have hx₀V := hV₀V hx₀
    have ha'0 : a' = 0 := by
      have h1 := ha' x₀ hx₀V
      rw [hzV₀ x₀ hx₀, natVecG_one] at h1
      have hne : natVecG d.lh.nat ⁅z₁, x₀⁆ ≠ 0 := by
        intro h0
        apply hx₀z
        have hU : ⁅z₁, x₀⁆ ∈ Uloc c.pu.le L α :=
          hVU (Subgroup.commutator_mem_commutator hz₁V hx₀V)
        exact natVecG_injective d.lh.nat hU (Subgroup.one_mem _) (by rw [h0, natVecG_one])
      exact (smul_eq_zero.mp h1.symm).resolve_right hne
    have hzB : z ∈ Bloc c.pu.le L α := by
      rw [hB]
      refine Subgroup.mem_inf.mpr ⟨d.zγVα hz, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hU : ⁅z, v⁆ ∈ Uloc c.pu.le L α :=
        hVU (Subgroup.commutator_mem_commutator (d.zγVα hz) hv)
      have h1 : ⁅z, v⁆ = 1 := natVecG_injective d.lh.nat hU (Subgroup.one_mem _)
        (by rw [ha' v hv, ha'0, zero_smul, natVecG_one])
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    rw [← hza]
    exact (Bloc c.pu.le L α).mul_mem hzB haB
  have hCB := le_bloc_of_commutator_qv_le_cfg h464 h467 h469 d hCV hCn hCT
  have hy₀Z := d.star ⟨zprod_mem hwS e _, hCB hy₀C⟩
  have hv := (natVecG_zprod_sq d hVU hwV hw2 hwc e (List.finRange 6)).2
  rw [d.lh.z2 _ hy₀Z, natVecG_one, he, qsumF_ind] at hv
  exact qsum_pencil (embv_injective (F := F) (by
    rw [embv_zero]
    exact (smul_eq_zero.mp hv.symm).resolve_left hκ))

theorem zm_smul_le_qv_of_row21 (h464 : I464) (h465 : I465) (h466a : I466a) (h467 : I467)
    (h469 : I469) (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α) :
    ∀ g ∈ stab (puAmalgam c.pu.le) α, ZM (puAmalgam c.pu.le) (g • γ) ≤ Qv _ γ :=
  zm_smul_le_qv_of_row21_cfg h464 h465 h466a h467 (h469 G M T L F φ) d h2

theorem kc4612Cfg_of_kc2 (hKC : KC4612TwoCfg M T L φ) (h43 : S43) (h463 : I463) (h464 : I464)
    (h465 : I465) (h466a : I466a) (h466b : I466b) (h467 : I467) (h469 : I469Cfg M T L φ) :
    KC4612Cfg M T L φ := by
  intro c α α' hc g hg
  have hb4 := c.b4
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by omega
  have hα : IsMVtx (puAmalgam c.pu.le) α := hc.1
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) :=
    adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hZγ := zm_geo_two_not_le_bloc h43 h467 c hc
  obtain ⟨ψ, hψs, hψU, hψT⟩ := exists_coord_qv h464 h465 h466a c hα hαβ
  have d := X3Data.ofCfg h463 h464 h465 h466b h467 h469 c hα hαβ hβγ hZγ hψs hψU hψT
  refine zm_smul_le_qv_of_row21_cfg h464 h465 h466a h467 h469 d (fun k hk z hz => ?_) g hg
  by_cases hq : Fintype.card F = 2
  · exact hKC c α _ _ hα hαβ hβγ hZγ ψ hψs hψU hψT hq k hk z hz
  · have hq4 : 4 ≤ Fintype.card F := by
      have := four_le_card_of_isSL3FullVia c.via (by rwa [Nat.card_eq_fintype_card])
      rwa [Nat.card_eq_fintype_card] at this
    exact KC.commutator_mem_of_rootGroup21 d hq4 hk (Subgroup.mem_sup_left hz)

theorem kc4612_of_kc2 (hKC : KC4612Two) (h43 : S43) (h463 : I463) (h464 : I464) (h465 : I465)
    (h466a : I466a) (h466b : I466b) (h467 : I467) (h469 : I469) : KC4612 :=
  fun G _ _ M T L F _ _ φ => kc4612Cfg_of_kc2 (hKC G M T L F φ) h43 h463 h464 h465 h466a h466b
    h467 (h469 G M T L F φ)

end CFSG.Quasithin.MS93.S46R
