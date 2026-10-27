module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res2ProofG2
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofSeven
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.RankThree.PartTwo.Sec6

namespace Res611G2Cent

open CFSG.RankThree.PartTwo.Sec21.Item223RankResProof CFSG.RankThree.PartOne.SEITZ11 Matrix

variable {K : Type*} [Field K]

theorem bil7_comm (u v : Fin 7 → K) : bil7 u v = bil7 v u := by
  rw [bil7_eq, bil7_eq]
  ring

theorem bil7_add_right (u v w : Fin 7 → K) : bil7 u (v + w) = bil7 u v + bil7 u w := by
  simp [bil7, Matrix.mulVec_add, dotProduct_add]

theorem bil7_add_left (u v w : Fin 7 → K) : bil7 (u + v) w = bil7 u w + bil7 v w := by
  rw [bil7_comm, bil7_add_right, bil7_comm w u, bil7_comm w v]

theorem bil7_smul_right (c : K) (u v : Fin 7 → K) : bil7 u (c • v) = c * bil7 u v := by
  simp [bil7, Matrix.mulVec_smul, dotProduct_smul]

theorem bil7_neg_right (u v : Fin 7 → K) : bil7 u (-v) = -bil7 u v := by
  simp [bil7, Matrix.mulVec_neg, dotProduct_neg]

theorem bil7_mulVec {M : Matrix (Fin 7) (Fin 7) K}
    (hM : M.transpose * G2Seven.gram K * M = G2Seven.gram K) (u v : Fin 7 → K) :
    bil7 (M *ᵥ u) (M *ᵥ v) = bil7 u v := by
  unfold bil7
  generalize hw : G2Seven.gram K *ᵥ (M *ᵥ v) = w
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose,
    ← hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

theorem cross7_add_right (u v w : Fin 7 → K) : cross7 u (v + w) = cross7 u v + cross7 u w := by
  funext k
  fin_cases k <;> simp [cross7] <;> ring

theorem cross7_neg_left (u v : Fin 7 → K) : cross7 (-u) v = -cross7 u v := by
  funext k
  fin_cases k <;> simp [cross7] <;> ring

theorem cross7_neg_right (u v : Fin 7 → K) : cross7 u (-v) = -cross7 u v := by
  funext k
  fin_cases k <;> simp [cross7] <;> ring

theorem cross7_zero_right (u : Fin 7 → K) : cross7 u 0 = 0 := by
  funext k
  fin_cases k <;> simp [cross7]

@[expose] def crossL (a : Fin 7 → K) : (Fin 7 → K) →ₗ[K] (Fin 7 → K) where
  toFun := cross7 a
  map_add' := cross7_add_right a
  map_smul' c y := cross7_smul_right c a y

@[expose] def bilL (a : Fin 7 → K) : (Fin 7 → K) →ₗ[K] K where
  toFun := bil7 a
  map_add' := bil7_add_right a
  map_smul' c y := bil7_smul_right c a y

@[expose] def eigP (M : Matrix (Fin 7) (Fin 7) K) : Submodule K (Fin 7 → K) :=
  LinearMap.ker (M.mulVecLin - LinearMap.id)

@[expose] def eigM (M : Matrix (Fin 7) (Fin 7) K) : Submodule K (Fin 7 → K) :=
  LinearMap.ker (M.mulVecLin + LinearMap.id)

theorem mem_eigP {M : Matrix (Fin 7) (Fin 7) K} {v : Fin 7 → K} : v ∈ eigP M ↔ M *ᵥ v = v := by
  simp [eigP, sub_eq_zero]

theorem mem_eigM {M : Matrix (Fin 7) (Fin 7) K} {v : Fin 7 → K} : v ∈ eigM M ↔ M *ᵥ v = -v := by
  simp [eigM, add_eq_zero_iff_eq_neg]

variable {M : Matrix (Fin 7) (Fin 7) K}

theorem half_add_mem_eigP (hM : M * M = 1) (v : Fin 7 → K) :
    (2 : K)⁻¹ • (v + M *ᵥ v) ∈ eigP M := by
  rw [mem_eigP, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec, hM,
    Matrix.one_mulVec, add_comm]

theorem half_sub_mem_eigM (hM : M * M = 1) (v : Fin 7 → K) :
    (2 : K)⁻¹ • (v - M *ᵥ v) ∈ eigM M := by
  rw [mem_eigM, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hM,
    Matrix.one_mulVec, ← smul_neg, neg_sub]

theorem half_decomp (h2 : (2 : K) ≠ 0) (v : Fin 7 → K) :
    v = (2 : K)⁻¹ • (v + M *ᵥ v) + (2 : K)⁻¹ • (v - M *ᵥ v) := by
  rw [← smul_add, add_add_sub_cancel, ← two_smul K v, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem finrank_split (h2 : (2 : K) ≠ 0) (hM : M * M = 1) (S : Submodule K (Fin 7 → K))
    (hS : ∀ v ∈ S, M *ᵥ v ∈ S) :
    Module.finrank K S = Module.finrank K ↥(S ⊓ eigP M) + Module.finrank K ↥(S ⊓ eigM M) := by
  have hinf : (S ⊓ eigP M) ⊓ (S ⊓ eigM M) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨-, hp⟩, -, hm⟩
    replace hp : M *ᵥ v = v := mem_eigP.mp hp
    replace hm : M *ᵥ v = -v := mem_eigM.mp hm
    rw [Submodule.mem_bot]
    have h : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rw 1 [← hp]
      rw [hm, neg_add_cancel]
    exact (smul_eq_zero.mp h).resolve_left h2
  have hsup : (S ⊓ eigP M) ⊔ (S ⊓ eigM M) = S := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro v hv
    rw [half_decomp (M := M) h2 v]
    exact Submodule.add_mem_sup ⟨S.smul_mem _ (S.add_mem hv (hS v hv)), half_add_mem_eigP hM v⟩
      ⟨S.smul_mem _ (S.sub_mem hv (hS v hv)), half_sub_mem_eigM hM v⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ eigP M) (S ⊓ eigM M)
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact h

theorem fix_of_split (h2 : (2 : K) ≠ 0) (hM : M * M = 1) {S : Submodule K (Fin 7 → K)}
    (hS : ∀ v ∈ S, M *ᵥ v ∈ S) {N : Matrix (Fin 7) (Fin 7) K}
    (hP : ∀ v ∈ S ⊓ eigP M, N *ᵥ v = v) (hQ : ∀ v ∈ S ⊓ eigM M, N *ᵥ v = v) :
    ∀ v ∈ S, N *ᵥ v = v := by
  intro v hv
  rw [half_decomp (M := M) h2 v, Matrix.mulVec_add,
    hP _ ⟨S.smul_mem _ (S.add_mem hv (hS v hv)), half_add_mem_eigP hM v⟩,
    hQ _ ⟨S.smul_mem _ (S.sub_mem hv (hS v hv)), half_sub_mem_eigM hM v⟩]

theorem bil7_eq_zero_of_eig (h2 : (2 : K) ≠ 0)
    (hMB : M.transpose * G2Seven.gram K * M = G2Seven.gram K) {v w : Fin 7 → K}
    (hv : v ∈ eigP M) (hw : w ∈ eigM M) : bil7 v w = 0 := by
  have h := bil7_mulVec hMB v w
  rw [mem_eigP.mp hv, mem_eigM.mp hw, bil7_neg_right] at h
  have h' : (2 : K) * bil7 v w = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h').resolve_left h2

@[expose] def NondegOn (S : Submodule K (Fin 7 → K)) : Prop :=
  ∀ w ∈ S, (∀ x ∈ S, bil7 w x = 0) → w = 0

theorem nondegOn_top (h2 : (2 : K) ≠ 0) : NondegOn (⊤ : Submodule K (Fin 7 → K)) := by
  intro w _ hw
  apply Matrix.eq_zero_of_vecMul_eq_zero (gram_det_ne_zero h2)
  funext j
  have h := hw (Pi.single j 1) Submodule.mem_top
  rw [bil7, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h
  simpa using h

theorem nondegOn_inf_eigP (h2 : (2 : K) ≠ 0) (hM : M * M = 1)
    (hMB : M.transpose * G2Seven.gram K * M = G2Seven.gram K) {S : Submodule K (Fin 7 → K)}
    (hS : ∀ v ∈ S, M *ᵥ v ∈ S) (hN : NondegOn S) : NondegOn (S ⊓ eigP M) := by
  intro w hw hw0
  apply hN w hw.1
  intro x hx
  rw [half_decomp (M := M) h2 x, bil7_add_right,
    hw0 _ ⟨S.smul_mem _ (S.add_mem hx (hS x hx)), half_add_mem_eigP hM x⟩, zero_add]
  exact bil7_eq_zero_of_eig h2 hMB hw.2 (half_sub_mem_eigM hM x)

theorem nondegOn_inf_eigM (h2 : (2 : K) ≠ 0) (hM : M * M = 1)
    (hMB : M.transpose * G2Seven.gram K * M = G2Seven.gram K) {S : Submodule K (Fin 7 → K)}
    (hS : ∀ v ∈ S, M *ᵥ v ∈ S) (hN : NondegOn S) : NondegOn (S ⊓ eigM M) := by
  intro w hw hw0
  apply hN w hw.1
  intro x hx
  rw [half_decomp (M := M) h2 x, bil7_add_right,
    hw0 _ ⟨S.smul_mem _ (S.sub_mem hx (hS x hx)), half_sub_mem_eigM hM x⟩, add_zero, bil7_comm]
  exact bil7_eq_zero_of_eig h2 hMB (half_add_mem_eigP hM x) hw.2

theorem exists_bil7_ne_zero (h2 : (2 : K) ≠ 0) {S : Submodule K (Fin 7 → K)} (hN : NondegOn S)
    (hS : S ≠ ⊥) : ∃ a ∈ S, bil7 a a ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hS
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  apply hN w hw
  intro x hx
  have h1 := hall (w + x) (S.add_mem hw hx)
  rw [bil7_add_left, bil7_add_right, bil7_add_right, hall w hw, hall x hx, bil7_comm x w] at h1
  have h' : (2 : K) * bil7 w x = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h').resolve_left h2

@[simp] theorem crossL_apply (a y : Fin 7 → K) : crossL a y = cross7 a y := rfl

@[simp] theorem bilL_apply (a y : Fin 7 → K) : bilL a y = bil7 a y := rfl

theorem eq_one_of_forall_mulVec_eq {N : Matrix (Fin 7) (Fin 7) K} (h : ∀ v, N *ᵥ v = v) :
    N = 1 := by
  ext i j
  have h' := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h'
  rw [h', Matrix.one_apply, Pi.single_apply]

theorem mulVec_mem_eigP_of_commute {M' : Matrix (Fin 7) (Fin 7) K} (h : M * M' = M' * M)
    {v : Fin 7 → K} (hv : v ∈ eigP M) : M' *ᵥ v ∈ eigP M := by
  rw [mem_eigP] at hv ⊢
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv]

theorem mulVec_mem_eigM_of_commute {M' : Matrix (Fin 7) (Fin 7) K} (h : M * M' = M' * M)
    {v : Fin 7 → K} (hv : v ∈ eigM M) : M' *ᵥ v ∈ eigM M := by
  rw [mem_eigM] at hv ⊢
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_neg]

theorem eq_zero_of_cross7_eq_zero (h2 : (2 : K) ≠ 0) {a y : Fin 7 → K} (ha : bil7 a a ≠ 0)
    (hy : bil7 a y = 0) (hc : cross7 a y = 0) : y = 0 := by
  have h := cross7_cross7 a y a
  rw [hc, cross7_zero_right, hy, mul_zero, zero_smul, sub_zero, sub_zero, add_zero] at h
  have h4 : (4 : K) * bil7 a a ≠ 0 := by
    refine mul_ne_zero ?_ ha
    have e : (4 : K) = 2 * 2 := by norm_num
    rw [e]
    exact mul_ne_zero h2 h2
  exact (smul_eq_zero.mp h.symm).resolve_left h4

theorem finrank_eigM_eq_four (h2 : (2 : K) ≠ 0) (hM : M * M = 1)
    (hMB : M.transpose * G2Seven.gram K * M = G2Seven.gram K)
    (hMX : ∀ u v, M *ᵥ cross7 u v = cross7 (M *ᵥ u) (M *ᵥ v)) (hM1 : M ≠ 1) :
    Module.finrank K (eigM M) = 4 := by
  have hsum : Module.finrank K (eigP M) + Module.finrank K (eigM M) = 7 := by
    have h := finrank_split h2 hM ⊤ (fun _ _ => Submodule.mem_top)
    rw [finrank_top, Module.finrank_fin_fun, top_inf_eq, top_inf_eq] at h
    omega
  have hQ : eigM M ≠ ⊥ := by
    intro hQ
    apply hM1
    refine eq_one_of_forall_mulVec_eq fun v => ?_
    have hm := half_sub_mem_eigM hM v
    rw [hQ, Submodule.mem_bot] at hm
    have h := (smul_eq_zero.mp hm).resolve_left (inv_ne_zero h2)
    rw [sub_eq_zero] at h
    exact h.symm
  have hNQ : NondegOn (eigM M) := by
    have h := nondegOn_inf_eigM h2 hM hMB (fun _ _ => Submodule.mem_top) (nondegOn_top h2)
    rwa [top_inf_eq] at h
  obtain ⟨a, haQ, ha⟩ := exists_bil7_ne_zero h2 hNQ hQ
  have haM : M *ᵥ a = -a := mem_eigM.mp haQ
  have hPQ : ∀ y ∈ eigP M, crossL a y ∈ eigM M := by
    intro y hy
    rw [mem_eigM, crossL_apply, hMX, haM, mem_eigP.mp hy, cross7_neg_left]
  have hQP : ∀ y ∈ eigM M ⊓ LinearMap.ker (bilL a), crossL a y ∈ eigP M := by
    intro y hy
    rw [mem_eigP, crossL_apply, hMX, haM, mem_eigM.mp hy.1, cross7_neg_left, cross7_neg_right,
      neg_neg]
  have h1 : Module.finrank K (eigP M) ≤ Module.finrank K (eigM M) := by
    apply LinearMap.finrank_le_finrank_of_injective (f := (crossL a).restrict hPQ)
    refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
    have hc : cross7 a (y : Fin 7 → K) = 0 := congrArg Subtype.val hy
    have hB : bil7 a (y : Fin 7 → K) = 0 := by
      rw [bil7_comm]
      exact bil7_eq_zero_of_eig h2 hMB y.2 haQ
    exact Subtype.ext (eq_zero_of_cross7_eq_zero h2 ha hB hc)
  have h2' : Module.finrank K ↥(eigM M ⊓ LinearMap.ker (bilL a)) ≤
      Module.finrank K (eigP M) := by
    apply LinearMap.finrank_le_finrank_of_injective (f := (crossL a).restrict hQP)
    refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
    have hc : cross7 a (y : Fin 7 → K) = 0 := congrArg Subtype.val hy
    have hB : bil7 a (y : Fin 7 → K) = 0 := LinearMap.mem_ker.mp y.2.2
    exact Subtype.ext (eq_zero_of_cross7_eq_zero h2 ha hB hc)
  have h3 : Module.finrank K (eigM M) ≤
      Module.finrank K ↥(eigM M ⊓ LinearMap.ker (bilL a)) + 1 := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq (eigM M) (LinearMap.ker (bilL a))
    have hsup : Module.finrank K ↥(eigM M ⊔ LinearMap.ker (bilL a)) ≤ 7 := by
      have h := Submodule.finrank_le (eigM M ⊔ LinearMap.ker (bilL a))
      rwa [Module.finrank_fin_fun] at h
    have hker : 6 ≤ Module.finrank K (LinearMap.ker (bilL a)) := by
      have hrk := LinearMap.finrank_range_add_finrank_ker (bilL a)
      have hr : Module.finrank K (LinearMap.range (bilL a)) ≤ 1 := by
        have h := Submodule.finrank_le (LinearMap.range (bilL a))
        rwa [Module.finrank_self] at h
      rw [Module.finrank_fin_fun] at hrk
      omega
    omega
  omega

theorem fix_of_finrank_le_two (h3 : (3 : K) = 0) (h2 : (2 : K) ≠ 0)
    {N : Matrix (Fin 7) (Fin 7) K} (hNB : N.transpose * G2Seven.gram K * N = G2Seven.gram K)
    (hN3 : N * (N * N) = 1) {W : Submodule K (Fin 7 → K)} (hW : Module.finrank K W ≤ 2)
    (hNW : ∀ w ∈ W, N *ᵥ w ∈ W) (hnd : NondegOn W) : ∀ w ∈ W, N *ᵥ w = w := by
  set T : (Fin 7 → K) →ₗ[K] (Fin 7 → K) := N.mulVecLin - LinearMap.id with hT
  have hTapp : ∀ w, T w = N *ᵥ w - w := fun w => by simp [hT]
  have hUW : ∀ w ∈ W, T w ∈ W := fun w hw => by
    rw [hTapp]
    exact W.sub_mem (hNW w hw) hw
  set U : Module.End K W := T.restrict hUW with hU
  have hUapp : ∀ w : W, ((U w : W) : Fin 7 → K) = N *ᵥ (w : Fin 7 → K) - w := fun w => by
    rw [hU, LinearMap.coe_restrict_apply, hTapp]
  have hU3 : U ^ 3 = 0 := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, hUapp, hUapp, hUapp,
      LinearMap.zero_apply, Submodule.coe_zero]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hN3, Matrix.one_mulVec]
    funext i
    simp only [Pi.sub_apply, Pi.zero_apply]
    linear_combination ((N *ᵥ (w : Fin 7 → K)) i - ((N * N) *ᵥ (w : Fin 7 → K)) i) * h3
  have hU2 : U ^ 2 = 0 := by
    have hk := Module.End.ker_pow_le_ker_pow_finrank U 3
    rw [hU3, LinearMap.ker_zero] at hk
    exact pow_eq_zero_of_le hW (LinearMap.ker_eq_top.mp (top_le_iff.mp hk))
  have hUU : ∀ w : W, U (U w) = 0 := fun w => by
    have h := congrArg (fun f : Module.End K W => f w) hU2
    simpa [pow_two] using h
  have hfixU : ∀ w : W, N *ᵥ ((U w : W) : Fin 7 → K) = U w := fun w => by
    have h := congrArg Subtype.val (hUU w)
    rw [hUapp, Submodule.coe_zero, sub_eq_zero] at h
    exact h
  have hNw : ∀ w : W, N *ᵥ (w : Fin 7 → K) = w + U w := fun w => by
    rw [hUapp]
    abel
  have hUU0 : ∀ v w : W, bil7 (U v : Fin 7 → K) (U w) = 0 := fun v w => by
    have h := bil7_mulVec hNB (U v : Fin 7 → K) w
    rw [hfixU, hNw, bil7_add_right] at h
    linear_combination h
  have hskew : ∀ v w : W, bil7 (U v : Fin 7 → K) w + bil7 (v : Fin 7 → K) (U w) = 0 := by
    intro v w
    have h := bil7_mulVec hNB v w
    rw [hNw, hNw, bil7_add_left, bil7_add_right, bil7_add_right, hUU0] at h
    linear_combination h
  have hself : ∀ v : W, bil7 (U v : Fin 7 → K) v = 0 := fun v => by
    have h := hskew v v
    rw [bil7_comm (v : Fin 7 → K)] at h
    have h' : (2 : K) * bil7 (U v : Fin 7 → K) v = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have hrange : Module.finrank K (LinearMap.range U) ≤ 1 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker U
    have hle : LinearMap.range U ≤ LinearMap.ker U := by
      rintro _ ⟨w, rfl⟩
      exact LinearMap.mem_ker.mpr (hUU w)
    have h := Submodule.finrank_mono hle
    omega
  intro w hw
  by_contra hne
  have hUw : U ⟨w, hw⟩ ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg Subtype.val h
    rw [hUapp, Submodule.coe_zero, sub_eq_zero] at h'
    exact h'
  set R := LinearMap.range U with hR
  set x : R := ⟨U ⟨w, hw⟩, LinearMap.mem_range_self U _⟩ with hx
  have hx0 : x ≠ 0 := fun h => hUw (congrArg Subtype.val h)
  have hrank1 : Module.finrank K R = 1 := by
    have hpos : 0 < Module.finrank K R := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx0⟩
    omega
  apply hUw
  apply Subtype.ext
  apply hnd _ (U ⟨w, hw⟩).2
  intro y hy
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (V := R) hrank1 hx0
    (⟨U ⟨y, hy⟩, LinearMap.mem_range_self U _⟩ : R)
  have hc' : c • ((U ⟨w, hw⟩ : W) : Fin 7 → K) = U ⟨y, hy⟩ := by
    have h := congrArg (fun z : R => ((z : W) : Fin 7 → K)) hc
    simpa [hx] using h
  have h := hskew ⟨w, hw⟩ ⟨y, hy⟩
  rw [← hc', bil7_smul_right, bil7_comm (w : Fin 7 → K)] at h
  have h0 := hself ⟨w, hw⟩
  simp only at h h0
  rw [h0, mul_zero, add_zero] at h
  exact h

theorem eq_one_of_commute (h3 : (3 : K) = 0) {M₁ M₂ N : Matrix (Fin 7) (Fin 7) K}
    (hM₁ : M₁ * M₁ = 1) (hM₂ : M₂ * M₂ = 1) (h12 : M₁ * M₂ = M₂ * M₁)
    (hB₁ : M₁.transpose * G2Seven.gram K * M₁ = G2Seven.gram K)
    (hB₂ : M₂.transpose * G2Seven.gram K * M₂ = G2Seven.gram K)
    (hX₁ : ∀ u v, M₁ *ᵥ cross7 u v = cross7 (M₁ *ᵥ u) (M₁ *ᵥ v))
    (hX₂ : ∀ u v, M₂ *ᵥ cross7 u v = cross7 (M₂ *ᵥ u) (M₂ *ᵥ v))
    (hne₁ : M₁ ≠ 1) (hne₂ : M₂ ≠ 1) (hne₁₂ : M₁ * M₂ ≠ 1)
    (hNB : N.transpose * G2Seven.gram K * N = G2Seven.gram K) (hN3 : N * (N * N) = 1)
    (hN₁ : N * M₁ = M₁ * N) (hN₂ : N * M₂ = M₂ * N) : N = 1 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by linear_combination h3 - h
    exact one_ne_zero h1
  have hM₃ : (M₁ * M₂) * (M₁ * M₂) = 1 := by
    calc (M₁ * M₂) * (M₁ * M₂) = M₁ * (M₂ * M₁) * M₂ := by simp only [mul_assoc]
      _ = M₁ * (M₁ * M₂) * M₂ := by rw [h12]
      _ = (M₁ * M₁) * (M₂ * M₂) := by simp only [mul_assoc]
      _ = 1 := by rw [hM₁, hM₂, one_mul]
  have hB₃ : (M₁ * M₂).transpose * G2Seven.gram K * (M₁ * M₂) = G2Seven.gram K := by
    rw [Matrix.transpose_mul]
    calc M₂.transpose * M₁.transpose * G2Seven.gram K * (M₁ * M₂)
        = M₂.transpose * (M₁.transpose * G2Seven.gram K * M₁) * M₂ := by simp only [mul_assoc]
      _ = G2Seven.gram K := by rw [hB₁, hB₂]
  have hX₃ : ∀ u v, (M₁ * M₂) *ᵥ cross7 u v = cross7 ((M₁ * M₂) *ᵥ u) ((M₁ * M₂) *ᵥ v) := by
    intro u v
    rw [← Matrix.mulVec_mulVec, hX₂, hX₁, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have d₁ := finrank_eigM_eq_four h2 hM₁ hB₁ hX₁ hne₁
  have d₂ := finrank_eigM_eq_four h2 hM₂ hB₂ hX₂ hne₂
  have d₃ := finrank_eigM_eq_four h2 hM₃ hB₃ hX₃ hne₁₂
  have h13 : M₁ * (M₁ * M₂) = (M₁ * M₂) * M₁ := by
    rw [← mul_assoc, hM₁, one_mul, mul_assoc, ← h12, ← mul_assoc, hM₁, one_mul]
  have s₁ := finrank_split h2 hM₂ (eigM M₁) fun v hv => mulVec_mem_eigM_of_commute h12 hv
  have s₂ := finrank_split h2 hM₁ (eigM M₂) fun v hv => mulVec_mem_eigM_of_commute h12.symm hv
  have s₃ := finrank_split h2 hM₁ (eigM (M₁ * M₂)) fun v hv =>
    mulVec_mem_eigM_of_commute h13.symm hv
  have s₄ := finrank_split h2 hM₁ ⊤ fun _ _ => Submodule.mem_top
  have s₅ := finrank_split h2 hM₂ (eigP M₁) fun v hv => mulVec_mem_eigP_of_commute h12 hv
  have e₁ : eigM (M₁ * M₂) ⊓ eigP M₁ = eigP M₁ ⊓ eigM M₂ := by
    ext v
    simp only [Submodule.mem_inf, mem_eigP, mem_eigM]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨h', ?_⟩
      calc M₂ *ᵥ v = (M₁ * M₁ * M₂) *ᵥ v := by rw [hM₁, one_mul]
        _ = M₁ *ᵥ ((M₁ * M₂) *ᵥ v) := by rw [Matrix.mulVec_mulVec, mul_assoc]
        _ = -v := by rw [h, Matrix.mulVec_neg, h']
    · rintro ⟨h, h'⟩
      exact ⟨by rw [← Matrix.mulVec_mulVec, h', Matrix.mulVec_neg, h], h⟩
  have e₂ : eigM (M₁ * M₂) ⊓ eigM M₁ = eigM M₁ ⊓ eigP M₂ := by
    ext v
    simp only [Submodule.mem_inf, mem_eigP, mem_eigM]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨h', ?_⟩
      calc M₂ *ᵥ v = (M₁ * M₁ * M₂) *ᵥ v := by rw [hM₁, one_mul]
        _ = M₁ *ᵥ ((M₁ * M₂) *ᵥ v) := by rw [Matrix.mulVec_mulVec, mul_assoc]
        _ = v := by rw [h, Matrix.mulVec_neg, h', neg_neg]
    · rintro ⟨h, h'⟩
      exact ⟨by rw [← Matrix.mulVec_mulVec, h', h], h⟩
  rw [inf_comm (eigM M₂) (eigP M₁), inf_comm (eigM M₂) (eigM M₁)] at s₂
  rw [e₁, e₂] at s₃
  rw [finrank_top, Module.finrank_fin_fun, top_inf_eq, top_inf_eq] at s₄
  have hPP : Module.finrank K ↥(eigP M₁ ⊓ eigP M₂) ≤ 2 := by omega
  have hPM : Module.finrank K ↥(eigP M₁ ⊓ eigM M₂) ≤ 2 := by omega
  have hMP : Module.finrank K ↥(eigM M₁ ⊓ eigP M₂) ≤ 2 := by omega
  have hMM : Module.finrank K ↥(eigM M₁ ⊓ eigM M₂) ≤ 2 := by omega
  have nP : NondegOn (eigP M₁) := by
    have h := nondegOn_inf_eigP h2 hM₁ hB₁ (fun _ _ => Submodule.mem_top) (nondegOn_top h2)
    rwa [top_inf_eq] at h
  have nM : NondegOn (eigM M₁) := by
    have h := nondegOn_inf_eigM h2 hM₁ hB₁ (fun _ _ => Submodule.mem_top) (nondegOn_top h2)
    rwa [top_inf_eq] at h
  have iP : ∀ v ∈ eigP M₁, M₂ *ᵥ v ∈ eigP M₁ := fun v hv => mulVec_mem_eigP_of_commute h12 hv
  have iM : ∀ v ∈ eigM M₁, M₂ *ᵥ v ∈ eigM M₁ := fun v hv => mulVec_mem_eigM_of_commute h12 hv
  have hNP₁ : ∀ v ∈ eigP M₁, N *ᵥ v ∈ eigP M₁ := fun v hv =>
    mulVec_mem_eigP_of_commute hN₁.symm hv
  have hNM₁ : ∀ v ∈ eigM M₁, N *ᵥ v ∈ eigM M₁ := fun v hv =>
    mulVec_mem_eigM_of_commute hN₁.symm hv
  have hNP₂ : ∀ v ∈ eigP M₂, N *ᵥ v ∈ eigP M₂ := fun v hv =>
    mulVec_mem_eigP_of_commute hN₂.symm hv
  have hNM₂ : ∀ v ∈ eigM M₂, N *ᵥ v ∈ eigM M₂ := fun v hv =>
    mulVec_mem_eigM_of_commute hN₂.symm hv
  have fPP := fix_of_finrank_le_two h3 h2 hNB hN3 hPP
    (fun v hv => ⟨hNP₁ v hv.1, hNP₂ v hv.2⟩) (nondegOn_inf_eigP h2 hM₂ hB₂ iP nP)
  have fPM := fix_of_finrank_le_two h3 h2 hNB hN3 hPM
    (fun v hv => ⟨hNP₁ v hv.1, hNM₂ v hv.2⟩) (nondegOn_inf_eigM h2 hM₂ hB₂ iP nP)
  have fMP := fix_of_finrank_le_two h3 h2 hNB hN3 hMP
    (fun v hv => ⟨hNM₁ v hv.1, hNP₂ v hv.2⟩) (nondegOn_inf_eigP h2 hM₂ hB₂ iM nM)
  have fMM := fix_of_finrank_le_two h3 h2 hNB hN3 hMM
    (fun v hv => ⟨hNM₁ v hv.1, hNM₂ v hv.2⟩) (nondegOn_inf_eigM h2 hM₂ hB₂ iM nM)
  have fP := fix_of_split h2 hM₂ iP fPP fPM
  have fM := fix_of_split h2 hM₂ iM fMP fMM
  have fT := fix_of_split h2 hM₁ (S := ⊤) (fun _ _ => Submodule.mem_top)
    (fun v hv => fP v (by simpa using hv)) (fun v hv => fM v (by simpa using hv))
  exact eq_one_of_forall_mulVec_eq fun v => fT v Submodule.mem_top

end Res611G2Cent

open Res611G2Cent

section Certs

open CFSG.RankThree.PartOne.SEITZ11 CFSG.RankThree.PartOne.SEITZ11.G2Seven
  CFSG.RankThree.PartTwo.Sec21.Item223RankResProof Matrix in
theorem kS611G2Cent_holds : KS611G2Cent := by
  intro X _ hX x hx1 hx3 V hV hxV
  by_contra hcard
  push Not at hcard
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hX.2
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  set ρ : X →* GL (Fin 7) K := (rep7 K).comp e.toMonoidHom with hρdef
  have hρ : Function.Injective ρ := (rep7_injective K hK2).comp e.injective
  have hform : ∀ g : X, ((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K).transpose *
      G2Seven.gram K * ((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = G2Seven.gram K :=
    fun g => rep7_form K (e g)
  have hcross : ∀ g : X, ∀ u v, ((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *ᵥ cross7 u v =
      cross7 (((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *ᵥ u)
        (((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *ᵥ v) := by
    intro g u v
    have h := rep7_map_mem_crossSubgroup K (RingHom.id K) (e g)
    rw [Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply] at h
    exact h u v
  have hmat1 : ∀ g : X, ((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = 1 → g = 1 := by
    intro g hg
    apply hρ
    rw [map_one]
    exact Units.ext hg
  have hmatmul : ∀ g h : X, ((ρ (g * h) : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
      ((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
        ((ρ h : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := fun g h => by
    rw [map_mul, Units.val_mul]
  have hVfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcard
  obtain ⟨t₁, t₂, ht₁V, ht₂V, ht₁, ht₂, ht₁₂⟩ : ∃ t₁ t₂ : X, t₁ ∈ V ∧ t₂ ∈ V ∧ t₁ ≠ 1 ∧ t₂ ≠ 1 ∧
      t₁ ≠ t₂ := by
    by_cases ha : (a : X) = 1
    · refine ⟨b, c, b.2, c.2, fun hb => hab ?_, fun hc => hac ?_, fun h => hbc (Subtype.ext h)⟩
      · exact Subtype.ext (ha.trans hb.symm)
      · exact Subtype.ext (ha.trans hc.symm)
    · by_cases hb : (b : X) = 1
      · exact ⟨a, c, a.2, c.2, ha, fun hc => hbc (Subtype.ext (hb.trans hc.symm)),
          fun h => hac (Subtype.ext h)⟩
      · exact ⟨a, b, a.2, b.2, ha, hb, fun h => hab (Subtype.ext h)⟩
  have hsq : ∀ t ∈ V, t * t = 1 := fun t ht => by
    rw [← pow_two]
    exact hV.2 t ht
  have hcommV : ∀ s ∈ V, ∀ t ∈ V, s * t = t * s := fun s hs t ht =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
  refine hx1 (hmat1 x ?_)
  refine eq_one_of_commute h3 (M₁ := ((ρ t₁ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K))
    (M₂ := ((ρ t₂ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) ?_ ?_ ?_ (hform t₁) (hform t₂)
    (hcross t₁) (hcross t₂) ?_ ?_ ?_ (hform x) ?_ ?_ ?_
  · rw [← hmatmul, hsq t₁ ht₁V, map_one, Units.val_one]
  · rw [← hmatmul, hsq t₂ ht₂V, map_one, Units.val_one]
  · rw [← hmatmul, ← hmatmul, hcommV t₁ ht₁V t₂ ht₂V]
  · exact fun h => ht₁ (hmat1 t₁ h)
  · exact fun h => ht₂ (hmat1 t₂ h)
  · intro h
    rw [← hmatmul] at h
    apply ht₁₂
    have h' := hmat1 _ h
    calc t₁ = t₁ * (t₂ * t₂) := by rw [hsq t₂ ht₂V, mul_one]
      _ = (t₁ * t₂) * t₂ := by rw [mul_assoc]
      _ = t₂ := by rw [h', one_mul]
  · rw [← hmatmul, ← hmatmul, ← mul_assoc, ← pow_three', hx3, map_one, Units.val_one]
  · rw [← hmatmul, ← hmatmul, hxV t₁ ht₁V]
  · rw [← hmatmul, ← hmatmul, hxV t₂ ht₂V]

end Certs

end CFSG.RankThree.PartTwo.Sec6
