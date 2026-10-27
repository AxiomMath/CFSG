module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6U0
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenTup
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenBlk

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

private def W0m : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

private theorem W0_mat_eq : Sp4Cen.W0.mat = W0m := by
  decide

private def bd (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (D : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => if h : i.val < 4 ∧ j.val < 4 then A ⟨i, h.1⟩ ⟨j, h.2⟩ else D i j

private def Jh : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0]

private def J0' : Matrix (Fin 6) (Fin 6) (ZMod 2) := bd W0m Jh

private theorem J0'_eq : permMᵀ * J0 * permM = J0' := by decide

private theorem bd_conj_row0 (A W : Matrix (Fin 4) (Fin 4) (ZMod 2)) (j : Fin 6) :
    ((bd A 1)ᵀ * bd W Jh * bd A 1) 0 j = bd (Aᵀ * W * A) Jh 0 j := by
  fin_cases j <;>
    simp (config := {decide := true}) [bd, Jh, Matrix.mul_apply, Fin.sum_univ_six,
      Fin.sum_univ_four] <;> ring

private theorem bd_conj_row1 (A W : Matrix (Fin 4) (Fin 4) (ZMod 2)) (j : Fin 6) :
    ((bd A 1)ᵀ * bd W Jh * bd A 1) 1 j = bd (Aᵀ * W * A) Jh 1 j := by
  fin_cases j <;>
    simp (config := {decide := true}) [bd, Jh, Matrix.mul_apply, Fin.sum_univ_six,
      Fin.sum_univ_four] <;> ring

private theorem bd_conj_row2 (A W : Matrix (Fin 4) (Fin 4) (ZMod 2)) (j : Fin 6) :
    ((bd A 1)ᵀ * bd W Jh * bd A 1) 2 j = bd (Aᵀ * W * A) Jh 2 j := by
  fin_cases j <;>
    simp (config := {decide := true}) [bd, Jh, Matrix.mul_apply, Fin.sum_univ_six,
      Fin.sum_univ_four] <;> ring

private theorem bd_conj_row3 (A W : Matrix (Fin 4) (Fin 4) (ZMod 2)) (j : Fin 6) :
    ((bd A 1)ᵀ * bd W Jh * bd A 1) 3 j = bd (Aᵀ * W * A) Jh 3 j := by
  fin_cases j <;>
    simp (config := {decide := true}) [bd, Jh, Matrix.mul_apply, Fin.sum_univ_six,
      Fin.sum_univ_four] <;> ring

private theorem bd_conj_row4 (A W : Matrix (Fin 4) (Fin 4) (ZMod 2)) (j : Fin 6) :
    ((bd A 1)ᵀ * bd W Jh * bd A 1) 4 j = bd (Aᵀ * W * A) Jh 4 j := by
  fin_cases j <;>
    simp (config := {decide := true}) [bd, Jh, Matrix.mul_apply, Fin.sum_univ_six,
      Fin.sum_univ_four] <;> ring

private theorem bd_conj_row5 (A W : Matrix (Fin 4) (Fin 4) (ZMod 2)) (j : Fin 6) :
    ((bd A 1)ᵀ * bd W Jh * bd A 1) 5 j = bd (Aᵀ * W * A) Jh 5 j := by
  fin_cases j <;>
    simp (config := {decide := true}) [bd, Jh, Matrix.mul_apply, Fin.sum_univ_six,
      Fin.sum_univ_four] <;> ring

private theorem bd_conj (A W : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    (bd A 1)ᵀ * bd W Jh * bd A 1 = bd (Aᵀ * W * A) Jh := by
  ext i j
  fin_cases i
  · exact bd_conj_row0 A W j
  · exact bd_conj_row1 A W j
  · exact bd_conj_row2 A W j
  · exact bd_conj_row3 A W j
  · exact bd_conj_row4 A W j
  · exact bd_conj_row5 A W j

private theorem permM_mul_permMt : permM * permMᵀ = 1 := by decide

private theorem permMt_mul_permM : permMᵀ * permM = 1 := by decide

private theorem pinv6_pi6 : ∀ s : Fin 6, pinv6 (pi6 s) = s := by decide

private theorem pi6_eq_two : ∀ s : Fin 6, pi6 s = 2 ↔ s = 4 := by decide

private theorem pi6_eq_five : ∀ s : Fin 6, pi6 s = 5 ↔ s = 5 := by decide

private theorem coe_conj_pg (x : G6) : ((pg * x * pg⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    permM * (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) * permMᵀ := rfl

private theorem conj_sp_iff (x : G6) : pg * x * pg⁻¹ ∈ Sp0 ↔
    (x : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0' * (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) = J0' := by
  show ((pg * x * pg⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 *
      ((pg * x * pg⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = J0 ↔ _
  rw [coe_conj_pg]
  set X : Matrix (Fin 6) (Fin 6) (ZMod 2) := (x : Matrix (Fin 6) (Fin 6) (ZMod 2))
  have hG : (permM * X * permMᵀ)ᵀ * J0 * (permM * X * permMᵀ) =
      permM * (Xᵀ * J0' * X) * permMᵀ := by
    rw [← J0'_eq]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hG]
  generalize Xᵀ * J0' * X = Y
  constructor
  · intro h
    calc Y = (permMᵀ * permM) * Y * (permMᵀ * permM) := by
          rw [permMt_mul_permM, Matrix.one_mul, Matrix.mul_one]
      _ = permMᵀ * (permM * Y * permMᵀ) * permM := by simp only [Matrix.mul_assoc]
      _ = permMᵀ * J0 * permM := by rw [h]
      _ = J0' := J0'_eq
  · intro h
    calc permM * Y * permMᵀ = permM * (permMᵀ * J0 * permM) * permMᵀ := by rw [h, ← J0'_eq]
      _ = (permM * permMᵀ) * J0 * (permM * permMᵀ) := by simp only [Matrix.mul_assoc]
      _ = J0 := by rw [permM_mul_permMt, Matrix.one_mul, Matrix.mul_one]

private theorem mem_sig0_iff_cols (g : G6) : g ∈ Sig0 ↔ g ∈ Sp0 ∧
    (∀ r : Fin 6, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) r 2 = if r = 2 then 1 else 0) ∧
    ∀ r : Fin 6, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) r 5 = if r = 5 then 1 else 0 := by
  show (g ∈ Sp0 ∧ (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (2 : Fin 6) 1 =
      Pi.single (2 : Fin 6) 1 ∧ (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (5 : Fin 6) 1 =
      Pi.single (5 : Fin 6) 1) ↔ _
  simp only [Matrix.mulVec_single_one, funext_iff, Pi.single_apply, Matrix.col_apply]

private theorem mem_sig0_iff (x : G6) : pg * x * pg⁻¹ ∈ Sig0 ↔
    ((x : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0' * (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) = J0' ∧
      (∀ r : Fin 6, (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) r 4 = if r = 4 then 1 else 0) ∧
      ∀ r : Fin 6, (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) r 5 = if r = 5 then 1 else 0) := by
  rw [mem_sig0_iff_cols, conj_sp_iff]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h s
      have := h (pi6 s)
      rw [coe_conj_pg, permM_conj_apply', pinv6_pi6] at this
      have e : pinv6 2 = 4 := by decide
      rw [e] at this
      rw [this]
      simp only [pi6_eq_two]
    · intro h r
      rw [coe_conj_pg, permM_conj_apply']
      have e : pinv6 2 = 4 := by decide
      rw [e, h]
      have : pinv6 r = 4 ↔ r = 2 := by revert r; decide
      simp only [this]
  · constructor
    · intro h s
      have := h (pi6 s)
      rw [coe_conj_pg, permM_conj_apply', pinv6_pi6] at this
      have e : pinv6 5 = 5 := by decide
      rw [e] at this
      rw [this]
      simp only [pi6_eq_five]
    · intro h r
      rw [coe_conj_pg, permM_conj_apply']
      have e : pinv6 5 = 5 := by decide
      rw [e, h]
      have : pinv6 r = 5 ↔ r = 5 := by revert r; decide
      simp only [this]

private theorem mem_Sbar_iff (A : Sp4Cen.GL4) :
    A ∈ Sp4Cen.Sbar ↔ (A : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ * W0m *
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) = W0m := by
  rw [Sp4Cen.stabilizer_eq4.1, ← inv_mem_iff, MulAction.mem_stabilizer_iff, Sp4Cen.Form4.ext_iff,
    Sp4Cen.inv_smul_mat4, W0_mat_eq]

private theorem rows_zero {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hJ : Xᵀ * J0' * X = J0')
    (hc4 : ∀ r : Fin 6, X r 4 = if r = 4 then 1 else 0)
    (hc5 : ∀ r : Fin 6, X r 5 = if r = 5 then 1 else 0) (j : Fin 4) :
    X 4 (Sp4Cen.topIdx j) = 0 ∧ X 5 (Sp4Cen.topIdx j) = 0 := by
  fin_cases j
  · have e5 := congr_fun (congr_fun hJ 0) 5
    have e4 := congr_fun (congr_fun hJ 0) 4
    simp [J0', bd, W0m, Jh, Matrix.mul_apply, Fin.sum_univ_six, hc4, hc5] at e4 e5
    exact ⟨e5, e4⟩
  · have e5 := congr_fun (congr_fun hJ 1) 5
    have e4 := congr_fun (congr_fun hJ 1) 4
    simp [J0', bd, W0m, Jh, Matrix.mul_apply, Fin.sum_univ_six, hc4, hc5] at e4 e5
    exact ⟨e5, e4⟩
  · have e5 := congr_fun (congr_fun hJ 2) 5
    have e4 := congr_fun (congr_fun hJ 2) 4
    simp [J0', bd, W0m, Jh, Matrix.mul_apply, Fin.sum_univ_six, hc4, hc5] at e4 e5
    exact ⟨e5, e4⟩
  · have e5 := congr_fun (congr_fun hJ 3) 5
    have e4 := congr_fun (congr_fun hJ 3) 4
    simp [J0', bd, W0m, Jh, Matrix.mul_apply, Fin.sum_univ_six, hc4, hc5] at e4 e5
    exact ⟨e5, e4⟩

private theorem bd_topIdx (B : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (D : Matrix (Fin 6) (Fin 6) (ZMod 2)) (i j : Fin 4) :
    bd B D (Sp4Cen.topIdx i) (Sp4Cen.topIdx j) = B i j := by
  show (if h : (i : ℕ) < 4 ∧ (j : ℕ) < 4 then B ⟨i, h.1⟩ ⟨j, h.2⟩ else D _ _) = _
  rw [dif_pos ⟨i.isLt, j.isLt⟩]

private theorem lt4_ne_four : ∀ c : Fin 6, c.val < 4 → (4 : Fin 6) ≠ c := by decide

private theorem lt4_ne_five : ∀ c : Fin 6, c.val < 4 → (5 : Fin 6) ≠ c := by decide

private theorem fin6_split : ∀ r c : Fin 6, ¬ (r.val < 4 ∧ c.val < 4) →
    c = 4 ∨ c = 5 ∨ (c.val < 4 ∧ (r = 4 ∨ r = 5)) := by decide

private theorem mem_map_iota_iff (x : G6) :
    x ∈ Sp4Cen.Sbar.map Sp4Cen.iota ↔ pg * x * pg⁻¹ ∈ Sig0 := by
  rw [mem_sig0_iff]
  have hbd : ∀ A : Sp4Cen.GL4,
      Sp4Cen.blkDiag (A : Sp4Cen.M4) = bd (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 := fun _ => rfl
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Sp4Cen.coe_iota, hbd, J0', bd_conj, (mem_Sbar_iff A).mp hA]
    · intro r
      rw [Sp4Cen.coe_iota]
      fin_cases r <;> simp [Sp4Cen.blkDiag]
    · intro r
      rw [Sp4Cen.coe_iota]
      fin_cases r <;> simp [Sp4Cen.blkDiag]
  · rintro ⟨hJ, hc4, hc5⟩
    have hrow := rows_zero hJ hc4 hc5
    have hxC : x ∈ Sp4Cen.C0 := by
      rw [Sp4Cen.mem_C0_iff, Sp4Cen.commute_U0_iff]
      refine ⟨fun i => ⟨?_, ?_, (hrow i).1, (hrow i).2⟩, ?_, ?_⟩
      · rw [hc4]; fin_cases i <;> decide
      · rw [hc5]; fin_cases i <;> decide
      · simp only [hc4, hc5]; decide
      · simp only [hc4, hc5]; decide
    set A : Sp4Cen.GL4 := Sp4Cen.tau ⟨x, hxC⟩ with hA
    have hxA : x = Sp4Cen.iota A := by
      apply Units.ext
      rw [Sp4Cen.coe_iota]
      ext r c
      by_cases h : r.val < 4 ∧ c.val < 4
      · have := Sp4Cen.coe_tau ⟨x, hxC⟩ ⟨r, h.1⟩ ⟨c, h.2⟩
        simp only [Sp4Cen.blkDiag, Matrix.of_apply, dif_pos h]
        exact this.symm
      · simp only [Sp4Cen.blkDiag, Matrix.of_apply, dif_neg h]
        rcases fin6_split r c h with h4 | h5 | ⟨hc, h4 | h5⟩
        · subst h4
          rw [hc4, Matrix.one_apply]
        · subst h5
          rw [hc5, Matrix.one_apply]
        · subst h4
          have := (hrow ⟨c, hc⟩).1
          rw [Matrix.one_apply_ne (lt4_ne_four c hc)]
          exact this
        · subst h5
          have := (hrow ⟨c, hc⟩).2
          rw [Matrix.one_apply_ne (lt4_ne_five c hc)]
          exact this
    refine ⟨A, (mem_Sbar_iff A).mpr ?_, hxA.symm⟩
    have hJ' := hJ
    rw [hxA, Sp4Cen.coe_iota, hbd, J0', bd_conj] at hJ'
    ext i j
    have := congr_fun (congr_fun hJ' (Sp4Cen.topIdx i)) (Sp4Cen.topIdx j)
    rwa [bd_topIdx, bd_topIdx] at this

theorem sig0_eq_map :
    Sig0 = (Sp4Cen.Sbar.map Sp4Cen.iota).map (MulAut.conj pg).toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨pg⁻¹ * g * pg, (mem_map_iota_iff _).mpr ?_, ?_⟩
    · have : pg * (pg⁻¹ * g * pg) * pg⁻¹ = g := by group
      rw [this]; exact hg
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨x, hx, rfl⟩
    exact (mem_map_iota_iff x).mp hx

theorem card_sig0 : Nat.card Sig0 = 720 := by
  rw [sig0_eq_map, Subgroup.card_map_of_injective (MulAut.conj pg).injective,
    Subgroup.card_map_of_injective Sp4Cen.iota_injective, Sp4Cen.card_Sbar]

private theorem map_conj_conj (K : Subgroup G6) (a b : G6) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  have : (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      _root_.mul_inv_rev]
    group
  rw [this]

private theorem mem_range_iota_of_sq {g : G6} (hg : g ∈ Sp4Cen.C0) (h2 : g * g = 1) :
    g ∈ Sp4Cen.iota.range := by
  obtain ⟨A, hA⟩ : ∃ A : Sp4Cen.GL4, Sp4Cen.tau ⟨g, hg⟩ = A := ⟨_, rfl⟩
  have haC : Sp4Cen.iota A ∈ Sp4Cen.C0 := Sp4Cen.iota_mem A
  have htau_a : Sp4Cen.tau ⟨Sp4Cen.iota A, haC⟩ = A := Sp4Cen.tau_iota A
  obtain ⟨z, hz⟩ : ∃ z : G6, z = (Sp4Cen.iota A)⁻¹ * g := ⟨_, rfl⟩
  have hzC : z ∈ Sp4Cen.C0 := by rw [hz]; exact mul_mem (inv_mem haC) hg
  have hz1 : Sp4Cen.tau ⟨z, hzC⟩ = 1 := by
    have : (⟨z, hzC⟩ : ↥Sp4Cen.C0) = ⟨Sp4Cen.iota A, haC⟩⁻¹ * ⟨g, hg⟩ := Subtype.ext hz
    rw [this, map_mul, map_inv, htau_a, hA]
    exact inv_mul_cancel _
  have hzpow : z ∈ Subgroup.zpowers Sp4Cen.u0 := (Sp4Cen.tau_eq_one_iff ⟨z, hzC⟩).mp hz1
  have hcz : Commute (Sp4Cen.iota A) z := by
    obtain ⟨k, hk⟩ := hzpow
    rw [← hk]
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp haC) k
  have hA2 : A * A = 1 := by
    have h1 : Sp4Cen.tau (⟨g, hg⟩ * ⟨g, hg⟩) = 1 := by
      have : (⟨g, hg⟩ * ⟨g, hg⟩ : ↥Sp4Cen.C0) = 1 := Subtype.ext h2
      rw [this, map_one]
    rwa [map_mul, hA] at h1
  have ha2 : Sp4Cen.iota A * Sp4Cen.iota A = 1 := by
    rw [← map_mul, hA2, map_one]
  have hg' : g = Sp4Cen.iota A * z := by rw [hz]; group
  have hz2 : z * z = 1 := by
    calc z * z = (Sp4Cen.iota A * Sp4Cen.iota A) * (z * z) := by rw [ha2, one_mul]
      _ = Sp4Cen.iota A * (Sp4Cen.iota A * z) * z := by group
      _ = Sp4Cen.iota A * (z * Sp4Cen.iota A) * z := by rw [hcz.eq]
      _ = (Sp4Cen.iota A * z) * (Sp4Cen.iota A * z) := by group
      _ = g * g := by rw [← hg']
      _ = 1 := h2
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hzpow
    rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      Sp4Cen.u0_pow_three, _root_.one_zpow]
  have hz1' : z = 1 := by
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; simp
  refine ⟨A, ?_⟩
  rw [hg', hz1', mul_one]

private theorem map_iota_conj (K : Subgroup Sp4Cen.GL4) (c : Sp4Cen.GL4) :
    (K.map (MulAut.conj c).toMonoidHom).map Sp4Cen.iota =
      (K.map Sp4Cen.iota).map (MulAut.conj (Sp4Cen.iota c)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  have : Sp4Cen.iota.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (Sp4Cen.iota c)).toMonoidHom.comp Sp4Cen.iota := by
    ext A
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  rw [this]

theorem exists_conj_sig0 (φ : Equiv.Perm (Fin 6) →* G6)
    (hφ : φ (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1) (hC : φ.range ≤ Subgroup.centralizer {u0}) :
    ∃ g ∈ Subgroup.centralizer {u0}, φ.range.map (MulAut.conj g).toMonoidHom = Sig0 := by
  obtain ⟨φ', hφ'⟩ : ∃ φ' : Equiv.Perm (Fin 6) →* G6,
      φ' = (MulAut.conj pg⁻¹).toMonoidHom.comp φ := ⟨_, rfl⟩
  have hφ'apply : ∀ σ, φ' σ = pg⁻¹ * φ σ * pg := fun σ => by
    rw [hφ']; simp [MulAut.conj_apply]
  have hu0R : pg⁻¹ * u0 * pg = Sp4Cen.u0 := by rw [← pg_conj_u0R]; group
  have hφ'C : ∀ σ, φ' σ ∈ Sp4Cen.C0 := by
    intro σ
    rw [Subgroup.mem_centralizer_singleton_iff, hφ'apply, ← hu0R]
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hC ⟨σ, rfl⟩)
    calc pg⁻¹ * φ σ * pg * (pg⁻¹ * u0 * pg) = pg⁻¹ * (φ σ * u0) * pg := by group
      _ = pg⁻¹ * (u0 * φ σ) * pg := by rw [h]
      _ = pg⁻¹ * u0 * pg * (pg⁻¹ * φ σ * pg) := by group
  have hφ'3 : φ' (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1 := by
    intro h
    apply hφ
    rw [hφ'apply] at h
    calc φ (Equiv.swap 0 1 * Equiv.swap 1 2)
        = pg * (pg⁻¹ * φ (Equiv.swap 0 1 * Equiv.swap 1 2) * pg) * pg⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨φc, hφc⟩ : ∃ φc : Equiv.Perm (Fin 6) →* ↥Sp4Cen.C0,
      φc = φ'.codRestrict Sp4Cen.C0 hφ'C := ⟨_, rfl⟩
  have hφc_val : ∀ σ, ((φc σ : ↥Sp4Cen.C0) : G6) = φ' σ := fun σ => by rw [hφc]; rfl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Equiv.Perm (Fin 6) →* Sp4Cen.GL4, ψ = Sp4Cen.tau.comp φc := ⟨_, rfl⟩
  have adj01_eq : Sp4Cen.adj 0 * Sp4Cen.adj 1 = Equiv.swap 0 1 * Equiv.swap 1 2 := by decide
  have adj01_pow_three : (Sp4Cen.adj 0 * Sp4Cen.adj 1) ^ 3 = 1 := by decide
  have adj01_conj : Sp4Cen.adj 0 * (Sp4Cen.adj 0 * Sp4Cen.adj 1) * (Sp4Cen.adj 0)⁻¹ =
      (Sp4Cen.adj 0 * Sp4Cen.adj 1)⁻¹ := by decide
  have hψ3 : ψ (Sp4Cen.adj 0 * Sp4Cen.adj 1) ≠ 1 := by
    intro h
    have hz : φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) ∈ Subgroup.zpowers Sp4Cen.u0 := by
      have := (Sp4Cen.tau_eq_one_iff (φc (Sp4Cen.adj 0 * Sp4Cen.adj 1))).mp
        (by rw [hψ] at h; exact h)
      rwa [hφc_val] at this
    obtain ⟨k, hk⟩ := hz
    have hgu : φ' (Sp4Cen.adj 0) * Sp4Cen.u0 = Sp4Cen.u0 * φ' (Sp4Cen.adj 0) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hφ'C _)
    have hc : φ' (Sp4Cen.adj 0) * φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) =
        φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) * φ' (Sp4Cen.adj 0) := by
      rw [← hk]
      exact (Commute.zpow_right (show Commute (φ' (Sp4Cen.adj 0)) Sp4Cen.u0 from hgu) k).eq
    have h2 : (φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1))⁻¹ = φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) := by
      calc (φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1))⁻¹ = φ' ((Sp4Cen.adj 0 * Sp4Cen.adj 1)⁻¹) :=
            (map_inv φ' _).symm
        _ = φ' (Sp4Cen.adj 0 * (Sp4Cen.adj 0 * Sp4Cen.adj 1) * (Sp4Cen.adj 0)⁻¹) := by
            rw [adj01_conj]
        _ = φ' (Sp4Cen.adj 0) * φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) * (φ' (Sp4Cen.adj 0))⁻¹ := by
            rw [map_mul φ' (Sp4Cen.adj 0 * (Sp4Cen.adj 0 * Sp4Cen.adj 1)),
              map_mul φ' (Sp4Cen.adj 0), map_inv]
        _ = φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) := by rw [hc, mul_inv_cancel_right]
    have hz2 : φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) * φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) = 1 :=
      mul_eq_one_iff_eq_inv.mpr h2.symm
    have h3 : φ' (Sp4Cen.adj 0 * Sp4Cen.adj 1) ^ 3 = 1 := by
      rw [← map_pow, adj01_pow_three, map_one]
    rw [pow_succ, pow_two, hz2, one_mul] at h3
    exact hφ'3 (by rw [← adj01_eq]; exact h3)
  obtain ⟨c, hc⟩ := Sp4Cen.exists_conj_range hψ3
  have hmem : ∀ σ, φ' σ ∈ Sp4Cen.iota.range := by
    have hclo : Subgroup.comap φ' Sp4Cen.iota.range = ⊤ := by
      rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
      intro s hs
      show φ' s ∈ Sp4Cen.iota.range
      apply mem_range_iota_of_sq (hφ'C s)
      obtain ⟨x, y, -, rfl⟩ := hs
      rw [← map_mul, Equiv.swap_mul_self, map_one]
    intro σ
    have : σ ∈ Subgroup.comap φ' Sp4Cen.iota.range := by rw [hclo]; trivial
    exact this
  have hφ'eq : ∀ σ, φ' σ = Sp4Cen.iota (ψ σ) := by
    intro σ
    obtain ⟨B, hB⟩ := hmem σ
    have hψσ : ψ σ = B := by
      rw [hψ]
      show Sp4Cen.tau (φc σ) = B
      have : φc σ = ⟨Sp4Cen.iota B, Sp4Cen.iota_mem B⟩ :=
        Subtype.ext (by rw [hφc_val]; exact hB.symm)
      rw [this, Sp4Cen.tau_iota]
    rw [hψσ, hB]
  have hrange' : φ'.range = ψ.range.map Sp4Cen.iota := by
    have : φ' = Sp4Cen.iota.comp ψ := MonoidHom.ext hφ'eq
    rw [this, MonoidHom.range_comp]
  have hφrange : φ.range = φ'.range.map (MulAut.conj pg).toMonoidHom := by
    have : φ = (MulAut.conj pg).toMonoidHom.comp φ' := by
      ext σ
      rw [MonoidHom.comp_apply, hφ'apply]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    conv_lhs => rw [this]
    rw [MonoidHom.range_comp]
  refine ⟨pg * (Sp4Cen.iota c)⁻¹ * pg⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (Sp4Cen.iota c)⁻¹ * Sp4Cen.u0 = Sp4Cen.u0 * (Sp4Cen.iota c)⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.mp (inv_mem (Sp4Cen.iota_mem c))
    rw [← pg_conj_u0R]
    calc pg * (Sp4Cen.iota c)⁻¹ * pg⁻¹ * (pg * Sp4Cen.u0 * pg⁻¹)
        = pg * ((Sp4Cen.iota c)⁻¹ * Sp4Cen.u0) * pg⁻¹ := by group
      _ = pg * (Sp4Cen.u0 * (Sp4Cen.iota c)⁻¹) * pg⁻¹ := by rw [hcomm]
      _ = pg * Sp4Cen.u0 * pg⁻¹ * (pg * (Sp4Cen.iota c)⁻¹ * pg⁻¹) := by group
  · have hgpc : pg * (Sp4Cen.iota c)⁻¹ * pg⁻¹ * pg * Sp4Cen.iota c = pg := by group
    rw [hφrange, hrange', hc, map_iota_conj, map_conj_conj, map_conj_conj, hgpc]
    exact sig0_eq_map.symm

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
