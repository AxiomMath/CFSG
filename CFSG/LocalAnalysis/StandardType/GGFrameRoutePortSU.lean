module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot

section Helpers

variable {K : Type} [Field K] {k n : ℕ}

private lemma frameRoutePortSU_card_units (h : UnitaryFieldData 2 1 K) :
    Nat.card Kˣ = 3 := by
  have hK : Nat.card K = 4 := by
    rw [h.card]
    norm_num
  rw [Nat.card_units, hK]

private lemma frameRoutePortSU_unit_pow_three (h : UnitaryFieldData 2 1 K) (u : Kˣ) :
    u ^ 3 = 1 := by
  have hu := pow_card_eq_one' (G := Kˣ) (x := u)
  rwa [frameRoutePortSU_card_units h] at hu

private lemma frameRoutePortSU_norm_unit (h : UnitaryFieldData 2 1 K) (u : Kˣ) :
    h.norm (u : K) = 1 := by
  rw [h.norm_eq_pow, show 2 ^ 1 + 1 = 3 by norm_num]
  rw [← Units.val_pow_eq_pow_val, frameRoutePortSU_unit_pow_three h u, Units.val_one]

private def frameRoutePortSU_shift (hkn : k + 2 ≤ n) (i : Fin k) : Fin n :=
  ⟨i.val + 1, by omega⟩

private lemma frameRoutePortSU_shift_injective (hkn : k + 2 ≤ n) :
    Function.Injective (frameRoutePortSU_shift hkn) := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only [frameRoutePortSU_shift, Fin.mk.injEq] at h
  rw [Fin.mk.injEq]
  omega

private noncomputable def frameRoutePortSU_A (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    (Fin k → Kˣ) →* (Fin n → Kˣ) where
  toFun u := Pi.mulSingle (⟨0, by omega⟩ : Fin n) (u ⟨0, by omega⟩)
  map_one' := by simp
  map_mul' u v := by simp [Pi.mulSingle_mul]

private noncomputable def frameRoutePortSU_B (hkn : k + 2 ≤ n) :
    (Fin k → Kˣ) →* (Fin n → Kˣ) where
  toFun u := ∏ i : Fin k, Pi.mulSingle (frameRoutePortSU_shift hkn i) (u i)
  map_one' := by simp
  map_mul' u v := by
    simp only [Pi.mul_apply, Pi.mulSingle_mul, Finset.prod_mul_distrib]

private noncomputable def frameRoutePortSU_P (hk : 1 ≤ k) :
    (Fin k → Kˣ) →* Kˣ where
  toFun u := u ⟨0, by omega⟩ * ∏ i, u i
  map_one' := by simp
  map_mul' u v := by
    simp only [Pi.mul_apply, Finset.prod_mul_distrib]
    ac_rfl

private noncomputable def frameRoutePortSU_C (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    (Fin k → Kˣ) →* (Fin n → Kˣ) where
  toFun u := Pi.mulSingle (⟨k + 1, by omega⟩ : Fin n) ((frameRoutePortSU_P hk u)⁻¹)
  map_one' := by simp
  map_mul' u v := by
    rw [map_mul, mul_inv_rev, mul_comm, Pi.mulSingle_mul]

private noncomputable def frameRoutePortSU_e (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    (Fin k → Kˣ) →* (Fin n → Kˣ) :=
  frameRoutePortSU_A hk hkn * frameRoutePortSU_B hkn * frameRoutePortSU_C hk hkn

private noncomputable def frameRoutePortSU_prodHom (n : ℕ) :
    (Fin n → Kˣ) →* Kˣ where
  toFun u := ∏ j, u j
  map_one' := by simp
  map_mul' u v := by simp only [Pi.mul_apply, Finset.prod_mul_distrib]

private lemma frameRoutePortSU_A_apply (hk : 1 ≤ k) (hkn : k + 2 ≤ n)
    (u : Fin k → Kˣ) :
    frameRoutePortSU_A hk hkn u =
      Pi.mulSingle (⟨0, by omega⟩ : Fin n) (u ⟨0, by omega⟩) := rfl

private lemma frameRoutePortSU_B_apply (hkn : k + 2 ≤ n) (u : Fin k → Kˣ) :
    frameRoutePortSU_B hkn u =
      ∏ i : Fin k, Pi.mulSingle (frameRoutePortSU_shift hkn i) (u i) := rfl

private lemma frameRoutePortSU_C_apply (hk : 1 ≤ k) (hkn : k + 2 ≤ n)
    (u : Fin k → Kˣ) :
    frameRoutePortSU_C hk hkn u =
      Pi.mulSingle (⟨k + 1, by omega⟩ : Fin n) ((frameRoutePortSU_P hk u)⁻¹) := rfl

private lemma frameRoutePortSU_P_apply (hk : 1 ≤ k) (u : Fin k → Kˣ) :
    frameRoutePortSU_P hk u = u ⟨0, by omega⟩ * ∏ i, u i := rfl

private lemma frameRoutePortSU_e_apply (hk : 1 ≤ k) (hkn : k + 2 ≤ n)
    (u : Fin k → Kˣ) :
    frameRoutePortSU_e hk hkn u =
      frameRoutePortSU_A hk hkn u * frameRoutePortSU_B hkn u *
        frameRoutePortSU_C hk hkn u := rfl

private lemma frameRoutePortSU_prodHom_mulSingle (n : ℕ) (i : Fin n) (x : Kˣ) :
    frameRoutePortSU_prodHom n (Pi.mulSingle i x) = x := by
  rw [frameRoutePortSU_prodHom]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.mulSingle_eq_of_ne hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma frameRoutePortSU_e_shift (hk : 1 ≤ k) (hkn : k + 2 ≤ n)
    (u : Fin k → Kˣ) (i : Fin k) :
    frameRoutePortSU_e hk hkn u (frameRoutePortSU_shift hkn i) = u i := by
  have hshiftinj := frameRoutePortSU_shift_injective hkn
  have h0 : frameRoutePortSU_shift hkn i ≠ (⟨0, by omega⟩ : Fin n) := by
    intro h
    have := congrArg Fin.val h
    simp only [frameRoutePortSU_shift, Fin.val_mk] at this
    omega
  have hlast : frameRoutePortSU_shift hkn i ≠ (⟨k + 1, by omega⟩ : Fin n) := by
    intro h
    have := congrArg Fin.val h
    simp only [frameRoutePortSU_shift, Fin.val_mk] at this
    omega
  rw [frameRoutePortSU_e_apply, frameRoutePortSU_A_apply, frameRoutePortSU_B_apply,
    frameRoutePortSU_C_apply]
  simp only [Pi.mul_apply, Finset.prod_apply, Pi.mulSingle_eq_of_ne h0,
    Pi.mulSingle_eq_of_ne hlast, one_mul, mul_one]
  rw [Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    rw [Pi.mulSingle_eq_of_ne]
    intro hls
    exact hl (hshiftinj hls.symm)
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma frameRoutePortSU_e_zero (hk : 1 ≤ k) (hkn : k + 2 ≤ n)
    (u : Fin k → Kˣ) :
    frameRoutePortSU_e hk hkn u (⟨0, by omega⟩ : Fin n) = u ⟨0, by omega⟩ := by
  have hlast : (⟨0, by omega⟩ : Fin n) ≠ (⟨k + 1, by omega⟩ : Fin n) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_mk] at hval
    omega
  rw [frameRoutePortSU_e_apply, frameRoutePortSU_A_apply, frameRoutePortSU_B_apply,
    frameRoutePortSU_C_apply]
  simp only [Pi.mul_apply, Finset.prod_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hlast,
    mul_one]
  rw [Finset.prod_eq_one]
  · simp
  · intro l _
    rw [Pi.mulSingle_eq_of_ne]
    intro h
    have hval : (frameRoutePortSU_shift hkn l).val = 0 := by
      rw [← h]
    dsimp only [frameRoutePortSU_shift] at hval
    omega

private lemma frameRoutePortSU_e_one (hk : 1 ≤ k) (hkn : k + 2 ≤ n)
    (u : Fin k → Kˣ) :
    frameRoutePortSU_e hk hkn u (⟨1, by omega⟩ : Fin n) = u ⟨0, by omega⟩ := by
  have h0 : (⟨1, by omega⟩ : Fin n) ≠ (⟨0, by omega⟩ : Fin n) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_mk] at hval
    omega
  have hlast : (⟨1, by omega⟩ : Fin n) ≠ (⟨k + 1, by omega⟩ : Fin n) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_mk] at hval
    omega
  have hsel : frameRoutePortSU_shift hkn (⟨0, by omega⟩ : Fin k) =
      (⟨1, by omega⟩ : Fin n) := by
    apply Fin.ext
    simp only [frameRoutePortSU_shift, Fin.val_mk]
  rw [frameRoutePortSU_e_apply, frameRoutePortSU_A_apply, frameRoutePortSU_B_apply,
    frameRoutePortSU_C_apply]
  simp only [Pi.mul_apply, Finset.prod_apply, Pi.mulSingle_eq_of_ne h0,
    Pi.mulSingle_eq_of_ne hlast, one_mul, mul_one]
  rw [Finset.prod_eq_single (⟨0, by omega⟩ : Fin k)]
  · simp [hsel]
  · intro l _ hl
    rw [Pi.mulSingle_eq_of_ne]
    intro h
    apply hl
    apply frameRoutePortSU_shift_injective hkn
    exact h.symm.trans hsel.symm
  · intro hi
    exact absurd (Finset.mem_univ _) hi

private lemma frameRoutePortSU_e_tail (hk : 1 ≤ k) (hkn : k + 2 ≤ n)
    (u : Fin k → Kˣ) {j : Fin n} (hj : k + 2 ≤ j.val) :
    frameRoutePortSU_e hk hkn u j = 1 := by
  have h0 : j ≠ (⟨0, by omega⟩ : Fin n) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_mk] at hval
    omega
  have hlast : j ≠ (⟨k + 1, by omega⟩ : Fin n) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_mk] at hval
    omega
  rw [frameRoutePortSU_e_apply, frameRoutePortSU_A_apply, frameRoutePortSU_B_apply,
    frameRoutePortSU_C_apply]
  simp only [Pi.mul_apply, Finset.prod_apply, Pi.mulSingle_eq_of_ne h0,
    Pi.mulSingle_eq_of_ne hlast, one_mul, mul_one]
  rw [Finset.prod_eq_one]
  · intro l _
    rw [Pi.mulSingle_eq_of_ne]
    intro h
    have hval : j.val = (frameRoutePortSU_shift hkn l).val := congrArg Fin.val h
    dsimp only [frameRoutePortSU_shift] at hval
    omega

private lemma frameRoutePortSU_e_injective (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    Function.Injective (frameRoutePortSU_e (K := K) hk hkn) := by
  intro u v h
  funext i
  have := congrFun h (frameRoutePortSU_shift hkn i)
  rwa [frameRoutePortSU_e_shift hk hkn u i, frameRoutePortSU_e_shift hk hkn v i] at this

private noncomputable abbrev frameRoutePortSU_diag (hk : 1 ≤ k) (hkn : k + 2 ≤ n)
    (u : Fin k → Kˣ) : Fin n → K :=
  fun j => (frameRoutePortSU_e hk hkn u j : K)

private lemma frameRoutePortSU_det (h : UnitaryFieldData 2 1 K) (hk : 1 ≤ k)
    (hkn : k + 2 ≤ n) (u : Fin k → Kˣ) :
    ∏ j : Fin n, frameRoutePortSU_diag hk hkn u j = 1 := by
  have hA : frameRoutePortSU_prodHom n (frameRoutePortSU_A hk hkn u) =
      u ⟨0, by omega⟩ := by
    rw [frameRoutePortSU_A_apply]
    exact frameRoutePortSU_prodHom_mulSingle n _ _
  have hB : frameRoutePortSU_prodHom n (frameRoutePortSU_B hkn u) = ∏ i, u i := by
    rw [frameRoutePortSU_B_apply]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact frameRoutePortSU_prodHom_mulSingle n _ _
  have hC : frameRoutePortSU_prodHom n (frameRoutePortSU_C hk hkn u) =
      (frameRoutePortSU_P hk u)⁻¹ := by
    rw [frameRoutePortSU_C_apply]
    exact frameRoutePortSU_prodHom_mulSingle n _ _
  have hprod : frameRoutePortSU_prodHom n (frameRoutePortSU_e hk hkn u) = 1 := by
    rw [frameRoutePortSU_e_apply, map_mul, map_mul, hA, hB, hC, frameRoutePortSU_P_apply]
    exact mul_inv_cancel _
  have hcoe : ((frameRoutePortSU_prodHom n (frameRoutePortSU_e hk hkn u) : Kˣ) : K) =
      ∏ j : Fin n, frameRoutePortSU_diag hk hkn u j := by
    rw [frameRoutePortSU_prodHom]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, frameRoutePortSU_diag]
    rw [Units.coe_prod]
  rw [← hcoe, hprod, Units.val_one]

private noncomputable def frameRoutePortSU_hom (h : UnitaryFieldData 2 1 K)
    (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    (Fin k → Kˣ) →* unitarySU 2 1 K n where
  toFun u := diagSU h (frameRoutePortSU_diag hk hkn u)
    (fun j => frameRoutePortSU_norm_unit h (frameRoutePortSU_e hk hkn u j))
    (frameRoutePortSU_det h hk hkn u)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change (((diagSU h (frameRoutePortSU_diag hk hkn 1) _ _ : unitarySU 2 1 K n) :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((1 : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [coe_diagSU, Subgroup.coe_one, Units.val_one]
    have hd : frameRoutePortSU_diag hk hkn (1 : Fin k → Kˣ) = 1 := by
      funext j
      simp [frameRoutePortSU_diag]
    rw [hd, Matrix.diagonal_one']
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    change (((diagSU h (frameRoutePortSU_diag hk hkn (u * v)) _ _ : unitarySU 2 1 K n) :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((((diagSU h (frameRoutePortSU_diag hk hkn u) _ _ : unitarySU 2 1 K n) *
        (diagSU h (frameRoutePortSU_diag hk hkn v) _ _ : unitarySU 2 1 K n) :
          unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [Subgroup.coe_mul, Units.val_mul, coe_diagSU, coe_diagSU, coe_diagSU,
      Matrix.diagonal_mul_diagonal]
    have hfun : frameRoutePortSU_diag hk hkn (u * v) =
        fun j => frameRoutePortSU_diag hk hkn u j * frameRoutePortSU_diag hk hkn v j := by
      funext j
      dsimp only [frameRoutePortSU_diag]
      rw [map_mul]
      rfl
    rw [hfun]

private lemma frameRoutePortSU_hom_injective (h : UnitaryFieldData 2 1 K) (hk : 1 ≤ k)
    (hkn : k + 2 ≤ n) : Function.Injective (frameRoutePortSU_hom h hk hkn) := by
  intro u v huv
  apply frameRoutePortSU_e_injective hk hkn
  have hmat := congrArg (fun w : unitarySU 2 1 K n =>
    (((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) huv
  have hmat' : Matrix.diagonal (frameRoutePortSU_diag hk hkn u) =
      Matrix.diagonal (frameRoutePortSU_diag hk hkn v) := by
    simpa only [frameRoutePortSU_hom, MonoidHom.coe_mk, OneHom.coe_mk, coe_diagSU] using hmat
  have hd := Matrix.diagonal_injective hmat'
  funext j
  exact Units.ext (congrFun hd j)

private lemma frameRoutePortSU_permMatrix_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ.permMatrix K i j = if σ i = j then (1 : K) else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply]
  simp [Pi.single_apply, eq_comm]

private lemma frameRoutePortSU_diagonal_permMatrix_commute {σ : Equiv.Perm (Fin n)}
    {d : Fin n → K} (hσ : ∀ i, d (σ i) = d i) :
    Matrix.diagonal d * σ.permMatrix K = σ.permMatrix K * Matrix.diagonal d := by
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_apply]
  by_cases h : σ i = j
  · have hs : i = σ.symm j := by rw [← h, Equiv.symm_apply_apply]
    rw [if_pos hs, if_pos h, hσ i]
  · have hs : ¬ i = σ.symm j := by
      intro hi
      apply h
      rw [hi, Equiv.apply_symm_apply]
    rw [if_neg hs, if_neg h]

private lemma frameRoutePortSU_comp_swap_eq {d : Fin n → K} {a b : Fin n} (h : d a = d b) :
    ∀ i, d (Equiv.swap a b i) = d i := by
  intro i
  by_cases hia : i = a
  · subst hia
    simp [h]
  · by_cases hib : i = b
    · subst hib
      simp [h]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

private lemma frameRoutePortSU_permSU_swap_sq (h : UnitaryFieldData 2 1 K) {n : ℕ}
    (a b : Fin n) : (permSU h (Equiv.swap a b) : unitarySU 2 1 K n) ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, coe_permSU, Units.val_one,
    sq]
  rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]

private lemma frameRoutePortSU_permSU_swap_not_center (h : UnitaryFieldData 2 1 K) {n : ℕ}
    (a b : Fin n) (hab : a ≠ b) :
    (permSU h (Equiv.swap a b) : unitarySU 2 1 K n) ∉
      Subgroup.center (unitarySU 2 1 K n) := by
  intro ht
  have hscalar := center_unitarySU_le_unitaryScalars h n ht
  rw [mem_unitaryScalars] at hscalar
  obtain ⟨c, -, -, hcmat⟩ := hscalar
  have h00 := congrArg (fun w : GL (Fin n) K =>
    ((w : Matrix (Fin n) (Fin n) K) a a)) hcmat
  rw [coe_permSU, frameRoutePortSU_permMatrix_apply,
    if_neg (by rw [Equiv.swap_apply_left]; exact hab.symm),
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h00
  exact Units.ne_zero c h00.symm

private lemma frameRoutePortSU_range_elemAbelian (h : UnitaryFieldData 2 1 K)
    (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    IsElemAbelian 3 (frameRoutePortSU_hom h hk hkn).range ∧
      Nat.card (frameRoutePortSU_hom h hk hkn).range = 3 ^ k := by
  have hιinj : Function.Injective (frameRoutePortSU_hom h hk hkn) :=
    frameRoutePortSU_hom_injective h hk hkn
  refine ⟨?_, ?_⟩
  · haveI : IsMulCommutative (Fin k → Kˣ) :=
      IsMulCommutative.of_comm fun u v => funext fun i => mul_comm (u i) (v i)
    refine ⟨?_, ?_⟩
    · infer_instance
    · intro x hx
      obtain ⟨u, rfl⟩ := hx
      rw [← map_pow]
      have hu : u ^ 3 = 1 := by
        funext i
        simpa using frameRoutePortSU_unit_pow_three h (u i)
      rw [hu, map_one]
  · change Nat.card (Set.range (frameRoutePortSU_hom h hk hkn)) = 3 ^ k
    rw [(Nat.card_congr (Equiv.ofInjective _ hιinj)).symm, Nat.card_fun, Nat.card_fin,
      frameRoutePortSU_card_units h]

private lemma frameRoutePortSU_scalar_one (h : UnitaryFieldData 2 1 K)
    (hk : 1 ≤ k) (hkn : k + 2 ≤ n) (hZ : k + 2 < n ∨ ¬ 3 ∣ n)
    {u : Fin k → Kˣ} {c : Kˣ} (hcn : c ^ n = 1)
    (hc_eq : ∀ j : Fin n, (frameRoutePortSU_e hk hkn u j : K) = (c : K)) :
    (c : K) = 1 := by
  rcases hZ with hlt | hndvd
  · have hn : 0 < n := by omega
    let j : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩
    have hj : k + 2 ≤ j.val := by
      change k + 2 ≤ n - 1
      omega
    have htail : frameRoutePortSU_e hk hkn u j = 1 := frameRoutePortSU_e_tail hk hkn u hj
    have hje := hc_eq j
    rw [htail, Units.val_one] at hje
    exact hje.symm
  · have h3 : c ^ 3 = 1 := frameRoutePortSU_unit_pow_three h c
    have h3dvd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hndvd' : orderOf c ∣ n := orderOf_dvd_of_pow_eq_one hcn
    have hcop : Nat.Coprime 3 n := (Nat.prime_three.coprime_iff_not_dvd).2 hndvd
    have hdvd1 : orderOf c ∣ 1 := by
      simpa [Nat.coprime_iff_gcd_eq_one.mp hcop] using Nat.dvd_gcd h3dvd hndvd'
    have horder : orderOf c = 1 := Nat.dvd_one.mp hdvd1
    rw [orderOf_eq_one_iff.mp horder, Units.val_one]

private lemma frameRoutePortSU_range_inter_center (h : UnitaryFieldData 2 1 K)
    (hk : 1 ≤ k) (hkn : k + 2 ≤ n) (hZ : k + 2 < n ∨ ¬ 3 ∣ n) :
    (frameRoutePortSU_hom h hk hkn).range ⊓
      Subgroup.center (unitarySU 2 1 K n) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨u, rfl⟩ := hx.1
  have hscalar : frameRoutePortSU_hom h hk hkn u ∈ unitaryScalars h n :=
    center_unitarySU_le_unitaryScalars h n hx.2
  obtain ⟨c, -, hcn, hcmat⟩ := mem_unitaryScalars.1 hscalar
  have hdiag : (((frameRoutePortSU_hom h hk hkn u : unitarySU 2 1 K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.diagonal (frameRoutePortSU_diag hk hkn u) := by
    simp only [frameRoutePortSU_hom, MonoidHom.coe_mk, OneHom.coe_mk, coe_diagSU]
  have hcmatM : (((frameRoutePortSU_hom h hk hkn u : unitarySU 2 1 K n) :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K) := congrArg _ hcmat
  have hcmat' : Matrix.diagonal (frameRoutePortSU_diag hk hkn u) =
      (((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K) := hdiag.symm.trans hcmatM
  have hc_eq : ∀ j : Fin n, (frameRoutePortSU_e hk hkn u j : K) = (c : K) := by
    intro j
    have hjj := congrFun (congrFun hcmat' j) j
    simpa only [frameRoutePortSU_diag, Matrix.diagonal_apply_eq,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      using hjj
  have hc_one : (c : K) = 1 := frameRoutePortSU_scalar_one h hk hkn hZ hcn hc_eq
  have heu : frameRoutePortSU_e hk hkn u = 1 := by
    funext j
    apply Units.ext
    rw [Pi.one_apply, hc_eq j, hc_one]
    rfl
  have hu : u = 1 := frameRoutePortSU_e_injective hk hkn (by rw [heu, map_one])
  rw [hu, map_one]

private lemma frameRoutePortSU_range_le_centralizer (h : UnitaryFieldData 2 1 K)
    (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    (frameRoutePortSU_hom h hk hkn).range ≤ Subgroup.centralizer
      ({permSU h (Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n))} :
        Set (unitarySU 2 1 K n)) := by
  intro x hx
  obtain ⟨u, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, frameRoutePortSU_hom, MonoidHom.coe_mk,
    OneHom.coe_mk, coe_diagSU, coe_permSU]
  have hd01 : frameRoutePortSU_diag hk hkn u (⟨0, by omega⟩ : Fin n) =
      frameRoutePortSU_diag hk hkn u (⟨1, by omega⟩ : Fin n) := by
    simp only [frameRoutePortSU_diag, frameRoutePortSU_e_zero hk hkn u,
      frameRoutePortSU_e_one hk hkn u]
  have hσfix := frameRoutePortSU_comp_swap_eq
    (a := (⟨0, by omega⟩ : Fin n)) (b := (⟨1, by omega⟩ : Fin n)) hd01
  exact (frameRoutePortSU_diagonal_permMatrix_commute
    (σ := Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n))
    (d := frameRoutePortSU_diag hk hkn u) hσfix).symm

end Helpers

theorem rank3Witness_unitarySU_two {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 2 ≤ n) (hZ : k + 2 < n ∨ ¬ 3 ∣ n) :
    Rank3Witness (unitarySU 2 1 K n) k := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let σ : Equiv.Perm (Fin n) := Equiv.swap a b
  let t : unitarySU 2 1 K n := permSU h σ
  have hElem_card := frameRoutePortSU_range_elemAbelian h hk hkn
  have hInter := frameRoutePortSU_range_inter_center h hk hkn hZ
  have ht_pow : t ^ 2 ^ 1 = 1 := by
    have hsq : t ^ 2 = 1 := by
      simpa only [t, σ] using frameRoutePortSU_permSU_swap_sq h a b
    simpa using hsq
  have ht_notcenter : t ∉ Subgroup.center (unitarySU 2 1 K n) := by
    have hab : a ≠ b := by
      intro hab
      have hval := congrArg Fin.val hab
      simp only [a, b, Fin.val_mk] at hval
      omega
    simpa only [t, σ] using frameRoutePortSU_permSU_swap_not_center h a b hab
  have hcentral : (frameRoutePortSU_hom h hk hkn).range ≤
      Subgroup.centralizer ({t} : Set (unitarySU 2 1 K n)) := by
    simpa only [t, σ, a, b] using frameRoutePortSU_range_le_centralizer h hk hkn
  exact ⟨(frameRoutePortSU_hom h hk hkn).range, t, hElem_card.1, hElem_card.2, hInter,
    ⟨1, ht_pow⟩, ht_notcenter, hcentral⟩

theorem F07a_SU5 {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) :
    Rank3Witness (unitarySU 2 1 K 5) 3 :=
  rank3Witness_unitarySU_two h (k := 3) (n := 5) (by norm_num) (by norm_num)
    (Or.inr (by decide))

theorem F07b_SU6 {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) :
    Rank3Witness (unitarySU 2 1 K 6) 3 :=
  rank3Witness_unitarySU_two h (k := 3) (n := 6) (by norm_num) (by norm_num)
    (Or.inl (by norm_num))

theorem F07c_SU7 {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) :
    Rank3Witness (unitarySU 2 1 K 7) 5 :=
  rank3Witness_unitarySU_two h (k := 5) (n := 7) (by norm_num) (by norm_num)
    (Or.inr (by decide))

end CFSG.StandardType.FrameRoute

end