module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamUSylow
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.ClassicalEven
open Matrix

variable {K : Type} [Field K]

private def u5Coe : (Fin 5 → rootsOfUnity 5 K) →* (Fin 5 → Kˣ) where
  toFun d i := (d i : Kˣ)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def u5TorusHom (h : UnitaryFieldData 2 2 K) :
    (Fin 5 → rootsOfUnity 5 K) →* uU h 5 :=
  (torusDiag.comp u5Coe).codRestrict (uU h 5) (fun d => by
    rw [mem_uU]
    have hbar : ∀ c : K, h.bar c = c ^ 4 := by
      intro c
      rw [h.bar_apply]
      norm_num
    have hd : ∀ i, (d i : Kˣ) ^ 5 = 1 := fun i =>
      (mem_rootsOfUnity 5 (d i : Kˣ)).mp (d i).2
    show ((((torusDiag (u5Coe d) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map
      h.bar)ᵀ * ((torusDiag (u5Coe d) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) = 1
    rw [coe_torusDiag]
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hd5 : ((d i : Kˣ) : K) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hd i, Units.val_one]
    rw [hbar]
    change ((d i : Kˣ) : K) ^ 4 * ((d i : Kˣ) : K) = 1
    rw [← pow_succ]
    exact hd5)

theorem u5TorusHom_injective (h : UnitaryFieldData 2 2 K) :
    Function.Injective (u5TorusHom h) := by
  intro d e hde
  have h2 := congrArg (fun x : uU h 5 => (((x : GL (Fin 5) K)) :
    Matrix (Fin 5) (Fin 5) K)) hde
  funext i
  apply Subtype.ext
  apply Units.ext
  have h3 := congrFun (congrFun h2 i) i
  simpa [u5TorusHom, u5Coe, coe_torusDiag] using h3

noncomputable def u5Torus (h : UnitaryFieldData 2 2 K) : Subgroup (uU h 5) :=
  (u5TorusHom h).range

noncomputable def u5Cycle : GL (Fin 5) K :=
  (Matrix.permMatrixHom (n := Fin 5) (R := K)).toHomUnits ((finRotate 5)⁻¹)

private theorem coe_u5Cycle :
    ((u5Cycle (K := K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (finRotate 5).permMatrix K := by
  show (((Matrix.permMatrixHom (n := Fin 5) (R := K)).toHomUnits ((finRotate 5)⁻¹) :
    (Matrix (Fin 5) (Fin 5) K)ˣ) : Matrix (Fin 5) (Fin 5) K) = _
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, inv_inv]

private theorem u5PermMatrix_apply (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    (σ.permMatrix K) i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp

private theorem u5Cycle_mem (h : UnitaryFieldData 2 2 K) : u5Cycle (K := K) ∈ uU h 5 := by
  rw [mem_uU]
  have hbar : ∀ c : K, h.bar c = c ^ 4 := by
    intro c
    rw [h.bar_apply]
    norm_num
  have hmap : ((finRotate 5).permMatrix K).map h.bar = (finRotate 5).permMatrix K := by
    ext i j
    rw [Matrix.map_apply, u5PermMatrix_apply]
    split_ifs <;> simp
  rw [coe_u5Cycle, hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, show (1 : Equiv.Perm (Fin 5)) = Equiv.refl (Fin 5) from rfl,
    Matrix.permMatrix_refl]

private theorem u5Cycle_pow_five : u5Cycle (K := K) ^ 5 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, u5Cycle, MonoidHom.coe_toHomUnits,
    ← map_pow]
  have hσ : finRotate 5 ^ 5 = 1 := by decide
  rw [inv_pow, hσ, inv_one, map_one]

private theorem u5PermMatrix_mul_diagonal (σ : Equiv.Perm (Fin 5)) (d : Fin 5 → K) :
    σ.permMatrix K * Matrix.diagonal d = Matrix.diagonal (d ∘ σ) * σ.permMatrix K := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, u5PermMatrix_apply]
  split_ifs with h
  · rw [Function.comp_apply, h, one_mul, mul_one]
  · rw [mul_zero, zero_mul]

private theorem u5PermMatrix_mul_transpose (σ : Equiv.Perm (Fin 5)) :
    σ.permMatrix K * (σ.permMatrix K)ᵀ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
    show (1 : Equiv.Perm (Fin 5)) = Equiv.refl (Fin 5) from rfl, Matrix.permMatrix_refl]

private theorem u5PermMatrix_transpose_mul (σ : Equiv.Perm (Fin 5)) :
    (σ.permMatrix K)ᵀ * σ.permMatrix K = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    show (1 : Equiv.Perm (Fin 5)) = Equiv.refl (Fin 5) from rfl, Matrix.permMatrix_refl]

private theorem u5Cycle_inv_coe :
    (((u5Cycle (K := K))⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((finRotate 5).permMatrix K)ᵀ := by
  let v : GL (Fin 5) K := ⟨((finRotate 5).permMatrix K)ᵀ, (finRotate 5).permMatrix K,
    u5PermMatrix_transpose_mul (finRotate 5), u5PermMatrix_mul_transpose (finRotate 5)⟩
  have h : u5Cycle (K := K) * v = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one, coe_u5Cycle]
    change (finRotate 5).permMatrix K * ((finRotate 5).permMatrix K)ᵀ = 1
    exact u5PermMatrix_mul_transpose (finRotate 5)
  have h2 : (u5Cycle (K := K))⁻¹ = v := inv_eq_of_mul_eq_one_right h
  rw [h2]

private theorem u5Conj_formula (d : Fin 5 → K) :
    (finRotate 5).permMatrix K * Matrix.diagonal d *
      ((finRotate 5).permMatrix K)ᵀ = Matrix.diagonal (d ∘ finRotate 5) := by
  rw [u5PermMatrix_mul_diagonal, Matrix.mul_assoc,
    u5PermMatrix_mul_transpose, Matrix.mul_one]

private noncomputable def u5CycleU (h : UnitaryFieldData 2 2 K) : uU h 5 :=
  ⟨u5Cycle, u5Cycle_mem h⟩

private theorem coe_u5Cycle_pow (k : ℕ) :
    ((u5Cycle (K := K) ^ k : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((finRotate 5) ^ k).permMatrix K := by
  have h : u5Cycle (K := K) ^ k = (Matrix.permMatrixHom (n := Fin 5) (R := K)).toHomUnits
      (((finRotate 5)⁻¹) ^ k) := by
    rw [u5Cycle, map_pow]
  rw [h, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, inv_pow, inv_inv]

private theorem orderOf_finRotate_five : orderOf (finRotate 5) = 5 := by
  have hdvd : orderOf (finRotate 5) ∣ 5 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by decide)
  have hne : orderOf (finRotate 5) ≠ 1 := by
    intro h
    have h1 : finRotate 5 = 1 := orderOf_eq_one_iff.mp h
    have h2 : (finRotate 5) 0 = (1 : Equiv.Perm (Fin 5)) 0 := by rw [h1]
    simp at h2
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
  · exact absurd h hne
  · exact h

private theorem u5CycleU_pow_not_torus (h : UnitaryFieldData 2 2 K) {k : ℕ} (hk0 : 0 < k)
    (hk5 : k < 5) : u5CycleU h ^ k ∉ u5Torus h := by
  rintro ⟨d, hd⟩
  have hσk : (finRotate 5) ^ k ≠ 1 := by
    intro h1
    have hdvd : orderOf (finRotate 5) ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [orderOf_finRotate_five] at hdvd
    omega
  have hex : ∃ i : Fin 5, (finRotate 5 ^ k) i ≠ i := by
    by_contra hall
    rw [not_exists] at hall
    simp only [not_not] at hall
    exact hσk (Equiv.ext hall)
  obtain ⟨i, hi⟩ := hex
  have hm : (((u5TorusHom h d : uU h 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (((u5CycleU h ^ k : uU h 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    rw [hd]
  have hentry := congrFun (congrFun hm i) ((finRotate 5 ^ k) i)
  have hrhs : (((u5CycleU h ^ k : uU h 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((finRotate 5 ^ k).permMatrix K) := by
    rw [Subgroup.coe_pow]
    change ((u5Cycle (K := K) ^ k : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = _
    rw [coe_u5Cycle_pow]
  rw [show ((u5TorusHom h d : uU h 5) : GL (Fin 5) K) =
      torusDiag (u5Coe d) from rfl, coe_torusDiag, diagonal_apply_ne _ (Ne.symm hi),
    hrhs, u5PermMatrix_apply] at hentry
  simp at hentry

private def u5Shift (σ : Equiv.Perm (Fin 5)) :
    (Fin 5 → rootsOfUnity 5 K) →* (Fin 5 → rootsOfUnity 5 K) where
  toFun d i := d (σ i)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem u5Shift_mul (σ τ : Equiv.Perm (Fin 5))
    (d : Fin 5 → rootsOfUnity 5 K) :
    u5Shift σ (u5Shift τ d) = u5Shift (τ * σ) d := rfl

private theorem u5CycleU_mul_torusHom (h : UnitaryFieldData 2 2 K)
    (d : Fin 5 → rootsOfUnity 5 K) :
    u5CycleU h * u5TorusHom h d * (u5CycleU h)⁻¹ =
      u5TorusHom h (u5Shift (finRotate 5) d) := by
  apply Subtype.ext
  apply Units.ext
  show (((u5Cycle : GL (Fin 5) K) * (torusDiag (u5Coe d) : GL (Fin 5) K) *
      ((u5Cycle : GL (Fin 5) K))⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
    ((torusDiag (u5Coe (u5Shift (finRotate 5) d)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)
  rw [Units.val_mul, Units.val_mul, coe_u5Cycle, u5Cycle_inv_coe, coe_torusDiag, coe_torusDiag]
  rw [u5Conj_formula]
  congr 1

private theorem u5CycleU_pow_five (h : UnitaryFieldData 2 2 K) : u5CycleU h ^ 5 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact u5Cycle_pow_five

private theorem u5CycleU_pow_mul_torusHom (h : UnitaryFieldData 2 2 K) (k : ℕ)
    (d : Fin 5 → rootsOfUnity 5 K) :
    u5CycleU h ^ k * u5TorusHom h d * (u5CycleU h ^ k)⁻¹ =
      u5TorusHom h (u5Shift ((finRotate 5) ^ k) d) := by
  induction k generalizing d with
  | zero => simp [u5Shift]
  | succ k ih =>
    have hgroup : u5CycleU h ^ (k + 1) * u5TorusHom h d * (u5CycleU h ^ (k + 1))⁻¹ =
        u5CycleU h ^ k * (u5CycleU h * u5TorusHom h d * (u5CycleU h)⁻¹) *
          (u5CycleU h ^ k)⁻¹ := by
      group
    rw [hgroup, u5CycleU_mul_torusHom h d, ih, u5Shift_mul, pow_succ']

private theorem u5CycleU_pow_mul_torusHom' (h : UnitaryFieldData 2 2 K) (k : ℕ)
    (d : Fin 5 → rootsOfUnity 5 K) :
    u5CycleU h ^ k * u5TorusHom h d =
      u5TorusHom h (u5Shift ((finRotate 5) ^ k) d) * u5CycleU h ^ k := by
  have h1 := u5CycleU_pow_mul_torusHom h k d
  rw [← h1]
  group

private def u5InvExp (j : ℕ) : ℕ := 5 * (j / 5 + 1) - j

private theorem u5CycleU_pow_mul_invExp (h : UnitaryFieldData 2 2 K) (j : ℕ) :
    u5CycleU h ^ j * u5CycleU h ^ u5InvExp j = 1 := by
  rw [← pow_add]
  have hle : j ≤ 5 * (j / 5 + 1) := by
    have h1 : j / 5 * 5 ≤ j := Nat.div_mul_le_self j 5
    omega
  rw [u5InvExp, Nat.add_sub_cancel' hle, pow_mul, u5CycleU_pow_five, one_pow]

private theorem u5CycleU_pow_inv_eq (h : UnitaryFieldData 2 2 K) (j : ℕ) :
    (u5CycleU h ^ j)⁻¹ = u5CycleU h ^ u5InvExp j :=
  inv_eq_of_mul_eq_one_right (u5CycleU_pow_mul_invExp h j)

noncomputable def u5Mono (h : UnitaryFieldData 2 2 K) : Subgroup (uU h 5) where
  carrier := {x | ∃ (d : Fin 5 → rootsOfUnity 5 K) (j : ℕ),
    x = u5TorusHom h d * u5CycleU h ^ j}
  mul_mem' := by
    rintro x y ⟨d, j, rfl⟩ ⟨e, j', rfl⟩
    refine ⟨d * u5Shift ((finRotate 5) ^ j) e, j + j', ?_⟩
    calc u5TorusHom h d * u5CycleU h ^ j * (u5TorusHom h e * u5CycleU h ^ j')
        = u5TorusHom h d * (u5CycleU h ^ j * u5TorusHom h e) * u5CycleU h ^ j' := by
          group
      _ = u5TorusHom h d * (u5TorusHom h (u5Shift ((finRotate 5) ^ j) e) *
            u5CycleU h ^ j) * u5CycleU h ^ j' := by
          rw [u5CycleU_pow_mul_torusHom']
      _ = (u5TorusHom h d * u5TorusHom h (u5Shift ((finRotate 5) ^ j) e)) *
            u5CycleU h ^ (j + j') := by
          rw [pow_add]
          group
      _ = u5TorusHom h (d * u5Shift ((finRotate 5) ^ j) e) * u5CycleU h ^ (j + j') := by
          rw [map_mul]
  one_mem' := ⟨1, 0, by simp⟩
  inv_mem' := by
    rintro x ⟨d, j, rfl⟩
    refine ⟨u5Shift ((finRotate 5) ^ u5InvExp j) d⁻¹, u5InvExp j, ?_⟩
    calc (u5TorusHom h d * u5CycleU h ^ j)⁻¹
        = (u5CycleU h ^ j)⁻¹ * (u5TorusHom h d)⁻¹ := by group
      _ = u5CycleU h ^ u5InvExp j * (u5TorusHom h d)⁻¹ := by
          rw [u5CycleU_pow_inv_eq]
      _ = u5CycleU h ^ u5InvExp j * u5TorusHom h d⁻¹ := by rw [map_inv]
      _ = u5TorusHom h (u5Shift ((finRotate 5) ^ u5InvExp j) d⁻¹) *
            u5CycleU h ^ u5InvExp j :=
          u5CycleU_pow_mul_torusHom' h (u5InvExp j) d⁻¹

private theorem u5Torus_le_u5Mono (h : UnitaryFieldData 2 2 K) : u5Torus h ≤ u5Mono h := by
  rintro x ⟨d, rfl⟩
  exact ⟨d, 0, by simp⟩

private theorem orderOf_u5CycleU (h : UnitaryFieldData 2 2 K) :
    orderOf (u5CycleU h) = 5 := by
  have hdvd : orderOf (u5CycleU h) ∣ 5 :=
    orderOf_dvd_iff_pow_eq_one.mpr (u5CycleU_pow_five h)
  have hne : orderOf (u5CycleU h) ≠ 1 := by
    intro h1
    have h3 : u5CycleU h ^ 1 ∈ u5Torus h := by
      rw [show u5CycleU h ^ 1 = 1 from by rw [pow_one, orderOf_eq_one_iff.mp h1]]
      exact (u5Torus h).one_mem
    exact u5CycleU_pow_not_torus h (by norm_num) (by norm_num) h3
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
  · exact absurd h hne
  · exact h

private theorem u5Exp_pos {a b : Fin 5} (hab : a ≠ b) :
    0 < (b + u5InvExp (a : ℕ)) % 5 ∧ (b + u5InvExp (a : ℕ)) % 5 < 5 := by
  have hne : (b + u5InvExp (a : ℕ)) % 5 ≠ 0 := by
    intro h0
    have hdvd : 5 ∣ (b + u5InvExp (a : ℕ)) := Nat.dvd_of_mod_eq_zero h0
    fin_cases a <;> fin_cases b <;>
      first
      | (exfalso; exact hab rfl)
      | (norm_num [u5InvExp] at hdvd)
  exact ⟨Nat.pos_of_ne_zero hne, Nat.mod_lt _ (by norm_num)⟩

private theorem u5Mono_normal_injective (h : UnitaryFieldData 2 2 K)
    {d e : Fin 5 → rootsOfUnity 5 K} {a b : Fin 5}
    (heq : u5TorusHom h d * u5CycleU h ^ (a : ℕ) =
      u5TorusHom h e * u5CycleU h ^ (b : ℕ)) : d = e ∧ a = b := by
  rcases eq_or_ne a b with hab | hab
  · subst hab
    refine ⟨u5TorusHom_injective h (mul_right_cancel heq), rfl⟩
  · exfalso
    have hT : (u5TorusHom h e)⁻¹ * u5TorusHom h d ∈ u5Torus h :=
      (u5Torus h).mul_mem ((u5Torus h).inv_mem ⟨e, rfl⟩) ⟨d, rfl⟩
    have heq' : (u5TorusHom h e)⁻¹ * u5TorusHom h d =
        u5CycleU h ^ (b : ℕ) * (u5CycleU h ^ (a : ℕ))⁻¹ := by
      calc (u5TorusHom h e)⁻¹ * u5TorusHom h d
          = (u5TorusHom h e)⁻¹ * (u5TorusHom h d * u5CycleU h ^ (a : ℕ)) *
              (u5CycleU h ^ (a : ℕ))⁻¹ := by group
        _ = (u5TorusHom h e)⁻¹ * (u5TorusHom h e * u5CycleU h ^ (b : ℕ)) *
              (u5CycleU h ^ (a : ℕ))⁻¹ := by rw [heq]
        _ = u5CycleU h ^ (b : ℕ) * (u5CycleU h ^ (a : ℕ))⁻¹ := by group
    rw [heq', u5CycleU_pow_inv_eq, ← pow_add, ← pow_mod_orderOf, orderOf_u5CycleU] at hT
    obtain ⟨hk0, hk5⟩ := u5Exp_pos hab
    exact u5CycleU_pow_not_torus h hk0 hk5 hT

private noncomputable def u5MonoFwd (h : UnitaryFieldData 2 2 K) :
    ((Fin 5 → rootsOfUnity 5 K) × Fin 5) → u5Mono h :=
  fun p => ⟨u5TorusHom h p.1 * u5CycleU h ^ (p.2 : ℕ), ⟨p.1, p.2, rfl⟩⟩

private theorem u5MonoFwd_injective (h : UnitaryFieldData 2 2 K) :
    Function.Injective (u5MonoFwd h) := by
  rintro ⟨d, a⟩ ⟨e, b⟩ heq
  have h2 : u5TorusHom h d * u5CycleU h ^ (a : ℕ) =
      u5TorusHom h e * u5CycleU h ^ (b : ℕ) := congrArg Subtype.val heq
  obtain ⟨hde, hab⟩ := u5Mono_normal_injective h h2
  subst hde
  subst hab
  rfl

private theorem u5MonoFwd_surjective (h : UnitaryFieldData 2 2 K) :
    Function.Surjective (u5MonoFwd h) := by
  rintro ⟨x, hx⟩
  obtain ⟨d, j, rfl⟩ := hx
  refine ⟨(d, ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
  apply Subtype.ext
  change u5TorusHom h d * u5CycleU h ^ ((j % 5 : ℕ)) =
    u5TorusHom h d * u5CycleU h ^ j
  rw [show u5CycleU h ^ ((j % 5 : ℕ)) = u5CycleU h ^ j from
    (pow_eq_pow_mod j (u5CycleU_pow_five h)).symm]

private noncomputable def u5MonoEquiv (h : UnitaryFieldData 2 2 K) :
    ((Fin 5 → rootsOfUnity 5 K) × Fin 5) ≃ u5Mono h :=
  Equiv.ofBijective (u5MonoFwd h) ⟨u5MonoFwd_injective h, u5MonoFwd_surjective h⟩

private theorem card_rootsOfUnity_five (h : UnitaryFieldData 2 2 K) :
    Nat.card (rootsOfUnity 5 K) = 5 := by
  have hfin : Finite K := h.finite
  rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, h.card]
  norm_num

private theorem card_u5Torus (h : UnitaryFieldData 2 2 K) : Nat.card (u5Torus h) = 5 ^ 5 := by
  have hfin : Finite K := h.finite
  rw [u5Torus, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (u5TorusHom_injective h), Subgroup.card_top,
    Nat.card_fun, Nat.card_fin, card_rootsOfUnity_five h]

private theorem card_u5Mono (h : UnitaryFieldData 2 2 K) : Nat.card (u5Mono h) = 5 ^ 6 := by
  have hfin : Finite K := h.finite
  rw [← Nat.card_congr (u5MonoEquiv h), Nat.card_prod, Nat.card_fun, Nat.card_fin,
    card_rootsOfUnity_five h]
  norm_num

private theorem isPGroup_u5Mono (h : UnitaryFieldData 2 2 K) : IsPGroup 5 (u5Mono h) :=
  IsPGroup.of_card (n := 6) (by rw [card_u5Mono h])

private theorem uU_eq_statedGU_five (h : UnitaryFieldData 2 2 K) :
    uU h 5 = CFSG.Quasithin.StatedGU 5 (2 ^ 2) K := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ 4 := by
    funext c
    rw [h.bar_apply]
    norm_num
  apply le_antisymm
  · intro A hA
    exact Subgroup.subset_closure (by simpa [hbar] using (mem_uU h).mp hA)
  · rw [CFSG.Quasithin.StatedGU, Subgroup.closure_le]
    intro A hA
    change A ∈ uU h 5
    rw [mem_uU]
    simpa [hbar] using hA

private theorem card_statedProj_statedSU_five (h : UnitaryFieldData 2 2 K) :
    Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K)) = 4 ^ 10 * 50968125 := by
  have hfin : Finite K := h.finite
  have hL : Nat.card K = (2 ^ 2) ^ 2 := by rw [h.card]; norm_num
  have hprod : (∏ i ∈ Finset.Icc 2 5, ((((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat)) =
      254840625 := by
    norm_num [Finset.prod_Icc_succ_top]
  have hPSU := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K)
    (p := 2) (f := 2) (n := 5) Nat.prime_two (by norm_num) hL (by norm_num)
  rw [hprod] at hPSU
  rw [hPSU]
  norm_num

private theorem card_statedSU_five (h : UnitaryFieldData 2 2 K) :
    Nat.card (StatedSU 5 (2 ^ 2) K) = 4 ^ 10 * 254840625 := by
  have hfin : Finite K := h.finite
  have hL : Nat.card K = (2 ^ 2) ^ 2 := by rw [h.card]; norm_num
  have hker := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.famU_card_ker_proj
    (L := K) (ℓ := 2) (f := 2) (n := 5) Nat.prime_two hL (by norm_num)
  have htop : (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.famUProj 5 (2 ^ 2) K).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (fun x => QuotientGroup.mk'_surjective _ x)
  have hrange : Nat.card
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.famUProj 5 (2 ^ 2) K).range =
      Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K)) := by
    rw [htop, Subgroup.card_top]
  have hSU := Subgroup.card_ker_mul_card_range
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.famUProj 5 (2 ^ 2) K)
  rw [hrange, hker, card_statedProj_statedSU_five h] at hSU
  rw [← hSU]
  norm_num

private theorem card_uU_five (h : UnitaryFieldData 2 2 K) :
    Nat.card (uU h 5) = 4 ^ 10 * 5 ^ 6 * 81549 := by
  have hfin : Finite K := h.finite
  have hL : Nat.card K = (2 ^ 2) ^ 2 := by rw [h.card]; norm_num
  have hGU := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.famU_card_GU
    (L := K) (ℓ := 2) (f := 2) (n := 5) Nat.prime_two hL (by norm_num)
  rw [uU_eq_statedGU_five h, hGU, card_statedSU_five h]
  norm_num

private def u5ConstHom : rootsOfUnity 5 K →* (Fin 5 → rootsOfUnity 5 K) where
  toFun c := fun _ => c
  map_one' := rfl
  map_mul' _ _ := rfl

private def u5Const : Subgroup (Fin 5 → rootsOfUnity 5 K) :=
  (u5ConstHom (K := K)).range

private theorem u5ConstHom_injective : Function.Injective (u5ConstHom (K := K)) := by
  intro a b h
  have := congrFun h 0
  simpa [u5ConstHom] using this

private theorem mem_u5Const {d : Fin 5 → rootsOfUnity 5 K} :
    d ∈ u5Const (K := K) ↔ ∃ c : rootsOfUnity 5 K, ∀ i, d i = c := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun _ => rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    funext i
    exact (hc i).symm

private theorem card_u5Const (h : UnitaryFieldData 2 2 K) : Nat.card (u5Const (K := K)) = 5 := by
  have hfin : Finite K := h.finite
  rw [u5Const, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (u5ConstHom_injective (K := K)), Subgroup.card_top,
    card_rootsOfUnity_five h]

private def u5Rat (k : ℕ) :
    (Fin 5 → rootsOfUnity 5 K) →* (Fin 5 → rootsOfUnity 5 K) where
  toFun d := d * (u5Shift (finRotate 5 ^ k) d)⁻¹
  map_one' := by
    funext i
    simp [u5Shift]
  map_mul' a b := by
    funext i
    show a i * b i * ((u5Shift (finRotate 5 ^ k)) (a * b) i)⁻¹ =
      a i * ((u5Shift (finRotate 5 ^ k)) a i)⁻¹ *
        (b i * ((u5Shift (finRotate 5 ^ k)) b i)⁻¹)
    rw [show (u5Shift (finRotate 5 ^ k)) (a * b) i =
      ((u5Shift (finRotate 5 ^ k)) a i) * ((u5Shift (finRotate 5 ^ k)) b i) from rfl,
      mul_inv]
    simp only [mul_left_comm, mul_assoc]

private theorem finRotate_pow_orbit {k : ℕ} (hk0 : 0 < k) (hk5 : k < 5) (i : Fin 5) :
    ∃ m : ℕ, ((finRotate 5 ^ k) ^ m) 0 = i := by
  have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk with rfl | rfl | rfl | rfl <;>
    fin_cases i <;>
    first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩
    | exact ⟨4, by decide⟩

private theorem u5Shift_eq_self_mem_const {k : ℕ} (hk0 : 0 < k) (hk5 : k < 5)
    {d : Fin 5 → rootsOfUnity 5 K} (hd : u5Shift (finRotate 5 ^ k) d = d) :
    d ∈ u5Const (K := K) := by
  rw [mem_u5Const]
  refine ⟨d 0, fun i => ?_⟩
  obtain ⟨m, hm⟩ := finRotate_pow_orbit hk0 hk5 i
  have hstep : ∀ x, d ((finRotate 5 ^ k) x) = d x := fun x => congrFun hd x
  have hind : ∀ m : ℕ, d (((finRotate 5 ^ k) ^ m) 0) = d 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hstep, ih]
  rw [← hm]
  exact hind m

private theorem u5Rat_ker_eq_u5Const {k : ℕ} (hk0 : 0 < k) (hk5 : k < 5) :
    (u5Rat (K := K) k).ker = u5Const (K := K) := by
  ext d
  rw [MonoidHom.mem_ker]
  constructor
  · intro hd
    have hshift : d = u5Shift (finRotate 5 ^ k) d := by
      funext i
      have hi := congrFun hd i
      change d i * ((u5Shift (finRotate 5 ^ k)) d i)⁻¹ = 1 at hi
      exact mul_inv_eq_one.mp hi
    exact u5Shift_eq_self_mem_const hk0 hk5 hshift.symm
  · intro hd
    rw [mem_u5Const] at hd
    obtain ⟨c, hc⟩ := hd
    funext i
    change d i * ((u5Shift (finRotate 5 ^ k)) d i)⁻¹ = 1
    rw [show (u5Shift (finRotate 5 ^ k)) d i = d ((finRotate 5 ^ k) i) from rfl,
      hc ((finRotate 5 ^ k) i), hc i, mul_inv_cancel]

private theorem u5Torus_scalar_family (h : UnitaryFieldData 2 2 K)
    {f : Fin 5 → rootsOfUnity 5 K}
    (hf : u5TorusHom h f ∈ (uConjAut h (n := 5) (by norm_num)).ker) :
    f ∈ u5Const (K := K) := by
  rw [MonoidHom.mem_ker] at hf
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h (by norm_num) (u5TorusHom h f)).mp hf
  have hcoef : ∀ i : Fin 5, (((u5TorusHom h f : uU h 5) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) i i = (c : K) := by
    intro i
    have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin 5) K =>
      (g : Matrix (Fin 5) (Fin 5) K)) hc) i) i
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h1
  rw [mem_u5Const]
  refine ⟨f 0, fun i => ?_⟩
  apply Subtype.ext
  apply Units.ext
  have hi := hcoef i
  have h0 := hcoef 0
  rw [show ((u5TorusHom h f : uU h 5) : GL (Fin 5) K) = torusDiag (u5Coe f)
    from rfl, coe_torusDiag, Matrix.diagonal_apply_eq] at hi h0
  exact hi.trans h0.symm

private theorem u5Mono_conj (h : UnitaryFieldData 2 2 K)
    {d : Fin 5 → rootsOfUnity 5 K} {j : ℕ} (e : Fin 5 → rootsOfUnity 5 K) :
    (u5TorusHom h d * u5CycleU h ^ j) * u5TorusHom h e *
        (u5TorusHom h d * u5CycleU h ^ j)⁻¹ =
      u5TorusHom h (u5Shift (finRotate 5 ^ j) e) := by
  have hw := u5CycleU_pow_mul_torusHom h j e
  calc (u5TorusHom h d * u5CycleU h ^ j) * u5TorusHom h e *
        (u5TorusHom h d * u5CycleU h ^ j)⁻¹
      = u5TorusHom h d * (u5CycleU h ^ j * u5TorusHom h e * (u5CycleU h ^ j)⁻¹) *
          (u5TorusHom h d)⁻¹ := by group
    _ = u5TorusHom h d * u5TorusHom h (u5Shift (finRotate 5 ^ j) e) *
          (u5TorusHom h d)⁻¹ := by rw [hw]
    _ = u5TorusHom h d * u5TorusHom h (u5Shift (finRotate 5 ^ j) e) *
          (u5TorusHom h d)⁻¹ := rfl
    _ = u5TorusHom h (d * u5Shift (finRotate 5 ^ j) e * d⁻¹) := by
        rw [map_mul, map_mul, map_inv]
    _ = u5TorusHom h (u5Shift (finRotate 5 ^ j) e) := by
        congr 1
        rw [mul_comm d (u5Shift (finRotate 5 ^ j) e), mul_assoc, mul_inv_cancel, mul_one]

private theorem u5Mono_card_le (h : UnitaryFieldData 2 2 K)
    {d : Fin 5 → rootsOfUnity 5 K} {j : ℕ}
    (hyT : u5TorusHom h d * u5CycleU h ^ j ∉ u5Torus h)
    (E : Subgroup (uU h 5)) (hE : E ≤ u5Torus h)
    (hcomm : ∀ s ∈ E, s * (u5TorusHom h d * u5CycleU h ^ j) * s⁻¹ *
      (u5TorusHom h d * u5CycleU h ^ j)⁻¹ ∈
        (uConjAut h (n := 5) (by norm_num)).ker) :
    Nat.card E ≤ 5 ^ 2 := by
  classical
  have hfin : Finite K := h.finite
  set k := j % 5 with hk
  have hklt : k < 5 := Nat.mod_lt _ (by norm_num)
  have hkne : k ≠ 0 := by
    intro h0
    apply hyT
    refine ⟨d, ?_⟩
    rw [pow_eq_pow_mod j (u5CycleU_pow_five h), ← hk, h0, pow_zero, mul_one]
  have hτ : finRotate 5 ^ j = finRotate 5 ^ k := pow_eq_pow_mod j (by decide)
  let E' : Subgroup (Fin 5 → rootsOfUnity 5 K) := E.comap (u5TorusHom h)
  let ψ : E' →* (Fin 5 → rootsOfUnity 5 K) := (u5Rat (K := K) k).comp E'.subtype
  have hconj : ∀ e : Fin 5 → rootsOfUnity 5 K,
      u5TorusHom h e * (u5TorusHom h d * u5CycleU h ^ j) * (u5TorusHom h e)⁻¹ *
        (u5TorusHom h d * u5CycleU h ^ j)⁻¹ =
        u5TorusHom h (u5Rat (K := K) k e) := by
    intro e
    have hc := u5Mono_conj h (d := d) (j := j) e
    rw [hτ] at hc
    calc u5TorusHom h e * (u5TorusHom h d * u5CycleU h ^ j) * (u5TorusHom h e)⁻¹ *
          (u5TorusHom h d * u5CycleU h ^ j)⁻¹
        = u5TorusHom h e * ((u5TorusHom h d * u5CycleU h ^ j) *
            (u5TorusHom h e)⁻¹ * (u5TorusHom h d * u5CycleU h ^ j)⁻¹) := by group
      _ = u5TorusHom h e * ((u5TorusHom h d * u5CycleU h ^ j) *
            (u5TorusHom h e) * (u5TorusHom h d * u5CycleU h ^ j)⁻¹)⁻¹ := by group
      _ = u5TorusHom h e * (u5TorusHom h (u5Shift (finRotate 5 ^ k) e))⁻¹ := by rw [hc]
      _ = u5TorusHom h (e * (u5Shift (finRotate 5 ^ k) e)⁻¹) := by
          rw [map_mul, map_inv]
      _ = u5TorusHom h (u5Rat (K := K) k e) := rfl
  have hcardker : Nat.card ψ.ker ≤ 5 := by
    have hle : ψ.ker.map E'.subtype ≤ u5Const (K := K) := by
      rintro f ⟨e, he, rfl⟩
      have he' : ψ e = 1 := he
      change u5Rat (K := K) k e.1 = 1 at he'
      rw [← u5Rat_ker_eq_u5Const (K := K) (by omega) hklt]
      exact MonoidHom.mem_ker.mpr he'
    have hcard : Nat.card ψ.ker = Nat.card (ψ.ker.map E'.subtype) :=
      (Subgroup.card_map_of_injective E'.subtype_injective).symm
    rw [hcard]
    calc Nat.card (ψ.ker.map E'.subtype) ≤ Nat.card (u5Const (K := K)) :=
          Subgroup.card_le_of_le hle
      _ = 5 := card_u5Const h
  have hcardrange : Nat.card ψ.range ≤ 5 := by
    have hle : ψ.range ≤ u5Const (K := K) := by
      rintro f hf
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hf
      have hmemE : u5TorusHom h e.1 ∈ E := e.2
      have hc := hcomm (u5TorusHom h e.1) hmemE
      rw [hconj e.1] at hc
      exact u5Torus_scalar_family h hc
    calc Nat.card ψ.range ≤ Nat.card (u5Const (K := K)) := Subgroup.card_le_of_le hle
      _ = 5 := card_u5Const h
  have hmap : E'.map (u5TorusHom h) = E := Subgroup.map_comap_eq_self hE
  have hcardE : Nat.card E = Nat.card E' := by
    rw [← hmap, Subgroup.card_map_of_injective (u5TorusHom_injective h)]
  have hcardE' : Nat.card E' = Nat.card ψ.ker * Nat.card ψ.range :=
    (Subgroup.card_ker_mul_card_range ψ).symm
  calc Nat.card E = Nat.card E' := hcardE
    _ = Nat.card ψ.ker * Nat.card ψ.range := hcardE'
    _ ≤ 5 * 5 := Nat.mul_le_mul hcardker hcardrange
    _ = 5 ^ 2 := by norm_num

private def u5Ratio :
    (Fin 5 → rootsOfUnity 5 K) →* (rootsOfUnity 5 K × rootsOfUnity 5 K) where
  toFun d := (d 0 * (d 1)⁻¹, d 2 * (d 3)⁻¹)
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext <;> simp [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc]

private def u5BlockEntries : Subgroup (Fin 5 → rootsOfUnity 5 K) :=
  (u5Ratio (K := K)).ker

noncomputable def u5BlockTorus (h : UnitaryFieldData 2 2 K) : Subgroup (uU h 5) :=
  (u5BlockEntries (K := K)).map (u5TorusHom h)

private theorem u5BlockTorus_le_u5Torus (h : UnitaryFieldData 2 2 K) :
    u5BlockTorus h ≤ u5Torus h := by
  rw [u5BlockTorus]
  exact Subgroup.map_le_range _ _

private theorem card_u5BlockEntries (h : UnitaryFieldData 2 2 K) :
    (u5BlockEntries (K := K)).index ≤ 5 ^ 2 := by
  have hfin : Finite K := h.finite
  have hindex := Subgroup.index_ker (u5Ratio (K := K))
  change (u5Ratio (K := K)).ker.index ≤ 5 ^ 2
  rw [hindex]
  calc Nat.card (u5Ratio (K := K)).range
      ≤ Nat.card (rootsOfUnity 5 K × rootsOfUnity 5 K) :=
        Subgroup.card_le_card_group (H := (u5Ratio (K := K)).range)
    _ = 5 ^ 2 := by
        rw [Nat.card_prod, card_rootsOfUnity_five h]
        norm_num

private theorem relIndex_u5BlockTorus (h : UnitaryFieldData 2 2 K) :
    (u5BlockTorus h).relIndex (u5Torus h) ≤ 5 ^ 2 := by
  have hfin : Finite K := h.finite
  have hle := u5BlockTorus_le_u5Torus h
  have hD : Nat.card (u5BlockTorus h) = Nat.card (u5BlockEntries (K := K)) := by
    rw [u5BlockTorus]
    exact Subgroup.card_map_of_injective (u5TorusHom_injective h)
  have hT : Nat.card (u5Torus h) = Nat.card (Fin 5 → rootsOfUnity 5 K) := by
    rw [u5Torus, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (u5TorusHom_injective h), Subgroup.card_top]
  have hdom : Nat.card (Fin 5 → rootsOfUnity 5 K) =
      (u5BlockEntries (K := K)).index * Nat.card (u5BlockEntries (K := K)) := by
    rw [Subgroup.index_mul_card]
  have hrel : (u5BlockTorus h).relIndex (u5Torus h) * Nat.card (u5BlockTorus h) =
      Nat.card (u5Torus h) := by
    have hrc := Subgroup.relIndex_mul_card (H := u5BlockTorus h) (K := u5Torus h)
    rw [inf_eq_left.mpr hle] at hrc
    exact hrc
  have hrel' : (u5BlockTorus h).relIndex (u5Torus h) *
      Nat.card (u5BlockEntries (K := K)) =
      (u5BlockEntries (K := K)).index * Nat.card (u5BlockEntries (K := K)) := by
    calc (u5BlockTorus h).relIndex (u5Torus h) * Nat.card (u5BlockEntries (K := K))
        = (u5BlockTorus h).relIndex (u5Torus h) * Nat.card (u5BlockTorus h) := by rw [hD]
      _ = Nat.card (u5Torus h) := hrel
      _ = Nat.card (Fin 5 → rootsOfUnity 5 K) := hT
      _ = (u5BlockEntries (K := K)).index * Nat.card (u5BlockEntries (K := K)) := hdom
  have hmul : (u5BlockTorus h).relIndex (u5Torus h) *
      Nat.card (u5BlockEntries (K := K)) ≤
      5 ^ 2 * Nat.card (u5BlockEntries (K := K)) := by
    rw [hrel']
    exact Nat.mul_le_mul_right _ (card_u5BlockEntries h)
  exact Nat.le_of_mul_le_mul_right hmul (Nat.card_pos)

private theorem ker_uConjAut_le_u5BlockTorus (h : UnitaryFieldData 2 2 K) :
    (uConjAut h (n := 5) (by norm_num)).ker ≤ u5BlockTorus h := by
  intro A hA
  rw [MonoidHom.mem_ker] at hA
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h (by norm_num) A).mp hA
  have hc5 : c ^ 5 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have hnorm : h.norm (c : K) = 1 := by
      have hA' := (mem_uU h).1 A.2
      rw [hc, GeneralLinearGroup.coe_scalar] at hA'
      have e := congrFun (congrFun hA' ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.mul_apply, scalar_apply, diagonal_apply, UnitaryFieldData.norm, mul_comm]
        using e
    rw [UnitaryFieldData.norm, h.bar_apply] at hnorm
    simpa [pow_succ, mul_comm] using hnorm
  let c5 : rootsOfUnity 5 K := ⟨c, (mem_rootsOfUnity 5 c).mpr hc5⟩
  have hent : (fun _ : Fin 5 => c5) ∈ u5BlockEntries (K := K) := by
    rw [u5BlockEntries, MonoidHom.mem_ker]
    ext <;> simp [u5Ratio]
  rw [u5BlockTorus]
  refine Subgroup.mem_map.mpr ⟨fun _ => c5, hent, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [hc]
  change ((torusDiag (fun _ => c) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
    (GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K)
  rw [scalar_eq_torusDiag]

private theorem u5BlockTorus_diag (h : UnitaryFieldData 2 2 K) :
    ∀ A ∈ u5BlockTorus h, ∃ d : Fin 5 → K,
      (((A : uU h 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal d ∧
        d 0 = d 1 ∧ d 2 = d 3 := by
  intro A hA
  rw [u5BlockTorus] at hA
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hA
  rw [u5BlockEntries, MonoidHom.mem_ker] at he
  have h01 : e 0 = e 1 := by
    have h := congrArg Prod.fst he
    simp [u5Ratio] at h
    exact mul_inv_eq_one.mp h
  have h23 : e 2 = e 3 := by
    have h := congrArg Prod.snd he
    simp [u5Ratio] at h
    exact mul_inv_eq_one.mp h
  refine ⟨fun i => ((e i : Kˣ) : K), ?_, ?_, ?_⟩
  · rw [show ((u5TorusHom h e : uU h 5) : GL (Fin 5) K) = torusDiag (u5Coe e)
      from rfl, coe_torusDiag]
    rfl
  · have := congrArg (fun x : rootsOfUnity 5 K => ((x : Kˣ) : K)) h01
    simpa using this
  · have := congrArg (fun x : rootsOfUnity 5 K => ((x : Kˣ) : K)) h23
    simpa using this

private theorem card_index_u5Mono (h : UnitaryFieldData 2 2 K) :
    (u5Mono h).index = 4 ^ 10 * 81549 := by
  have hpos : 0 < 5 ^ 6 := by norm_num
  have hidx : (u5Mono h).index * Nat.card (u5Mono h) = Nat.card (uU h 5) :=
    Subgroup.index_mul_card _
  rw [card_u5Mono h, card_uU_five h] at hidx
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hidx]
  ring

private theorem not_dvd_index_u5Mono (h : UnitaryFieldData 2 2 K) :
    ¬ 5 ∣ (u5Mono h).index := by
  rw [card_index_u5Mono h]
  norm_num

private theorem relIndex_u5Torus_u5Mono (h : UnitaryFieldData 2 2 K) :
    (u5Torus h).relIndex (u5Mono h) ≤ 5 := by
  have hle := u5Torus_le_u5Mono h
  have hrc := Subgroup.relIndex_mul_card (H := u5Torus h) (K := u5Mono h)
  rw [inf_eq_left.mpr hle] at hrc
  have hcard : (u5Torus h).relIndex (u5Mono h) = 5 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card (u5Torus h) from by
      rw [card_u5Torus h]; norm_num)
    rw [hrc, card_u5Torus h, card_u5Mono h]
    norm_num
  rw [hcard]

theorem exists_u5_monomial (h : UnitaryFieldData 2 2 K) :
    ∃ Q T D : Subgroup (uU h 5), IsPGroup 5 Q ∧ ¬ 5 ∣ Q.index ∧ T ≤ Q ∧ T.relIndex Q ≤ 5 ∧
      (∀ y ∈ Q, y ∉ T → ∀ E : Subgroup (uU h 5), E ≤ T →
        (∀ s ∈ E, s * y * s⁻¹ * y⁻¹ ∈ (uConjAut h (n := 5) (by norm_num)).ker) →
          Nat.card E ≤ 5 ^ 2) ∧
      D ≤ T ∧ (uConjAut h (n := 5) (by norm_num)).ker ≤ D ∧ D.relIndex T ≤ 5 ^ 2 ∧
      ∀ A ∈ D, ∃ d : Fin 5 → K,
        ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal d ∧ d 0 = d 1 ∧
          d 2 = d 3 := by
  refine ⟨u5Mono h, u5Torus h, u5BlockTorus h, isPGroup_u5Mono h, not_dvd_index_u5Mono h,
    u5Torus_le_u5Mono h, relIndex_u5Torus_u5Mono h, ?_, u5BlockTorus_le_u5Torus h,
    ker_uConjAut_le_u5BlockTorus h, relIndex_u5BlockTorus h, u5BlockTorus_diag h⟩
  intro y hy hyT E hE hcomm
  obtain ⟨d, j, rfl⟩ := hy
  exact u5Mono_card_le h hyT E hE hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
