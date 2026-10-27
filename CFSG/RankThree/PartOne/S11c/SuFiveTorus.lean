module

public import CFSG.RankThree.PartOne.KF.SU5Swap
public import CFSG.RankThree.PartOne.KF.SymTorus
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K]

@[expose] def torusVecEq (i j : Fin 5) (K : Type) [Field K] : Subgroup (Fin 5 → Kˣ) where
  carrier := {d | (∀ k, d k ^ 5 = 1) ∧ ∏ k, d k = 1 ∧ d i = d j}
  mul_mem' := fun {a b} ha hb => ⟨fun k => by simp [mul_pow, ha.1 k, hb.1 k],
    by simp [Finset.prod_mul_distrib, ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩
  one_mem' := ⟨fun k => by simp, by simp, rfl⟩
  inv_mem' := fun {a} ha => ⟨fun k => by simp [inv_pow, ha.1 k],
    by simp [Finset.prod_inv_distrib, ha.2.1], by simp [ha.2.2]⟩

@[expose] def torusEq (i j : Fin 5) (K : Type) [Field K] : Subgroup (GL (Fin 5) K) :=
  (torusVecEq i j K).map KFU.diagUHom

theorem mem_torusEq_iff {i j : Fin 5} {g : GL (Fin 5) K} :
    g ∈ torusEq i j K ↔ ∃ d : Fin 5 → Kˣ, (∀ k, d k ^ 5 = 1) ∧ ∏ k, d k = 1 ∧ d i = d j ∧
      KFU.diagU d = g := by
  constructor
  · rintro ⟨d, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨d, h1, h2, h3, rfl⟩
  · rintro ⟨d, h1, h2, h3, rfl⟩
    exact ⟨d, ⟨h1, h2, h3⟩, rfl⟩

theorem isDiag_of_mem_torusEq {i j : Fin 5} {g : GL (Fin 5) K} (hg : g ∈ torusEq i j K) :
    ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag := by
  obtain ⟨d, -, -, -, rfl⟩ := mem_torusEq_iff.mp hg
  exact KFU.isDiag_diagU d

theorem entry_eq_of_mem_torusEq {i j : Fin 5} {g : GL (Fin 5) K} (hg : g ∈ torusEq i j K) :
    ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i i =
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) j j := by
  obtain ⟨d, -, -, hd, rfl⟩ := mem_torusEq_iff.mp hg
  rw [KFU.diagU_apply_same, KFU.diagU_apply_same, hd]

theorem bar_mul_self_eq_one_of_pow_five (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {u : K}
    (hu : u ^ 5 = 1) : h.bar u * u = 1 := by
  obtain ⟨t, ht⟩ := h5
  rw [UnitaryFieldData.bar_apply, ← pow_succ, ht, pow_mul, hu, one_pow]

theorem torusEq_le_unitarySU (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (i j : Fin 5) :
    torusEq i j K ≤ unitarySU 2 f K 5 := by
  intro g hg
  obtain ⟨d, hd5, hprod, -, rfl⟩ := mem_torusEq_iff.mp hg
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [KFU.det_diagU, ← Units.coe_prod, hprod, Units.val_one]
  · rw [KFU.diagU_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have : (fun k => h.bar (d k : K) * (d k : K)) = fun _ => 1 := funext fun k =>
      bar_mul_self_eq_one_of_pow_five h h5 (by rw [← Units.val_pow_eq_pow_val, hd5 k]; rfl)
    rw [this, Matrix.diagonal_one]

theorem isElementaryAbelian_torusEq (i j : Fin 5) : IsElementaryAbelian 5 (torusEq i j K) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hV : IsElementaryAbelian 5 (torusVecEq i j K) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (funext fun k => x.2.1 k) }
  exact IsElementaryAbelian.map KFU.diagUHom

theorem apply_eq_of_pow_five_eq_one (σ : K ≃+* K) (hσ : σ ^ 5 = 1) {u : K} (hu : u ^ 5 = 1) :
    σ u = u := by
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf u = 5 := orderOf_eq_prime hu hu1
  have hprim : IsPrimitiveRoot u 5 := IsPrimitiveRoot.iff_orderOf.mpr hord
  have hσu : (σ u) ^ 5 = 1 := by rw [← map_pow, hu, map_one]
  obtain ⟨m, hm5, hm⟩ := hprim.eq_pow_of_pow_eq_one hσu
  have hiter : ∀ n : ℕ, (σ ^ n) u = u ^ (m ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, RingAut.mul_apply, ← hm, map_pow, ih, ← pow_mul, ← pow_succ]
  have h5 : u ^ (m ^ 5) = u ^ 1 := by
    rw [← hiter 5, hσ, pow_one]
    rfl
  have hmod : m ^ 5 % 5 = 1 := by
    have h1 := pow_mod_orderOf u (m ^ 5)
    rw [hord] at h1
    exact hprim.pow_inj (Nat.mod_lt _ (by norm_num)) (by norm_num) (h1.trans h5)
  have hm1 : m = 1 := by
    interval_cases m <;> first | rfl | exact absurd hmod (by decide)
  rw [← hm, hm1, pow_one]

theorem apply_eq_of_mem_torusEq (σ : K ≃+* K) (hσ : σ ^ 5 = 1) {i j : Fin 5} {g : GL (Fin 5) K}
    (hg : g ∈ torusEq i j K) (r s : Fin 5) :
    σ (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) r s) =
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) r s := by
  obtain ⟨d, hd, -, -, rfl⟩ := mem_torusEq_iff.mp hg
  rw [KFU.diagU_val]
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.diagonal_apply_eq]
    exact apply_eq_of_pow_five_eq_one σ hσ (by rw [← Units.val_pow_eq_pow_val, hd r]; rfl)
  · rw [Matrix.diagonal_apply_ne _ hrs, map_zero]

theorem card_torusEq [Finite K] (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {i j : Fin 5}
    (hij : i ≠ j) : Nat.card (torusEq i j K) = 5 ^ 3 := by
  obtain ⟨ζ, hζ⟩ := KFU.exists_isPrimitiveRoot h Nat.prime_five h5
  obtain ⟨z, hz⟩ := hζ.isUnit (by norm_num)
  have hzp : IsPrimitiveRoot z 5 := IsPrimitiveRoot.coe_units_iff.mp (hz ▸ hζ)
  let χ : KFU.torusVec 5 5 K →* Kˣ :=
    { toFun := fun d => (d : Fin 5 → Kˣ) i * ((d : Fin 5 → Kˣ) j)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, Pi.mul_apply, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hT : Nat.card (KFU.torusVec 5 5 K) = 5 ^ 4 :=
    KFU.card_torusVec_eq (by norm_num) ⟨z, hzp⟩ 4
  have hrange : χ.range = rootsOfUnity 5 K := by
    ext u
    rw [MonoidHom.mem_range, mem_rootsOfUnity]
    constructor
    · rintro ⟨d, rfl⟩
      show ((d : Fin 5 → Kˣ) i * ((d : Fin 5 → Kˣ) j)⁻¹) ^ 5 = 1
      rw [mul_pow, inv_pow, d.2.1 i, d.2.1 j, inv_one, mul_one]
    · intro hu
      have hv : (u ^ 3) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]
      refine ⟨⟨KFU.torusElt i j (u ^ 3), KFU.torusElt_mem hij hv⟩, ?_⟩
      show KFU.torusElt i j (u ^ 3) i * (KFU.torusElt i j (u ^ 3) j)⁻¹ = u
      rw [KFU.torusElt_apply_left hij, KFU.torusElt_apply_right hij, inv_inv, ← pow_add,
        show 3 + 3 = 5 + 1 from rfl, pow_succ, hu, one_mul]
  have hrange_card : Nat.card χ.range = 5 := by
    rw [hrange]
    exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hzp)
  have hker : Nat.card χ.ker = 5 ^ 3 := by
    have := Subgroup.card_ker_mul_card_range χ
    rw [hT, hrange_card] at this
    omega
  have hVE : Nat.card (torusVecEq i j K) = Nat.card χ.ker :=
    Nat.card_congr
      { toFun := fun d => ⟨⟨d.1, d.2.1, d.2.2.1⟩, by
          show d.1 i * (d.1 j)⁻¹ = 1
          rw [d.2.2.2, mul_inv_cancel]⟩
        invFun := fun d => ⟨d.1.1, d.1.2.1, d.1.2.2, mul_inv_eq_one.mp d.2⟩
        left_inv := fun d => rfl
        right_inv := fun d => rfl }
  rw [torusEq, Subgroup.card_map_of_injective KFU.diagU_injective, hVE, hker]

theorem swapUnit_mem_unitarySU (h : UnitaryFieldData 2 f K) {i j : Fin 5} :
    KFSU5.swapUnit K i j ∈ unitarySU 2 f K 5 := by
  have : CharP K 2 := h.charP
  rw [mem_unitarySU_iff h, KFSU5.swapUnit_val, KFSU5.det_swapMatrix, KFSU5.swapMatrix_map,
    KFSU5.swapMatrix_transpose, KFSU5.swapMatrix_mul_self]
  exact ⟨rfl, rfl⟩

theorem swapUnit_comm_of_mem_torusEq {i j : Fin 5} {g : GL (Fin 5) K} (hg : g ∈ torusEq i j K) :
    KFSU5.swapUnit K i j * g = g * KFSU5.swapUnit K i j :=
  KFSU5.swapUnit_mul_comm g (isDiag_of_mem_torusEq hg) (entry_eq_of_mem_torusEq hg)

end CFSG.RankThree.PartOne
