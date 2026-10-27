module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.Centralizer
public import CFSG.GroupTheory.NormalizerIndexModEq
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

omit [CharP K 2] in
theorem natCard_torus_two : Nat.card (torus 2 K) = (Nat.card K - 1) ^ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h := Fintype.card_coeSort_range (f := torusHom (r := 2) (k := K)) torusHom_injective
  have h1 : Nat.card (torus 2 K) = Nat.card (Fin 2 → Kˣ) := by
    rw [torus, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact h
  have h2 : Nat.card (Fin 2 → Kˣ) = Nat.card Kˣ ^ Nat.card (Fin 2) := Nat.card_fun
  rw [Nat.card_fin] at h2
  rw [Nat.card_units] at h2
  rw [h1, h2]

theorem odd_natCard_torus_two : Odd (Nat.card (torus 2 K)) := by
  rw [natCard_torus_two]
  have hq : Even (Nat.card K) := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero
      (FiniteField.even_card_of_char_two (ringChar.eq (R := K) 2)))
  obtain ⟨m, hm⟩ := hq
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hm1 : 1 ≤ m := by omega
  have hodd : Odd (Nat.card K - 1) := by
    refine ⟨m - 1, ?_⟩
    omega
  simpa [pow_two] using hodd.mul hodd

omit [CharP K 2] in
theorem natCard_nonzero_vectors_sp4 :
    Nat.card {v : Fin 2 ⊕ Fin 2 → K // v ≠ 0} = Nat.card K ^ 4 - 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : Nat.card {v : Fin 2 ⊕ Fin 2 → K // v ≠ 0} =
      Nat.card (Fin 2 ⊕ Fin 2 → K) - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun v : Fin 2 ⊕ Fin 2 → K => v = 0)]
    simp
  have h2 : Nat.card (Fin 2 ⊕ Fin 2 → K) = Nat.card K ^ 4 := by
    simp only [Nat.card_fun, Nat.card_sum, Nat.card_fin]
  rw [h1, h2]

omit [Finite K] [CharP K 2] in
theorem torusHom_mulVec_single (t : Fin 2 → Kˣ) (j : Fin 2 ⊕ Fin 2) :
    (spMat (torusHom t)) *ᵥ Pi.single j 1 =
      (Sum.elim (fun i => (t i : K)) (fun i => ((t i)⁻¹ : Kˣ)) j) • Pi.single j 1 := by
  rw [coe_torusHom, Matrix.diagonal_mulVec_single]
  ext x
  by_cases hx : x = j <;> simp [hx]

omit [Finite K] [CharP K 2] in
theorem spMat_inv_mulVec_single {z : StatedSp 2 K} {j j' : Fin 2 ⊕ Fin 2} {v : K}
    (hv : v ≠ 0) (hzj : (spMat z) *ᵥ Pi.single j 1 = v • Pi.single j' 1) :
    (spMat z⁻¹) *ᵥ Pi.single j' 1 = v⁻¹ • Pi.single j 1 := by
  have h := congrArg (fun w => (spMat z⁻¹) *ᵥ w) hzj
  rw [Matrix.mulVec_mulVec,
    ← CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.spMat_mul,
    inv_mul_cancel, Matrix.mulVec_smul] at h
  simp only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at h
  have h2 := congrArg (fun w => v⁻¹ • w) h
  simpa [inv_smul_smul₀ hv] using h2.symm

omit [Finite K] [CharP K 2] in
theorem spMat_conj_torusHom_mulVec_single {z : StatedSp 2 K} (t : Fin 2 → Kˣ)
    {j j' : Fin 2 ⊕ Fin 2} {v : K} (hv : v ≠ 0)
    (hzj : (spMat z) *ᵥ Pi.single j 1 = v • Pi.single j' 1) :
    (spMat (z * torusHom t * z⁻¹)) *ᵥ Pi.single j' 1 =
      (Sum.elim (fun i => (t i : K)) (fun i => ((t i)⁻¹ : Kˣ)) j) •
        Pi.single j' 1 := by
  have hzinv := spMat_inv_mulVec_single hv hzj
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.spMat_mul,
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.spMat_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hzinv, Matrix.mulVec_smul, torusHom_mulVec_single, Matrix.mulVec_smul,
    Matrix.mulVec_smul, hzj, smul_smul, smul_smul]
  congr 1
  field_simp

omit [Finite K] [CharP K 2] in
theorem spMat_mulVec_smul_single_ne_zero (x : StatedSp 2 K) (j : Fin 2 ⊕ Fin 2) (u : Kˣ) :
    (spMat x) *ᵥ ((u : K) • Pi.single j 1) ≠ 0 := by
  intro h0
  have h := congrArg (fun w => (spMat x⁻¹) *ᵥ w) h0
  rw [Matrix.mulVec_mulVec,
    ← CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.spMat_mul,
    inv_mul_cancel, Matrix.mulVec_zero] at h
  simp only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at h
  have h2 := congrFun h j
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at h2
  exact u.ne_zero h2

theorem mem_normalizer_torus_of_maps_single (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {z : StatedSp 2 K} (hz : z ∈ X) {j j' : Fin 2 ⊕ Fin 2} {v : K} (hv : v ≠ 0)
    (hzj : (spMat z) *ᵥ Pi.single j 1 = v • Pi.single j' 1) :
    z ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  have hTodd : Odd (Nat.card (torus 2 K)) := odd_natCard_torus_two
  have hmap : (torus 2 K).map (MulAut.conj z).toMonoidHom ≤ torus 2 K := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨t, rfl⟩ := hd
    change z * torusHom t * z⁻¹ ∈ torus 2 K
    have hdX : torusHom t ∈ X := hT ⟨t, rfl⟩
    have hconjX : z * torusHom t * z⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem hz hdX) (X.inv_mem hz)
    have hfix := spMat_conj_torusHom_mulVec_single (z := z) t hv hzj
    have hN : z * torusHom t * z⁻¹ ∈
        Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
      mem_normalizer_torus_of_fixes_single hK hT hX hconjX j' hfix
    have hdvd : orderOf (torusHom t) ∣ Nat.card (torus 2 K) :=
      Subgroup.orderOf_dvd_natCard _ ⟨t, rfl⟩
    have hodd : Odd (orderOf (torusHom t)) := Odd.of_dvd_nat hTodd hdvd
    have hsem : SemiconjBy z (torusHom t) (z * torusHom t * z⁻¹) := by
      show z * torusHom t = z * torusHom t * z⁻¹ * z
      group
    have horder : orderOf (z * torusHom t * z⁻¹) = orderOf (torusHom t) :=
      (SemiconjBy.orderOf_eq z hsem).symm
    exact mem_torus_of_mem_normalizer_of_odd hK hN (by rwa [horder])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hmap
    (by rw [Subgroup.card_map_of_injective (MulAut.conj z).injective])

theorem index_modEq_one (hK : 8 ≤ Nat.card K) {X : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ X) (hX : IsRootFree X) :
    ((Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))).subgroupOf X).index ≡ 1
      [MOD (Nat.card K - 1) ^ 2] := by
  have hTodd : Odd (Nat.card (torus 2 K)) := odd_natCard_torus_two
  have h := CFSG.GroupTheory.index_normalizer_modEq_one hT hTodd ?_ ?_
  · rwa [natCard_torus_two] at h
  · intro m _ hmN hmOdd
    exact mem_torus_of_mem_normalizer_of_odd hK hmN hmOdd
  · intro x hx hne
    exact mem_normalizer_torus_of_inf_ne_bot hK hT hX hx hne

theorem four_mul_index_le (hK : 8 ≤ Nat.card K) {X : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ X) (hX : IsRootFree X) :
    4 * (Nat.card K - 1) *
        ((Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))).subgroupOf X).index ≤
      Nat.card K ^ 4 - 1 := by
  classical
  set N := Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) with hN
  set M : Subgroup ↥X := N.subgroupOf X with hM
  let f : (↥X ⧸ M) × (Fin 2 ⊕ Fin 2) × Kˣ → {v : Fin 2 ⊕ Fin 2 → K // v ≠ 0} :=
    fun p => ⟨(spMat ((p.1.out : ↥X) : StatedSp 2 K)) *ᵥ
        (((p.2.2 : Kˣ) : K) • Pi.single p.2.1 1),
      spMat_mulVec_smul_single_ne_zero _ _ _⟩
  have hinj : Function.Injective f := by
    rintro ⟨c, j, u⟩ ⟨c', j', u'⟩ heq
    have hvec : (spMat ((c.out : ↥X) : StatedSp 2 K)) *ᵥ ((u : K) • Pi.single j 1) =
        (spMat ((c'.out : ↥X) : StatedSp 2 K)) *ᵥ ((u' : K) • Pi.single j' 1) :=
      congrArg Subtype.val heq
    set x : ↥X := c.out with hx
    set y : ↥X := c'.out with hy
    set z : ↥X := y⁻¹ * x with hz
    have hvec' : (spMat (x : StatedSp 2 K)) *ᵥ ((u : K) • Pi.single j 1) =
        (spMat (y : StatedSp 2 K)) *ᵥ ((u' : K) • Pi.single j' 1) := by
      simpa [x, y] using hvec
    have hline : (spMat (z : StatedSp 2 K)) *ᵥ Pi.single j 1 =
        (((u⁻¹ * u' : Kˣ) : K)) • Pi.single j' 1 := by
      have h := congrArg (fun w => (spMat ((y : StatedSp 2 K)⁻¹)) *ᵥ w) hvec'
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.spMat_mul,
        ← CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.spMat_mul,
        inv_mul_cancel] at h
      simp only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at h
      rw [Matrix.mulVec_smul] at h
      have h3 := congrArg (fun w => (u⁻¹ : K) • w) h
      rw [smul_smul, inv_mul_cancel₀ u.ne_zero, one_smul] at h3
      simpa [z, hz, Units.val_mul, Matrix.mulVec_single_one, smul_smul] using h3
    have hv : (((u⁻¹ * u' : Kˣ) : K)) ≠ 0 := (u⁻¹ * u').ne_zero
    have hzX : (z : StatedSp 2 K) ∈ X := z.2
    have hN : (z : StatedSp 2 K) ∈ N :=
      mem_normalizer_torus_of_maps_single hK hT hX hzX hv hline
    have hzM : z ∈ M := by
      rw [hM, Subgroup.mem_subgroupOf]
      exact hN
    have hcc' : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      have h : z⁻¹ ∈ M := M.inv_mem hzM
      simpa [x, y, z, mul_inv_rev] using h
    have hxy : x = y := by
      have h := congrArg Quotient.out hcc'
      simpa [x, y] using h
    have hcancel : (u : K) • Pi.single j 1 = (u' : K) • Pi.single j' 1 := by
      rw [← hxy] at hvec'
      have h := congrArg (fun w => (spMat ((x : StatedSp 2 K)⁻¹)) *ᵥ w) hvec'
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.spMat_mul,
        inv_mul_cancel] at h
      simpa using h
    have hjj' : j = j' := by
      by_contra hne
      have h := congrFun hcancel j
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero] at h
      exact u.ne_zero h
    have huu : u = u' := by
      subst hjj'
      exact Units.ext (by simpa using congrFun hcancel j)
    subst hcc'; subst hjj'; subst huu
    rfl
  have hle := Nat.card_le_card_of_injective f hinj
  have hcard_dom : Nat.card ((↥X ⧸ M) × (Fin 2 ⊕ Fin 2) × Kˣ) =
      4 * (Nat.card K - 1) * M.index := by
    rw [Nat.card_prod, Nat.card_prod, ← Subgroup.index_eq_card]
    simp only [Nat.card_sum, Nat.card_fin, Nat.card_units]
    ring
  have hcard_cod : Nat.card {v : Fin 2 ⊕ Fin 2 → K // v ≠ 0} = Nat.card K ^ 4 - 1 :=
    natCard_nonzero_vectors_sp4
  rw [hcard_dom, hcard_cod] at hle
  simpa [M, mul_assoc, mul_comm, mul_left_comm] using hle

omit [CharP K 2] in
theorem index_dvd {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) :
    ((Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))).subgroupOf X).index ∣
      Nat.card K ^ 4 * (Nat.card K + 1) ^ 2 * (Nat.card K ^ 2 + 1) := by
  classical
  set M : Subgroup ↥X :=
    (Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))).subgroupOf X with hM
  have hTleM : (torus 2 K).subgroupOf X ≤ M := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact Subgroup.le_normalizer ht
  have hTM : Nat.card (torus 2 K) ∣ Nat.card M := by
    have hcard : Nat.card (torus 2 K) = Nat.card ((torus 2 K).subgroupOf X) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv).symm
    rw [hcard]
    exact Subgroup.card_dvd_of_le hTleM
  rw [natCard_torus_two] at hTM
  have hX : Nat.card ↥X ∣ Nat.card (StatedSp 2 K) := Subgroup.card_subgroup_dvd_card X
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two] at hX
  have hidx : M.index * Nat.card M = Nat.card ↥X := Subgroup.index_mul_card M
  have h1 : M.index * (Nat.card K - 1) ^ 2 ∣
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
    calc M.index * (Nat.card K - 1) ^ 2 ∣ M.index * Nat.card M :=
          Nat.mul_dvd_mul_left _ hTM
      _ = Nat.card ↥X := hidx
      _ ∣ Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := hX
  have hq2 : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
    have h := Nat.pow_two_sub_pow_two (Nat.card K) 1
    simpa using h
  have hq4 : Nat.card K ^ 4 - 1 = (Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 - 1) := by
    have h := Nat.pow_two_sub_pow_two (Nat.card K ^ 2) 1
    rw [show Nat.card K ^ 4 = (Nat.card K ^ 2) ^ 2 by ring]
    simpa using h
  have hfac : Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) =
      (Nat.card K ^ 4 * (Nat.card K + 1) ^ 2 * (Nat.card K ^ 2 + 1)) *
        (Nat.card K - 1) ^ 2 := by
    rw [hq4, hq2]
    ring
  rw [hfac] at h1
  have hkpos : 0 < (Nat.card K - 1) ^ 2 := by
    have : Fintype K := Fintype.ofFinite K
    have hq2 : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have : 0 < Nat.card K - 1 := by omega
    positivity
  exact Nat.dvd_of_mul_dvd_mul_right hkpos h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
