module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocksBasic
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.LinearPilot (blockComplProj blockSpecialLinear)

section Conj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem map_conj_unitaryBlock_of_mul_eq {I J : Finset (Fin n)} (g : unitarySU p f K n)
    (hg : blockComplProj J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * blockComplProj I) :
    (unitaryBlock h I).map (MulAut.conj g).toMonoidHom = unitaryBlock h J := by
  have hSL := LinearPilot.map_conj_blockSpecialLinear_of_mul_eq (toSL h n g) hg
  have hconj : ∀ A : unitarySU p f K n, toSL h n ((MulAut.conj g).toMonoidHom A) =
      (MulAut.conj (toSL h n g)).toMonoidHom (toSL h n A) := fun A => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    rw [mem_unitaryBlock_iff_toSL, hconj, ← hSL]
    exact Subgroup.mem_map_of_mem _ hA
  · intro B hB
    rw [mem_unitaryBlock_iff_toSL, ← hSL] at hB
    obtain ⟨A', hA', hA'B⟩ := hB
    refine ⟨g⁻¹ * B * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [SetLike.mem_coe, mem_unitaryBlock_iff_toSL]
    have hA'eq : toSL h n (g⁻¹ * B * g) = A' := by
      rw [map_mul, map_mul, map_inv, ← hA'B]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hA'eq]
    exact hA'

theorem map_conj_blockSU_of_mul_eq {I J : Finset (Fin n)} (g : unitarySU p f K n)
    (hg : blockComplProj J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * blockComplProj I) :
    (blockSU h I).map (MulAut.conj (unitaryProj h n g)).toMonoidHom = blockSU h J := by
  have hcomp : (MulAut.conj (unitaryProj h n g)).toMonoidHom.comp (unitaryProj h n) =
      (unitaryProj h n).comp (MulAut.conj g).toMonoidHom :=
    MonoidHom.ext fun A => by simp [MulAut.conj_apply, map_mul, map_inv]
  rw [blockSU, blockSU, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    map_conj_unitaryBlock_of_mul_eq h g hg]

end Conj

section Monomial

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

include h in
theorem det_permMatrix_eq_one (σ : Equiv.Perm (Fin n)) : (σ.permMatrix K).det = 1 := by
  have := h.charP
  rw [det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simp [hs]
  · simp [hs, CharTwo.neg_eq]

theorem map_permMatrix {p : ℕ} (h : UnitaryFieldData p f K) (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix K).map h.bar = σ.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  split_ifs <;> simp

theorem unitary_permMatrix {p : ℕ} (h : UnitaryFieldData p f K) (σ : Equiv.Perm (Fin n)) :
    ((σ.permMatrix K).map h.bar)ᵀ * σ.permMatrix K = 1 := by
  rw [map_permMatrix h, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

@[expose] def permSU (σ : Equiv.Perm (Fin n)) : unitarySU 2 f K n :=
  ofSL h ⟨σ.permMatrix K, det_permMatrix_eq_one h σ⟩ (unitary_permMatrix h σ)

@[simp]
theorem coe_permSU (σ : Equiv.Perm (Fin n)) :
    (((permSU h σ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      σ.permMatrix K :=
  rfl

theorem blockComplProj_mul_permSU (ρ : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    blockComplProj (I.map ρ.toEmbedding) *
        (((permSU h ρ.symm : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((permSU h ρ.symm : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        blockComplProj I := by
  have hP := LinearPilot.blockComplProj_mul_permMatrix (K := K) ρ.symm I
  rw [Equiv.symm_symm] at hP
  exact hP

theorem map_conj_permSU_unitaryBlock (ρ : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    (unitaryBlock h I).map (MulAut.conj (permSU h ρ.symm)).toMonoidHom =
      unitaryBlock h (I.map ρ.toEmbedding) :=
  map_conj_unitaryBlock_of_mul_eq h _ (blockComplProj_mul_permSU h ρ I)

theorem exists_conj_blockSU (ρ : Equiv.Perm (Fin n)) : ∃ w : unitaryPSU h n,
    ∀ I : Finset (Fin n),
      (blockSU h I).map (MulAut.conj w).toMonoidHom = blockSU h (I.map ρ.toEmbedding) :=
  ⟨unitaryProj h n (permSU h ρ.symm), fun I =>
    map_conj_blockSU_of_mul_eq h _ (blockComplProj_mul_permSU h ρ I)⟩

theorem exists_conj_rootSU2 {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ w : unitaryPSU h n, (rootSU2 h a b).map (MulAut.conj w).toMonoidHom = rootSU2 h c d := by
  obtain ⟨σ, hσa, hσb⟩ := LinearPilot.exists_perm_apply_eq_apply_eq hab hcd
  obtain ⟨w, hw⟩ := exists_conj_blockSU h σ
  refine ⟨w, ?_⟩
  rw [rootSU2, hw, rootSU2, Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding, hσa,
    hσb]

end Monomial

section Quasisimple

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

include h in
theorem isQuasisimple_unitarySU {m : ℕ} (hm : 3 ≤ m) (hmq : (m, p ^ f) ≠ (3, 2)) :
    CFSG.IsQuasisimple (unitarySU p f K m) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card h.card_eq_sq hm hmq).1

theorem isQuasisimple_blockSU_of_three_le {I : Finset (Fin n)} (hI3 : 3 ≤ I.card)
    (hIq : (I.card, p ^ f) ≠ (3, 2)) (hIn : I.card < n) : CFSG.IsQuasisimple (blockSU h I) :=
  CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv (blockSUEquiv h hIn)
    (isQuasisimple_unitarySU h hI3 hIq)

theorem isQuasisimple_blockSU {I : Finset (Fin n)} (hI4 : 4 ≤ I.card) (hIn : I.card < n) :
    CFSG.IsQuasisimple (blockSU h I) :=
  isQuasisimple_blockSU_of_three_le h (by omega)
    (fun h3 => by have := congrArg Prod.fst h3; simp only at this; omega) hIn

omit [Field K] in
theorem card_compl_pair {a b : Fin n} (hab : a ≠ b) :
    ({a, b}ᶜ : Finset (Fin n)).card = n - 2 := by
  rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]

theorem blockSU_compl_pair_mulEquiv {a b : Fin n} (hab : a ≠ b) :
    Nonempty (blockSU h ({a, b}ᶜ : Finset (Fin n)) ≃* unitarySU p f K (n - 2)) := by
  have hn2 : 2 ≤ n := by
    have := Finset.card_le_univ ({a, b} : Finset (Fin n))
    rw [Finset.card_pair hab, Fintype.card_fin] at this
    exact this
  obtain ⟨e⟩ := blockSU_mulEquiv h ({a, b}ᶜ : Finset (Fin n))
    (by rw [card_compl_pair hab]; omega)
  rw [card_compl_pair hab] at e
  exact ⟨e⟩

theorem isQuasisimple_blockSU_compl_pair (hn : 6 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    CFSG.IsQuasisimple (blockSU h ({a, b}ᶜ : Finset (Fin n))) :=
  isQuasisimple_blockSU h (by rw [card_compl_pair hab]; omega)
    (by rw [card_compl_pair hab]; omega)

end Quasisimple

section Diagonal

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m : ℕ}

theorem unitary_diagonal {d : Fin m → K} (hd : ∀ k, h.norm (d k) = 1) :
    ((diagonal d).map h.bar)ᵀ * diagonal d = 1 := by
  rw [diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  have hk := hd k
  rwa [UnitaryFieldData.norm, mul_comm] at hk

@[expose] def diagSU (d : Fin m → K) (hd : ∀ k, h.norm (d k) = 1) (hdet : ∏ k, d k = 1) :
    unitarySU p f K m :=
  ofSL h ⟨diagonal d, by rw [det_diagonal]; exact hdet⟩ (unitary_diagonal h hd)

@[simp]
theorem coe_diagSU (d : Fin m → K) (hd : ∀ k, h.norm (d k) = 1) (hdet : ∏ k, d k = 1) :
    (((diagSU h d hd hdet : unitarySU p f K m) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      diagonal d :=
  rfl

theorem diagSU_mem_unitaryBlock {I : Finset (Fin m)} (d : Fin m → K)
    (hd : ∀ k, h.norm (d k) = 1) (hdet : ∏ k, d k = 1) (hdI : ∀ k ∉ I, d k = 1) :
    diagSU h d hd hdet ∈ unitaryBlock h I := by
  intro i j hij
  change diagonal d i j = (1 : Matrix (Fin m) (Fin m) K) i j
  by_cases e : i = j
  · subst e
    rw [diagonal_apply_eq, one_apply_eq]
    exact hdI i (hij.elim id id)
  · rw [diagonal_apply_ne _ e, one_apply_ne e]

theorem norm_eq_one_of_unitary_scalar (hm : 0 < m) {c : K}
    (hu : ((scalar (Fin m) c).map h.bar)ᵀ * scalar (Fin m) c = 1) : h.norm c = 1 := by
  rw [scalar_apply, diagonal_map (map_zero h.bar), diagonal_transpose,
    diagonal_mul_diagonal] at hu
  have h00 := congrFun (congrFun hu ⟨0, hm⟩) ⟨0, hm⟩
  rw [diagonal_apply_eq, one_apply_eq] at h00
  rwa [UnitaryFieldData.norm, mul_comm]

theorem exists_norm_eq_one_ne_one : ∃ κ : Kˣ, h.norm (κ : K) = 1 ∧ κ ≠ 1 := by
  have := h.finite
  have hcard := h.card_ker_normUnits_and_surjective.1
  have hnt : Nontrivial (Units.map h.normHom).ker := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    have := h.one_lt_pow
    omega
  obtain ⟨κ, hκ⟩ := exists_ne (1 : (Units.map h.normHom).ker)
  exact ⟨κ, h.mem_ker_normUnits.1 κ.2, fun h1 => hκ (Subtype.ext h1)⟩

end Diagonal

section Center

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem coe_ne_coe_inv_of_ne_one {κ : Kˣ} (hκ : κ ≠ 1) : (κ : K) ≠ ((κ⁻¹ : Kˣ) : K) := by
  have := h.charP
  intro heq
  apply hκ
  have h2 : (κ : K) ^ 2 = 1 ^ 2 := by
    rw [one_pow, sq]
    nth_rewrite 2 [heq]
    exact Units.mul_inv κ
  exact Units.ext ((CharTwo.sq_inj).1 h2)

theorem center_unitarySU_le_unitaryScalars (m : ℕ) :
    Subgroup.center (unitarySU 2 f K m) ≤ unitaryScalars h m := by
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  rw [mem_unitaryScalars]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, by simp [UnitaryFieldData.norm], pow_zero _,
      Units.ext (Matrix.ext fun i _ => Fin.elim0 i)⟩
  set Z := ((z : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) with hZ
  have hoff : ∀ i j, i ≠ j → Z i j = 0 := by
    intro i j hij
    obtain ⟨κ, hκN, hκ1⟩ := exists_norm_eq_one_ne_one h
    have hκ := coe_ne_coe_inv_of_ne_one h hκ1
    have hκN' : h.norm ((κ⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hκN, inv_one]
    set d : Fin m → K := Pi.mulSingle i (κ : K) * Pi.mulSingle j ((κ⁻¹ : Kˣ) : K) with hd
    have hdN : ∀ k, h.norm (d k) = 1 := by
      intro k
      have h1 : h.norm 1 = 1 := by simp [UnitaryFieldData.norm]
      rw [hd, Pi.mul_apply, norm_mul_eq h, Pi.mulSingle_apply, Pi.mulSingle_apply]
      split_ifs
      · rw [hκN, hκN', one_mul]
      · rw [hκN, h1, one_mul]
      · rw [h1, hκN', one_mul]
      · rw [h1, one_mul]
    have hdprod : ∏ k, d k = 1 := by
      rw [hd]
      simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle',
        ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), Units.mul_inv]
    have hcomm := hz (diagSU h d hdN hdprod)
    have hij' := congrArg
      (fun g : unitarySU 2 f K m => ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) i j) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul, coe_diagSU, diagonal_mul, mul_diagonal] at hij'
    have hdi : d i = κ := by simp [hd, hij]
    have hdj : d j = ((κ⁻¹ : Kˣ) : K) := by simp [hd, Ne.symm hij]
    rw [hdi, hdj] at hij'
    have hzero : Z i j * ((κ : K) - ((κ⁻¹ : Kˣ) : K)) = 0 := by
      rw [mul_sub, mul_comm, hij', sub_self]
    rcases mul_eq_zero.1 hzero with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.1 h0) hκ
  have hdiag : ∀ i j, Z i i = Z j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have hcomm := hz (permSU h (Equiv.swap i j))
    have hij' := congrArg
      (fun g : unitarySU 2 f K m => ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) i j) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul, coe_permSU, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, id,
      Equiv.swap_apply_left, Equiv.symm_swap, Equiv.swap_apply_right] at hij'
    exact hij'.symm
  set i₀ : Fin m := ⟨0, hm⟩
  have hZscalar : Z = scalar (Fin m) (Z i₀ i₀) := by
    ext i j
    rw [scalar_apply, diagonal_apply]
    split_ifs with hij
    · rw [hij]
      exact hdiag j i₀
    · exact hoff i j hij
  have hdet : Z i₀ i₀ ^ m = 1 := by
    have hd1 := ((mem_unitarySU_iff h).1 z.2).1
    rw [← hZ, hZscalar, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hd1
    exact hd1
  have hc0 : Z i₀ i₀ ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by omega)] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk0 _ hc0, ?_, Units.ext (by simpa using hdet), Units.ext ?_⟩
  · have hu := ((mem_unitarySU_iff h).1 z.2).2
    rw [← hZ, hZscalar] at hu
    rw [Units.val_mk0]
    exact norm_eq_one_of_unitary_scalar h hm hu
  · rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, ← hZscalar]

include h in
theorem odd_card_center_unitarySU (m : ℕ) :
    Odd (Nat.card (Subgroup.center (unitarySU 2 f K m))) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : Subsingleton (Subgroup.center (unitarySU 2 f K 0)) :=
      ⟨fun x y => Subtype.ext (Subtype.ext (Units.ext (Matrix.ext fun i _ => Fin.elim0 i)))⟩
    rw [Nat.card_of_subsingleton (1 : Subgroup.center (unitarySU 2 f K 0))]
    exact odd_one
  · have hdvd := Subgroup.card_dvd_of_le (center_unitarySU_le_unitaryScalars h m)
    rw [card_unitaryScalars h hm] at hdvd
    have hodd : Odd (2 ^ f + 1) :=
      (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩).add_one
    exact hodd.of_dvd_nat (hdvd.trans (Nat.gcd_dvd_right _ _))

theorem odd_card_center_blockSU {n : ℕ} {I : Finset (Fin n)} (hIn : I.card < n) :
    Odd (Nat.card (Subgroup.center (blockSU h I))) := by
  rw [← Nat.card_congr (Subgroup.centerCongr (blockSUEquiv h hIn)).toEquiv]
  exact odd_card_center_unitarySU h I.card

theorem center_unitarySU_eq_unitaryScalars (m : ℕ) :
    Subgroup.center (unitarySU 2 f K m) = unitaryScalars h m :=
  le_antisymm (center_unitarySU_le_unitaryScalars h m) (unitaryScalars_le_center h m)

@[expose] noncomputable def blockSUQuotientCenterEquiv {n : ℕ} {I : Finset (Fin n)}
    (hIn : I.card < n) :
    blockSU h I ⧸ Subgroup.center (blockSU h I) ≃* unitaryPSU h I.card :=
  QuotientGroup.congr _ _ (blockSUEquiv h hIn).symm
    ((CFSG.LieType.Universal.Unitary.map_center_mulEquiv (blockSUEquiv h hIn).symm).trans
      (center_unitarySU_eq_unitaryScalars h I.card))

end Center

section PSL

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem unitaryScalars_le_comap_scalars :
    unitaryScalars h n ≤ (LinearFlag.scalars n K).comap (toSL h n) := by
  rintro z ⟨c, -, hcn, hz⟩
  exact ⟨c, hcn, by rw [coe_toSL, hz, GeneralLinearGroup.coe_scalar]⟩

variable (n) in
@[expose] def toPSL : unitaryPSU h n →* LinearFlag.projectiveSL n K :=
  QuotientGroup.map _ _ (toSL h n) (unitaryScalars_le_comap_scalars h)

@[simp]
theorem toPSL_unitaryProj (A : unitarySU p f K n) :
    toPSL h n (unitaryProj h n A) = LinearFlag.proj n K (toSL h n A) :=
  rfl

theorem toPSL_injective : Function.Injective (toPSL h n) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨A, rfl⟩ := unitaryProj_surjective h n x
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hA : A = 1 := Subtype.ext (Units.ext (Matrix.ext fun i _ => Fin.elim0 i))
    rw [hA, map_one]
  rw [toPSL_unitaryProj, LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at hx
  obtain ⟨c, -, hc⟩ := hx
  have hA : A ∈ unitaryScalars h n := by
    rw [unitaryScalars_eq h hn, Subgroup.mem_subgroupOf]
    exact ⟨c, Units.ext (by rw [GeneralLinearGroup.coe_scalar, ← hc, coe_toSL])⟩
  rw [← MonoidHom.mem_ker, ker_unitaryProj]
  exact hA

theorem map_blockSU_le_blockSL (I : Finset (Fin n)) :
    (blockSU h I).map (toPSL h n) ≤ LinearPilot.blockSL I := by
  rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  exact LinearPilot.proj_mem_blockSL hA

end PSL

end CFSG.SeitzReduction.UnitaryPilot
