module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoPair
public import CFSG.ClassicalGroups.Unitary.Transitivity
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] {n : ℕ}

private theorem s16k_fin_ne {n i j : ℕ} (hi : i < n) (hj : j < n) (h : i ≠ j) :
    (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun e => h (Fin.mk.inj_iff.1 e)

private theorem s16k_prod_update₂ {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (c d : K) :
    ∏ k, Function.update (Function.update (1 : ι → K) i c) j d k = c * d := by
  classical
  rw [Finset.prod_update_of_mem (s := Finset.univ) (i := j)
    (f := Function.update (1 : ι → K) i c) (b := d) (Finset.mem_univ j)]
  rw [Finset.prod_update_of_mem (s := Finset.univ \ {j}) (i := i)
    (f := (1 : ι → K)) (b := c) (by simpa using hij)]
  simp [mul_comm]

private noncomputable def s16k_diagGL (a : Fin n → K) (ha : ∀ i, a i ≠ 0) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal a)
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i)

private theorem s16k_diagGL_val (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    ((s16k_diagGL a ha : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal a :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private def s16k_stabVec (u : Fin n → K) : Subgroup (GL (Fin n) K) where
  carrier := {b | (b : Matrix (Fin n) (Fin n) K) *ᵥ u = u}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change ((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u
    have h1 : ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rwa [ha] at h1

private theorem s16k_diagGL_mulVec_single {a : Fin n → K} (ha : ∀ i, a i ≠ 0) {j : Fin n}
    (haj : a j = 1) :
    ((s16k_diagGL a ha : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 =
      Pi.single j 1 := by
  rw [s16k_diagGL_val, Matrix.diagonal_mulVec_single, haj, one_mul]

private theorem s16k_diagGL_mulVec_add_single {a : Fin n → K} (ha : ∀ i, a i ≠ 0)
    {j k : Fin n} (haj : a j = 1) (hak : a k = 1) :
    ((s16k_diagGL a ha : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (Pi.single j 1 + Pi.single k 1) = Pi.single j 1 + Pi.single k 1 := by
  rw [Matrix.mulVec_add, s16k_diagGL_mulVec_single ha haj, s16k_diagGL_mulVec_single ha hak]

private theorem s16k_pow_three_eq_one (hK : Nat.card K = 4) (c : K) (hc : c ≠ 0) :
    c ^ 3 = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one c hc
  rw [← Nat.card_eq_fintype_card, hK] at h
  simpa using h

section Unitary

variable [Fact (Nat.Prime 2)] [CharP K 2]

private theorem s16k_sigma_mul_self (hK : Nat.card K = 4) (c : K) (hc : c ≠ 0) :
    unitaryInvolution K 2 1 c * c = 1 := by
  rw [unitaryInvolution_apply, pow_one, ← pow_succ]
  exact s16k_pow_three_eq_one hK c hc

private theorem s16k_sigma_fixed_eq_zero_or_one (hK : Nat.card K = 4) (x : K)
    (hx : unitaryInvolution K 2 1 x = x) : x = 0 ∨ x = 1 := by
  have hx2 : x ^ 2 = x := by
    rw [unitaryInvolution_apply, pow_one] at hx
    exact hx
  rcases mul_eq_zero.mp (show x * (x - 1) = 0 by
    rw [mul_sub, mul_one, ← pow_two, hx2, sub_self]) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private theorem s16k_herm_self_eq_zero_or_one (hK : Nat.card K = 4) (a : Fin n → K) :
    herm (unitaryInvolution K 2 1) a a = 0 ∨ herm (unitaryInvolution K 2 1) a a = 1 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  exact s16k_sigma_fixed_eq_zero_or_one hK _
    (herm_self_fixed (unitaryInvolution K 2 1)
      (unitaryInvolution_involutive (p := 2) (f := 1) hF) a)

private theorem s16k_herm_single_self {i : Fin n} :
    herm (unitaryInvolution K 2 1) (Pi.single i 1) (Pi.single i 1) = 1 := by
  rw [herm_single_left, map_one, one_mul, Pi.single_eq_same]

private theorem s16k_herm_single_add_self {i j : Fin n} (hij : i ≠ j) :
    herm (unitaryInvolution K 2 1) (Pi.single i 1 + Pi.single j 1)
      (Pi.single i 1 + Pi.single j 1) = 0 := by
  rw [herm_add_left, herm_add_right, herm_add_right]
  rw [herm_single_left, herm_single_left, herm_single_left, herm_single_left]
  rw [map_one, one_mul]
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij 1, Pi.single_eq_of_ne (Ne.symm hij) 1,
    Pi.single_eq_same]
  simp [CharTwo.add_self_eq_zero]

private theorem s16k_diagGL_mem_SUid {a : Fin n → K} (ha : ∀ i, a i ≠ 0)
    (hnorm : ∀ i, unitaryInvolution K 2 1 (a i) * a i = 1) (hprod : ∏ i, a i = 1) :
    s16k_diagGL a ha ∈ SUid (unitaryInvolution K 2 1) n := by
  rw [mem_SUid_iff]
  refine ⟨?_, ?_⟩
  · rw [s16k_diagGL_val, Matrix.det_diagonal]; exact hprod
  · intro x y
    rw [s16k_diagGL_val]
    have hx : Matrix.diagonal a *ᵥ x = fun i => a i * x i := by
      funext i; rw [Matrix.mulVec_diagonal]
    have hy : Matrix.diagonal a *ᵥ y = fun i => a i * y i := by
      funext i; rw [Matrix.mulVec_diagonal]
    rw [hx, hy]
    simp only [herm, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hkey : unitaryInvolution K 2 1 (a i) * unitaryInvolution K 2 1 (x i) * (a i * y i) =
        (unitaryInvolution K 2 1 (a i) * a i) *
          (unitaryInvolution K 2 1 (x i) * y i) := by
      ring
    rw [hkey, hnorm i, one_mul]

end Unitary

theorem s16k_fixNc_statedSU_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {n : ℕ} (hn : 5 ≤ n) : FixNc (StatedSU n 2 K) 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2)
      (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) hF
  have heq : SUid (unitaryInvolution K 2 1) n = StatedSU n 2 K :=
    SUid_eq_statedSU (p := 2) (f := 1) hF n
  rw [← heq]
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  have h2n : 2 < n := by omega
  have h3n : 3 < n := by omega
  have h4n : 4 < n := by omega
  let i0 : Fin n := ⟨0, h0n⟩
  let i1 : Fin n := ⟨1, h1n⟩
  let i2 : Fin n := ⟨2, h2n⟩
  let i3 : Fin n := ⟨3, h3n⟩
  let i4 : Fin n := ⟨4, h4n⟩
  have h01 : i0 ≠ i1 := s16k_fin_ne h0n h1n (by omega)
  have h02 : i0 ≠ i2 := s16k_fin_ne h0n h2n (by omega)
  have h03 : i0 ≠ i3 := s16k_fin_ne h0n h3n (by omega)
  have h04 : i0 ≠ i4 := s16k_fin_ne h0n h4n (by omega)
  have h12 : i1 ≠ i2 := s16k_fin_ne h1n h2n (by omega)
  have h13 : i1 ≠ i3 := s16k_fin_ne h1n h3n (by omega)
  have h14 : i1 ≠ i4 := s16k_fin_ne h1n h4n (by omega)
  have h23 : i2 ≠ i3 := s16k_fin_ne h2n h3n (by omega)
  have h24 : i2 ≠ i4 := s16k_fin_ne h2n h4n (by omega)
  have h34 : i3 ≠ i4 := s16k_fin_ne h3n h4n (by omega)
  have h43 : i4 ≠ i3 := h34.symm
  have h42 : i4 ≠ i2 := h24.symm
  have h32 : i3 ≠ i2 := h23.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hgord : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcu]
  set ω : K := (g : K) with hωdef
  have hω3 : ω ^ 3 = 1 := by
    rw [hωdef, ← Units.val_pow_eq_pow_val, ← hgord, pow_orderOf_eq_one, Units.val_one]
  have hω0 : ω ≠ 0 := by rw [hωdef]; exact g.ne_zero
  have hω1 : ω ≠ 1 := by
    intro h
    have h1 : g = 1 := Units.ext (by rw [← hωdef]; exact h)
    rw [h1, orderOf_one] at hgord
    omega
  have hωinv1 : ω⁻¹ ≠ 1 := fun h => hω1 (inv_eq_one.mp h)
  let ax : Fin n → K := Function.update (Function.update (1 : Fin n → K) i2 ω) i3 ω⁻¹
  let ay : Fin n → K := Function.update (Function.update (1 : Fin n → K) i2 ω) i4 ω⁻¹
  have hax_i2 : ax i2 = ω := by
    dsimp only [ax]
    rw [Function.update_apply, if_neg h23, Function.update_apply, if_pos rfl]
  have hax_i3 : ax i3 = ω⁻¹ := by
    dsimp only [ax]; rw [Function.update_apply, if_pos rfl]
  have hax_i4 : ax i4 = 1 := by
    dsimp only [ax]; rw [Function.update_apply, if_neg h43, Function.update_apply, if_neg h42]
    rfl
  have hax_i0 : ax i0 = 1 := by
    dsimp only [ax]; rw [Function.update_apply, if_neg h03, Function.update_apply, if_neg h02]
    rfl
  have hax_i1 : ax i1 = 1 := by
    dsimp only [ax]; rw [Function.update_apply, if_neg h13, Function.update_apply, if_neg h12]
    rfl
  have hay_i2 : ay i2 = ω := by
    dsimp only [ay]
    rw [Function.update_apply, if_neg h24, Function.update_apply, if_pos rfl]
  have hay_i4 : ay i4 = ω⁻¹ := by
    dsimp only [ay]; rw [Function.update_apply, if_pos rfl]
  have hay_i3 : ay i3 = 1 := by
    dsimp only [ay]; rw [Function.update_apply, if_neg h34, Function.update_apply, if_neg h32]
    rfl
  have hay_i0 : ay i0 = 1 := by
    dsimp only [ay]; rw [Function.update_apply, if_neg h04, Function.update_apply, if_neg h02]
    rfl
  have hay_i1 : ay i1 = 1 := by
    dsimp only [ay]; rw [Function.update_apply, if_neg h14, Function.update_apply, if_neg h12]
    rfl
  have hax0 : ∀ i, ax i ≠ 0 := by
    intro i
    dsimp only [ax]
    rw [Function.update_apply, Function.update_apply]
    split_ifs with h3 h2
    · exact inv_ne_zero hω0
    · exact hω0
    · exact one_ne_zero
  have hay0 : ∀ i, ay i ≠ 0 := by
    intro i
    dsimp only [ay]
    rw [Function.update_apply, Function.update_apply]
    split_ifs with h4 h2
    · exact inv_ne_zero hω0
    · exact hω0
    · exact one_ne_zero
  have haxn : ∀ i, unitaryInvolution K 2 1 (ax i) * ax i = 1 := by
    intro i
    dsimp only [ax]
    rw [Function.update_apply, Function.update_apply]
    split_ifs with h3 h2
    · exact s16k_sigma_mul_self hK ω⁻¹ (inv_ne_zero hω0)
    · exact s16k_sigma_mul_self hK ω hω0
    · simp
  have hayn : ∀ i, unitaryInvolution K 2 1 (ay i) * ay i = 1 := by
    intro i
    dsimp only [ay]
    rw [Function.update_apply, Function.update_apply]
    split_ifs with h4 h2
    · exact s16k_sigma_mul_self hK ω⁻¹ (inv_ne_zero hω0)
    · exact s16k_sigma_mul_self hK ω hω0
    · simp
  have hax_prod : ∏ i, ax i = 1 := by
    show (∏ i, Function.update (Function.update (1 : Fin n → K) i2 ω) i3 ω⁻¹ i) = 1
    rw [s16k_prod_update₂ h23 ω ω⁻¹, mul_inv_cancel₀ hω0]
  have hay_prod : ∏ i, ay i = 1 := by
    show (∏ i, Function.update (Function.update (1 : Fin n → K) i2 ω) i4 ω⁻¹ i) = 1
    rw [s16k_prod_update₂ h24 ω ω⁻¹, mul_inv_cancel₀ hω0]
  have hax_cube : ∀ i, ax i ^ 3 = 1 := by
    intro i
    dsimp only [ax]
    rw [Function.update_apply, Function.update_apply]
    split_ifs with h3 h2
    · rw [inv_pow, hω3, inv_one]
    · exact hω3
    · simp
  have hay_cube : ∀ i, ay i ^ 3 = 1 := by
    intro i
    dsimp only [ay]
    rw [Function.update_apply, Function.update_apply]
    split_ifs with h4 h2
    · rw [inv_pow, hω3, inv_one]
    · exact hω3
    · simp
  let x : GL (Fin n) K := s16k_diagGL ax hax0
  let y : GL (Fin n) K := s16k_diagGL ay hay0
  have hxSU : x ∈ SUid (unitaryInvolution K 2 1) n := s16k_diagGL_mem_SUid hax0 haxn hax_prod
  have hySU : y ∈ SUid (unitaryInvolution K 2 1) n := s16k_diagGL_mem_SUid hay0 hayn hay_prod
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by
    apply Units.ext
    have hcube : (ax ^ 3) = (fun _ => (1 : K)) := by
      funext i; rw [Pi.pow_apply, hax_cube i]
    rw [Units.val_pow_eq_pow_val, s16k_diagGL_val, Matrix.diagonal_pow, hcube]
    simp [Matrix.diagonal_one]
  have hy3 : y ^ 3 = 1 := by
    apply Units.ext
    have hcube : (ay ^ 3) = (fun _ => (1 : K)) := by
      funext i; rw [Pi.pow_apply, hay_cube i]
    rw [Units.val_pow_eq_pow_val, s16k_diagGL_val, Matrix.diagonal_pow, hcube]
    simp [Matrix.diagonal_one]
  have hx1 : x ≠ 1 := by
    intro h
    have hmat : ax i2 = 1 := by
      have h1 := congrArg (fun gg : GL (Fin n) K =>
        (gg : Matrix (Fin n) (Fin n) K) i2 i2) h
      rw [s16k_diagGL_val, Matrix.diagonal_apply_eq] at h1
      simpa using h1
    rw [hax_i2] at hmat
    exact hω1 hmat
  have hy1 : y ≠ 1 := by
    intro h
    have hmat : ay i2 = 1 := by
      have h1 := congrArg (fun gg : GL (Fin n) K =>
        (gg : Matrix (Fin n) (Fin n) K) i2 i2) h
      rw [s16k_diagGL_val, Matrix.diagonal_apply_eq] at h1
      simpa using h1
    rw [hay_i2] at hmat
    exact hω1 hmat
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hxy : Commute x y := by
    show (s16k_diagGL ax hax0) * (s16k_diagGL ay hay0) =
      (s16k_diagGL ay hay0) * (s16k_diagGL ax hax0)
    apply Units.ext
    simp only [Units.val_mul, s16k_diagGL_val, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (mul_comm ax ay)
  have hyx : y ∉ Subgroup.zpowers x := by
    have hxstab : x ∈ s16k_stabVec (Pi.single i4 1) :=
      s16k_diagGL_mulVec_single hax0 hax_i4
    have hyle : y ∉ s16k_stabVec (Pi.single i4 1) := by
      intro hy
      change ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i4 1 =
        Pi.single i4 1 at hy
      rw [s16k_diagGL_val, Matrix.diagonal_mulVec_single, hay_i4, mul_one] at hy
      have h2 := congrFun hy i4
      simp only [Pi.single_eq_same] at h2
      exact hωinv1 h2
    intro hmem
    exact hyle ((Subgroup.zpowers_le.mpr hxstab) hmem)
  let B : Subgroup (GL (Fin n) K) := Subgroup.zpowers x ⊔ Subgroup.zpowers y
  obtain ⟨hBcard, hBexp⟩ := s16g_card_pair_subgroup Nat.prime_three hxy hxord hyord hyx
  have hBΓ : B ≤ SUid (unitaryInvolution K 2 1) n :=
    sup_le (Subgroup.zpowers_le.mpr hxSU) (Subgroup.zpowers_le.mpr hySU)
  let e0 : Fin n → K := Pi.single i0 1
  let e1 : Fin n → K := Pi.single i1 1
  let w : Fin 2 → Fin n → K := fun k => if k = 0 then e0 else e0 + e1
  have hw0 : w 0 = e0 := by simp [w]
  have hw1 : w 1 = e0 + e1 := by
    simp only [w]
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
  have hw : ∀ k, ∀ b ∈ B, (b : Matrix (Fin n) (Fin n) K) *ᵥ w k = w k := by
    intro k
    by_cases hk : k = 0
    · rw [show w k = e0 by simp [w, hk]]
      exact s16g_fixed_of_pair (s16k_diagGL_mulVec_single hax0 hax_i0)
        (s16k_diagGL_mulVec_single hay0 hay_i0)
    · rw [show w k = e0 + e1 by simp [w, hk]]
      exact s16g_fixed_of_pair (s16k_diagGL_mulVec_add_single hax0 hax_i0 hax_i1)
        (s16k_diagGL_mulVec_add_single hay0 hay_i0 hay_i1)
  have hconj : ∀ a : Fin n → K, a ≠ 0 → ∃ k, ∃ A ∈ SUid (unitaryInvolution K 2 1) n,
      (A : Matrix (Fin n) (Fin n) K) *ᵥ w k = a := by
    intro a ha
    rcases s16k_herm_self_eq_zero_or_one hK a with h0 | h1
    · have hrep0 : e0 + e1 ≠ 0 := by
        intro h
        have h' := congrFun h i0
        simp only [Pi.add_apply, Pi.zero_apply, e0, e1, Pi.single_eq_same,
          Pi.single_eq_of_ne h01, add_zero] at h'
        exact one_ne_zero h'
      have hrepiso : herm (unitaryInvolution K 2 1) (e0 + e1) (e0 + e1) = 0 := by
        have hcoe : e0 + e1 = Pi.single i0 1 + Pi.single i1 1 := by simp [e0, e1]
        rw [hcoe]; exact s16k_herm_single_add_self h01
      obtain ⟨t, _ht, htsmul⟩ :=
        exists_mem_T_smul_eq_of_iso hσ (by omega : 3 ≤ n) hrep0 hrepiso ha h0
      exact ⟨1, (t : GL (Fin n) K), t.2, by rw [hw1]; exact htsmul⟩
    · have hrepnorm : herm (unitaryInvolution K 2 1) e0 e0 = 1 :=
        s16k_herm_single_self
      obtain ⟨t, _ht, htsmul⟩ :=
        exists_mem_T_smul_eq_of_norm_one hσ (Or.inl (by omega : 4 ≤ n)) hrepnorm h1
      exact ⟨0, (t : GL (Fin n) K), t.2, by rw [hw0]; exact htsmul⟩
  exact s16g_fixNc_of_conj (SUid (unitaryInvolution K 2 1) n) Nat.prime_three B hBΓ hBcard
    hBexp w hw hconj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
