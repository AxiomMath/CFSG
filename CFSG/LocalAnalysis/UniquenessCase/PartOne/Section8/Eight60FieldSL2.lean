module

public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.SectionRank.OddCover.CubicCyclic
import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix
open CFSG.Open (StatedSL)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Open.StatedAPI (mem_statedSL_iff)
open scoped Pointwise
open CFSG.SectionRank.OddCover (isCyclic_of_isPGroup_of_card_eq_mul exists_isCyclic_card_GL)

private def sl2DiagHom (K : Type) [Field K] : Kˣ →* StatedSL 2 K where
  toFun u := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K)])
      (by rw [Matrix.det_diagonal, Fin.prod_univ_two]; simp),
    mem_statedSL_iff.mpr (by
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_diagonal, Fin.prod_univ_two]
      simp)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.mul_apply, Units.val_mul, mul_comm]

private theorem sl2DiagHom_injective (K : Type) [Field K] :
    Function.Injective (sl2DiagHom K) := by
  intro u v huv
  have h := congrArg (fun x : StatedSL 2 K =>
    ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) huv
  apply Units.ext
  simpa [sl2DiagHom, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.diagonal] using h

private theorem isCyclic_of_isPGroup_three_statedSL_two {K : Type} [Field K] [Finite K]
    (h3q : ¬ 3 ∣ Nat.card K)
    (R : Subgroup (StatedSL 2 K)) (hR : IsPGroup 3 R) : IsCyclic R := by
  have hfact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hsplit : 3 ∣ Nat.card K - 1
  · have hTcard : Nat.card (sl2DiagHom K).range = Nat.card K - 1 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective (sl2DiagHom_injective K)).toEquiv]
      simp [Nat.card_units]
    have hcycT : IsCyclic (sl2DiagHom K).range :=
      isCyclic_of_surjective _ (sl2DiagHom K).rangeRestrict_surjective
    refine isCyclic_of_isPGroup_of_card_eq_mul (Z := (sl2DiagHom K).range)
      (m := Nat.card K * (Nat.card K + 1)) ?_ ?_ hR
    · rw [CFSG.Open.StatedAPI.card_statedSL_two, hTcard]
      have hq : 1 ≤ Nat.card K := Nat.card_pos
      zify [hq, Nat.one_le_pow 2 (Nat.card K) hq]
      ring
    · intro h
      have hp : ¬ 3 ∣ Nat.card K + 1 := by
        intro hqp1
        have h2 : 3 ∣ 2 := by
          have hs := Nat.dvd_sub hqp1 hsplit
          have heq : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
          rwa [heq] at hs
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      exact Nat.Prime.not_dvd_mul Nat.prime_three h3q hp h
  · have hGL : IsCyclic (R.map (StatedSL 2 K).subtype) := by
      have hR' : IsPGroup 3 (R.map (StatedSL 2 K).subtype) := hR.map _
      obtain ⟨S, hScyc, hScard⟩ := exists_isCyclic_card_GL K 2
      have hcycS : IsCyclic S := hScyc
      refine isCyclic_of_isPGroup_of_card_eq_mul (Z := S)
        (m := Nat.card K ^ 2 - Nat.card K) ?_ ?_ hR'
      · let hF : Fintype K := Fintype.ofFinite K
        rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hScard]
        simp
      · intro h
        have h' : 3 ∣ Nat.card K * (Nat.card K - 1) := by
          have hq : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
            rw [Nat.mul_sub_one, sq]
          rwa [hq] at h
        exact Nat.Prime.not_dvd_mul Nat.prime_three h3q hsplit h'
    exact (R.equivMapOfInjective (StatedSL 2 K).subtype Subtype.coe_injective).isCyclic.2 hGL

private theorem map_mem_statedSL_two {K : Type} [Field K] (φ : K →+* K) {g : GL (Fin 2) K}
    (hg : g ∈ StatedSL 2 K) : Matrix.GeneralLinearGroup.map φ g ∈ StatedSL 2 K := by
  rw [mem_statedSL_iff] at hg ⊢
  have hg' : Matrix.GeneralLinearGroup.det g = 1 := by
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using hg
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map_det, hg']
  simp

private def statedSLTwoMapAut {K : Type} [Field K] (φ : K →+* K) :
    StatedSL 2 K →* StatedSL 2 K where
  toFun g := ⟨Matrix.GeneralLinearGroup.map φ g, map_mem_statedSL_two φ g.2⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

private theorem statedSLTwoMapAut_apply {K : Type} [Field K] (φ : K →+* K)
    (g : StatedSL 2 K) :
    ((statedSLTwoMapAut φ g : StatedSL 2 K) : GL (Fin 2) K) =
      Matrix.GeneralLinearGroup.map φ (g : GL (Fin 2) K) := rfl

private theorem statedSLTwoMapAut_bijective {K : Type} [Field K] (φ : RingAut K) :
    Function.Bijective (statedSLTwoMapAut (φ : K →+* K)) := by
  constructor
  · intro a b hab
    have h := congrArg (fun x : StatedSL 2 K => (x : GL (Fin 2) K)) hab
    rw [statedSLTwoMapAut_apply, statedSLTwoMapAut_apply] at h
    have h2 := congrArg (Matrix.GeneralLinearGroup.map (φ.symm : K →+* K)) h
    rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp_apply,
      ← Matrix.GeneralLinearGroup.map_comp,
      RingEquiv.symm_comp, Matrix.GeneralLinearGroup.map_id] at h2
    exact Subtype.ext h2
  · intro b
    refine ⟨⟨Matrix.GeneralLinearGroup.map (φ.symm : K →+* K) (b : GL (Fin 2) K),
      map_mem_statedSL_two _ b.2⟩, ?_⟩
    apply Subtype.ext
    change Matrix.GeneralLinearGroup.map (φ : K →+* K)
        (Matrix.GeneralLinearGroup.map (φ.symm : K →+* K) (b : GL (Fin 2) K)) =
      (b : GL (Fin 2) K)
    rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
      RingEquiv.comp_symm, Matrix.GeneralLinearGroup.map_id]
    rfl

private noncomputable def statedSLTwoMulAut {K : Type} [Field K] (φ : RingAut K) :
    MulAut (StatedSL 2 K) :=
  MulEquiv.ofBijective (statedSLTwoMapAut (φ : K →+* K)) (statedSLTwoMapAut_bijective φ)

private theorem statedSLTwoMulAut_apply {K : Type} [Field K] (φ : RingAut K)
    (g : StatedSL 2 K) :
    ((statedSLTwoMulAut φ g : StatedSL 2 K) : GL (Fin 2) K) =
      Matrix.GeneralLinearGroup.map (φ : K →+* K) (g : GL (Fin 2) K) := rfl

private theorem statedSLTwoMulAut_pow_apply {K : Type} [Field K] (φ : RingAut K)
    (n : ℕ) (g : StatedSL 2 K) :
    (((statedSLTwoMulAut φ) ^ n) g : GL (Fin 2) K) =
      Matrix.GeneralLinearGroup.map ((φ ^ n : RingAut K) : K →+* K) (g : GL (Fin 2) K) := by
  induction n generalizing g with
  | zero =>
      have h1 : ((φ ^ 0 : RingAut K) : K →+* K) = RingHom.id K := rfl
      rw [pow_zero, h1, Matrix.GeneralLinearGroup.map_id]
      rfl
  | succ n ih =>
      rw [pow_succ]
      change ((((statedSLTwoMulAut φ) ^ n) (statedSLTwoMulAut φ g)) : GL (Fin 2) K) =
        Matrix.GeneralLinearGroup.map ((φ ^ (n + 1) : RingAut K) : K →+* K) (g : GL (Fin 2) K)
      rw [ih, statedSLTwoMulAut_apply]
      have hpow : ((φ ^ n : RingAut K) : K →+* K).comp (φ : K →+* K) =
          ((φ ^ (n + 1) : RingAut K) : K →+* K) := by
        ext x
        simp [pow_succ]
      rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp, hpow]

private theorem fieldAut_pow_three_pow_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (φ : RingAut K)
    (hφpow : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3)))) :
    φ ^ (3 ^ (f.factorization 3)) = 1 := by
  let q₀ := p ^ (f / 3 ^ (f.factorization 3))
  have hpow : ∀ m : ℕ, ∀ x : K, (φ ^ m) x = x ^ (q₀ ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ']
        change φ ((φ ^ m) x) = x ^ (q₀ ^ (m + 1))
        rw [ih, hφpow, ← pow_mul, pow_succ]
  have hq0pow : q₀ ^ (3 ^ (f.factorization 3)) = p ^ f := by
    dsimp only [q₀]
    rw [← pow_mul, Nat.div_mul_cancel]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr le_rfl
  have hpowcard : ∀ x : K, x ^ Nat.card K = x := by
    intro x
    let hF : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  apply RingEquiv.ext
  intro x
  rw [hpow, hq0pow, ← hK]
  exact hpowcard x

private theorem statedSLTwoMulAut_pow_three_pow_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (φ : RingAut K)
    (hφ : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3)))) :
    (statedSLTwoMulAut φ) ^ (3 ^ (f.factorization 3)) = 1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [statedSLTwoMulAut_pow_apply, fieldAut_pow_three_pow_eq_one hf hK φ hφ]
  rfl

private def invariantRestrictHom {X : Type*} [Group X] (Φ : MulAut X) (C : Subgroup X)
    (hC : C.map Φ.toMonoidHom = C) : C →* C where
  toFun x := ⟨Φ (x : X), by
    have h : Φ (x : X) ∈ C.map Φ.toMonoidHom := ⟨x, x.2, rfl⟩
    rwa [hC] at h⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

private theorem invariantRestrictHom_bijective {X : Type*} [Group X] (Φ : MulAut X)
    (C : Subgroup X) (hC : C.map Φ.toMonoidHom = C) :
    Function.Bijective (invariantRestrictHom Φ C hC) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact Φ.injective (congrArg Subtype.val hab)
  · intro y
    have hy : (y : X) ∈ C.map Φ.toMonoidHom := by rw [hC]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

private noncomputable def invariantRestrictAut {X : Type*} [Group X] (Φ : MulAut X)
    (C : Subgroup X) (hC : C.map Φ.toMonoidHom = C) : MulAut C :=
  MulEquiv.ofBijective (invariantRestrictHom Φ C hC) (invariantRestrictHom_bijective Φ C hC)

private theorem invariantRestrictAut_apply_coe {X : Type*} [Group X] (Φ : MulAut X)
    (C : Subgroup X) (hC : C.map Φ.toMonoidHom = C) (x : C) :
    ((invariantRestrictAut Φ C hC x : C) : X) = Φ x :=
  rfl

private theorem invariantRestrictAut_pow_apply {X : Type*} [Group X] (Φ : MulAut X)
    (C : Subgroup X) (hC : C.map Φ.toMonoidHom = C) (n : ℕ) (x : C) :
    (((invariantRestrictAut Φ C hC) ^ n) x : X) = ((Φ ^ n) x : X) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change ((((invariantRestrictAut Φ C hC) ^ n)
        (invariantRestrictAut Φ C hC x)) : X) = ((Φ ^ n) (Φ x) : X)
      rw [ih, invariantRestrictAut_apply_coe]

private theorem zmod_three_pow_eq_self (b : ℕ) (w : ZMod 3) : w ^ (3 ^ b) = w := by
  have h3 : w ^ 3 = w := ZMod.pow_card w
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, pow_mul, ih, h3]

private theorem exists_pow_eq_of_isCyclic_of_three {C : Type*} [Group C] [Finite C] {b : ℕ}
    (hcyc : IsCyclic C) (h3dvd : 3 ∣ Nat.card C) (θ : MulAut C)
    (hθ : θ ^ (3 ^ b) = 1) :
    ∃ s : ℕ, s % 3 = 1 ∧ ∀ x : C, θ x = x ^ s := by
  classical
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic θ.toMonoidHom
  have hiter : ∀ k : ℕ, ∀ x : C, (θ ^ k) x = x ^ (m ^ k) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ']
        change θ ((θ ^ k) x) = x ^ (m ^ (k + 1))
        rw [ih]
        have hθx : θ (x ^ (m ^ k)) = (x ^ (m ^ k)) ^ m := hm (x ^ (m ^ k))
        rw [hθx, ← _root_.zpow_mul]
        congr 1
        rw [pow_succ]
  have hcgen : orderOf c = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hc
  have hcm : c ^ (m ^ (3 ^ b)) = c ^ (1 : ℤ) := by
    have h1 := hiter (3 ^ b) c
    rw [hθ] at h1
    simpa using h1.symm
  have hmod : m ^ (3 ^ b) ≡ 1 [ZMOD Nat.card C] := by
    rw [← hcgen]
    exact zpow_eq_zpow_iff_modEq.mp hcm
  have hmod3 : m ^ (3 ^ b) ≡ 1 [ZMOD 3] := by
    have hdvdZ : (3 : ℤ) ∣ (Nat.card C : ℤ) := by exact_mod_cast h3dvd
    exact Int.modEq_iff_dvd.mpr (dvd_trans hdvdZ (Int.modEq_iff_dvd.mp hmod))
  have hm3 : m ≡ 1 [ZMOD 3] := by
    have hz : (m : ZMod 3) ^ (3 ^ b) = 1 := by
      have h1 : ((m ^ (3 ^ b) : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod3
      simpa using h1
    have hmz : (m : ZMod 3) = 1 := by
      rw [← zmod_three_pow_eq_self b (m : ZMod 3)]
      exact hz
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hmz
  let s := m.natMod (Nat.card C : ℤ)
  have hscast : (s : ℤ) ≡ m [ZMOD Nat.card C] := by
    dsimp only [s]
    rw [show (Int.natMod m (Nat.card C : ℤ) : ℤ) = m % (Nat.card C : ℤ) from
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (Nat.card_pos (α := C)).ne'))]
    exact Int.emod_emod _ _
  have hs3 : (s : ℤ) ≡ 1 [ZMOD 3] := by
    have hdvdZ : (3 : ℤ) ∣ (Nat.card C : ℤ) := by exact_mod_cast h3dvd
    exact (Int.modEq_iff_dvd.mpr
      (dvd_trans hdvdZ (Int.modEq_iff_dvd.mp hscast))).trans hm3
  refine ⟨s, ?_, ?_⟩
  · have hnat : s ≡ 1 [MOD 3] := by
      rw [← Int.natCast_modEq_iff]
      exact hs3
    have hnat2 : s % 3 = 1 % 3 := hnat
    rw [show 1 % 3 = 1 from by norm_num] at hnat2
    exact hnat2
  · intro x
    have hx : orderOf x ∣ Nat.card C := by
      rw [← hcgen]
      exact orderOf_dvd_of_mem_zpowers (hc x)
    have hsm : (s : ℤ) ≡ m [ZMOD orderOf x] := by
      have h2 : (orderOf x : ℤ) ∣ (Nat.card C : ℤ) := by exact_mod_cast hx
      exact Int.modEq_iff_dvd.mpr (dvd_trans h2 (Int.modEq_iff_dvd.mp hscast))
    have hxθ : θ x = x ^ m := hm x
    rw [hxθ, ← zpow_natCast]
    exact zpow_eq_zpow_iff_modEq.mpr hsm.symm

theorem exists_stable_cyclic_sylow_three_statedSL_two {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f) (φ : RingAut K)
    (hφ : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3)))) :
    ∃ (C : Subgroup (GL (Fin 2) K)) (s : ℕ), IsSylowOf 3 C (StatedSL 2 K) ∧ IsCyclic C ∧
      s % 3 = 1 ∧ ∀ g ∈ C, Matrix.GeneralLinearGroup.map (φ : K →+* K) g = g ^ s := by
  have hfact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfactp : Fact p.Prime := ⟨hp⟩
  have h3q : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  let X := StatedSL 2 K
  let Φ : MulAut X := statedSLTwoMulAut φ
  have hΦ : Φ ^ (3 ^ (f.factorization 3)) = 1 :=
    statedSLTwoMulAut_pow_three_pow_eq_one hf hK φ hφ
  let P : Subgroup (MulAut X) := Subgroup.zpowers Φ
  have hPp : IsPGroup 3 P := by
    apply IsPGroup.of_card_dvd_pow (n := f.factorization 3)
    rw [show P = Subgroup.zpowers Φ from rfl, Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hΦ
  let hAct : MulDistribMulAction P X := MulDistribMulAction.compHom X P.subtype
  have hnot : ¬ 3 ∣ Nat.card (Sylow 3 X) := not_dvd_card_sylow 3 X
  obtain ⟨Q, hQfix⟩ := hPp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 X) hnot
  have hΦQ : ((Q : Subgroup X).map Φ.toMonoidHom) = (Q : Subgroup X) := by
    have h1 := MulAction.mem_fixedPoints.mp hQfix ⟨Φ, Subgroup.mem_zpowers Φ⟩
    have h2 := congrArg (fun R : Sylow 3 X => (R : Subgroup X)) h1
    have h3 : (⟨Φ, Subgroup.mem_zpowers Φ⟩ : P) • (Q : Subgroup X) = (Q : Subgroup X) := h2
    have h4 : (⟨Φ, Subgroup.mem_zpowers Φ⟩ : P) • (Q : Subgroup X) =
        (Q : Subgroup X).map
          (MulDistribMulAction.toMonoidEnd P X ⟨Φ, Subgroup.mem_zpowers Φ⟩) :=
      Subgroup.pointwise_smul_def _
    rw [h4] at h3
    have h5 : MulDistribMulAction.toMonoidEnd P X
        (⟨Φ, Subgroup.mem_zpowers Φ⟩ : P) = (Φ : X →* X) := by
      ext x; rfl
    rw [h5] at h3
    exact h3
  let C₀ : Subgroup X := (Q : Subgroup X)
  have hcycC₀ : IsCyclic C₀ :=
    isCyclic_of_isPGroup_three_statedSL_two h3q C₀ Q.isPGroup'
  have h3cardX : 3 ∣ Nat.card X := by
    rw [show Nat.card X = Nat.card K * (Nat.card K ^ 2 - 1) from
      CFSG.Open.StatedAPI.card_statedSL_two K]
    have hne : (Nat.card K : ZMod 3) ≠ 0 := by
      intro h
      exact h3q ((ZMod.natCast_eq_zero_iff (Nat.card K) 3).mp h)
    have h1 : (Nat.card K : ZMod 3) ^ 2 = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one (p := 3) hne
    have hz : ((Nat.card K ^ 2 - 1 : ℕ) : ZMod 3) = 0 := by
      have hcast : ((Nat.card K ^ 2 - 1 : ℕ) : ZMod 3) =
          (Nat.card K : ZMod 3) ^ 2 - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow 2 (Nat.card K) Nat.card_pos)]
        push_cast
        ring
      rw [hcast, h1]; ring
    exact dvd_mul_of_dvd_right ((ZMod.natCast_eq_zero_iff (Nat.card K ^ 2 - 1) 3).mp hz) _
  have h3C₀ : 3 ∣ Nat.card C₀ := by
    rw [show Nat.card C₀ = 3 ^ Nat.factorization (Nat.card X) 3 from Sylow.card_eq_multiplicity Q]
    exact dvd_pow_self 3 (Nat.prime_three.factorization_pos_of_dvd (Nat.card_pos.ne') h3cardX).ne'
  let θ : MulAut C₀ := invariantRestrictAut Φ C₀ hΦQ
  have hθ : θ ^ (3 ^ (f.factorization 3)) = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [invariantRestrictAut_pow_apply, hΦ]
    rfl
  obtain ⟨s, hs, hsθ⟩ := exists_pow_eq_of_isCyclic_of_three hcycC₀ h3C₀ θ hθ
  refine ⟨C₀.map X.subtype, s, ⟨Q, rfl⟩, ?_, hs, ?_⟩
  · exact (C₀.equivMapOfInjective X.subtype Subtype.coe_injective).isCyclic.1 hcycC₀
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := hg
    have hxθ := hsθ ⟨x, hx⟩
    have hcoe : ((θ ⟨x, hx⟩ : C₀) : X) = statedSLTwoMulAut φ x :=
      invariantRestrictAut_apply_coe Φ C₀ hΦQ ⟨x, hx⟩
    have hX : statedSLTwoMulAut φ x = x ^ s := by
      rw [← hcoe]
      simpa using congrArg Subtype.val hxθ
    exact congrArg (fun y : X => (y : GL (Fin 2) K)) hX

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
