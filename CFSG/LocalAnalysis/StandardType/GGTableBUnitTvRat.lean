module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdCent
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvCob
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeAMono

public section

namespace CFSG.StandardType.UnitTv

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB TableB

section Dlog

variable {K : Type} [Field K] {p : ℕ}

open Classical in
@[expose] noncomputable def dlog (p : ℕ) (ζ x : K) : ZMod p :=
  if h : ∃ n : ℤ, ζ ^ n = x then ((Classical.choose h : ℤ) : ZMod p) else 0

theorem dlog_zpow [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (m : ℤ) :
    dlog p ζ (ζ ^ m) = (m : ZMod p) := by
  classical
  have h : ∃ n : ℤ, ζ ^ n = ζ ^ m := ⟨m, rfl⟩
  unfold dlog
  rw [dif_pos h]
  have hn : ζ ^ (Classical.choose h) = ζ ^ m := Classical.choose_spec h
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne p)
  have h1 : ζ ^ (m - Classical.choose h) = 1 := by
    rw [zpow_sub₀ hζ0, hn, div_self (zpow_ne_zero _ hζ0)]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ m p).mpr ((hζ.zpow_eq_one_iff_dvd _).mp h1)

theorem exists_zpow_of_pow_eq_one [NeZero p] {ζ x : K} (hζ : IsPrimitiveRoot ζ p) (hx : x ^ p = 1) :
    ∃ m : ℤ, ζ ^ m = x := by
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
  exact ⟨(i : ℤ), by rw [zpow_natCast, hi]⟩

theorem dlog_inj [NeZero p] {ζ x y : K} (hζ : IsPrimitiveRoot ζ p) (hx : x ^ p = 1)
    (hy : y ^ p = 1) (h : dlog p ζ x = dlog p ζ y) : x = y := by
  obtain ⟨a, rfl⟩ := exists_zpow_of_pow_eq_one hζ hx
  obtain ⟨b, rfl⟩ := exists_zpow_of_pow_eq_one hζ hy
  rw [dlog_zpow hζ, dlog_zpow hζ] at h
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne p)
  have h1 : ζ ^ (b - a) = 1 := (hζ.zpow_eq_one_iff_dvd _).mpr
    ((ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mp h)
  rw [zpow_sub₀ hζ0, div_eq_one_iff_eq (zpow_ne_zero _ hζ0)] at h1
  exact h1.symm

theorem dlog_mul [NeZero p] {ζ x y : K} (hζ : IsPrimitiveRoot ζ p) (hx : x ^ p = 1)
    (hy : y ^ p = 1) : dlog p ζ (x * y) = dlog p ζ x + dlog p ζ y := by
  obtain ⟨a, rfl⟩ := exists_zpow_of_pow_eq_one hζ hx
  obtain ⟨b, rfl⟩ := exists_zpow_of_pow_eq_one hζ hy
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne p)
  rw [← zpow_add₀ hζ0, dlog_zpow hζ, dlog_zpow hζ, dlog_zpow hζ, Int.cast_add]

end Dlog

section Ratio

variable {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

open Classical in
@[expose] noncomputable def ratU (φ : ↥(unitarySU 2 n K d) →* L') (a : MulAut L')
    (k l : Fin d) : K :=
  if h : ∃ t : Fin d → K, ActsDiagU φ a t then
    Classical.choose h k * (Classical.choose h l)⁻¹ else 1

theorem ratU_eq (hM : Model φ) (hd : 3 ≤ d) {a : MulAut L'} {t : Fin d → K}
    (ha : ActsDiagU φ a t) (k l : Fin d) : ratU φ a k l = t k * (t l)⁻¹ := by
  classical
  have h : ∃ t : Fin d → K, ActsDiagU φ a t := ⟨t, ha⟩
  unfold ratU
  rw [dif_pos h]
  exact (Classical.choose_spec h).ratio_eq hM.field hd hM.ker ha k l

theorem ratU_mul (hM : Model φ) (hd : 3 ≤ d) {a b : MulAut L'} {t u : Fin d → K}
    (ha : ActsDiagU φ a t) (hb : ActsDiagU φ b u) (k l : Fin d) :
    ratU φ (a * b) k l = ratU φ a k l * ratU φ b k l := by
  rw [ratU_eq hM hd (actsDiagU_mul ha hb), ratU_eq hM hd ha, ratU_eq hM hd hb]
  have h1 := ha.ne_zero l
  have h2 := hb.ne_zero l
  field_simp

theorem ratU_coc (hM : Model φ) (hd : 3 ≤ d) {a : MulAut L'} {t : Fin d → K}
    (ha : ActsDiagU φ a t) (k l m : Fin d) :
    ratU φ a k l * ratU φ a l m = ratU φ a k m := by
  rw [ratU_eq hM hd ha, ratU_eq hM hd ha, ratU_eq hM hd ha]
  have h1 := ha.ne_zero l
  field_simp

theorem ratU_pow (hM : Model φ) (hd : 3 ≤ d) {a : MulAut L'} {t : Fin d → K}
    (ha : ActsDiagU φ a t) {p : ℕ} (hap : a ^ p = 1) (k l : Fin d) : ratU φ a k l ^ p = 1 := by
  rw [ratU_eq hM hd ha]
  exact ha.ratio_pow hM.field hd hM.ker hap k l

theorem eq_of_ratU_eq (hM : Model φ) (hd : 3 ≤ d) {a b : MulAut L'} {t u : Fin d → K}
    (ha : ActsDiagU φ a t) (hb : ActsDiagU φ b u)
    (h : ∀ k l, ratU φ a k l = ratU φ b k l) : a = b := by
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  have hne : t i0 ≠ 0 := ha.ne_zero _
  have hne' : u i0 ≠ 0 := hb.ne_zero _
  have hc : u i0 * (t i0)⁻¹ ≠ 0 := mul_ne_zero hne' (inv_ne_zero hne)
  have hmul : ActsDiagU φ a (fun k => t k * (u i0 * (t i0)⁻¹)) := actsDiagU_mul_const ha hc
  have heq : (fun k => t k * (u i0 * (t i0)⁻¹)) = u := by
    funext k
    have h1 := h k i0
    rw [ratU_eq hM hd ha, ratU_eq hM hd hb] at h1
    field_simp at h1 ⊢
    linear_combination h1
  rw [heq] at hmul
  exact actsDiagU_unique hM.surj hmul hb

end Ratio

section Heart

variable {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

@[expose] def pairZ {d : ℕ} (i j k : Fin d) : ℤ :=
  (if k = i then 1 else 0) - (if k = j then 1 else 0)

theorem pairZ_cast {p : ℕ} {d : ℕ} (i j k : Fin d) :
    ((pairZ i j k : ℤ) : ZMod p) = LinTvA.pairVec p i j k := by
  simp [pairZ, LinTvA.pairVec]

theorem ggPairVec_eq_zpow {ζ : K} (hζ0 : ζ ≠ 0) (i j k : Fin d) :
    TypeA.ggPairVec i j ζ k = ζ ^ pairZ i j k := by
  rw [TypeA.ggPairVec_apply]
  unfold pairZ
  split_ifs <;> simp [_root_.zpow_neg, hζ0]

theorem exists_heart (hM : Model φ) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (i j : Fin d) : ∃ h ∈ A, ActsDiagU φ h (TypeA.ggPairVec i j ζ) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hpv : ∀ m : Fin d, TypeA.ggPairVec i j ζ m ^ p = 1 := fun m =>
    TypeA.pow_ggPairVec hζ.pow_eq_one m
  obtain ⟨D, hD⟩ := exists_diagSU hM.field hpq hpv (TypeA.prod_ggPairVec ζ hζ0)
  exact ⟨MulAut.conj (φ D), conj_mem_of_selfCent hsc hdiag hD hpv, actsDiagU_conj hD⟩

theorem dlog_ratU_heart (hM : Model φ) (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {h : MulAut L'} (i j : Fin d)
    (hh : ActsDiagU φ h (TypeA.ggPairVec i j ζ)) (k l : Fin d) :
    dlog p ζ (ratU φ h k l) = LinTvA.pairVec p i j k - LinTvA.pairVec p i j l := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  rw [ratU_eq hM hd hh, ggPairVec_eq_zpow hζ0, ggPairVec_eq_zpow hζ0, ← _root_.zpow_neg,
    ← zpow_add₀ hζ0, dlog_zpow hζ, Int.cast_add, Int.cast_neg, pairZ_cast, pairZ_cast]
  ring

end Heart

section Monomial

variable {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem exists_monomial [Finite K] (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {s : ↥(unitarySU 2 n K d)}
    (hw : ∀ a ∈ A, MulAut.conj (φ s) * a * (MulAut.conj (φ s))⁻¹ ∈ A) :
    ∃ π : Equiv.Perm (Fin d), ∀ u : Fin d → K,
      ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal u =
        diagonal (u ∘ π) * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  classical
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hpv : ∀ k l m : Fin d, TypeA.ggPairVec k l ζ m ^ p = 1 := fun k l m =>
    TypeA.pow_ggPairVec hζ.pow_eq_one m
  have hDex : ∀ k l : Fin d, k ≠ l → ∃ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (TypeA.ggPairVec k l ζ) :=
    fun k l _ => exists_diagSU hM.field hpq (fun m => hpv k l m) (TypeA.prod_ggPairVec ζ hζ0)
  have hconj : ∀ x : ↥(unitarySU 2 n K d),
      MulAut.conj (φ (s * x * s⁻¹)) =
        MulAut.conj (φ s) * MulAut.conj (φ x) * (MulAut.conj (φ s))⁻¹ := by
    intro x
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D' : Fin d → K,
      ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal (TypeA.rootT ζ i j) =
        diagonal D' * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    obtain ⟨Dij, hDij⟩ := exists_diagSU hM.field hpq (u := TypeA.rootT ζ i j)
      (fun k => TypeA.rootT_pow hζ.pow_eq_one i j k) (TypeA.prod_rootT hζ0 hij)
    set X := s * Dij * s⁻¹ with hX
    have hXA : MulAut.conj (φ X) ∈ A := by
      have h1 : MulAut.conj (φ Dij) ∈ A :=
        conj_mem_of_selfCent hsc hdiag hDij (TypeA.rootT_pow hζ.pow_eq_one i j)
      rw [hX, hconj]
      exact hw _ h1
    have hXd : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag :=
      isDiag_of_conj_comm hM hK (by omega) hζinv hDex fun k l _ D hD =>
        IsElemAbelian.comm hA hXA (conj_mem_of_selfCent hsc hdiag hD (hpv k l))
    refine ⟨fun k => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k, ?_⟩
    have e1 : X * s = s * Dij := by rw [hX]; group
    have e2 := congrArg (fun y : ↥(unitarySU 2 n K d) =>
      ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) e1
    simp only [Subgroup.coe_mul, Units.val_mul] at e2
    have hXm : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal fun k => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k :=
      ((isDiag_iff_diagonal_diag _).mp hXd).symm
    rw [← hDij, ← e2]
    exact congrArg (· * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hXm
  exact TypeA.exists_perm_mul_diagonal hζinv (s : GL (Fin d) K) hmono

theorem actsDiagU_conj_elt {a : MulAut L'} {t t' : Fin d → K} (ha : ActsDiagU φ a t)
    (s : ↥(unitarySU 2 n K d))
    (hst : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal t' * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    ActsDiagU φ (MulAut.conj (φ s) * a * (MulAut.conj (φ s))⁻¹) t' := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  have hsN : (s : GL (Fin d) K) ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := Subgroup.le_normalizer s.2
  have hsiN : (s : GL (Fin d) K)⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := Subgroup.inv_mem _ hsN
  refine ⟨(s : GL (Fin d) K) * D * (s : GL (Fin d) K)⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hsN hD) hsiN, ?_, fun x => ?_⟩
  · have h1 : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t *
        (((s : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal t' := by
      rw [hst, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul, hDt]
    exact h1
  · have hs₀ : φ (conjN ((s : GL (Fin d) K)⁻¹) hsiN x) = (φ s)⁻¹ * φ x * φ s := by
      have e : conjN ((s : GL (Fin d) K)⁻¹) hsiN x = s⁻¹ * x * s := by
        apply Subtype.ext
        simp only [coe_conjN, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [e, map_mul, map_mul, map_inv]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply, ← hs₀, hact,
      ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [coe_conjN, Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem conj_perm_mem (hM : Model φ) (hd : 3 ≤ d) {p : ℕ} {A : Subgroup (MulAut L')}
    (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (σ : Equiv.Perm (Fin d)) {a : MulAut L'}
    (ha : a ∈ A) : MulAut.conj (φ (permSU hM.field σ)) * a *
      (MulAut.conj (φ (permSU hM.field σ)))⁻¹ ∈ A := by
  obtain ⟨h1, h2⟩ := weyl_W_prop hM.field hd hM.ker hAp hdiag (φ (permSU hM.field σ)) ⟨σ, rfl⟩ a ha
  have hc := hsc _ h2 h1
  have e : ∀ n : L', MulAut.conj n * a * (MulAut.conj n)⁻¹ = MulAut.conj (n * (a n)⁻¹) * a := by
    intro n
    refine MulEquiv.ext fun l => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv]
  rw [e]
  exact A.mul_mem hc ha

end Monomial

end CFSG.StandardType.UnitTv

end
