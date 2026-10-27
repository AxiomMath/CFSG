module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open scoped Matrix

namespace TableB

section UnitaryInn

variable {K : Type} [Field K]

theorem matConjImage_gu_subset_inn [Finite K] {n d : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)
    (hcop : (2 ^ n + 1).Coprime d) :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)) ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  rintro φ ⟨A, ⟨μ, hμ0, hμq, hA⟩, hφ⟩
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ x, σ x = x ^ 2 ^ n := iterateFrobenius_def 2 n
  have hm : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ 2 ^ n) = M.map σ := fun M => by
    ext i j
    simp [hσ]
  have hq : 2 ≤ 2 ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [hm] at hA
  obtain ⟨l, hl⟩ := exists_norm_eq hq hK hμ0 hμq
  set A' := Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ * A with hA'
  have hA'U : ((A' : Matrix (Fin d) (Fin d) K).map σ)ᵀ * (A' : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hA', coe_scalar_mul, transpose_map_smul, Matrix.smul_mul, Matrix.mul_smul,
      hA, smul_smul, smul_smul, hσ, ← hl]
    have h0 : ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) = 1 := by
      have hinv : ((l⁻¹ : Kˣ) : K) * (l : K) = 1 := Units.inv_mul l
      calc ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) =
            (((l⁻¹ : Kˣ) : K) * l) ^ 2 ^ n * (((l⁻¹ : Kˣ) : K) * l) := by ring
        _ = 1 := by rw [hinv, one_pow, one_mul]
    rw [h0, one_smul]
  set δ := Matrix.GeneralLinearGroup.det A' with hδ
  have hδq : δ ^ (2 ^ n + 1) = 1 := by
    apply Units.ext
    have h1 := congrArg Matrix.det hA'U
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    have h2 : ((A' : Matrix (Fin d) (Fin d) K).map σ).det =
        (A' : Matrix (Fin d) (Fin d) K).det ^ 2 ^ n := by
      rw [← hσ, RingHom.map_det]
      rfl
    rw [Units.val_pow_eq_pow_val, hδ, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
      pow_succ, ← h2, h1]
  have hb : ((d : ℤ) * Nat.gcdA d (2 ^ n + 1) + ((2 ^ n + 1 : ℕ) : ℤ) * Nat.gcdB d (2 ^ n + 1)) =
      1 := by
    have h := Nat.gcd_eq_gcd_ab d (2 ^ n + 1)
    rw [Nat.Coprime.gcd_eq_one hcop.symm] at h
    exact_mod_cast h.symm
  set ν : Kˣ := δ ^ Nat.gcdA d (2 ^ n + 1) with hν
  have hδq' : δ ^ ((2 ^ n + 1 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, hδq]
  have hνd : ν ^ d = δ := by
    have e1 : δ = δ ^ ((d : ℤ) * Nat.gcdA d (2 ^ n + 1)) := by
      conv_lhs => rw [← zpow_one δ, ← hb]
      rw [zpow_add, zpow_mul δ ((2 ^ n + 1 : ℕ) : ℤ), hδq', one_zpow, mul_one]
    rw [hν, ← zpow_natCast, ← zpow_mul, mul_comm, ← e1]
  have hνq : ν ^ (2 ^ n + 1) = 1 := by
    rw [hν, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hδq', one_zpow]
  set S := Matrix.GeneralLinearGroup.scalar (Fin d) ν⁻¹ * A' with hS
  have hSdet : (S : Matrix (Fin d) (Fin d) K).det = 1 := by
    have h : Matrix.GeneralLinearGroup.det S = 1 := by
      rw [hS, map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hδ, ← hνd,
        inv_pow, inv_mul_cancel]
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]
  have hSU : ((S : Matrix (Fin d) (Fin d) K).map σ)ᵀ * (S : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hS, coe_scalar_mul, transpose_map_smul, Matrix.smul_mul, Matrix.mul_smul, hA'U,
      smul_smul, hσ]
    have h0 : ((ν⁻¹ : Kˣ) : K) ^ 2 ^ n * ((ν⁻¹ : Kˣ) : K) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ, inv_pow, hνq, inv_one,
        Units.val_one]
    rw [h0, one_smul]
  have hSmem : S ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) :=
    Subgroup.subset_closure ⟨hSdet, by rw [hm]; exact hSU⟩
  have hconj : ∀ g : GL (Fin d) K, S * g * S⁻¹ = A * g * A⁻¹ := fun g => by
    rw [hS, hA', ← mul_assoc, ← map_mul]
    have hc := Subgroup.mem_center_iff.mp (scalar_mem_center (ι := Fin d) (ν⁻¹ * l⁻¹))
    set s := Matrix.GeneralLinearGroup.scalar (Fin d) (ν⁻¹ * l⁻¹)
    rw [mul_inv_rev]
    calc s * A * g * (A⁻¹ * s⁻¹) = s * (A * g * A⁻¹) * s⁻¹ := by group
      _ = (A * g * A⁻¹) * s * s⁻¹ := by rw [hc (A * g * A⁻¹)]
      _ = A * g * A⁻¹ := by group
  obtain ⟨a, ha⟩ : ∃ a : LargeEvenSUGroup (Fin d) K (2 ^ n), (a : GL (Fin d) K) = S :=
    ⟨⟨S, hSmem⟩, rfl⟩
  refine ⟨(a : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))), ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hrel : ((a * h * a⁻¹ : LargeEvenSUGroup (Fin d) K (2 ^ n)) : GL (Fin d) K) =
        A * h * A⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha]
      exact hconj h
    exact (hφ h (a * h * a⁻¹) hrel).symm

end UnitaryInn

end TableB

section Labels

theorem recipeUnitary_subsetInn {d n : ℕ} {Q : LargeEvenRawCont} (hcop : (2 ^ n + 1).Coprime d)
    (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ =>
    TableB.matConjImage_gu_subset_inn hK hcop⟩

@[expose] def GGMpUnitaryCopLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ (2 ^ lab.n + 1).Coprime (lab.rank + 1)) ∨ (lab.tag = .twD ∧ lab.rank = 3)

theorem coprime_two_pow_add_one_four {n : ℕ} (hn : 1 ≤ n) : (2 ^ n + 1).Coprime 4 := by
  have hodd : Odd (2 ^ n + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ k, by rw [pow_succ]; ring⟩
  simpa using Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)

theorem coprime_two_pow_sub_one_three {n : ℕ} (hn : Odd n) : (2 ^ n - 1).Coprime 3 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    ring
  have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three, h2]
  omega


theorem largeEvenLabelAll_subset_inn_E6_odd {n : ℕ} (hn : Odd n) :
    LargeEvenLabelAll ⟨.E6, 0, n⟩
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
  intro Q hQ
  exact recipeChevalley_subsetInn (fun K _ _ hK => by
    have hcop : (Nat.card Kˣ).Coprime 3 := by
      rw [Nat.card_units, hK]
      exact coprime_two_pow_sub_one_three hn
    exact chevIDImage_subset_inn_of_top (τ := .E6)
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE6_adj fun s =>
        ⟨(powCoprime hcop).symm s, by rw [← powCoprime_apply hcop, Equiv.apply_symm_apply]⟩))
    hQ

end Labels

section Input

theorem ggInnerDiagMpInputOn_unitaryCop : GGInnerDiagMpInputOn GGMpUnitaryCopLabel :=
  ggInnerDiagMpInputOn_of_subset_inn fun lab hlab h => by
    obtain ⟨t, l, n⟩ := lab
    intro Q hQ
    rcases h with ⟨h, hc⟩ | ⟨h, h3⟩
    · dsimp only at h hc
      subst h
      exact recipeUnitary_subsetInn hc hQ
    · dsimp only at h h3
      subst h h3
      have hn : 1 ≤ n := hlab.1
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      simp only [show (3 : ℕ) ≠ 2 by decide, ↓reduceIte] at hQ ⊢
      exact recipeUnitary_subsetInn (coprime_two_pow_add_one_four hn) hQ

theorem ggInnerDiagMpInputOn_E6_odd :
    GGInnerDiagMpInputOn fun lab => lab.tag = .E6 ∧ Odd lab.n :=
  ggInnerDiagMpInputOn_of_subset_inn fun lab hlab h => by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨ht, hn⟩ := h
    dsimp only at ht hn
    subst ht
    obtain ⟨-, hl⟩ := hlab
    dsimp only at hl
    subst hl
    exact largeEvenLabelAll_subset_inn_E6_odd hn

end Input

end CFSG.StandardType
