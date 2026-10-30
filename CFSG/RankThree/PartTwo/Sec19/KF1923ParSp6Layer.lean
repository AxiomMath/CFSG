module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Late.KFParSp6

open Matrix

theorem sq_not_inverting_of_normalized_three {S : Type*} [Group S] (t : S) (D K : Subgroup S)
    (hexp : ∀ d ∈ D, d ^ 3 = 1) (hKD : K ≤ D) (hK : Nat.card K = 3)
    (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (ht2 : ∀ d ∈ D, t ^ 2 * d * (t ^ 2)⁻¹ = d⁻¹) : False := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Nontrivial K := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hK]; norm_num)
  obtain ⟨d, hd1⟩ := exists_ne (1 : K)
  have hdK : (d : S) ∈ K := d.2
  have hdD : (d : S) ∈ D := hKD hdK
  have hd3 : (d : S) ^ 3 = 1 := hexp _ hdD
  have hdne : (d : S) ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hord : orderOf (d : S) = 3 := orderOf_eq_prime hd3 hdne
  have hzle : Subgroup.zpowers (d : S) ≤ K := Subgroup.zpowers_le.2 hdK
  have hzcard : Nat.card (Subgroup.zpowers (d : S)) = Nat.card K := by
    rw [Nat.card_zpowers, hord, hK]
  have hzK : Subgroup.zpowers (d : S) = K := Subgroup.eq_of_le_of_card_ge hzle hzcard.ge
  have hyK : t * (d : S) * t⁻¹ ∈ K := htK _ hdK
  have hyne : t * (d : S) * t⁻¹ ≠ 1 := fun h => hdne (by
    calc (d : S) = t⁻¹ * (t * (d : S) * t⁻¹) * t := by group
      _ = t⁻¹ * 1 * t := by rw [h]
      _ = 1 := by group)
  have hyz : t * (d : S) * t⁻¹ ∈ Subgroup.zpowers (d : S) := by rw [hzK]; exact hyK
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyz
  have hmod : (d : S) ^ (m % 3) = t * (d : S) * t⁻¹ := by
    have h := zpow_mod_orderOf (d : S) m
    rw [hord, hm] at h
    simpa using h
  have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hsq : t ^ 2 * (d : S) * (t ^ 2)⁻¹ = (d : S) := by
    have e : t ^ 2 * (d : S) * (t ^ 2)⁻¹ = t * (t * (d : S) * t⁻¹) * t⁻¹ := by
      simp only [pow_two, _root_.mul_inv_rev, mul_assoc]
    rcases hcases with h0 | h1 | h2
    · rw [h0, zpow_zero] at hmod
      exact absurd hmod.symm hyne
    · rw [h1, zpow_one] at hmod
      rw [e, ← hmod, ← hmod]
    · rw [h2] at hmod
      have h2' : (d : S) ^ 2 = t * (d : S) * t⁻¹ := by simpa using hmod
      rw [e]
      calc t * (t * (d : S) * t⁻¹) * t⁻¹ = t * ((d : S) ^ 2) * t⁻¹ := by rw [← h2']
        _ = (t * (d : S) * t⁻¹) ^ 2 := by simp only [pow_two]; group
        _ = ((d : S) ^ 2) ^ 2 := by rw [← h2']
        _ = (d : S) ^ 3 * (d : S) := by group
        _ = (d : S) := by rw [hd3, one_mul]
  have hfin := ht2 _ hdD
  rw [hsq] at hfin
  have hdd : (d : S) * (d : S) = 1 := by
    calc (d : S) * (d : S) = (d : S) * (d : S)⁻¹ := by rw [← hfin]
      _ = 1 := mul_inv_cancel _
  have hsq1 : (d : S) ^ 2 = 1 := by rw [pow_two]; exact hdd
  exact hdne (by
    calc (d : S) = (d : S) ^ 3 * ((d : S) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hd3, hsq1, inv_one, mul_one])

@[expose] def BlockTri (blk : Fin 6 → ℕ) (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop :=
  ∀ i j, blk j < blk i → g i j = 0

@[expose] abbrev Blk (blk : Fin 6 → ℕ) (β : ℕ) : Type := {i : Fin 6 // blk i = β}

@[expose] def diagBlock (blk : Fin 6 → ℕ) (β : ℕ) (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    Matrix (Blk blk β) (Blk blk β) (ZMod 2) :=
  fun i j => g i.1 j.1

theorem blockTri_mul {blk : Fin 6 → ℕ} {g h : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hg : BlockTri blk g) (hh : BlockTri blk h) : BlockTri blk (g * h) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : blk k < blk i
  · rw [hg i k hk, zero_mul]
  · rw [hh k j (by omega), mul_zero]

theorem sum_blk_eq {blk : Fin 6 → ℕ} {β : ℕ} (F : Fin 6 → ZMod 2)
    (hF : ∀ k, blk k ≠ β → F k = 0) :
    ∑ k : Fin 6, F k = ∑ k : Blk blk β, F k.1 := by
  classical
  have h1 : ∑ a : Blk blk β, F a.1 = ∑ a ∈ Finset.univ.filter (fun k => blk k = β), F a :=
    (Finset.sum_subtype _ (fun x => by simp) F).symm
  rw [h1]
  exact (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hF x (by simpa using hx)).symm

theorem diagBlock_mul {blk : Fin 6 → ℕ} {g h : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hg : BlockTri blk g) (hh : BlockTri blk h) (β : ℕ) :
    diagBlock blk β (g * h) = diagBlock blk β g * diagBlock blk β h := by
  ext i j
  simp only [diagBlock, Matrix.mul_apply]
  refine sum_blk_eq (fun k => g i.1 k * h k j.1) fun k hk => ?_
  show g i.1 k * h k j.1 = 0
  rcases lt_or_gt_of_ne hk with h1 | h1
  · rw [hg i.1 k (by rw [i.2]; exact h1), zero_mul]
  · rw [hh k j.1 (by rw [j.2]; exact h1), mul_zero]

theorem diagBlock_one (blk : Fin 6 → ℕ) (β : ℕ) : diagBlock blk β 1 = 1 := by
  ext i j
  simp [diagBlock, Matrix.one_apply, Subtype.ext_iff]

@[expose] def diagUnit (blk : Fin 6 → ℕ) (β : ℕ) (g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2))
    (hg : BlockTri blk (g : Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (hg' : BlockTri blk ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :
      Matrix (Fin 6) (Fin 6) (ZMod 2))) :
    Matrix.GeneralLinearGroup (Blk blk β) (ZMod 2) :=
  Units.mk (diagBlock blk β g)
    (diagBlock blk β ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (by
      rw [← diagBlock_mul hg hg', ← Units.val_mul, mul_inv_cancel, Units.val_one, diagBlock_one])
    (by
      rw [← diagBlock_mul hg' hg, ← Units.val_mul, inv_mul_cancel, Units.val_one, diagBlock_one])

@[expose] def diagHom (blk : Fin 6 → ℕ) (β : ℕ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)))
    (hH : ∀ g ∈ H, BlockTri blk (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) :
    H →* Matrix.GeneralLinearGroup (Blk blk β) (ZMod 2) :=
  MonoidHom.mk' (fun g => diagUnit blk β (g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2))
      (hH _ g.2) (hH _ (H.inv_mem g.2)))
    (fun g h => Units.ext (by
      show diagBlock blk β ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) *
          (h : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2))) = _
      rw [Units.val_mul]
      exact diagBlock_mul (hH _ g.2) (hH _ h.2) β))

theorem not_nine_dvd_card_GL_fin (k : ℕ) (hk : k ≤ 3) :
    ¬ 9 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases k <;> decide

theorem not_nine_dvd_card_GL_block (blk : Fin 6 → ℕ) (β : ℕ) (hsz : Fintype.card (Blk blk β) ≤ 3) :
    ¬ 9 ∣ Nat.card (Matrix.GeneralLinearGroup (Blk blk β) (ZMod 2)) := by
  have e1 : Blk blk β ≃ Fin (Fintype.card (Blk blk β)) := Fintype.equivFin _
  have e : Nat.card (Matrix.GeneralLinearGroup (Blk blk β) (ZMod 2)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin (Fintype.card (Blk blk β))) (ZMod 2)) :=
    Nat.card_congr (Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e1).toMulEquiv).toEquiv
  rw [e]
  exact not_nine_dvd_card_GL_fin _ hsz

theorem pow_entry_level (blk : Fin 6 → ℕ) (M : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (hM : ∀ i j, M i j ≠ 0 → blk i < blk j) :
    ∀ k : ℕ, ∀ i j, (M ^ k) i j ≠ 0 → blk i + k ≤ blk j := by
  intro k
  induction k with
  | zero =>
    intro i j h
    rw [pow_zero] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [mul_ne_zero_iff] at hl
    have h1 := ih i l hl.1
    have h2 := hM l j hl.2
    omega

theorem one_add_pow_eight (blk : Fin 6 → ℕ) (hblk : ∀ i, blk i < 6)
    (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hM : ∀ i j, M i j ≠ 0 → blk i < blk j) :
    (1 + M) ^ 8 = 1 := by
  have hNN : ∀ N : Matrix (Fin 6) (Fin 6) (ZMod 2), N + N = 0 := fun N => by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  have hsq2 : ∀ N : Matrix (Fin 6) (Fin 6) (ZMod 2), (1 + N) ^ 2 = 1 + N ^ 2 := fun N => by
    rw [pow_two, pow_two]
    calc (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
      _ = 1 + N * N := by rw [hNN N, add_zero]
  have hM6 : M ^ 6 = 0 := by
    ext i j
    rw [Matrix.zero_apply]
    by_contra h
    have h1 := pow_entry_level blk M hM 6 i j h
    have h2 := hblk j
    omega
  have hM8 : M ^ 8 = 0 := by
    rw [show (8 : ℕ) = 6 + 2 from rfl, pow_add, hM6, zero_mul]
  rw [show (8 : ℕ) = 2 * 2 * 2 from rfl, pow_mul, pow_mul, hsq2, hsq2, hsq2]
  rw [← pow_mul, ← pow_mul, show (2 * 2 * 2 : ℕ) = 8 from rfl, hM8, add_zero]

theorem eq_one_of_diag_one (blk : Fin 6 → ℕ) (hblk : ∀ i, blk i < 6)
    {d : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)}
    (hd : BlockTri blk (d : Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (hdiag : ∀ β : ℕ, diagBlock blk β (d : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1)
    (h3 : d ^ 3 = 1) : d = 1 := by
  have hMlt : ∀ i j, ((d : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) i j ≠ 0 → blk i < blk j := by
    intro i j hij
    by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · apply hij
      have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hlt
      simp [Matrix.sub_apply, Matrix.one_apply_ne hne, hd i j hlt]
    · apply hij
      have hdi := congrFun (congrFun (hdiag (blk i)) ⟨i, rfl⟩) ⟨j, heq⟩
      simp [diagBlock, Matrix.one_apply] at hdi
      simp [Matrix.sub_apply, Matrix.one_apply, hdi]
  have hd8m : (d : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 8 = 1 := by
    rw [show (d : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + ((d : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) by abel]
    exact one_add_pow_eight blk hblk _ hMlt
  have hd8 : d ^ 8 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hd8m)
  have h9 : d ^ 9 = 1 := by rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, h3, one_pow]
  calc d = d ^ 9 * (d ^ 8)⁻¹ := by group
    _ = 1 := by rw [h9, hd8, inv_one, mul_one]

theorem layer_contradiction (blk : Fin 6 → ℕ) (hblk : ∀ i, blk i < 6)
    (hsz : ∀ β : ℕ, Fintype.card (Blk blk β) ≤ 3)
    (P D : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)))
    (t : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2))
    (hP : ∀ g ∈ P, BlockTri blk (g : Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (hDP : D ≤ P) (hD9 : Nat.card D = 9) (hexp : ∀ d ∈ D, d ^ 3 = 1) (htP : t ∈ P)
    (htD : ∀ d ∈ D, t * d * t⁻¹ ∈ D)
    (ht2 : ∀ d ∈ D, t ^ 2 * d * (t ^ 2)⁻¹ = d⁻¹) : False := by
  have hD : ∀ g ∈ D, BlockTri blk (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) :=
    fun g hg => hP g (hDP hg)
  have hrange : ∀ β : ℕ, Nat.card (diagHom blk β D hD).range = 1 ∨
      Nat.card (diagHom blk β D hD).range = 3 := by
    intro β
    have hprod := (diagHom blk β D hD).ker.card_mul_index
    rw [Subgroup.index_ker, hD9] at hprod
    have hdiv : Nat.card (diagHom blk β D hD).range ∣ 3 ^ 2 :=
      Dvd.intro_left _ (by simpa using hprod)
    obtain ⟨m, hm, hx⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdiv
    have hnot := not_nine_dvd_card_GL_block blk β (hsz β)
    have hdvd := Subgroup.card_subgroup_dvd_card (diagHom blk β D hD).range
    interval_cases m
    · left; simpa using hx
    · right; simpa using hx
    · exfalso
      apply hnot
      rw [hx] at hdvd
      simpa using hdvd
  by_cases hA : ∃ β : ℕ, Nat.card (diagHom blk β D hD).range = 3
  · obtain ⟨β, hβ⟩ := hA
    have hkerD : Nat.card (diagHom blk β D hD).ker = 3 := by
      have hprod := (diagHom blk β D hD).ker.card_mul_index
      rw [Subgroup.index_ker, hβ, hD9] at hprod
      omega
    have hKcard : Nat.card ((diagHom blk β D hD).ker.map D.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective D), hkerD]
    have hKD : (diagHom blk β D hD).ker.map D.subtype ≤ D := by
      rintro _ ⟨x, _, hx⟩
      rw [← hx]
      exact x.2
    have hconj : ∀ k : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2), k ∈ D →
        diagBlock blk β (k : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 →
        diagBlock blk β ((t * k * t⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :
          Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
      intro k hk hkd
      have ht_inv : t⁻¹ ∈ P := P.inv_mem htP
      rw [Units.val_mul, Units.val_mul]
      rw [diagBlock_mul (blockTri_mul (hP t htP) (hD k hk)) (hP _ ht_inv) β,
        diagBlock_mul (hP t htP) (hD k hk) β, hkd, mul_one]
      rw [← diagBlock_mul (hP t htP) (hP _ ht_inv) β, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, diagBlock_one]
    refine sq_not_inverting_of_normalized_three t D _ hexp hKD hKcard ?_ ht2
    rintro k ⟨x, hx, rfl⟩
    have hdx : diagBlock blk β ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hx)
      simpa [diagHom, diagUnit] using this
    refine Subgroup.mem_map.2 ⟨⟨t * (x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) * t⁻¹,
      htD _ x.2⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    simpa [diagHom, diagUnit] using hconj _ x.2 hdx
  · push Not at hA
    have hone : ∀ β : ℕ, Nat.card (diagHom blk β D hD).range = 1 := fun β =>
      (hrange β).resolve_right (hA β)
    have hdiag : ∀ d ∈ D, ∀ β : ℕ, diagBlock blk β (d : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
      intro d hd β
      have hbot : (diagHom blk β D hD).range = ⊥ := Subgroup.eq_bot_of_card_eq _ (hone β)
      have hmem : diagHom blk β D hD ⟨d, hd⟩ ∈ (diagHom blk β D hD).range :=
        MonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have := congrArg Units.val hmem
      simpa [diagHom, diagUnit] using this
    have hall : ∀ d ∈ D, d = 1 := fun d hd =>
      eq_one_of_diag_one blk hblk (hD d hd) (hdiag d hd) (hexp d hd)
    have hDbot : D = ⊥ :=
      (Subgroup.eq_bot_iff_forall D).2 fun d hd => Subgroup.mem_bot.2 (hall d hd)
    rw [hDbot, Subgroup.card_bot] at hD9
    norm_num at hD9

end CFSG.RankThree.PartTwo.Late.KFParSp6

end
