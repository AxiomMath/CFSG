module

public import CFSG.GH74.GLS.IVK.L2.BorelStd
public import CFSG.GH74.GLS.IVK.L2.FieldProj
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bWreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bFrobenius

open CFSG.GH74.GLS.IVK hiding innAut
open CFSG.GH74.GLS.IVK.L2Borel
open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bWreath
open scoped commutatorElement

abbrev F27 : Type := GaloisField 3 3

theorem card_F27 : Nat.card F27 = 27 := by
  rw [GaloisField.card 3 3 (by norm_num)]; norm_num

theorem three_eq_zero_F27 : (3 : F27) = 0 := CharP.cast_eq_zero F27 3

theorem two_ne_zero_F27 : (2 : F27) ≠ 0 :=
  two_ne_zero_of_odd_card (by rw [card_F27]; decide)

@[expose] noncomputable def frobF27 : F27 ≃+* F27 := frobeniusEquiv F27 3

theorem frobF27_apply (t : F27) : frobF27 t = t ^ 3 := by
  simp [frobF27, frobeniusEquiv_apply, frobenius_def]

theorem factorization_three_58968 : (58968 : ℕ).factorization 3 = 4 := by
  have h : (58968 : ℕ) = 3 ^ 4 * 728 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem exists_trace_ne_zero : ∃ t : F27, frobF27 (frobF27 t) - 2 * frobF27 t + t ≠ 0 := by
  classical
  have hcard : Nat.card F27 = 27 := card_F27
  let f : Polynomial F27 := Polynomial.X ^ 9 + Polynomial.X ^ 3 + Polynomial.X
  have hf : f ≠ 0 := by
    intro h
    have := congrArg (Polynomial.coeff · 9) h
    simp [f, Polynomial.coeff_X, Polynomial.coeff_X_pow] at this
  have hdeg : (f.natDegree : Cardinal) < Cardinal.mk F27 := by
    have h9 : f.natDegree ≤ 9 := by
      simp only [f]
      compute_degree
    rw [← Nat.cast_card, hcard]
    exact_mod_cast lt_of_le_of_lt h9 (by norm_num)
  obtain ⟨r, hr⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f hf hdeg
  refine ⟨r, ?_⟩
  simp only [frobF27_apply]
  intro h
  apply hr
  simp only [f, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
  have h3 : (3 : F27) = 0 := three_eq_zero_F27
  linear_combination h + r ^ 3 * h3

theorem frobF27_pow_three_apply (t : F27) : frobF27 (frobF27 (frobF27 t)) = t := by
  letI : Fintype F27 := Fintype.ofFinite F27
  have hcard : Fintype.card F27 = 27 := by
    have := card_F27
    rw [Nat.card_eq_fintype_card] at this
    exact this
  have h := FiniteField.pow_card t
  rw [hcard] at h
  simp only [frobF27_apply]
  rw [← pow_mul, ← pow_mul]
  simpa using h

theorem frobF27_pow_three : frobF27 ^ 3 = 1 := by
  ext t
  simpa [pow_succ] using frobF27_pow_three_apply t

theorem frobF27_ne_one : frobF27 ≠ 1 := by
  intro h
  obtain ⟨t, ht⟩ := exists_trace_ne_zero
  apply ht
  rw [h]
  simp
  ring

section Concrete

variable {Y : Type} [Group Y] (e : Y ≃* L2 F27)

theorem commutator_mulAut_conj (α : MulAut Y) (x : Y) :
    ⁅α, MulAut.conj x⁆ = MulAut.conj (α x * x⁻¹) := by
  ext y
  simp [commutatorElement_def, MulAut.conj_apply]

theorem mulAut_mul_conj_mul_inv (α : MulAut Y) (x : Y) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext y
  simp [MulAut.conj_apply]

@[expose] noncomputable def frobAut : MulAut Y := fieldAutHom e frobF27

theorem frobAut_pow_three : frobAut e ^ 3 = 1 := by
  rw [frobAut, ← map_pow, frobF27_pow_three, map_one]

theorem frobAut_wt (t : F27) : frobAut e (wt e t) = wt e (frobF27 t) :=
  fieldAutHom_wt _ _

theorem frobAut_not_mem_innAut : frobAut e ∉ innAut Y := by
  intro h
  have h1 := (innAut_le_innDiagSub e) h
  rw [mem_innDiagSub_iff, frobAut, fieldProj_fieldAutHom] at h1
  exact frobF27_ne_one h1

theorem wt_sub (a b : F27) : wt e (a - b) = wt e a * (wt e b)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← wt_add, sub_add_cancel]

theorem commutator_frobAut_conj_wt (t : F27) :
    ⁅frobAut e, MulAut.conj (wt e t)⁆ = MulAut.conj (wt e (frobF27 t - t)) := by
  rw [commutator_mulAut_conj, frobAut_wt, wt_sub]

theorem exists_jordan_frobAut :
    ∃ t : F27, ⁅frobAut e, ⁅frobAut e, MulAut.conj (wt e t)⁆⁆ ≠ 1 := by
  obtain ⟨t, ht⟩ := exists_trace_ne_zero
  refine ⟨t, ?_⟩
  rw [commutator_frobAut_conj_wt, commutator_frobAut_conj_wt]
  intro h
  have h1 := conj_injective_of_L2 e (h.trans (map_one MulAut.conj).symm)
  have h3 := wt_injective e two_ne_zero_F27 (h1.trans (wt_zero e).symm)
  apply ht
  rw [← h3]
  simp only [map_sub]
  ring

variable [Finite Y]

@[expose] noncomputable def U₀ : Subgroup Y := (wtHom e).range

theorem wt_mem_U₀ (t : F27) : wt e t ∈ U₀ e := ⟨Multiplicative.ofAdd t, rfl⟩

theorem exists_wt_of_mem_U₀ {k : Y} (hk : k ∈ U₀ e) : ∃ t : F27, wt e t = k := by
  obtain ⟨t, rfl⟩ := hk
  exact ⟨Multiplicative.toAdd t, rfl⟩

theorem card_U₀ : Nat.card (U₀ e) = 27 := by
  have hinj : Function.Injective (wtHom e) := fun s t h =>
    Multiplicative.toAdd.injective (wt_injective e two_ne_zero_F27 h)
  rw [U₀, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr Multiplicative.toAdd, card_F27]

theorem isElemAbelian_U₀ : IsElemAbelian 3 (U₀ e) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨s, rfl⟩ := exists_wt_of_mem_U₀ e ha
    obtain ⟨t, rfl⟩ := exists_wt_of_mem_U₀ e hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← wt_add, ← wt_add, add_comm]
  · obtain ⟨t, rfl⟩ := exists_wt_of_mem_U₀ e hx
    rw [pow_three, ← wt_add, ← wt_add]
    have : t + (t + t) = 0 := by
      have h3 := three_eq_zero_F27
      linear_combination t * h3
    rw [this, wt_zero]

@[expose] noncomputable def S₀ : Subgroup (MulAut Y) := (U₀ e).map (MulAut.conj : Y →* MulAut Y)

theorem card_S₀ : Nat.card (S₀ e) = 27 := by
  rw [S₀, Subgroup.card_map_of_injective (conj_injective_of_L2 e), card_U₀]

theorem isElemAbelian_S₀ : IsElemAbelian 3 (S₀ e) := isElemAbelian_map (isElemAbelian_U₀ e) _

theorem S₀_le_innAut : S₀ e ≤ innAut Y := by
  rintro _ ⟨u, -, rfl⟩
  exact ⟨u, rfl⟩

theorem frobAut_conj_mem {s : MulAut Y} (hs : s ∈ S₀ e) :
    frobAut e * s * (frobAut e)⁻¹ ∈ S₀ e := by
  obtain ⟨u, hu, rfl⟩ := hs
  obtain ⟨t, rfl⟩ := exists_wt_of_mem_U₀ e hu
  refine ⟨wt e (frobF27 t), wt_mem_U₀ e _, ?_⟩
  rw [mulAut_mul_conj_mul_inv, frobAut_wt]

theorem orderOf_frobAut : orderOf (frobAut e) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (frobAut_pow_three e) ?_
  intro h1
  exact frobAut_not_mem_innAut e (h1 ▸ Subgroup.one_mem _)

theorem frobAut_mem_normalizer : frobAut e ∈ Subgroup.normalizer (S₀ e) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => frobAut_conj_mem e hs, fun hs => ?_⟩
  have h2 := frobAut_conj_mem e hs
  have h3 := frobAut_conj_mem e h2
  have h4 : frobAut e * (frobAut e * (frobAut e * s * (frobAut e)⁻¹) * (frobAut e)⁻¹) *
      (frobAut e)⁻¹ = s := by
    have hα3 : frobAut e * frobAut e * frobAut e = 1 := by
      rw [← pow_three']; exact frobAut_pow_three e
    calc _ = (frobAut e * frobAut e * frobAut e) * s * (frobAut e * frobAut e * frobAut e)⁻¹ := by
          group
      _ = s := by rw [hα3]; simp
  rwa [h4] at h3

@[expose] noncomputable def M₀ : Subgroup (MulAut Y) := Subgroup.zpowers (frobAut e) ⊔ S₀ e

theorem zpowers_frobAut_le_normalizer :
    Subgroup.zpowers (frobAut e) ≤ Subgroup.normalizer (S₀ e) :=
  (Subgroup.zpowers_le).2 (frobAut_mem_normalizer e)

theorem M₀_le_normalizer : M₀ e ≤ Subgroup.normalizer (S₀ e) :=
  sup_le (zpowers_frobAut_le_normalizer e) Subgroup.le_normalizer

theorem isPGroup_M₀ : IsPGroup 3 (M₀ e) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH : IsPGroup 3 (Subgroup.zpowers (frobAut e)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_frobAut]; norm_num)
  have hK : IsPGroup 3 (S₀ e) := IsPGroup.of_card (n := 3) (by rw [card_S₀]; norm_num)
  exact hH.to_sup_of_normal_right' hK (zpowers_frobAut_le_normalizer e)

theorem frobAut_mem_M₀ : frobAut e ∈ M₀ e := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem card_M₀ (hA : Nat.card (MulAut Y) = 58968) : Nat.card (M₀ e) = 81 := by
  haveI : Finite (MulAut Y) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_M₀ e)
  have hdvd : Nat.card (M₀ e) ∣ 58968 := hA ▸ Subgroup.card_subgroup_dvd_card _
  have hk4 : k ≤ 4 := by
    have : 3 ^ k ∣ 58968 := hk ▸ hdvd
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num),
      factorization_three_58968] at this
    exact this
  have hS₀le : S₀ e ≤ M₀ e := le_sup_right
  have h27 : 27 ∣ Nat.card (M₀ e) := by
    rw [← card_S₀ e]; exact Subgroup.card_dvd_of_le hS₀le
  have hk3 : 3 ≤ k := by
    rw [hk] at h27
    have : 3 ^ 3 ∣ 3 ^ k := by simpa using h27
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hne : k ≠ 3 := by
    intro hk3'
    have hcard : Nat.card (M₀ e) = 27 := by rw [hk, hk3']; norm_num
    have hEq := Subgroup.eq_of_le_of_card_ge hS₀le (by rw [hcard, card_S₀])
    have hα := frobAut_mem_M₀ e
    rw [← hEq] at hα
    exact frobAut_not_mem_innAut e (S₀_le_innAut e hα)
  have : k = 4 := by omega
  rw [hk, this]; norm_num

theorem M₀_inf_innAut (hA : Nat.card (MulAut Y) = 58968) : M₀ e ⊓ innAut Y = S₀ e := by
  haveI : Finite (MulAut Y) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hM := card_M₀ e hA
  have hle : S₀ e ≤ M₀ e ⊓ innAut Y := le_inf le_sup_right (S₀_le_innAut e)
  have hd : Nat.card ↥(M₀ e ⊓ innAut Y) ∣ 81 := by
    rw [← hM]; exact Subgroup.card_dvd_of_le inf_le_left
  have h27 : 27 ∣ Nat.card ↥(M₀ e ⊓ innAut Y) := by
    rw [← card_S₀ e]; exact Subgroup.card_dvd_of_le hle
  have hne : Nat.card ↥(M₀ e ⊓ innAut Y) ≠ 81 := by
    intro h81
    have hEq := Subgroup.eq_of_le_of_card_ge (inf_le_left : M₀ e ⊓ innAut Y ≤ M₀ e)
      (by rw [h81, hM])
    have hα := frobAut_mem_M₀ e
    rw [← hEq] at hα
    exact frobAut_not_mem_innAut e hα.2
  have h27' : Nat.card ↥(M₀ e ⊓ innAut Y) = 27 := by
    obtain ⟨c, hc⟩ := h27
    rw [hc] at hd hne ⊢
    have hc3 : c ≤ 3 := by
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    interval_cases c <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h27', card_S₀])).symm

theorem wreath81_M₀ (hA : Nat.card (MulAut Y) = 58968) :
    Wreath81 (M₀ e) (M₀ e ⊓ innAut Y) := by
  rw [M₀_inf_innAut e hA]
  refine ⟨le_sup_right, card_M₀ e hA, card_S₀ e, isElemAbelian_S₀ e, ?_, ?_⟩
  · intro r hr s hs
    exact (Subgroup.mem_normalizer_iff.1 (M₀_le_normalizer e hr) s).1 hs
  · obtain ⟨t, ht⟩ := exists_jordan_frobAut e
    exact ⟨frobAut e, frobAut_mem_M₀ e, fun h => frobAut_not_mem_innAut e (S₀_le_innAut e h),
      MulAut.conj (wt e t), ⟨wt e t, wt_mem_U₀ e t, rfl⟩, ht⟩

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bFrobenius
