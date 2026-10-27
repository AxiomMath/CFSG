module

public import CFSG.SignalizerFunctorTheorem.NonLocal.UMain
public import CFSG.SignalizerFunctorTheorem.NonLocal.HeisDist
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
  CFSG.SignalizerFunctorTheorem.CatalogBridge
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {ℓ e : ℕ} {k : Type} [Field k] (h₀ : UnitaryFieldData ℓ e k)

section Vectors

variable {m : ℕ}

noncomputable def pad (u : Fin m → k) : Fin (m + 2) → k :=
  (Fin.cons 0 (Fin.cons 0 u : Fin (m + 1) → k) : Fin (m + 2) → k)

noncomputable def isoVec (ι : k) : Fin (m + 2) → k :=
  (Fin.cons 1 (Fin.cons ι 0 : Fin (m + 1) → k) : Fin (m + 2) → k)

theorem hform_apply {n : ℕ} (x y : Fin n → k) :
    gramForm h₀ (1 : Matrix (Fin n) (Fin n) k) x y = ∑ a, h₀.bar (x a) * y a := by
  rw [gramForm_apply, one_mulVec]
  rfl

theorem hform_pad (u u' : Fin m → k) :
    gramForm h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (pad u) (pad u') =
      ∑ j, h₀.bar (u j) * u' j := by
  simp [hform_apply, pad, Fin.sum_univ_succ]

theorem hform_isoVec_isoVec {ι : k} (hι : h₀.norm ι = -1) :
    gramForm h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (isoVec ι) (isoVec ι) = 0 := by
  simp [hform_apply, isoVec, Fin.sum_univ_succ]
  rw [mul_comm]
  have := hι
  rw [UnitaryFieldData.norm] at this
  linear_combination this

theorem hform_isoVec_pad (ι : k) (u : Fin m → k) :
    gramForm h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (isoVec ι) (pad u) = 0 := by
  simp [hform_apply, isoVec, pad, Fin.sum_univ_succ]

theorem hform_pad_isoVec (ι : k) (u : Fin m → k) :
    gramForm h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (pad u) (isoVec ι) = 0 := by
  simp [hform_apply, isoVec, pad, Fin.sum_univ_succ]

theorem pad_add (u u' : Fin m → k) : pad (u + u') = pad u + pad u' := by
  ext a
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun j => ?_) a) a <;> simp [pad]

theorem pad_zero : pad (0 : Fin m → k) = 0 := by
  ext a
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun j => ?_) a) a <;> simp [pad]

theorem hform_symm : (gramForm h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k)).IsSymm :=
  gramForm_isSymm h₀ (by simp)

noncomputable def eich (ι : k) (u : Fin m → k) (c : k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k :=
  eichlerMatrix h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (isoVec ι) (pad u) c

theorem eich_mul {ι : k} (hι : h₀.norm ι = -1) (u u' : Fin m → k) (c c' : k) :
    eich h₀ ι u c * eich h₀ ι u' c' =
      eich h₀ ι (u + u') (c + c' - ∑ j, h₀.bar (u j) * u' j) := by
  have hww := hform_isoVec_isoVec h₀ (m := m) hι
  have hwy := hform_isoVec_pad h₀ (m := m) ι
  have hyw := hform_pad_isoVec h₀ (m := m) ι
  refine sub_eq_zero.mp (eq_zero_of_forall_mulVec_eq_zero fun v => ?_)
  rw [sub_mulVec, ← mulVec_mulVec]
  simp only [eich, eichlerMatrix_mulVec, pad_add]
  have e1 : gramForm h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (isoVec ι)
      (v + gramForm h₀ 1 (isoVec ι) v • pad u' - gramForm h₀ 1 (pad u') v • isoVec ι +
        (c' * gramForm h₀ 1 (isoVec ι) v) • isoVec ι) = gramForm h₀ 1 (isoVec ι) v := by
    simp [map_add, map_sub, map_smul, hww, hwy]
  have e2 : gramForm h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (pad u)
      (v + gramForm h₀ 1 (isoVec ι) v • pad u' - gramForm h₀ 1 (pad u') v • isoVec ι +
        (c' * gramForm h₀ 1 (isoVec ι) v) • isoVec ι) =
        gramForm h₀ 1 (pad u) v + gramForm h₀ 1 (isoVec ι) v * ∑ j, h₀.bar (u j) * u' j := by
    simp [map_add, map_sub, map_smul, hyw, hform_pad]
  rw [e1, e2, map_add, LinearMap.add_apply]
  rw [sub_eq_zero]
  module

theorem eich_zero (ι : k) : eich h₀ ι (0 : Fin m → k) 0 = 1 := by
  have h0 : gramRow h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) 0 = 0 := by
    simp only [gramRow, Pi.zero_apply, map_zero]
    exact zero_vecMul _
  simp [eich, eichlerMatrix, pad_zero, h0]

theorem eich_sub_one_pow_three {ι : k} (hι : h₀.norm ι = -1) (u : Fin m → k) (c : k) :
    (eich h₀ ι u c - 1) ^ 3 = 0 :=
  eichlerMatrix_sub_one_pow_three (hform_symm h₀) (hform_isoVec_isoVec h₀ hι)
    (hform_isoVec_pad h₀ ι u) c

noncomputable def eichSU {ι : k} (hι : h₀.norm ι = -1) (u : Fin m → k) (c : k)
    (hc : c + h₀.bar c = -∑ j, h₀.bar (u j) * u j) :
    gramSU h₀ ((1 : GL (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k) :=
  ⟨unipotentGL (eich h₀ ι u c) (eich_sub_one_pow_three h₀ hι u c),
    eichlerGL_mem (hform_symm h₀) (hform_isoVec_isoVec h₀ hι) (hform_isoVec_pad h₀ ι u)
      (by rw [hform_pad]; exact hc)⟩

theorem trace_add {u u' : Fin m → k} {c c' : k} (hc : c + h₀.bar c = -∑ j, h₀.bar (u j) * u j)
    (hc' : c' + h₀.bar c' = -∑ j, h₀.bar (u' j) * u' j) :
    (c + c' - ∑ j, h₀.bar (u j) * u' j) + h₀.bar (c + c' - ∑ j, h₀.bar (u j) * u' j) =
      -∑ j, h₀.bar ((u + u') j) * (u + u') j := by
  simp only [map_sub, map_add, map_sum, map_mul, UnitaryFieldData.bar_bar, Pi.add_apply]
  have : ∑ j, (h₀.bar (u j) + h₀.bar (u' j)) * (u j + u' j) =
      ∑ j, h₀.bar (u j) * u j + ∑ j, h₀.bar (u' j) * u' j + ∑ j, h₀.bar (u j) * u' j +
        ∑ j, u j * h₀.bar (u' j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  linear_combination hc + hc'

variable {h₀} in
theorem eichSU_ext {ι : k} (hι : h₀.norm ι = -1) {u u' : Fin m → k} {c c' : k}
    (hc : c + h₀.bar c = -∑ j, h₀.bar (u j) * u j)
    (hc' : c' + h₀.bar c' = -∑ j, h₀.bar (u' j) * u' j) (h : eich h₀ ι u c = eich h₀ ι u' c') :
    eichSU h₀ hι u c hc = eichSU h₀ hι u' c' hc' :=
  Subtype.ext (Units.ext h)

theorem eichSU_mul {ι : k} (hι : h₀.norm ι = -1) {u u' : Fin m → k} {c c' : k}
    (hc : c + h₀.bar c = -∑ j, h₀.bar (u j) * u j)
    (hc' : c' + h₀.bar c' = -∑ j, h₀.bar (u' j) * u' j) :
    eichSU h₀ hι u c hc * eichSU h₀ hι u' c' hc' =
      eichSU h₀ hι (u + u') (c + c' - ∑ j, h₀.bar (u j) * u' j) (trace_add h₀ hc hc') :=
  Subtype.ext (Units.ext (eich_mul h₀ hι u u' c c'))

theorem eichSU_zero {ι : k} (hι : h₀.norm ι = -1) :
    eichSU h₀ hι (0 : Fin m → k) 0 (by simp) = 1 :=
  Subtype.ext (Units.ext (eich_zero h₀ ι))

theorem eichSU_inv {ι : k} (hι : h₀.norm ι = -1) {u : Fin m → k} {c : k}
    (hc : c + h₀.bar c = -∑ j, h₀.bar (u j) * u j) :
    (eichSU h₀ hι u c hc)⁻¹ = eichSU h₀ hι (-u) (h₀.bar c) (by
      simp only [Pi.neg_apply, map_neg, neg_mul_neg, UnitaryFieldData.bar_bar]
      rw [add_comm]
      exact hc) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [eichSU_mul h₀ hι hc]
  have h0 : (u + -u : Fin m → k) = 0 := add_neg_cancel u
  have h1 : (c + h₀.bar c - ∑ j, h₀.bar (u j) * (-u) j) = 0 := by
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
    rw [hc]
    ring
  exact (eichSU_ext hι _ (by simp) (by rw [h0, h1])).trans (eichSU_zero h₀ hι)

theorem exists_norm_neg_one : ∃ ι : k, h₀.norm ι = -1 := by
  obtain ⟨ι, hι⟩ := h₀.normHom_surjective ⟨-1, neg_mem (one_mem _)⟩
  exact ⟨ι, by simpa using congrArg Subtype.val hι⟩

theorem exists_trace_eq_one : ∃ κ : k, κ + h₀.bar κ = 1 := by
  obtain ⟨x, hx⟩ : ∃ x : k, x + h₀.bar x ≠ 0 := by
    by_contra hz
    push Not at hz
    obtain ⟨c, hc⟩ := h₀.exists_bar_ne
    have h1 := hz 1
    have h2 := hz c
    rw [map_one] at h1
    exact hc (by linear_combination h2 - c * h1)
  have hreal : h₀.bar (x + h₀.bar x) = x + h₀.bar x := by
    rw [map_add, UnitaryFieldData.bar_bar, add_comm]
  refine ⟨x / (x + h₀.bar x), ?_⟩
  rw [map_div₀, hreal, ← add_div, div_self hx]

theorem real_trace {κ s : k} (hκ : κ + h₀.bar κ = 1) (hs : h₀.bar s = s) :
    -(κ * s) + h₀.bar (-(κ * s)) = -s := by
  rw [map_neg, map_mul, hs]
  linear_combination (-s) * hκ

theorem bar_real (t : h₀.fixedField) : h₀.bar (t : k) = t := h₀.mem_fixedField.mp t.2

section Heis

variable {h₀} {ι : k} (hι : h₀.norm ι = -1) (m : ℕ)

noncomputable def realEichSub :
    Subgroup (gramSU h₀ ((1 : GL (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k)) where
  carrier := {g | ∃ (v : Fin m → h₀.fixedField) (c : k)
    (hc : c + h₀.bar c = -∑ j, h₀.bar ((v j : h₀.fixedField) : k) * ((v j : h₀.fixedField) : k)),
    g = eichSU h₀ hι (fun j => ((v j : h₀.fixedField) : k)) c hc}
  mul_mem' := by
    rintro g g' ⟨v, c, hc, rfl⟩ ⟨v', c', hc', rfl⟩
    exact ⟨v + v', _, trace_add h₀ hc hc', eichSU_mul h₀ hι hc hc'⟩
  one_mem' := ⟨0, 0, by simp, (eichSU_zero h₀ hι).symm⟩
  inv_mem' := by
    rintro g ⟨v, c, hc, rfl⟩
    refine ⟨-v, h₀.bar c, ?_, eichSU_inv h₀ hι hc⟩
    simp only [Pi.neg_apply, Subfield.coe_neg, map_neg, neg_mul_neg, UnitaryFieldData.bar_bar]
    rw [add_comm]
    exact hc

variable {m}

theorem real_sum_comm (v v' : Fin m → h₀.fixedField) :
    ∑ j, h₀.bar ((v j : h₀.fixedField) : k) * ((v' j : h₀.fixedField) : k) =
      ∑ j, h₀.bar ((v' j : h₀.fixedField) : k) * ((v j : h₀.fixedField) : k) := by
  refine Finset.sum_congr rfl fun j => ?_
  intro _
  rw [bar_real, bar_real]
  ring

theorem realEichSub_comm (g g' : realEichSub hι m) : g * g' = g' * g := by
  obtain ⟨g, v, c, hc, rfl⟩ := g
  obtain ⟨g', v', c', hc', rfl⟩ := g'
  refine Subtype.ext ?_
  show eichSU h₀ hι _ c hc * eichSU h₀ hι _ c' hc' = eichSU h₀ hι _ c' hc' * eichSU h₀ hι _ c hc
  rw [eichSU_mul h₀ hι hc hc', eichSU_mul h₀ hι hc' hc]
  refine eichSU_ext hι _ _ ?_
  have e1 : ((fun j => ((v j : h₀.fixedField) : k)) + fun j => ((v' j : h₀.fixedField) : k)) =
      ((fun j => ((v' j : h₀.fixedField) : k)) + fun j => ((v j : h₀.fixedField) : k)) :=
    add_comm _ _
  have e2 : c + c' - ∑ j, h₀.bar ((v j : h₀.fixedField) : k) * ((v' j : h₀.fixedField) : k) =
      c' + c - ∑ j, h₀.bar ((v' j : h₀.fixedField) : k) * ((v j : h₀.fixedField) : k) := by
    rw [real_sum_comm v v']
    ring
  rw [e1, e2]

theorem eichSU_pow_char_sq [Fact ℓ.Prime] [CharP k ℓ] {u : Fin m → k} {c : k}
    (hc : c + h₀.bar c = -∑ j, h₀.bar (u j) * u j) :
    (eichSU h₀ hι u c hc) ^ (ℓ ^ 2) = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have h1 : eich h₀ ι u c = 1 + (eich h₀ ι u c - 1) := by abel
  have h2 : ((eichSU h₀ hι u c hc : gramSU h₀ ((1 : GL (Fin (m + 2)) k) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) k)) : GL (Fin (m + 2)) k).val = eich h₀ ι u c := rfl
  rw [h2, h1, add_pow_char_pow_of_commute ℓ 2 (Commute.one_left _), one_pow]
  have h3 : (eich h₀ ι u c - 1) ^ (ℓ ^ 2) = 0 := by
    refine pow_eq_zero_of_le ?_ (eich_sub_one_pow_three h₀ hι u c)
    have := h₀.prime.two_le
    nlinarith
  rw [h3, add_zero]
  rfl

theorem realEichSub_isPGroup [Fact ℓ.Prime] [CharP k ℓ] : IsPGroup ℓ (realEichSub hι m) := by
  rintro ⟨g, v, c, hc, rfl⟩
  refine ⟨2, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow]
  exact eichSU_pow_char_sq hι hc

section Zeta

variable {κ₀ : k} (hκ₀ : h₀.bar κ₀ = -κ₀)

noncomputable def zetaEl (t : h₀.fixedField) :
    gramSU h₀ ((1 : GL (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k) :=
  eichSU h₀ hι (0 : Fin m → k) (κ₀ * t) (by
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, neg_zero, map_mul, hκ₀,
      bar_real]
    ring)

theorem zetaEl_add (t t' : h₀.fixedField) :
    zetaEl (m := m) hι hκ₀ (t + t') = zetaEl hι hκ₀ t * zetaEl hι hκ₀ t' := by
  unfold zetaEl
  rw [eichSU_mul h₀ hι]
  refine eichSU_ext hι _ _ ?_
  simp [mul_add]

theorem zetaEl_zero : zetaEl (m := m) hι hκ₀ 0 = 1 := by
  unfold zetaEl
  rw [← eichSU_zero h₀ hι (m := m)]
  refine eichSU_ext hι _ _ ?_
  simp

noncomputable def zetaSub :
    Subgroup (gramSU h₀ ((1 : GL (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k)) :=
  (MonoidHom.mk' (fun t : Multiplicative h₀.fixedField =>
    zetaEl (m := m) hι hκ₀ (Multiplicative.toAdd t))
    (fun a b => zetaEl_add hι hκ₀ (Multiplicative.toAdd a) (Multiplicative.toAdd b))).range

theorem zetaEl_mem (t : h₀.fixedField) : zetaEl (m := m) hι hκ₀ t ∈ zetaSub hι hκ₀ :=
  ⟨Multiplicative.ofAdd t, rfl⟩

theorem exists_of_mem_zetaSub {g : gramSU h₀ ((1 : GL (Fin (m + 2)) k) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) k)} (hg : g ∈ zetaSub hι hκ₀) :
    ∃ t, zetaEl (m := m) hι hκ₀ t = g := by
  obtain ⟨y, rfl⟩ := hg
  exact ⟨Multiplicative.toAdd y, rfl⟩

theorem zetaSub_le : zetaSub (m := m) hι hκ₀ ≤ realEichSub hι m := by
  intro g hg
  obtain ⟨t, rfl⟩ := exists_of_mem_zetaSub hι hκ₀ hg
  refine ⟨0, κ₀ * t, ?_, rfl⟩
  simp only [Pi.zero_apply, ZeroMemClass.coe_zero, map_zero, zero_mul, Finset.sum_const_zero,
    neg_zero, map_mul, hκ₀, bar_real]
  ring

end Zeta

theorem bar_bar_sub_self (ι₁ : k) : h₀.bar (h₀.bar ι₁ - ι₁) = -(h₀.bar ι₁ - ι₁) := by
  rw [map_sub, UnitaryFieldData.bar_bar]
  ring

theorem sum_single_real (t : h₀.fixedField) (j : Fin m) :
    ∑ i, h₀.bar (((Pi.single j t : Fin m → h₀.fixedField) i : h₀.fixedField) : k) *
      (((Pi.single j t : Fin m → h₀.fixedField) i : h₀.fixedField) : k) = (t : k) * (t : k) := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, bar_real]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

section Y

variable {ι₁ κ : k} (hκ : κ + h₀.bar κ = 1)

noncomputable def yEl (v : Fin m → h₀.fixedField) :
    gramSU h₀ ((1 : GL (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k) :=
  eichSU h₀ hι (fun j => ι₁ * ((v j : h₀.fixedField) : k))
    (-(κ * (h₀.norm ι₁ * ∑ j, ((v j : h₀.fixedField) : k) * ((v j : h₀.fixedField) : k))))
    (by
      have hs : h₀.bar (h₀.norm ι₁ *
          ∑ j, ((v j : h₀.fixedField) : k) * ((v j : h₀.fixedField) : k)) =
          h₀.norm ι₁ * ∑ j, ((v j : h₀.fixedField) : k) * ((v j : h₀.fixedField) : k) := by
        rw [map_mul, map_sum, h₀.mem_fixedField.mp (h₀.norm_mem_fixedField ι₁)]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, bar_real]
      rw [real_trace h₀ hκ hs, neg_inj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, bar_real]
      simp only [UnitaryFieldData.norm]
      ring)

noncomputable def aEl (t : h₀.fixedField) (j : Fin m) :
    gramSU h₀ ((1 : GL (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k) :=
  eichSU h₀ hι
    (fun i => (((Pi.single j t : Fin m → h₀.fixedField) i : h₀.fixedField) : k))
    (-(κ * ((t : k) * (t : k)))) (by
      have hs : h₀.bar ((t : k) * (t : k)) = (t : k) * (t : k) := by rw [map_mul, bar_real]
      rw [real_trace h₀ hκ hs, neg_inj, sum_single_real])

theorem aEl_mem (t : h₀.fixedField) (j : Fin m) : aEl (m := m) hι hκ t j ∈ realEichSub hι m :=
  ⟨Pi.single j t, _, _, rfl⟩

theorem commutator_inv_eq_of_mul_eq {G : Type*} [Group G] {x g z : G}
    (h : g * x = x * (z * g)) : ⁅x⁻¹, g⁆ = z := by
  rw [commutatorElement_def, inv_inv]
  calc x⁻¹ * g * x * g⁻¹ = x⁻¹ * (g * x) * g⁻¹ := by group
    _ = x⁻¹ * (x * (z * g)) * g⁻¹ := by rw [h]
    _ = z := by group

theorem comm_y_eich (v v' : Fin m → h₀.fixedField) {c' : k}
    (hc' : c' + h₀.bar c' =
      -∑ j, h₀.bar ((v' j : h₀.fixedField) : k) * ((v' j : h₀.fixedField) : k)) :
    ⁅(yEl (m := m) hι hκ (ι₁ := ι₁) v)⁻¹,
        eichSU h₀ hι (fun j => ((v' j : h₀.fixedField) : k)) c' hc'⁆ =
      zetaEl (m := m) hι (bar_bar_sub_self (h₀ := h₀) ι₁) (∑ i, v i * v' i) := by
  have key : eichSU h₀ hι (fun j => ((v' j : h₀.fixedField) : k)) c' hc' *
      yEl hι hκ (ι₁ := ι₁) v = yEl hι hκ (ι₁ := ι₁) v *
        (zetaEl hι (bar_bar_sub_self (h₀ := h₀) ι₁) (∑ i, v i * v' i) *
          eichSU h₀ hι (fun j => ((v' j : h₀.fixedField) : k)) c' hc') := by
    unfold yEl zetaEl
    rw [eichSU_mul h₀ hι, eichSU_mul h₀ hι, eichSU_mul h₀ hι]
    refine eichSU_ext hι _ _ ?_
    congr 1
    · rw [zero_add]
      exact add_comm _ _
    · have h1 : ∑ j, h₀.bar (((v' j : h₀.fixedField) : k)) * (ι₁ * ((v j : h₀.fixedField) : k)) =
          ι₁ * ∑ j, ((v j : h₀.fixedField) : k) * ((v' j : h₀.fixedField) : k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [bar_real]
        ring
      have h2 : ∑ j, h₀.bar (ι₁ * ((v j : h₀.fixedField) : k)) *
          ((0 : Fin m → k) + fun j => ((v' j : h₀.fixedField) : k)) j =
          h₀.bar ι₁ * ∑ j, ((v j : h₀.fixedField) : k) * ((v' j : h₀.fixedField) : k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.add_apply, Pi.zero_apply, zero_add, map_mul, bar_real]
        ring
      have h3 : ∑ j, h₀.bar ((0 : Fin m → k) j) * ((v' j : h₀.fixedField) : k) = 0 := by simp
      have h4 : (((∑ i, v i * v' i : h₀.fixedField)) : k) =
          ∑ j, ((v j : h₀.fixedField) : k) * ((v' j : h₀.fixedField) : k) := by
        push_cast
        rfl
      rw [h1, h2, h3, h4]
      ring
  exact commutator_inv_eq_of_mul_eq key

theorem zetaEl_one_not_scalar {κ₀ : k} (hκ₀ : h₀.bar κ₀ = -κ₀) (hκ₀ne : κ₀ ≠ 0) (hι0 : ι ≠ 0) :
    zetaEl (m := m) hι hκ₀ 1 ∉ normOneScalars h₀
      (gramSU h₀ ((1 : GL (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k)) (m + 2) := by
  rintro ⟨c, -, -, hc⟩
  have h1 := congrArg
    (fun g : GL (Fin (m + 2)) k => (g : Matrix (Fin (m + 2)) (Fin (m + 2)) k) 1 0) hc
  have h2 : (((zetaEl (m := m) hι hκ₀ 1 : gramSU h₀ ((1 : GL (Fin (m + 2)) k) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) k)) : GL (Fin (m + 2)) k) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) k) = eich h₀ ι (0 : Fin m → k) (κ₀ * (1 : k)) := rfl
  simp only [h2] at h1
  have h0 : gramRow h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) 0 = 0 := by
    simp only [gramRow, Pi.zero_apply, map_zero]
    exact zero_vecMul _
  have h3 : gramRow h₀ (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (isoVec ι) 0 = 1 := by
    simp [gramRow, isoVec, vecMul, dotProduct, Matrix.one_apply]
  have h4 : (isoVec ι : Fin (m + 2) → k) 1 = ι := by simp [isoVec]
  rw [GeneralLinearGroup.coe_scalar] at h1
  simp [eich, eichlerMatrix, pad_zero, h0, h3, h4, Matrix.vecMulVec_apply] at h1
  rcases h1 with h | h
  · exact hκ₀ne h
  · exact hι0 h

end Y

end Heis

theorem sum_mul_single (v : Fin m → h₀.fixedField) (t : h₀.fixedField) (j : Fin m) :
    ∑ i, v i * (Pi.single j t : Fin m → h₀.fixedField) i = t * v j := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_comm]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem unitary_heisenberg_system_add_two (m : ℕ) : UnitaryHeisenbergSystem h₀ (m + 2) := by
  classical
  have hfin : Finite k := h₀.finite
  have : Fact ℓ.Prime := ⟨h₀.prime⟩
  have : CharP k ℓ := h₀.charP
  obtain ⟨ι, hι⟩ := exists_norm_neg_one h₀
  obtain ⟨ι₁, hι₁⟩ := h₀.exists_bar_ne
  obtain ⟨κ, hκ⟩ := exists_trace_eq_one h₀
  have hκ₀ := bar_bar_sub_self (h₀ := h₀) ι₁
  have hκ₀ne : h₀.bar ι₁ - ι₁ ≠ 0 := sub_ne_zero.mpr hι₁
  have hι0 : ι ≠ 0 := by
    rintro rfl
    simp [UnitaryFieldData.norm] at hι
  have : Finite h₀.fixedField := inferInstance
  refine ⟨realEichSub hι m, zetaSub hι hκ₀, Fin m → h₀.fixedField, yEl hι hκ (ι₁ := ι₁),
    inferInstance, inferInstance, ⟨⟨realEichSub_comm hι⟩⟩, realEichSub_isPGroup hι,
    zetaSub_le hι hκ₀, ?_, ?_, ⟨zetaEl hι hκ₀ 1, zetaEl_mem hι hκ₀ 1,
      zetaEl_one_not_scalar hι hκ₀ hκ₀ne hι0⟩, ?_⟩
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
      h₀.card_fixedField, ← pow_mul, Nat.add_sub_cancel]
  · intro v g hg
    obtain ⟨v', c', hc', rfl⟩ := hg
    rw [comm_y_eich hι hκ v v' hc']
    exact zetaEl_mem hι hκ₀ _
  · intro s hs F _ _ ξ hmul hne0 hnt i j hij
    refine hdist_of_pairing (zetaSub hι hκ₀) (realEichSub hι m) (zetaEl hι hκ₀)
      (zetaEl_add hι hκ₀) (zetaEl_mem hι hκ₀) (fun z hz => exists_of_mem_zetaSub hι hκ₀ hz)
      (yEl hι hκ (ι₁ := ι₁)) (aEl hι hκ) (aEl_mem hι hκ) ?_ ξ hmul hne0 hnt i j hij
    intro v t j
    have := comm_y_eich hι hκ (ι₁ := ι₁) v (Pi.single j t)
      (c' := -(κ * ((t : k) * (t : k)))) (by
        have hs : h₀.bar ((t : k) * (t : k)) = (t : k) * (t : k) := by rw [map_mul, bar_real]
        rw [real_trace h₀ hκ hs, neg_inj, sum_single_real])
    rw [sum_mul_single] at this
    exact this

end Vectors

theorem unitary_heisenberg_system {ℓ e : ℕ} {k : Type} [Field k] (h₀ : UnitaryFieldData ℓ e k)
    {n : ℕ} (hn : 2 ≤ n) : UnitaryHeisenbergSystem h₀ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact unitary_heisenberg_system_add_two h₀ m

theorem nonLocalized_unitarySubfield {ℓ f e n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {k : Subfield K} (h₀ : UnitaryFieldData ℓ e k)
    (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (hn : 3 ≤ n) (hq₀ : ¬(n = 3 ∧ ℓ ^ e = 2)) :
    NonLocalized (subfieldPSU h h₀ hbar n).range :=
  nonLocalized_unitarySubfield_of_system h h₀ hbar hn hq₀
    (unitary_heisenberg_system h₀ (by omega))

end CFSG.SignalizerFunctorTheorem.NonLocal
