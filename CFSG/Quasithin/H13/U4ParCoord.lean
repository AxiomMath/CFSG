module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

abbrev Ix : Type := HypIndex 2 0

@[expose] def ie1 : Ix := .inl 0

@[expose] def ie2 : Ix := .inl 1

@[expose] def if1 : Ix := .inr (.inr 0)

@[expose] def if2 : Ix := .inr (.inr 1)

@[simp] theorem ie1_ne_ie2 : ie1 ≠ ie2 := by decide
@[simp] theorem ie1_ne_if1 : ie1 ≠ if1 := by decide
@[simp] theorem ie1_ne_if2 : ie1 ≠ if2 := by decide
@[simp] theorem ie2_ne_ie1 : ie2 ≠ ie1 := by decide
@[simp] theorem ie2_ne_if1 : ie2 ≠ if1 := by decide
@[simp] theorem ie2_ne_if2 : ie2 ≠ if2 := by decide
@[simp] theorem if1_ne_ie1 : if1 ≠ ie1 := by decide
@[simp] theorem if1_ne_ie2 : if1 ≠ ie2 := by decide
@[simp] theorem if1_ne_if2 : if1 ≠ if2 := by decide
@[simp] theorem if2_ne_ie1 : if2 ≠ ie1 := by decide
@[simp] theorem if2_ne_ie2 : if2 ≠ ie2 := by decide
@[simp] theorem if2_ne_if1 : if2 ≠ if1 := by decide

@[simp] theorem hypPartner_ie1 : hypPartner ie1 = if1 := rfl
@[simp] theorem hypPartner_ie2 : hypPartner ie2 = if2 := rfl
@[simp] theorem hypPartner_if1 : hypPartner if1 = ie1 := rfl
@[simp] theorem hypPartner_if2 : hypPartner if2 = ie2 := rfl

@[simp] theorem fullPos_ie1 : fullPos ie1 = 0 := rfl
@[simp] theorem fullPos_ie2 : fullPos ie2 = 1 := rfl
@[simp] theorem fullPos_if1 : fullPos if1 = 3 := rfl
@[simp] theorem fullPos_if2 : fullPos if2 = 2 := rfl

theorem ix_cases (a : Ix) : a = ie1 ∨ a = ie2 ∨ a = if1 ∨ a = if2 := by
  rcases a with i | k | i
  · fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact k.elim0
  · fin_cases i
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem sum_ix {M : Type*} [AddCommMonoid M] (g : Ix → M) :
    ∑ a, g a = g ie1 + g ie2 + g if1 + g if2 := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Finset.univ_eq_empty, Finset.sum_empty,
    zero_add, ie1, ie2, if1, if2]
  abel

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

@[expose] noncomputable def sMat (x y c : K) : Matrix Ix Ix K :=
  1 + single ie1 if1 c + single ie2 if1 x + single if2 if1 y + single ie1 ie2 (h.bar y) +
    single ie1 if2 (h.bar x)

theorem sMat_apply (x y c : K) (i j : Ix) :
    sMat h x y c i j = (1 : Matrix Ix Ix K) i j + (if ie1 = i ∧ if1 = j then c else 0) +
      (if ie2 = i ∧ if1 = j then x else 0) + (if if2 = i ∧ if1 = j then y else 0) +
      (if ie1 = i ∧ ie2 = j then h.bar y else 0) + (if ie1 = i ∧ if2 = j then h.bar x else 0) := by
  simp only [sMat, Matrix.add_apply, Matrix.single_apply]

theorem sMat_mul (x y c x' y' c' : K) :
    sMat h x y c * sMat h x' y' c' =
      sMat h (x + x') (y + y') (c + c' + (h.bar y * x' + h.bar x * y')) := by
  ext i j
  rw [mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, ie1, ie2, if1, if2, map_add] <;> ring

theorem sMat_eq_one_add (x y c : K) :
    sMat h x y c = 1 + (single ie1 if1 c + single ie2 if1 x + single if2 if1 y +
      single ie1 ie2 (h.bar y) + single ie1 if2 (h.bar x)) := by
  simp only [sMat, add_assoc]

theorem sNil_pow_three (x y c : K) :
    (single ie1 if1 c + single ie2 if1 x + single if2 if1 y + single ie1 ie2 (h.bar y) +
      single ie1 if2 (h.bar x) : Matrix Ix Ix K) ^ 3 = 0 := by
  ext i j
  rw [pow_succ, pow_two, mul_apply, sum_ix]
  simp only [mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [Matrix.add_apply, ie1, ie2, if1, if2]

theorem det_sMat (x y c : K) : (sMat h x y c).det = 1 := by
  have := h.charP
  rw [sMat_eq_one_add]
  exact CFSG.LieType.BorelTits.det_one_add_of_isNilpotent 2 ⟨3, sNil_pow_three h x y c⟩

theorem sMat_gram {x y c : K} (hc : c + h.bar c = h.bar x * y + h.bar y * x) :
    ((sMat h x y c).map h.bar)ᵀ * hypGram 2 0 K * sMat h x y c = hypGram 2 0 K := by
  have := h.charP
  ext i j
  rw [mul_apply, sum_ix]
  simp only [mul_hypGram_apply, transpose_apply, map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, hypGram_apply, hypPartner, ie1, ie2, if1, if2, h.bar_bar] <;>
    grind

@[expose] def SAdm (x y c : K) : Prop := c + h.bar c = h.bar x * y + h.bar y * x

theorem sMat_mul_bar {x y c : K} (hc : SAdm h x y c) : sMat h x y c * sMat h x y (h.bar c) = 1 := by
  have := h.charP
  rw [sMat_mul]
  have hx : x + x = 0 := CharTwo.add_self_eq_zero x
  have hy : y + y = 0 := CharTwo.add_self_eq_zero y
  have hcc : c + h.bar c + (h.bar y * x + h.bar x * y) = 0 := by
    rw [hc]; grind
  rw [hx, hy, hcc]
  ext i j
  simp [sMat_apply, map_zero]

theorem sMat_bar_mul {x y c : K} (hc : SAdm h x y c) : sMat h x y (h.bar c) * sMat h x y c = 1 := by
  have := h.charP
  rw [sMat_mul]
  have hx : x + x = 0 := CharTwo.add_self_eq_zero x
  have hy : y + y = 0 := CharTwo.add_self_eq_zero y
  have hcc : h.bar c + c + (h.bar y * x + h.bar x * y) = 0 := by
    rw [add_comm (h.bar c), hc]; grind
  rw [hx, hy, hcc]
  ext i j
  simp [sMat_apply, map_zero]

@[expose] noncomputable def sElt {x y c : K} (hc : SAdm h x y c) : hypSU h 2 0 :=
  ⟨⟨sMat h x y c, sMat h x y (h.bar c), sMat_mul_bar h hc, sMat_bar_mul h hc⟩,
    mem_gramSU.mpr ⟨sMat_gram h hc, det_sMat h x y c⟩⟩

theorem coe_sElt {x y c : K} (hc : SAdm h x y c) :
    (((sElt h hc : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h x y c :=
  rfl

theorem SAdm.mul {x y c x' y' c' : K} (hc : SAdm h x y c) (hc' : SAdm h x' y' c') :
    SAdm h (x + x') (y + y') (c + c' + (h.bar y * x' + h.bar x * y')) := by
  have := h.charP
  unfold SAdm at *
  simp only [map_add, map_mul, h.bar_bar]
  grind

@[expose] noncomputable def radQ : Subgroup (hypSU h 2 0) where
  carrier := {g | ∃ x y c : K, SAdm h x y c ∧
    ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c}
  mul_mem' := by
    rintro g g' ⟨x, y, c, hc, hg⟩ ⟨x', y', c', hc', hg'⟩
    refine ⟨_, _, _, hc.mul h hc', ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hg, hg', sMat_mul]
  one_mem' := ⟨0, 0, 0, by simp [SAdm], by ext i j; simp [sMat_apply]⟩
  inv_mem' := by
    rintro g ⟨x, y, c, hc, hg⟩
    refine ⟨x, y, h.bar c, ?_, ?_⟩
    · have := h.charP
      unfold SAdm at *
      rw [h.bar_bar, add_comm, hc]
    · have h1 : ((g : GL Ix K) : Matrix Ix Ix K) * sMat h x y (h.bar c) = 1 := by
        rw [hg, sMat_mul_bar h hc]
      exact Units.inv_eq_of_mul_eq_one_right h1

theorem mem_radQ {g : hypSU h 2 0} :
    g ∈ radQ h ↔ ∃ x y c : K, SAdm h x y c ∧ ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c :=
  Iff.rfl

theorem sElt_mem_radQ {x y c : K} (hc : SAdm h x y c) : sElt h hc ∈ radQ h :=
  ⟨x, y, c, hc, rfl⟩

theorem hypSU_ext {g g' : hypSU h 2 0}
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = ((g' : GL Ix K) : Matrix Ix Ix K)) : g = g' :=
  Subtype.ext (Units.ext hg)

theorem coe_mul_hypSU (g g' : hypSU h 2 0) :
    (((g * g' : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      ((g : GL Ix K) : Matrix Ix Ix K) * ((g' : GL Ix K) : Matrix Ix Ix K) :=
  rfl

theorem sMat_ie2_if1 (x y c : K) : sMat h x y c ie2 if1 = x := by
  simp [sMat_apply, one_apply, ie1, ie2, if1, if2]

theorem sMat_if2_if1 (x y c : K) : sMat h x y c if2 if1 = y := by
  simp [sMat_apply, one_apply, ie1, ie2, if1, if2]

theorem sMat_ie1_if1 (x y c : K) : sMat h x y c ie1 if1 = c := by
  simp [sMat_apply, one_apply, ie1, ie2, if1, if2]

theorem sMat_injective {x y c x' y' c' : K} (hs : sMat h x y c = sMat h x' y' c') :
    x = x' ∧ y = y' ∧ c = c' := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun (congrFun hs ie2) if1
    rwa [sMat_ie2_if1, sMat_ie2_if1] at this
  · have := congrFun (congrFun hs if2) if1
    rwa [sMat_if2_if1, sMat_if2_if1] at this
  · have := congrFun (congrFun hs ie1) if1
    rwa [sMat_ie1_if1, sMat_ie1_if1] at this

@[expose] noncomputable def radPhi : radQ h →* Multiplicative (K × K) where
  toFun g := Multiplicative.ofAdd ((((g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie2 if1,
    (((g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) if2 if1)
  map_one' := by
    simp [one_apply, ie2, if1, if2]
  map_mul' g g' := by
    obtain ⟨x, y, c, -, hg⟩ := g.2
    obtain ⟨x', y', c', -, hg'⟩ := g'.2
    simp only [Subgroup.coe_mul, Units.val_mul, hg, hg', sMat_mul, sMat_ie2_if1, sMat_if2_if1]
    rfl

theorem radPhi_apply {g : radQ h} {x y c : K}
    (hg : (((g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) :
    radPhi h g = Multiplicative.ofAdd (x, y) := by
  simp only [radPhi, MonoidHom.coe_mk, OneHom.coe_mk, hg, sMat_ie2_if1, sMat_if2_if1]

theorem sAdm_zero_zero_iff {c : K} : SAdm h 0 0 c ↔ h.bar c = c := by
  have := h.charP
  unfold SAdm
  simp only [map_zero, mul_zero, add_zero]
  constructor
  · intro hc
    have : h.bar c = -c := eq_neg_of_add_eq_zero_right hc
    rw [this, CharTwo.neg_eq]
  · intro hc
    rw [hc, CharTwo.add_self_eq_zero]

@[expose] noncomputable def zRad : Subgroup (hypSU h 2 0) where
  carrier := {g | ∃ c : K, h.bar c = c ∧ ((g : GL Ix K) : Matrix Ix Ix K) = sMat h 0 0 c}
  mul_mem' := by
    rintro g g' ⟨c, hc, hg⟩ ⟨c', hc', hg'⟩
    refine ⟨c + c', by rw [map_add, hc, hc'], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hg, hg', sMat_mul]
    simp
  one_mem' := ⟨0, map_zero _, by ext i j; simp [sMat_apply]⟩
  inv_mem' := by
    rintro g ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    have hadm : SAdm h 0 0 c := (sAdm_zero_zero_iff h).mpr hc
    have h1 : ((g : GL Ix K) : Matrix Ix Ix K) * sMat h 0 0 (h.bar c) = 1 := by
      rw [hg, sMat_mul_bar h hadm]
    rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_right h1, hc]

theorem zRad_le_radQ : zRad h ≤ radQ h := by
  rintro g ⟨c, hc, hg⟩
  exact ⟨0, 0, c, (sAdm_zero_zero_iff h).mpr hc, hg⟩

theorem sMat_zero_comm (c x y c' : K) :
    sMat h 0 0 c * sMat h x y c' = sMat h x y c' * sMat h 0 0 c := by
  rw [sMat_mul, sMat_mul]
  simp only [zero_add, add_zero, map_zero, zero_mul, mul_zero]
  rw [add_comm c c']

theorem zRad_le_centralizer : zRad h ≤ Subgroup.centralizer (radQ h : Set (hypSU h 2 0)) := by
  rintro z ⟨c, -, hz⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro g ⟨x, y, c', -, hg⟩
  apply hypSU_ext
  rw [coe_mul_hypSU, coe_mul_hypSU, hz, hg, sMat_zero_comm]

theorem commutator_sMat {x y c x' y' c' : K} (hc : SAdm h x y c) (hc' : SAdm h x' y' c') :
    sMat h x y c * sMat h x' y' c' * sMat h x y (h.bar c) * sMat h x' y' (h.bar c') =
      sMat h 0 0 (h.trace (h.bar y * x' + h.bar x * y')) := by
  have := h.charP
  simp only [sMat_mul]
  have e1 : x + x' + x + x' = 0 := by grind
  have e2 : y + y' + y + y' = 0 := by grind
  rw [e1, e2]
  congr 1
  unfold SAdm at hc hc'
  simp only [UnitaryFieldData.trace, map_add, map_mul, h.bar_bar]
  grind

theorem radQ_isPGroup : IsPGroup 2 (radQ h) := by
  intro g
  refine ⟨2, ?_⟩
  obtain ⟨x, y, c, -, hg⟩ := g.2
  apply Subtype.ext
  apply hypSU_ext
  have := h.charP
  have hx : x + x = 0 := CharTwo.add_self_eq_zero x
  have hy : y + y = 0 := CharTwo.add_self_eq_zero y
  change (((((g : hypSU h 2 0) ^ 4 : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)) = 1
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg]
  have hsq : sMat h x y c ^ 2 = sMat h 0 0 (h.bar y * x + h.bar x * y) := by
    rw [sq, sMat_mul, hx, hy]
    congr 1
    grind
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, sq, sMat_mul]
  simp only [add_zero, map_zero, mul_zero]
  have hz : h.bar y * x + h.bar x * y + (h.bar y * x + h.bar x * y) = 0 :=
    CharTwo.add_self_eq_zero _
  rw [hz]
  ext i j
  simp [sMat_apply]

theorem sAdm_x_zero (x : K) : SAdm h x 0 0 := by simp [SAdm]

theorem sAdm_zero_y (y : K) : SAdm h 0 y 0 := by simp [SAdm]

theorem mem_zRad_of_comm {g : hypSU h 2 0} (hg : g ∈ radQ h)
    (hcomm : ∀ g' ∈ radQ h, g * g' = g' * g) : g ∈ zRad h := by
  have := h.charP
  obtain ⟨x, y, c, hc, hgm⟩ := hg
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  have hx : ∀ t : K, h.bar y * t = h.bar t * y := by
    intro t
    have h1 := congrArg (fun g : hypSU h 2 0 => ((g : GL Ix K) : Matrix Ix Ix K))
      (hcomm _ (sElt_mem_radQ h (sAdm_x_zero h t)))
    simp only [coe_mul_hypSU, hgm, coe_sElt, sMat_mul] at h1
    have := (sMat_injective h h1).2.2
    simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add] at this
    grind
  have hy : ∀ t : K, h.bar x * t = h.bar t * x := by
    intro t
    have h1 := congrArg (fun g : hypSU h 2 0 => ((g : GL Ix K) : Matrix Ix Ix K))
      (hcomm _ (sElt_mem_radQ h (sAdm_zero_y h t)))
    simp only [coe_mul_hypSU, hgm, coe_sElt, sMat_mul] at h1
    have := (sMat_injective h h1).2.2
    simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add] at this
    grind
  have hy0 : y = 0 := by
    have h1 := hx 1
    have h2 := hx ω
    simp only [map_one, mul_one, one_mul] at h1
    rw [h1] at h2
    have : y * (ω - h.bar ω) = 0 := by rw [mul_sub, h2]; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0).symm hω
  have hx0 : x = 0 := by
    have h1 := hy 1
    have h2 := hy ω
    simp only [map_one, mul_one, one_mul] at h1
    rw [h1] at h2
    have : x * (ω - h.bar ω) = 0 := by rw [mul_sub, h2]; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0).symm hω
  subst hx0 hy0
  exact ⟨c, (sAdm_zero_zero_iff h).mp hc, hgm⟩

theorem centerOf_radQ : CFSG.Quasithin.centerOf (radQ h) = zRad h := by
  apply le_antisymm
  · rintro g ⟨hgQ, hgC⟩
    refine mem_zRad_of_comm h hgQ fun g' hg' => ?_
    exact (Subgroup.mem_centralizer_iff.mp hgC g' hg').symm
  · intro g hg
    exact ⟨zRad_le_radQ h hg, zRad_le_centralizer h hg⟩

theorem zRad_le_commutator : zRad h ≤ ⁅radQ h, radQ h⁆ := by
  have := h.charP
  rintro g ⟨c, hc, hg⟩
  obtain ⟨t, ht⟩ := h.traceLin_surjective ⟨c, (h.mem_fixedField).mpr hc⟩
  have ht' : h.trace t = c := congrArg Subtype.val ht
  set a := sElt h (sAdm_x_zero h 1)
  set b := sElt h (sAdm_zero_y h t)
  have hab : g = a * b * a⁻¹ * b⁻¹ := by
    apply hypSU_ext
    have hainv : (((a⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h 1 0 (h.bar 0) := by
      have h1 : ((a : GL Ix K) : Matrix Ix Ix K) * sMat h 1 0 (h.bar 0) = 1 :=
        sMat_mul_bar h (sAdm_x_zero h 1)
      rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_right h1]
    have hbinv : (((b⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h 0 t (h.bar 0) := by
      have h1 : ((b : GL Ix K) : Matrix Ix Ix K) * sMat h 0 t (h.bar 0) = 1 :=
        sMat_mul_bar h (sAdm_zero_y h t)
      rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_right h1]
    rw [coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, hainv, hbinv, coe_sElt, coe_sElt,
      commutator_sMat h (sAdm_x_zero h 1) (sAdm_zero_y h t), hg]
    congr 1
    rw [← ht']
    simp
  rw [hab]
  exact Subgroup.commutator_mem_commutator (sElt_mem_radQ h _) (sElt_mem_radQ h _)

theorem commutator_radQ : ⁅radQ h, radQ h⁆ = zRad h := by
  apply le_antisymm _ (zRad_le_commutator h)
  rw [Subgroup.commutator_le]
  rintro g ⟨x, y, c, hc, hg⟩ g' ⟨x', y', c', hc', hg'⟩
  have hginv : (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h x y (h.bar c) := by
    have h1 : ((g : GL Ix K) : Matrix Ix Ix K) * sMat h x y (h.bar c) = 1 := by
      rw [hg, sMat_mul_bar h hc]
    rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_right h1]
  have hg'inv : (((g'⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h x' y' (h.bar c') := by
    have h1 : ((g' : GL Ix K) : Matrix Ix Ix K) * sMat h x' y' (h.bar c') = 1 := by
      rw [hg', sMat_mul_bar h hc']
    rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_right h1]
  refine ⟨h.trace (h.bar y * x' + h.bar x * y'), ?_, ?_⟩
  · exact (h.mem_fixedField).mp (h.trace_mem_fixedField _)
  · rw [commutatorElement_def, coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, hginv, hg'inv, hg,
      hg', commutator_sMat h hc hc']

theorem card_zRad : Nat.card (zRad h) = 2 ^ m := by
  rw [← h.card_fixedField]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun c : h.fixedField =>
    (⟨sElt h ((sAdm_zero_zero_iff h).mpr ((h.mem_fixedField).mp c.2)),
      ⟨c, (h.mem_fixedField).mp c.2, rfl⟩⟩ : zRad h)) ⟨?_, ?_⟩)
  · intro c c' hcc
    have := congrArg (fun z : zRad h => (((z : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)) hcc
    exact Subtype.ext (sMat_injective h this).2.2
  · rintro ⟨g, c, hc, hg⟩
    exact ⟨⟨c, (h.mem_fixedField).mpr hc⟩, Subtype.ext (hypSU_ext h hg.symm)⟩

end CFSG.Quasithin.H13.U4Par
