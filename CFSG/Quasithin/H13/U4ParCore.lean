module

public import CFSG.Quasithin.H13.U4ParPoint
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_le_derivedSeriesOf
  le_perfectCore_of_perfect normalizer_le_normalizer_perfectCore)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem charP_fixedField : CharP h.fixedField 2 := by
  have := h.charP
  exact RingHom.charP h.fixedField.subtype Subtype.val_injective 2

theorem center_sl2_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) = ⊥ := by
  have := charP_fixedField h
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (2 : h.fixedField) = 0 := CharTwo.two_eq_zero
    have h1 : (r + 1) * (r + 1) = 0 := by linear_combination hr + (r + 1) * h2
    have h2 := mul_self_eq_zero.mp h1
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h2
    exact h2
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

@[expose] noncomputable def slU : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

@[expose] noncomputable def slL : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩

theorem slU_mul_slL_ne : slU h * slL h ≠ slL h * slU h := by
  have := charP_fixedField h
  intro hc
  have hm := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField =>
    (A : Matrix (Fin 2) (Fin 2) h.fixedField)) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  have := congrFun (congrFun hm 0) 0
  simp [slU, slL, mul_apply, Fin.sum_univ_two] at this

theorem isSimpleGroup_sl2 (hm : 2 ≤ m) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  have h4 : 4 ≤ Nat.card h.fixedField := by
    rw [h.card_fixedField]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) h.fixedField) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  let e : Matrix.SpecialLinearGroup (Fin 2) h.fixedField ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) h.fixedField :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot h).symm)
  exact e.isSimpleGroup

theorem commutator_sl2_eq_top (hm : 2 ≤ m) :
    ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) h.fixedField)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) h.fixedField))⁆ =
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) h.fixedField)) := by
  have := isSimpleGroup_sl2 h hm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) h.fixedField)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) h.fixedField))⁆ with h0 | h0
  · exfalso
    have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top (slU h))
      (Subgroup.mem_top (slL h))
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact slU_mul_slL_ne h hmem
  · exact h0

theorem not_isPGroup_sl2 :
    ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  intro hp
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite h.fixedField := Finite.of_injective _ Subtype.val_injective
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :=
    ⟨⟨slU h * slL h, slL h * slU h, slU_mul_slL_ne h⟩⟩
  have hc := hp.center_nontrivial
  rw [center_sl2_eq_bot] at hc
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hc rfl

@[expose] noncomputable def parH : Subgroup (hypSU h 2 0) where
  carrier := {g | g ∈ parP h ∧ chi h g = 1 ∧ (rho h g).det = 1}
  mul_mem' := by
    rintro g g' ⟨hg, hcg, hdg⟩ ⟨hg', hcg', hdg'⟩
    refine ⟨(parP h).mul_mem hg hg', ?_, ?_⟩
    · rw [chi_mul h hg', hcg, hcg', mul_one]
    · rw [rho_mul h hg hg', det_mul, hdg, hdg', mul_one]
  one_mem' := ⟨(parP h).one_mem, chi_one h, by rw [rho_one, det_one]⟩
  inv_mem' := by
    rintro g ⟨hg, hcg, hdg⟩
    refine ⟨(parP h).inv_mem hg, ?_, ?_⟩
    · have := chi_mul_inv h hg
      rwa [hcg, one_mul] at this
    · have := congrArg Matrix.det (rho_mul_inv h hg)
      rwa [det_mul, hdg, one_mul, det_one] at this

theorem parH_le_parP : parH h ≤ parP h := fun _ hg => hg.1

theorem commutator_parP_le : ⁅parP h, parP h⁆ ≤ parH h := by
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  have hgi := (parP h).inv_mem hg
  have hgi' := (parP h).inv_mem hg'
  have hgg := (parP h).mul_mem hg hg'
  have hggi := (parP h).mul_mem hgg hgi
  refine ⟨(parP h).mul_mem hggi hgi', ?_, ?_⟩
  · rw [commutatorElement_def, chi_mul h hgi', chi_mul h hgi, chi_mul h hg']
    have h1 := chi_mul_inv h hg
    have h2 := chi_mul_inv h hg'
    calc chi h g * chi h g' * chi h g⁻¹ * chi h g'⁻¹
        = (chi h g * chi h g⁻¹) * (chi h g' * chi h g'⁻¹) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
  · rw [commutatorElement_def, rho_mul h hggi hgi', rho_mul h hgg hgi, rho_mul h hg hg', det_mul,
      det_mul, det_mul]
    have h1 := congrArg Matrix.det (rho_mul_inv h hg)
    have h2 := congrArg Matrix.det (rho_mul_inv h hg')
    rw [det_mul, det_one] at h1 h2
    calc (rho h g).det * (rho h g').det * (rho h g⁻¹).det * (rho h g'⁻¹).det
        = ((rho h g).det * (rho h g⁻¹).det) * ((rho h g').det * (rho h g'⁻¹).det) := by ring
      _ = 1 := by rw [h1, h2, mul_one]

theorem perfectCore_parP_le_parH : perfectCore (parP h) ≤ parH h :=
  (perfectCore_le_derivedSeriesOf (parP h) 1).trans (commutator_parP_le h)

theorem rho_bar_of_mem_parH {g : hypSU h 2 0} (hg : g ∈ parH h) :
    (rho h g).map h.bar = rho h g := by
  have := h.charP
  obtain ⟨hgP, -, hdet⟩ := hg
  have hcol := (mem_parP_iff h g).mp hgP
  have hrow := (row_if1_of_col h g hcol).1
  have r2 := hrow ie2 ie2_ne_if1
  have r4 := hrow if2 if2_ne_if1
  have hgram := (mem_gramSU.mp g.2).1
  have entry : ∀ i j, ∑ k, h.bar ((((g : GL Ix K) : Matrix Ix Ix K)) (hypPartner k) i) *
      ((g : GL Ix K) : Matrix Ix Ix K) k j = hypGram 2 0 K i j := by
    intro i j
    have := congrFun (congrFun hgram i) j
    rw [mul_apply] at this
    simpa only [mul_hypGram_apply, transpose_apply, map_apply] using this
  have e1 := entry ie2 ie2
  have e2 := entry ie2 if2
  have e3 := entry if2 ie2
  have e4 := entry if2 if2
  rw [sum_ix, hypGram_apply] at e1 e2 e3 e4
  simp [r2, r4] at e1 e2 e3 e4
  simp only [rho, det_fin_two_of] at hdet
  have b1 := congrArg h.bar e1
  have b2 := congrArg h.bar e2
  simp only [map_add, map_mul, h.bar_bar, map_zero, map_one] at b1 b2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho] <;> grind

theorem rho_mem_fixedField {g : hypSU h 2 0} (hg : g ∈ parH h) (i j : Fin 2) :
    rho h g i j ∈ h.fixedField :=
  (h.mem_fixedField).mpr (congrFun (congrFun (rho_bar_of_mem_parH h hg) i) j)

@[expose] noncomputable def rhoFMat (g : parH h) : Matrix (Fin 2) (Fin 2) h.fixedField :=
  Matrix.of fun i j => ⟨rho h g i j, rho_mem_fixedField h g.2 i j⟩

theorem map_rhoFMat (g : parH h) : (rhoFMat h g).map h.fixedField.subtype = rho h g := by
  ext i j
  rfl

theorem det_rhoFMat (g : parH h) : (rhoFMat h g).det = 1 := by
  apply Subtype.val_injective
  have := RingHom.map_det h.fixedField.subtype (rhoFMat h g)
  rw [RingHom.mapMatrix_apply, map_rhoFMat] at this
  exact this.trans g.2.2.2

@[expose] noncomputable def rhoF : parH h →* Matrix.SpecialLinearGroup (Fin 2) h.fixedField where
  toFun g := ⟨rhoFMat h g, det_rhoFMat h g⟩
  map_one' := by
    ext i j
    change rho h (1 : parH h) i j = (((1 : Matrix (Fin 2) (Fin 2) h.fixedField) i j :
      h.fixedField) : K)
    rw [OneMemClass.coe_one, rho_one]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g g' := by
    ext i j
    have := congrFun (congrFun (rho_mul h (parH_le_parP h g.2) (parH_le_parP h g'.2)) i) j
    change rho h (g * g' : parH h) i j =
      (((rhoFMat h g * rhoFMat h g') i j : h.fixedField) : K)
    rw [Subgroup.coe_mul, this, mul_apply, mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [rhoFMat]

theorem rho_levHom (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    rho h (levHom h A) = slMat h A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho, coe_levHom, levMat_apply, slMat]

theorem levHom_range_le_parH : (levHom h).range ≤ parH h := by
  rintro _ ⟨A, rfl⟩
  refine ⟨levHom_le_parP h ⟨A, rfl⟩, ?_, ?_⟩
  · simp [chi, coe_levHom, levMat_apply]
  · rw [rho_levHom, det_slMat]

theorem rhoF_levHom (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    rhoF h ⟨levHom h A, levHom_range_le_parH h ⟨A, rfl⟩⟩ = A := by
  ext i j
  change rho h (levHom h A) i j = (((A : Matrix (Fin 2) (Fin 2) h.fixedField) i j :
    h.fixedField) : K)
  rw [rho_levHom]
  rfl

theorem levHom_range_le_perfectCore (hm : 2 ≤ m) : (levHom h).range ≤ perfectCore (parP h) := by
  refine le_perfectCore_of_perfect (levHom_le_parP h) ?_
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, commutator_sl2_eq_top h hm]

theorem radQ_le_of {X : Subgroup (hypSU h 2 0)} (hX : X ≤ radQ h)
    (h1 : ∀ t : K, ∃ g ∈ X, ∃ c : K, ((g : GL Ix K) : Matrix Ix Ix K) = sMat h t 0 c)
    (h2 : ∀ t : K, ∃ g ∈ X, ∃ c : K, ((g : GL Ix K) : Matrix Ix Ix K) = sMat h 0 t c) :
    radQ h ≤ X := by
  have := h.charP
  have hadm : ∀ g ∈ X, ∀ x y c : K, ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c →
      SAdm h x y c := by
    intro g hg x y c hgm
    obtain ⟨x', y', c', hc', hg'⟩ := hX hg
    rw [hgm] at hg'
    obtain ⟨rfl, rfl, rfl⟩ := sMat_injective h hg'
    exact hc'
  have hinv : ∀ g : hypSU h 2 0, ∀ x y c : K, SAdm h x y c →
      ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c →
      (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h x y (h.bar c) := by
    intro g x y c hc hg
    have h1 : ((g : GL Ix K) : Matrix Ix Ix K) * sMat h x y (h.bar c) = 1 := by
      rw [hg, sMat_mul_bar h hc]
    rw [Subgroup.coe_inv]
    exact Units.inv_eq_of_mul_eq_one_right h1
  have hZ : zRad h ≤ X := by
    rintro z ⟨c, hc, hz⟩
    obtain ⟨t, ht⟩ := h.traceLin_surjective ⟨c, (h.mem_fixedField).mpr hc⟩
    have ht' : h.trace t = c := congrArg Subtype.val ht
    obtain ⟨a, haX, c₁, ha⟩ := h1 1
    obtain ⟨b, hbX, c₂, hb⟩ := h2 t
    have hadma := hadm a haX _ _ _ ha
    have hadmb := hadm b hbX _ _ _ hb
    have hcomm : z = a * b * a⁻¹ * b⁻¹ := by
      apply hypSU_ext
      rw [coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, hinv a _ _ _ hadma ha,
        hinv b _ _ _ hadmb hb, ha, hb, commutator_sMat h hadma hadmb, hz, ← ht']
      simp
    rw [hcomm]
    exact X.mul_mem (X.mul_mem (X.mul_mem haX hbX) (X.inv_mem haX)) (X.inv_mem hbX)
  rintro g ⟨x, y, c, hc, hg⟩
  obtain ⟨a, haX, c₁, ha⟩ := h1 x
  obtain ⟨b, hbX, c₂, hb⟩ := h2 y
  have hadma := hadm a haX _ _ _ ha
  have hadmb := hadm b hbX _ _ _ hb
  have hab := SAdm.mul h hadma hadmb
  simp only [add_zero, zero_add, map_zero, mul_zero] at hab
  set C := c₁ + c₂ + h.bar x * y with hC
  have hd : h.bar (c - C) = c - C := by
    unfold SAdm at hc hab
    rw [map_sub]
    grind
  have hzZ : sElt h ((sAdm_zero_zero_iff h).mpr hd) ∈ zRad h := ⟨c - C, hd, rfl⟩
  have hgeq : g = a * b * sElt h ((sAdm_zero_zero_iff h).mpr hd) := by
    apply hypSU_ext
    rw [coe_mul_hypSU, coe_mul_hypSU, ha, hb, coe_sElt, sMat_mul, sMat_mul, hg]
    simp only [add_zero, zero_add, map_zero, mul_zero]
    congr 1
    rw [hC]
    ring
  rw [hgeq]
  exact X.mul_mem (X.mul_mem haX hbX) (hZ hzZ)

theorem levMat_conj_sMat (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) (x y c : K) :
    levMat (slMat h A) * sMat h x y c * levMat (slMat h A⁻¹) =
      sMat h (slMat h A 0 0 * x + slMat h A 0 1 * y) (slMat h A 1 0 * x + slMat h A 1 1 * y)
        c := by
  rw [levMat_mul_sMat h (slMat_bar h A) (det_slMat h A), Matrix.mul_assoc, levMat_mul,
    ← slMat_mul, mul_inv_cancel, slMat_one, levMat_one, Matrix.mul_one]

theorem coe_levHom_inv (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    ((((levHom h A)⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = levMat (slMat h A⁻¹) := by
  rw [← map_inv, coe_levHom]

theorem coe_sElt_inv {x y c : K} (hc : SAdm h x y c) :
    ((((sElt h hc)⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h x y (h.bar c) := by
  rw [Subgroup.coe_inv]
  exact Units.inv_eq_of_mul_eq_one_right (sMat_mul_bar h hc)

theorem comm_slU (t : K) :
    ((((sElt h (sAdm_zero_y h t)) * levHom h (slU h) * (sElt h (sAdm_zero_y h t))⁻¹ *
      (levHom h (slU h))⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h t 0 (h.bar t * t) := by
  have := h.charP
  rw [coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, coe_levHom_inv, coe_sElt_inv, coe_sElt,
    coe_levHom, Matrix.mul_assoc (sMat h 0 t 0), Matrix.mul_assoc (sMat h 0 t 0), map_zero,
    levMat_conj_sMat, sMat_mul]
  simp [slMat, slU, CharTwo.add_self_eq_zero]

theorem comm_slL (t : K) :
    ((((sElt h (sAdm_x_zero h t)) * levHom h (slL h) * (sElt h (sAdm_x_zero h t))⁻¹ *
      (levHom h (slL h))⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h 0 t (h.bar t * t) := by
  have := h.charP
  rw [coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, coe_levHom_inv, coe_sElt_inv, coe_sElt,
    coe_levHom, Matrix.mul_assoc (sMat h t 0 0), Matrix.mul_assoc (sMat h t 0 0), map_zero,
    levMat_conj_sMat, sMat_mul]
  simp [slMat, slL, CharTwo.add_self_eq_zero]

theorem parP_le_normalizer_perfectCore :
    parP h ≤ Subgroup.normalizer (perfectCore (parP h) : Set (hypSU h 2 0)) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (parP h))

theorem commutator_radQ_perfectCore_le : ⁅radQ h, perfectCore (parP h)⁆ ≤ radQ h := by
  rw [Subgroup.commutator_le]
  intro q hq p hp
  have hpP := perfectCore_le (parP h) hp
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  refine (radQ h).mul_mem hq ?_
  have := (Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_radQ h hpP) q⁻¹).mp
    ((radQ h).inv_mem hq)
  rwa [← mul_assoc]

theorem commutator_radQ_perfectCore_le_perfectCore :
    ⁅radQ h, perfectCore (parP h)⁆ ≤ perfectCore (parP h) := by
  rw [Subgroup.commutator_le]
  intro q hq p hp
  have hqP := radQ_le_parP h hq
  rw [commutatorElement_def]
  refine (perfectCore (parP h)).mul_mem ?_ ((perfectCore (parP h)).inv_mem hp)
  exact (Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_perfectCore h hqP) p).mp hp

theorem commutator_radQ_perfectCore (hm : 2 ≤ m) :
    ⁅radQ h, perfectCore (parP h)⁆ = radQ h := by
  refine le_antisymm (commutator_radQ_perfectCore_le h) (radQ_le_of h
    (commutator_radQ_perfectCore_le h) (fun t => ?_) (fun t => ?_))
  · refine ⟨_, ?_, _, comm_slU h t⟩
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (sElt_mem_radQ h _)
      (levHom_range_le_perfectCore h hm ⟨_, rfl⟩)
  · refine ⟨_, ?_, _, comm_slL h t⟩
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (sElt_mem_radQ h _)
      (levHom_range_le_perfectCore h hm ⟨_, rfl⟩)

theorem radQ_le_perfectCore (hm : 2 ≤ m) : radQ h ≤ perfectCore (parP h) := by
  rw [← commutator_radQ_perfectCore h hm]
  exact commutator_radQ_perfectCore_le_perfectCore h

theorem pCoreOf_perfectCore_le_radQ (hm : 2 ≤ m) :
    CFSG.Open.pCoreOf 2 (perfectCore (parP h)) ≤ radQ h := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 (perfectCore (parP h)) with hOdef
  have hOH : O ≤ parH h :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (perfectCore_parP_le_parH h)
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hOn : parP h ≤ Subgroup.normalizer (O : Set (hypSU h 2 0)) :=
    (parP_le_normalizer_perfectCore h).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) h.fixedField),
      N = (O.subgroupOf (parH h)).map (rhoF h) := ⟨_, rfl⟩
  have hNn : N.Normal := by
    refine ⟨fun n hn A => ?_⟩
    rw [hNdef] at hn ⊢
    obtain ⟨o, ho, rfl⟩ := hn
    have hl := levHom_range_le_parH h ⟨A, rfl⟩
    have hmem : (levHom h A) * (o : hypSU h 2 0) * (levHom h A)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hOn (parH_le_parP h hl)) o).mp ho
    refine ⟨⟨levHom h A, hl⟩ * o * ⟨levHom h A, hl⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact hmem
    · rw [map_mul, map_mul, map_inv, rhoF_levHom]
  have hOp' : IsPGroup 2 (O.subgroupOf (parH h)) :=
    hOp.of_equiv (Subgroup.subgroupOfEquivOfLe hOH).symm
  have hNp : IsPGroup 2 N := by
    rw [hNdef]
    exact IsPGroup.map hOp' (rhoF h)
  have := isSimpleGroup_sl2 h hm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  · intro o ho
    have h1 : rhoF h ⟨o, hOH ho⟩ = 1 := by
      have : rhoF h ⟨o, hOH ho⟩ ∈ N := by
        rw [hNdef]
        exact ⟨⟨o, hOH ho⟩, ho, rfl⟩
      rwa [hN, Subgroup.mem_bot] at this
    have hrho : rho h o = 1 := by
      ext i j
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField =>
        (((A : Matrix (Fin 2) (Fin 2) h.fixedField) i j : h.fixedField) : K)) h1
      change rho h o i j = _ at this
      rw [this]
      fin_cases i <;> fin_cases j <;> simp
    exact mem_radQ_of_chi_rho h (hOH ho).1 (hOH ho).2.1 hrho
  · exfalso
    rw [hN] at hNp
    exact not_isPGroup_sl2 h (hNp.of_equiv Subgroup.topEquiv)

theorem pCoreOf_perfectCore_parP (hm : 2 ≤ m) :
    CFSG.Open.pCoreOf 2 (perfectCore (parP h)) = radQ h := by
  refine le_antisymm (pCoreOf_perfectCore_le_radQ h hm) ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (radQ_le_perfectCore h hm)
    ((perfectCore_le (parP h)).trans (parP_le_normalizer_radQ h)) (radQ_isPGroup h)

theorem perfectCore_parP_le_centralizer :
    perfectCore (parP h) ≤ Subgroup.centralizer (zRad h : Set (hypSU h 2 0)) := by
  intro g hg
  obtain ⟨hgP, hchi, -⟩ := perfectCore_parP_le_parH h hg
  have hcol := (mem_parP_iff h g).mp hgP
  obtain ⟨hrow, hdiag⟩ := row_if1_of_col h g hcol
  unfold chi at hchi
  have hff : ((g : GL Ix K) : Matrix Ix Ix K) if1 if1 = 1 := by
    rw [hchi, map_one, one_mul] at hdiag
    exact hdiag
  have c2 := hcol ie2 ie2_ne_ie1
  have c3 := hcol if1 if1_ne_ie1
  have c4 := hcol if2 if2_ne_ie1
  have r1 := hrow ie1 ie1_ne_if1
  have r2 := hrow ie2 ie2_ne_if1
  have r4 := hrow if2 if2_ne_if1
  rw [Subgroup.mem_centralizer_iff]
  rintro z ⟨c, -, hz⟩
  apply hypSU_ext
  rw [coe_mul_hypSU, coe_mul_hypSU, hz]
  ext i j
  rw [mul_apply, sum_ix, mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, c2, c3, c4, r2, r4, hchi, hff, add_comm]

end CFSG.Quasithin.H13.U4Par
