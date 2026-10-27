module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalModel
public import CFSG.Quasithin.H13.U4ParExt
public import CFSG.RankThree.CentralLiftU.HypRankOneConj

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par
open scoped Pointwise commutatorElement

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

@[expose] noncomputable def u4xbMat (t : K) : Matrix Ix Ix K := 1 + single ie2 if2 t

theorem u4xbMat_apply (t : K) (i j : Ix) :
    u4xbMat t i j = (1 : Matrix Ix Ix K) i j + (if ie2 = i ∧ if2 = j then t else 0) := by
  simp only [u4xbMat, Matrix.add_apply, Matrix.single_apply]

theorem u4xbMat_mul (t t' : K) : u4xbMat t * u4xbMat t' = u4xbMat (t + t') := by
  ext i j
  rw [mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [u4xbMat_apply, one_apply, ie1, ie2, if1, if2] <;> ring

theorem u4xbMat_zero : u4xbMat (0 : K) = 1 := by
  simp [u4xbMat]

theorem det_u4xbMat (t : K) : (u4xbMat t).det = 1 :=
  Matrix.det_transvection_of_ne ie2 if2 ie2_ne_if2 t

include h in
theorem u4xbMat_mul_self (t : K) : u4xbMat t * u4xbMat t = 1 := by
  have := h.charP
  rw [u4xbMat_mul, CharTwo.add_self_eq_zero, u4xbMat_zero]

theorem u4xbMat_gram {t : K} (ht : h.bar t = t) :
    ((u4xbMat t).map h.bar)ᵀ * hypGram 2 0 K * u4xbMat t = hypGram 2 0 K := by
  have := h.charP
  ext i j
  rw [mul_apply, sum_ix]
  simp only [mul_hypGram_apply, transpose_apply, map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [u4xbMat_apply, one_apply, hypGram_apply, hypPartner, ie1, ie2, if1, if2, ht] <;>
    grind

@[expose] noncomputable def u4xbElt {t : K} (ht : h.bar t = t) : hypSU h 2 0 :=
  ⟨⟨u4xbMat t, u4xbMat t, u4xbMat_mul_self h t, u4xbMat_mul_self h t⟩,
    mem_gramSU.mpr ⟨u4xbMat_gram h ht, det_u4xbMat t⟩⟩

theorem coe_u4xbElt {t : K} (ht : h.bar t = t) :
    (((u4xbElt h ht : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = u4xbMat t :=
  rfl

theorem u4xbElt_mul_self {t : K} (ht : h.bar t = t) : u4xbElt h ht * u4xbElt h ht = 1 :=
  hypSU_ext h (by rw [coe_mul_hypSU, coe_u4xbElt, u4xbMat_mul_self h]; rfl)

theorem u4xbElt_inv {t : K} (ht : h.bar t = t) : (u4xbElt h ht)⁻¹ = u4xbElt h ht :=
  inv_eq_of_mul_eq_one_right (u4xbElt_mul_self h ht)

theorem u4xbElt_add {t t' : K} (ht : h.bar t = t) (ht' : h.bar t' = t')
    (htt : h.bar (t + t') = t + t') :
    u4xbElt h htt = u4xbElt h ht * u4xbElt h ht' :=
  hypSU_ext h (by rw [coe_mul_hypSU, coe_u4xbElt, coe_u4xbElt, coe_u4xbElt, u4xbMat_mul])

theorem u4xbMat_mul_sMat {t : K} (ht : h.bar t = t) (x y c : K) :
    u4xbMat t * sMat h x y c = sMat h (x + t * y) y c * u4xbMat t := by
  have := h.charP
  ext i j
  rw [mul_apply, sum_ix, mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [u4xbMat_apply, sMat_apply, one_apply, ie1, ie2, if1, if2, map_add, map_mul, ht] <;>
    grind

theorem u4xbMat_comm_sMat {t : K} (ht : h.bar t = t) (y : K) :
    u4xbMat t * sMat h 0 y 0 * u4xbMat t * sMat h 0 y 0 =
      sMat h (t * y) 0 (t * (h.bar y * y)) := by
  have := h.charP
  rw [u4xbMat_mul_sMat h ht, Matrix.mul_assoc (sMat h _ _ _), u4xbMat_mul_self h, Matrix.mul_one,
    sMat_mul]
  congr 1
  · ring
  · exact CharTwo.add_self_eq_zero y
  · simp only [map_add, map_zero, map_mul, ht]
    ring

theorem sMat_zero_u4 : sMat h 0 0 0 = 1 := by
  ext i j
  simp [sMat_apply]

@[expose] noncomputable def u4RootA : Subgroup (hypSU h 2 0) where
  carrier := {g | ∃ y : K, ((g : GL Ix K) : Matrix Ix Ix K) = sMat h 0 y 0}
  mul_mem' := by
    rintro g g' ⟨y, hg⟩ ⟨y', hg'⟩
    exact ⟨y + y', by rw [coe_mul_hypSU, hg, hg', sMat_mul]; simp⟩
  one_mem' := ⟨0, (sMat_zero_u4 h).symm⟩
  inv_mem' := by
    rintro g ⟨y, hg⟩
    exact ⟨y, by rw [coe_inv_of_sMat (sAdm_zero_y h y) hg, map_zero]⟩

theorem mem_u4RootA {g : hypSU h 2 0} :
    g ∈ u4RootA h ↔ ∃ y : K, ((g : GL Ix K) : Matrix Ix Ix K) = sMat h 0 y 0 :=
  Iff.rfl

theorem syElt_mem_u4RootA (y : K) : syElt h y ∈ u4RootA h :=
  ⟨y, coe_syElt y⟩

theorem syElt_add_u4 (y y' : K) : syElt h (y + y') = syElt h y * syElt h y' :=
  hypSU_ext h (by rw [coe_mul_hypSU, coe_syElt, coe_syElt, coe_syElt, sMat_mul]; simp)

@[expose] noncomputable def u4RootB : Subgroup (hypSU h 2 0) where
  carrier := {g | ∃ t : K, h.bar t = t ∧ ((g : GL Ix K) : Matrix Ix Ix K) = u4xbMat t}
  mul_mem' := by
    rintro g g' ⟨t, ht, hg⟩ ⟨t', ht', hg'⟩
    exact ⟨t + t', by rw [map_add, ht, ht'], by rw [coe_mul_hypSU, hg, hg', u4xbMat_mul]⟩
  one_mem' := ⟨0, map_zero _, u4xbMat_zero.symm⟩
  inv_mem' := by
    rintro g ⟨t, ht, hg⟩
    refine ⟨t, ht, ?_⟩
    rw [Subgroup.coe_inv]
    exact Units.inv_eq_of_mul_eq_one_right (by rw [hg, u4xbMat_mul_self h])

theorem mem_u4RootB {g : hypSU h 2 0} :
    g ∈ u4RootB h ↔ ∃ t : K, h.bar t = t ∧ ((g : GL Ix K) : Matrix Ix Ix K) = u4xbMat t :=
  Iff.rfl

theorem u4xbElt_mem_u4RootB {t : K} (ht : h.bar t = t) : u4xbElt h ht ∈ u4RootB h :=
  ⟨t, ht, rfl⟩

theorem parP_inf_parP2_eq_u4 : parP h ⊓ parP2 h = hypBorel h 2 0 := by
  ext g
  rw [Subgroup.mem_inf, mem_hypBorel]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hi2
    interval_cases i
    · exact MulAction.mem_stabilizer_iff.mp h1
    · exact MulAction.mem_stabilizer_iff.mp h2
  · intro hg
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hg 1 le_rfl (by norm_num)),
      MulAction.mem_stabilizer_iff.mpr (hg 2 (by norm_num) le_rfl)⟩

theorem hypUnitriangular_le_inf_u4 : hypUnitriangular h 2 0 ≤ parP h ⊓ parP2 h := by
  rw [parP_inf_parP2_eq_u4 h]
  exact hypUnitriangular_le_hypBorel h

theorem hypTorus_le_inf_u4 : hypTorus h 2 0 ≤ parP h ⊓ parP2 h := by
  rw [parP_inf_parP2_eq_u4 h]
  exact hypTorus_le_hypBorel h

theorem radQ_le_hypUnitriangular_u4 : radQ h ≤ hypUnitriangular h 2 0 := by
  rintro g ⟨x, y, c, -, hg⟩
  refine mem_hypUnitriangular.mpr ⟨?_, fun a => ?_⟩
  · intro i j hij
    rw [hg, sMat_apply]
    rcases ix_cases i with rfl | rfl | rfl | rfl <;>
      rcases ix_cases j with rfl | rfl | rfl | rfl <;> simp at hij <;> simp [one_apply]
  · rw [hg, sMat_apply]
    rcases ix_cases a with rfl | rfl | rfl | rfl <;> simp [one_apply]

theorem radQ_le_inf_u4 : radQ h ≤ parP h ⊓ parP2 h :=
  (radQ_le_hypUnitriangular_u4 h).trans (hypUnitriangular_le_inf_u4 h)

theorem u4xbElt_mem_hypUnitriangular {t : K} (ht : h.bar t = t) :
    u4xbElt h ht ∈ hypUnitriangular h 2 0 := by
  refine mem_hypUnitriangular.mpr ⟨?_, fun a => ?_⟩
  · intro i j hij
    rw [coe_u4xbElt, u4xbMat_apply]
    rcases ix_cases i with rfl | rfl | rfl | rfl <;>
      rcases ix_cases j with rfl | rfl | rfl | rfl <;> simp at hij <;> simp [one_apply]
  · rw [coe_u4xbElt, u4xbMat_apply]
    rcases ix_cases a with rfl | rfl | rfl | rfl <;> simp [one_apply]

theorem u4RootA_le_inf : u4RootA h ≤ parP h ⊓ parP2 h := by
  rintro g ⟨y, hg⟩
  exact radQ_le_inf_u4 h ⟨0, y, 0, sAdm_zero_y h y, hg⟩

theorem u4RootB_le_hypUnitriangular : u4RootB h ≤ hypUnitriangular h 2 0 := by
  rintro g ⟨t, ht, hg⟩
  have : g = u4xbElt h ht := hypSU_ext h hg
  rw [this]
  exact u4xbElt_mem_hypUnitriangular h ht

theorem u4RootB_le_inf : u4RootB h ≤ parP h ⊓ parP2 h :=
  (u4RootB_le_hypUnitriangular h).trans (hypUnitriangular_le_inf_u4 h)

theorem u4xbMat_mul_sMat_apply (t x y c : K) :
    (u4xbMat t * sMat h x y c) ie1 ie2 = h.bar y ∧ (u4xbMat t * sMat h x y c) ie1 if2 = h.bar x ∧
      (u4xbMat t * sMat h x y c) ie1 if1 = c ∧ (u4xbMat t * sMat h x y c) ie2 if2 = t := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mul_apply, sum_ix] <;>
    simp [u4xbMat_apply, sMat_apply, one_apply]

theorem u4xbMat_mul_sMat_if2_if1 (t x y c : K) : (u4xbMat t * sMat h x y c) if2 if1 = y := by
  rw [mul_apply, sum_ix]
  simp [u4xbMat_apply, sMat_apply, one_apply]

theorem exists_u4xbElt_mul_of_mem {g : hypSU h 2 0} (hg : g ∈ hypUnitriangular h 2 0) :
    ∃ (t : K) (ht : h.bar t = t), ∃ r ∈ radQ h, g = u4xbElt h ht * r := by
  have := h.charP
  obtain ⟨hT, hd⟩ := mem_hypUnitriangular.mp hg
  have hgP : g ∈ parP h := (hypUnitriangular_le_inf_u4 h hg).1
  have e42 : ((g : GL Ix K) : Matrix Ix Ix K) if2 ie2 = 0 := hT (by simp)
  have e34 : ((g : GL Ix K) : Matrix Ix Ix K) if1 if2 = 0 := hT (by simp)
  have ht : h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie2 if2) =
      ((g : GL Ix K) : Matrix Ix Ix K) ie2 if2 := by
    have hgram := (mem_gramSU.mp g.2).1
    have h1 := congrFun (congrFun hgram if2) if2
    rw [mul_apply, sum_ix] at h1
    simp only [mul_hypGram_apply, transpose_apply, map_apply, hypPartner_ie1, hypPartner_ie2,
      hypPartner_if1, hypPartner_if2, e34, hd if2, map_zero, zero_mul, mul_zero, map_one,
      one_mul, mul_one, zero_add, add_zero, hypGram_apply] at h1
    simp at h1
    grind
  have hxP := u4xbElt_mem_hypUnitriangular h ht
  have hxP' : u4xbElt h ht ∈ parP h := (hypUnitriangular_le_inf_u4 h hxP).1
  refine ⟨_, ht, u4xbElt h ht * g, ?_, ?_⟩
  · refine mem_radQ_of_chi_rho h ((parP h).mul_mem hxP' hgP) ?_ ?_
    · rw [chi_mul h hgP]
      simp [chi, coe_u4xbElt, u4xbMat_apply, one_apply, hd ie1]
    · rw [rho_mul h hxP' hgP]
      have h1 : rho h (u4xbElt h ht) =
          !![1, ((g : GL Ix K) : Matrix Ix Ix K) ie2 if2; 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [rho, coe_u4xbElt, u4xbMat_apply, one_apply]
      have h2 : rho h g = !![1, ((g : GL Ix K) : Matrix Ix Ix K) ie2 if2; 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [rho, hd, e42]
      rw [h1, h2, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  · rw [← mul_assoc, u4xbElt_mul_self, one_mul]

private theorem mem_of_u4Roots_xN {S : Subgroup (hypSU h 2 0)} (ha : u4RootA h ≤ S)
    (hb : u4RootB h ≤ S) {y : K} {g : hypSU h 2 0}
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h y 0 (h.bar y * y)) : g ∈ S := by
  have h1 : h.bar (1 : K) = 1 := map_one _
  have hxb := hb (u4xbElt_mem_u4RootB h h1)
  have hya := ha (syElt_mem_u4RootA h y)
  have e : g = u4xbElt h h1 * syElt h y * u4xbElt h h1 * syElt h y := by
    apply hypSU_ext h
    rw [hg, coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, coe_u4xbElt, coe_syElt,
      u4xbMat_comm_sMat h h1, one_mul, one_mul]
  rw [e]
  exact S.mul_mem (S.mul_mem (S.mul_mem hxb hya) hxb) hya

private theorem mem_of_u4Roots_z {S : Subgroup (hypSU h 2 0)} (ha : u4RootA h ≤ S)
    (hb : u4RootB h ≤ S) {c : K} (hc : h.bar c = c) {g : hypSU h 2 0}
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h 0 0 c) : g ∈ S := by
  obtain ⟨w, hw⟩ := h.traceLin_surjective ⟨c, (h.mem_fixedField).mpr hc⟩
  have hw' : h.trace w = c := congrArg Subtype.val hw
  have hadm : SAdm h 1 0 (h.bar 1 * 1) := (sAdm_of_y_zero_iff h).mpr (by simp)
  have haS : sElt h hadm ∈ S := mem_of_u4Roots_xN h ha hb (coe_sElt h hadm)
  have hyS := ha (syElt_mem_u4RootA h w)
  have e : g = syElt h w * sElt h hadm * syElt h w * sElt h hadm := by
    apply hypSU_ext h
    have hc' := commutator_sMat h (sAdm_zero_y h w) hadm
    rw [map_zero, show h.bar (h.bar 1 * 1) = h.bar 1 * 1 by simp] at hc'
    rw [hg, coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, coe_syElt, coe_sElt, hc', ← hw']
    congr 1
    simp [UnitaryFieldData.trace, h.bar_bar, add_comm]
  rw [e]
  exact S.mul_mem (S.mul_mem (S.mul_mem hyS haS) hyS) haS

theorem radQ_inf_radQ2_le_of_u4 {S : Subgroup (hypSU h 2 0)}
    (hxN : ∀ (y : K) (g : hypSU h 2 0),
      ((g : GL Ix K) : Matrix Ix Ix K) = sMat h y 0 (h.bar y * y) → g ∈ S)
    (hz : ∀ c : K, h.bar c = c → ∀ g : hypSU h 2 0,
      ((g : GL Ix K) : Matrix Ix Ix K) = sMat h 0 0 c → g ∈ S) :
    radQ h ⊓ radQ2 h ≤ S := by
  have := h.charP
  intro g hg
  obtain ⟨x, c, hc, hgm⟩ := (mem_radQ_inf_radQ2_iff h).mp hg
  have hN : h.bar (h.bar x * x) = h.bar x * x := by rw [map_mul, h.bar_bar, mul_comm]
  have hadm1 : SAdm h x 0 (h.bar x * x) := (sAdm_of_y_zero_iff h).mpr hN
  have hc2 : h.bar (c + h.bar x * x) = c + h.bar x * x := by rw [map_add, hc, hN]
  have hadm2 : SAdm h 0 0 (c + h.bar x * x) := (sAdm_zero_zero_iff h).mpr hc2
  have e : g = sElt h hadm1 * sElt h hadm2 := by
    apply hypSU_ext h
    rw [hgm, coe_mul_hypSU, coe_sElt, coe_sElt, sMat_mul]
    congr 1
    · simp
    · simp
    · simp only [map_zero, mul_zero, add_zero]
      grind
  rw [e]
  exact S.mul_mem (hxN x _ (coe_sElt h hadm1)) (hz _ hc2 _ (coe_sElt h hadm2))

theorem u4RootA_le_radQ : u4RootA h ≤ radQ h := by
  rintro g ⟨y, hg⟩
  exact ⟨0, y, 0, sAdm_zero_y h y, hg⟩

theorem mem_radQ_iff_u4 {g : hypSU h 2 0} :
    g ∈ radQ h ↔ ∃ a ∈ u4RootA h, ∃ r ∈ radQ h ⊓ radQ2 h, g = a * r := by
  have := h.charP
  constructor
  · rintro ⟨x, y, c, hc, hgm⟩
    have hc' : h.bar (c + h.bar y * x) = c + h.bar y * x := by
      unfold SAdm at hc
      simp only [map_add, map_mul, h.bar_bar]
      grind
    have hadm : SAdm h x 0 (c + h.bar y * x) := (sAdm_of_y_zero_iff h).mpr hc'
    refine ⟨syElt h y, syElt_mem_u4RootA h y, sElt h hadm,
      (mem_radQ_inf_radQ2_iff h).mpr ⟨x, _, hc', coe_sElt h hadm⟩, ?_⟩
    apply hypSU_ext h
    rw [hgm, coe_mul_hypSU, coe_syElt, coe_sElt, sMat_mul]
    congr 1
    · simp
    · simp
    · simp only [map_zero, zero_mul, add_zero, zero_add]
      grind
  · rintro ⟨a, ha, r, hr, rfl⟩
    exact (radQ h).mul_mem (u4RootA_le_radQ h ha) hr.1

theorem hypUnitriangular_le_of_u4Roots {S : Subgroup (hypSU h 2 0)} (ha : u4RootA h ≤ S)
    (hb : u4RootB h ≤ S) : hypUnitriangular h 2 0 ≤ S := by
  intro u hu
  obtain ⟨t, ht, r, hr, rfl⟩ := exists_u4xbElt_mul_of_mem h hu
  refine S.mul_mem (hb (u4xbElt_mem_u4RootB h ht)) ?_
  obtain ⟨a, haA, r', hr', rfl⟩ := (mem_radQ_iff_u4 h).mp hr
  exact S.mul_mem (ha haA) (radQ_inf_radQ2_le_of_u4 h
    (fun _ _ hg => mem_of_u4Roots_xN h ha hb hg)
    (fun _ hc _ hg => mem_of_u4Roots_z h ha hb hc hg) hr')

theorem radQ2_le_inf_u4 : radQ2 h ≤ parP h ⊓ parP2 h := by
  intro g hg
  refine ⟨(mem_parP_iff h g).mpr fun a ha => ?_, radQ2_le_parP2 h hg⟩
  obtain ⟨-, -, a3, -, a5, -, -, -, a9, -, -, -⟩ := hg
  rcases ix_cases a with rfl | rfl | rfl | rfl
  · exact absurd rfl ha
  · exact a3
  · exact a5
  · exact a9

theorem u4xbElt_mem_radQ2 {t : K} (ht : h.bar t = t) : u4xbElt h ht ∈ radQ2 h := by
  show IsQ2Mat (u4xbMat t)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [u4xbMat_apply, one_apply]

theorem commutator_radQ2_u4RootA : ⁅radQ2 h, u4RootA h⁆ = radQ h ⊓ radQ2 h := by
  have := h.charP
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro r hr x hx
    have hrB := radQ2_le_inf_u4 h hr
    have hxB := u4RootA_le_inf h hx
    have hxQ := u4RootA_le_radQ h hx
    rw [commutatorElement_def]
    constructor
    · exact (radQ h).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (parP_le_normalizer_radQ h hrB.1) x).mp hxQ) ((radQ h).inv_mem hxQ)
    · have e := (Subgroup.mem_normalizer_iff.mp (parP2_le_normalizer_radQ2 h hxB.2) r⁻¹).mp
        ((radQ2 h).inv_mem hr)
      rw [mul_assoc, mul_assoc]
      exact (radQ2 h).mul_mem hr (by simpa [mul_assoc] using e)
  · refine radQ_inf_radQ2_le_of_u4 h (fun y g hg => ?_) (fun c hc g hg => ?_)
    · have h1 : h.bar (1 : K) = 1 := map_one _
      have e : g = ⁅u4xbElt h h1, syElt h y⁆ := by
        apply hypSU_ext h
        rw [commutatorElement_def, u4xbElt_inv, coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU,
          coe_syElt_inv, map_zero, coe_u4xbElt, coe_syElt, u4xbMat_comm_sMat h h1, one_mul,
          one_mul, hg]
      rw [e]
      exact Subgroup.commutator_mem_commutator (u4xbElt_mem_radQ2 h h1) (syElt_mem_u4RootA h y)
    · obtain ⟨w, hw⟩ := h.traceLin_surjective ⟨c, (h.mem_fixedField).mpr hc⟩
      have hw' : h.trace w = c := congrArg Subtype.val hw
      have hadm : SAdm h 1 0 (h.bar 1 * 1) := (sAdm_of_y_zero_iff h).mpr (by simp)
      have haQ2 : sElt h hadm ∈ radQ2 h :=
        ((mem_radQ_inf_radQ2_iff h).mpr ⟨1, _, (sAdm_of_y_zero_iff h).mp hadm, rfl⟩).2
      have e : g = ⁅sElt h hadm, syElt h w⁆ := by
        apply hypSU_ext h
        have hc' := commutator_sMat h hadm (sAdm_zero_y h w)
        rw [map_zero, show h.bar (h.bar 1 * 1) = h.bar 1 * 1 by simp] at hc'
        rw [commutatorElement_def, coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, coe_sElt_inv,
          coe_syElt_inv, coe_sElt, coe_syElt, map_zero,
          show h.bar (h.bar 1 * 1) = h.bar 1 * 1 by simp, hc', hg, ← hw']
        congr 1
        simp
      rw [e]
      exact Subgroup.commutator_mem_commutator haQ2 (syElt_mem_u4RootA h w)

theorem coe_inv_of_diag_u4 {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) :
    (((d⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = diagonal fun i => (q i)⁻¹ := by
  rw [Subgroup.coe_inv]
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hd, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd i)

theorem comm_diag_iff_u4 {d g : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) :
    d * g = g * d ↔ ∀ i j, q i * ((g : GL Ix K) : Matrix Ix Ix K) i j =
      ((g : GL Ix K) : Matrix Ix Ix K) i j * q j := by
  constructor
  · intro hc i j
    have e := congrFun (congrFun
      (congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K)) hc) i) j
    simpa only [coe_mul_hypSU, hd, diagonal_mul, mul_diagonal] using e
  · intro H
    apply hypSU_ext h
    rw [coe_mul_hypSU, coe_mul_hypSU, hd]
    ext i j
    rw [diagonal_mul, mul_diagonal]
    exact H i j

theorem exists_diag_of_mem_hypTorus_u4 {d : hypSU h 2 0} (hd : d ∈ hypTorus h 2 0) :
    ∃ q : Ix → K, ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q := by
  obtain ⟨a, d0, -, -, hm⟩ := hd
  exact ⟨_, hm⟩

theorem exists_mem_hypTorus_u4 {a0 a1 : K} (h0 : a0 ≠ 0) (h1 : a1 ≠ 0)
    (hr : h.bar (a0 * a1) = a0 * a1) :
    ∃ d ∈ hypTorus h 2 0, ∃ q : Ix → K, ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q ∧
      q ie1 = a0 ∧ q ie2 = a1 ∧ q if1 = (h.bar a0)⁻¹ ∧ q if2 = (h.bar a1)⁻¹ := by
  let a : Fin 2 → Kˣ := ![Units.mk0 a0 h0, Units.mk0 a1 h1]
  have hb0 : h.bar a0 ≠ 0 := (map_ne_zero h.bar).mpr h0
  have hb1 : h.bar a1 ≠ 0 := (map_ne_zero h.bar).mpr h1
  have hp : torusRatio h a (Fin.elim0 : Fin 0 → Kˣ) = 1 := by
    simp only [torusRatio, Fin.prod_univ_two, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0]
    rw [map_mul] at hr
    field_simp
    exact hr.symm
  obtain ⟨d, hdT, hdm⟩ := torusMat_mem_hypSU h a (fun k => k.elim0) hp
  exact ⟨d, hdT, _, hdm, rfl, rfl, rfl, rfl⟩

theorem diag_rel_u4 {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) :
    h.bar (q if1) = (q ie1)⁻¹ ∧ h.bar (q if2) = (q ie2)⁻¹ ∧ h.bar (q ie1) = (q if1)⁻¹ ∧
      h.bar (q ie2) = (q if2)⁻¹ := by
  have r1 := CFSG.RankThree.CentralLiftU.diag_entries h hd if1
  have r2 := CFSG.RankThree.CentralLiftU.diag_entries h hd if2
  have r3 := CFSG.RankThree.CentralLiftU.diag_entries h hd ie1
  have r4 := CFSG.RankThree.CentralLiftU.diag_entries h hd ie2
  rw [hypPartner_if1] at r1
  rw [hypPartner_if2] at r2
  rw [hypPartner_ie1] at r3
  rw [hypPartner_ie2] at r4
  exact ⟨eq_inv_of_mul_eq_one_left r1, eq_inv_of_mul_eq_one_left r2,
    eq_inv_of_mul_eq_one_left r3, eq_inv_of_mul_eq_one_left r4⟩

theorem coe_conj_syElt_of_diag {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (y : K) :
    (((d * syElt h y * d⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h 0 (q if2 * (q if1)⁻¹ * y) 0 := by
  obtain ⟨b1, b2, -, -⟩ := diag_rel_u4 h hd
  have n1 := CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd ie1
  have n2 := CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd ie2
  have n3 := CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd if1
  have n4 := CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd if2
  rw [coe_mul_hypSU, coe_mul_hypSU, hd, coe_inv_of_diag_u4 h hd, coe_syElt]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, map_mul, map_inv₀, b1, b2, n1, n2, n3, n4] <;> ring

theorem coe_conj_u4xbElt_of_diag {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) {t : K} (ht : h.bar t = t) :
    (((d * u4xbElt h ht * d⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      u4xbMat (q ie2 * (q if2)⁻¹ * t) := by
  have n1 := CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd ie1
  have n2 := CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd ie2
  have n3 := CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd if1
  have n4 := CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd if2
  rw [coe_mul_hypSU, coe_mul_hypSU, hd, coe_inv_of_diag_u4 h hd, coe_u4xbElt]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [u4xbMat_apply, one_apply, n1, n2, n3, n4] <;> ring

theorem mem_u4RootB_of_comm_diag {d u : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (h12 : q ie1 ≠ q ie2)
    (h14 : q ie1 ≠ q if2) (h13 : q ie1 ≠ q if1) (hu : u ∈ hypUnitriangular h 2 0)
    (hc : d * u = u * d) : u ∈ u4RootB h := by
  obtain ⟨t, ht, r, hr, rfl⟩ := exists_u4xbElt_mul_of_mem h hu
  obtain ⟨x, y, c, -, hrm⟩ := hr
  have H := (comm_diag_iff_u4 h hd).mp hc
  have hM : (((u4xbElt h ht * r : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      u4xbMat t * sMat h x y c := by
    rw [coe_mul_hypSU, coe_u4xbElt, hrm]
  obtain ⟨e1, e2, e3, -⟩ := u4xbMat_mul_sMat_apply h t x y c
  have hy : h.bar y = 0 := by
    have h1 := H ie1 ie2
    rw [hM, e1] at h1
    have h2 : (q ie1 - q ie2) * h.bar y = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h12)
  have hx : h.bar x = 0 := by
    have h1 := H ie1 if2
    rw [hM, e2] at h1
    have h2 : (q ie1 - q if2) * h.bar x = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h14)
  have hc0 : c = 0 := by
    have h1 := H ie1 if1
    rw [hM, e3] at h1
    have h2 : (q ie1 - q if1) * c = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h13)
  have hy0 : y = 0 := by rw [← h.bar_bar y, hy, map_zero]
  have hx0 : x = 0 := by rw [← h.bar_bar x, hx, map_zero]
  refine ⟨t, ht, ?_⟩
  rw [hM, hx0, hy0, hc0, sMat_zero_u4, Matrix.mul_one]

theorem mem_radQ_of_comm_diag {d u : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (h24 : q ie2 ≠ q if2)
    (hu : u ∈ hypUnitriangular h 2 0) (hc : d * u = u * d) : u ∈ radQ h := by
  obtain ⟨t, ht, r, hr, rfl⟩ := exists_u4xbElt_mul_of_mem h hu
  have hr' := hr
  obtain ⟨x, y, c, -, hrm⟩ := hr
  have H := (comm_diag_iff_u4 h hd).mp hc
  have hM : (((u4xbElt h ht * r : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      u4xbMat t * sMat h x y c := by
    rw [coe_mul_hypSU, coe_u4xbElt, hrm]
  have ht0 : t = 0 := by
    have h1 := H ie2 if2
    rw [hM, (u4xbMat_mul_sMat_apply h t x y c).2.2.2] at h1
    have h2 : (q ie2 - q if2) * t = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h24)
  have h1 : u4xbElt h ht = 1 := hypSU_ext h (by rw [coe_u4xbElt, ht0, u4xbMat_zero]; rfl)
  rw [h1, one_mul]
  exact hr'

theorem mem_radQ2_of_comm_diag {d u : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (h43 : q if2 ≠ q if1)
    (hu : u ∈ hypUnitriangular h 2 0) (hc : d * u = u * d) : u ∈ radQ2 h := by
  obtain ⟨t, ht, r, hr, rfl⟩ := exists_u4xbElt_mul_of_mem h hu
  obtain ⟨x, y, c, hadm, hrm⟩ := hr
  have H := (comm_diag_iff_u4 h hd).mp hc
  have hy : y = 0 := by
    have h1 := H if2 if1
    rw [coe_mul_hypSU, coe_u4xbElt, hrm, u4xbMat_mul_sMat_if2_if1] at h1
    have h2 : (q if2 - q if1) * y = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h43)
  subst hy
  exact (radQ2 h).mul_mem (u4xbElt_mem_radQ2 h ht)
    ((mem_radQ_inf_radQ2_iff h).mpr ⟨x, c, (sAdm_of_y_zero_iff h).mp hadm, hrm⟩).2

theorem mem_radQ_inf_radQ2_of_comm_diag {d r : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (h43 : q if2 ≠ q if1)
    (hr : r ∈ radQ h) (hc : d * r = r * d) : r ∈ radQ h ⊓ radQ2 h := by
  obtain ⟨x, y, c, hadm, hrm⟩ := hr
  have H := (comm_diag_iff_u4 h hd).mp hc
  have hy : y = 0 := by
    have h1 := H if2 if1
    rw [hrm, sMat_if2_if1] at h1
    have h2 : (q if2 - q if1) * y = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h43)
  subst hy
  exact (mem_radQ_inf_radQ2_iff h).mpr ⟨x, c, (sAdm_of_y_zero_iff h).mp hadm, hrm⟩

theorem mem_u4RootA_of_comm_diag {d r : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (h23 : q ie2 ≠ q if1)
    (h13 : q ie1 ≠ q if1) (hr : r ∈ radQ h) (hc : d * r = r * d) : r ∈ u4RootA h := by
  obtain ⟨x, y, c, -, hrm⟩ := hr
  have H := (comm_diag_iff_u4 h hd).mp hc
  have hx : x = 0 := by
    have h1 := H ie2 if1
    rw [hrm, sMat_ie2_if1] at h1
    have h2 : (q ie2 - q if1) * x = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h23)
  have hc0 : c = 0 := by
    have h1 := H ie1 if1
    rw [hrm, sMat_ie1_if1] at h1
    have h2 : (q ie1 - q if1) * c = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h13)
  exact ⟨y, by rw [hrm, hx, hc0]⟩

theorem comm_of_mem_u4RootB {d g : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (h24 : q ie2 = q if2)
    (hg : g ∈ u4RootB h) : d * g = g * d := by
  obtain ⟨t, -, hgm⟩ := hg
  refine (comm_diag_iff_u4 h hd).mpr fun i j => ?_
  rw [hgm, u4xbMat_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [one_apply, h24, mul_comm]

theorem comm_of_mem_u4RootA {d g : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (h43 : q if2 = q if1)
    (hg : g ∈ u4RootA h) : d * g = g * d := by
  obtain ⟨b1, b2, -, -⟩ := diag_rel_u4 h hd
  have h12 : q ie1 = q ie2 := by
    rw [h43, b1] at b2
    exact inv_injective b2
  obtain ⟨y, hgm⟩ := hg
  refine (comm_diag_iff_u4 h hd).mpr fun i j => ?_
  rw [hgm, sMat_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [one_apply, h12, h43, mul_comm]

omit [Field K] in
private theorem eq_one_of_mul_self_u4 {F : Type} [Field F] [CharP F 2] {x : F} (hx : x * x = 1) :
    x = 1 := by
  have h0 : (x + 1) * (x + 1) = 0 := by
    have e : (x + 1) * (x + 1) = x * x + (x + x) + 1 := by ring
    rw [e, hx, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h1 : x + 1 = 0 := mul_self_eq_zero.mp h0
  rw [← CharTwo.neg_eq (1 : F)]
  exact eq_neg_of_add_eq_zero_left h1

private theorem prod_ix_u4 (g : Ix → K) : ∏ a, g a = g ie1 * g ie2 * g if1 * g if2 := by
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul, ie1, ie2, if1, if2]
  ring

theorem eq_one_of_comm_u4Roots {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q)
    (ha : d * syElt h 1 = syElt h 1 * d)
    (hb : d * u4xbElt h (map_one h.bar) = u4xbElt h (map_one h.bar) * d) : d = 1 := by
  have := h.charP
  have H1 := (comm_diag_iff_u4 h hd).mp ha if2 if1
  rw [coe_syElt, sMat_if2_if1, mul_one, one_mul] at H1
  have H2 := (comm_diag_iff_u4 h hd).mp hb ie2 if2
  rw [coe_u4xbElt, u4xbMat_apply] at H2
  simp at H2
  obtain ⟨b1, b2, b3, -⟩ := diag_rel_u4 h hd
  have h12 : q ie1 = q ie2 := by
    rw [H1, b1] at b2
    exact inv_injective b2
  have hdet := (mem_gramSU.mp d.2).2
  rw [hd, det_diagonal, prod_ix_u4, h12, H2, H1] at hdet
  have h4 : (q if1 * q if1) * (q if1 * q if1) = 1 := by rw [← hdet]; ring
  have hl : q if1 = 1 := eq_one_of_mul_self_u4 (eq_one_of_mul_self_u4 h4)
  have hq : q = fun _ => 1 := by
    funext i
    rcases ix_cases i with rfl | rfl | rfl | rfl
    · rw [h12, H2, H1, hl]
    · rw [H2, H1, hl]
    · exact hl
    · rw [H1, hl]
  apply hypSU_ext h
  rw [hd, hq, diagonal_one]
  rfl

theorem mem_radQ_inf_radQ2_iff_comm {g : hypSU h 2 0} :
    g ∈ radQ h ⊓ radQ2 h ↔ g ∈ radQ h ∧ ∀ x ∈ u4RootB h, g * x = x * g := by
  constructor
  · intro hg
    obtain ⟨x, c, -, hgm⟩ := (mem_radQ_inf_radQ2_iff h).mp hg
    refine ⟨hg.1, fun b hb => ?_⟩
    obtain ⟨t, ht, hbm⟩ := hb
    apply hypSU_ext h
    rw [coe_mul_hypSU, coe_mul_hypSU, hgm, hbm, u4xbMat_mul_sMat h ht]
    simp
  · rintro ⟨hgQ, hcomm⟩
    obtain ⟨x, y, c, hadm, hgm⟩ := hgQ
    have h1 : h.bar (1 : K) = 1 := map_one _
    have H := congrFun (congrFun (congrArg (fun z : hypSU h 2 0 => ((z : GL Ix K) : Matrix Ix Ix K))
      (hcomm _ (u4xbElt_mem_u4RootB h h1))) ie2) if1
    simp only [coe_mul_hypSU, hgm, coe_u4xbElt] at H
    rw [mul_apply, sum_ix, mul_apply, sum_ix] at H
    simp [u4xbMat_apply, sMat_apply, one_apply] at H
    subst H
    exact (mem_radQ_inf_radQ2_iff h).mpr ⟨x, c, (sAdm_of_y_zero_iff h).mp hadm, hgm⟩

theorem mem_zRad_iff_comm {g : hypSU h 2 0} :
    g ∈ zRad h ↔ g ∈ radQ h ∧ ∀ x ∈ radQ h, g * x = x * g := by
  rw [← centerOf_radQ h, CFSG.Quasithin.centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact and_congr_right fun _ => forall₂_congr fun x _ => eq_comm

end CFSG.Quasithin.F112R.St84

end
