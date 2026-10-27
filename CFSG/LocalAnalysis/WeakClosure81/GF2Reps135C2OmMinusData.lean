module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums
import CFSG.LieType.Steinberg.CentralExt.TorusLift
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.RootSystem
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped Matrix

instance omMinus_finite_spin {K : Type} [Field K] [Finite K] (b c : K) :
    Finite (spinGroup (quadMinus 4 K b c)) := by
  have : FiniteDimensional K (CliffordAlgebra (quadMinus 4 K b c)) :=
    finiteDimensional_cliffordAlgebra' _
  have : Finite (CliffordAlgebra (quadMinus 4 K b c)) := Module.finite_of_finite K
  infer_instance

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

noncomputable abbrev o8mDatum (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CurtisDatum (spinGroup (quadMinus 4 K b c))
      (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem 2 :=
  SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ

noncomputable abbrev o8mS (i : Fin 3) : (coxeterMatrix (isFiniteType_cartanB (4 - 1))).Group :=
  (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.simple i

variable (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
variable {k : Type} [Field k] [CharP k 2]

private theorem o8m_not_isLeftDescent_simple {B : Type*} {M : CoxeterMatrix B} {W : Type*}
    [Group W] {cs : CoxeterSystem M W} {i j : B} (h : i ≠ j) :
    ¬ cs.IsLeftDescent (cs.simple j) i := by
  intro hd
  rw [CoxeterSystem.IsLeftDescent, CoxeterSystem.length_simple] at hd
  have h0 : cs.simple i * cs.simple j = 1 :=
    cs.length_eq_zero_iff.mp (Nat.lt_one_iff.mp hd)
  exact h (cs.simple_injective (by
    rw [eq_inv_of_mul_eq_one_right h0, CoxeterSystem.inv_simple]))

private theorem o8m_mul_self_ne_one_of_ne_one {k : Type*} [Field k] [CharP k 2] {a : k}
    (ha : a ≠ 1) : a * a ≠ 1 := by
  rw [← pow_two, sq_ne_one_iff]
  exact ⟨ha, by simpa [CharTwo.neg_eq] using ha⟩

private theorem o8m_weylAction_s1s2_single_one :
    weylAction (isFiniteType_cartanB (4 - 1))
      ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.simple 1 *
       (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.simple 2)
      (Pi.single (1 : Fin 3) 1) = Pi.single 1 1 + 2 • Pi.single 2 1 := by
  rw [weylAction_mul_apply, weylAction_simple, weylAction_simple, reflection_apply,
    reflection_apply]
  ext a
  fin_cases a <;> simp [cartanB, Fin.sum_univ_three]

omit [CharP K 2] in
private theorem o8m_minusTorus_of_lt_eq_bot (hK : Nat.card K = 2) {i : Fin 3}
    (hi : i.val + 1 < 4 - 1) : minusTorus 4 hirrQ i = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  rw [minusTorus_of_lt 4 hirrQ hi, Subgroup.eq_bot_iff_forall]
  rintro x ⟨u, rfl⟩
  have hu : u = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact Units.ext (by simpa using h)
  rw [hu, map_one]

private theorem o8mDatum_H_le_shortTorus (hK : Nat.card K = 2) :
    (o8mDatum hirrQ).H ≤ shortTorus 4 hirrQ 2 := by
  change (⨆ k, minusTorus 4 hirrQ k) ≤ shortTorus 4 hirrQ 2
  refine iSup_le fun k => ?_
  by_cases hk : k.val + 1 < 4 - 1
  · rw [o8m_minusTorus_of_lt_eq_bot hirrQ hK hk]
    exact bot_le
  · have hk2 : k = 2 := by
      apply Fin.ext
      show k.val = 2
      omega
    rw [minusTorus_of_not_lt 4 hirrQ hk, hk2]

omit [CharP K 2] in
private theorem o8mDatum_shortWeyl_inv_conj_of_mem {h : spinGroup (quadMinus 4 K b c)}
    (hh : h ∈ shortTorus 4 hirrQ 2) :
    (minusWeyl 4 hirrQ 2)⁻¹ * h * (minusWeyl 4 hirrQ 2) = h⁻¹ := by
  have := fact_shortField hirrQ
  have := finite_shortField (b := b) (c := c)
  obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff 4 hirrQ 2).mp hh
  obtain ⟨t, ht, he⟩ := exists_shortRels_h_eq 4 hirrQ 2 ha
  rw [← he]
  set R := shortRels 4 hirrQ 2 with hR
  have hC : ∀ s t : ShortField b c, s ≠ 0 → t ≠ 0 → R.h (s * t) = R.h s * R.h t :=
    fun s t hs ht => R.h_mul hs ht
  have hw : minusWeyl 4 hirrQ 2 = R.w 1 := by
    rw [minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num), shortRels_w_one]
  rw [hw]
  have hres := CFSG.LieType.Steinberg.CentralExt.TorusLift.w_conj_h (R := R) (t := -1)
    (u := t) (by norm_num) ht
  rw [← CFSG.LieType.Steinberg.RankOneRels.w_inv (R := R) (t := 1), inv_inv] at hres
  rwa [← R.h_inv hC ht] at hres

private theorem o8mDatum_dScalar_eq_one_of_trivial {χ : spinGroup (quadMinus 4 K b c) → k}
    (i : Fin 3) (hχ : ∀ h ∈ minusTorus 4 hirrQ i, χ h = 1) :
    (o8mDatum hirrQ).dScalar χ i = 1 := by
  have h := CFSG.LieType.Steinberg.curtisDatumOf_dScalar_eq_neg_one
    (minusDatum_isCTGroupDatum 4 hirrQ (by norm_num))
    (minusDatum_steinbergExtras 4 hirrQ)
    (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirrQ (by norm_num)) 2
    (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirrQ hγ) χ i hχ
  have h' : (o8mDatum hirrQ).dScalar χ i = -1 := h
  rwa [CharTwo.neg_eq] at h'

private theorem o8mDatum_d'Scalar_eq_one_of_trivial {χ : spinGroup (quadMinus 4 K b c) → k}
    (i : Fin 3) (hχ : ∀ h ∈ minusTorus 4 hirrQ i, χ h = 1) :
    (o8mDatum hirrQ).d'Scalar χ i = 1 := by
  have h := CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
    (minusDatum_isCTGroupDatum 4 hirrQ (by norm_num))
    (minusDatum_steinbergExtras 4 hirrQ)
    (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirrQ (by norm_num)) 2
    (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirrQ hγ) χ i
  have h' : (o8mDatum hirrQ).d'Scalar χ i = (o8mDatum hirrQ).dScalar χ i := h
  rw [h']
  exact o8mDatum_dScalar_eq_one_of_trivial hirrQ i hχ

theorem o8mDatum_n (i : Fin 3) : (o8mDatum hirrQ).n i = minusWeyl 4 hirrQ i := by
  rfl

theorem o8mDatum_X (i : Fin 3) : (o8mDatum hirrQ).X i = minusRootGroup 4 hirrQ (Pi.single i 1) := by
  rfl

theorem o8mDatum_nW_simple (i : Fin 3) : (o8mDatum hirrQ).nW (o8mS i) = (o8mDatum hirrQ).n i := by
  have h := (o8mDatum hirrQ).nW_simple_mul 1 i (by
    rw [mul_one, (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.length_simple]
    exact (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.length_one ▸ rfl)
  simp only [mul_one, (o8mDatum hirrQ).nW_one] at h
  exact h

theorem o8mDatum_nW_zero_two :
    (o8mDatum hirrQ).nW (o8mS 0 * o8mS 2) = (o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2 := by
  have hlen : (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.length
      ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.simple 0 * o8mS 2) =
      (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.length (o8mS 2) + 1 :=
    ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.not_isLeftDescent_iff).mp
      (o8m_not_isLeftDescent_simple
        (cs := (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem)
        (i := 0) (j := 2) (by decide))
  have h := (o8mDatum hirrQ).nW_simple_mul (o8mS 2) 0 hlen
  rw [h, o8mDatum_nW_simple hirrQ 2]

theorem o8mDatum_nW_one_two_one :
    (o8mDatum hirrQ).nW (o8mS 1 * o8mS 2 * o8mS 1) =
      (o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1 := by
  have hnd1 : ¬ (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.IsLeftDescent
      (o8mS 1) 2 :=
    o8m_not_isLeftDescent_simple
      (cs := (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem)
      (i := 2) (j := 1) (by decide)
  have hlen1 := ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem
    ).not_isLeftDescent_iff.mp hnd1
  have hnd2 : ¬ (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.IsLeftDescent
      (o8mS 2 * o8mS 1) 1 := by
    rw [show o8mS 2 * o8mS 1 = (o8mS 1 * o8mS 2)⁻¹ from by
      rw [mul_inv_rev, CoxeterSystem.inv_simple, CoxeterSystem.inv_simple]]
    rw [CoxeterSystem.isLeftDescent_inv_iff]
    exact (CFSG.LieType.RootSystem.nonneg_iff_not_isRightDescent
      (isFiniteType_cartanB (4 - 1)) (o8mS 1 * o8mS 2) 1).mp (by
        rw [o8m_weylAction_s1s2_single_one]
        intro a
        fin_cases a <;> simp)
  have hlen2 := ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem
    ).not_isLeftDescent_iff.mp hnd2
  have h1 := (o8mDatum hirrQ).nW_simple_mul (o8mS 1) 2 hlen1
  have h2 := (o8mDatum hirrQ).nW_simple_mul (o8mS 2 * o8mS 1) 1 hlen2
  rw [mul_assoc, h2, h1, o8mDatum_nW_simple hirrQ 1]
  group

theorem o8mDatum_card_X_short (hK : Nat.card K = 2) : Nat.card ((o8mDatum hirrQ).X 2) = 4 := by
  rw [o8mDatum_X, minusRootGroup_single_of_not_lt 4 hirrQ (k := 2) (by norm_num)]
  change Nat.card (Set.range (shortPosHom 4 hirrQ 2)) = 4
  rw [Nat.card_range_of_injective (shortPosHom_injective 4 hirrQ 2)]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hK]
  norm_num

theorem o8mDatum_dScalar_long (hK : Nat.card K = 2) {χ : spinGroup (quadMinus 4 K b c) → k}
    (hχ : χ 1 = 1) {i : Fin 3} (hi : i.val < 2) : (o8mDatum hirrQ).dScalar χ i = 1 := by
  refine o8mDatum_dScalar_eq_one_of_trivial hirrQ i fun h hh => ?_
  have hbot := o8m_minusTorus_of_lt_eq_bot hirrQ hK (by omega : i.val + 1 < 4 - 1)
  rw [hbot] at hh
  rw [show h = 1 from by simpa using hh, hχ]

theorem o8mDatum_d'Scalar_long (hK : Nat.card K = 2) {χ : spinGroup (quadMinus 4 K b c) → k}
    (hχ : χ 1 = 1) {i : Fin 3} (hi : i.val < 2) : (o8mDatum hirrQ).d'Scalar χ i = 1 := by
  refine o8mDatum_d'Scalar_eq_one_of_trivial hirrQ i fun h hh => ?_
  have hbot := o8m_minusTorus_of_lt_eq_bot hirrQ hK (by omega : i.val + 1 < 4 - 1)
  rw [hbot] at hh
  rw [show h = 1 from by simpa using hh, hχ]

theorem o8mDatum_dScalar_short_of_trivial (hK : Nat.card K = 2)
    {χ : spinGroup (quadMinus 4 K b c) → k} (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) :
    (o8mDatum hirrQ).dScalar χ 2 = 1 ∧ (o8mDatum hirrQ).d'Scalar χ 2 = 1 := by
  have _ := hK
  have htriv : ∀ h ∈ minusTorus 4 hirrQ 2, χ h = 1 :=
    fun h hh => hχ h (le_iSup (fun j => minusTorus 4 hirrQ j) 2 hh)
  exact ⟨o8mDatum_dScalar_eq_one_of_trivial hirrQ 2 htriv,
    o8mDatum_d'Scalar_eq_one_of_trivial hirrQ 2 htriv⟩

theorem o8mDatum_dScalar_short_of_ne (hK : Nat.card K = 2) {V : Type} [AddCommGroup V]
    [Module k V] {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V} {y : V}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ) (hχ : ∃ h ∈ (o8mDatum hirrQ).H, χ h ≠ 1) :
    (o8mDatum hirrQ).dScalar χ 2 = 0 ∧ (o8mDatum hirrQ).d'Scalar χ 2 = 0 := by
  obtain ⟨h₀, hh₀, hχh₀⟩ := hχ
  have hshort : h₀ ∈ shortTorus 4 hirrQ 2 := o8mDatum_H_le_shortTorus hirrQ hK hh₀
  have hinv : (minusWeyl 4 hirrQ 2)⁻¹ * h₀⁻¹ * (minusWeyl 4 hirrQ 2) = h₀ := by
    have h := o8mDatum_shortWeyl_inv_conj_of_mem hirrQ hshort
    have e : (minusWeyl 4 hirrQ 2)⁻¹ * h₀⁻¹ * (minusWeyl 4 hirrQ 2) =
        ((minusWeyl 4 hirrQ 2)⁻¹ * h₀ * (minusWeyl 4 hirrQ 2))⁻¹ := by group
    rw [e, h, inv_inv]
  have hcond : χ h₀ * χ ((minusWeyl 4 hirrQ 2)⁻¹ * h₀⁻¹ * (minusWeyl 4 hirrQ 2)) ≠ 1 := by
    rw [hinv]
    exact o8m_mul_self_ne_one_of_ne_one hχh₀
  have hd := CFSG.LieType.Steinberg.curtisDatumOf_dScalar_eq_zero_of_conj
    (minusDatum_isCTGroupDatum 4 hirrQ (by norm_num))
    (minusDatum_steinbergExtras 4 hirrQ)
    (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirrQ (by norm_num)) 2
    (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirrQ hγ)
    χ (fun a ha b hb => ht.chi_mul ha hb) (2 : Fin 3) hh₀ hcond
  have hd' := CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
    (minusDatum_isCTGroupDatum 4 hirrQ (by norm_num))
    (minusDatum_steinbergExtras 4 hirrQ)
    (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirrQ (by norm_num)) 2
    (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirrQ hγ) χ (2 : Fin 3)
  have hd'' : (o8mDatum hirrQ).d'Scalar χ 2 = (o8mDatum hirrQ).dScalar χ 2 := hd'
  exact ⟨hd, by rw [hd'']; exact hd⟩

omit [CharP k 2] in
theorem omMinus_isSimpleRep_trivial (G : Type) [Group G] :
    IsSimpleRep (Representation.trivial k G k) := by
  refine ⟨inferInstance, fun W _ => Ideal.eq_bot_or_top W⟩

theorem isCurtisType_omMinus_two_trivial {χ : spinGroup (quadMinus 4 K b c) → k}
    (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) :
    (o8mDatum hirrQ).IsCurtisType (Representation.trivial k (spinGroup (quadMinus 4 K b c)) k)
      1 χ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, one_ne_zero, ?_, ?_⟩
  · intro u _
    rw [Representation.trivial_apply]
  · intro h hh
    rw [Representation.trivial_apply, hχ h hh, one_smul]
  · intro s
    let D := o8mDatum hirrQ
    have : Fintype (D.X s) := Fintype.ofFinite _
    rw [CurtisDatum.heckeT_apply D]
    simp only [Representation.trivial_apply, Pi.zero_apply, zero_smul]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul k,
      (CharP.cast_eq_zero_iff k 2 (Nat.card (D.X s))).mpr (D.dvd_card_X s), zero_smul]

omit [Finite K] [CharP K 2] [CharP k 2] in
private theorem o8mNatural_map_vector (φ : K →+* k) (g : spinGroup (quadMinus 4 K b c))
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    SmallO8mCurtis.naturalRep 4 b c φ g (fun a => φ (v a)) =
      fun a => φ (spinAction (quadMinus 4 K b c) g v a) := by
  rw [SmallO8mCurtis.naturalRep_apply]
  have hact : (mat 4 g) *ᵥ v = spinAction (quadMinus 4 K b c) g v := by
    rw [mat, coe_spinMatrix]
    exact LinearMap.toMatrix'_mulVec _ v
  ext a
  rw [show Matrix.mulVec ((mat 4 g).map φ) (fun a => φ (v a)) a =
      φ (Matrix.mulVec (mat 4 g) v a) from
    (RingHom.map_mulVec φ (mat 4 g) v a).symm]
  rw [hact]

omit [Finite K] [CharP k 2] in
private theorem o8mNatural_Weyl_highest (φ : K →+* k) (i : Fin 3) :
    SmallO8mCurtis.naturalRep 4 b c φ (minusWeyl 4 hirrQ i) SmallO8mCurtis.highestVec =
      if i = 0 then Pi.single (.inl 1) 1 else SmallO8mCurtis.highestVec := by
  have hact : spinAction (quadMinus 4 K b c) (minusWeyl 4 hirrQ i) (eVec 4 0) =
      if i = 0 then eVec 4 1 else eVec 4 0 := by
    fin_cases i
    · change spinAction (quadMinus 4 K b c) (minusWeyl 4 hirrQ 0) (eVec 4 0) = _
      rw [minusWeyl_of_lt 4 hirrQ (k := 0) (by norm_num)]
      have h := (minusFrame 4 b c).toHypFrame.spinAction_longWeyl_vec_left
        (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false
      simpa [minusFrame_vec, minusVec_true, eVec, CharTwo.neg_eq] using h
    · change spinAction (quadMinus 4 K b c) (minusWeyl 4 hirrQ 1) (eVec 4 0) = _
      rw [minusWeyl_of_lt 4 hirrQ (k := 1) (by norm_num)]
      have h := (minusFrame 4 b c).toHypFrame.spinAction_longWeyl_vec_of_ne
        (succ_ne_of_lt 4 (k := 1) (by norm_num)) true false
        (k := 0) (by decide) (by decide) true
      simpa [minusFrame_vec, minusVec_true] using h
    · change spinAction (quadMinus 4 K b c) (minusWeyl 4 hirrQ 2) (eVec 4 0) = _
      rw [minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num)]
      simpa [shortWeyl] using spinAction_shortWeylElt_eVec_of_ne 4 hirrQ (i := 2) (j := 0)
        (by decide) planeOne
  have h := o8mNatural_map_vector φ (minusWeyl 4 hirrQ i) (eVec 4 0)
  rw [hact] at h
  have hvec : ∀ j : Fin 3, (fun a => φ (eVec 4 j a)) =
      (Pi.single (.inl j) 1 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → k) := by
    intro j
    ext a
    simp [eVec, Pi.single_apply]
  simp only [hvec] at h
  split_ifs at h ⊢ <;> simpa only [hvec, SmallO8mCurtis.highestVec] using h

omit [Finite K] [CharP K 2] [CharP k 2] in
private theorem o8mNatural_first_X_next (φ : K →+* k) (a : K) :
    SmallO8mCurtis.naturalRep 4 b c φ
        ((minusFrame 4 b c).longRoot (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false
          (.ofAdd a)) (Pi.single (.inl 1) 1) =
      Pi.single (.inl 1) 1 + φ a • SmallO8mCurtis.highestVec := by
  have hact := (minusFrame 4 b c).toHypFrame.spinAction_longRoot_vec_not_right
    (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false a
  have h := o8mNatural_map_vector φ
    ((minusFrame 4 b c).longRoot (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false
      (.ofAdd a)) (eVec 4 1)
  rw [show spinAction (quadMinus 4 K b c)
        ((minusFrame 4 b c).longRoot (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false
          (.ofAdd a)) (eVec 4 1) = eVec 4 1 + a • eVec 4 0 from
        hact] at h
  have hvec : (fun i => φ (eVec 4 1 i)) =
      (Pi.single (.inl 1) 1 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → k) := by
    ext i
    simp [eVec, Pi.single_apply]
  rw [hvec] at h
  convert h using 1
  ext i
  simp [SmallO8mCurtis.highestVec, eVec, Pi.single_apply, map_add, Pi.smul_apply]
  split_ifs <;> simp_all

omit [CharP k 2] in
private theorem o8mNatural_fix_H (hK : Nat.card K = 2) (φ : K →+* k)
    {h : spinGroup (quadMinus 4 K b c)} (hh : h ∈ (o8mDatum hirrQ).H) :
    SmallO8mCurtis.naturalRep 4 b c φ h SmallO8mCurtis.highestVec =
      SmallO8mCurtis.highestVec := by
  have hshort := o8mDatum_H_le_shortTorus hirrQ hK hh
  have := fact_shortField hirrQ
  have := finite_shortField (b := b) (c := c)
  obtain ⟨a, -, rfl⟩ := (mem_shortTorus_iff 4 hirrQ 2).mp hshort
  have h := o8mNatural_map_vector φ (shortTorusElt 4 hirrQ 2 a) (eVec 4 0)
  rw [show spinAction (quadMinus 4 K b c) (shortTorusElt 4 hirrQ 2 a) (eVec 4 0) = eVec 4 0
      from spinAction_shortTorusElt_eVec_of_ne 4 hirrQ (i := 2) (j := 0) (by decide) a] at h
  have hvec : (fun b => φ (eVec 4 0 b)) = (SmallO8mCurtis.highestVec (k := k)) := by
    ext b
    simp [eVec, SmallO8mCurtis.highestVec, Pi.single_apply]
  rw [← hvec]
  exact h

omit [CharP k 2] in
private theorem o8mNatural_highestChar_eq_one (hK : Nat.card K = 2) (φ : K →+* k)
    {h : spinGroup (quadMinus 4 K b c)} (hh : h ∈ (o8mDatum hirrQ).H) :
    SmallO8mCurtis.highestChar φ h = 1 := by
  have hfix := o8mNatural_fix_H hirrQ hK φ hh
  have hchar := SmallO8mCurtis.naturalRep_highestChar hirrQ φ hh
  rw [hfix] at hchar
  have := congrFun hchar (.inl 0)
  simpa [SmallO8mCurtis.highestVec] using this.symm

private theorem o8mX0_bijective :
    Function.Bijective (fun a : K =>
      (⟨(minusFrame 4 b c).longRoot (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false
          (.ofAdd a),
        by
          change _ ∈ minusRootGroup 4 hirrQ (Pi.single 0 1)
          rw [minusRootGroup_single_of_lt 4 hirrQ (k := 0) (by norm_num)]
          exact ⟨.ofAdd a, rfl⟩⟩ : (o8mDatum hirrQ).X 0)) := by
  refine ⟨fun a a' h => ?_, ?_⟩
  · have hx := congrArg Subtype.val h
    exact Multiplicative.ofAdd.injective
      ((minusFrame 4 b c).toHypFrame.longRoot_injective
        (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false hx)
  · intro x
    have hx : (x : spinGroup _) ∈ minusRootGroup 4 hirrQ (Pi.single 0 1) := x.2
    rw [minusRootGroup_single_of_lt 4 hirrQ (k := 0) (by norm_num)] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a.toAdd, Subtype.ext ha⟩

private theorem o8mNatural_heckeT_zero (hK : Nat.card K = 2) (φ : K →+* k) :
    (o8mDatum hirrQ).heckeT (SmallO8mCurtis.naturalRep 4 b c φ) 0
      (SmallO8mCurtis.highestVec (k := k)) = 1 • SmallO8mCurtis.highestVec (k := k) := by
  classical
  have : Finite (spinGroup (quadMinus 4 K b c)) := inferInstance
  let D := o8mDatum hirrQ
  have : Fintype (D.X 0) := Fintype.ofFinite _
  have : Fintype K := Fintype.ofFinite _
  change D.heckeT (SmallO8mCurtis.naturalRep 4 b c φ) 0 SmallO8mCurtis.highestVec = _
  rw [D.heckeT_apply]
  have hn : D.n 0 = minusWeyl 4 hirrQ 0 := o8mDatum_n hirrQ 0
  have hmul : ∀ x : D.X 0, SmallO8mCurtis.naturalRep 4 b c φ ((x : _) * D.n 0)
        SmallO8mCurtis.highestVec =
      SmallO8mCurtis.naturalRep 4 b c φ (x : _)
        (SmallO8mCurtis.naturalRep 4 b c φ (D.n 0) SmallO8mCurtis.highestVec) := by
    intro x
    rw [map_mul, Module.End.mul_apply]
  have hsum : (∑ x : D.X 0, SmallO8mCurtis.naturalRep 4 b c φ ((x : _) * D.n 0)
        SmallO8mCurtis.highestVec) =
      ∑ x : D.X 0, SmallO8mCurtis.naturalRep 4 b c φ (x : _)
        (Pi.single (.inl 1) 1) :=
    Finset.sum_congr rfl fun x _ => by
      rw [hmul, hn, o8mNatural_Weyl_highest hirrQ φ 0, if_pos rfl]
  rw [hsum]
  let f : K → D.X 0 := fun a =>
    ⟨(minusFrame 4 b c).longRoot (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false (.ofAdd a),
      by
        change _ ∈ minusRootGroup 4 hirrQ (Pi.single 0 1)
        rw [minusRootGroup_single_of_lt 4 hirrQ (k := 0) (by norm_num)]
        exact ⟨.ofAdd a, rfl⟩⟩
  have hf : Function.Bijective f := o8mX0_bijective hirrQ
  rw [← (Equiv.ofBijective f hf).sum_comp]
  simp_rw [Equiv.ofBijective_apply, show ∀ a : K,
    SmallO8mCurtis.naturalRep 4 b c φ (f a : spinGroup _) (Pi.single (.inl 1) 1) =
      Pi.single (.inl 1) 1 + φ a • SmallO8mCurtis.highestVec from
    fun a => o8mNatural_first_X_next φ a]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
    ← Finset.sum_smul, ← map_sum]
  have hcard : (Fintype.card K : k) = 0 := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact CharTwo.two_eq_zero
  have h01 : ({0, 1} : Finset K) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (zero_ne_one : (0 : K) ≠ 1), ← Nat.card_eq_fintype_card, hK]
  have hsumK : ∑ a : K, a = 1 := by
    rw [← h01, Finset.sum_pair (zero_ne_one : (0 : K) ≠ 1)]
    simp
  rw [hcard, zero_smul, hsumK, map_one, one_smul, zero_add]
  simp

private theorem o8mNatural_heckeT_ne (φ : K →+* k) {i : Fin 3} (hi : i ≠ 0) :
    (o8mDatum hirrQ).heckeT (SmallO8mCurtis.naturalRep 4 b c φ) i
      (SmallO8mCurtis.highestVec (k := k)) = 0 • SmallO8mCurtis.highestVec (k := k) := by
  classical
  have : Finite (spinGroup (quadMinus 4 K b c)) := inferInstance
  let D := o8mDatum hirrQ
  have : Fintype (D.X i) := Fintype.ofFinite _
  change D.heckeT (SmallO8mCurtis.naturalRep 4 b c φ) i SmallO8mCurtis.highestVec = _
  rw [D.heckeT_apply]
  have hn : D.n i = minusWeyl 4 hirrQ i := o8mDatum_n hirrQ i
  have hmul : ∀ x : D.X i, SmallO8mCurtis.naturalRep 4 b c φ ((x : _) * D.n i)
        SmallO8mCurtis.highestVec =
      SmallO8mCurtis.naturalRep 4 b c φ (x : _)
        (SmallO8mCurtis.naturalRep 4 b c φ (D.n i) SmallO8mCurtis.highestVec) := by
    intro x
    rw [map_mul, Module.End.mul_apply]
  have hsum : (∑ x : D.X i, SmallO8mCurtis.naturalRep 4 b c φ ((x : _) * D.n i)
        SmallO8mCurtis.highestVec) =
      ∑ x : D.X i, SmallO8mCurtis.naturalRep 4 b c φ (x : _)
        SmallO8mCurtis.highestVec :=
    Finset.sum_congr rfl fun x _ => by
      rw [hmul, hn, o8mNatural_Weyl_highest hirrQ φ i, if_neg hi]
  rw [hsum]
  have hfix : ∀ x : D.X i, SmallO8mCurtis.naturalRep 4 b c φ (x : _)
      SmallO8mCurtis.highestVec = SmallO8mCurtis.highestVec :=
    fun x => (D.mem_fixU (SmallO8mCurtis.naturalRep 4 b c φ)).mp
      (SmallO8mCurtis.naturalRep_highestVec_mem_fixU hirrQ φ) _ (D.X_le i x.2)
  have hcount : (Fintype.card (D.X i) : k) = 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff k 2 (Nat.card (D.X i))).mpr (D.dvd_card_X i)
  rw [Finset.sum_congr rfl (fun x _ => hfix x), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k, hcount, zero_smul]
  simp

private theorem o8mNatural_heckeT (hK : Nat.card K = 2) (φ : K →+* k) (i : Fin 3) :
    (o8mDatum hirrQ).heckeT (SmallO8mCurtis.naturalRep 4 b c φ) i
      (SmallO8mCurtis.highestVec (k := k)) =
      (if i.val = 0 then 1 else 0) • SmallO8mCurtis.highestVec (k := k) := by
  by_cases hi : i = 0
  · subst hi
    simpa using o8mNatural_heckeT_zero hirrQ hK φ
  · have hne : (i.val : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    rw [if_neg hne]
    exact o8mNatural_heckeT_ne hirrQ φ hi

theorem isCurtisType_omMinus_two_natural (hK : Nat.card K = 2) (φ : K →+* k)
    {χ : spinGroup (quadMinus 4 K b c) → k} (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) :
    (o8mDatum hirrQ).IsCurtisType (SmallO8mCurtis.naturalRep 4 b c φ)
      (SmallO8mCurtis.highestVec (k := k)) χ (fun s => if s.val = 0 then 1 else 0) := by
  refine ⟨SmallO8mCurtis.naturalRep_highestVec_mem_fixU hirrQ φ, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h (.inl 0)
    simp [SmallO8mCurtis.highestVec] at this
  · intro h hh
    rw [SmallO8mCurtis.naturalRep_highestChar hirrQ φ hh,
      o8mNatural_highestChar_eq_one hirrQ hK φ hh, hχ h hh, one_smul]
  · intro s
    simpa using o8mNatural_heckeT hirrQ hK φ s

end CFSG.LocalAnalysis.WeakClosure81
