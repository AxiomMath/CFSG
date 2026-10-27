module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUIndex
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUPar
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherBruhat
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private abbrev spUCitedMat {h : UnitaryFieldData p f K} {r ε : ℕ} (g : ↥(hypSU h r ε)) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)

private theorem spUCited_mem_sylow_of_mem_normalizer {G : Type*} [Group G] {T : Sylow 2 G}
    {y : G} (hy : y ∈ Subgroup.normalizer (T : Set G))
    (h2 : IsPGroup 2 (Subgroup.zpowers y)) : y ∈ T := by
  have hsup : IsPGroup 2 (T ⊔ Subgroup.zpowers y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' T.isPGroup' h2 (Subgroup.zpowers_le.mpr hy)
  have hmax : (T ⊔ Subgroup.zpowers y : Subgroup G) = T := T.is_maximal' hsup le_sup_left
  exact (le_of_eq hmax) (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))

private lemma spUCited_posFlag_two_eq (hr : 2 ≤ r) {v : HypIndex r ε → K}
    (hv : v ∈ posFlag r ε K 2) :
    v = v (Sum.inl (⟨0, by omega⟩ : Fin r)) •
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) +
        v (Sum.inl (⟨1, by omega⟩ : Fin r)) •
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) := by
  funext y
  rcases y with j | (k | j)
  · by_cases hj0 : (j : ℕ) = 0
    · have hje : j = (⟨0, by omega⟩ : Fin r) := Fin.ext hj0
      rw [hje]
      simp
    · by_cases hj1 : (j : ℕ) = 1
      · have hje : j = (⟨1, by omega⟩ : Fin r) := Fin.ext hj1
        rw [hje]
        simp
      · have hj2 : 2 ≤ (j : ℕ) := by omega
        have hz : v (Sum.inl j) = 0 := hv (Sum.inl j) (by simpa using hj2)
        have h0 : j ≠ (⟨0, by omega⟩ : Fin r) := fun hh => hj0 (by rw [hh])
        have h1 : j ≠ (⟨1, by omega⟩ : Fin r) := fun hh => hj1 (by rw [hh])
        simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, h0, h1, hz]
  · have hz : v (Sum.inr (Sum.inl k)) = 0 :=
      hv (Sum.inr (Sum.inl k)) (by simp [fullPos_inr_inl]; omega)
    have h0 : (Sum.inr (Sum.inl k) : HypIndex r ε) ≠ Sum.inl (⟨0, by omega⟩ : Fin r) := by
      simp
    have h1 : (Sum.inr (Sum.inl k) : HypIndex r ε) ≠ Sum.inl (⟨1, by omega⟩ : Fin r) := by
      simp
    simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, h0, h1, hz]
  · have hz : v (Sum.inr (Sum.inr j)) = 0 :=
      hv (Sum.inr (Sum.inr j)) (by simp [fullPos_inr_inr]; omega)
    have h0 : (Sum.inr (Sum.inr j) : HypIndex r ε) ≠ Sum.inl (⟨0, by omega⟩ : Fin r) := by
      simp
    have h1 : (Sum.inr (Sum.inr j) : HypIndex r ε) ≠ Sum.inl (⟨1, by omega⟩ : Fin r) := by
      simp
    simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, h0, h1, hz]

private lemma spUCited_unipotent_fixes_two (h : UnitaryFieldData p f K) (hr : 2 ≤ r)
    (hε : ε ≤ 1) {u : ↥(hypSU h r ε)} (hu : u ∈ hypUnitriangular h r ε)
    (hu2 : spUCitedMat u *ᵥ
        (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) =
      (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K)) :
    ∀ v ∈ hypFlag h r ε 2, spUCitedMat u *ᵥ v = v := by
  intro v hv
  have hue1 : spUCitedMat u *ᵥ
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) =
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) := by
    have hv1 : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) ∈
        posFlag r ε K (0 + 1) := by
      intro a ha
      by_cases hae : a = Sum.inl (⟨0, by omega⟩ : Fin r)
      · exfalso
        rw [hae] at ha
        simp only [fullPos_inl] at ha
        omega
      · simp [Pi.single_apply, hae]
    have hsub := unitriangular_sub_mem_posFlag hu (i := 0) hv1
    rw [posFlag_zero, Submodule.mem_bot, sub_eq_zero] at hsub
    exact hsub
  rw [hypFlag_eq_posFlag h hε (by omega : 2 ≤ 2 * r + ε)] at hv
  rw [spUCited_posFlag_two_eq hr hv]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hue1, hu2]

private lemma spUCited_mulVec_mem_of_smul_eq {h : UnitaryFieldData p f K} {g : ↥(hypSU h r ε)}
    {i : ℕ} (hg : g • hypFlag h r ε i = hypFlag h r ε i) {v : HypIndex r ε → K}
    (hv : v ∈ hypFlag h r ε i) : spUCitedMat g *ᵥ v ∈ hypFlag h r ε i := by
  have hmem : spUCitedMat g *ᵥ v ∈ g • hypFlag h r ε i := by
    change spUCitedMat g *ᵥ v ∈ (hypFlag h r ε i).map (Matrix.mulVecLin (spUCitedMat g))
    exact Submodule.mem_map.mpr ⟨v, hv, by rw [Matrix.mulVecLin_apply]⟩
  rwa [hg] at hmem

theorem uCited_mem_inf_normalizer_iff (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1)
    (x : ↥(hypSU h r ε)) :
    x ∈ hypUnitriangular h r ε ⊓
        Subgroup.normalizer (uCitedRoot h r ε
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) : Set ↥(hypSU h r ε)) ↔
      x ∈ hypUnitriangular h r ε ∧
        ((x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
            (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) =
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) := by
  constructor
  · rintro ⟨hxu, hxn⟩
    refine ⟨hxu, ?_⟩
    obtain ⟨c, _hc0, hc⟩ :=
      (uCited_mem_normalizer_root_iff h (⟨1, by omega⟩ : Fin r) x).mp hxn
    obtain ⟨c', hc'⟩ := uCited_unipotent_apply_one h hr hε hxu
    have hcoef := congrFun (hc.symm.trans hc') (Sum.inl (⟨1, by omega⟩ : Fin r))
    have hc1 : c = 1 := by simpa using hcoef
    rw [hc1, one_smul] at hc
    exact hc
  · rintro ⟨hxu, hxe⟩
    refine ⟨hxu, ?_⟩
    change x ∈ Subgroup.normalizer
      (uCitedRoot h r ε (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) :
        Set ↥(hypSU h r ε))
    rw [uCited_mem_normalizer_root_iff h (⟨1, by omega⟩ : Fin r) x]
    exact ⟨1, one_ne_zero, by simpa using hxe⟩

theorem uCited_conj_mem_inf_normalizer {f : ℕ} (h : UnitaryFieldData 2 f K) (hr : 2 ≤ r)
    (hε : ε ≤ 1) {g x : ↥(hypSU h r ε)} (hg : g ∈ uCitedPar h r ε)
    (hx : x ∈ hypUnitriangular h r ε ⊓
        Subgroup.normalizer (uCitedRoot h r ε
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) : Set ↥(hypSU h r ε))) :
    g * x * g⁻¹ ∈ hypUnitriangular h r ε ⊓
        Subgroup.normalizer (uCitedRoot h r ε
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) : Set ↥(hypSU h r ε)) := by
  obtain ⟨hxu, hxe2⟩ := (uCited_mem_inf_normalizer_iff h hr hε x).mp hx
  have hxP : x ∈ uCitedPar h r ε :=
    uCited_borel_le_par h (hypUnitriangular_le_hypBorel h hxu)
  have hginv : g⁻¹ ∈ uCitedPar h r ε := (uCitedPar h r ε).inv_mem hg
  have hyP : g * x * g⁻¹ ∈ uCitedPar h r ε :=
    (uCitedPar h r ε).mul_mem ((uCitedPar h r ε).mul_mem hg hxP) hginv
  have hfixx : ∀ v ∈ hypFlag h r ε 2, spUCitedMat x *ᵥ v = v :=
    spUCited_unipotent_fixes_two h hr hε hxu hxe2
  have hyfix2 : ∀ v ∈ hypFlag h r ε 2, spUCitedMat (g * x * g⁻¹) *ᵥ v = v := by
    intro v hv
    have hw : spUCitedMat g⁻¹ *ᵥ v ∈ hypFlag h r ε 2 :=
      spUCited_mulVec_mem_of_smul_eq
        (mem_flagStabilizer.mp hginv 2 (Set.mem_Icc.mpr ⟨le_rfl, hr⟩)) hv
    have hxw : spUCitedMat x *ᵥ (spUCitedMat g⁻¹ *ᵥ v) = spUCitedMat g⁻¹ *ᵥ v := hfixx _ hw
    have hgg : spUCitedMat g *ᵥ (spUCitedMat g⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec]
      have h1 : spUCitedMat g * spUCitedMat g⁻¹ = 1 := by
        rw [spUCitedMat, spUCitedMat, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel,
          Units.val_one]
      rw [h1, Matrix.one_mulVec]
    calc spUCitedMat (g * x * g⁻¹) *ᵥ v
        = spUCitedMat g *ᵥ (spUCitedMat x *ᵥ (spUCitedMat g⁻¹ *ᵥ v)) := by
          rw [spUCitedMat, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
            Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = spUCitedMat g *ᵥ (spUCitedMat g⁻¹ *ᵥ v) := by rw [hxw]
      _ = v := hgg
  have hyinv_fix2 : ∀ v ∈ hypFlag h r ε 2, spUCitedMat ((g * x * g⁻¹)⁻¹) *ᵥ v = v := by
    intro v hv
    have h1 : spUCitedMat ((g * x * g⁻¹)⁻¹) *ᵥ (spUCitedMat (g * x * g⁻¹) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec]
      have h2 : spUCitedMat ((g * x * g⁻¹)⁻¹) * spUCitedMat (g * x * g⁻¹) = 1 := by
        rw [spUCitedMat, spUCitedMat, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel,
          Units.val_one]
      rw [h2, Matrix.one_mulVec]
    rwa [hyfix2 v hv] at h1
  have hyB : g * x * g⁻¹ ∈ hypBorel h r ε := by
    rw [mem_hypBorel]
    intro i hi1 hir
    rcases eq_or_lt_of_le hi1 with rfl | hi2
    · have hF1 : hypFlag h r ε 1 ≤ hypFlag h r ε 2 := by
        rw [hypFlag_eq_posFlag h hε (by omega : 1 ≤ 2 * r + ε),
          hypFlag_eq_posFlag h hε (by omega : 2 ≤ 2 * r + ε)]
        exact posFlag_mono (by norm_num)
      rw [Subgroup.smul_def]
      apply smul_eq_of_mulVec_mem
      · intro v hv
        rw [hyfix2 v (hF1 hv)]
        exact hv
      · intro v hv
        change spUCitedMat ((g * x * g⁻¹)⁻¹) *ᵥ v ∈ hypFlag h r ε 1
        rw [hyinv_fix2 v (hF1 hv)]
        exact hv
    · exact mem_flagStabilizer.mp hyP i ⟨by omega, hir⟩
  obtain ⟨P, hP⟩ := (unitary_order_and_Sylow h (by omega : 1 ≤ r) hε).2.1
  have hU2 : IsPGroup 2 (hypUnitriangular h r ε) := hP ▸ P.isPGroup'
  have hyN : g * x * g⁻¹ ∈
      Subgroup.normalizer (hypUnitriangular h r ε : Set ↥(hypSU h r ε)) := by
    rw [normalizer_hypUnitriangular h (by omega : 1 ≤ r) hε]
    exact hyB
  have hyT : g * x * g⁻¹ ∈ Subgroup.normalizer (P : Set ↥(hypSU h r ε)) := by
    rwa [← hP] at hyN
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_dvd_pow hU2 ⟨x, hxu⟩
  have hk' : orderOf x ∣ 2 ^ k := by
    rwa [Subgroup.orderOf_mk] at hk
  have hy2 : IsPGroup 2 (Subgroup.zpowers (g * x * g⁻¹)) := by
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers]
    have hconj : orderOf (g * x * g⁻¹) = orderOf x :=
      (SemiconjBy.orderOf_eq g (show SemiconjBy g x (g * x * g⁻¹) from by
        rw [SemiconjBy]; group)).symm
    rw [hconj]
    exact hk'
  have hyU : g * x * g⁻¹ ∈ hypUnitriangular h r ε := by
    have hmem : g * x * g⁻¹ ∈ (P : Subgroup (hypSU h r ε)) :=
      spUCited_mem_sylow_of_mem_normalizer hyT hy2
    rwa [hP] at hmem
  have he2mem : (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) ∈
      hypFlag h r ε 2 := by
    rw [hypFlag_eq_posFlag h hε (by omega : 2 ≤ 2 * r + ε)]
    intro a ha
    by_cases hae : a = Sum.inl (⟨1, by omega⟩ : Fin r)
    · exfalso
      rw [hae] at ha
      simp only [fullPos_inl] at ha
      omega
    · simp [Pi.single_apply, hae]
  exact (uCited_mem_inf_normalizer_iff h hr hε (g * x * g⁻¹)).mpr ⟨hyU, hyfix2 _ he2mem⟩

theorem uCited_normal {f : ℕ} (h : UnitaryFieldData 2 f K) (hr : 2 ≤ r) (hε : ε ≤ 1) :
    ((hypUnitriangular h r ε ⊓
        Subgroup.normalizer (uCitedRoot h r ε
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) : Set ↥(hypSU h r ε))).subgroupOf
      (uCitedPar h r ε)).Normal := by
  have hQle : hypUnitriangular h r ε ⊓
      Subgroup.normalizer (uCitedRoot h r ε
        (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) : Set ↥(hypSU h r ε)) ≤
      uCitedPar h r ε :=
    inf_le_left.trans ((hypUnitriangular_le_hypBorel h).trans (uCited_borel_le_par h))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQle]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact uCited_conj_mem_inf_normalizer h hr hε hg hx
  · intro hx
    have hinv : g⁻¹ ∈ uCitedPar h r ε := (uCitedPar h r ε).inv_mem hg
    have hconj := uCited_conj_mem_inf_normalizer h hr hε hinv hx
    have hsimp : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
    rwa [hsimp] at hconj

end CFSG.LocalAnalysis.WeakClosure81

end
