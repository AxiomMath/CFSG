module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

private theorem s16c13bcA_transvFun_comm {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M)
    {a b : ι → K} (hab : a ⬝ᵥ (M *ᵥ b) = 0) (x : ι → K) :
    transvFun M a (transvFun M b x) = transvFun M b (transvFun M a x) := by
  have hba : b ⬝ᵥ (M *ᵥ a) = 0 := (h.symm b a).trans hab
  have e1 : transvFun M a (transvFun M b x) =
      x + (x ⬝ᵥ (M *ᵥ a)) • a + (x ⬝ᵥ (M *ᵥ b)) • b := by
    conv_lhs => rw [transvFun]
    rw [transvFun_dot M b x a, hba]
    simp only [transvFun, mul_zero, add_zero, smul_add]
    abel
  have e2 : transvFun M b (transvFun M a x) =
      x + (x ⬝ᵥ (M *ᵥ a)) • a + (x ⬝ᵥ (M *ᵥ b)) • b := by
    conv_lhs => rw [transvFun]
    rw [transvFun_dot M a x b, hab]
    simp only [transvFun, mul_zero, add_zero, smul_add]
  rw [e1, e2]

private theorem s16c13bcA_transv_comm {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M)
    {a b : ι → K} (hab : a ⬝ᵥ (M *ᵥ b) = 0) {s t : GL ι K}
    (hs : ∀ x, (s : Matrix ι ι K) *ᵥ x = transvFun M a x)
    (ht : ∀ x, (t : Matrix ι ι K) *ᵥ x = transvFun M b x) : s * t = t * s := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  have := s16c13bcA_transvFun_comm h hab x
  simpa only [Units.val_mul, ← mulVec_mulVec, hs, ht] using this

private theorem s16c13bcA_elliptic_pair {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M)
    {a b : ι → K} {s t : GL ι K}
    (hs : ∀ x, (s : Matrix ι ι K) *ᵥ x = transvFun M a x)
    (ht : ∀ x, (t : Matrix ι ι K) *ᵥ x = transvFun M b x)
    (ha : Q a = 1) (hb : Q b = 1) (hab : a ⬝ᵥ (M *ᵥ b) = 1) :
    s * t ∈ CFSG.Open.StatedOmega Q ∧ orderOf (s * t) = 3 ∧
      (((s * t : GL ι K) : Matrix ι ι K) *ᵥ a = b) ∧
      (∀ w, w ⬝ᵥ (M *ᵥ a) = 0 → w ⬝ᵥ (M *ᵥ b) = 0 →
        (((s * t : GL ι K) : Matrix ι ι K) *ᵥ w = w)) := by
  have hba : b ⬝ᵥ (M *ᵥ a) = 1 := (h.symm b a).trans hab
  have hss : s * s = 1 := by
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [Units.val_mul, Units.val_one, ← mulVec_mulVec, hs, hs, transvFun_transvFun h,
      one_mulVec]
  have htt : t * t = 1 := by
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [Units.val_mul, Units.val_one, ← mulVec_mulVec, ht, ht, transvFun_transvFun h,
      one_mulVec]
  have hbraid : s * t * s = t * s * t := Units.ext (Matrix.ext_iff_mulVec.mpr fun x => by
    simp only [Units.val_mul, ← mulVec_mulVec, hs, ht]
    exact transvFun_braid h hab x)
  have hg3 : (s * t) ^ 3 = 1 := by
    calc (s * t) ^ 3 = (s * t * s) * (t * s * t) := by simp [pow_succ, mul_assoc]
      _ = (s * t * s) * (s * t * s) := by rw [hbraid]
      _ = s * t * (s * s) * t * s := by group
      _ = 1 := by rw [hss, mul_one, mul_assoc s t t, htt, mul_one, hss]
  have hmap : ((s * t : GL ι K) : Matrix ι ι K) *ᵥ a = b := by
    rw [Units.val_mul, ← mulVec_mulVec, ht, hs]
    have h1 : transvFun M b a = a + b := by
      rw [transvFun, hab, one_smul, add_comm]
    have h2 : (a + b) ⬝ᵥ (M *ᵥ a) = 1 := by
      rw [add_dotProduct, h.self a, hba, zero_add]
    have h3 : a + a = 0 := by
      have htwo : (2 : K) • a = 0 := by rw [two_eq_zero_K, zero_smul]
      rwa [two_smul] at htwo
    rw [h1, transvFun, h2, one_smul]
    rw [add_assoc, add_comm b a, ← add_assoc, h3, zero_add]
  have hane : a ≠ b := by
    intro hEq
    rw [hEq, h.self] at hab
    exact zero_ne_one hab
  have hg1 : s * t ≠ 1 := by
    intro h1
    have h2 : ((s * t : GL ι K) : Matrix ι ι K) *ᵥ a = a := by rw [h1]; simp
    rw [hmap] at h2
    exact hane h2.symm
  have hfix : ∀ w, w ⬝ᵥ (M *ᵥ a) = 0 → w ⬝ᵥ (M *ᵥ b) = 0 →
      (((s * t : GL ι K) : Matrix ι ι K) *ᵥ w = w) := by
    intro w hwa hwb
    rw [Units.val_mul, ← mulVec_mulVec, ht, hs]
    have h1 : transvFun M b w = w := by simp [transvFun, hwb]
    have h2 : transvFun M a w = w := by simp [transvFun, hwa]
    rw [h1, h2]
  have hsI : s ∈ Subgroup.closure {A : GL ι K |
      ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    Subgroup.subset_closure fun x => by rw [hs]; exact Q_transvFun h ha x
  have htI : t ∈ Subgroup.closure {A : GL ι K |
      ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    Subgroup.subset_closure fun x => by rw [ht]; exact Q_transvFun h hb x
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hc : (s * t) ^ 2 ∈ CFSG.Open.StatedOmega Q := by
    have hcomm := Subgroup.commutator_mem_commutator hsI htI
    rw [commutatorElement_def, hs1, ht1] at hcomm
    rw [pow_two]
    unfold CFSG.Open.StatedOmega
    simpa [mul_assoc] using hcomm
  have h4 : s * t = ((s * t) ^ 2) ^ 2 := by
    rw [← pow_mul]; simp [pow_succ, hg3]
  have hmem : s * t ∈ CFSG.Open.StatedOmega Q := by
    rw [h4]; exact pow_mem hc 2
  exact ⟨hmem, orderOf_eq_prime hg3 hg1, hmap, hfix⟩

theorem s16c13bcA_pair_omega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
    {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M) {a₁ a₁' a₂ a₂' v : ι → K}
    (h1 : Q a₁ = 1) (h1' : Q a₁' = 1) (h11 : a₁ ⬝ᵥ (M *ᵥ a₁') = 1)
    (h2 : Q a₂ = 1) (h2' : Q a₂' = 1) (h22 : a₂ ⬝ᵥ (M *ᵥ a₂') = 1)
    (h12 : a₁ ⬝ᵥ (M *ᵥ a₂) = 0) (h12' : a₁ ⬝ᵥ (M *ᵥ a₂') = 0)
    (h1'2 : a₁' ⬝ᵥ (M *ᵥ a₂) = 0) (h1'2' : a₁' ⬝ᵥ (M *ᵥ a₂') = 0)
    (hv1 : v ⬝ᵥ (M *ᵥ a₁) = 0) (hv1' : v ⬝ᵥ (M *ᵥ a₁') = 0)
    (hv2 : v ⬝ᵥ (M *ᵥ a₂) = 0) (hv2' : v ⬝ᵥ (M *ᵥ a₂') = 0) :
    ∃ g₁ g₂ : ↥(CFSG.Open.StatedOmega Q), orderOf g₁ = 3 ∧ orderOf g₂ = 3 ∧ g₁ * g₂ = g₂ * g₁ ∧
      g₂ ∉ Subgroup.zpowers g₁ ∧ g₁ • v = v ∧ g₂ • v = v := by
  obtain ⟨s1, hs1, _⟩ := exists_transv h a₁
  obtain ⟨t1, ht1, _⟩ := exists_transv h a₁'
  obtain ⟨s2, hs2, _⟩ := exists_transv h a₂
  obtain ⟨t2, ht2, _⟩ := exists_transv h a₂'
  obtain ⟨hm1, ho1, _, hfix1⟩ := s16c13bcA_elliptic_pair h hs1 ht1 h1 h1' h11
  obtain ⟨hm2, ho2, hmap2, hfix2⟩ := s16c13bcA_elliptic_pair h hs2 ht2 h2 h2' h22
  have h21 : a₂ ⬝ᵥ (M *ᵥ a₁) = 0 := (h.symm a₂ a₁).trans h12
  have h21' : a₂ ⬝ᵥ (M *ᵥ a₁') = 0 := (h.symm a₂ a₁').trans h1'2
  have hg1v : ((s1 * t1 : GL ι K) : Matrix ι ι K) *ᵥ v = v := hfix1 v hv1 hv1'
  have hg2v : ((s2 * t2 : GL ι K) : Matrix ι ι K) *ᵥ v = v := hfix2 v hv2 hv2'
  have hg1a : ((s1 * t1 : GL ι K) : Matrix ι ι K) *ᵥ a₂ = a₂ := hfix1 a₂ h21 h21'
  have hne : a₂' ≠ a₂ := by
    intro hEq
    rw [hEq, h.self] at h22
    exact zero_ne_one h22
  have hc12 : s1 * s2 = s2 * s1 := s16c13bcA_transv_comm h h12 hs1 hs2
  have hc12' : s1 * t2 = t2 * s1 := s16c13bcA_transv_comm h h12' hs1 ht2
  have hc1'2 : t1 * s2 = s2 * t1 := s16c13bcA_transv_comm h h1'2 ht1 hs2
  have hc1'2' : t1 * t2 = t2 * t1 := s16c13bcA_transv_comm h h1'2' ht1 ht2
  have hprod : s1 * t1 * (s2 * t2) = s2 * t2 * (s1 * t1) := by
    calc s1 * t1 * (s2 * t2) = s1 * (t1 * s2) * t2 := by group
      _ = s1 * (s2 * t1) * t2 := by rw [hc1'2]
      _ = (s1 * s2) * (t1 * t2) := by group
      _ = (s2 * s1) * (t2 * t1) := by rw [hc12, hc1'2']
      _ = s2 * (s1 * t2) * t1 := by group
      _ = s2 * (t2 * s1) * t1 := by rw [hc12']
      _ = s2 * t2 * (s1 * t1) := by group
  refine ⟨⟨s1 * t1, hm1⟩, ⟨s2 * t2, hm2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact ho1
  · rw [Subgroup.orderOf_mk]; exact ho2
  · exact Subtype.ext hprod
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : ((s1 * t1 : GL ι K) ^ k) = (s2 * t2 : GL ι K) := by
      simpa using congrArg (Subtype.val) hk
    have hstab : (s1 * t1 : GL ι K) ∈ MulAction.stabilizer (GL ι K) a₂ := by
      rw [MulAction.mem_stabilizer_iff]
      simpa only [Units.smul_def, Matrix.smul_eq_mulVec] using hg1a
    have hpowGL : ((s1 * t1 : GL ι K) ^ k) ∈
        MulAction.stabilizer (GL ι K) a₂ := Subgroup.zpow_mem _ hstab k
    have hpow : ((s1 * t1 : GL ι K) ^ k) • a₂ = a₂ := by
      simpa only [MulAction.mem_stabilizer_iff] using hpowGL
    have h2map : (s2 * t2 : GL ι K) • a₂ = a₂' := by
      simpa only [Units.smul_def, Matrix.smul_eq_mulVec] using hmap2
    have hcontra : a₂' = a₂ := by
      calc a₂' = (s2 * t2 : GL ι K) • a₂ := h2map.symm
        _ = ((s1 * t1 : GL ι K) ^ k) • a₂ := by rw [← hk']
        _ = a₂ := hpow
    exact hne hcontra
  · simpa only [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec] using hg1v
  · simpa only [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec] using hg2v

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
