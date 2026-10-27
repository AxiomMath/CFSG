module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOrthPairA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem s16k_natAct_one (Γ : Subgroup (GL ι K)) (a : Multiplicative (ι → K)) :
    natAct Γ 1 a = a := by
  simp [natAct]

theorem s16k_natAct_mul (Γ : Subgroup (GL ι K)) (x y : ↥Γ)
    (a : Multiplicative (ι → K)) : natAct Γ (x * y) a = natAct Γ x (natAct Γ y a) := by
  simp [natAct, Units.val_mul, Matrix.mulVec_mulVec]

theorem s16k_natAct_inv (Γ : Subgroup (GL ι K)) (x : ↥Γ) (a : Multiplicative (ι → K))
    (h : natAct Γ x a = a) : natAct Γ x⁻¹ a = a := by
  rw [← h, ← s16k_natAct_mul, inv_mul_cancel, s16k_natAct_one]
  exact h.symm

theorem s16k_natAct_eq (Γ : Subgroup (GL ι K)) (x : ↥Γ)
    (a : Multiplicative (ι → K)) :
    natAct Γ x a = Multiplicative.ofAdd (((x : GL ι K) : Matrix ι ι K) *ᵥ
      Multiplicative.toAdd a) := rfl

private theorem s16k_transv_comm [CharP K 2] {Q : (ι → K) → K} {M : Matrix ι ι K}
    (h : IsQuadWith Q M) {a b : ι → K} (hab : a ⬝ᵥ (M *ᵥ b) = 0) {s t : GL ι K}
    (hs : ∀ x, (s : Matrix ι ι K) *ᵥ x = transvFun M a x)
    (ht : ∀ x, (t : Matrix ι ι K) *ᵥ x = transvFun M b x) : s * t = t * s := by
  have hba : b ⬝ᵥ (M *ᵥ a) = 0 := (h.symm b a).trans hab
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  have := s16t3_transvFun_comm (M := M) hab hba x
  simpa only [Units.val_mul, ← mulVec_mulVec, hs, ht] using this

private theorem s16k_elliptic_pair [CharP K 2] {Q : (ι → K) → K} {M : Matrix ι ι K}
    (h : IsQuadWith Q M) {a b : ι → K} {s t : GL ι K}
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
  exact ⟨h4 ▸ pow_mem hc 2, orderOf_eq_prime hg3 hg1, hmap, hfix⟩

theorem s16k_pair_omega_two [CharP K 2] {Q : (ι → K) → K} {M : Matrix ι ι K}
    (h : IsQuadWith Q M) {a₁ a₁' a₂ a₂' x y : ι → K}
    (h1 : Q a₁ = 1) (h1' : Q a₁' = 1) (h11 : a₁ ⬝ᵥ (M *ᵥ a₁') = 1)
    (h2 : Q a₂ = 1) (h2' : Q a₂' = 1) (h22 : a₂ ⬝ᵥ (M *ᵥ a₂') = 1)
    (h12 : a₁ ⬝ᵥ (M *ᵥ a₂) = 0) (h12' : a₁ ⬝ᵥ (M *ᵥ a₂') = 0)
    (h1'2 : a₁' ⬝ᵥ (M *ᵥ a₂) = 0) (h1'2' : a₁' ⬝ᵥ (M *ᵥ a₂') = 0)
    (hx1 : x ⬝ᵥ (M *ᵥ a₁) = 0) (hx1' : x ⬝ᵥ (M *ᵥ a₁') = 0)
    (hx2 : x ⬝ᵥ (M *ᵥ a₂) = 0) (hx2' : x ⬝ᵥ (M *ᵥ a₂') = 0)
    (hy1 : y ⬝ᵥ (M *ᵥ a₁) = 0) (hy1' : y ⬝ᵥ (M *ᵥ a₁') = 0)
    (hy2 : y ⬝ᵥ (M *ᵥ a₂) = 0) (hy2' : y ⬝ᵥ (M *ᵥ a₂') = 0) :
    ∃ g₁ g₂ : ↥(CFSG.Open.StatedOmega Q), orderOf g₁ = 3 ∧ orderOf g₂ = 3 ∧
      g₁ * g₂ = g₂ * g₁ ∧ g₂ ∉ Subgroup.zpowers g₁ ∧
      natAct (CFSG.Open.StatedOmega Q) g₁ (Multiplicative.ofAdd x) = Multiplicative.ofAdd x ∧
      natAct (CFSG.Open.StatedOmega Q) g₂ (Multiplicative.ofAdd x) = Multiplicative.ofAdd x ∧
      natAct (CFSG.Open.StatedOmega Q) g₁ (Multiplicative.ofAdd y) = Multiplicative.ofAdd y ∧
      natAct (CFSG.Open.StatedOmega Q) g₂ (Multiplicative.ofAdd y) = Multiplicative.ofAdd y := by
  obtain ⟨s1, hs1, _⟩ := exists_transv h a₁
  obtain ⟨t1, ht1, _⟩ := exists_transv h a₁'
  obtain ⟨s2, hs2, _⟩ := exists_transv h a₂
  obtain ⟨t2, ht2, _⟩ := exists_transv h a₂'
  obtain ⟨hm1, ho1, hmap1, hfix1⟩ := s16k_elliptic_pair h hs1 ht1 h1 h1' h11
  obtain ⟨hm2, ho2, hmap2, hfix2⟩ := s16k_elliptic_pair h hs2 ht2 h2 h2' h22
  have h21 : a₂ ⬝ᵥ (M *ᵥ a₁) = 0 := (h.symm a₂ a₁).trans h12
  have h21' : a₂ ⬝ᵥ (M *ᵥ a₁') = 0 := (h.symm a₂ a₁').trans h1'2
  have hg1x : ((s1 * t1 : GL ι K) : Matrix ι ι K) *ᵥ x = x := hfix1 x hx1 hx1'
  have hg1y : ((s1 * t1 : GL ι K) : Matrix ι ι K) *ᵥ y = y := hfix1 y hy1 hy1'
  have hg2x : ((s2 * t2 : GL ι K) : Matrix ι ι K) *ᵥ x = x := hfix2 x hx2 hx2'
  have hg2y : ((s2 * t2 : GL ι K) : Matrix ι ι K) *ᵥ y = y := hfix2 y hy2 hy2'
  have hg1a : ((s1 * t1 : GL ι K) : Matrix ι ι K) *ᵥ a₂ = a₂ := hfix1 a₂ h21 h21'
  have hne : a₂' ≠ a₂ := by
    intro hEq
    rw [hEq, h.self] at h22
    exact zero_ne_one h22
  have hc12 : s1 * s2 = s2 * s1 := s16k_transv_comm h h12 hs1 hs2
  have hc12' : s1 * t2 = t2 * s1 := s16k_transv_comm h h12' hs1 ht2
  have hc1'2 : t1 * s2 = s2 * t1 := s16k_transv_comm h h1'2 ht1 hs2
  have hc1'2' : t1 * t2 = t2 * t1 := s16k_transv_comm h h1'2' ht1 ht2
  have hprod : s1 * t1 * (s2 * t2) = s2 * t2 * (s1 * t1) := by
    calc s1 * t1 * (s2 * t2) = s1 * (t1 * s2) * t2 := by group
      _ = s1 * (s2 * t1) * t2 := by rw [hc1'2]
      _ = (s1 * s2) * (t1 * t2) := by group
      _ = (s2 * s1) * (t2 * t1) := by rw [hc12, hc1'2']
      _ = s2 * (s1 * t2) * t1 := by group
      _ = s2 * (t2 * s1) * t1 := by rw [hc12']
      _ = s2 * t2 * (s1 * t1) := by group
  have hnat1x : natAct (CFSG.Open.StatedOmega Q) (⟨s1 * t1, hm1⟩ : ↥(CFSG.Open.StatedOmega Q))
      (Multiplicative.ofAdd x) = Multiplicative.ofAdd x := by
    rw [s16k_natAct_eq]
    exact congrArg Multiplicative.ofAdd hg1x
  have hnat1y : natAct (CFSG.Open.StatedOmega Q) (⟨s1 * t1, hm1⟩ : ↥(CFSG.Open.StatedOmega Q))
      (Multiplicative.ofAdd y) = Multiplicative.ofAdd y := by
    rw [s16k_natAct_eq]
    exact congrArg Multiplicative.ofAdd hg1y
  have hnat2x : natAct (CFSG.Open.StatedOmega Q) (⟨s2 * t2, hm2⟩ : ↥(CFSG.Open.StatedOmega Q))
      (Multiplicative.ofAdd x) = Multiplicative.ofAdd x := by
    rw [s16k_natAct_eq]
    exact congrArg Multiplicative.ofAdd hg2x
  have hnat2y : natAct (CFSG.Open.StatedOmega Q) (⟨s2 * t2, hm2⟩ : ↥(CFSG.Open.StatedOmega Q))
      (Multiplicative.ofAdd y) = Multiplicative.ofAdd y := by
    rw [s16k_natAct_eq]
    exact congrArg Multiplicative.ofAdd hg2y
  refine ⟨⟨s1 * t1, hm1⟩, ⟨s2 * t2, hm2⟩, ?_, ?_, ?_, ?_, hnat1x, hnat2x, hnat1y, hnat2y⟩
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

private theorem s16k_Q_add_smul {Q : (ι → K) → K} {M : Matrix ι ι K}
    (h : IsQuadWith Q M) {a w : ι → K} (hQw : Q w = 0) (haw : a ⬝ᵥ (M *ᵥ w) = 0) (μ : K) :
    Q (a + μ • w) = Q a := by
  rw [h.add, h.smul, hQw, Matrix.mulVec_smul, dotProduct_smul, haw, smul_eq_mul]
  ring

private theorem s16k_dot_add_smul_eq {M : Matrix ι ι K} {a b w : ι → K}
    (hww : w ⬝ᵥ (M *ᵥ w) = 0) (haw : a ⬝ᵥ (M *ᵥ w) = 0) (hwb : w ⬝ᵥ (M *ᵥ b) = 0)
    (μ μ' : K) : (a + μ • w) ⬝ᵥ (M *ᵥ (b + μ' • w)) = a ⬝ᵥ (M *ᵥ b) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, hww, haw, hwb]
  ring

private theorem s16k_v_add_smul [CharP K 2] {M : Matrix ι ι K} {a w v : ι → K}
    (hvw : v ⬝ᵥ (M *ᵥ w) ≠ 0) :
    v ⬝ᵥ (M *ᵥ (a + (v ⬝ᵥ (M *ᵥ a) / (v ⬝ᵥ (M *ᵥ w))) • w)) = 0 := by
  have hμ : (v ⬝ᵥ (M *ᵥ a) / (v ⬝ᵥ (M *ᵥ w))) * (v ⬝ᵥ (M *ᵥ w)) = v ⬝ᵥ (M *ᵥ a) :=
    div_mul_cancel₀ _ hvw
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  linear_combination (v ⬝ᵥ (M *ᵥ a)) * two_eq_zero_K (K := K) + hμ

private theorem s16k_dot_add_smul_left {M : Matrix ι ι K} {u a w : ι → K}
    (hua : u ⬝ᵥ (M *ᵥ a) = 0) (huw : u ⬝ᵥ (M *ᵥ w) = 0) (μ : K) :
    u ⬝ᵥ (M *ᵥ (a + μ • w)) = 0 := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
    smul_eq_mul, hua, huw, mul_zero, add_zero]

theorem s16k_pairs_of_singular_two [CharP K 2] {Q : (ι → K) → K} {M : Matrix ι ι K}
    (h : IsQuadWith Q M) {a₁ a₁' a₂ a₂' w v u : ι → K}
    (h1 : Q a₁ = 1) (h1' : Q a₁' = 1) (h11 : a₁ ⬝ᵥ (M *ᵥ a₁') = 1)
    (h2 : Q a₂ = 1) (h2' : Q a₂' = 1) (h22 : a₂ ⬝ᵥ (M *ᵥ a₂') = 1)
    (h12 : a₁ ⬝ᵥ (M *ᵥ a₂) = 0) (h12' : a₁ ⬝ᵥ (M *ᵥ a₂') = 0)
    (h1'2 : a₁' ⬝ᵥ (M *ᵥ a₂) = 0) (h1'2' : a₁' ⬝ᵥ (M *ᵥ a₂') = 0)
    (hwQ : Q w = 0) (hw1 : w ⬝ᵥ (M *ᵥ a₁) = 0) (hw1' : w ⬝ᵥ (M *ᵥ a₁') = 0)
    (hw2 : w ⬝ᵥ (M *ᵥ a₂) = 0) (hw2' : w ⬝ᵥ (M *ᵥ a₂') = 0)
    (hvw : v ⬝ᵥ (M *ᵥ w) ≠ 0)
    (hu1 : u ⬝ᵥ (M *ᵥ a₁) = 0) (hu1' : u ⬝ᵥ (M *ᵥ a₁') = 0)
    (hu2 : u ⬝ᵥ (M *ᵥ a₂) = 0) (hu2' : u ⬝ᵥ (M *ᵥ a₂') = 0)
    (huw : u ⬝ᵥ (M *ᵥ w) = 0) :
    ∃ b₁ b₁' b₂ b₂' : ι → K,
      Q b₁ = 1 ∧ Q b₁' = 1 ∧ b₁ ⬝ᵥ (M *ᵥ b₁') = 1 ∧
      Q b₂ = 1 ∧ Q b₂' = 1 ∧ b₂ ⬝ᵥ (M *ᵥ b₂') = 1 ∧
      b₁ ⬝ᵥ (M *ᵥ b₂) = 0 ∧ b₁ ⬝ᵥ (M *ᵥ b₂') = 0 ∧
      b₁' ⬝ᵥ (M *ᵥ b₂) = 0 ∧ b₁' ⬝ᵥ (M *ᵥ b₂') = 0 ∧
      v ⬝ᵥ (M *ᵥ b₁) = 0 ∧ v ⬝ᵥ (M *ᵥ b₁') = 0 ∧ v ⬝ᵥ (M *ᵥ b₂) = 0 ∧ v ⬝ᵥ (M *ᵥ b₂') = 0 ∧
      u ⬝ᵥ (M *ᵥ b₁) = 0 ∧ u ⬝ᵥ (M *ᵥ b₁') = 0 ∧ u ⬝ᵥ (M *ᵥ b₂) = 0 ∧ u ⬝ᵥ (M *ᵥ b₂') = 0 := by
  have hww : w ⬝ᵥ (M *ᵥ w) = 0 := h.self w
  have hw1'' : a₁ ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₁ w).trans hw1
  have hw1''' : a₁' ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₁' w).trans hw1'
  have hw2'' : a₂ ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₂ w).trans hw2
  have hw2''' : a₂' ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₂' w).trans hw2'
  refine ⟨a₁ + (v ⬝ᵥ (M *ᵥ a₁) / (v ⬝ᵥ (M *ᵥ w))) • w,
    a₁' + (v ⬝ᵥ (M *ᵥ a₁') / (v ⬝ᵥ (M *ᵥ w))) • w,
    a₂ + (v ⬝ᵥ (M *ᵥ a₂) / (v ⬝ᵥ (M *ᵥ w))) • w,
    a₂' + (v ⬝ᵥ (M *ᵥ a₂') / (v ⬝ᵥ (M *ᵥ w))) • w,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s16k_Q_add_smul h hwQ hw1'', h1]
  · rw [s16k_Q_add_smul h hwQ hw1''', h1']
  · rw [s16k_dot_add_smul_eq hww hw1'' hw1', h11]
  · rw [s16k_Q_add_smul h hwQ hw2'', h2]
  · rw [s16k_Q_add_smul h hwQ hw2''', h2']
  · rw [s16k_dot_add_smul_eq hww hw2'' hw2', h22]
  · rw [s16k_dot_add_smul_eq hww hw1'' hw2, h12]
  · rw [s16k_dot_add_smul_eq hww hw1'' hw2', h12']
  · rw [s16k_dot_add_smul_eq hww hw1''' hw2, h1'2]
  · rw [s16k_dot_add_smul_eq hww hw1''' hw2', h1'2']
  · exact s16k_v_add_smul hvw
  · exact s16k_v_add_smul hvw
  · exact s16k_v_add_smul hvw
  · exact s16k_v_add_smul hvw
  · exact s16k_dot_add_smul_left hu1 huw _
  · exact s16k_dot_add_smul_left hu1' huw _
  · exact s16k_dot_add_smul_left hu2 huw _
  · exact s16k_dot_add_smul_left hu2' huw _

theorem s16k_pair_omega_two_subgroup [CharP K 2] [Finite K] {Q : (ι → K) → K}
    {M : Matrix ι ι K} (h : IsQuadWith Q M) {a₁ a₁' a₂ a₂' x y : ι → K}
    (hstruct : Q a₁ = 1 ∧ Q a₁' = 1 ∧ a₁ ⬝ᵥ (M *ᵥ a₁') = 1 ∧ Q a₂ = 1 ∧ Q a₂' = 1 ∧
      a₂ ⬝ᵥ (M *ᵥ a₂') = 1 ∧ a₁ ⬝ᵥ (M *ᵥ a₂) = 0 ∧ a₁ ⬝ᵥ (M *ᵥ a₂') = 0 ∧
      a₁' ⬝ᵥ (M *ᵥ a₂) = 0 ∧ a₁' ⬝ᵥ (M *ᵥ a₂') = 0)
    (hx : x ⬝ᵥ (M *ᵥ a₁) = 0 ∧ x ⬝ᵥ (M *ᵥ a₁') = 0 ∧ x ⬝ᵥ (M *ᵥ a₂) = 0 ∧
      x ⬝ᵥ (M *ᵥ a₂') = 0)
    (hy : y ⬝ᵥ (M *ᵥ a₁) = 0 ∧ y ⬝ᵥ (M *ᵥ a₁') = 0 ∧ y ⬝ᵥ (M *ᵥ a₂) = 0 ∧
      y ⬝ᵥ (M *ᵥ a₂') = 0) :
    ∃ B : Subgroup ↥(CFSG.Open.StatedOmega Q), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
      natAct (CFSG.Open.StatedOmega Q) g (Multiplicative.ofAdd x) = Multiplicative.ofAdd x ∧
      natAct (CFSG.Open.StatedOmega Q) g (Multiplicative.ofAdd y) = Multiplicative.ofAdd y := by
  obtain ⟨h1, h1', h11, h2, h2', h22, h12, h12', h1'2, h1'2'⟩ := hstruct
  obtain ⟨hx1, hx1', hx2, hx2'⟩ := hx
  obtain ⟨hy1, hy1', hy2, hy2'⟩ := hy
  obtain ⟨g₁, g₂, hg13, hg23, hgc, hgn, hg1x, hg2x, hg1y, hg2y⟩ :=
    s16k_pair_omega_two h h1 h1' h11 h2 h2' h22 h12 h12' h1'2 h1'2' hx1 hx1' hx2 hx2'
      hy1 hy1' hy2 hy2'
  haveI : Finite ↥(CFSG.Open.StatedOmega Q) := by infer_instance
  let B : Subgroup ↥(CFSG.Open.StatedOmega Q) := Subgroup.closure ({g₁, g₂} : Set _)
  have hpg := s16c13bcA_pair_group Nat.prime_three hg13 hg23 hgc hgn
  refine ⟨B, hpg.1, hpg.2, ?_⟩
  let Hfix : Subgroup ↥(CFSG.Open.StatedOmega Q) :=
    { carrier := {z | natAct (CFSG.Open.StatedOmega Q) z (Multiplicative.ofAdd x) =
          Multiplicative.ofAdd x ∧
        natAct (CFSG.Open.StatedOmega Q) z (Multiplicative.ofAdd y) =
          Multiplicative.ofAdd y}
      one_mem' := ⟨s16k_natAct_one _ _, s16k_natAct_one _ _⟩
      mul_mem' := fun ha hb =>
        ⟨by rw [s16k_natAct_mul, hb.1, ha.1], by rw [s16k_natAct_mul, hb.2, ha.2]⟩
      inv_mem' := fun ha => ⟨s16k_natAct_inv _ _ _ ha.1, s16k_natAct_inv _ _ _ ha.2⟩ }
  have hle : B ≤ Hfix := by
    change Subgroup.closure ({g₁, g₂} : Set ↥(CFSG.Open.StatedOmega Q)) ≤ Hfix
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact ⟨hg1x, hg1y⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hg2x, hg2y⟩
  intro z hz
  exact hle hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
