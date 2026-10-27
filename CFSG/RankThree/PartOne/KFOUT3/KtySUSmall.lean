module

public import CFSG.RankThree.PartOne.KFOUT3.KtySUCls
public import CFSG.RankThree.PartOne.KFOUT3.KtySUQuot
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix

section Small

variable {K : Type} [Field K] {n : ℕ} [NeZero n]

@[expose] def centB (n : ℕ) [NeZero n] (b : Kˣ) : Subgroup (GL (Fin n) K) :=
  Subgroup.centralizer ({diagU (dvecN n 1 b)} : Set (GL (Fin n) K))

theorem mem_centB {b : Kˣ} {x : GL (Fin n) K} :
    x ∈ centB n b ↔ x * diagU (dvecN n 1 b) = diagU (dvecN n 1 b) * x := by
  unfold centB
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h _ (Set.mem_singleton _)).symm
  · intro h w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact h.symm

theorem centB_vanish_row {b : Kˣ} (hb1 : b ≠ 1) (hb2 : b⁻¹ ≠ b) {k : ℕ} {e : Fin k → Fin n}
    (hrange : ∀ j, j ∈ Set.range e ↔ gq (d8Cls n j) = 0) {m : GL (Fin n) K}
    (hm : m ∈ centB n b) (a : Fin k) (j : Fin n) (hj : j ∉ Set.range e) :
    ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (e a) j = 0 := by
  apply vanish_1b hb1 hb2 (comm_matrix (mem_centB.mp hm))
  have h1 : gq (d8Cls n (e a)) = 0 := (hrange _).mp ⟨a, rfl⟩
  have h2 : gq (d8Cls n j) ≠ 0 := fun h => hj ((hrange j).mpr h)
  rw [h1]; exact Ne.symm h2

theorem centB_vanish_col {b : Kˣ} (hb1 : b ≠ 1) (hb2 : b⁻¹ ≠ b) {k : ℕ} {e : Fin k → Fin n}
    (hrange : ∀ j, j ∈ Set.range e ↔ gq (d8Cls n j) = 0) {m : GL (Fin n) K}
    (hm : m ∈ centB n b) (a : Fin k) (l : Fin n) (hl : l ∉ Set.range e) :
    ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) l (e a) = 0 := by
  apply vanish_1b hb1 hb2 (comm_matrix (mem_centB.mp hm))
  have h1 : gq (d8Cls n (e a)) = 0 := (hrange _).mp ⟨a, rfl⟩
  have h2 : gq (d8Cls n l) ≠ 0 := fun h => hl ((hrange l).mpr h)
  rw [h1]; exact h2

theorem centB_vanish_one (hc : D8Comb n) {b : Kˣ} (hb1 : b ≠ 1) (hb2 : b⁻¹ ≠ b) {m : GL (Fin n) K}
    (hm : m ∈ centB n b) (j : Fin n) (hj : j ∉ Set.range (fun _ : Fin 1 => (1 : Fin n))) :
    ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) 1 j = 0 := by
  apply vanish_1b hb1 hb2 (comm_matrix (mem_centB.mp hm))
  rw [gq_cls_one hc]
  intro h
  exact hj ⟨0, ((gq_cls_eq_one_iff hc).mp h.symm).symm⟩

omit [NeZero n] in
theorem gram_block (σ : K ≃+* K) {k : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (hrev : ∀ a, e (Fin.rev a) = Fin.rev (e a)) {m : Matrix (Fin n) (Fin n) K}
    (hcol : ∀ a l, l ∉ Set.range e → m l (e a) = 0)
    (hgram : conjTr σ m * antidiag n * m = antidiag n) :
    conjTr σ (m.submatrix e e) * antidiag k * m.submatrix e e = antidiag k := by
  ext a b
  rw [gram_apply]
  have h1 := congrFun (congrFun hgram (e a)) (e b)
  rw [gram_apply] at h1
  have h2 : ∑ l : Fin n, σ (m l (e a)) * m (Fin.rev l) (e b) =
      ∑ c : Fin k, σ (m (e c) (e a)) * m (Fin.rev (e c)) (e b) := by
    rw [← Finset.sum_image (s := Finset.univ) (g := e)
      (f := fun l => σ (m l (e a)) * m (Fin.rev l) (e b)) (fun x _ y _ h => he h)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    rw [hcol a l (fun ⟨c, hc⟩ => hl (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩)), map_zero,
      zero_mul]
  rw [h2] at h1
  simp only [Matrix.submatrix_apply, hrev]
  rw [h1]
  simp only [antidiag, Matrix.of_apply]
  have : e b = Fin.rev (e a) ↔ b = Fin.rev a := by rw [← hrev, he.eq_iff]
  simp only [this]

theorem small_rr (hc : D8Comb n) (σ : K ≃+* K) {b : Kˣ} (hb1 : b ≠ 1) (hb2 : b⁻¹ ≠ b)
    {M : Matrix (Fin n) (Fin n) K}
    (hcomm : M * Matrix.diagonal (fun i => (dvecN n 1 b i : K)) =
      Matrix.diagonal (fun i => (dvecN n 1 b i : K)) * M)
    (hgram : conjTr σ M * antidiag n * M = antidiag n) (h11 : M 1 1 = 1) :
    M (Fin.rev 1) (Fin.rev 1) = 1 := by
  have h1 := congrFun (congrFun hgram 1) (Fin.rev 1)
  rw [gram_apply, Finset.sum_eq_single (1 : Fin n)] at h1
  · simp only [antidiag, Matrix.of_apply] at h1
    rw [h11, map_one, one_mul] at h1
    simpa using h1
  · intro l _ hl
    have : M l 1 = 0 := by
      apply vanish_1b hb1 hb2 hcomm
      rw [gq_cls_one hc]
      intro h
      exact hl ((gq_cls_eq_one_iff hc).mp h)
    rw [this, map_zero, zero_mul]
  · simp

theorem small_one (hc : D8Comb n) {b : Kˣ} (hb1 : b ≠ 1) (hb2 : b⁻¹ ≠ b) {k : ℕ}
    {e : Fin k → Fin n} (he : Function.Injective e)
    (hrange : ∀ j, j ∈ Set.range e ↔ gq (d8Cls n j) = 0) {M : Matrix (Fin n) (Fin n) K}
    (hcomm : M * Matrix.diagonal (fun i => (dvecN n 1 b i : K)) =
      Matrix.diagonal (fun i => (dvecN n 1 b i : K)) * M)
    (hX : ∀ a b' : Fin k, M (e a) (e b') = (1 : Matrix (Fin k) (Fin k) K) a b')
    (h11 : M 1 1 = 1) (hrr : M (Fin.rev 1) (Fin.rev 1) = 1) : M = 1 := by
  have hkinds : ∀ i : Fin n, i ∈ Set.range e ∨ i = 1 ∨ i = Fin.rev 1 := by
    intro i
    by_cases hi : gq (d8Cls n i) = 0
    · exact Or.inl ((hrange i).mpr hi)
    · right
      have : gq (d8Cls n i) = 1 ∨ gq (d8Cls n i) = 2 := by
        generalize d8Cls n i = c at hi
        fin_cases c <;> simp_all [gq]
      rcases this with h | h
      · exact Or.inl ((gq_cls_eq_one_iff hc).mp h)
      · exact Or.inr ((gq_cls_eq_two_iff hc).mp h)
  have off : ∀ i j : Fin n, gq (d8Cls n i) ≠ gq (d8Cls n j) →
      M i j = (1 : Matrix (Fin n) (Fin n) K) i j := fun i j h => by
    rw [vanish_1b hb1 hb2 hcomm h, Matrix.one_apply_ne (fun e => h (by rw [e]))]
  have ga : ∀ a, gq (d8Cls n (e a)) = 0 := fun a => (hrange _).mp ⟨a, rfl⟩
  have g1 := gq_cls_one hc
  have g2 := gq_cls_rev_one hc
  ext i j
  rcases hkinds i with ⟨a, rfl⟩ | rfl | rfl <;> rcases hkinds j with ⟨b', rfl⟩ | rfl | rfl
  · rw [hX a b']
    simp [Matrix.one_apply, he.eq_iff]
  · exact off _ _ (by rw [ga, g1]; omega)
  · exact off _ _ (by rw [ga, g2]; omega)
  · exact off _ _ (by rw [ga, g1]; omega)
  · simpa using h11
  · exact off _ _ (by rw [g1, g2]; omega)
  · exact off _ _ (by rw [ga, g2]; omega)
  · exact off _ _ (by rw [g1, g2]; omega)
  · simpa using hrr

theorem small_su_aux (hc : D8Comb n) (σ : K ≃+* K) {b : Kˣ} (hb1 : b ≠ 1) (hb2 : b⁻¹ ≠ b)
    {k : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (hrev : ∀ a, e (Fin.rev a) = Fin.rev (e a))
    (hrange : ∀ j, j ∈ Set.range e ↔ gq (d8Cls n j) = 0)
    (hu : diagU (dvecN n 1 b) ∈ SU σ n) (T : Subgroup ↥(SU σ n)) (hT : Group.IsPerfect T)
    (hTc : ∀ τ ∈ T, (⟨diagU (dvecN n 1 b), hu⟩ : ↥(SU σ n)) * τ =
      τ * ⟨diagU (dvecN n 1 b), hu⟩) :
    Nat.card T ∣ Nat.card ↥(SU σ k) := by
  classical
  have hTC : ∀ τ : ↥T, ((τ : ↥(SU σ n)) : GL (Fin n) K) ∈ centB n b := by
    intro τ
    apply mem_centB.mpr
    have := congrArg (fun g : ↥(SU σ n) => (g : GL (Fin n) K)) (hTc τ τ.2)
    exact this.symm
  let ιT : ↥T →* ↥(centB n b) :=
    ((SU σ n).subtype.comp T.subtype).codRestrict (centB n b) hTC
  let φ : ↥T →* GL (Fin k) K :=
    (blkHom e he (centB n b) (fun m hm a j hj => centB_vanish_row hb1 hb2 hrange hm a j hj)).comp ιT
  let ℓ₁ : ↥T →* GL (Fin 1) K :=
    (blkHom (fun _ : Fin 1 => (1 : Fin n)) (fun _ _ _ => Subsingleton.elim _ _) (centB n b)
      (fun m hm _ j hj => centB_vanish_one hc hb1 hb2 hm j hj)).comp ιT
  have hφval : ∀ τ : ↥T, ((φ τ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      (((τ : ↥(SU σ n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix e e := fun τ => rfl
  have hℓval : ∀ τ : ↥T, ((ℓ₁ τ : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) =
      (((τ : ↥(SU σ n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
        (fun _ : Fin 1 => (1 : Fin n)) (fun _ : Fin 1 => (1 : Fin n)) := fun τ => rfl
  have hTtop : Group.IsPerfect (⊤ : Subgroup ↥T) := Group.IsPerfect.top_iff.mpr hT
  have hdetφ : ∀ τ : ↥T, Matrix.GeneralLinearGroup.det (φ τ) = 1 := fun τ =>
    perfect_le_ker (Matrix.GeneralLinearGroup.det.comp φ) hTtop (Subgroup.mem_top τ)
  have hdetℓ : ∀ τ : ↥T, Matrix.GeneralLinearGroup.det (ℓ₁ τ) = 1 := fun τ =>
    perfect_le_ker (Matrix.GeneralLinearGroup.det.comp ℓ₁) hTtop (Subgroup.mem_top τ)
  have h11 : ∀ τ : ↥T, (((τ : ↥(SU σ n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) 1 1 = 1 := by
    intro τ
    have h1 := congrArg Units.val (hdetℓ τ)
    rw [Matrix.GeneralLinearGroup.val_det_apply, hℓval τ, Matrix.det_unique] at h1
    simpa using h1
  have hgramτ : ∀ τ : ↥T, conjTr σ (((τ : ↥(SU σ n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      antidiag n * (((τ : ↥(SU σ n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antidiag n :=
    fun τ => (mem_SU.mp τ.1.2).2
  have hcommτ : ∀ τ : ↥T, (((τ : ↥(SU σ n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      Matrix.diagonal (fun i => (dvecN n 1 b i : K)) = Matrix.diagonal (fun i => (dvecN n 1 b i : K)) *
      (((τ : ↥(SU σ n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun τ =>
    comm_matrix (mem_centB.mp (hTC τ))
  have hψmem : ∀ τ : ↥T, φ τ ∈ SU σ k := by
    intro τ
    refine mem_SU.mpr ⟨?_, ?_⟩
    · have := congrArg Units.val (hdetφ τ)
      rw [Matrix.GeneralLinearGroup.val_det_apply] at this
      simpa using this
    · rw [hφval τ]
      exact gram_block σ e he hrev (fun a l hl => centB_vanish_col hb1 hb2 hrange (hTC τ) a l hl)
        (hgramτ τ)
  let ψ : ↥T →* ↥(SU σ k) := φ.codRestrict (SU σ k) hψmem
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro τ hτ
    have hφ1 : φ τ = 1 := congrArg Subtype.val hτ
    have hX : ∀ a b' : Fin k, (((τ : ↥(SU σ n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (e a) (e b') = (1 : Matrix (Fin k) (Fin k) K) a b' := by
      intro a b'
      have := congrFun (congrFun (congrArg (fun g : GL (Fin k) K => (g : Matrix (Fin k) (Fin k) K))
        hφ1) a) b'
      rw [hφval τ] at this
      simpa using this
    have hMone := small_one hc hb1 hb2 he hrange (hcommτ τ) hX (h11 τ)
      (small_rr hc σ hb1 hb2 (hcommτ τ) (hgramτ τ) (h11 τ))
    have : ((τ : ↥(SU σ n)) : GL (Fin n) K) = 1 := Units.ext hMone
    exact Subtype.ext (Subtype.ext this)
  exact Subgroup.card_dvd_of_injective ψ hψinj

theorem eig_range_four : ∀ j : Fin 4,
    (∃ a : Fin 2, (![0, 3] : Fin 2 → Fin 4) a = j) ↔ gq (d8Cls 4 j) = 0 := by decide

theorem eig_range_five : ∀ j : Fin 5,
    (∃ a : Fin 3, (![0, 2, 4] : Fin 3 → Fin 5) a = j) ↔ gq (d8Cls 5 j) = 0 := by decide

theorem eig_inj_four : Function.Injective (![0, 3] : Fin 2 → Fin 4) := by decide

theorem eig_rev_four : ∀ a : Fin 2, (![0, 3] : Fin 2 → Fin 4) (Fin.rev a) =
    Fin.rev ((![0, 3] : Fin 2 → Fin 4) a) := by decide

theorem eig_inj_five : Function.Injective (![0, 2, 4] : Fin 3 → Fin 5) := by decide

theorem eig_rev_five : ∀ a : Fin 3, (![0, 2, 4] : Fin 3 → Fin 5) (Fin.rev a) =
    Fin.rev ((![0, 2, 4] : Fin 3 → Fin 5) a) := by decide

theorem small_su (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) {b : Kˣ} (hb1 : b ≠ 1)
    (hb2 : b⁻¹ ≠ b) (hu : diagU (dvecN n 1 b) ∈ SU σ n) (T : Subgroup ↥(SU σ n))
    (hT : Group.IsPerfect T)
    (hTc : ∀ τ ∈ T, (⟨diagU (dvecN n 1 b), hu⟩ : ↥(SU σ n)) * τ =
      τ * ⟨diagU (dvecN n 1 b), hu⟩) :
    Nat.card T ∣ Nat.card ↥(SU σ (n - 2)) := by
  rcases hn with rfl | rfl
  · exact small_su_aux hc σ hb1 hb2 (k := 2) ![0, 3] eig_inj_four eig_rev_four
      (fun j => by rw [Set.mem_range]; exact eig_range_four j) hu T hT hTc
  · exact small_su_aux hc σ hb1 hb2 (k := 3) ![0, 2, 4] eig_inj_five eig_rev_five
      (fun j => by rw [Set.mem_range]; exact eig_range_five j) hu T hT hTc

end Small

section Orders

open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem card_suAnti (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.card ↥(SU (unitaryInvolution K 2 f) k) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  rw [Nat.card_congr (equivStatedSU hK k).toEquiv]
  exact card_statedSU_eq (unitaryFieldData_two hK hf) hk

theorem card_suAnti_two (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    Nat.card ↥(SU (unitaryInvolution K 2 f) (4 - 2)) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have h := card_suAnti hK hf (k := 2) (by norm_num)
  have hq : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_two_pow)
  zify [hq]
  simpa using h

theorem card_suAnti_three (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    Nat.card ↥(SU (unitaryInvolution K 2 f) (5 - 2)) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
  have h := card_suAnti hK hf (k := 3) (by norm_num)
  have hq : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_two_pow)
  zify [hq]
  have h3 : ((2 : ℤ) ^ f) ^ 3 = ((2 ^ f : ℕ) : ℤ) ^ 3 := by push_cast; ring
  simp [Finset.prod_Icc_succ_top] at h
  push_cast at h ⊢
  linear_combination h

theorem not_dvd_four {q : ℕ} (hq : 2 ≤ q) :
    ¬ q ^ 2 * ((q ^ 2) ^ 2 - 1) ∣ q * (q ^ 2 - 1) := by
  intro h
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  have h2 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ h1
  have hpos : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  have hle := Nat.le_of_dvd hpos h
  zify [h1, h2] at hle
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  nlinarith [mul_pos (by positivity : (0 : ℤ) < q) (by positivity : (0 : ℤ) < q),
    mul_nonneg (sub_nonneg.mpr hq') (sub_nonneg.mpr hq')]

theorem not_dvd_five {q : ℕ} (hq : 2 ≤ q) :
    ¬ q ^ 2 * ((q ^ 2) ^ 2 - 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  intro h
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < q ^ 2 * (q ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
  have e1 : (q ^ 2) ^ 2 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [h1, show 1 ≤ (q ^ 2) ^ 2 from Nat.one_le_pow _ _ h1]
    ring
  have h2 : q ^ 2 * (q ^ 2 - 1) * (q ^ 2 + 1) ∣ q ^ 2 * (q ^ 2 - 1) * (q * (q ^ 3 + 1)) := by
    have : q ^ 2 * ((q ^ 2) ^ 2 - 1) = q ^ 2 * (q ^ 2 - 1) * (q ^ 2 + 1) := by rw [e1]; ring
    rw [this] at h
    have e2 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) = q ^ 2 * (q ^ 2 - 1) * (q * (q ^ 3 + 1)) := by
      ring
    rw [e2] at h
    exact h
  have h3 : q ^ 2 + 1 ∣ q * (q ^ 3 + 1) := Nat.dvd_of_mul_dvd_mul_left hpos h2
  obtain ⟨c, hc⟩ := h3
  have h5 : (q : ℤ) + 1 = ((q : ℤ) ^ 2 + 1) * ((c : ℤ) - ((q : ℤ) ^ 2 - 1)) := by
    have : ((q : ℤ) * ((q : ℤ) ^ 3 + 1)) = ((q : ℤ) ^ 2 + 1) * c := by exact_mod_cast hc
    linear_combination this
  have hd : ((q : ℤ) ^ 2 + 1) ∣ ((q : ℤ) + 1) := ⟨_, h5⟩
  have hd' : q ^ 2 + 1 ∣ q + 1 := by exact_mod_cast hd
  have := Nat.le_of_dvd (by omega) hd'
  nlinarith

theorem not_dvd_card_su (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ}
    (hn : n = 4 ∨ n = 5) :
    ¬ Nat.card K * (Nat.card K ^ 2 - 1) ∣ Nat.card ↥(SU (unitaryInvolution K 2 f) (n - 2)) := by
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rcases hn with rfl | rfl
  · rw [card_suAnti_two hK hf, hK]
    exact not_dvd_four hq
  · rw [card_suAnti_three hK hf, hK]
    exact not_dvd_five hq

end Orders

end CFSG.RankThree.PartOne.KFOUT3
