module

public import CFSG.RankThree.PartOne.D4RC.Regular

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Matrix

variable {L : Type*} [Field L]

theorem rco_det_diag_sub {D : Matrix (Fin 3) (Fin 3) L} (hD : ∀ i j, i ≠ j → D i j = 0) (c : L) :
    (D - c • (1 : Matrix (Fin 3) (Fin 3) L)).det = ∏ i, (D i i - c) := by
  have : D - c • (1 : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal (fun i => D i i - c) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hD i j hij, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [this, Matrix.det_diagonal]

theorem rco_exists_entry {D : Matrix (Fin 3) (Fin 3) L} (hD : ∀ i j, i ≠ j → D i j = 0) {c : L}
    (h : (D - c • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0) : ∃ i, D i i = c := by
  rw [rco_det_diag_sub hD, Finset.prod_eq_zero_iff] at h
  obtain ⟨i, -, hi⟩ := h
  exact ⟨i, sub_eq_zero.1 hi⟩

theorem rco_det_entry {D : Matrix (Fin 3) (Fin 3) L} (hD : ∀ i j, i ≠ j → D i j = 0)
    (i : Fin 3) : (D - D i i • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0 := by
  rw [rco_det_diag_sub hD]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

theorem rco_det_conj (X : SL(3, L)) (D : Matrix (Fin 3) (Fin 3) L) (c : L) :
    ((X : Matrix (Fin 3) (Fin 3) L) * D * ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) -
      c • (1 : Matrix (Fin 3) (Fin 3) L)).det = (D - c • (1 : Matrix (Fin 3) (Fin 3) L)).det := by
  have hX : (X : Matrix (Fin 3) (Fin 3) L) * ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h : (X : Matrix (Fin 3) (Fin 3) L) * D * ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) -
      c • (1 : Matrix (Fin 3) (Fin 3) L) = (X : Matrix (Fin 3) (Fin 3) L) *
        (D - c • (1 : Matrix (Fin 3) (Fin 3) L)) *
          ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hX]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
    Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]

theorem rco_det_frob_split {k : Type*} [Field k] [Algebra k L] (φ : L →+* L)
    (hφ : ∀ y : k, φ (algebraMap k L y) = algebraMap k L y) (H : SL(3, L)) (Y : SL(3, k)) {c : L}
    (h : (((H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹ : SL(3, L)) :
      Matrix (Fin 3) (Fin 3) L) - c • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0) :
    (((H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹ : SL(3, L)) :
      Matrix (Fin 3) (Fin 3) L) - φ c • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, rco_det_conj] at h ⊢
  set M : Matrix (Fin 3) (Fin 3) L :=
    ((Matrix.SpecialLinearGroup.map (algebraMap k L) Y : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)
    with hM
  have hmap : φ.mapMatrix (M - c • (1 : Matrix (Fin 3) (Fin 3) L)) =
      M - φ c • (1 : Matrix (Fin 3) (Fin 3) L) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, map_mul, hM, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, hφ]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [← hmap, ← RingHom.map_det, h, map_zero]

theorem rco_det_conj_GL (H Y : GL (Fin 3) L) (c : L) :
    (((H * Y * H⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) -
      c • (1 : Matrix (Fin 3) (Fin 3) L)).det =
      ((Y : Matrix (Fin 3) (Fin 3) L) - c • (1 : Matrix (Fin 3) (Fin 3) L)).det := by
  have hX : (H : Matrix (Fin 3) (Fin 3) L) * ((H⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h : ((H * Y * H⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) -
      c • (1 : Matrix (Fin 3) (Fin 3) L) = (H : Matrix (Fin 3) (Fin 3) L) *
        ((Y : Matrix (Fin 3) (Fin 3) L) - c • (1 : Matrix (Fin 3) (Fin 3) L)) *
          ((H⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, hX]
  have hdet : (H : Matrix (Fin 3) (Fin 3) L).det *
      ((H⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rw [← Matrix.det_mul, hX, Matrix.det_one]
  rw [h, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det _) (Matrix.det _), mul_assoc,
    hdet, mul_one]

theorem rco_det_frob_unitary {q : ℕ} (φ : L →+* L) (hφ : ∀ c, φ c = c ^ q) (H : GL (Fin 3) L)
    {Y : GL (Fin 3) L} (hY : Y ∈ unitarySet q 3) {c : L} (hc : c ≠ 0)
    (h : (((H * Y * H⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) -
      c • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0) :
    (((H * Y * H⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) -
      (φ c)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0 := by
  rw [rco_det_conj_GL] at h ⊢
  set M : Matrix (Fin 3) (Fin 3) L := (Y : Matrix (Fin 3) (Fin 3) L) with hM
  set e : L := φ c with he
  have he0 : e ≠ 0 := by
    rw [he]
    exact (map_ne_zero φ).2 hc
  have hU : (M.map (· ^ q))ᵀ * M = 1 := hY.2.2
  have hmapq : M.map (· ^ q) = φ.mapMatrix M := by
    ext i j
    simp [hφ]
  have hMdet : IsUnit M.det := by
    rw [hM]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit Y)
  have hinv : (φ.mapMatrix M)ᵀ = M⁻¹ := by
    rw [← hmapq]
    exact (Matrix.inv_eq_left_inv hU).symm
  have h1 : (φ.mapMatrix M - e • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0 := by
    have hmap : φ.mapMatrix (M - c • (1 : Matrix (Fin 3) (Fin 3) L)) =
        φ.mapMatrix M - e • (1 : Matrix (Fin 3) (Fin 3) L) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [he]
      · simp [Matrix.one_apply_ne hij]
    rw [← hmap, ← RingHom.map_det, h, map_zero]
  have h2 : (M⁻¹ - e • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0 := by
    rw [← hinv, ← Matrix.det_transpose, Matrix.transpose_sub, Matrix.transpose_transpose,
      Matrix.transpose_smul, Matrix.transpose_one]
    exact h1
  have h3 : M⁻¹ - e • (1 : Matrix (Fin 3) (Fin 3) L) =
      (-e) • (M⁻¹ * (M - e⁻¹ • (1 : Matrix (Fin 3) (Fin 3) L))) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hMdet, Matrix.mul_smul, Matrix.mul_one,
      smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ he0, neg_smul, neg_smul, one_smul]
    abel
  have hinv0 : (M⁻¹).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (Matrix.nonsing_inv_mul M hMdet)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [h3, Matrix.det_smul, Matrix.det_mul] at h2
  rcases mul_eq_zero.1 h2 with h4 | h4
  · exact absurd h4 (pow_ne_zero _ (neg_ne_zero.2 he0))
  · rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 hinv0
    · exact h5

end Matrix

section FrameMatrix

variable {L : Type} [Field L]

theorem rco_ratio {ρ : SL(3, L) →* ModGL TwistTag.D4.tag L}
    {σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ} (hρ : IsA2Frame ρ σ') {D₀ : SL(3, L)}
    (hD : ∀ i j, i ≠ j → (D₀ : Matrix (Fin 3) (Fin 3) L) i j = 0)
    {b : Fin TwistTag.D4.tag.rank → Lˣ} (hb : ρ D₀ = rootDiagUnit TwistTag.D4.tag b) {u v : Fin 3}
    (huv : u ≠ v) :
    (D₀ : Matrix (Fin 3) (Fin 3) L) u u =
      (rootChar b (σ' u v) : L) * (D₀ : Matrix (Fin 3) (Fin 3) L) v v := by
  obtain ⟨e, he⟩ := hρ.transv u v huv
  have hc : D₀ * Matrix.SpecialLinearGroup.transvection huv 1 * D₀⁻¹ =
      Matrix.SpecialLinearGroup.transvection huv (rootChar b (σ' u v) : L) := by
    apply hρ.injective
    rw [map_mul, map_mul, map_inv, hb, he, he, rootDiagUnit_conj_pinnedX b (hρ.isRoot u v huv)]
    congr 1
    ring
  have hm : D₀ * Matrix.SpecialLinearGroup.transvection huv 1 =
      Matrix.SpecialLinearGroup.transvection huv (rootChar b (σ' u v) : L) * D₀ := by
    rw [← hc]
    group
  have h := congrFun (congrFun (congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) hm)
    u) v
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h
  have h01 := hD 0 1 (by decide)
  have h02 := hD 0 2 (by decide)
  have h10 := hD 1 0 (by decide)
  have h12 := hD 1 2 (by decide)
  have h20 := hD 2 0 (by decide)
  have h21 := hD 2 1 (by decide)
  fin_cases u <;> fin_cases v <;> (try exact absurd rfl huv) <;>
    simp_all [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, Matrix.add_apply]

theorem rco_entries_conj {X D₀ D₁ : SL(3, L)}
    (hD₀ : ∀ i j, i ≠ j → (D₀ : Matrix (Fin 3) (Fin 3) L) i j = 0)
    (hD₁ : ∀ i j, i ≠ j → (D₁ : Matrix (Fin 3) (Fin 3) L) i j = 0) (h : X * D₀ * X⁻¹ = D₁)
    (u : Fin 3) :
    ∃ v, (D₁ : Matrix (Fin 3) (Fin 3) L) v v = (D₀ : Matrix (Fin 3) (Fin 3) L) u u := by
  refine rco_exists_entry hD₁ ?_
  rw [← h, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, rco_det_conj]
  exact rco_det_entry hD₀ u

end FrameMatrix

section Arith

theorem rco_not_dvd {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq : 2 ≤ q) (hpd : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) :
    ¬ p ∣ q ∧ ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsmall : ∀ m : ℤ, m = 1 ∨ m = 3 → ¬ (p : ℤ) ∣ m := by
    intro m hm h
    rcases hm with rfl | rfl
    · exact hpz.not_dvd_one h
    · have : p ∣ 3 := by exact_mod_cast h
      have := Nat.le_of_dvd (by norm_num) this
      omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h' : (p : ℤ) ∣ q := by exact_mod_cast h
    have h1 : (p : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - q * (q + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h' _)
    exact hpz.not_dvd_one h1
  · have h' : (p : ℤ) ∣ (q : ℤ) - 1 := by
      have : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ q)]; ring
      rw [← this]
      exact_mod_cast h
    have h3 : (p : ℤ) ∣ 2 + ε := by
      have e : (2 + ε : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - ((q : ℤ) - 1) * (q + 1 + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h' _)
    refine hsmall (2 + ε) ?_ h3
    rcases hε with rfl | rfl <;> norm_num
  · have h' : (p : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast h
    have h3 : (p : ℤ) ∣ 2 - ε := by
      have e : (2 - ε : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - ((q : ℤ) + 1) * (q - 1 + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h' _)
    refine hsmall (2 - ε) ?_ h3
    rcases hε with rfl | rfl <;> norm_num

theorem rco_eq_one_of_pow {G : Type*} [Monoid G] {p m n : ℕ} (hp : p.Prime) {t : G}
    (h1 : t ^ (p ^ m) = 1) (h2 : t ^ n = 1) (hpn : ¬ p ∣ n) : t = 1 := by
  have ha : orderOf t ∣ p ^ m := orderOf_dvd_of_pow_eq_one h1
  have hb : orderOf t ∣ n := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 ha
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.1 hj
  · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero j)).trans (hj ▸ hb)) hpn

end Arith

section Frob

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem rco_frob_entry (F : RclFrame ℓ f K σ ε p L) {i : Fin 4} (D : RclAlgData F i)
    {D₀ : SL(3, L)} (hfix : D₀ ∈ fixSubgroup D.Φ')
    (hD : ∀ i j, i ≠ j → (D₀ : Matrix (Fin 3) (Fin 3) L) i j = 0) {u : Fin 3}
    (ht0 : (D₀ : Matrix (Fin 3) (Fin 3) L) u u ≠ 0) :
    (ε = 1 → ∃ v, (D₀ : Matrix (Fin 3) (Fin 3) L) v v =
      ((D₀ : Matrix (Fin 3) (Fin 3) L) u u) ^ (ℓ ^ f)) ∧
    (ε = -1 → ∃ v, (D₀ : Matrix (Fin 3) (Fin 3) L) v v =
      (((D₀ : Matrix (Fin 3) (Fin 3) L) u u) ^ (ℓ ^ f))⁻¹) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set t := (D₀ : Matrix (Fin 3) (Fin 3) L) u u with ht
  have hdet : ((D₀ : Matrix (Fin 3) (Fin 3) L) - t • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0 :=
    rco_det_entry hD u
  set φ : L →+* L := iterateFrobenius L ℓ f with hφdef
  have hφ : ∀ c, φ c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · obtain ⟨Y, hY⟩ := (D.split h1 D₀).1 hfix
    have hk : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_cube hℓ F.hf F.hK σ F.hσ
    have hfix' : ∀ y : fixSubfield σ, φ (algebraMap (fixSubfield σ) L y) =
        algebraMap (fixSubfield σ) L y := by
      intro y
      have : Fintype (fixSubfield σ) := Fintype.ofFinite _
      rw [hφ, ← map_pow]
      congr 1
      have h2 := FiniteField.pow_card y
      rwa [Fintype.card_eq_nat_card, hk] at h2
    have hdet2 : (((D.H * Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) L) Y *
        D.H⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) - t • (1 : Matrix (Fin 3) (Fin 3) L)).det =
          0 := by
      rw [← hY]
      exact hdet
    have h3 := rco_det_frob_split φ hfix' D.H Y hdet2
    rw [← hY] at h3
    obtain ⟨v, hv⟩ := rco_exists_entry hD h3
    exact ⟨v, by rw [hv, hφ]⟩
  · obtain ⟨Y, hYU, hY⟩ := (D.unit h1 D₀).1 hfix
    have hcoe : ((Matrix.SpecialLinearGroup.toGL D₀ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        (D₀ : Matrix (Fin 3) (Fin 3) L) := Matrix.SpecialLinearGroup.coe_GL_coe_matrix D₀
    have hdet' : (((Matrix.SpecialLinearGroup.toGL D.H * Y *
        (Matrix.SpecialLinearGroup.toGL D.H)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) -
          t • (1 : Matrix (Fin 3) (Fin 3) L)).det = 0 := by
      rw [← hY, hcoe]
      exact hdet
    have h2 := rco_det_frob_unitary φ hφ _ hYU ht0 hdet'
    rw [← hY, hcoe] at h2
    obtain ⟨v, hv⟩ := rco_exists_entry hD h2
    exact ⟨v, by rw [hv, hφ]⟩

end Frob

section Main

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem rco_pow_three_conj (F : RclFrame ℓ f K σ ε p L) [Fact p.Prime] (S : Sylow p 𝒞[K, σ])
    {c : 𝒞[K, σ]} (hc : RclConj F S c) {x : 𝒞[K, σ]} {i : Fin 4} (sp : RclSpecial F x i)
    (hspc : sp.c = c) (hxS : x ∈ (S : Subgroup 𝒞[K, σ])) {g : 𝒞[K, σ]} (hgP : g ∈ rclPx sp)
    (hgN : g ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) :
    ∀ a ∈ (S : Subgroup 𝒞[K, σ]) ⊓ rclPx sp, g ^ 3 * a * (g ^ 3)⁻¹ = a := by
  classical
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by have := F.hf; omega) hℓ.one_lt
  set T : Subgroup 𝒞[K, σ] := (S : Subgroup 𝒞[K, σ]) with hT
  set P := rclPx sp with hP
  obtain ⟨hcyc, hA1, -, hAZ, -, -⟩ := rcy_sylow_split F S hc sp hspc hxS
  obtain ⟨β, hβ, hβfix, -, -⟩ := rcy_coord F hc
  obtain ⟨D⟩ := rcl_exists_algData F i
  have hrange : D.ρ.range = rootSpan TwistTag.D4.tag L (d4Sigma i) := by
    rw [D.frame.range, D.sigma_eq]
  have hQ : (fixSubgroup D.Φ').map D.ρ = rclQ F i :=
    rcl_map_fix_eq D.frame.injective hrange D.Φ_eq
  have hψ : Function.Injective (rclPsi sp) := d4QPsi_injective triEmb_injective F.g0 sp.c x
  have hTp : IsPGroup p T := S.isPGroup'
  have : IsCyclic ↥(T ⊓ P) := hcyc
  obtain ⟨a₀', ha₀gen⟩ := IsCyclic.exists_generator (α := ↥(T ⊓ P))
  set a₀ : 𝒞[K, σ] := a₀'.1 with ha₀def
  have ha₀A : a₀ ∈ T ⊓ P := a₀'.2
  have ha₀x : a₀ ∈ Subgroup.centralizer ({x} : Set 𝒞[K, σ]) := rclPx_le_centralizer sp ha₀A.2
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    apply hA1
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (ha₀gen ⟨y, hy⟩)
    have h2 : a₀' = 1 := Subtype.ext h
    rw [h2, one_zpow] at hn
    rw [Subgroup.mem_bot]
    exact (congrArg (fun z : ↥(T ⊓ P) => (z : 𝒞[K, σ])) hn).symm
  set b₀ := β ⟨a₀, ha₀A.1⟩ with hb₀
  have hψa : rclPsi sp ⟨a₀, ha₀x⟩ = rootDiagUnit TwistTag.D4.tag b₀ := by
    rw [d4QPsi_apply, hb₀, hβ, hspc]
  have hψaQ : rclPsi sp ⟨a₀, ha₀x⟩ ∈ rclQ F i := (mem_rclPx_iff sp ha₀x).1 ha₀A.2
  rw [← hQ] at hψaQ
  obtain ⟨D₀, hD₀fix, hD₀⟩ := hψaQ
  have hD₀T : D.ρ D₀ ∈ torusGroup TwistTag.D4.tag L := by
    rw [hD₀, d4QPsi_apply, hspc]
    exact (hc a₀ ha₀A.1).1
  have hD₀d := rct_diag_of_mem_torus D.frame hD₀T
  set d : Fin 3 → L := fun u => (D₀ : Matrix (Fin 3) (Fin 3) L) u u with hd
  have hD₀diag : (D₀ : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d := by
    ext u v
    by_cases huv : u = v
    · subst huv
      simp [hd]
    · rw [hD₀d u v huv, Matrix.diagonal_apply_ne _ huv]
  have hpowD : ∀ n : ℕ, ((D₀ ^ n : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal (fun u => d u ^ n) := fun n => by
    rw [Matrix.SpecialLinearGroup.coe_pow, hD₀diag, Matrix.diagonal_pow]
    rfl
  have hpowd : ∀ n : ℕ, ∀ u v, u ≠ v →
      ((D₀ ^ n : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) u v = 0 :=
    fun n u v huv => by rw [hpowD n, Matrix.diagonal_apply_ne _ huv]
  have hpowe : ∀ n : ℕ, ∀ u, ((D₀ ^ n : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) u u = d u ^ n :=
    fun n u => by rw [hpowD n, Matrix.diagonal_apply_eq]
  have hψpow : ∀ n : ℕ, rclPsi sp (⟨a₀, ha₀x⟩ ^ n) = D.ρ (D₀ ^ n) := fun n => by
    rw [map_pow, map_pow, hD₀]
  have hpow_eq : ∀ m n : ℕ, (∀ u, d u ^ m = d u ^ n) → a₀ ^ m = a₀ ^ n := by
    intro m n h
    have h1 : D₀ ^ m = D₀ ^ n := by
      apply Subtype.ext
      rw [hpowD, hpowD]
      congr 1
      funext u
      exact h u
    have h2 := hψ (show rclPsi sp (⟨a₀, ha₀x⟩ ^ m) = rclPsi sp (⟨a₀, ha₀x⟩ ^ n) by
      rw [hψpow, hψpow, h1])
    have h3 := congrArg (fun z : Subgroup.centralizer ({x} : Set 𝒞[K, σ]) => (z : 𝒞[K, σ])) h2
    simp only [Subgroup.coe_pow] at h3
    exact h3
  have hpow_eq' : ∀ m n : ℕ, a₀ ^ m = a₀ ^ n → ∀ u, d u ^ m = d u ^ n := by
    intro m n h u
    have h1 : (⟨a₀, ha₀x⟩ : Subgroup.centralizer ({x} : Set 𝒞[K, σ])) ^ m =
        ⟨a₀, ha₀x⟩ ^ n := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_pow]; exact h)
    have h2 : D₀ ^ m = D₀ ^ n := D.frame.injective (by rw [← hψpow, ← hψpow, h1])
    rw [← hpowe m u, ← hpowe n u, h2]
  have hd0 : ∀ u, d u ≠ 0 := by
    intro u h0
    have hdet : (D₀ : Matrix (Fin 3) (Fin 3) L).det = 1 := D₀.2
    rw [hD₀diag, Matrix.det_diagonal, Finset.prod_eq_zero (Finset.mem_univ u) h0] at hdet
    exact zero_ne_one hdet
  have hdist : ∀ u v, u ≠ v → d u ≠ d v := by
    intro u v huv heq
    have hr := rco_ratio D.frame hD₀d (hD₀.trans hψa) huv
    have hχ : rootChar b₀ (D.σ' u v) = 1 := by
      apply Units.ext
      have h1 : (rootChar b₀ (D.σ' u v) : L) * d v = 1 * d v := by
        rw [one_mul]
        exact hr.symm.trans heq
      exact mul_right_cancel₀ (hd0 v) h1
    have hα : D.σ' u v ∈ d4Sigma i := by
      rw [← D.sigma_eq]
      exact ⟨u, v, huv, rfl⟩
    have hb : rootDiagUnit TwistTag.D4.tag b₀ =
        F.g0⁻¹ * triEmb K σ L (sp.c * a₀ * sp.c⁻¹) * F.g0 := by rw [hb₀, hβ, hspc]
    have hZ := rcy_mem_centralizer_of_rootChar F sp ha₀x hb (hβfix _) hα hχ
    have h3 : a₀ ∈ T ⊓ P ⊓ Subgroup.centralizer (P : Set 𝒞[K, σ]) := ⟨ha₀A, hZ⟩
    rw [hAZ, Subgroup.mem_bot] at h3
    exact ha₀1 h3
  have hgx : g ∈ Subgroup.centralizer ({x} : Set 𝒞[K, σ]) := rclPx_le_centralizer sp hgP
  have hgA : g * a₀ * g⁻¹ ∈ T ⊓ P :=
    ⟨(Subgroup.mem_normalizer_iff.1 hgN a₀).1 ha₀A.1, rclPx_normal sp hgx ha₀A.2⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, a₀' ^ r = ⟨g * a₀ * g⁻¹, hgA⟩ :=
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (ha₀gen _))
  have hr' : a₀ ^ r = g * a₀ * g⁻¹ := by
    have := congrArg (fun z : ↥(T ⊓ P) => (z : 𝒞[K, σ])) hr
    simp only [Subgroup.coe_pow] at this
    exact this
  have hψgQ := (mem_rclPx_iff sp hgx).1 hgP
  rw [← hQ] at hψgQ
  obtain ⟨X, -, hX⟩ := hψgQ
  have hconj : X * D₀ * X⁻¹ = D₀ ^ r := by
    apply D.frame.injective
    rw [map_mul, map_mul, map_inv, map_pow, hX, hD₀, ← map_pow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact hr'.symm
  have hex : ∀ u, ∃ v, d v ^ r = d u := fun u => by
    obtain ⟨v, hv⟩ := rco_entries_conj hD₀d (hpowd r) hconj u
    exact ⟨v, by rw [← hpowe r v]; exact hv⟩
  choose π' hπ' using hex
  have hπinj : Function.Injective π' := fun u u' h => by
    by_contra hne
    exact hdist u u' hne (by rw [← hπ' u, ← hπ' u', h])
  let π : Equiv.Perm (Fin 3) := Equiv.ofBijective π' (Finite.injective_iff_bijective.1 hπinj)
  have hπ : ∀ u, d (π u) ^ r = d u := hπ'
  have hπn : ∀ n : ℕ, ∀ u, d ((π ^ n) u) ^ (r ^ n) = d u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ' π, Equiv.Perm.mul_apply, pow_succ' r, pow_mul, hπ, ih]
  have hgpow : ∀ n : ℕ, g ^ n * a₀ * (g ^ n)⁻¹ = a₀ ^ (r ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, pow_one, one_mul, inv_one, mul_one]
    | succ n ih =>
      have h1 : g ^ (n + 1) * a₀ * (g ^ (n + 1))⁻¹ = g * (g ^ n * a₀ * (g ^ n)⁻¹) * g⁻¹ := by
        rw [pow_succ']
        simp only [mul_inv_rev, mul_assoc]
      rw [h1, ih, ← conj_pow, ← hr', ← pow_mul, pow_succ, mul_comm r (r ^ n)]
  have hfin3 : g ^ 3 * a₀ * (g ^ 3)⁻¹ = a₀ → ∀ a ∈ T ⊓ P, g ^ 3 * a * (g ^ 3)⁻¹ = a := by
    intro h a ha
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (ha₀gen ⟨a, ha⟩)
    have hn' : a₀ ^ n = a := by
      have := congrArg (fun z : ↥(T ⊓ P) => (z : 𝒞[K, σ])) hn
      simp only [Subgroup.coe_zpow] at this
      exact this
    rw [← hn', ← conj_zpow, h]
  have hS3 : ∀ τ : Equiv.Perm (Fin 3), τ ^ 2 = 1 ∨ τ ^ 3 = 1 := by decide
  rcases hS3 π with h2 | h3
  · by_cases hπ1 : π = 1
    · refine hfin3 ?_
      have h1 : a₀ ^ r = a₀ ^ 1 := hpow_eq r 1 (fun u => by
        have := hπ u
        rw [hπ1, Equiv.Perm.one_apply] at this
        rw [this, pow_one])
      rw [pow_one] at h1
      have h6 : ∀ n : ℕ, a₀ ^ (r ^ n) = a₀ := by
        intro n
        induction n with
        | zero => rw [pow_zero, pow_one]
        | succ n ih => rw [pow_succ, pow_mul, ih, h1]
      rw [hgpow 3, h6]
    · exfalso
      obtain ⟨k, hk⟩ := (show ∀ τ : Equiv.Perm (Fin 3), τ ^ 2 = 1 → τ ≠ 1 → ∃ k, τ k = k by
        decide) π h2 hπ1
      obtain ⟨u, hu⟩ : ∃ u, π u ≠ u := by
        by_contra hall
        push Not at hall
        exact hπ1 (Equiv.ext hall)
      have hπ2 : ∀ v, π (π v) = v := fun v => by
        have := congrArg (fun τ : Equiv.Perm (Fin 3) => τ v) h2
        simpa [pow_two] using this
      have hr2 : a₀ ^ (r ^ 2) = a₀ ^ 1 := hpow_eq _ _ (fun v => by
        have := hπn 2 v
        rw [h2, Equiv.Perm.one_apply] at this
        rw [this, pow_one])
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hTp) ⟨a₀, ha₀A.1⟩
      have hm' : orderOf a₀ = p ^ m := (Subgroup.orderOf_coe (⟨a₀, ha₀A.1⟩ : T)).trans hm
      have hpm : a₀ ^ (p ^ m) = a₀ ^ 0 := by rw [← hm', pow_orderOf_eq_one, pow_zero]
      have hr0 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · exfalso
          rw [h0, pow_zero] at hr'
          apply ha₀1
          have h5 : g * a₀ = g := by
            calc g * a₀ = g * a₀ * g⁻¹ * g := by group
              _ = g := by rw [← hr', one_mul]
          exact mul_eq_left.1 h5
        · exact h0
      have hdvd : p ^ m ∣ (r - 1) * (r + 1) := by
        rw [← hm']
        apply orderOf_dvd_of_pow_eq_one
        have h6 : (r - 1) * (r + 1) + 1 = r ^ 2 := by
          zify [hr0]
          ring
        have h7 := hr2
        rw [← h6, pow_succ, pow_one] at h7
        exact mul_eq_right.1 h7
      have hpr : ¬ p ∣ r - 1 := by
        intro hpr1
        have hcop : Nat.Coprime (p ^ m) (r + 1) := by
          apply Nat.Coprime.pow_left
          rw [Nat.Prime.coprime_iff_not_dvd hp]
          intro hp1
          have h8 : p ∣ 2 := by
            have e : r + 1 = (r - 1) + 2 := by omega
            rw [e] at hp1
            exact (Nat.dvd_add_right hpr1).1 hp1
          have := Nat.le_of_dvd (by norm_num) h8
          have := F.hp3
          omega
        have h9 : p ^ m ∣ r - 1 := hcop.dvd_of_dvd_mul_right hdvd
        have h10 : a₀ ^ r = a₀ ^ 1 := by
          rw [← hm'] at h9
          have h11 := orderOf_dvd_iff_pow_eq_one.1 h9
          calc a₀ ^ r = a₀ ^ (r - 1) * a₀ ^ 1 := by rw [← pow_add]; congr 1; omega
            _ = a₀ ^ 1 := by rw [h11, one_mul]
        have h12 := hpow_eq' r 1 h10
        apply hu
        by_contra hne
        apply hdist (π u) u hne
        rw [← hπ u, h12 (π u), pow_one]
      have hcop : Nat.Coprime (p ^ m) (r - 1) :=
        Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr)
      have hr1 : p ^ m ∣ r + 1 := hcop.dvd_of_dvd_mul_left hdvd
      have hr1' : a₀ ^ (r + 1) = a₀ ^ 0 := by
        rw [← hm'] at hr1
        rw [orderOf_dvd_iff_pow_eq_one.1 hr1, pow_zero]
      have hdr1 : ∀ v, d v ^ (r + 1) = 1 := fun v => by
        rw [hpow_eq' _ _ hr1' v, pow_zero]
      have hdp : ∀ v, d v ^ (p ^ m) = 1 := fun v => by
        rw [hpow_eq' _ _ hpm v, pow_zero]
      have hdk : d k = 1 := by
        have h1 : d k ^ r = d k := by
          have := hπ k
          rwa [hk] at this
        have h2' : d k ^ 2 = 1 := by
          calc d k ^ 2 = d k ^ r * d k := by rw [h1, sq]
            _ = d k ^ (r + 1) := (pow_succ _ _).symm
            _ = 1 := hdr1 k
        exact rco_eq_one_of_pow hp (hdp k) h2' (fun h => by
          have := Nat.le_of_dvd (by norm_num) h
          have := F.hp3
          omega)
      have huk : u ≠ k := fun h => hu (by rw [h, hk])
      have hπuk : π u ≠ k := fun h => huk (by rw [← hπ2 u, h, hk])
      set t := d u with ht
      have ht1 : t ≠ 1 := fun h => hdist u k huk (by rw [← ht, h, hdk])
      have hπu : d (π u) = t⁻¹ := by
        have h1 : t ^ r = d (π u) := by
          have := hπ (π u)
          rwa [hπ2 u] at this
        rw [← h1]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hdr1 u])
      have hall : ∀ v, d v = 1 ∨ d v = t ∨ d v = t⁻¹ := by
        intro v
        rcases (show ∀ a b c w : Fin 3, a ≠ b → b ≠ c → a ≠ c → w = a ∨ w = b ∨ w = c by
          decide) k u (π u) v huk.symm hu.symm hπuk.symm with h | h | h
        · left
          rw [h]
          exact hdk
        · right; left
          rw [h]
        · right; right
          rw [h]
          exact hπu
      have hfr := rco_frob_entry F D hD₀fix hD₀d (u := u) (hd0 u)
      have htq : t ^ (ℓ ^ f) = 1 ∨ t ^ (ℓ ^ f) = t ∨ t ^ (ℓ ^ f) = t⁻¹ := by
        rcases F.hε with h1 | h1
        · obtain ⟨v, hv⟩ := hfr.1 h1
          rcases hall v with h | h | h <;>
            rw [show d v = (D₀ : Matrix (Fin 3) (Fin 3) L) v v from rfl, hv] at h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        · obtain ⟨v, hv⟩ := hfr.2 h1
          rcases hall v with h | h | h <;>
            rw [show d v = (D₀ : Matrix (Fin 3) (Fin 3) L) v v from rfl, hv] at h
          · exact Or.inl (inv_eq_one.1 h)
          · exact Or.inr (Or.inr (by rw [← inv_inv (t ^ (ℓ ^ f)), h]))
          · exact Or.inr (Or.inl (inv_injective h))
      obtain ⟨hnq, hnq1, hnq1'⟩ := rco_not_dvd F.hε hp F.hp3 hq2 (by exact_mod_cast F.hpd)
      apply ht1
      rcases htq with h | h | h
      · exact rco_eq_one_of_pow hp (hdp u) h hnq
      · refine rco_eq_one_of_pow hp (hdp u) (n := ℓ ^ f - 1) ?_ hnq1
        have h1 : t ^ (ℓ ^ f - 1) * t = t ^ (ℓ ^ f) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [h] at h1
        exact mul_right_cancel₀ (hd0 u) (h1.trans (one_mul t).symm)
      · refine rco_eq_one_of_pow hp (hdp u) (n := ℓ ^ f + 1) ?_ hnq1'
        rw [pow_succ, h, inv_mul_cancel₀ (hd0 u)]
  · refine hfin3 ?_
    have h33 := hpow_eq (r ^ 3) 1 (fun u => by
      have := hπn 3 u
      rw [h3, Equiv.Perm.one_apply] at this
      rw [this, pow_one])
    rw [pow_one] at h33
    rw [hgpow 3, h33]

end Main

end CFSG.RankThree.PartOne.D4RC
