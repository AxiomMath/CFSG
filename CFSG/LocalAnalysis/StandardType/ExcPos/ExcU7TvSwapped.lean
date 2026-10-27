module

public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7TvDefs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcU7

open Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {L : Type} [Field L] {ν : ℕ}

lemma u7sw_dotProduct_map (σ : L →+* L) {v φ : Fin ν → L} (h : φ ⬝ᵥ v = 0) :
    (fun i => σ (v i)) ⬝ᵥ (fun i => σ (φ i)) = 0 := by
  simp only [dotProduct] at h ⊢
  simp_rw [← map_mul]
  rw [← map_sum]
  have hsum : (∑ i, v i * φ i) = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsum, map_zero]

lemma u7sw_dotProduct_map' (σ : L →+* L) {v φ : Fin ν → L} (h : φ ⬝ᵥ v = 0) :
    (fun i => σ (φ i)) ⬝ᵥ (fun i => σ (v i)) = 0 := by
  simp only [dotProduct] at h ⊢
  simp_rw [← map_mul]
  rw [← map_sum, h, map_zero]

lemma u7sw_map_ne_zero {σ : L →+* L} (hσ : Function.Injective σ) {v : Fin ν → L}
    (hv : v ≠ 0) : (fun i => σ (v i)) ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi : σ (v i) = 0 := by simpa using congrFun h i
  exact hσ (by simpa using hi)

lemma u7sw_map_ne_zero' {σ : L → L} (hσ : Function.Injective σ) (h0 : σ 0 = 0)
    {v : Fin ν → L} (hv : v ≠ 0) : (fun i => σ (v i)) ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi : σ (v i) = 0 := by simpa using congrFun h i
  exact hσ (by simpa [h0] using hi)

lemma u7sw_map_tvMat (σ : L →+* L) {v φ : Fin ν → L} (s : L) :
    (tvMat v φ s).map σ =
      1 + σ s • Matrix.vecMulVec (fun i => σ (v i)) (fun i => σ (φ i)) := by
  ext i j
  simp only [tvMat, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply]
  by_cases hij : i = j
  · subst hij
    simp [map_add, map_mul, mul_assoc]
  · simp [hij, map_mul, mul_assoc]

lemma u7sw_inv_one_add_smul_vecMulVec {w u : Fin ν → L} (c : L) (h : u ⬝ᵥ w = 0) :
    (1 + c • Matrix.vecMulVec w u)⁻¹ = 1 - c • Matrix.vecMulVec w u := by
  have hsq : Matrix.vecMulVec w u * Matrix.vecMulVec w u = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]
  apply Matrix.inv_eq_right_inv
  calc (1 + c • Matrix.vecMulVec w u) * (1 - c • Matrix.vecMulVec w u)
      = 1 - (c * c) • (Matrix.vecMulVec w u * Matrix.vecMulVec w u) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
          Matrix.smul_mul, smul_smul]
        abel
    _ = 1 := by rw [hsq, smul_zero, sub_zero]

lemma u7sw_stdUnitary_tvMat_of_coe (σ : L ≃+* L) {v φ : Fin ν → L} (h : φ ⬝ᵥ v = 0)
    {X : SL(ν, L)} {s : L} (hX : (X : Matrix (Fin ν) (Fin ν) L) = tvMat v φ s) :
    ((stdUnitary σ.toRingHom X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ s)) := by
  have hwu : (fun i => σ.toRingHom (φ i)) ⬝ᵥ (fun i => σ.toRingHom (v i)) = 0 :=
    u7sw_dotProduct_map' σ.toRingHom h
  rw [coe_stdUnitary, hX, u7sw_map_tvMat σ.toRingHom s,
    u7sw_inv_one_add_smul_vecMulVec (σ.toRingHom s) hwu,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  rw [tvMat]
  simp only [neg_smul, sub_eq_add_neg]
  rfl

lemma u7sw_tvMat_injective {v φ : Fin ν → L} (hv : v ≠ 0) (hφ : φ ≠ 0) {s t : L}
    (H : tvMat v φ s = tvMat v φ t) : s = t := by
  have hN : Matrix.vecMulVec v φ ≠ 0 := Matrix.vecMulVec_ne_zero hv hφ
  have h1 : s • Matrix.vecMulVec v φ = t • Matrix.vecMulVec v φ := by
    have := congrArg (fun M => M - 1) H
    simpa only [tvMat, add_sub_cancel_left] using this
  have h2 : (s - t) • Matrix.vecMulVec v φ = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hN

lemma u7sw_smul_eq_zero_of_not_proportional {v u : Fin ν → L} (hv : v ≠ 0)
    (hvu : ¬ ∃ a : L, u = a • v) {c d : L} (hcd : c • v = d • u) : c = 0 ∧ d = 0 := by
  have hu : u ≠ 0 := fun h => hvu ⟨0, by simp [h]⟩
  have hc : c = 0 := by
    by_contra hc
    have hd : d ≠ 0 := by
      intro hd
      rw [hd, zero_smul] at hcd
      rcases smul_eq_zero.mp hcd with h | h
      · exact hc h
      · exact hv h
    apply hvu
    refine ⟨d⁻¹ * c, ?_⟩
    rw [← smul_smul, hcd, smul_smul, inv_mul_cancel₀ hd, one_smul]
  constructor
  · exact hc
  · have : d • u = 0 := by rw [← hcd, hc, zero_smul]
    rcases smul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hu

lemma u7sw_rankOne_independent {v u w φ : Fin ν → L} (hv : v ≠ 0) (hu : u ≠ 0)
    (hvu : ¬ ∃ a : L, u = a • v) (hw : w ≠ 0) (hφ : φ ≠ 0) {α β : L}
    (H : α • Matrix.vecMulVec v w = β • Matrix.vecMulVec u φ) : α = 0 ∧ β = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hvec : (α * w j) • v = (β * φ j) • u := by
    ext i
    have h := congrFun (congrFun H i) j
    simpa [Matrix.smul_apply, Matrix.vecMulVec_apply, mul_assoc, mul_comm, mul_left_comm] using h
  obtain ⟨hα, _⟩ := u7sw_smul_eq_zero_of_not_proportional hv hvu hvec
  have hα0 : α = 0 := by
    rcases mul_eq_zero.mp hα with h | h
    · exact h
    · exact absurd h hj
  have hβ0 : β = 0 := by
    rw [hα0, zero_smul] at H
    rcases smul_eq_zero.mp H.symm with h | h
    · exact h
    · exact absurd h (Matrix.vecMulVec_ne_zero hu hφ)
  exact ⟨hα0, hβ0⟩

lemma u7sw_tvMat_mul {v φ u w : Fin ν → L} (a b : L) :
    tvMat v φ a * tvMat u w b =
      1 + a • Matrix.vecMulVec v φ + b • Matrix.vecMulVec u w +
        (a * b) • (Matrix.vecMulVec v φ * Matrix.vecMulVec u w) := by
  simp only [tvMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_add, mul_comm b a]
  abel

lemma u7sw_vecMulVec_comm_of_tvMat_comm {v φ u w : Fin ν → L} {s t : L} (hs : s ≠ 0)
    (ht : t ≠ 0) (H : tvMat v φ s * tvMat u w t = tvMat u w t * tvMat v φ s) :
    Matrix.vecMulVec v φ * Matrix.vecMulVec u w =
      Matrix.vecMulVec u w * Matrix.vecMulVec v φ := by
  have hsum : 1 + s • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w +
        (s * t) • (Matrix.vecMulVec v φ * Matrix.vecMulVec u w) =
      1 + t • Matrix.vecMulVec u w + s • Matrix.vecMulVec v φ +
        (t * s) • (Matrix.vecMulVec u w * Matrix.vecMulVec v φ) := by
    rw [← u7sw_tvMat_mul (v := v) (φ := φ) (u := u) (w := w) (a := s) (b := t),
      ← u7sw_tvMat_mul (v := u) (φ := w) (u := v) (w := φ) (a := t) (b := s)]
    exact H
  have hEq : (s * t) • (Matrix.vecMulVec v φ * Matrix.vecMulVec u w) =
      (t * s) • (Matrix.vecMulVec u w * Matrix.vecMulVec v φ) := by
    have hthis := congrArg
      (fun M => M - (1 + s • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w)) hsum
    rw [show 1 + s • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w +
            (s * t) • (Matrix.vecMulVec v φ * Matrix.vecMulVec u w) -
            (1 + s • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w) =
            (s * t) • (Matrix.vecMulVec v φ * Matrix.vecMulVec u w) by abel,
          show 1 + t • Matrix.vecMulVec u w + s • Matrix.vecMulVec v φ +
            (t * s) • (Matrix.vecMulVec u w * Matrix.vecMulVec v φ) -
            (1 + s • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w) =
            (t * s) • (Matrix.vecMulVec u w * Matrix.vecMulVec v φ) by abel] at hthis
    exact hthis
  have hst : s * t ≠ 0 := mul_ne_zero hs ht
  have hzero : (s * t) • (Matrix.vecMulVec v φ * Matrix.vecMulVec u w -
      Matrix.vecMulVec u w * Matrix.vecMulVec v φ) = 0 := by
    rw [smul_sub, hEq, mul_comm t s, sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · exact absurd h hst
  · exact sub_eq_zero.mp h

lemma u7sw_tvMat_mul_eq_iff {v φ u w : Fin ν → L} (hv : v ≠ 0) (hu : u ≠ 0)
    (hvu : ¬ ∃ a : L, u = a • v) (hw : w ≠ 0) (hφ : φ ≠ 0)
    (hNN' : Matrix.vecMulVec v φ * Matrix.vecMulVec u w = 0)
    {s s' t t' : L}
    (H : tvMat v φ s * tvMat u w t = tvMat v φ s' * tvMat u w t') :
    s = s' ∧ t = t' := by
  rw [u7sw_tvMat_mul (v := v) (φ := φ) (u := u) (w := w) (a := s) (b := t),
    u7sw_tvMat_mul (v := v) (φ := φ) (u := u) (w := w) (a := s') (b := t')] at H
  rw [hNN'] at H
  simp only [smul_zero, add_zero] at H
  have h2 : s • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w =
      s' • Matrix.vecMulVec v φ + t' • Matrix.vecMulVec u w := by
    rw [add_assoc, add_assoc] at H
    exact add_left_cancel H
  have h3 : (s - s') • Matrix.vecMulVec v φ =
      (t' - t) • Matrix.vecMulVec u w := by
    calc (s - s') • Matrix.vecMulVec v φ
        = s • Matrix.vecMulVec v φ - s' • Matrix.vecMulVec v φ := by rw [sub_smul]
      _ = (s • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w) -
            (s' • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w) := by abel
      _ = (s' • Matrix.vecMulVec v φ + t' • Matrix.vecMulVec u w) -
            (s' • Matrix.vecMulVec v φ + t • Matrix.vecMulVec u w) := by rw [h2]
      _ = t' • Matrix.vecMulVec u w - t • Matrix.vecMulVec u w := by abel
      _ = (t' - t) • Matrix.vecMulVec u w := by rw [sub_smul]
  obtain ⟨hss, htt⟩ := u7sw_rankOne_independent hv hu hvu hφ hw h3
  exact ⟨sub_eq_zero.mp hss, (sub_eq_zero.mp htt).symm⟩

lemma u7sw_smul_one_pow (a : L) (n : ℕ) :
    ((a • (1 : Matrix (Fin ν) (Fin ν) L)) ^ n) =
      (a ^ n) • (1 : Matrix (Fin ν) (Fin ν) L) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, Matrix.smul_mul, Matrix.one_mul, smul_smul, pow_succ]

lemma u7sw_vecMulVec_smul_mul {v φ : Fin ν → L} (a b : L) :
    Matrix.vecMulVec (a • v) (b • φ) = (a * b) • Matrix.vecMulVec v φ := by
  simp only [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
  rw [mul_comm b a]

theorem exists_rational_of_stable (σ : L ≃+* L) {T : Subgroup SL(ν, L)} (hT : IsTvGroup T)
    (hs : (T.map (stdUnitary σ.toRingHom)).map (stdUnitary σ.toRingHom) = T) :
    ∃ v φ : Fin ν → L, (∀ i, σ (σ (v i)) = v i) ∧ (∀ i, σ (σ (φ i)) = φ i) ∧ v ≠ 0 ∧ φ ≠ 0 ∧
      φ ⬝ᵥ v = 0 ∧ T = tvGroup v φ := by
  obtain ⟨v, φ, hv0, hφ0, h, hTeq⟩ := hT
  subst hTeq
  have hmap : (tvGroup v φ).map (stdUnitary σ.toRingHom) =
      tvGroup (fun i => σ (φ i)) (fun i => σ (v i)) := tvGroup_map_stdUnitary h σ
  have hwu : (fun i => σ (v i)) ⬝ᵥ (fun i => σ (φ i)) = 0 := u7sw_dotProduct_map σ.toRingHom h
  have hwu' : (fun i => σ (φ i)) ⬝ᵥ (fun i => σ (v i)) = 0 := by
    rw [dotProduct_comm]; exact hwu
  have hu2w2 : (fun i => σ (σ (φ i))) ⬝ᵥ (fun i => σ (σ (v i))) = 0 :=
    u7sw_dotProduct_map' σ.toRingHom hwu'
  have hmap2 : ((tvGroup v φ).map (stdUnitary σ.toRingHom)).map (stdUnitary σ.toRingHom) =
      tvGroup (fun i => σ (σ (v i))) (fun i => σ (σ (φ i))) := by
    rw [hmap]
    exact tvGroup_map_stdUnitary hwu σ
  have heq : tvGroup (fun i => σ (σ (v i))) (fun i => σ (σ (φ i))) = tvGroup v φ := by
    rw [← hmap2]
    exact hs
  have h2v0 : (fun i => σ (σ (v i))) ≠ 0 := by
    simpa using (u7sw_map_ne_zero (σ := σ.toRingHom) σ.injective
      (u7sw_map_ne_zero (σ := σ.toRingHom) σ.injective hv0))
  have h2φ0 : (fun i => σ (σ (φ i))) ≠ 0 := by
    simpa using (u7sw_map_ne_zero (σ := σ.toRingHom) σ.injective
      (u7sw_map_ne_zero (σ := σ.toRingHom) σ.injective hφ0))
  obtain ⟨a, b, ha0, hb0, h2v, h2φ⟩ :=
    (tvGroup_eq_iff hv0 hφ0 h2v0 h2φ0 h hu2w2).mp heq.symm
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv0
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hφ0
  set v0 : Fin ν → L := fun i => (v k)⁻¹ * v i with hv0def
  set φ0 : Fin ν → L := fun i => (φ m)⁻¹ * φ i with hφ0def
  have hσ2v : ∀ i, σ (σ (v0 i)) = v0 i := by
    intro i
    have hk2 : σ (σ (v k)) = a * v k := congrFun h2v k
    have hi2 : σ (σ (v i)) = a * v i := congrFun h2v i
    simp only [hv0def]
    simp only [map_mul, map_inv₀]
    rw [hk2, hi2, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ ha0]
  have hσ2φ : ∀ i, σ (σ (φ0 i)) = φ0 i := by
    intro i
    have hm2 : σ (σ (φ m)) = b * φ m := congrFun h2φ m
    have hi2 : σ (σ (φ i)) = b * φ i := congrFun h2φ i
    simp only [hφ0def]
    simp only [map_mul, map_inv₀]
    rw [hm2, hi2, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ hb0]
  have hv0' : v0 ≠ 0 := by
    intro hzero
    have hk' := congrFun hzero k
    simp only [hv0def, Pi.zero_apply] at hk'
    rw [inv_mul_cancel₀ hk] at hk'
    exact one_ne_zero hk'
  have hφ0' : φ0 ≠ 0 := by
    intro hzero
    have hm' := congrFun hzero m
    simp only [hφ0def, Pi.zero_apply] at hm'
    rw [inv_mul_cancel₀ hm] at hm'
    exact one_ne_zero hm'
  have hdot : φ0 ⬝ᵥ v0 = 0 := by
    have hfac : φ0 ⬝ᵥ v0 = ((φ m)⁻¹ * (v k)⁻¹) * (φ ⬝ᵥ v) := by
      simp only [dotProduct, hv0def, hφ0def]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfac, h, mul_zero]
  refine ⟨v0, φ0, hσ2v, hσ2φ, hv0', hφ0', hdot, ?_⟩
  rw [tvGroup_eq_iff hv0 hφ0 hv0' hφ0' h hdot]
  exact ⟨(v k)⁻¹, (φ m)⁻¹, inv_ne_zero hk, inv_ne_zero hm, by
      funext i; simp only [hv0def, Pi.smul_apply, smul_eq_mul], by
      funext i; simp only [hφ0def, Pi.smul_apply, smul_eq_mul]⟩

theorem swapped_isotropic (σ : L ≃+* L) {v φ : Fin ν → L} (hv : ∀ i, σ (σ (v i)) = v i)
    (hφ : ∀ i, σ (σ (φ i)) = φ i) (hv0 : v ≠ 0) (hφ0 : φ ≠ 0) (h : φ ⬝ᵥ v = 0)
    (hs : IsSwappedTv (stdUnitary σ.toRingHom) (tvGroup v φ)) :
    (∑ i, σ (v i) * v i = 0) ∧ (∑ i, σ (φ i) * φ i = 0) ∧
      ¬ ∃ a : L, (fun i => σ (φ i)) = a • v := by
  let u : Fin ν → L := fun i => σ (φ i)
  let w : Fin ν → L := fun i => σ (v i)
  have hu0 : u ≠ 0 := by
    simpa only [u] using u7sw_map_ne_zero' σ.injective (map_zero σ) hφ0
  have hw0 : w ≠ 0 := by
    simpa only [w] using u7sw_map_ne_zero' σ.injective (map_zero σ) hv0
  have hwu : w ⬝ᵥ u = 0 := u7sw_dotProduct_map σ.toRingHom h
  have hmap : (tvGroup v φ).map (stdUnitary σ.toRingHom) = tvGroup u w :=
    tvGroup_map_stdUnitary h σ
  have hnotprop : ¬ ∃ a : L, u = a • v := by
    rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro h0
      apply hu0
      rw [h0, zero_smul] at ha
      exact ha
    have hphi : φ = σ a • w := by
      funext i
      have hi2 : σ (u i) = σ a * σ (v i) := by
        rw [congrFun ha i]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      simpa only [u, w, Pi.smul_apply, smul_eq_mul, hφ i] using hi2
    have hr : ∃ a' b : L, a' ≠ 0 ∧ b ≠ 0 ∧ v = a' • u ∧ φ = b • w :=
      ⟨a⁻¹, σ a, inv_ne_zero ha0, fun hzero => ha0 (σ.injective (by rw [hzero, map_zero])),
        by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul], hphi⟩
    have huv : tvGroup u w = tvGroup v φ := (tvGroup_eq_iff hu0 hw0 hv0 hφ0 hwu h).mpr hr
    exact hs.2.2 (hmap.trans huv).symm
  have hne : tvGroup v φ ≠ ⊥ := tvGroup_ne_bot hv0 hφ0 h
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨s, hsx⟩ := (mem_tvGroup_iff h).mp x.property
  have hs0 : s ≠ 0 := by
    intro hs0
    apply hxne
    exact Subtype.ext (Subtype.ext (by rw [hsx, hs0]; simp [tvMat]))
  have hne' : tvGroup u w ≠ ⊥ := tvGroup_ne_bot hu0 hw0 hwu
  obtain ⟨y, hyne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
  obtain ⟨t, hty⟩ := (mem_tvGroup_iff hwu).mp y.property
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hyne
    exact Subtype.ext (Subtype.ext (by rw [hty, ht0]; simp [tvMat]))
  have hXY : (x : SL(ν, L)) * (y : SL(ν, L)) = (y : SL(ν, L)) * (x : SL(ν, L)) :=
    hs.2.1 x.val x.property y.val (by rw [hmap]; exact y.property)
  have hmats : (x.val : Matrix (Fin ν) (Fin ν) L) * (y.val : Matrix (Fin ν) (Fin ν) L) =
      (y.val : Matrix (Fin ν) (Fin ν) L) * (x.val : Matrix (Fin ν) (Fin ν) L) := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun z : SL(ν, L) => (z : Matrix (Fin ν) (Fin ν) L)) hXY
  have hcomm' : tvMat v φ s * tvMat u w t = tvMat u w t * tvMat v φ s := by
    simpa only [← hsx, ← hty] using hmats
  have hNN' : Matrix.vecMulVec v φ * Matrix.vecMulVec u w =
      Matrix.vecMulVec u w * Matrix.vecMulVec v φ :=
    u7sw_vecMulVec_comm_of_tvMat_comm hs0 ht0 hcomm'
  have hind : (φ ⬝ᵥ u) • Matrix.vecMulVec v w =
      (w ⬝ᵥ v) • Matrix.vecMulVec u φ := by
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_smul, Matrix.vecMulVec_smul] at hNN'
    exact hNN'
  obtain ⟨h1, h2⟩ := u7sw_rankOne_independent hv0 hu0 hnotprop hw0 hφ0 hind
  refine ⟨?_, ?_, hnotprop⟩
  · simpa only [w, dotProduct] using h2
  · have : (∑ i, σ (φ i) * φ i) = φ ⬝ᵥ u := by
      simp only [dotProduct, u]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]
    exact h1

theorem card_fixed_stable_le (σ : L ≃+* L) {Q : ℕ} (hσ : ∀ c, σ c = c ^ Q) (hQ : 2 ≤ Q)
    {v φ : Fin ν → L} (hv0 : v ≠ 0) (hφ0 : φ ≠ 0) (h : φ ⬝ᵥ v = 0)
    (hst : (tvGroup v φ).map (stdUnitary σ.toRingHom) = tvGroup v φ) :
    Finite ↥(tvGroup v φ ⊓ (stdUnitary σ.toRingHom).eqLocus (MonoidHom.id SL(ν, L))) ∧
      Nat.card ↥(tvGroup v φ ⊓ (stdUnitary σ.toRingHom).eqLocus (MonoidHom.id SL(ν, L))) ≤ Q := by
  let u : Fin ν → L := fun i => σ (φ i)
  let w : Fin ν → L := fun i => σ (v i)
  have hu0 : u ≠ 0 := by
    simpa only [u] using u7sw_map_ne_zero' σ.injective (map_zero σ) hφ0
  have hw0 : w ≠ 0 := by
    simpa only [w] using u7sw_map_ne_zero' σ.injective (map_zero σ) hv0
  have hwu : w ⬝ᵥ u = 0 := u7sw_dotProduct_map σ.toRingHom h
  have hmap : (tvGroup v φ).map (stdUnitary σ.toRingHom) = tvGroup u w :=
    tvGroup_map_stdUnitary h σ
  have huv : tvGroup u w = tvGroup v φ := by rw [← hmap]; exact hst
  obtain ⟨a, b, ha0, hb0, hua, hwb⟩ :=
    (tvGroup_eq_iff hv0 hφ0 hu0 hw0 h hwu).mp huv.symm
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have hPne : (Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ Q : Polynomial L) ≠ 0 := by
    have hdeg : (Polynomial.C (a * b) * Polynomial.X ^ Q : Polynomial L).natDegree = Q :=
      Polynomial.natDegree_C_mul_X_pow Q (a * b) hab0
    have hlt : (Polynomial.X : Polynomial L).natDegree <
        (Polynomial.C (a * b) * Polynomial.X ^ Q : Polynomial L).natDegree := by
      calc (Polynomial.X : Polynomial L).natDegree = 1 := Polynomial.natDegree_X
        _ < Q := by omega
        _ = (Polynomial.C (a * b) * Polynomial.X ^ Q : Polynomial L).natDegree := hdeg.symm
    have hdeg2 := Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt
    intro h0
    rw [h0] at hdeg2
    rw [Polynomial.natDegree_zero, hdeg] at hdeg2
    omega
  classical
  have hroot : ∀ z : ↥(tvGroup v φ ⊓ (stdUnitary σ.toRingHom).eqLocus (MonoidHom.id SL(ν, L))),
      ∃ t : L, ((z : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = tvMat v φ t ∧
        Polynomial.aeval t (Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ Q) = 0 := by
    intro z
    obtain ⟨hzT, hzfix⟩ := Subgroup.mem_inf.mp z.property
    obtain ⟨t, ht⟩ := (mem_tvGroup_iff h).mp hzT
    have hzfix' : stdUnitary σ.toRingHom z.val = z.val := hzfix
    refine ⟨t, ht, ?_⟩
    have hPh : ((stdUnitary σ.toRingHom z.val : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        tvMat u w (-(σ t)) := u7sw_stdUnitary_tvMat_of_coe σ h ht
    have hzmat : ((stdUnitary σ.toRingHom z.val : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        tvMat v φ t := by rw [hzfix', ht]
    have hEq : tvMat u w (-(σ t)) = tvMat v φ t := hPh.symm.trans hzmat
    have hrewrite : tvMat u w (-(σ t)) = tvMat v φ (-(σ t * (a * b))) := by
      rw [tvMat, tvMat, hua, hwb, u7sw_vecMulVec_smul_mul, smul_smul]
      congr 2
      ring
    have htt : t = -(σ t * (a * b)) :=
      u7sw_tvMat_injective hv0 hφ0 (hEq.symm.trans hrewrite)
    have hpoly : t + (a * b) * t ^ Q = 0 := by
      have ht' : t = -((a * b) * t ^ Q) := by
        calc t = -(σ t * (a * b)) := htt
          _ = -(t ^ Q * (a * b)) := by rw [hσ t]
          _ = -((a * b) * t ^ Q) := by ring
      nth_rewrite 1 [ht']
      exact neg_add_cancel _
    rw [show Polynomial.aeval t (Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ Q) =
        t + (a * b) * t ^ Q by
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_self_apply]]
    exact hpoly
  let par : ↥(tvGroup v φ ⊓ (stdUnitary σ.toRingHom).eqLocus (MonoidHom.id SL(ν, L))) →
      (Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ Q : Polynomial L).rootSet L :=
    fun z => ⟨Classical.choose (hroot z),
      (Polynomial.mem_rootSet_of_ne hPne).mpr (Classical.choose_spec (hroot z)).2⟩
  have hpar : Function.Injective par := by
    intro z z' hh
    have hz := (Classical.choose_spec (hroot z)).1
    have hz' := (Classical.choose_spec (hroot z')).1
    have hst : Classical.choose (hroot z) = Classical.choose (hroot z') := Subtype.ext_iff.mp hh
    apply Subtype.ext
    apply Subtype.ext
    rw [hz, hz', hst]
  have hbound : Nat.card
      ((Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ Q : Polynomial L).rootSet L) ≤
      Q := by
    rw [Nat.card_coe_set_eq]
    calc ((Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ Q : Polynomial L).rootSet L).ncard
        ≤ (Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ Q : Polynomial L).natDegree :=
          Polynomial.ncard_rootSet_le _ _
      _ ≤ Q := by
        have h1 : (Polynomial.X : Polynomial L).natDegree ≤ Q := by
          rw [Polynomial.natDegree_X]; omega
        have h2 := Polynomial.natDegree_C_mul_X_pow_le (a * b) Q
        exact le_trans (Polynomial.natDegree_add_le _ _) (max_le h1 h2)
  exact ⟨Finite.of_injective par hpar, le_trans (Nat.card_le_card_of_injective par hpar) hbound⟩

end CFSG.StandardType.LieKnownR2.ExcPos.ExcU7
