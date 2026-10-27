module

public import CFSG.RankThree.Classical.SiegelRadical
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitarySummand

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

variable {k : Type*} [Field k] {n : ℕ}

section Rect

variable {R : Finset (Fin n × Fin n)}

@[expose] def rectSum (R : Finset (Fin n × Fin n)) (c : R → k) : Matrix (Fin n) (Fin n) k :=
  ∑ α : R, Matrix.single α.1.1 α.1.2 (c α)

theorem rectSum_add (c d : R → k) : rectSum R (c + d) = rectSum R c + rectSum R d := by
  simp only [rectSum, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]

theorem rectSum_zero : rectSum R (0 : R → k) = 0 := by
  simp [rectSum]

theorem rectSum_apply (c : R → k) (x y : Fin n) :
    rectSum R c x y = ∑ α : R, if α.1.1 = x ∧ α.1.2 = y then c α else 0 := by
  simp only [rectSum, Matrix.sum_apply, Matrix.single_apply]

theorem rectSum_apply_self (c : R → k) (α : R) : rectSum R c α.1.1 α.1.2 = c α := by
  rw [rectSum_apply, Finset.sum_eq_single α]
  · exact ite_eq_left ⟨rfl, rfl⟩
  · intro δ _ hδ
    refine ite_eq_right fun h => hδ (Subtype.ext (Prod.ext h.1 h.2))
  · exact fun h => absurd (Finset.mem_univ α) h

theorem sum_single_eq_rectSum (c : Fin n × Fin n → k) :
    ∑ ij ∈ R, Matrix.single ij.1 ij.2 (c ij) = rectSum R (fun α => c α.1) :=
  (Finset.sum_coe_sort R (fun ij => Matrix.single ij.1 ij.2 (c ij))).symm

theorem diagonal_mul_rectSum (d : Fin n → k) (hd : ∀ x, d x ≠ 0) (c : R → k) :
    Matrix.diagonal d * rectSum R c =
      rectSum R (fun α => d α.1.1 * c α * (d α.1.2)⁻¹) * Matrix.diagonal d := by
  rw [rectSum, rectSum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [diagonal_mul_single', single_mul_diagonal', inv_mul_cancel_right₀ (hd _)]

variable {I J : Finset (Fin n)} (hIJ : Disjoint I J) (hR : R ⊆ I ×ˢ J)
include hIJ hR

omit hIJ in
theorem fst_mem_of_rect (α : R) : α.1.1 ∈ I := (Finset.mem_product.mp (hR α.2)).1

omit hIJ in
theorem snd_mem_of_rect (α : R) : α.1.2 ∈ J := (Finset.mem_product.mp (hR α.2)).2

theorem fst_ne_snd_of_rect (α δ : R) : α.1.1 ≠ δ.1.2 := fun h =>
  Finset.disjoint_left.mp hIJ (fst_mem_of_rect hR α) (h ▸ snd_mem_of_rect hR δ)

theorem rectSum_mul_rectSum (c d : R → k) : rectSum R c * rectSum R d = 0 := by
  rw [rectSum, rectSum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun δ _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (fst_ne_snd_of_rect hIJ hR δ α).symm _

theorem rectMat_mul (c d : R → k) :
    (1 + rectSum R c) * (1 + rectSum R d) = 1 + rectSum R (c + d) := by
  rw [add_mul, one_mul, mul_add, mul_one, rectSum_mul_rectSum hIJ hR, add_zero, rectSum_add]
  abel

theorem det_rectMat (c : R → k) : (1 + rectSum R c).det = 1 := by
  classical
  have hzero : ∀ x y : Fin n, (x ∉ I ∨ y ∈ I) → rectSum R c x y = 0 := by
    intro x y hxy
    rw [rectSum_apply]
    refine Finset.sum_eq_zero fun α _ => ite_eq_right fun h => ?_
    rcases hxy with hx | hy
    · exact hx (h.1 ▸ fst_mem_of_rect hR α)
    · exact Finset.disjoint_left.mp hIJ hy (h.2 ▸ snd_mem_of_rect hR α)
  rw [Matrix.twoBlockTriangular_det' _ (fun x => x ∉ I)]
  · have h1 : Matrix.toSquareBlockProp (1 + rectSum R c) (fun x => x ∉ I) = 1 := by
      ext x y
      rw [Matrix.toSquareBlockProp_def, Matrix.of_apply, Matrix.add_apply,
        hzero x y (Or.inl x.2), add_zero]
      by_cases hxy : x = y
      · rw [hxy, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hxy, Matrix.one_apply_ne fun h => hxy (Subtype.ext h)]
    have h2 : Matrix.toSquareBlockProp (1 + rectSum R c) (fun x => ¬x ∉ I) = 1 := by
      ext x y
      rw [Matrix.toSquareBlockProp_def, Matrix.of_apply, Matrix.add_apply,
        hzero x y (Or.inr (not_not.mp y.2)), add_zero]
      by_cases hxy : x = y
      · rw [hxy, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hxy, Matrix.one_apply_ne fun h => hxy (Subtype.ext h)]
    rw [h1, h2, Matrix.det_one, Matrix.det_one, mul_one]
  · intro i hi j hj
    have hij : i ≠ j := fun h => hi (h ▸ not_not.mp hj)
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, hzero i j (Or.inl hi)]

@[expose] def rectSL (c : R → k) : Matrix.SpecialLinearGroup (Fin n) k :=
  ⟨1 + rectSum R c, det_rectMat hIJ hR c⟩

theorem coe_rectSL (c : R → k) :
    (rectSL hIJ hR c : Matrix (Fin n) (Fin n) k) = 1 + rectSum R c :=
  rfl

variable (k) in
@[expose] def rectHom : Multiplicative (R → k) →* Matrix.SpecialLinearGroup (Fin n) k where
  toFun c := rectSL hIJ hR c.toAdd
  map_one' := Subtype.ext (by
    rw [coe_rectSL, toAdd_one, rectSum_zero, add_zero, Matrix.SpecialLinearGroup.coe_one])
  map_mul' c d := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_rectSL, coe_rectSL, coe_rectSL, rectMat_mul hIJ hR,
      toAdd_mul])

variable (k) in
@[expose] def rectUnipotent : Subgroup (LinearFlag.projectiveSL n k) :=
  ((LinearFlag.proj n k).comp (rectHom k hIJ hR)).range

theorem det_one_add_sum_single (c : Fin n × Fin n → k) :
    (1 + ∑ ij ∈ R, Matrix.single ij.1 ij.2 (c ij)).det = 1 := by
  rw [sum_single_eq_rectSum]
  exact det_rectMat hIJ hR _

theorem mem_rectUnipotent {x : LinearFlag.projectiveSL n k} :
    x ∈ rectUnipotent k hIJ hR ↔ ∃ c : Fin n × Fin n → k,
      x = LinearFlag.proj n k ⟨1 + ∑ ij ∈ R, Matrix.single ij.1 ij.2 (c ij),
        det_one_add_sum_single hIJ hR c⟩ := by
  classical
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun ij => if h : ij ∈ R then c.toAdd ⟨ij, h⟩ else 0, ?_⟩
    change LinearFlag.proj n k (rectSL hIJ hR c.toAdd) = _
    congr 1
    apply Subtype.ext
    rw [coe_rectSL]
    change 1 + rectSum R c.toAdd = 1 + ∑ ij ∈ R, _
    rw [sum_single_eq_rectSum]
    congr 2
    funext α
    simp
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd (fun α => c α.1), ?_⟩
    change LinearFlag.proj n k (rectSL hIJ hR _) = _
    congr 1
    apply Subtype.ext
    rw [coe_rectSL]
    change _ = 1 + ∑ ij ∈ R, _
    rw [sum_single_eq_rectSum]
    rfl

theorem proj_comp_rectHom_injective :
    Function.Injective ((LinearFlag.proj n k).comp (rectHom k hIJ hR)) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  rw [MonoidHom.comp_apply, LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at hc
  obtain ⟨u, -, hu⟩ := hc
  apply Multiplicative.toAdd.injective
  funext α
  have h := congrFun (congrFun hu α.1.1) α.1.2
  change (1 + rectSum R c.toAdd) α.1.1 α.1.2 = _ at h
  have hne := fst_ne_snd_of_rect hIJ hR α α
  rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, rectSum_apply_self,
    Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hne] at h
  rw [h, toAdd_one, Pi.zero_apply]

end Rect

section Torus

theorem pairDiag_apply_left (i j : Fin n) (ζ : k) : pairDiag i j ζ i = ζ := by
  rw [pairDiag, Function.update_self]

theorem pairDiag_apply_right {i j : Fin n} (hij : i ≠ j) (ζ : k) : pairDiag i j ζ j = ζ⁻¹ := by
  rw [pairDiag, Function.update_of_ne hij.symm, Function.update_self]

theorem pairDiag_apply_of_ne {i j x : Fin n} (hi : x ≠ i) (hj : x ≠ j) (ζ : k) :
    pairDiag i j ζ x = 1 := by
  rw [pairDiag, Function.update_of_ne hi, Function.update_of_ne hj, Pi.one_apply]

theorem pairDiag_apply_ne_zero (i j : Fin n) {ζ : k} (hζ : ζ ≠ 0) (x : Fin n) :
    pairDiag i j ζ x ≠ 0 := by
  by_cases hi : x = i
  · rw [hi, pairDiag_apply_left]
    exact hζ
  · by_cases hj : x = j
    · rw [hj, pairDiag, Function.update_of_ne (hj ▸ hi), Function.update_self]
      exact inv_ne_zero hζ
    · rw [pairDiag_apply_of_ne hi hj]
      exact one_ne_zero

@[expose] def pairTorus {i j : Fin n} (hij : i ≠ j) {ζ : k} (hζ : ζ ≠ 0) :
    Matrix.SpecialLinearGroup (Fin n) k :=
  ⟨Matrix.diagonal (pairDiag i j ζ), det_pairDiag hij hζ⟩

variable {I J : Finset (Fin n)} (hIJ : Disjoint I J) {R : Finset (Fin n × Fin n)}
  (hR : R ⊆ I ×ˢ J)

theorem pairTorus_conj_rectSL {i j : Fin n} (hij : i ≠ j) {ζ : k} (hζ : ζ ≠ 0) (c : R → k) :
    pairTorus hij hζ * rectSL hIJ hR c * (pairTorus hij hζ)⁻¹ =
      rectSL hIJ hR (fun α => pairDiag i j ζ α.1.1 * c α * (pairDiag i j ζ α.1.2)⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rectSL,
    coe_rectSL]
  change Matrix.diagonal (pairDiag i j ζ) * _ = _ * Matrix.diagonal (pairDiag i j ζ)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    diagonal_mul_rectSum _ (pairDiag_apply_ne_zero i j hζ)]

end Torus

theorem linear_rectangular_unipotent_central_preimage_abelian {p f : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) [Finite k] (hk : Nat.card k = p ^ f) {I J : Finset (Fin n)}
    (hIJ : Disjoint I J) {R : Finset (Fin n × Fin n)} (hR : R ⊆ I ×ˢ J) :
    IsElemAbelian p (rectUnipotent k hIJ hR) ∧
      Nat.card (rectUnipotent k hIJ hR) = p ^ (f * R.card) ∧
      ∀ {Y : Type*} [Group Y] (φ : Y →* LinearFlag.projectiveSL n k), Function.Surjective φ →
        φ.ker ≤ Subgroup.center Y → ∀ a ∈ (rectUnipotent k hIJ hR).comap φ,
          ∀ b ∈ (rectUnipotent k hIJ hR).comap φ, a * b = b * a := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite k
  have : CharP k p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  have hpv : ∀ v : R → k, p • v = 0 := fun v => funext fun α => by
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hcard : Nat.card (rectUnipotent k hIJ hR) = p ^ (f * R.card) := by
    rw [rectUnipotent,
      ← Nat.card_congr (MonoidHom.ofInjective (proj_comp_rectHom_injective hIJ hR)).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hk, Nat.card_eq_fintype_card,
      Fintype.card_coe, ← pow_mul]
  set ρ := (LinearFlag.proj n k).comp (rectHom k hIJ hR) with hρ
  refine ⟨isElemAbelian_range hpv ρ, hcard, ?_⟩
  intro Y _ φ hφ hZ a ha b hb
  have hp2 : p ≠ 2 := by omega
  have h9 : p ^ f ≠ 9 := by
    intro h
    have h3 : p ∣ 9 := h ▸ dvd_pow_self p (by rintro rfl; simp at h)
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h3))
    omega
  have hconj : ∀ {i j : Fin n} (hij : i ≠ j) {ζ : k} (hζ : ζ ≠ 0) (v : R → k),
      LinearFlag.proj n k (pairTorus hij hζ) * ρ (Multiplicative.ofAdd v) *
        (LinearFlag.proj n k (pairTorus hij hζ))⁻¹ =
      ρ (Multiplicative.ofAdd (fun α => pairDiag i j ζ α.1.1 * v α * (pairDiag i j ζ α.1.2)⁻¹)) :=
    fun hij ζ hζ v => by
      change LinearFlag.proj n k (pairTorus hij hζ) * LinearFlag.proj n k (rectSL hIJ hR v) *
        (LinearFlag.proj n k (pairTorus hij hζ))⁻¹ = LinearFlag.proj n k (rectSL hIJ hR _)
      rw [← map_inv, ← map_mul, ← map_mul, pairTorus_conj_rectSL hIJ hR hij hζ v]
      rfl
  have hscale : ∀ (i j : Fin n) (ζ : k) (δ : R) (y : k),
      (fun ε : R => pairDiag i j ζ ε.1.1 * (Pi.single δ y : R → k) ε *
        (pairDiag i j ζ ε.1.2)⁻¹) =
        (Pi.single δ (pairDiag i j ζ δ.1.1 * y * (pairDiag i j ζ δ.1.2)⁻¹) : R → k) := by
    intro i j ζ δ y
    funext ε
    by_cases h : ε = δ
    · subst h
      simp
    · simp [h]
  have hsmul : ∀ (δ : R) (m : ℕ) (y : k),
      (Pi.single δ ((m : k) * y) : R → k) = m • (Pi.single δ y : R → k) := by
    intro δ m y
    funext ε
    by_cases h : ε = δ
    · subst h
      simp [nsmul_eq_mul]
    · simp [h]
  have hsingle : ∀ (α : R) (x : k) (δ : R) (y : k),
      liftPair hφ ρ (Pi.single α x) (Pi.single δ y) = 1 := by
    intro α x δ y
    have hα : α.1.1 ≠ α.1.2 := fst_ne_snd_of_rect hIJ hR α α
    by_cases hαδ : α = δ
    · subst hαδ
      let _ := centerCommGroup Y
      let β : k → k → Additive (Subgroup.center Y) := fun x y =>
        liftPairAdd hφ ρ hZ (Pi.single α x) (Pi.single α y)
      have hsq : ∀ c z : k,
          pairDiag α.1.1 α.1.2 c α.1.1 * z * (pairDiag α.1.1 α.1.2 c α.1.2)⁻¹ = c ^ 2 * z := by
        intro c z
        rw [pairDiag_apply_left, pairDiag_apply_right hα, inv_inv]
        ring
      have hb := CFSG.SectionRank.OddCover.square_invariant_alternating_eq_zero hp2 hk β
        (fun x x' y => by simp only [β, Pi.single_add, liftPairAdd_add_left])
        (fun x y y' => by simp only [β, Pi.single_add, liftPairAdd_add_right])
        (fun x => liftPairAdd_self hφ ρ hZ _)
        (fun c hc x y => by
          refine liftPairAdd_congr hφ ρ hZ (liftPair_conj' hφ ρ hZ _
            ((hconj hα hc _).trans ?_) ((hconj hα hc _).trans ?_))
          · rw [hscale, hsq]
          · rw [hscale, hsq])
        h9 x y
      exact (liftPairAdd_eq_zero_iff hφ ρ hZ _ _).mp hb
    ·
      obtain ⟨m, hm0, hm2, hm3⟩ : ∃ m : ℕ, (m : k) ≠ 0 ∧ ¬p ∣ m ^ 2 * 1 - 1 ∧
          ¬p ∣ m ^ 2 * m - 1 := by
        have hcast : ∀ m : ℕ, m < p → 0 < m → (m : k) ≠ 0 := fun m hm hm0 h =>
          absurd (Nat.le_of_dvd hm0 ((CharP.cast_eq_zero_iff k p m).mp h)) (by omega)
        by_cases h7 : p = 7
        · subst h7
          exact ⟨3, hcast 3 (by norm_num) (by norm_num), by decide, by decide⟩
        · refine ⟨2, hcast 2 (by omega) (by norm_num), fun h => ?_, fun h => ?_⟩
          · norm_num at h
            have := Nat.le_of_dvd (by norm_num) h
            omega
          · norm_num at h
            exact h7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
      have hpow : pairDiag α.1.1 α.1.2 (m : k) α.1.1 * x *
          (pairDiag α.1.1 α.1.2 (m : k) α.1.2)⁻¹ =
          ((m ^ 2 : ℕ) : k) * x := by
        rw [pairDiag_apply_left, pairDiag_apply_right hα, inv_inv, Nat.cast_pow]
        ring
      have key : ∀ t : ℕ, (t = 1 ∨ t = m) →
          pairDiag α.1.1 α.1.2 (m : k) δ.1.1 * y * (pairDiag α.1.1 α.1.2 (m : k) δ.1.2)⁻¹ =
            (t : k) * y →
          liftPair hφ ρ (Pi.single α x) (Pi.single δ y) = 1 := by
        intro t ht hfac
        refine liftPair_eq_one_of_weight hφ ρ hZ hp (hpv _) (s := m ^ 2) (t := t) ?_ ?_ ?_
        · rcases ht with rfl | rfl
          · rw [mul_one]
            exact Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h => hm0 (by rw [h, Nat.cast_zero]))
          · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ fun h =>
              hm0 (by rw [h, Nat.cast_zero])) fun h => hm0 (by rw [h, Nat.cast_zero]))
        · rcases ht with rfl | rfl
          · exact hm2
          · exact hm3
        · refine liftPair_conj' hφ ρ hZ _ ((hconj hα hm0 _).trans ?_)
            ((hconj hα hm0 _).trans ?_)
          · rw [hscale, hpow, hsmul]
          · rw [hscale, hfac, hsmul]
      have hδs : δ.1.2 ≠ α.1.1 := (fst_ne_snd_of_rect hIJ hR α δ).symm
      have hδr : δ.1.1 ≠ α.1.2 := fst_ne_snd_of_rect hIJ hR δ α
      by_cases hr : δ.1.1 = α.1.1
      · have hs : δ.1.2 ≠ α.1.2 := fun hs => hαδ (Subtype.ext (Prod.ext hr.symm hs.symm))
        refine key m (Or.inr rfl) ?_
        rw [hr, pairDiag_apply_left, pairDiag_apply_of_ne hδs hs, inv_one, mul_one]
      · by_cases hs : δ.1.2 = α.1.2
        · refine key m (Or.inr rfl) ?_
          rw [pairDiag_apply_of_ne hr hδr, hs, pairDiag_apply_right hα, inv_inv]
          ring
        · refine key 1 (Or.inl rfl) ?_
          rw [pairDiag_apply_of_ne hr hδr, pairDiag_apply_of_ne hδs hs, inv_one, mul_one,
            Nat.cast_one]
  have hvanish : ∀ v w : R → k, liftPair hφ ρ v w = 1 := by
    intro v w
    rw [← Finset.univ_sum_single v, ← Finset.univ_sum_single w]
    exact liftPair_eq_one_of_sum hφ ρ hZ _ _ _ _ fun α _ δ _ => hsingle α (v α) δ (w δ)
  exact mul_comm_of_liftPair_eq_one hφ ρ hZ hvanish ha hb

end CFSG.RankThree.Classical
