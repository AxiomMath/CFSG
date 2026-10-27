module

public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDPair

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

namespace Cliff

open TauCeti CliffordAlgebra

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {P : SpinPolarizationData Q} {ι : Type*}
  {b : Module.Basis ι K P.W} {z : CliffordAlgebra Q}

theorem zS_sq {m : ι} (hzc : z * cr b m = -(cr b m * z)) : cr b m * z * (cr b m * z) = 0 := by
  calc cr b m * z * (cr b m * z) = cr b m * (z * cr b m) * z := by noncomm_ring
    _ = 0 := by rw [hzc, mul_neg, ← mul_assoc, cr_sq, zero_mul, neg_mul, zero_mul, neg_zero]

theorem zT_sq {m : ι} (hza : z * an b m = -(an b m * z)) : z * an b m * (z * an b m) = 0 := by
  calc z * an b m * (z * an b m) = z * (an b m * z) * an b m := by noncomm_ring
    _ = 0 := by
        rw [show an b m * z = -(z * an b m) by rw [hza, neg_neg], mul_neg, neg_mul, mul_assoc,
          mul_assoc, an_sq, mul_zero, mul_zero, neg_zero]

theorem zSTS (hz : z * z = 1) (m : ι) :
    cr b m * z * (z * an b m) * (cr b m * z) = cr b m * z := by
  calc cr b m * z * (z * an b m) * (cr b m * z)
      = cr b m * (z * z) * an b m * cr b m * z := by noncomm_ring
    _ = cr b m * z := by rw [hz, mul_one, cr_an_cr]

theorem zTST (hz : z * z = 1) (m : ι) :
    z * an b m * (cr b m * z) * (z * an b m) = z * an b m := by
  calc z * an b m * (cr b m * z) * (z * an b m)
      = z * (an b m * cr b m * (z * z) * an b m) := by noncomm_ring
    _ = z * an b m := by rw [hz, mul_one, an_cr_an]

theorem z_anticomm (hz : z * z = 1) {m : ι} (hzc : z * cr b m = -(cr b m * z))
    (hza : z * an b m = -(an b m * z)) :
    cr b m * z * (z * an b m) + z * an b m * (cr b m * z) = 1 := by
  have hc := commute_mul_of_anticomm₂ hza hzc
  calc cr b m * z * (z * an b m) + z * an b m * (cr b m * z)
      = cr b m * (z * z) * an b m + z * (an b m * cr b m) * z := by noncomm_ring
    _ = cr b m * (z * z) * an b m + an b m * cr b m * (z * z) := by
        rw [hc]
        noncomm_ring
    _ = 1 := by rw [hz, mul_one, mul_one, cr_an_self]

theorem zSS {m m' : ι} (hzc : z * cr b m = -(cr b m * z)) (hzc' : z * cr b m' = -(cr b m' * z)) :
    cr b m * z * (cr b m' * z) = -(cr b m' * z * (cr b m * z)) := by
  calc cr b m * z * (cr b m' * z) = cr b m * (z * cr b m') * z := by noncomm_ring
    _ = -(cr b m * cr b m' * (z * z)) := by rw [hzc']; noncomm_ring
    _ = -(-(cr b m' * cr b m * (z * z))) := by rw [cr_cr b m m']; noncomm_ring
    _ = -(cr b m' * (z * cr b m) * z) := by rw [hzc]; noncomm_ring
    _ = -(cr b m' * z * (cr b m * z)) := by noncomm_ring

theorem zST (hz : z * z = 1) {m m' : ι} (hmm : m ≠ m') (hzc : z * cr b m = -(cr b m * z))
    (hza' : z * an b m' = -(an b m' * z)) :
    cr b m * z * (z * an b m') = -(z * an b m' * (cr b m * z)) := by
  have hc := commute_mul_of_anticomm₂ hza' hzc
  calc cr b m * z * (z * an b m') = cr b m * (z * z) * an b m' := by noncomm_ring
    _ = -(an b m' * cr b m * (z * z)) := by rw [hz, mul_one, mul_one, cr_an b hmm]
    _ = -(z * (an b m' * cr b m) * z) := by rw [hc]; noncomm_ring
    _ = -(z * an b m' * (cr b m * z)) := by noncomm_ring

theorem zTT {m m' : ι} (hza : z * an b m = -(an b m * z)) (hza' : z * an b m' = -(an b m' * z)) :
    z * an b m * (z * an b m') = -(z * an b m' * (z * an b m)) := by
  have h1 : an b m * z = -(z * an b m) := by rw [hza, neg_neg]
  have h2 : an b m' * z = -(z * an b m') := by rw [hza', neg_neg]
  calc z * an b m * (z * an b m') = z * (an b m * z) * an b m' := by noncomm_ring
    _ = -((z * z) * (an b m * an b m')) := by rw [h1]; noncomm_ring
    _ = -(-((z * z) * (an b m' * an b m))) := by rw [an_an b m m']; noncomm_ring
    _ = -(z * (an b m' * z) * an b m) := by rw [h2]; noncomm_ring
    _ = -(z * an b m' * (z * an b m)) := by noncomm_ring

variable (b) in
noncomputable abbrev twV (k : ι) : CliffordAlgebra Q := cr b k + an b k

theorem twV_sq (k : ι) : twV b k * twV b k = 1 := by
  rw [twV, add_mul, mul_add, mul_add, cr_sq, an_sq, zero_add, add_zero, cr_an_self]

theorem twV_cr {k m : ι} (hmk : m ≠ k) : twV b k * cr b m = -(cr b m * twV b k) := by
  rw [twV, add_mul, mul_add, cr_cr b k m, an_cr b hmk, neg_add]

theorem twV_an {k m : ι} (hmk : m ≠ k) : twV b k * an b m = -(an b m * twV b k) := by
  rw [twV, add_mul, mul_add, cr_an b hmk.symm, an_an b k m, neg_add]

end Cliff

namespace CarrierTD

open TauCeti TauCeti.TypeDSpinCarrier CarrierD Cliff RootData
open scoped commutatorElement

section Generic

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K] {σ : K →+* K} {π : Equiv.Perm (Fin n)}
  {F : (rootData n hn K).G →* (rootData n hn K).G}

theorem CM_fork : (rootData n hn K).CM (forkA n hn) (forkB n hn) = 0 := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  rw [rootData_CM, D_apply']
  split_ifs <;> omega

@[expose] noncomputable def twTorus (σ : K →+* K) (c : Kˣ) : Fin n → Kˣ := fun j =>
  if j.val = n - 2 then c else if j.val = n - 1 then Units.map (σ : K →* K) c else 1

theorem twTorus_char_A (c : Kˣ) :
    (∏ j, twTorus σ c j ^ (rootData n hn K).CM j (forkA n hn) : Kˣ) = c ^ 2 := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  rw [Finset.prod_eq_single (forkA n hn)]
  · have h2 : (rootData n hn K).CM (forkA n hn) (forkA n hn) = 2 := by
      rw [rootData_CM, D_apply', ite_eq_left rfl]
    dsimp only [twTorus]
    rw [ite_eq_left hAv, h2]
    exact zpow_ofNat c 2
  · intro j _ hj
    by_cases hjB : j = forkB n hn
    · subst hjB
      have h0 : (rootData n hn K).CM (forkB n hn) (forkA n hn) = 0 := by
        rw [rootData_CM, D_apply']
        split_ifs <;> omega
      rw [h0, zpow_zero]
    · have h1 : j.val ≠ n - 2 := fun h => hj (Fin.ext (h.trans hAv.symm))
      have h2 : j.val ≠ n - 1 := fun h => hjB (Fin.ext (h.trans hBv.symm))
      dsimp only [twTorus]
      rw [ite_eq_right h1, ite_eq_right h2, one_zpow]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem twTorus_char_B (c : Kˣ) :
    (∏ j, twTorus σ c j ^ (rootData n hn K).CM j (forkB n hn) : Kˣ) =
      Units.map (σ : K →* K) c ^ 2 := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  rw [Finset.prod_eq_single (forkB n hn)]
  · have h2 : (rootData n hn K).CM (forkB n hn) (forkB n hn) = 2 := by
      rw [rootData_CM, D_apply', ite_eq_left rfl]
    dsimp only [twTorus]
    rw [ite_eq_right (by omega : (forkB n hn).val ≠ n - 2), ite_eq_left hBv, h2]
    exact zpow_ofNat _ 2
  · intro j _ hj
    by_cases hjA : j = forkA n hn
    · subst hjA
      rw [CM_fork, zpow_zero]
    · have h1 : j.val ≠ n - 2 := fun h => hjA (Fin.ext (h.trans hAv.symm))
      have h2 : j.val ≠ n - 1 := fun h => hj (Fin.ext (h.trans hBv.symm))
      dsimp only [twTorus]
      rw [ite_eq_right h1, ite_eq_right h2, one_zpow]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem twTorus_mem_fixed (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ} (hc : σ (σ c) = c) :
    (rootData n hn K).torus (twTorus σ c) ∈ fixedSubgroup F := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  refine torus_mem_fixed_tw hF fun j => ?_
  have hBA : (forkB n hn).val ≠ n - 2 := by omega
  by_cases hjA : j = forkA n hn
  · subst hjA
    rw [hπA]
    dsimp only [twTorus]
    rw [ite_eq_right hBA, ite_eq_left hBv, ite_eq_left hAv]
    exact hc
  · by_cases hjB : j = forkB n hn
    · subst hjB
      rw [hπB]
      dsimp only [twTorus]
      rw [ite_eq_left hAv, ite_eq_right hBA, ite_eq_left hBv]
      rfl
    · have h1 : j.val ≠ n - 2 := fun h => hjA (Fin.ext (h.trans hAv.symm))
      have h2 : j.val ≠ n - 1 := fun h => hjB (Fin.ext (h.trans hBv.symm))
      have hj : j.val < n - 2 := by
        have := j.isLt
        omega
      rw [hπ j hj]
      dsimp only [twTorus]
      rw [ite_eq_right h1, ite_eq_right h2, Units.val_one, map_one]

theorem pairX_mem_commutator_sq (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ} (hc : σ (σ c) = c) (hc1 : (c : K) ^ 2 ≠ 1)
    {u : K} (hu : σ (σ u) = u) :
    (rootData n hn K).pairX σ (forkA n hn) (forkB n hn) u ∈
      ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  have hd : (c : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have hσw : σ (σ (u / ((c : K) ^ 2 - 1))) = u / ((c : K) ^ 2 - 1) := by
    simp only [map_div₀, map_sub, map_pow, hc, hu, map_one]
  have hconj : ∀ w : K, (rootData n hn K).torus (twTorus σ c) *
      (rootData n hn K).pairX σ (forkA n hn) (forkB n hn) w *
      ((rootData n hn K).torus (twTorus σ c))⁻¹ =
      (rootData n hn K).pairX σ (forkA n hn) (forkB n hn) ((c : K) ^ 2 * w) := fun w => by
    have e1 : (rootData n hn K).torus (twTorus σ c) *
        (rootData n hn K).pairX σ (forkA n hn) (forkB n hn) w *
        ((rootData n hn K).torus (twTorus σ c))⁻¹ =
        ((rootData n hn K).torus (twTorus σ c) * (rootData n hn K).x (forkA n hn) w *
          ((rootData n hn K).torus (twTorus σ c))⁻¹) *
        ((rootData n hn K).torus (twTorus σ c) * (rootData n hn K).x (forkB n hn) (σ w) *
          ((rootData n hn K).torus (twTorus σ c))⁻¹) := by
      simp only [pairX]
      group
    rw [e1, torus_conj_x, torus_conj_x, twTorus_char_A, twTorus_char_B, pairX, map_mul,
      map_pow]
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass]
  have hcomm : (rootData n hn K).pairX σ (forkA n hn) (forkB n hn) u =
      ⁅(rootData n hn K).torus (twTorus σ c),
        (rootData n hn K).pairX σ (forkA n hn) (forkB n hn) (u / ((c : K) ^ 2 - 1))⁆ := by
    rw [commutatorElement_def, hconj, pairX_inv CM_fork, ← pairX_add CM_fork]
    congr 1
    field_simp
    ring
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (twTorus_mem_fixed hF hπ hπA hπB hc)
    (pairX_mem_fixed hF hπA hπB CM_fork hσw)

theorem pairY_mem_commutator_sq (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ} (hc : σ (σ c) = c) (hc1 : (c : K) ^ 2 ≠ 1)
    {u : K} (hu : σ (σ u) = u) :
    (rootData n hn K).pairY σ (forkA n hn) (forkB n hn) u ∈
      ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  have hc1' : ((c : K) ^ 2)⁻¹ ≠ 1 := fun h => hc1 (inv_eq_one.mp h)
  have hd : ((c : K) ^ 2)⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hc1'
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hσw : σ (σ (u / (((c : K) ^ 2)⁻¹ - 1))) = u / (((c : K) ^ 2)⁻¹ - 1) := by
    simp only [map_div₀, map_sub, map_inv₀, map_pow, hc, hu, map_one]
  have hconj : ∀ w : K, (rootData n hn K).torus (twTorus σ c) *
      (rootData n hn K).pairY σ (forkA n hn) (forkB n hn) w *
      ((rootData n hn K).torus (twTorus σ c))⁻¹ =
      (rootData n hn K).pairY σ (forkA n hn) (forkB n hn) (((c : K) ^ 2)⁻¹ * w) := fun w => by
    have e1 : (rootData n hn K).torus (twTorus σ c) *
        (rootData n hn K).pairY σ (forkA n hn) (forkB n hn) w *
        ((rootData n hn K).torus (twTorus σ c))⁻¹ =
        ((rootData n hn K).torus (twTorus σ c) * (rootData n hn K).y (forkA n hn) w *
          ((rootData n hn K).torus (twTorus σ c))⁻¹) *
        ((rootData n hn K).torus (twTorus σ c) * (rootData n hn K).y (forkB n hn) (σ w) *
          ((rootData n hn K).torus (twTorus σ c))⁻¹) := by
      simp only [pairY]
      group
    rw [e1, torus_conj_y, torus_conj_y, twTorus_char_A, twTorus_char_B, pairY, map_mul,
      map_inv₀, map_pow]
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.coe_map,
      MonoidHom.coe_ofClass]
  have hcomm : (rootData n hn K).pairY σ (forkA n hn) (forkB n hn) u =
      ⁅(rootData n hn K).torus (twTorus σ c),
        (rootData n hn K).pairY σ (forkA n hn) (forkB n hn) (u / (((c : K) ^ 2)⁻¹ - 1))⁆ := by
    rw [commutatorElement_def, hconj, pairY_inv CM_fork, ← pairY_add CM_fork]
    congr 1
    field_simp
    ring
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (twTorus_mem_fixed hF hπ hπA hπB hc)
    (pairY_mem_fixed hF hπA hπB CM_fork hσw)

theorem exists_twShortOp (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {μ : Kˣ} (hμ : σ (σ μ) = μ) (hμ1 : (μ : K) ^ 2 ≠ 1)
    (m : Fin n) (hm : m.val ≤ n - 2) :
    ∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n m * twV (polarizationBasis n) (forkB n hn)) M ∧
      IsIntOp n (twV (polarizationBasis n) (forkB n hn) * anD n m) N ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M) ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K N) := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : (forkA n hn).val + 1 = (forkB n hn).val := by omega
  have hp := isDisjointPair_fork n hn K
  have hDj : ∀ j : Fin n, j.val < n - 2 → ∀ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      nu j * g * (nu j)⁻¹ ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun j hj g hg =>
    conj_mem_commutator (nu_mem_fixed hF (hπ j hj)) g hg
  have base : ∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n (forkA n hn) * twV (polarizationBasis n) (forkB n hn)) M ∧
      IsIntOp n (twV (polarizationBasis n) (forkB n hn) * anD n (forkA n hn)) N ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M) ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K N) := by
    refine ⟨rootIntMatrix n hn (.inl (forkB n hn)) + rootIntMatrix n hn (.inl (forkA n hn)),
      rootIntMatrix n hn (.inr (forkA n hn)) + rootIntMatrix n hn (.inr (forkB n hn)),
      ((isIntOp_forkE hn).add' (isIntOp_chainE hn hAB)).congr (mul_add _ _ _).symm,
      ((isIntOp_chainF hn hAB).add' (isIntOp_forkF hn)).congr (add_mul _ _ _).symm, ?_, ?_⟩
    · refine ⟨?_, fun u => ⟨(rootData n hn K).x (forkA n hn) u *
        (rootData n hn K).x (forkB n hn) u, ?_⟩, fun u hu => ⟨(rootData n hn K).pairX σ
          (forkA n hn) (forkB n hn) u, pairX_mem_commutator_sq hF hπ hπA hπB hμ hμ1
            (by rw [show σ u = u from hu, show σ u = u from hu]), ?_⟩⟩
      · rw [intMap_add']
        show ((rootData n hn K).E (forkB n hn) + (rootData n hn K).E (forkA n hn)) *
          ((rootData n hn K).E (forkB n hn) + (rootData n hn K).E (forkA n hn)) = 0
        rw [add_mul, mul_add, mul_add, ((rootData n hn K).sqZero _).ee,
          ((rootData n hn K).sqZero _).ee, hp.EE, hp.EE']
        simp
      · rw [mat_x_mul_x hp, intMap_add', smul_add]
        show 1 + u • (rootData n hn K).E (forkA n hn) + u • (rootData n hn K).E (forkB n hn) =
          1 + (u • (rootData n hn K).E (forkB n hn) + u • (rootData n hn K).E (forkA n hn))
        abel
      · rw [pairX, show σ u = u from hu, mat_x_mul_x hp, intMap_add', smul_add]
        show 1 + u • (rootData n hn K).E (forkA n hn) + u • (rootData n hn K).E (forkB n hn) =
          1 + (u • (rootData n hn K).E (forkB n hn) + u • (rootData n hn K).E (forkA n hn))
        abel
    · refine ⟨?_, fun u => ⟨(rootData n hn K).y (forkA n hn) u *
        (rootData n hn K).y (forkB n hn) u, ?_⟩, fun u hu => ⟨(rootData n hn K).pairY σ
          (forkA n hn) (forkB n hn) u, pairY_mem_commutator_sq hF hπ hπA hπB hμ hμ1
            (by rw [show σ u = u from hu, show σ u = u from hu]), ?_⟩⟩
      · rw [intMap_add']
        show ((rootData n hn K).F (forkA n hn) + (rootData n hn K).F (forkB n hn)) *
          ((rootData n hn K).F (forkA n hn) + (rootData n hn K).F (forkB n hn)) = 0
        rw [add_mul, mul_add, mul_add, ((rootData n hn K).sqZero _).ff,
          ((rootData n hn K).sqZero _).ff, hp.FF, hp.FF']
        simp
      · rw [mat_y_mul_y hp, intMap_add', smul_add, add_assoc]
        rfl
      · rw [pairY, show σ u = u from hu, mat_y_mul_y hp, intMap_add', smul_add, add_assoc]
        rfl
  have step : ∀ t : ℕ, (ht : t ≤ n - 2) →
      ∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
        IsIntOp n (crD n ⟨n - 2 - t, by omega⟩ * twV (polarizationBasis n) (forkB n hn)) M ∧
        IsIntOp n (twV (polarizationBasis n) (forkB n hn) * anD n ⟨n - 2 - t, by omega⟩) N ∧
        (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
          (intMap K M) ∧
        (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
          (intMap K N) := by
    intro t
    induction t with
    | zero => exact fun _ => base
    | succ t ih =>
      intro ht
      obtain ⟨M, N, hM, hN, hMR, hNR⟩ := ih (by omega)
      set j : Fin n := ⟨n - 2 - (t + 1), by omega⟩
      set k : Fin n := ⟨n - 2 - t, by omega⟩
      have hjv : j.val = n - 2 - (t + 1) := rfl
      have hkv : k.val = n - 2 - t := rfl
      have hjk : j.val + 1 = k.val := by omega
      have hjk' : j ≠ k := fin_ne (by omega)
      have hjB : j ≠ forkB n hn := fin_ne (by omega)
      have hkB : k ≠ forkB n hn := fin_ne (by omega)
      have hv := (commute_weyls (b := polarizationBasis n) (twV_cr hjB) (twV_an hjB) (twV_cr hkB)
        (twV_an hkB)).1
      have h1 : chainWeyl (polarizationBasis n) j k *
          (crD n k * twV (polarizationBasis n) (forkB n hn)) =
          crD n j * twV (polarizationBasis n) (forkB n hn) *
            chainWeyl (polarizationBasis n) j k := by
        rw [← mul_assoc, chainWeyl_mul_cr hjk', mul_assoc, ← hv.eq, ← mul_assoc]
      have h2 : chainWeyl (polarizationBasis n) j k *
          (twV (polarizationBasis n) (forkB n hn) * anD n k) =
          twV (polarizationBasis n) (forkB n hn) * anD n j *
            chainWeyl (polarizationBasis n) j k := by
        rw [← mul_assoc, ← hv.eq, mul_assoc, chainWeyl_mul_an hjk', ← mul_assoc]
      have hE := isIntOp_chainE hn hjk
      have hF' := isIntOp_chainF hn hjk
      have hD := hDj j (by omega)
      obtain ⟨hM', hMR'⟩ := rootOpIn_conj hE hF' (chain_E_sq hjk') (chain_F_sq hjk') hM h1 hD hMR
      obtain ⟨hN', hNR'⟩ := rootOpIn_conj hE hF' (chain_E_sq hjk') (chain_F_sq hjk') hN h2 hD hNR
      exact ⟨_, _, hM', hN', hMR', hNR'⟩
  have hm' : (⟨n - 2 - (n - 2 - m.val), by omega⟩ : Fin n) = m := Fin.ext (by simp only; omega)
  have h := step (n - 2 - m.val) (by omega)
  rw [hm'] at h
  exact h

theorem hasWitness_twShort_gen (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {μ : Kˣ} (hμ : σ (σ μ) = μ) (hμ1 : (μ : K) ^ 2 ≠ 1)
    (hchar : (2 : K) = 0) (h6 : 6 ≤ n) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 4 := by
  have hBv : (forkB n hn).val = n - 1 := rfl
  let J : Fin 5 → Fin n := fun a => ⟨a.val, by omega⟩
  have hJm : ∀ a, (J a).val ≤ n - 2 := fun a => by simp only [J]; omega
  have hJB : ∀ a, J a ≠ forkB n hn := fun a => fin_ne (by simp only [J]; omega)
  choose M N hM hN hMR hNR using fun a : Fin 5 =>
    exists_twShortOp hF hπ hπA hπB hμ hμ1 (J a) (hJm a)
  have h1 : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  choose gM hgMD hgM using fun a => (hMR a).memD 1 h1
  choose gN hgND hgN using fun a => (hNR a).memD 1 h1
  have hgM' : ∀ a, (rootData n hn K).mat (gM a) = 1 + intMap K (M a) := fun a => by
    rw [hgM, one_smul]
  have hgN' : ∀ a, (rootData n hn K).mat (gN a) = 1 + intMap K (N a) := fun a => by
    rw [hgN, one_smul]
  have hneg : ∀ A : Matrix (Fin (dimension n)) (Fin (dimension n)) K, -A = A := fun A => by
    ext a b
    rw [Matrix.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, hchar, zero_mul]
  have hcomm : ∀ {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ},
      IsIntOp n c X → IsIntOp n d Y → c * d = -(d * c) →
        Commute (intMap K X) (intMap K Y) := fun hc hd h => by
    show intMap K _ * intMap K _ = intMap K _ * intMap K _
    rw [← intMap_mul, ← intMap_mul, (hc.mul hd).eq ((hd.mul hc).neg.congr h.symm), intMap_neg',
      hneg]
  have hv2 := twV_sq (b := polarizationBasis n) (forkB n hn)
  have hpair : ∀ a, SqZeroPair (intMap K (M a)) (intMap K (N a)) := fun a =>
    { ee := (hMR a).sq
      ff := (hNR a).sq
      efe := intMap_eq_of (hM a) (hN a) (hM a) (zSTS hv2 (J a))
      fef := intMap_eq_of (hN a) (hM a) (hN a) (zTST hv2 (J a)) }
  have hne : ∀ a, intMap K (M a) ≠ 0 := fun a h0 => by
    have h : intMap K (M a) * intMap K (N a) + intMap K (N a) * intMap K (M a) = 1 := by
      rw [← intMap_mul, ← intMap_mul, ← intMap_add',
        (((hM a).mul (hN a)).add' ((hN a).mul (hM a))).eq
          (isIntOp_one.congr (z_anticomm hv2 (twV_cr (hJB a)) (twV_an (hJB a))).symm),
        intMap_one']
    rw [h0, zero_mul, mul_zero, add_zero] at h
    have h' := congrFun (congrFun h (vac (n := n))) (vac (n := n))
    rw [Matrix.zero_apply, Matrix.one_apply_eq] at h'
    exact zero_ne_one h'
  have hJ : ∀ a b, a ≠ b → J a ≠ J b := fun a b hab h => by
    have h' := congrArg Fin.val h
    exact hab (Fin.ext h')
  let I : Fin 4 → Fin 5 := fun a => ⟨a.val, by omega⟩
  have hI : ∀ a b, a ≠ b → I a ≠ I b := fun a b hab h => by
    have h' := congrArg Fin.val h
    exact hab (Fin.ext h')
  let t4 : Fin 5 := ⟨4, by omega⟩
  have hIt : ∀ a, t4 ≠ I a := fun a h => by
    have h' := congrArg Fin.val h
    simp only [t4, I] at h'
    omega
  have h := RootData.three_witness_pairs (R := rootData n hn K) hchar (F := F)
    (X := fun a => intMap K (M (I a))) (Y := fun a => intMap K (N (I a)))
    (fun a => hpair (I a)) (fun a => hne (I a)) (fun a => gM (I a)) (fun a => gN (I a))
    (fun a => hgM' (I a)) (fun a => hgN' (I a)) (fun a => hgMD (I a)) (fun a => hgND (I a))
    (fun a b _ => hcomm (hM _) (hM _) (zSS (twV_cr (hJB _)) (twV_cr (hJB _))))
    (fun a b hab => hcomm (hM _) (hN _)
      (zST hv2 (hJ _ _ (hI a b hab)) (twV_cr (hJB _)) (twV_an (hJB _))))
    (fun a b _ => hcomm (hN _) (hN _) (zTT (twV_an (hJB _)) (twV_an (hJB _)))) (gM t4)
    (hgMD t4) ?_ ?_
    (fun a => (rootData n hn K).commute_of_mat (by
      rw [hgM, hgM]
      exact commute_one_add_smul (hcomm (hM t4) (hM (I a))
        (zSS (twV_cr (hJB _)) (twV_cr (hJB _)))) 1 1))
    (fun a => (rootData n hn K).commute_of_mat (by
      rw [hgM, hgN]
      exact commute_one_add_smul (hcomm (hM t4) (hN (I a))
        (zST hv2 (hJ _ _ (hIt a)) (twV_cr (hJB _)) (twV_an (hJB _)))) 1 1))
  · rwa [Fintype.card_fin] at h
  · apply (rootData n hn K).mat_injective
    have hXX : intMap K (M t4) + intMap K (M t4) = 0 := by
      nth_rewrite 1 [← hneg (intMap K (M t4))]
      exact neg_add_cancel _
    rw [pow_two, mat_mul, hgM', mat_one, mul_add, mul_one, add_mul, one_mul, (hMR t4).sq,
      add_zero, add_assoc, hXX, add_zero]
  · refine ⟨gN t4, hgND t4, fun h => hne t4 ?_⟩
    have hm := congrArg (rootData n hn K).mat h
    rw [mat_mul, mat_mul, hgM', hgN'] at hm
    have hXY : intMap K (M t4) * intMap K (N t4) = intMap K (N t4) * intMap K (M t4) := by
      have e1 : intMap K (M t4) * intMap K (N t4) =
          (1 + intMap K (M t4)) * (1 + intMap K (N t4)) - 1 - intMap K (M t4) -
            intMap K (N t4) := by noncomm_ring
      have e2 : intMap K (N t4) * intMap K (M t4) =
          (1 + intMap K (N t4)) * (1 + intMap K (M t4)) - 1 - intMap K (M t4) -
            intMap K (N t4) := by noncomm_ring
      rw [e1, e2, hm]
    calc intMap K (M t4) = intMap K (M t4) * intMap K (N t4) * intMap K (M t4) :=
          (hpair t4).efe.symm
      _ = intMap K (M t4) * intMap K (M t4) * intMap K (N t4) := by
          rw [mul_assoc, ← hXY, mul_assoc]
      _ = 0 := by rw [(hpair t4).ee, zero_mul]

end Generic

variable (d : TypeTwistedDLieIndex)

theorem hasWitness_twShort (h2 : d.1.characteristic = 2) (h6 : 6 ≤ d.1.rank) :
    HasWitness d.Group 3 4 := by
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  have hcard := card_fixedField2 d
  have hf : 0 < d.1.fieldExponent := d.1.1.fieldExponent_pos
  have : Finite (fixedField2 d) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ d.1.characteristic_prime.ne_zero)
  have h4 : 4 ≤ Nat.card (fixedField2 d) := by
    rw [hcard, h2]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * d.1.fieldExponent) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨μ, hμL, hμ1⟩ := exists_unit_sq_ne_one (fixedField2 d) h4
  exact hasWitness_twShort_gen (isTwistedFrobenius d) (fun i hi => perm_of_lt d hi)
    (perm_forkA d) (perm_forkB d) hμL hμ1 hchar h6

end CarrierTD

end CFSG.RankThree.PartTwo.Census.Spin
