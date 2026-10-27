module

public import CFSG.Timmesfeld.Transvection.GenerateFrameMain
public import CFSG.Timmesfeld.Transvection.Small

public section

open CFSG.LieType.Universal.Unitary

namespace CFSG.LieType.Universal.Unitary

theorem lowIdx_swap {n : ℕ} (j j' b : Fin (n / 2)) :
    lowIdx (Equiv.swap j j' b) = Equiv.swap (lowIdx j) (lowIdx j') (lowIdx b) := by
  ext
  simp only [lowIdx, val_swap_apply]

end CFSG.LieType.Universal.Unitary

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.BorelTits CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.Steinberg CFSG.Timmesfeld.Transvection.Pres

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

namespace IsMaxFrame


theorem exists_cPart (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hr : 2 ≤ r) (hF : IsMaxFrame Δ P Q) :
    ∃ f, 2 ≤ f ∧ (∀ A ∈ Δ, Nat.card A = 2 ^ f) ∧
      ((∃ R : SpRelations r (GaloisField 2 f) H, R.HasFrameImages Δ P Q) ∨
        ∃ R : SURelations r (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) H,
          R.HasFrameImages Δ P Q) := by
  haveI : Finite H := h.finite
  let i₀ : Fin r := ⟨0, by omega⟩
  have hPi₀ : P i₀ ∈ Δ := hF.memP i₀
  obtain ⟨f, hf, hcard₀, -⟩ :=
    Opposite.exists_mulEquiv_SL2 h.cls.root hPi₀ (hF.opposite i₀) (hq _ hPi₀)
  have hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ f := fun A hA =>
    (h.cls.root.card_eq hA hPi₀).trans hcard₀
  refine ⟨f, hf, hcard, ?_⟩
  exact hF.exists_relations_hasFrameImages h.cls h.points
    (h.cls.noIsolated h.points h.rank) hML
    (thickLines_of_meetsLines h.cls h.center hML) hf hcard hr

end IsMaxFrame

private theorem levelPerm_crd {n : ℕ} {j : Fin (n / 2)}
    (hj : j.val + 1 < n / 2) (a : Fin (n / 2) ⊕ Fin (n / 2)) :
    levelPerm j (crd a) =
      crd (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩) (Equiv.swap j ⟨j.val + 1, hj⟩) a) := by
  have hL : ∀ b : Fin (n / 2),
      levelPerm j (lowIdx b) = lowIdx (Equiv.swap j ⟨j.val + 1, hj⟩ b) := by
    intro b
    rw [levelPerm, dite_eq_left hj, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (lowIdx_ne_rev b j) (lowIdx_ne_rev b _), lowIdx_swap]
  rcases a with b | b
  · rw [crd_inl, Sum.map_inl, crd_inl, hL]
  · rw [crd_inr, Sum.map_inr, crd_inr, levelPerm_rev, hL]

private theorem levelSign_eq_one {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {n : ℕ}
    {j : Fin (n / 2)} (hj : j.val + 1 < n / 2) (ζ : traceZero σ) (s : Fin n) :
    levelSign σ (ζ : F) j s = 1 := by
  rw [levelSign, dite_eq_left hj]
  simp only [shortSign]
  split_ifs <;> simp [CharTwo.neg_eq]

theorem levelWeyl_conj_suLong {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) {m : ℕ} {j : Fin (m / 2)} (hj : j.val + 1 < m / 2)
    (a : Fin (m / 2) ⊕ Fin (m / 2)) (c : F) :
    levelWeyl hσ ζ j * suLong σ a c * (levelWeyl hσ ζ j)⁻¹ =
      suLong σ (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
        (Equiv.swap j ⟨j.val + 1, hj⟩) a) c := by
  by_cases hc : c + σ c = 0
  · rw [mul_inv_eq_iff_eq_mul]
    apply mat_injective
    rw [map_mul, map_mul, mat_apply, coe_levelWeyl hσ hζ j, mat_suLong a hc, crd_swap a,
      mat_suLong (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
        (Equiv.swap j ⟨j.val + 1, hj⟩) a) hc, crd_swap]
    change signedPerm (levelPerm j) (levelSign σ (ζ : F) j) * longRootMatrix (crd a) c =
      longRootMatrix (crd (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
        (Equiv.swap j ⟨j.val + 1, hj⟩) a)) c *
        signedPerm (levelPerm j) (levelSign σ (ζ : F) j)
    rw [signedPerm_mul_longRootMatrix (levelPerm_rev j) (levelSign_unitary hσ hζ j)]
    have hπ : levelPerm j (crd a) = crd (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
        (Equiv.swap j ⟨j.val + 1, hj⟩) a) := levelPerm_crd hj a
    have hd : levelSign σ (ζ : F) j (crd a) * c *
        (levelSign σ (ζ : F) j (Fin.rev (crd a)))⁻¹ = c := by
      rw [levelSign_eq_one hj ζ (crd a), levelSign_eq_one hj ζ (Fin.rev (crd a)),
        inv_one, mul_one, one_mul]
    rw [hπ, hd]
  · simp [suLong, hc]

namespace SURelations

variable
  {m : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2) (he : Even m) (hm : 4 ≤ m)
  (R : SURelations (m / 2) (unitaryInvolution F 2 n) H)

@[expose] noncomputable def lastBlock : SU (unitaryInvolution F 2 n) 2 →* H :=
  (R.toHom hFn he hm).comp
    (((CurtisTits.rankOne (Unitary.rootGroup (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) m) ⟨m / 2 - 1, by omega⟩).subtype).comp
      (rankOneLastEvenEquiv hFn he (by simp only [Fin.val_mk]; omega)).symm.toMonoidHom)

theorem lastBlock_suLong_inl {c : F} (hc : unitaryInvolution F 2 n c = c) :
    R.lastBlock hFn he hm (suLong (unitaryInvolution F 2 n) (Sum.inl 0) c) =
      R.ξL (Sum.inl (⟨m / 2 - 1,
        Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
          Nat.zero_lt_one⟩ : Fin (m / 2))) c := by
  let k : Fin (m / 2) := ⟨m / 2 - 1, by omega⟩
  have hk : ¬ k.val + 1 < m / 2 := by
    dsimp only [k]
    omega
  have hmem : suLong (unitaryInvolution F 2 n) (Sum.inl k) c ∈
      CurtisTits.rankOne (Unitary.rootGroup (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) m) k :=
    Subgroup.mem_sup_left (suLong_mem (unitaryInvolution_involutive hFn) (Sum.inl k)
      (toStd_single_last_even hk he) c)
  have hc' : c + unitaryInvolution F 2 n c = 0 := by
    rw [hc, CharTwo.add_self_eq_zero]
  have hblock : rankOneLastEvenEquiv hFn he hk
      ⟨suLong (unitaryInvolution F 2 n) (Sum.inl k) c, hmem⟩ =
      suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) c := by
    apply mat_injective
    rw [mat_rankOneLastEvenEquiv, toBlock_eq_submatrix, mat_suLong (Sum.inl k) hc',
      crd_swap, mat_suLong (Sum.inl (0 : Fin (2 / 2))) hc', crd_swap]
    change (longRootMatrix (lastIdxEven k 0) c).submatrix (lastIdxEven k) (lastIdxEven k) =
      longRootMatrix (0 : Fin 2) c
    rw [submatrix_longRootMatrix lastIdxEven_injective lastIdxEven_rev rfl]
  have hsymm : ((rankOneLastEvenEquiv hFn he hk).symm
      (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) c) :
        SU (unitaryInvolution F 2 n) m) =
      suLong (unitaryInvolution F 2 n) (Sum.inl k) c := by
    rw [← hblock, MulEquiv.symm_apply_apply]
  change R.toHom hFn he hm
      ↑((rankOneLastEvenEquiv hFn he hk).symm
        (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) c)) = _
  rw [hsymm, R.toHom_suLong hFn he hm (Sum.inl k) hc]

theorem lastBlock_suLong_inr {c : F} (hc : unitaryInvolution F 2 n c = c) :
    R.lastBlock hFn he hm (suLong (unitaryInvolution F 2 n) (Sum.inr 0) c) =
      R.ξL (Sum.inr (⟨m / 2 - 1,
        Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
          Nat.zero_lt_one⟩ : Fin (m / 2))) c := by
  let k : Fin (m / 2) := ⟨m / 2 - 1, by omega⟩
  have hk : ¬ k.val + 1 < m / 2 := by
    dsimp only [k]
    omega
  have hmem : suLong (unitaryInvolution F 2 n) (Sum.inr k) c ∈
      CurtisTits.rankOne (Unitary.rootGroup (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) m) k :=
    Subgroup.mem_sup_right (suLong_mem (unitaryInvolution_involutive hFn) (Sum.inr k)
      (toStd_neg_single_last he hk) c)
  have hc' : c + unitaryInvolution F 2 n c = 0 := by
    rw [hc, CharTwo.add_self_eq_zero]
  have hblock : rankOneLastEvenEquiv hFn he hk
      ⟨suLong (unitaryInvolution F 2 n) (Sum.inr k) c, hmem⟩ =
      suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) c := by
    apply mat_injective
    rw [mat_rankOneLastEvenEquiv, toBlock_eq_submatrix, mat_suLong (Sum.inr k) hc',
      crd_swap, crd_inr, Fin.rev_rev, mat_suLong (Sum.inr (0 : Fin (2 / 2))) hc',
      crd_swap, crd_inr, Fin.rev_rev]
    change (1 + Matrix.single (lastIdxEven k 1) (lastIdxEven k 0) c).submatrix
        (lastIdxEven k) (lastIdxEven k) = 1 + Matrix.single (1 : Fin 2) (0 : Fin 2) c
    have h01 : lastIdxEven k 0 ≠ lastIdxEven k 1 := by
      simpa [lastIdxEven] using lowIdx_ne_rev k k
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        lastIdxEven, h01, h01.symm, lowIdx_ne_rev k k, (lowIdx_ne_rev k k).symm]
  have hsymm : ((rankOneLastEvenEquiv hFn he hk).symm
      (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) c) :
        SU (unitaryInvolution F 2 n) m) =
      suLong (unitaryInvolution F 2 n) (Sum.inr k) c := by
    rw [← hblock, MulEquiv.symm_apply_apply]
  change R.toHom hFn he hm
      ↑((rankOneLastEvenEquiv hFn he hk).symm
        (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) c)) = _
  rw [hsymm, R.toHom_suLong hFn he hm (Sum.inr k) hc]

end SURelations

namespace SURelations.HasFrameImages

variable
  {m : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2) (he : Even m) (hm : 4 ≤ m)
  (R : SURelations (m / 2) (unitaryInvolution F 2 n) H)

private theorem conj_ξL_levelWeyl {ζ : traceZero (unitaryInvolution F 2 n)}
    (hζ : (ζ : F) ≠ 0) {j : Fin (m / 2)} (hj : j.val + 1 < m / 2)
    (a : Fin (m / 2) ⊕ Fin (m / 2)) {c : F} (hc : unitaryInvolution F 2 n c = c) :
    R.toHom hFn he hm (levelWeyl (unitaryInvolution_involutive hFn) ζ j) * R.ξL a c *
        (R.toHom hFn he hm (levelWeyl (unitaryInvolution_involutive hFn) ζ j))⁻¹ =
      R.ξL (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
        (Equiv.swap j ⟨j.val + 1, hj⟩) a) c := by
  rw [← R.toHom_suLong hFn he hm a hc, ← map_inv, ← map_mul, ← map_mul]
  rw [levelWeyl_conj_suLong (unitaryInvolution_involutive hFn) hζ hj a c,
    R.toHom_suLong hFn he hm _ hc]

private theorem conjSub_framePt_levelWeyl {P Q : Fin (m / 2) → Subgroup H}
    (hR : R.HasFrameImages Δ P Q) {ζ : traceZero (unitaryInvolution F 2 n)}
    (hζ : (ζ : F) ≠ 0) {j : Fin (m / 2)} (hj : j.val + 1 < m / 2)
    (a : Fin (m / 2) ⊕ Fin (m / 2)) :
    conjSub (framePt P Q a)
        (R.toHom hFn he hm (levelWeyl (unitaryInvolution_involutive hFn) ζ j)) =
      framePt P Q (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
        (Equiv.swap j ⟨j.val + 1, hj⟩) a) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (hR.long a y).1 hy
    exact (hR.long (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
        (Equiv.swap j ⟨j.val + 1, hj⟩) a) _).2
      ⟨c, hc, (conj_ξL_levelWeyl hFn he hm R hζ hj a hc).symm⟩
  · intro hx
    obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.map (Equiv.swap j ⟨j.val + 1, hj⟩)
      (Equiv.swap j ⟨j.val + 1, hj⟩) a) x).1 hx
    exact ⟨R.ξL a c, (hR.long a (R.ξL a c)).2 ⟨c, hc, rfl⟩,
      conj_ξL_levelWeyl hFn he hm R hζ hj a hc⟩

theorem conjSub_levelWeyl {P Q : Fin (m / 2) → Subgroup H}
    (hR : R.HasFrameImages Δ P Q) {ζ : traceZero (unitaryInvolution F 2 n)}
    (hζ : (ζ : F) ≠ 0) {j : Fin (m / 2)} (hj : j.val + 1 < m / 2) (i : Fin (m / 2)) :
    conjSub (P i) (R.toHom hFn he hm (levelWeyl (unitaryInvolution_involutive hFn) ζ j)) =
        P (Equiv.swap j ⟨j.val + 1, hj⟩ i) ∧
      conjSub (Q i) (R.toHom hFn he hm (levelWeyl (unitaryInvolution_involutive hFn) ζ j)) =
        Q (Equiv.swap j ⟨j.val + 1, hj⟩ i) := by
  constructor
  · simpa using conjSub_framePt_levelWeyl hFn he hm R hR hζ hj (Sum.inl i)
  · simpa using conjSub_framePt_levelWeyl hFn he hm R hR hζ hj (Sum.inr i)

end SURelations.HasFrameImages

end CFSG.Timmesfeld.Transvection
