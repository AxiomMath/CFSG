module

public import CFSG.Quasithin.Background.SmithB42G2TenZorn

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.QuasithinUnique.Setup.X7
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.B42G2Id

section Eigen

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

open Classical in
@[expose] def eigval (ρ : Representation k G V) (y : V) (g : G) : k :=
  if h : ∃ c : k, ρ g y = c • y then h.choose else 0

theorem eigval_spec {ρ : Representation k G V} {y : V} (hy : y ≠ 0) {g : G} {c : k}
    (h : ρ g y = c • y) : eigval ρ y g = c := by
  unfold eigval
  split_ifs with hex
  · exact smul_left_injective k hy (hex.choose_spec.symm.trans h)
  · exact absurd ⟨c, h⟩ hex

end Eigen

section Exponents

variable {f : ℕ}

theorem eExp_eq_mBits (lab : Fin f → G2L) (i : Fin 2) :
    eExp lab i = mBits fun j => decide (i ∈ (lab j).roots) := by
  simp only [eExp, mBits, decide_eq_true_eq]

theorem eExp_lt (lab : Fin f → G2L) (i : Fin 2) : eExp lab i < 2 ^ f := by
  rw [eExp_eq_mBits]
  exact mBits_lt _

theorem forall_mem_roots_iff (lab : Fin f → G2L) (i : Fin 2) :
    (∀ j, i ∈ (lab j).roots) ↔ eExp lab i = 2 ^ f - 1 := by
  rw [eExp_eq_mBits]
  constructor
  · intro h
    have e : (fun j => decide (i ∈ (lab j).roots)) = ones f :=
      funext fun j => by simp [ones, h j]
    rw [e, mBits_ones]
  · intro h j
    simpa [ones] using congrFun (eq_ones_of_mBits h) j

theorem G2L.eq_of_roots {l l' : G2L} (h : ∀ i, i ∈ l.roots ↔ i ∈ l'.roots) : l = l' := by
  have h0 := h 0
  have h1 := h 1
  cases l <;> cases l' <;> first | rfl | (exfalso; revert h0 h1; decide)

theorem eExp_injective {lab lab' : Fin f → G2L} (h : ∀ i, eExp lab i = eExp lab' i) :
    lab = lab' := by
  funext j
  refine G2L.eq_of_roots fun i => ?_
  have hb : (fun j => decide (i ∈ (lab j).roots)) = fun j => decide (i ∈ (lab' j).roots) :=
    mBits_injective (by rw [← eExp_eq_mBits, ← eExp_eq_mBits, h i])
  simpa only [decide_eq_decide] using congrFun hb j

theorem two_pow_sub_one_ne_zero {K : Type*} [Field K] [Fintype K]
    (hK : Fintype.card K = 2 ^ f) : 2 ^ f - 1 ≠ 0 := by
  have h := Fintype.one_lt_card (α := K)
  rw [hK] at h
  exact Nat.sub_ne_zero_of_lt h

variable {K k : Type*} [Field K] [Fintype K] [Field k] [Algebra K k]

theorem forall_pow_eq_one_iff (hK : Fintype.card K = 2 ^ f) {e : ℕ} (he : e < 2 ^ f) :
    (∀ t : Kˣ, algebraMap K k (t : K) ^ e = 1) ↔ e = 0 ∨ e = 2 ^ f - 1 := by
  constructor
  · intro h
    have h' : ∀ z : Kˣ, z ^ e = z ^ 0 := fun z => by
      rw [pow_zero]
      refine Units.ext ((algebraMap K k).injective ?_)
      rw [Units.val_pow_eq_pow_val, map_pow, h z, Units.val_one, map_one]
    rcases torus_weight_eq hK he (by positivity) h' with h1 | ⟨h1, -⟩ | ⟨-, h1⟩
    · exact Or.inl h1
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (rfl | rfl) t
    · rw [pow_zero]
    · rw [← map_pow, ← hK, FiniteField.pow_card_sub_one_eq_one _ t.ne_zero, map_one]

theorem eExp_eq_of_pow (hK : Fintype.card K = 2 ^ f) {lab lab' : Fin f → G2L} {i : Fin 2}
    (hpow : ∀ t : Kˣ, algebraMap K k (t : K) ^ eExp lab i = algebraMap K k (t : K) ^ eExp lab' i)
    (h0 : eExp lab i = 0 → eExp lab' i ≠ 2 ^ f - 1)
    (h1 : eExp lab' i = 0 → eExp lab i ≠ 2 ^ f - 1) : eExp lab i = eExp lab' i := by
  have hz : ∀ z : Kˣ, z ^ eExp lab i = z ^ eExp lab' i := fun z =>
    Units.ext ((algebraMap K k).injective (by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, hpow z]))
  rcases torus_weight_eq hK (eExp_lt lab i) (eExp_lt lab' i) hz with h | ⟨ha, hb⟩ | ⟨hb, ha⟩
  · exact h
  · exact absurd hb (h0 ha)
  · exact absurd ha (h1 hb)

end Exponents

section Distinct

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {k : Type} [Field k] [Algebra K k]
  [CharP k 2] {f : ℕ}

theorem tRep_iso_iff_eq (hK : Fintype.card K = 2 ^ f) (lab lab' : Fin f → G2L) :
    (∃ β : (TIdx lab → k) ≃ₗ[k] (TIdx lab' → k), ∀ (g : ↥(cayleyGroup K)) (v : TIdx lab → k),
      β (matRep (tRep K k lab) g v) = matRep (tRep K k lab') g (β v)) ↔ lab = lab' := by
  constructor
  · rintro ⟨β, hβ⟩
    have hy : tHwZ K k lab ∈ SmithCurtis.fixSub (matRep (tRep K k lab)) (Uz K) := by
      rw [fixSub_zPos_tRep K k hK lab]
      exact Submodule.mem_span_singleton_self _
    have hfix : β (tHwZ K k lab) ∈ SmithCurtis.fixSub (matRep (tRep K k lab')) (Uz K) :=
      fun u hu => by rw [← hβ, hy u hu]
    rw [fixSub_zPos_tRep K k hK lab', Submodule.mem_span_singleton] at hfix
    obtain ⟨c, hc⟩ := hfix
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact tHwZ_ne_zero K k lab (β.injective (by rw [← hc, map_zero]))
    have key : ∀ (a a' : k) (A : (TIdx lab → k) →ₗ[k] (TIdx lab → k))
        (A' : (TIdx lab' → k) →ₗ[k] (TIdx lab' → k)), (∀ v, β (A v) = A' (β v)) →
        A (tHwZ K k lab) = a • tHwZ K k lab → A' (tHwZ K k lab') = a' • tHwZ K k lab' →
          a = a' := by
      intro a a' A A' hA ha ha'
      have e := hA (tHwZ K k lab)
      rw [ha, map_smul, ← hc, map_smul, ha', smul_smul, smul_smul] at e
      exact mul_right_cancel₀ hc0
        ((smul_left_injective k (tHwZ_ne_zero K k lab') e).trans (mul_comm c a'))
    have hpow : ∀ (i : Fin 2) (t : Kˣ), algebraMap K k (t : K) ^ eExp lab i =
        algebraMap K k (t : K) ^ eExp lab' i := fun i t =>
      key _ _ _ _ (hβ _) (rankOne_tRep' K k lab i t) (rankOne_tRep' K k lab' i t)
    have hhecke : ∀ i : Fin 2, (∀ j, i ∈ (lab j).roots) ↔ ∀ j, i ∈ (lab' j).roots := by
      intro i
      have h := key _ _ (∑ c : K, matRep (tRep K k lab) (zPsi (Pi.single i 1) c * zW K i))
        (∑ c : K, matRep (tRep K k lab') (zPsi (Pi.single i 1) c * zW K i))
        (fun v => by simp only [LinearMap.sum_apply, map_sum, hβ])
        (by rw [LinearMap.sum_apply]; exact hecke_tRep K k hK lab i)
        (by rw [LinearMap.sum_apply]; exact hecke_tRep K k hK lab' i)
      by_cases h1 : ∀ j, i ∈ (lab j).roots <;> by_cases h2 : ∀ j, i ∈ (lab' j).roots
      · exact iff_of_true h1 h2
      · rw [ite_eq_left h1, ite_eq_right h2] at h
        exact absurd h one_ne_zero
      · rw [ite_eq_right h1, ite_eq_left h2] at h
        exact absurd h zero_ne_one
      · exact iff_of_false h1 h2
    have hq := two_pow_sub_one_ne_zero hK
    refine eExp_injective fun i => eExp_eq_of_pow (k := k) hK (hpow i) (fun ha hb => ?_)
      (fun ha hb => ?_)
    · have h2 : eExp lab i = 2 ^ f - 1 :=
        (forall_mem_roots_iff lab i).mp ((hhecke i).mpr ((forall_mem_roots_iff lab' i).mpr hb))
      exact hq (h2.symm.trans ha)
    · have h2 : eExp lab' i = 2 ^ f - 1 :=
        (forall_mem_roots_iff lab' i).mp ((hhecke i).mp ((forall_mem_roots_iff lab i).mpr hb))
      exact hq (h2.symm.trans ha)
  · rintro rfl
    exact ⟨LinearEquiv.refl k _, fun g v => rfl⟩

theorem eq_of_tRep_equiv (hK : Fintype.card K = 2 ^ f) {lab lab' : Fin f → G2L}
    (e : (matRep (tRep K k lab)).Equiv (matRep (tRep K k lab'))) : lab = lab' :=
  (tRep_iso_iff_eq hK lab lab').mp
    ⟨e.toLinearEquiv, fun g v =>
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v⟩

end Distinct

section Frob

variable {K : Type} [Field K] [Fintype K] [CharP K 2] (k : Type) [Field k] [Algebra K k]
  [CharP k 2] {f : ℕ}

omit [CharP K 2] in
theorem frK_add_mul (hK : Fintype.card K = 2 ^ f) (i m : ℕ) (z : K) :
    frK k (i + f * m) z = frK k i z := by
  induction m with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ m ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, frK_apply, pow_add, mul_comm, pow_mul, ← map_pow, ← hK,
      FiniteField.pow_card, ← frK_apply, ih]

omit [CharP K 2] in
theorem frK_mod (hK : Fintype.card K = 2 ^ f) (n : ℕ) (z : K) :
    frK k n z = frK k (n % f) z := by
  conv_lhs => rw [← Nat.mod_add_div n f]
  exact frK_add_mul k hK _ _ z

omit [Fintype K] [CharP K 2] in
theorem iterateFrobenius_frK (d j : ℕ) (z : K) :
    iterateFrobenius k 2 d (frK k j z) = frK k (j + d) z := by
  rw [iterateFrobenius_def, frK_apply, frK_apply, ← pow_mul, ← pow_add]

omit [Field K] [Fintype K] [CharP K 2] [Field k] [Algebra K k] [CharP k 2] in
theorem val_finRotate (j : Fin f) : ((finRotate f j : Fin f) : ℕ) = ((j : ℕ) + 1) % f := by
  cases f with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h
      simp
    · have : (j : ℕ) + 1 < n + 1 := by
        have := Fin.val_lt_last h
        omega
      rw [Nat.mod_eq_of_lt this]

omit [Field K] [Fintype K] [CharP K 2] [Field k] [Algebra K k] [CharP k 2] in
theorem val_finRotate_pow (d : ℕ) (j : Fin f) :
    (((finRotate f ^ d) j : Fin f) : ℕ) = ((j : ℕ) + d) % f := by
  induction d with
  | zero => rw [pow_zero, Equiv.Perm.one_apply, Nat.add_zero, Nat.mod_eq_of_lt j.2]
  | succ d ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, val_finRotate, ih, Nat.mod_add_mod, Nat.add_assoc]

theorem tRep_map_frob (hK : Fintype.card K = 2 ^ f) (lab : Fin f → G2L) (d : ℕ) :
    ∃ (P : Matrix (TIdx (lab ∘ ⇑(finRotate f ^ d).symm)) (TIdx lab) k)
      (Q : Matrix (TIdx lab) (TIdx (lab ∘ ⇑(finRotate f ^ d).symm)) k),
      MatIso (matMap (iterateFrobenius k 2 d) (tRep K k lab))
        (tRep K k (lab ∘ ⇑(finRotate f ^ d).symm)) P Q := by
  refine ⟨_, _, matIso_of_reindex (Equiv.piCongrLeft' (fun j => (lab j).idx) (finRotate f ^ d))
    fun g x' x => ?_⟩
  show ∏ j, frK k ((j : Fin f) : ℕ) ((lab ((finRotate f ^ d).symm j)).rep g
      (x' ((finRotate f ^ d).symm j)) (x ((finRotate f ^ d).symm j))) =
    iterateFrobenius k 2 d (∏ j, frK k ((j : Fin f) : ℕ) ((lab j).rep g (x' j) (x j)))
  rw [map_prod]
  refine Fintype.prod_equiv (finRotate f ^ d).symm _ _ fun j => ?_
  rw [iterateFrobenius_frK, frK_mod k hK (((finRotate f ^ d).symm j : Fin f) + d),
    ← val_finRotate_pow, Equiv.apply_symm_apply]

theorem tRep_map_frob_equiv (hK : Fintype.card K = 2 ^ f) (lab : Fin f → G2L) (d : ℕ) :
    Nonempty ((matRep (matMap (iterateFrobenius k 2 d) (tRep K k lab))).Equiv
      (matRep (tRep K k (lab ∘ ⇑(finRotate f ^ d).symm)))) := by
  obtain ⟨P, Q, h⟩ := tRep_map_frob k hK lab d
  exact h.equiv

theorem lab_comp_finRotate_pow (hK : Fintype.card K = 2 ^ f) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : ↥(cayleyGroup K) →* Matrix ι ι k) (d : ℕ)
    (hR : ∀ g, (R g).map (iterateFrobenius k 2 d) = R g) {lab : Fin f → G2L}
    (β : (ι → k) ≃ₗ[k] (TIdx lab → k))
    (hβ : ∀ g v, β (matRep R g v) = matRep (tRep K k lab) g (β v)) :
    lab ∘ ⇑(finRotate f ^ d) = lab := by
  obtain ⟨P, Q, h⟩ := MatIso.exists_of_equiv
    (Representation.Equiv.mk β fun g => LinearMap.ext fun v => hβ g v)
  have hR' : matMap (iterateFrobenius k 2 d) R = R := MonoidHom.ext hR
  have h1 := h.map (iterateFrobenius k 2 d)
  rw [hR'] at h1
  obtain ⟨P', Q', h2⟩ := tRep_map_frob k hK lab d
  obtain ⟨e⟩ := (h.symm.trans (h1.trans h2)).equiv
  have he := eq_of_tRep_equiv hK e
  funext j
  have h3 := congrFun he ((finRotate f ^ d) j)
  rw [Function.comp_apply, Equiv.symm_apply_apply] at h3
  exact h3

end Frob

end CFSG.Quasithin.B42G2Ten
