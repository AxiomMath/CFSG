module

public import CFSG.Sporadic.Schreier.Co1WeightStab

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix CFSG.Blueprint CFSG.Sporadic.Mathieu

theorem exists_plane_decomp
    (w : Vec24) : ∃ u : Fin 12 → Vec24, (∀ k, u k ∈ plane k) ∧
    w = ∑ k, u k := by
  have hw : w ∈ Submodule.span (ZMod 2)
      (Set.range fun p : Fin 12 × Fin 2 => (zM ^ p.2.val) *ᵥ q p.1) := by
    rw [span_q]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hw
  refine ⟨fun k => ∑ e : Fin 2, c (k, e) • ((zM ^ e.val) *ᵥ q k), fun k => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ ?_
    exact zM_pow_mulVec_mem_plane (q_mem_plane k) _
  · rw [← hc, Fintype.sum_prod_type]

theorem plane_decomp_unique
    {u u' : Fin 12 → Vec24} (hu : ∀ k, u k ∈ plane k)
    (hu' : ∀ k, u' k ∈ plane k) (h : ∑ k, u k = ∑ k, u' k) : ∀ k, u k = u' k := by
  choose α β hαβ using fun k => Submodule.mem_span_pair.mp (hu k)
  choose α' β' hαβ' using fun k => Submodule.mem_span_pair.mp (hu' k)
  have hli := linearIndependent_q
  rw [Fintype.linearIndependent_iffₛ] at hli
  have hsum : ∀ (x y : Fin 12 → ZMod 2) (w : Fin 12 → Vec24),
      (∀ k, x k • q k + y k • zM *ᵥ q k = w k) →
      ∑ p : Fin 12 × Fin 2, (fun p => if p.2 = 0 then x p.1 else y p.1) p •
        ((zM ^ p.2.val) *ᵥ q p.1) = ∑ k, w k := by
    intro x y w hw
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_two, ← hw k]
    simp
  have h0 := hli _ _ ((hsum α β u hαβ).trans (h.trans (hsum α' β' u' hαβ').symm))
  intro k
  rw [← hαβ k, ← hαβ' k]
  have h1 := h0 (k, 0)
  have h2 := h0 (k, 1)
  simp only [↓reduceIte, one_ne_zero] at h1 h2
  rw [h1, h2]

theorem mem_plane_of_eigen
    {j : Fin 12} {w : Vec24}
    (h : ∀ i, ((a i : GL24) : Mat24) *ᵥ w = (zM ^ (γ j i).val) *ᵥ w) : w ∈ plane j := by
  obtain ⟨u, hu, rfl⟩ := exists_plane_decomp w
  have hcomp : ∀ i, ∀ k, (zM ^ (γ k i).val) *ᵥ u k = (zM ^ (γ j i).val) *ᵥ u k := by
    intro i
    refine plane_decomp_unique (fun k => zM_pow_mulVec_mem_plane (hu k) _)
      (fun k => zM_pow_mulVec_mem_plane (hu k) _) ?_
    have := h i
    rw [mulVec_sum, mulVec_sum] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => (a_mulVec_plane i (hu k)).symm
  have hzero : ∀ k, k ≠ j → u k = 0 := by
    intro k hk
    obtain ⟨i, hi⟩ : ∃ i, γ k i ≠ γ j i := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      exact hk (γ_injective (funext hne))
    by_contra hne
    exact hi (ZMod.val_injective _ (zM_pow_inj hne (ZMod.val_lt _) (ZMod.val_lt _) (hcomp i k)))
  rw [Finset.sum_eq_single j (fun k _ hk => hzero k hk) (fun h => absurd (Finset.mem_univ _) h)]
  exact hu j

theorem nonzero_plane_eq
    {j : Fin 12} {v : Vec24} (hv : v ∈ plane j) (hv0 : v ≠ 0) :
    ∃ e : ZMod 3, v = (zM ^ e.val) *ᵥ q j := by
  obtain ⟨m, hm⟩ := exists_zM_pow_eq_q hv hv0
  have h3 : ∀ n : ℕ, zM ^ n = zM ^ (n % 3) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, zM_cube, one_pow, one_mul]
  refine ⟨((2 * m : ℕ) : ZMod 3), ?_⟩
  rw [ZMod.val_natCast, ← h3, ← hm, mulVec_mulVec, ← pow_add,
    show 2 * m + m = 3 * m by ring, pow_mul, zM_cube, one_pow, one_mulVec]

theorem zM_pow_cancel
    (n : ℕ) {x y : Vec24} (h : (zM ^ n) *ᵥ x = (zM ^ n) *ᵥ y) : x = y := by
  have h1 : (zM ^ (2 * n)) *ᵥ ((zM ^ n) *ᵥ x) = (zM ^ (2 * n)) *ᵥ ((zM ^ n) *ᵥ y) := by rw [h]
  rwa [mulVec_mulVec, mulVec_mulVec, ← pow_add, show 2 * n + n = 3 * n by ring, pow_mul, zM_cube,
    one_pow, one_mulVec, one_mulVec] at h1

theorem lines_transitive
    (j : Fin 12) : ∃ c ∈ C, (msData ((c : GL24) : Mat24)).1 0 = j := by
  have h2 := isMultiplyPretransitive_two m12_hyp (by decide) (by norm_num)
  have : MulAction.IsPretransitive NativeSporadic.M12 (Fin 12) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq NativeSporadic.M12 (coordBij⁻¹ 0) (coordBij⁻¹ j)
  have hm : MulAut.conj coordBij (n : Equiv.Perm (Fin 12)) ∈ cPerm.range := by
    rw [cPerm_range']
    exact Subgroup.mem_map_of_mem _ n.2
  obtain ⟨c, hc⟩ := hm
  refine ⟨c, c.2, ?_⟩
  rw [← cPerm_apply, hc, MulAut.conj_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [Subgroup.smul_def, Equiv.Perm.smul_def] at hn
  rw [hn]
  exact Equiv.apply_symm_apply coordBij j


theorem end_A
    {T : Mat24} (hT : ∀ x ∈ A, T * ((x : GL24) : Mat24) = ((x : GL24) : Mat24) * T) :
    T = 0 ∨ T = 1 := by
  have hz : T * zM = zM * T := by
    have := hT _ (a_mem_A 0)
    rwa [a_zero] at this
  have hzn : ∀ n : ℕ, T * zM ^ n = zM ^ n * T := by
    intro n
    induction n with
    | zero => rw [pow_zero, mul_one, one_mul]
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hz, ← mul_assoc]
  have hzpow : ∀ (n : ℕ) (v : Vec24), T *ᵥ ((zM ^ n) *ᵥ v) = (zM ^ n) *ᵥ (T *ᵥ v) := by
    intro n v
    rw [mulVec_mulVec, mulVec_mulVec, hzn]
  have hplane : ∀ j, T *ᵥ q j ∈ plane j := by
    intro j
    apply mem_plane_of_eigen
    intro i
    have hTa : T * ((a i : GL24) : Mat24) = ((a i : GL24) : Mat24) * T := hT _ (a_mem_A i)
    calc ((a i : GL24) : Mat24) *ᵥ (T *ᵥ q j) = T *ᵥ (((a i : GL24) : Mat24) *ᵥ q j) := by
          rw [mulVec_mulVec, mulVec_mulVec, hTa]
      _ = T *ᵥ ((zM ^ (γ j i).val) *ᵥ q j) := by rw [a_mulVec_q]
      _ = (zM ^ (γ j i).val) *ᵥ (T *ᵥ q j) := hzpow _ _
  have hr := (msData_spec (A_isMS _ r_mem_A)).2
  rw [msData_r.1, msData_r.2] at hr
  have h01 : ∀ j, T *ᵥ q j = 0 ∨ T *ᵥ q j = q j := by
    intro j
    by_cases h0 : T *ᵥ q j = 0
    · exact Or.inl h0
    · right
      obtain ⟨e, he⟩ := nonzero_plane_eq (hplane j) h0
      have hTr : T * ((r : GL24) : Mat24) = ((r : GL24) : Mat24) * T := hT _ r_mem_A
      have h1 : T *ᵥ (((r : GL24) : Mat24) *ᵥ q j) = ((r : GL24) : Mat24) *ᵥ (T *ᵥ q j) := by
        rw [mulVec_mulVec, mulVec_mulVec, hTr]
      have hr0 := hr j 0
      rw [ZMod.val_zero, pow_zero, one_mulVec, mul_zero, add_zero, id_eq] at hr0
      rw [hr0, hzpow, he, mulVec_mulVec, ← pow_val_add_of_pow_three zM_cube, hr j e] at h1
      have := (zq_inj h1).2
      have he0 : e = 0 := by
        have h2 : (msData ((r : GL24) : Mat24)).2.1 j + e =
            (msData ((r : GL24) : Mat24)).2.1 j + 2 * e := this
        have h3 : (3 : ZMod 3) = 0 := by decide
        linear_combination 2 * h2 + e * h3
      rw [he, he0, ZMod.val_zero, pow_zero, one_mulVec]
  have hall : (∀ j, T *ᵥ q j = 0) ∨ ∀ j, T *ᵥ q j = q j := by
    have key : ∀ j, (T *ᵥ q 0 = 0 → T *ᵥ q j = 0) ∧ (T *ᵥ q 0 = q 0 → T *ᵥ q j = q j) := by
      intro j
      obtain ⟨c, hc, hcj⟩ := lines_transitive j
      have hcMS := (msData_spec (A_isMS _ (C_le_A hc))).2
      have hc0 := hcMS 0 0
      rw [ZMod.val_zero, pow_zero, one_mulVec, mul_zero, add_zero, hcj] at hc0
      have hTc : T * ((c : GL24) : Mat24) = ((c : GL24) : Mat24) * T := hT _ (C_le_A hc)
      have hcomm : T *ᵥ (((c : GL24) : Mat24) *ᵥ q 0) = ((c : GL24) : Mat24) *ᵥ (T *ᵥ q 0) := by
        rw [mulVec_mulVec, mulVec_mulVec, hTc]
      rw [hc0, hzpow] at hcomm
      constructor
      · intro h
        exact zM_pow_cancel _ (hcomm.trans (by rw [h, mulVec_zero, mulVec_zero]))
      · intro h
        rw [h, hc0] at hcomm
        exact zM_pow_cancel _ hcomm
    rcases h01 0 with h | h
    · exact Or.inl fun j => (key j).1 h
    · exact Or.inr fun j => (key j).2 h
  rcases hall with h | h
  · left
    refine eq_of_zq fun j e => ?_
    rw [hzpow, h, mulVec_zero, zero_mulVec]
  · right
    refine eq_of_zq fun j e => ?_
    rw [hzpow, h, one_mulVec]

end CFSG.Sporadic.Co1Schreier
