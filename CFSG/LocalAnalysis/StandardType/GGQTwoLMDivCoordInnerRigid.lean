module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

private lemma qTwoLMDivCoordInner_rigid_cube_root {F0 : Type} [Field F0] [Finite F0]
    (hF0 : Nat.card F0 = 4) :
    ∃ ω : F0, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ≠ 0 := by
  have hcard : Nat.card F0ˣ = 3 := by
    have h := Nat.card_units F0
    omega
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F0ˣ)
  rw [hcard] at hζ
  refine ⟨(ζ : F0), ?_, ?_, ?_⟩
  · have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  · intro h
    have hζ1 : ζ = 1 := Units.ext h
    rw [hζ1] at hζ
    have : (1 : ℕ) = 3 := by simpa using hζ
    omega
  · exact ζ.ne_zero

private lemma qTwoLMDivCoordInner_rigid_diag_mem {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ} [NeZero m] (hm : 4 ≤ m) {ω : F0} (hω : ω ^ 3 = 1) :
    ∃ t : Su F0 2 1 m, ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i : Fin m =>
        if i = 0 then ω else if i = 1 then ω ^ 2 else 1) := by
  have hm1 : 1 < m := by omega
  let d : Fin m → F0 := fun i => if i = 0 then ω else if i = 1 then ω ^ 2 else 1
  let T : Matrix (Fin m) (Fin m) F0 := Matrix.diagonal d
  have h01 : (0 : Fin m) ≠ 1 := by
    intro h
    have hv : (0 : ℕ) = 1 := by
      have := congrArg Fin.val h
      simpa [Nat.mod_eq_of_lt hm1] using this
    omega
  have h10 : (1 : Fin m) ≠ (0 : Fin m) := Ne.symm h01
  have hd0 : d (0 : Fin m) = ω := by dsimp only [d]; rw [if_pos rfl]
  have hd1 : d (1 : Fin m) = ω ^ 2 := by dsimp only [d]; rw [if_neg h10, if_pos rfl]
  have hprod : ∏ i : Fin m, d i = 1 := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ (0 : Fin m))]
    rw [hd0]
    have hmem1 : (1 : Fin m) ∈ (Finset.univ \ {(0 : Fin m)} : Finset (Fin m)) := by
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [Finset.mem_singleton] using h10
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmem1]
    rw [hd1]
    have hrest : ∏ i ∈ (Finset.univ \ {(0 : Fin m)}) \ {(1 : Fin m)}, d i = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hi0 : i ≠ (0 : Fin m) := by
        have h1 := (Finset.mem_sdiff.mp hi).1
        exact fun h => (Finset.mem_sdiff.mp h1).2 (by simpa [h])
      have hi1 : i ≠ (1 : Fin m) := by
        have h1 := (Finset.mem_sdiff.mp hi).2
        simpa only [Finset.mem_singleton] using h1
      dsimp only [d]
      rw [if_neg hi0, if_neg hi1]
    rw [hrest, mul_one, show ω * ω ^ 2 = ω ^ 3 by ring, hω]
  have hcube : ∀ i : Fin m, (d i) ^ 2 * d i = 1 := by
    intro i
    have h3 : (d i) ^ 3 = 1 := by
      by_cases h0 : i = (0 : Fin m)
      · have : d i = ω := by dsimp only [d]; rw [if_pos h0]
        rw [this, hω]
      · by_cases h1 : i = (1 : Fin m)
        · have : d i = ω ^ 2 := by dsimp only [d]; rw [if_neg h0, if_pos h1]
          rw [this, show (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 by ring, hω, one_pow]
        · have : d i = 1 := by dsimp only [d]; rw [if_neg h0, if_neg h1]
          rw [this, one_pow]
    calc (d i) ^ 2 * d i = (d i) ^ 3 := by ring
      _ = 1 := h3
  have hconj : conjTr (unitaryInvolution F0 2 1) T =
      Matrix.diagonal (fun i : Fin m => (d i) ^ 2) := by
    simp only [T, conjTr, Matrix.diagonal_map (map_zero (unitaryInvolution F0 2 1)),
      Matrix.diagonal_transpose]
    congr 1
  have huni : conjTr (unitaryInvolution F0 2 1) T * T = 1 := by
    have h1 : conjTr (unitaryInvolution F0 2 1) T * T =
        Matrix.diagonal (fun i : Fin m => (d i) ^ 2 * d i) := by
      rw [hconj]
      simp only [T, Matrix.diagonal_mul_diagonal]
    rw [h1]
    rw [show (fun i : Fin m => (d i) ^ 2 * d i) = fun _ => (1 : F0) by
      funext i; exact hcube i, Matrix.diagonal_one]
  have hTdet : T.det = 1 := by
    rw [Matrix.det_diagonal]
    exact hprod
  have hdetnz : T.det ≠ 0 := by rw [hTdet]; exact one_ne_zero
  have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero T hdetnz ∈
      SUid (unitaryInvolution F0 2 1) m := by
    refine ⟨?_, ?_⟩
    · exact hTdet
    · exact huni
  exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero T hdetnz, hg⟩, rfl⟩

private lemma qTwoLMDivCoordInner_rigid_swap_entry {F0 : Type} [Field F0] {m : ℕ}
    {A : Matrix (Fin m) (Fin m) F0} {i j : Fin m}
    (h : A * (Equiv.swap i j).permMatrix F0 =
      (Equiv.swap i j).permMatrix F0 * A) (a b : Fin m) :
    A a b = A (Equiv.swap i j a) (Equiv.swap i j b) := by
  set σ : Equiv.Perm (Fin m) := Equiv.swap i j with hσ
  have hsub : A.submatrix id σ.symm = A.submatrix σ id := by
    rw [← PEquiv.mul_toMatrix_toPEquiv A σ, ← PEquiv.toMatrix_toPEquiv_mul σ A]
    simpa [hσ] using h
  have := congrFun (congrFun hsub a) (σ b)
  simpa [Matrix.submatrix_apply, hσ] using this

private lemma qTwoLMDivCoordInner_rigid_entries {F0 : Type} [Field F0] {m : ℕ} [NeZero m]
    (hm1 : 1 < m) {A : Matrix (Fin m) (Fin m) F0}
    (hcomm : ∀ i j : Fin m, i ≠ j →
      A * (Equiv.swap i j).permMatrix F0 = (Equiv.swap i j).permMatrix F0 * A) :
    (∀ i : Fin m, A i i = A 0 0) ∧ (∀ i j : Fin m, i ≠ j → A i j = A 0 1) := by
  have h01 : (0 : Fin m) ≠ 1 := by
    intro h
    have hv : (0 : ℕ) = 1 := by
      have := congrArg Fin.val h
      simpa [Nat.mod_eq_of_lt hm1] using this
    omega
  have hdiag : ∀ i : Fin m, A i i = A 0 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · have he := (qTwoLMDivCoordInner_rigid_swap_entry (hcomm 0 i (Ne.symm hi)) 0 0).symm
      simpa [Equiv.swap_apply_left] using he
  have hsym : ∀ i j : Fin m, i ≠ j → A i j = A j i := by
    intro i j hij
    have he := qTwoLMDivCoordInner_rigid_swap_entry (hcomm i j hij) i j
    simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using he
  have hshift1 : ∀ i b : Fin m, i ≠ 0 → b ≠ 0 → b ≠ i → A i b = A 0 b := by
    intro i b hi0 hb0 hbi
    have he := qTwoLMDivCoordInner_rigid_swap_entry (hcomm 0 i (Ne.symm hi0)) i b
    rw [Equiv.swap_apply_right (0 : Fin m) i,
      Equiv.swap_apply_of_ne_of_ne (a := (0 : Fin m)) (b := i) (x := b) hb0 hbi] at he
    exact he
  have hshift2 : ∀ a j : Fin m, j ≠ 1 → a ≠ 1 → a ≠ j → A a j = A a 1 := by
    intro a j hj1 ha1 haj
    have he := (qTwoLMDivCoordInner_rigid_swap_entry (hcomm 1 j (Ne.symm hj1)) a 1).symm
    rw [Equiv.swap_apply_left (1 : Fin m) j,
      Equiv.swap_apply_of_ne_of_ne (a := (1 : Fin m)) (b := j) (x := a) ha1 haj] at he
    exact he
  refine ⟨hdiag, ?_⟩
  intro i j hij
  by_cases hj0 : j = 0
  · subst hj0
    rw [hsym i 0 hij]
    by_cases hi1 : i = 1
    · rw [hi1]
    · exact hshift2 0 i hi1 h01 (Ne.symm hij)
  · by_cases hi0 : i = 0
    · subst hi0
      by_cases hj1 : j = 1
      · rw [hj1]
      · exact hshift2 0 j hj1 h01 (Ne.symm hj0)
    · rw [hshift1 i j hi0 hj0 (Ne.symm hij)]
      by_cases hj1 : j = 1
      · rw [hj1]
      · exact hshift2 0 j hj1 h01 (Ne.symm hj0)

private lemma qTwoLMDivCoordInner_rigid_swap_comm {F0 : Type} [Field F0] [Finite F0]
    [CharP F0 2] (hF0 : Nat.card F0 = 4) {m : ℕ} (hm : 4 ≤ m) {L0 : Type} [Group L0]
    (π : Su F0 2 1 m →* L0) (hπk : π.ker ≤ Subgroup.center (Su F0 2 1 m))
    {k : GL (Fin m) F0}
    (hk : ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
      (s' : GL (Fin m) F0) = k * (s : GL (Fin m) F0) * k⁻¹ ∧ π s' = π s)
    {i j : Fin m} (hij : i ≠ j) :
    (k : Matrix (Fin m) (Fin m) F0) * (Equiv.swap i j).permMatrix F0 =
      (Equiv.swap i j).permMatrix F0 * (k : Matrix (Fin m) (Fin m) F0) := by
  set σ : Equiv.Perm (Fin m) := Equiv.swap i j with hσ
  set P : Su F0 2 1 m := ggPermSU (f := 1) σ with hP
  obtain ⟨P', hP'⟩ := hk P
  let z : Su F0 2 1 m := P'⁻¹ * P
  have hzker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    show π (P'⁻¹ * P) = 1
    rw [map_mul, map_inv, hP'.2, inv_mul_cancel]
  have hzcenter : z ∈ Subgroup.center (Su F0 2 1 m) := hπk hzker
  obtain ⟨c, hc⟩ := qTwoLMDivCoordInner_center_scalar hF0 hm hzcenter
  have hPz : P = P' * z := by
    rw [show z = P'⁻¹ * P from rfl]
    group
  have hσ2 : σ * σ = 1 := by
    rw [hσ]
    ext a
    simp [Equiv.swap_apply_self]
  have hP2 : P * P = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one]
    change σ.permMatrix F0 * σ.permMatrix F0 = 1
    rw [← Matrix.permMatrix_mul, hσ2, Matrix.permMatrix_one]
  have hP2gl : (P : GL (Fin m) F0) * (P : GL (Fin m) F0) = 1 := by
    rw [← Subgroup.coe_mul, hP2, Subgroup.coe_one]
  have hP'2 : P' * P' = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    calc (P' : GL (Fin m) F0) * (P' : GL (Fin m) F0)
        = (k * (P : GL (Fin m) F0) * k⁻¹) * (k * (P : GL (Fin m) F0) * k⁻¹) := by
          rw [hP'.1]
      _ = k * ((P : GL (Fin m) F0) * (P : GL (Fin m) F0)) * k⁻¹ := by group
      _ = k * 1 * k⁻¹ := by rw [hP2gl]
      _ = 1 := by group
  have hzz : P * P = (P' * P') * (z * z) := by
    calc P * P = (P' * z) * (P' * z) := by rw [hPz]
      _ = P' * (z * P') * z := by group
      _ = P' * (P' * z) * z := by rw [Subgroup.mem_center_iff.mp hzcenter P']
      _ = (P' * P') * (z * z) := by group
  have hz2 : z * z = 1 := by
    rw [hP2, hP'2, one_mul] at hzz
    exact hzz.symm
  have hz2gl : (z : GL (Fin m) F0) * (z : GL (Fin m) F0) = 1 := by
    rw [← Subgroup.coe_mul, hz2, Subgroup.coe_one]
  have hcc2 : c * c = 1 := by
    have h := congrArg (fun x : GL (Fin m) F0 => (x : Matrix (Fin m) (Fin m) F0)) hz2gl
    rw [Units.val_mul, Units.val_one, hc] at h
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at h
    have h0 := congrFun (congrFun h i) i
    simpa [Matrix.diagonal_apply] using h0
  have hcc1 : c = 1 := by
    rcases (mul_self_eq_one_iff.mp hcc2) with h | h
    · exact h
    · rw [CharTwo.neg_eq] at h; exact h
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hc, hcc1]
    simp [Matrix.diagonal_one]
  have hP'eq : P' = P := by
    have h : P' = P' * z := by rw [hz1, mul_one]
    rw [h, hPz]
  have hPP : (P : GL (Fin m) F0) = k * (P : GL (Fin m) F0) * k⁻¹ := by
    rw [← hP'.1, hP'eq]
  have hcomm_gl : k * (P : GL (Fin m) F0) = (P : GL (Fin m) F0) * k := by
    have h : (P : GL (Fin m) F0) * k = k * (P : GL (Fin m) F0) := by
      calc (P : GL (Fin m) F0) * k = (k * (P : GL (Fin m) F0) * k⁻¹) * k := by rw [← hPP]
        _ = k * (P : GL (Fin m) F0) := by group
    exact h.symm
  have hPmat : ((P : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = σ.permMatrix F0 := rfl
  have hcomm_mat : (k : Matrix (Fin m) (Fin m) F0) * σ.permMatrix F0 =
      σ.permMatrix F0 * (k : Matrix (Fin m) (Fin m) F0) := by
    have h := congrArg (fun x : GL (Fin m) F0 => (x : Matrix (Fin m) (Fin m) F0)) hcomm_gl
    simp only [Units.val_mul, hPmat] at h
    exact h
  simpa [hσ] using hcomm_mat

theorem qTwoLMDivCoordInner_rigid {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) {m : ℕ} (hm : 4 ≤ m) {L0 : Type} [Group L0]
    (π : Su F0 2 1 m →* L0) (hπk : π.ker ≤ Subgroup.center (Su F0 2 1 m)) {k : GL (Fin m) F0}
    (hk : ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
      (s' : GL (Fin m) F0) = k * (s : GL (Fin m) F0) * k⁻¹ ∧ π s' = π s) :
    ∃ c : F0, ((k : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => c := by
  haveI : NeZero m := ⟨by omega⟩
  have hm1 : 1 < m := by omega
  set A : Matrix (Fin m) (Fin m) F0 := ((k : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
    with hA
  have hcomm : ∀ i j : Fin m, i ≠ j →
      A * (Equiv.swap i j).permMatrix F0 = (Equiv.swap i j).permMatrix F0 * A := by
    intro i j hij
    have h := qTwoLMDivCoordInner_rigid_swap_comm hF0 hm π hπk hk hij
    simpa [← hA] using h
  obtain ⟨hdiag, hoff⟩ := qTwoLMDivCoordInner_rigid_entries hm1 hcomm
  by_cases hb : A (0 : Fin m) (1 : Fin m) = 0
  · refine ⟨A (0 : Fin m) (0 : Fin m), ?_⟩
    ext i j
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact hdiag i
    · rw [if_neg hij, hoff i j hij]
      exact hb
  · obtain ⟨ω, hω3, hω1, hω0⟩ := qTwoLMDivCoordInner_rigid_cube_root hF0
    obtain ⟨t, htmat⟩ := qTwoLMDivCoordInner_rigid_diag_mem hm hω3
    let d : Fin m → F0 := fun i => if i = 0 then ω else if i = 1 then ω ^ 2 else 1
    have htmat' : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal d := by
      simpa [d] using htmat
    obtain ⟨t', ht'⟩ := hk t
    let z : Su F0 2 1 m := t * t'⁻¹
    have hzker : z ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      show π (t * t'⁻¹) = 1
      rw [map_mul, map_inv, ht'.2, mul_inv_cancel]
    have hzcenter : z ∈ Subgroup.center (Su F0 2 1 m) := hπk hzker
    obtain ⟨c, hc⟩ := qTwoLMDivCoordInner_center_scalar hF0 hm hzcenter
    have hz_mul : z * t' = t := by
      rw [show z = t * t'⁻¹ from rfl]
      group
    have ht_eq : (t : GL (Fin m) F0) =
        (z : GL (Fin m) F0) * k * (t : GL (Fin m) F0) * k⁻¹ := by
      calc (t : GL (Fin m) F0) = ((z * t' : Su F0 2 1 m) : GL (Fin m) F0) := by
            rw [hz_mul]
        _ = (z : GL (Fin m) F0) * (t' : GL (Fin m) F0) := Subgroup.coe_mul ..
        _ = (z : GL (Fin m) F0) * (k * (t : GL (Fin m) F0) * k⁻¹) := by rw [ht'.1]
        _ = (z : GL (Fin m) F0) * k * (t : GL (Fin m) F0) * k⁻¹ := by group
    have hmul : (t : GL (Fin m) F0) * k =
        (z : GL (Fin m) F0) * k * (t : GL (Fin m) F0) := by
      conv_lhs => rw [ht_eq]
      group
    have hmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) * A =
        ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) * A *
          ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
      have h := congrArg (fun x : GL (Fin m) F0 => (x : Matrix (Fin m) (Fin m) F0)) hmul
      simpa only [Units.val_mul, ← hA] using h
    have hentry : ∀ r s : Fin m, d r * A r s = c * A r s * d s := by
      intro r s
      have h := congrFun (congrFun hmat r) s
      rw [htmat', hc] at h
      simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal] using h
    have h02 := hentry (0 : Fin m) (2 : Fin m)
    have h12 := hentry (1 : Fin m) (2 : Fin m)
    have h01' : (0 : Fin m) ≠ 1 := by
      intro h
      have hv : (0 : ℕ) = 1 := by
        have := congrArg Fin.val h
        simpa [Nat.mod_eq_of_lt hm1] using this
      omega
    have h10' : (1 : Fin m) ≠ (0 : Fin m) := Ne.symm h01'
    have h20 : (2 : Fin m) ≠ (0 : Fin m) := by
      intro h
      have hv : (2 : ℕ) = 0 := by
        have := congrArg Fin.val h
        simpa [Nat.mod_eq_of_lt (by omega : 2 < m)] using this
      omega
    have h21 : (2 : Fin m) ≠ (1 : Fin m) := by
      intro h
      have hv : (2 : ℕ) = 1 := by
        have := congrArg Fin.val h
        simpa [Nat.mod_eq_of_lt (by omega : 2 < m), Nat.mod_eq_of_lt hm1] using this
      omega
    have hd0 : d (0 : Fin m) = ω := by dsimp only [d]; rw [if_pos rfl]
    have hd1 : d (1 : Fin m) = ω ^ 2 := by dsimp only [d]; rw [if_neg h10', if_pos rfl]
    have hd2 : d (2 : Fin m) = 1 := by dsimp only [d]; rw [if_neg h20, if_neg h21]
    have hA02 : A (0 : Fin m) (2 : Fin m) = A (0 : Fin m) (1 : Fin m) :=
      hoff _ _ (by
        intro h
        have hv : (0 : ℕ) = 2 := by
          have := congrArg Fin.val h
          simpa [Nat.mod_eq_of_lt (by omega : 2 < m)] using this
        omega)
    have hA12 : A (1 : Fin m) (2 : Fin m) = A (0 : Fin m) (1 : Fin m) :=
      hoff _ _ (by
        intro h
        have hv : (1 : ℕ) = 2 := by
          have := congrArg Fin.val h
          simpa [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt (by omega : 2 < m)] using this
        omega)
    rw [hd0, hd2, hA02] at h02
    rw [hd1, hd2, hA12] at h12
    have hzero : ω * A (0 : Fin m) (1 : Fin m) = ω ^ 2 * A (0 : Fin m) (1 : Fin m) := by
      rw [h02, h12]
    have hω_eq : ω = ω ^ 2 := mul_right_cancel₀ hb hzero
    have hω_one : ω = 1 := by
      have h : ω * 1 = ω * ω := by rw [mul_one, ← pow_two, ← hω_eq]
      exact (mul_left_cancel₀ hω0 h).symm
    exact absurd hω_one hω1

end CFSG.StandardType.QTwo

end
