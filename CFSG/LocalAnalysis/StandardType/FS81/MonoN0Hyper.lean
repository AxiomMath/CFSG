module

public import CFSG.LocalAnalysis.StandardType.FS81.MonoN0Hyp
public import CFSG.LocalAnalysis.StandardType.FS81.WtTwo

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {n : ℕ}

private theorem monoHyper_one_ne_zero {n : ℕ} (hn : 1 ≤ n) : (1 : Fin (n + 1)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_one', Fin.val_zero] at h'
  rw [Nat.mod_eq_of_lt (by omega)] at h'
  exact one_ne_zero h'

private theorem monoHyper_coordRefl_mulVec_e0 {a : Fin (n + 1)} (ha : a ≠ 0) :
    coordRefl a *ᵥ (Pi.single 0 1 : Fin (n + 1) → ZMod 3) = Pi.single 0 1 := by
  rw [coordRefl_mulVec]
  funext i
  by_cases hi : i = 0
  · subst hi
    rw [Pi.single_eq_same]
    rw [if_neg (Ne.symm ha)]
  · rw [Pi.single_eq_of_ne hi]
    by_cases hia : i = a
    · rw [if_pos hia]
      exact neg_zero
    · rw [if_neg hia]

private theorem monoHyper_eq_smul_single_of_coordRefl_eq_neg {a : Fin (n + 1)}
    {z : Fin (n + 1) → ZMod 3} (hz : coordRefl a *ᵥ z = -z) :
    z = z a • Pi.single a 1 := by
  have hzero : ∀ i, i ≠ a → z i = 0 := by
    intro i hi
    have h := congrFun hz i
    simp only [coordRefl_mulVec, Pi.neg_apply] at h
    rw [if_neg hi] at h
    exact zmod3_eq_zero_of_eq_neg (by simpa using h)
  funext i
  by_cases hi : i = a
  · subst hi
    simp
  · rw [hzero i hi, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]

private theorem monoHyper_eq_smul_single_of_wt_eq_one {v : Fin (n + 1) → ZMod 3}
    (hv : wt v = 1) :
    ∃ (a : Fin (n + 1)) (c : ZMod 3), c ≠ 0 ∧ v = c • Pi.single a 1 := by
  unfold wt at hv
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hv
  have ha_mem : a ∈ Finset.univ.filter fun i => v i ≠ 0 := by
    rw [ha]
    exact Finset.mem_singleton_self a
  rw [Finset.mem_filter] at ha_mem
  refine ⟨a, v a, ha_mem.2, ?_⟩
  funext i
  by_cases hi : i = a
  · subst hi
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · have hvi : v i = 0 := by
      by_contra hne
      have hmem : i ∈ Finset.univ.filter fun j => v j ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
      rw [ha, Finset.mem_singleton] at hmem
      exact hi hmem
    rw [hvi, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]

private theorem monoHyper_exists_pair (f : Fin 3 → ZMod 3) :
    ∃ i j : Fin 3, i ≠ j ∧ ∃ c : ZMod 3, (c = 1 ∨ c = -1) ∧ f i + c * f j = 0 := by
  revert f
  decide

private theorem monoHyper_spMat_conj_coordRefl {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (hσ : σ * σ = 1) (a : Fin k) :
    spMat σ 1 * coordRefl a * spMat σ 1 = coordRefl (σ a) := by
  have h1 : spMat σ 1 * coordRefl a
      = spMat σ (fun j => if j = a then -1 else 1) := by
    rw [coordRefl, spMat_mul, mul_one]
    congr 1
    funext j
    change 1 * (if j = a then -1 else 1) = (if j = a then -1 else 1)
    rw [one_mul]
    rfl
  rw [h1, spMat_mul, hσ, coordRefl]
  congr 1
  funext j
  by_cases h : j = σ a
  · subst h
    have hss : σ (σ a) = a := by
      have := congrArg (fun z => z a) hσ
      simpa [Equiv.Perm.mul_apply] using this
    rw [if_pos hss, if_pos rfl]
    change -1 * 1 = -1
    rw [mul_one]
    rfl
  · rw [if_neg h]
    have hne : σ j ≠ a := by
      intro hc
      exact h (by
        have hss : (σ * σ) j = j := by rw [hσ]; rfl
        rw [Equiv.Perm.mul_apply] at hss
        rw [← hss, hc])
    rw [if_neg hne]
    change 1 * 1 = 1
    rw [mul_one]

private theorem monoHyper_mulVec_e0_eq_smul {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hcomm : ∀ j : Fin (n + 1), j ≠ 0 → Commute M (coordRefl j)) :
    M *ᵥ Pi.single 0 1 = (M *ᵥ Pi.single 0 1) 0 • Pi.single 0 1 := by
  funext i
  by_cases hi : i = 0
  · subst hi
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · have hzi : (M *ᵥ Pi.single 0 1) i = 0 := by
      have h := congrArg (fun N : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3) =>
        N *ᵥ Pi.single 0 1) (hcomm i hi).eq
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        monoHyper_coordRefl_mulVec_e0 hi] at h
      have hi' := congrFun h i
      simp only [coordRefl_mulVec, Pi.neg_apply] at hi'
      exact zmod3_eq_zero_of_eq_neg hi'
    rw [hzi, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]

private theorem monoHyper_false_of_conj_one {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg)
    (h1 : ∀ a : Fin (n + 1), a ≠ 0 → ¬ OrbN Xg (Pi.single a 1))
    (hn : 4 ≤ n)
    {T T₁ : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    (hT₁ : (T₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 1)
    {B : GL (Fin (n + 1)) (ZMod 3)} (hBX : B ∈ Xg)
    (hT1eq : T₁ = B * T * B⁻¹) : False := by
  classical
  have hsingle0_ne : (Pi.single (0 : Fin (n + 1)) 1 : Fin (n + 1) → ZMod 3) ≠ 0 := by
    intro h0
    have h1' := congrFun h0 (0 : Fin (n + 1))
    rw [Pi.single_eq_same, Pi.zero_apply] at h1'
    exact one_ne_zero h1'
  set z : Fin (n + 1) → ZMod 3 :=
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 with hz_def
  have hz_axis : (T₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z = -z := by
    rw [hT1eq]
    exact conj_coordRefl_mulVec_axis hT B
  have hz_smul' : z = z 1 • Pi.single 1 1 := by
    apply monoHyper_eq_smul_single_of_coordRefl_eq_neg
    rw [← hT₁]
    exact hz_axis
  have hz_ne : z ≠ 0 := by
    rw [hz_def]
    exact gl_mulVec_ne_zero B hsingle0_ne
  have hz1' : z 1 ≠ 0 := by
    intro hzc
    apply hz_ne
    rw [hz_smul', hzc, zero_smul]
  set cz : ZMod 3 := z 1 with hcz_def
  have hz_smul : z = cz • Pi.single 1 1 := by
    rw [hcz_def]
    exact hz_smul'
  have hz1 : cz ≠ 0 := by
    rw [hcz_def]
    exact hz1'
  have hz_orb : OrbN Xg z := by
    rw [hz_def]
    exact orbN_mulVec (Xg := Xg) (orbN_e0 (Xg := Xg)) hBX
  have hsingle_orb : OrbN Xg (Pi.single 1 1) := by
    have h' := h.orbN_smul hz_orb (inv_ne_zero hz1)
    rw [hz_smul, smul_smul, inv_mul_cancel₀ hz1, one_smul] at h'
    exact h'
  exact h1 1 (monoHyper_one_ne_zero (by omega)) hsingle_orb

private theorem monoHyper_d1 {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg)
    (h1 : ∀ a : Fin (n + 1), a ≠ 0 → ¬ OrbN Xg (Pi.single a 1))
    (hn : 4 ≤ n)
    {T T₁ : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    (hT₁ : (T₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 1)
    (horb₂ : ∀ w : Fin (n + 1) → ZMod 3, w 0 = 0 → wt w = 2 → OrbN Xg w)
    {y : GL (Fin (n + 1)) (ZMod 3)} (hy : y ∈ Xg)
    (huM : (((y * T₁ * y⁻¹ : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n) :
    ∃ c : Fin (n + 1), c ≠ 0 ∧
      (((y * T₁ * y⁻¹ : GL (Fin (n + 1)) (ZMod 3))) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl c := by
  classical
  set u : GL (Fin (n + 1)) (ZMod 3) := y * T₁ * y⁻¹ with hu_def
  set w : Fin (n + 1) → ZMod 3 :=
    (y : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 1 1 with hw_def
  have hsingle_ne : (Pi.single (1 : Fin (n + 1)) 1 : Fin (n + 1) → ZMod 3) ≠ 0 := by
    intro h0
    have h1' := congrFun h0 (1 : Fin (n + 1))
    rw [Pi.single_eq_same, Pi.zero_apply] at h1'
    exact one_ne_zero h1'
  have hsingle0_ne : (Pi.single (0 : Fin (n + 1)) 1 : Fin (n + 1) → ZMod 3) ≠ 0 := by
    intro h0
    have h1' := congrFun h0 (0 : Fin (n + 1))
    rw [Pi.single_eq_same, Pi.zero_apply] at h1'
    exact one_ne_zero h1'
  have hwne : w ≠ 0 := by
    rw [hw_def]
    exact gl_mulVec_ne_zero y hsingle_ne
  have hu_axis : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ w = -w := by
    rw [hu_def, hw_def]
    exact conj_coordRefl_mulVec_axis hT₁ y
  have hune : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ≠ 1 := by
    intro hmat
    have hzero : w = 0 := by
      have h := hu_axis
      rw [hmat, Matrix.one_mulVec] at h
      funext i
      exact zmod3_eq_zero_of_eq_neg (by simpa using congrFun h i)
    exact hwne hzero
  have hcols : ∀ m : Fin (n + 1), ∃ c : ZMod 3,
      (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1 -
        Pi.single m 1 = c • w := by
    intro m
    refine ⟨(((y⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) 1, ?_⟩
    rw [hu_def, hw_def]
    exact conj_coordRefl_mulVec_sub hT₁ y (Pi.single m 1)
  have hu_sp : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈
      spSet (fun σ (_ : Fin (n + 1) → ZMod 3) => σ 0 = 0) := by
    simpa [hu_def, monoN0] using huM
  obtain ⟨σ, s, hs, hσ0, hmat⟩ := hu_sp
  have hne : spMat σ s ≠ 1 := by
    rw [← hmat]
    exact hune
  have hcols' : ∀ m : Fin (n + 1), ∃ c : ZMod 3,
      spMat σ s *ᵥ Pi.single m 1 - Pi.single m 1 = c • w := by
    intro m
    obtain ⟨c, hc⟩ := hcols m
    exact ⟨c, by rwa [← hmat]⟩
  have hcases := spMat_refl_cases (w := w) hs hne hcols'
  rcases hcases with ⟨a, hcase, c, hc, hwc⟩ | ⟨a, b, hab, δ, hδ, hcase, c, hc, hwc⟩
  · by_cases ha0 : a = 0
    · exfalso
      have huT : u = T := by
        apply Units.ext
        calc (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s := hmat
          _ = coordRefl a := hcase
          _ = coordRefl 0 := by rw [ha0]
          _ = (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := hT.symm
      have hT1eq : T₁ = y⁻¹ * T * (y⁻¹)⁻¹ := by
        have h := congrArg (fun z => y⁻¹ * z * y) huT
        rw [hu_def] at h
        simpa [mul_assoc] using h
      exact monoHyper_false_of_conj_one h h1 hn hT hT₁ (Xg.inv_mem hy) hT1eq
    · exact ⟨a, ha0, hmat.trans hcase⟩
  · exfalso
    have hcomm : Commute (spMat σ s) (coordRefl 0) := by
      rw [← hmat]
      exact commute_coordRefl_zero_of_mem_monoN0 huM
    have h0ab : 0 ≠ a ∧ 0 ≠ b := by
      refine (coordRefl_commute_swapRefl_iff hab hδ 0).mp ?_
      rw [← hcase]
      exact hcomm.symm
    have ha : a ≠ 0 := fun h' => h0ab.1 h'.symm
    have hb : b ≠ 0 := fun h' => h0ab.2 h'.symm
    have hv : OrbN Xg (c • (Pi.single a 1 - δ • Pi.single b 1)) := by
      refine horb₂ _ ?_ (wt_smul_single_sub_smul hab hc hδ)
      simp [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm ha),
        Pi.single_eq_of_ne (Ne.symm hb)]
    obtain ⟨A, hAX, hAe, hAconj⟩ := h.exists_conj_swapRefl hT ha hb hab hc hδ hv
    have hconj : A * T * A⁻¹ = y * T₁ * y⁻¹ := by
      apply Units.ext
      rw [hAconj, ← hcase, ← hmat, hu_def]
    let B : GL (Fin (n + 1)) (ZMod 3) := y⁻¹ * A
    have hBX : B ∈ Xg := Xg.mul_mem (Xg.inv_mem hy) hAX
    have hT1eq : T₁ = B * T * B⁻¹ := by
      have h := congrArg (fun z => y⁻¹ * z * y) hconj
      dsimp only [B]
      simpa [mul_assoc] using h.symm
    exact monoHyper_false_of_conj_one h h1 hn hT hT₁ hBX hT1eq


private theorem monoHyper_perm_conj {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) (hn : 4 ≤ n)
    {T₁ : GL (Fin (n + 1)) (ZMod 3)}
    (hT₁ : (T₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 1)
    (hT₁X : T₁ ∈ Xg) {j : Fin (n + 1)} (hj : j ≠ 0)
    {Tj : GL (Fin (n + 1)) (ZMod 3)}
    (hTj : (Tj : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl j)
    (hTjX : Tj ∈ Xg) :
    ∃ P : GL (Fin (n + 1)) (ZMod 3), P ∈ Xg ∧
      (P : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        spMat (Equiv.swap (1 : Fin (n + 1)) j) 1 ∧ P * T₁ * P⁻¹ = Tj := by
  classical
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap (1 : Fin (n + 1)) j
  have hσ : σ * σ = 1 := Equiv.swap_mul_self 1 j
  have hσ0 : σ 0 = 0 := by
    have h10 : (1 : Fin (n + 1)) ≠ 0 := monoHyper_one_ne_zero (by omega)
    exact Equiv.swap_apply_of_ne_of_ne h10.symm hj.symm
  have hmem : spMat σ 1 ∈ monoN0 n :=
    ⟨σ, fun _ => 1, fun _ => Or.inl rfl, hσ0, rfl⟩
  obtain ⟨P, hPX, hP⟩ := h.sub _ hmem
  have hP2 : P * P = 1 := by
    apply Units.ext
    rw [Units.val_mul, hP, Units.val_one]
    exact spMat_mul_self σ 1 hσ (fun _ => by
      change (1 : ZMod 3) * 1 = 1
      rw [one_mul])
  have hPinv : P⁻¹ = P := inv_eq_of_mul_eq_one_right hP2
  have hσ1 : σ 1 = j := by
    simp only [σ, Equiv.swap_apply_left]
  refine ⟨P, hPX, hP, ?_⟩
  apply Units.ext
  rw [hPinv, Units.val_mul, Units.val_mul, hP, hT₁, hTj]
  rw [monoHyper_spMat_conj_coordRefl hσ 1, hσ1]

private theorem monoHyper_axis_two {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (hn : 4 ≤ n)
    (horb₂ : ∀ w : Fin (n + 1) → ZMod 3, w 0 = 0 → wt w = 2 → OrbN Xg w)
    (x : GL (Fin (n + 1)) (ZMod 3)) :
    ∃ v : Fin (n + 1) → ZMod 3, v 0 = 0 ∧ v 1 = 0 ∧ wt v = 2 ∧
      (((x⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 1 = 0 ∧
      ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1 = v := by
  classical
  let idx : Fin 3 → Fin (n + 1) := fun t => ⟨t.val + 2, by have := t.isLt; omega⟩
  have hidx_inj : Function.Injective idx := by
    intro s t hst
    apply Fin.ext
    have h' := congrArg Fin.val hst
    simp only [idx] at h'
    omega
  have hidx0 : ∀ t, idx t ≠ 0 := by
    intro t h
    have h' := congrArg Fin.val h
    simp only [idx, Fin.val_zero] at h'
    omega
  have hidx1 : ∀ t, idx t ≠ 1 := by
    intro t h
    have h' := congrArg Fin.val h
    simp only [idx] at h'
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h'
    omega
  let f : Fin 3 → ZMod 3 := fun t =>
    (((x⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single (idx t) 1) 1
  obtain ⟨i, j, hij, c, hc, hfij⟩ := monoHyper_exists_pair f
  have hcne : c ≠ 0 := by
    rcases hc with hc | hc
    · rw [hc]; exact one_ne_zero
    · rw [hc]; exact neg_ne_zero.mpr one_ne_zero
  let v : Fin (n + 1) → ZMod 3 :=
    Pi.single (idx i) 1 + c • Pi.single (idx j) 1
  have hv0 : v 0 = 0 := by
    simp only [v, Pi.add_apply, Pi.smul_apply]
    rw [Pi.single_eq_of_ne (Ne.symm (hidx0 i)), Pi.single_eq_of_ne (Ne.symm (hidx0 j))]
    simp
  have hv1 : v 1 = 0 := by
    simp only [v, Pi.add_apply, Pi.smul_apply]
    rw [Pi.single_eq_of_ne (Ne.symm (hidx1 i)), Pi.single_eq_of_ne (Ne.symm (hidx1 j))]
    simp
  have hvwt : wt v = 2 := by
    have hv : v = (Pi.single (idx i) 1 + Pi.single (idx j) c :
        Fin (n + 1) → ZMod 3) := by
      funext k
      change (Pi.single (idx i) 1 : Fin (n + 1) → ZMod 3) k +
          (c • (Pi.single (idx j) 1 : Fin (n + 1) → ZMod 3)) k =
        (Pi.single (idx i) 1 : Fin (n + 1) → ZMod 3) k +
          (Pi.single (idx j) c : Fin (n + 1) → ZMod 3) k
      rw [← Pi.single_smul']
      simp
    rw [hv]
    exact wt_single_add_single (hidx_inj.ne hij) one_ne_zero hcne
  have hfv : (((x⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 1 = 0 := by
    have h : (((x⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 1 = f i + c * f j := by
      simp only [v, f, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [h, hfij]
  obtain ⟨A, hAX, hAe⟩ := horb₂ v hv0 hvwt
  exact ⟨v, hv0, hv1, hvwt, hfv, A, hAX, hAe⟩

private theorem monoHyper_d2 {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg)
    (h1 : ∀ a : Fin (n + 1), a ≠ 0 → ¬ OrbN Xg (Pi.single a 1))
    (hn : 4 ≤ n)
    {T T₁ : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    (hT₁ : (T₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 1)
    (hT₁X : T₁ ∈ Xg)
    (horb₂ : ∀ w : Fin (n + 1) → ZMod 3, w 0 = 0 → wt w = 2 → OrbN Xg w)
    {x : GL (Fin (n + 1)) (ZMod 3)} (hx : x ∈ Xg) :
    Commute T₁ (x * T₁ * x⁻¹) := by
  obtain ⟨v, _, hv1, _, hfv, A, hAX, hAe⟩ := monoHyper_axis_two hn horb₂ x
  have hT1v : (T₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v := by
    rw [hT₁, coordRefl_mulVec]
    funext k
    by_cases hk : k = 1
    · subst hk
      rw [if_pos rfl, hv1]
      exact neg_zero
    · rw [if_neg hk]
  set U : GL (Fin (n + 1)) (ZMod 3) := x * T₁ * x⁻¹ with hU_def
  have hUv : (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v := by
    have h := conj_coordRefl_mulVec_sub hT₁ x v
    rw [hfv, zero_smul] at h
    rw [← hU_def] at h
    exact sub_eq_zero.mp h
  set R : GL (Fin (n + 1)) (ZMod 3) := A * T * A⁻¹ with hR_def
  have hT1A : T₁ * A ∈ Xg := Xg.mul_mem hT₁X hAX
  have hAB1 : (((T₁ * A : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        (1 : ZMod 3) • ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          Pi.single 0 1) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hAe, hT1v, one_smul]
  have hUX : U ∈ Xg := Xg.mul_mem (Xg.mul_mem hx hT₁X) (Xg.inv_mem hx)
  have hUA : U * A ∈ Xg := Xg.mul_mem hUX hAX
  have hAB2 : (((U * A : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        (1 : ZMod 3) • ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          Pi.single 0 1) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hAe, hUv, one_smul]
  have hR1 : T₁ * R * T₁⁻¹ = R := by
    have h := MonoN0Hyp.conj_eq_of_mulVec_e0 h (Xg := Xg) (c := 1) hT hT1A hAX hAB1
    simpa [hR_def, mul_assoc] using h
  have hR2 : U * R * U⁻¹ = R := by
    have h := MonoN0Hyp.conj_eq_of_mulVec_e0 h (Xg := Xg) (c := 1) hT hUA hAX hAB2
    simpa [hR_def, mul_assoc] using h
  have hcommR1 : Commute T₁ R :=
    (commute_iff_eq T₁ R).mpr (by
      have h := congrArg (fun z => z * T₁) hR1
      simpa [mul_assoc] using h)
  have hcommR2 : Commute U R :=
    (commute_iff_eq U R).mpr (by
      have h := congrArg (fun z => z * U) hR2
      simpa [mul_assoc] using h)
  have hcomm1 : Commute (A⁻¹ * T₁ * A) T := by
    have h := hcommR1.conj A⁻¹
    simpa [hR_def, mul_assoc] using h
  have hcomm2 : Commute (A⁻¹ * U * A) T := by
    have h := hcommR2.conj A⁻¹
    simpa [hR_def, mul_assoc] using h
  have hmono1 : (((A⁻¹ * T₁ * A : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
    refine MonoN0Hyp.mem_monoN0_of_commute h hT ?_ hcomm1
    exact Xg.mul_mem (Xg.mul_mem (Xg.inv_mem hAX) hT₁X) hAX
  have hmono2 : (((A⁻¹ * U * A : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
    refine MonoN0Hyp.mem_monoN0_of_commute h hT ?_ hcomm2
    exact Xg.mul_mem (Xg.mul_mem (Xg.inv_mem hAX) hUX) hAX
  have hmono1' : (((A⁻¹ * T₁ * (A⁻¹)⁻¹ : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
    simpa using hmono1
  have hmono2' : ((((A⁻¹ * x : GL (Fin (n + 1)) (ZMod 3)) * T₁ *
      (A⁻¹ * x)⁻¹) : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
    simpa [hU_def, mul_assoc] using hmono2
  obtain ⟨c₁, hc₁, hmat1'⟩ := monoHyper_d1 h h1 hn hT hT₁ horb₂ (Xg.inv_mem hAX) hmono1'
  obtain ⟨c₂, hc₂, hmat2'⟩ := monoHyper_d1 h h1 hn hT hT₁ horb₂
    (Xg.mul_mem (Xg.inv_mem hAX) hx) hmono2'
  have hmat1 : (((A⁻¹ * T₁ * A : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl c₁ := by
    simpa using hmat1'
  have hmat2 : (((A⁻¹ * U * A : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl c₂ := by
    simpa [hU_def, mul_assoc] using hmat2'
  have hcommPQ : Commute (A⁻¹ * T₁ * A) (A⁻¹ * U * A) :=
    (commute_iff_eq _ _).mpr (by
      apply Units.ext
      change (((A⁻¹ * T₁ * A : GL (Fin (n + 1)) (ZMod 3))) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
          (((A⁻¹ * U * A : GL (Fin (n + 1)) (ZMod 3))) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        (((A⁻¹ * U * A : GL (Fin (n + 1)) (ZMod 3))) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
          (((A⁻¹ * T₁ * A : GL (Fin (n + 1)) (ZMod 3))) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))
      rw [hmat1, hmat2]
      exact (coordRefl_commute c₁ c₂).eq)
  have hcommT1U : Commute T₁ U := by
    have h := hcommPQ.conj A
    simpa [mul_assoc] using h
  exact hcommT1U


private theorem monoHyper_d3 {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg)
    (h1 : ∀ a : Fin (n + 1), a ≠ 0 → ¬ OrbN Xg (Pi.single a 1))
    (hn : 4 ≤ n)
    {T T₁ : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    (hT₁ : (T₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 1)
    (hT₁X : T₁ ∈ Xg)
    (horb₂ : ∀ w : Fin (n + 1) → ZMod 3, w 0 = 0 → wt w = 2 → OrbN Xg w)
    {x : GL (Fin (n + 1)) (ZMod 3)} (hx : x ∈ Xg) {k : Fin (n + 1)} (hk : k ≠ 0)
    {Tk : GL (Fin (n + 1)) (ZMod 3)}
    (hTk : (Tk : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl k)
    (hTkX : Tk ∈ Xg) :
    ∃ c : Fin (n + 1), c ≠ 0 ∧
      (((x * Tk * x⁻¹ : GL (Fin (n + 1)) (ZMod 3))) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl c := by
  classical
  set U : GL (Fin (n + 1)) (ZMod 3) := x * Tk * x⁻¹ with hU_def
  have hUX : U ∈ Xg := Xg.mul_mem (Xg.mul_mem hx hTkX) (Xg.inv_mem hx)
  obtain ⟨Pk, hPkX, hPk, hconjPk⟩ := monoHyper_perm_conj h hn hT₁ hT₁X hk hTk hTkX
  have hcommU : ∀ j : Fin (n + 1), j ≠ 0 → Commute (U :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) (coordRefl j) := by
    intro j hj
    obtain ⟨Tj, hTjX, hTj⟩ := h.exists_coordRefl j
    obtain ⟨Pj, hPjX, hPj, hconjPj⟩ := monoHyper_perm_conj h hn hT₁ hT₁X hj hTj hTjX
    have hzX : Pj⁻¹ * x * Pk ∈ Xg :=
      Xg.mul_mem (Xg.mul_mem (Xg.inv_mem hPjX) hx) hPkX
    have hz_eq : (Pj⁻¹ * x * Pk) * T₁ * (Pj⁻¹ * x * Pk)⁻¹ = Pj⁻¹ * U * Pj := by
      calc (Pj⁻¹ * x * Pk) * T₁ * (Pj⁻¹ * x * Pk)⁻¹
          = Pj⁻¹ * (x * (Pk * T₁ * Pk⁻¹) * x⁻¹) * Pj := by group
        _ = Pj⁻¹ * (x * Tk * x⁻¹) * Pj := by rw [hconjPk]
        _ = Pj⁻¹ * U * Pj := by rw [hU_def]
    have hD2 := monoHyper_d2 h h1 hn hT hT₁ hT₁X horb₂ hzX
    have hDj : Commute T₁ (Pj⁻¹ * U * Pj) := by rwa [← hz_eq]
    have hcommTj : Commute Tj U := by
      have h' := hDj.conj Pj
      simpa [hconjPj, mul_assoc] using h'
    exact (commute_iff_eq (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))
      (coordRefl j)).mpr (by
        have h' := congrArg (fun z : GL (Fin (n + 1)) (ZMod 3) =>
          (z : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))) hcommTj
        simp only [Units.val_mul, hTj] at h'
        exact h'.symm)
  have hUmono : (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n :=
    MonoN0Hyp.mem_of_mulVec_e0 h hUX (monoHyper_mulVec_e0_eq_smul hcommU)
  have hyX : x * Pk ∈ Xg := Xg.mul_mem hx hPkX
  have hy_eq : (x * Pk) * T₁ * (x * Pk)⁻¹ = U := by
    calc (x * Pk) * T₁ * (x * Pk)⁻¹ = x * (Pk * T₁ * Pk⁻¹) * x⁻¹ := by group
      _ = x * Tk * x⁻¹ := by rw [hconjPk]
      _ = U := by rw [hU_def]
  have hmono' : ((((x * Pk) * T₁ * (x * Pk)⁻¹ : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
    rwa [hy_eq]
  obtain ⟨c, hc, hmat⟩ := monoHyper_d1 h h1 hn hT hT₁ horb₂ hyX hmono'
  rw [hy_eq] at hmat
  exact ⟨c, hc, hmat⟩

namespace MonoN0Hyp

variable {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))} (h : MonoN0Hyp Xg)
include h

theorem false_of_not_orbN_single (hn : 4 ≤ n)
    (h1 : ∀ a : Fin (n + 1), a ≠ 0 → ¬ OrbN Xg (Pi.single a 1)) : False := by
  classical
  obtain ⟨T, hTX, hT⟩ := h.exists_coordRefl 0
  obtain ⟨T₁, hT₁X, hT₁⟩ := h.exists_coordRefl 1
  obtain ⟨v, hv, hv0⟩ := h.exists_orbN_zero
  have hzero2 : ∃ v, OrbN Xg v ∧ v 0 = 0 ∧ wt v = 2 := by
    rcases h.wt_of_orbN_zero hv hv0 with hw | hw
    · exfalso
      obtain ⟨a, c, hc, hva⟩ := monoHyper_eq_smul_single_of_wt_eq_one hw
      have ha : a ≠ 0 := by
        intro ha0
        have h : v 0 = 0 := hv0
        rw [hva, ha0] at h
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
        exact hc h
      have hvc : OrbN Xg (c • Pi.single a 1) := hva ▸ hv
      have hsingle : OrbN Xg (Pi.single a 1) := by
        have h' := h.orbN_smul hvc (inv_ne_zero hc)
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
      exact h1 a ha hsingle
    · exact ⟨v, hv, hv0, hw⟩
  obtain ⟨v, hv, hv0, hwt2⟩ := hzero2
  have horb₂ : ∀ w : Fin (n + 1) → ZMod 3, w 0 = 0 → wt w = 2 → OrbN Xg w := by
    intro w hw0 hw
    exact h.orbN_of_wt_eq_zero hv hv0 hw0 (by omega)
  obtain ⟨x, hxX, i, hi, hxi⟩ := h.moves
  obtain ⟨Ti, hTiX, hTi⟩ := h.exists_coordRefl i
  obtain ⟨c, hc, hmat⟩ := monoHyper_d3 h h1 hn hT hT₁ hT₁X horb₂
    (Xg.inv_mem hxX) hi hTi hTiX
  have hmat' : (((x⁻¹ * Ti * x : GL (Fin (n + 1)) (ZMod 3))) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl c := by
    simpa using hmat
  have hTi_eq : Ti = x * (x⁻¹ * Ti * x) * x⁻¹ := by group
  have hfix : (Ti : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
        (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 := by
    rw [hTi_eq, gl_conj_mulVec, gl_inv_mulVec_mulVec, hmat',
      monoHyper_coordRefl_mulVec_e0 hc]
  have hwi : ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      Pi.single 0 1) i = (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  have hzero : ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      Pi.single 0 1) i = 0 := by
    have hcoord := congrFun hfix i
    simp only [hTi, coordRefl_mulVec, Pi.neg_apply] at hcoord
    exact zmod3_eq_zero_of_eq_neg hcoord.symm
  exact hxi (hwi ▸ hzero)

end MonoN0Hyp

end CFSG.StandardType.FrameRoute.FS81
