module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open Module Subgroup

variable {𝕜 : Type*} [Field 𝕜]
  {Γ : Type*} [Group Γ] [Finite Γ]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  (ρ : Representation 𝕜 Γ V) (W : Fin 6 → Submodule 𝕜 V)
  (σ : Γ →* Equiv.Perm (Fin 6))

private lemma exists_nonzero_mem_line (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1) (i : Fin 6) :
    ∃ b ∈ W i, b ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro hbot
  have h := h1 i
  rw [hbot, finrank_bot] at h
  exact zero_ne_one h

private lemma exists_scalar_of_map_line {g : Γ} {i : Fin 6}
    (h1 : Module.finrank 𝕜 (W i) = 1) (hg : (W i).map (ρ g) = W i) :
    ∃ c : 𝕜ˣ, ∀ v ∈ W i, ρ g v = (c : 𝕜) • v := by
  classical
  have hne : W i ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨b, hbW, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hbmem : ρ g b ∈ W i := by
    rw [← hg]
    exact Submodule.mem_map_of_mem hbW
  have hinj : Function.Injective (ρ g) := by
    intro x y hxy
    have h : ρ g⁻¹ (ρ g x) = ρ g⁻¹ (ρ g y) := by rw [hxy]
    calc x = ρ g⁻¹ (ρ g x) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]
      _ = ρ g⁻¹ (ρ g y) := h
      _ = y := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]
  have hbne : ρ g b ≠ 0 := fun h0 => hb0 (hinj (by simpa using h0))
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one h1
    (x := (⟨b, hbW⟩ : W i)) (by simpa using hb0) (⟨ρ g b, hbmem⟩ : W i)
  have hcv : (c : 𝕜) • b = ρ g b := by simpa using congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hcv
    exact hbne hcv.symm
  refine ⟨Units.mk0 c hc0, fun v hv => ?_⟩
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one h1
    (x := (⟨b, hbW⟩ : W i)) (by simpa using hb0) (⟨v, hv⟩ : W i)
  have hav : a • b = v := by simpa using congrArg Subtype.val ha
  calc ρ g v = ρ g (a • b) := by rw [hav]
    _ = a • ρ g b := by rw [map_smul]
    _ = a • ((c : 𝕜) • b) := by rw [hcv]
    _ = ((c : 𝕜) * a) • b := by rw [smul_smul, mul_comm]
    _ = (c : 𝕜) • (a • b) := by rw [smul_smul]
    _ = (c : 𝕜) • v := by rw [hav]

private lemma units_eq_of_smul_eq {b : V} (hb : b ≠ 0) {c d : 𝕜ˣ}
    (h : (c : 𝕜) • b = (d : 𝕜) • b) : c = d :=
  Units.ext (smul_left_injective (R := 𝕜) (M := V) hb h)

private lemma map_line_ker (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (i : Fin 6)
    (n : σ.ker) : (W i).map (ρ (n : Γ)) = W i := by
  rw [hσW, MonoidHom.mem_ker.mp n.2, Equiv.Perm.one_apply]

private noncomputable def chi (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (i : Fin 6) (n : σ.ker) : 𝕜ˣ :=
  (exists_scalar_of_map_line (ρ := ρ) (W := W) (g := (n : Γ)) (h1 := h1 i)
    (map_line_ker (ρ := ρ) (W := W) (σ := σ) hσW i n)).choose

private lemma chi_spec (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (i : Fin 6) (n : σ.ker)
    (v : V) (hv : v ∈ W i) :
    ρ (n : Γ) v = (chi ρ W σ h1 hσW i n : 𝕜) • v := by
  unfold chi
  exact Classical.choose_spec (exists_scalar_of_map_line (ρ := ρ) (W := W) (g := (n : Γ))
    (h1 := h1 i) (map_line_ker (ρ := ρ) (W := W) (σ := σ) hσW i n)) v hv

private lemma chi_one (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (i : Fin 6) :
    chi ρ W σ h1 hσW i 1 = 1 := by
  obtain ⟨b, hbW, hb0⟩ := exists_nonzero_mem_line (W := W) h1 i
  apply units_eq_of_smul_eq hb0
  simpa using (chi_spec ρ W σ h1 hσW i 1 b hbW).symm

private lemma chi_mul (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (i : Fin 6) (n m : σ.ker) :
    chi ρ W σ h1 hσW i (n * m) = chi ρ W σ h1 hσW i n * chi ρ W σ h1 hσW i m := by
  obtain ⟨b, hbW, hb0⟩ := exists_nonzero_mem_line (W := W) h1 i
  apply units_eq_of_smul_eq hb0
  have h2 : ρ (((n * m : σ.ker) : Γ)) b
      = (((chi ρ W σ h1 hσW i n * chi ρ W σ h1 hσW i m : 𝕜ˣ)) : 𝕜) • b := by
    calc ρ (((n * m : σ.ker) : Γ)) b
        = ρ ((n : Γ) * (m : Γ)) b := rfl
      _ = ρ (n : Γ) (ρ (m : Γ) b) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (n : Γ) ((chi ρ W σ h1 hσW i m : 𝕜) • b) := by
            rw [chi_spec ρ W σ h1 hσW i m b hbW]
      _ = (chi ρ W σ h1 hσW i m : 𝕜) • ρ (n : Γ) b := by rw [map_smul]
      _ = (chi ρ W σ h1 hσW i m : 𝕜) • ((chi ρ W σ h1 hσW i n : 𝕜) • b) := by
            rw [chi_spec ρ W σ h1 hσW i n b hbW]
      _ = (((chi ρ W σ h1 hσW i n * chi ρ W σ h1 hσW i m : 𝕜ˣ)) : 𝕜) • b := by
            rw [Units.val_mul, smul_smul, mul_comm]
  rw [← chi_spec ρ W σ h1 hσW i (n * m) b hbW, h2]

private noncomputable def chiHom (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (i : Fin 6) : σ.ker →* 𝕜ˣ where
  toFun := chi ρ W σ h1 hσW i
  map_one' := chi_one ρ W σ h1 hσW i
  map_mul' := chi_mul ρ W σ h1 hσW i

private noncomputable def chiJoint (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) : σ.ker →* (Fin 6 → 𝕜ˣ) where
  toFun n i := chiHom ρ W σ h1 hσW i n
  map_one' := by funext i; exact map_one (chiHom ρ W σ h1 hσW i)
  map_mul' n m := by funext i; exact map_mul (chiHom ρ W σ h1 hσW i) n m

private lemma chiJoint_injective (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hWtop : ⨆ i, W i = ⊤) (hfaith : Function.Injective ρ) :
    Function.Injective (chiJoint ρ W σ h1 hσW) := by
  intro n m h
  have hfun : ∀ i, chi ρ W σ h1 hσW i n = chi ρ W σ h1 hσW i m :=
    fun i => congrFun h i
  have hker : ∀ v : V, ρ (n : Γ) v = ρ (m : Γ) v := by
    intro v
    have hv : v ∈ ⨆ i, W i := by rw [hWtop]; exact Submodule.mem_top
    refine Submodule.iSup_induction (fun i => W i)
      (motive := fun v => ρ (n : Γ) v = ρ (m : Γ) v) hv ?_ ?_ ?_
    · intro i w hw
      rw [chi_spec ρ W σ h1 hσW i n w hw, chi_spec ρ W σ h1 hσW i m w hw, hfun i]
    · simp
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  have hρ : ρ (n : Γ) = ρ (m : Γ) := by
    ext v
    exact hker v
  have hnm : (n : Γ) = (m : Γ) := hfaith hρ
  exact Subtype.ext hnm

private lemma mul_comm_ker (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (hWtop : ⨆ i, W i = ⊤)
    (hfaith : Function.Injective ρ) (a b : σ.ker) : a * b = b * a := by
  have h : chiJoint ρ W σ h1 hσW (a * b) = chiJoint ρ W σ h1 hσW (b * a) := by
    ext i
    simp only [chiJoint, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
    exact mul_comm _ _
  exact chiJoint_injective ρ W σ h1 hσW hWtop hfaith h


private lemma threeCycleDiff_pointwise (S : Set (Fin 6)) {a b c e : Fin 6}
    {π : Equiv.Perm (Fin 6)} (haS : a ∈ S) (hbS : b ∉ S) (hca : c ≠ a) (hcb : c ≠ b)
    (he : (c ∈ S ∧ e = c) ∨ (c ∉ S ∧ e = a))
    (hπ : π = Equiv.swap a b * Equiv.swap b c) :
    ∀ x : Fin 6, x ≠ b → x ≠ e → (x ∈ S ↔ π⁻¹ x ∈ S) := by
  have hπinv : π⁻¹ = Equiv.swap b c * Equiv.swap a b := by
    rw [hπ, mul_inv_rev]
    simp
  intro x hxb hxe
  rw [hπinv]
  have hρa : (Equiv.swap b c * Equiv.swap a b) a = c := by
    rw [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_left]
  have hρc : (Equiv.swap b c * Equiv.swap a b) c = b := by
    rw [Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (a := a) (b := b) (x := c) hca hcb,
      Equiv.swap_apply_right]
  by_cases hxa : x = a
  · rw [hxa] at hxe ⊢
    have hcS : c ∈ S := by
      rcases he with ⟨hcS, -⟩ | ⟨-, hea⟩
      · exact hcS
      · exact absurd hea.symm hxe
    rw [hρa]
    exact ⟨fun _ => hcS, fun _ => haS⟩
  by_cases hxc : x = c
  · rw [hxc] at hxe ⊢
    have hcS : c ∉ S := by
      rcases he with ⟨hcS, hec⟩ | ⟨hcS, -⟩
      · exact absurd hec.symm hxe
      · exact hcS
    rw [hρc]
    exact ⟨fun h => absurd h hcS, fun h => absurd h hbS⟩
  · have hρx : (Equiv.swap b c * Equiv.swap a b) x = x := by
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (a := a) (b := b) (x := x) hxa hxb]
      exact Equiv.swap_apply_of_ne_of_ne (a := b) (b := c) (x := x) hxb hxc
    rw [hρx]

private lemma threeCycleDiff_b_e (S : Set (Fin 6)) {a b c e : Fin 6}
    {π : Equiv.Perm (Fin 6)} (haS : a ∈ S) (hbS : b ∉ S) (hca : c ≠ a) (hcb : c ≠ b)
    (hab : a ≠ b) (he : (c ∈ S ∧ e = c) ∨ (c ∉ S ∧ e = a))
    (hπ : π = Equiv.swap a b * Equiv.swap b c) :
    (b ∉ S ∧ π⁻¹ b ∈ S) ∧ (e ∈ S ∧ π⁻¹ e ∉ S) := by
  have hπinv : π⁻¹ = Equiv.swap b c * Equiv.swap a b := by
    rw [hπ, mul_inv_rev]
    simp
  have hρa : (Equiv.swap b c * Equiv.swap a b) a = c := by
    rw [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_left]
  have hρb : (Equiv.swap b c * Equiv.swap a b) b = a := by
    rw [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (a := b) (b := c) (x := a) hab (Ne.symm hca)]
  have hρc : (Equiv.swap b c * Equiv.swap a b) c = b := by
    rw [Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (a := a) (b := b) (x := c) hca hcb,
      Equiv.swap_apply_right]
  constructor
  · refine ⟨hbS, ?_⟩
    rw [hπinv, hρb]
    exact haS
  · rcases he with ⟨hcS, hec⟩ | ⟨hcS, hea⟩
    · refine ⟨hec ▸ hcS, ?_⟩
      rw [hec, hπinv, hρc]
      exact hbS
    · refine ⟨hea ▸ haS, ?_⟩
      rw [hea, hπinv, hρa]
      exact hcS

private lemma exists_threeCycle_diff_two (S : Set (Fin 6)) (hne : S.Nonempty)
    (hproper : S ≠ Set.univ) :
    ∃ (b e : Fin 6) (π : Equiv.Perm (Fin 6)),
      b ≠ e ∧ π ∈ alternatingGroup (Fin 6) ∧
        (∀ x : Fin 6, x ≠ b → x ≠ e → (x ∈ S ↔ π⁻¹ x ∈ S)) ∧
        (b ∉ S ∧ π⁻¹ b ∈ S) ∧ (e ∈ S ∧ π⁻¹ e ∉ S) := by
  classical
  obtain ⟨a, haS⟩ := hne
  have hbS : ∃ b : Fin 6, b ∉ S := by
    by_contra h
    push Not at h
    exact hproper (Set.eq_univ_of_forall h)
  obtain ⟨b, hbS⟩ := hbS
  have hab : a ≠ b := by
    intro h
    rw [h] at haS
    exact hbS haS
  have hc : ∃ c : Fin 6, c ≠ a ∧ c ≠ b := by
    have h2 : ({a, b} : Finset (Fin 6)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
    have hcard : (Finset.univ \ ({a, b} : Finset (Fin 6))).card = 4 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, h2]
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num)
    rw [Finset.mem_sdiff] at hc
    simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    exact ⟨c, hc⟩
  obtain ⟨c, hca, hcb⟩ := hc
  let π : Equiv.Perm (Fin 6) := Equiv.swap a b * Equiv.swap b c
  let e : Fin 6 := if c ∈ S then c else a
  have hbe : b ≠ e := by
    by_cases hcS : c ∈ S
    · simp only [e, if_pos hcS]
      exact fun h => hcb h.symm
    · simp only [e, if_neg hcS]
      exact fun h => hab h.symm
  have hπA : π ∈ alternatingGroup (Fin 6) :=
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      (Equiv.Perm.swap_isSwap_iff.mpr hab) (Equiv.Perm.swap_isSwap_iff.mpr (Ne.symm hcb))
  have heq : (c ∈ S ∧ e = c) ∨ (c ∉ S ∧ e = a) := by
    by_cases hcS : c ∈ S
    · exact Or.inl ⟨hcS, by simp [e, hcS]⟩
    · exact Or.inr ⟨hcS, by simp [e, hcS]⟩
  have hπeq : π = Equiv.swap a b * Equiv.swap b c := rfl
  refine ⟨b, e, π, hbe, hπA, threeCycleDiff_pointwise S haS hbS hca hcb heq hπeq,
    (threeCycleDiff_b_e S haS hbS hca hcb hab heq hπeq).1,
    (threeCycleDiff_b_e S haS hbS hca hcb hab heq hπeq).2⟩

private lemma ringChar_ne_two_of_two_ne_zero {𝕜 : Type*} [Field 𝕜]
    (h2 : (2 : 𝕜) ≠ 0) : ringChar 𝕜 ≠ 2 := by
  intro h
  apply h2
  have hdvd : ringChar 𝕜 ∣ 2 := by simpa [h] using (dvd_refl 2 : (2 : ℕ) ∣ 2)
  exact (ringChar.spec (R := 𝕜) 2).mpr hdvd

private lemma neg_one_ne_one {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0) :
    (-1 : 𝕜ˣ) ≠ 1 := by
  intro h
  have h' : (-1 : 𝕜) = 1 := by simpa using congrArg Units.val h
  exact Ring.neg_one_ne_one_of_char_ne_two (ringChar_ne_two_of_two_ne_zero h2) h'

private lemma chi_sq_eq_one (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (i : Fin 6) (n : σ.ker)
    (hn2 : n * n = 1) :
    chi ρ W σ h1 hσW i n = 1 ∨ chi ρ W σ h1 hσW i n = -1 := by
  have hsq : chi ρ W σ h1 hσW i n ^ 2 = 1 := by
    rw [sq, ← chi_mul, hn2, chi_one]
  have h := Units.eq_or_eq_neg_of_sq_eq_sq (chi ρ W σ h1 hσW i n) (1 : 𝕜ˣ)
    (by simpa using hsq)
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h

private lemma chi_conj (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i)) (g : Γ) (n : σ.ker) (i : Fin 6)
    (hmem : g * (n : Γ) * g⁻¹ ∈ σ.ker) :
    chi ρ W σ h1 hσW i ⟨g * (n : Γ) * g⁻¹, hmem⟩
      = chi ρ W σ h1 hσW ((σ g)⁻¹ i) n := by
  obtain ⟨b, hbW, hb0⟩ := exists_nonzero_mem_line (W := W) h1 i
  apply units_eq_of_smul_eq hb0
  have hmap : (W ((σ g)⁻¹ i)).map (ρ g) = W i := by
    rw [hσW]
    simp
  have hbW' : b ∈ (W ((σ g)⁻¹ i)).map (ρ g) := by
    rw [hmap]
    exact hbW
  obtain ⟨w, hwW, hw⟩ := Submodule.mem_map.mp hbW'
  have hginv : ρ g⁻¹ b = w := by
    rw [← hw, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  calc (chi ρ W σ h1 hσW i ⟨g * (n : Γ) * g⁻¹, hmem⟩ : 𝕜) • b
      = ρ (g * (n : Γ) * g⁻¹) b := (chi_spec ρ W σ h1 hσW i ⟨_, hmem⟩ b hbW).symm
    _ = ρ g (ρ (n : Γ) (ρ g⁻¹ b)) := by
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    _ = ρ g (ρ (n : Γ) w) := by rw [hginv]
    _ = ρ g ((chi ρ W σ h1 hσW ((σ g)⁻¹ i) n : 𝕜) • w) := by
          rw [chi_spec ρ W σ h1 hσW ((σ g)⁻¹ i) n w hwW]
    _ = (chi ρ W σ h1 hσW ((σ g)⁻¹ i) n : 𝕜) • ρ g w := by rw [map_smul]
    _ = (chi ρ W σ h1 hσW ((σ g)⁻¹ i) n : 𝕜) • b := by rw [hw]

private lemma chi_product_eq_one (h2 : (2 : 𝕜) ≠ 0)
    (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (n hN : σ.ker) (hn2 : n * n = 1) (hh2 : hN * hN = 1)
    {π : Equiv.Perm (Fin 6)} {b e : Fin 6} (S : Set (Fin 6))
    (hS : ∀ i, i ∈ S ↔ chi ρ W σ h1 hσW i n = -1)
    (hprop : ∀ x : Fin 6, x ≠ b → x ≠ e → (x ∈ S ↔ π⁻¹ x ∈ S))
    (hconj : ∀ i, chi ρ W σ h1 hσW i hN = chi ρ W σ h1 hσW (π⁻¹ i) n)
    (i : Fin 6) (hib : i ≠ b) (hie : i ≠ e) :
    chi ρ W σ h1 hσW i (n * hN) = 1 := by
  have hiff : chi ρ W σ h1 hσW i n = -1 ↔ chi ρ W σ h1 hσW i hN = -1 := by
    rw [hconj i, ← hS i, ← hS (π⁻¹ i)]
    exact hprop i hib hie
  have hn_sq := chi_sq_eq_one (ρ := ρ) (W := W) (σ := σ) h1 hσW i n hn2
  have hh_sq := chi_sq_eq_one (ρ := ρ) (W := W) (σ := σ) h1 hσW i hN hh2
  have heq : chi ρ W σ h1 hσW i n = chi ρ W σ h1 hσW i hN := by
    rcases hn_sq with hn | hn
    · rcases hh_sq with hh | hh
      · rw [hn, hh]
      · have h1' : chi ρ W σ h1 hσW i n = -1 := hiff.mpr hh
        rw [hn] at h1'
        exact absurd h1'.symm (neg_one_ne_one h2)
    · rw [hn, hiff.mp hn]
  calc chi ρ W σ h1 hσW i (n * hN)
      = chi ρ W σ h1 hσW i n * chi ρ W σ h1 hσW i hN := by rw [chi_mul]
    _ = chi ρ W σ h1 hσW i n * chi ρ W σ h1 hσW i n := by rw [heq]
    _ = 1 := by
        rcases hn_sq with hn | hn
        · rw [hn, one_mul]
        · rw [hn]
          ext
          simp

private lemma chi_at_e_eq_neg_one (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (n hN : σ.ker) (hn2 : n * n = 1)
    {π : Equiv.Perm (Fin 6)} {e : Fin 6} (S : Set (Fin 6))
    (hS : ∀ i, i ∈ S ↔ chi ρ W σ h1 hσW i n = -1)
    (heS : e ∈ S) (hpre : π⁻¹ e ∉ S)
    (hconj : ∀ i, chi ρ W σ h1 hσW i hN = chi ρ W σ h1 hσW (π⁻¹ i) n) :
    chi ρ W σ h1 hσW e (n * hN) = -1 := by
  have hne_e : chi ρ W σ h1 hσW e n = -1 := (hS e).mp heS
  have hpre' : chi ρ W σ h1 hσW (π⁻¹ e) n = 1 := by
    have hs := chi_sq_eq_one (ρ := ρ) (W := W) (σ := σ) h1 hσW (π⁻¹ e) n hn2
    rcases hs with h | h
    · exact h
    · exact absurd ((hS (π⁻¹ e)).mpr h) hpre
  calc chi ρ W σ h1 hσW e (n * hN)
      = chi ρ W σ h1 hσW e n * chi ρ W σ h1 hσW e hN := by rw [chi_mul]
    _ = (-1) * 1 := by rw [hne_e, hconj e, hpre']
    _ = -1 := by simp

private lemma four_le_finrank_of_chi_off (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hWind : iSupIndep W) (u : σ.ker) (hu2 : u * u = 1) {b e : Fin 6} (hbe : b ≠ e)
    (hchi : ∀ i, i ≠ b → i ≠ e → chi ρ W σ h1 hσW i u = 1) :
    4 ≤ Module.finrank 𝕜 (LinearMap.ker (ρ (u : Γ) - 1)) := by
  classical
  let T : Finset (Fin 6) := (Finset.univ.erase b).erase e
  have he_erase : e ∈ Finset.univ.erase b :=
    Finset.mem_erase.mpr ⟨Ne.symm hbe, Finset.mem_univ e⟩
  have hTcard : T.card = 4 := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem he_erase,
      Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin]
  have hTmem : ∀ i, i ∈ T → i ≠ b ∧ i ≠ e := by
    intro i hi
    dsimp only [T] at hi
    have h1 := Finset.mem_erase.mp hi
    have h2 := Finset.mem_erase.mp h1.2
    exact ⟨h2.1, h1.1⟩
  choose v hvW hv0 using fun i : {i : Fin 6 // i ∈ T} =>
    exists_nonzero_mem_line (W := W) h1 i.1
  have hind : iSupIndep (fun i : {i : Fin 6 // i ∈ T} => W i.1) :=
    hWind.comp Subtype.val_injective
  have hli : LinearIndependent 𝕜 v := hind.linearIndependent _ hvW hv0
  have hfix : ∀ i : {i : Fin 6 // i ∈ T}, v i ∈ LinearMap.ker (ρ (u : Γ) - 1) := by
    intro i
    obtain ⟨hib, hie⟩ := hTmem i.1 i.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [chi_spec ρ W σ h1 hσW i.1 u (v i) (hvW i), hchi i.1 hib hie]
    simp
  have hli' : LinearIndependent 𝕜
      (fun i : {i : Fin 6 // i ∈ T} =>
        (⟨v i, hfix i⟩ : LinearMap.ker (ρ (u : Γ) - 1))) :=
    hli.codRestrict _ hfix
  have hcardT : Fintype.card {i : Fin 6 // i ∈ T} = 4 := by
    rw [Fintype.card_coe, hTcard]
  have hle : 4 ≤ Module.finrank 𝕜 (LinearMap.ker (ρ (u : Γ) - 1)) := by
    have h := hli'.fintype_card_le_finrank
    rwa [hcardT] at h
  exact hle

private lemma exists_conj_involution_data (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hWtop : ⨆ i, W i = ⊤) (hfaith : Function.Injective ρ)
    (hσ : σ.range = alternatingGroup (Fin 6))
    (n : σ.ker) (hn2 : n * n = 1) {π : Equiv.Perm (Fin 6)}
    (hπA : π ∈ alternatingGroup (Fin 6)) :
    ∃ hN : σ.ker, hN * hN = 1 ∧ n * hN = hN * n ∧
      (∀ i, chi ρ W σ h1 hσW i hN = chi ρ W σ h1 hσW (π⁻¹ i) n) := by
  classical
  have hπmem : π ∈ σ.range := by rw [hσ]; exact hπA
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hπmem
  have hmem : g * (n : Γ) * g⁻¹ ∈ σ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp n.2]
    simp
  let hN : σ.ker := ⟨g * (n : Γ) * g⁻¹, hmem⟩
  have hn2' : (n : Γ) * (n : Γ) = 1 := by simpa using congrArg Subtype.val hn2
  have hh2 : hN * hN = 1 := by
    apply Subtype.ext
    show (g * (n : Γ) * g⁻¹) * (g * (n : Γ) * g⁻¹) = 1
    calc (g * (n : Γ) * g⁻¹) * (g * (n : Γ) * g⁻¹)
        = g * ((n : Γ) * (n : Γ)) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [hn2']
      _ = 1 := by group
  have hcomm : n * hN = hN * n := mul_comm_ker ρ W σ h1 hσW hWtop hfaith n hN
  have hconj : ∀ i, chi ρ W σ h1 hσW i hN = chi ρ W σ h1 hσW (π⁻¹ i) n := by
    intro i
    have h := chi_conj ρ W σ h1 hσW g n i hmem
    rw [hg] at h
    exact h
  exact ⟨hN, hh2, hcomm, hconj⟩

private lemma false_of_involution_minus_one_on_proper
    (h2 : (2 : 𝕜) ≠ 0) (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hWind : iSupIndep W) (hWtop : ⨆ i, W i = ⊤)
    (hfaith : Function.Injective ρ) (hσ : σ.range = alternatingGroup (Fin 6))
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3)
    (n : σ.ker) (hn2 : n * n = 1) (S : Set (Fin 6))
    (hS : ∀ i, i ∈ S ↔ chi ρ W σ h1 hσW i n = -1)
    (hne : S.Nonempty) (hproper : S ≠ Set.univ) : False := by
  classical
  obtain ⟨b, e, π, hbe, hπA, hprop, hbD, heD⟩ := exists_threeCycle_diff_two S hne hproper
  obtain ⟨hN, hh2, hcomm, hconj_chi⟩ := exists_conj_involution_data (ρ := ρ) (W := W)
    (σ := σ) h1 hσW hWtop hfaith hσ n hn2 hπA
  have hn2' : (n : Γ) * (n : Γ) = 1 := by simpa using congrArg Subtype.val hn2
  have hh2' : (hN : Γ) * (hN : Γ) = 1 := by simpa using congrArg Subtype.val hh2
  have hcomm' : (hN : Γ) * (n : Γ) = (n : Γ) * (hN : Γ) := congrArg Subtype.val hcomm.symm
  let u : σ.ker := n * hN
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    show ((n * hN : σ.ker) : Γ) * ((n * hN : σ.ker) : Γ) = 1
    calc (n : Γ) * (hN : Γ) * ((n : Γ) * (hN : Γ))
        = (n : Γ) * ((hN : Γ) * (n : Γ)) * (hN : Γ) := by group
      _ = (n : Γ) * ((n : Γ) * (hN : Γ)) * (hN : Γ) := by rw [hcomm']
      _ = (n : Γ) * (n : Γ) * ((hN : Γ) * (hN : Γ)) := by group
      _ = 1 := by rw [hn2', hh2']; group
  have hchi_fixed : ∀ i, i ≠ b → i ≠ e → chi ρ W σ h1 hσW i u = 1 := by
    intro i hib hie
    exact chi_product_eq_one (ρ := ρ) (W := W) (σ := σ) h2 h1 hσW n hN hn2 hh2
      S hS hprop hconj_chi i hib hie
  have hchi_e : chi ρ W σ h1 hσW e u = -1 :=
    chi_at_e_eq_neg_one (ρ := ρ) (W := W) (σ := σ) h1 hσW n hN hn2 S hS heD.1 heD.2
      hconj_chi
  have hu1 : (u : Γ) ≠ 1 := by
    intro hu
    have hu' : u = 1 := Subtype.ext hu
    have h1' : chi ρ W σ h1 hσW e u = 1 := by
      rw [hu']
      exact chi_one ρ W σ h1 hσW e
    rw [hchi_e] at h1'
    exact (neg_one_ne_one h2) h1'
  have hu2' : (u : Γ) * (u : Γ) = 1 := congrArg Subtype.val hu2
  have hpg : IsPGroup 2 (Subgroup.zpowers (u : Γ)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by simpa [sq] using hu2')
  have hle := four_le_finrank_of_chi_off (ρ := ρ) (W := W) (σ := σ) h1 hσW hWind u hu2
    hbe hchi_fixed
  have hle3 := hr3 (u : Γ) hpg hu1
  omega

private lemma involution_dichotomy (h2 : (2 : 𝕜) ≠ 0)
    (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hWind : iSupIndep W) (hWtop : ⨆ i, W i = ⊤)
    (hfaith : Function.Injective ρ) (hσ : σ.range = alternatingGroup (Fin 6))
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3)
    (n : σ.ker) (hn2 : n * n = 1) :
    n = 1 ∨ ∀ i, chi ρ W σ h1 hσW i n = -1 := by
  classical
  by_cases hn1 : n = 1
  · exact Or.inl hn1
  · right
    by_contra hall
    push Not at hall
    obtain ⟨i0, hi0⟩ := hall
    let S : Set (Fin 6) := {i | chi ρ W σ h1 hσW i n = -1}
    have hS : ∀ i, i ∈ S ↔ chi ρ W σ h1 hσW i n = -1 := fun i => Iff.rfl
    have hproper : S ≠ Set.univ := by
      intro h
      have : i0 ∈ S := by rw [h]; exact Set.mem_univ i0
      exact hi0 ((hS i0).mp this)
    have hne : S.Nonempty := by
      by_contra hne
      have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hall1 : ∀ j, chi ρ W σ h1 hσW j n = 1 := by
        intro j
        have hj : j ∉ S := by rw [hempty]; simp
        have hnot : chi ρ W σ h1 hσW j n ≠ -1 := fun h => hj ((hS j).mpr h)
        rcases chi_sq_eq_one (ρ := ρ) (W := W) (σ := σ) h1 hσW j n hn2 with h | h
        · exact h
        · exact absurd h hnot
      apply hn1
      apply chiJoint_injective ρ W σ h1 hσW hWtop hfaith
      funext j
      simp [chiJoint, chiHom, hall1 j, chi_one ρ W σ h1 hσW j]
    exact false_of_involution_minus_one_on_proper (ρ := ρ) (W := W) (σ := σ)
      h2 h1 hσW hWind hWtop hfaith hσ hr3 n hn2 S hS hne hproper



private def cOne : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

private def cTwo : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 3

private def doubleTransposition : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

private lemma cOne_mem : cOne ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

private lemma cTwo_mem : cTwo ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

private lemma cOne_fix_four : cOne 4 = 4 := by decide

private lemma cOne_fix_five : cOne 5 = 5 := by decide

private lemma cTwo_fix_four : cTwo 4 = 4 := by decide

private lemma cTwo_fix_five : cTwo 5 = 5 := by decide

private lemma commutator_eq : cOne * cTwo * cOne⁻¹ * cTwo⁻¹ = doubleTransposition := by
  decide

private lemma doubleTransposition_zero : doubleTransposition 0 = 1 := by decide

private lemma doubleTransposition_two : doubleTransposition 2 = 3 := by decide

private lemma doubleTransposition_sq : doubleTransposition * doubleTransposition = 1 := by decide

private lemma doubleTransposition_ne_one : doubleTransposition ≠ 1 := by decide

private lemma rho_inv_apply_of_scalar {i : Fin 6} {g : Γ}
    (hg : (W i).map (ρ g) = W i) {c : 𝕜ˣ}
    (hc : ∀ v ∈ W i, ρ g v = (c : 𝕜) • v) :
    ∀ v ∈ W i, ρ g⁻¹ v = ((c⁻¹ : 𝕜ˣ) : 𝕜) • v := by
  have hginv : (W i).map (ρ g⁻¹) = W i := by
    have h := congrArg (Submodule.map (ρ g⁻¹)) hg
    rw [← Submodule.map_comp, show (ρ g⁻¹).comp (ρ g) = 1 by
      rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]] at h
    rw [show (1 : Module.End 𝕜 V) = LinearMap.id from rfl, Submodule.map_id] at h
    exact h.symm
  intro v hv
  have hmem : ρ g⁻¹ v ∈ W i := by
    rw [← hginv]
    exact Submodule.mem_map_of_mem hv
  have hcv : (c : 𝕜) • (ρ g⁻¹ v) = v := by
    rw [← hc (ρ g⁻¹ v) hmem]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc ρ g⁻¹ v = (c : 𝕜)⁻¹ • ((c : 𝕜) • (ρ g⁻¹ v)) := by
        rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul]
    _ = (c : 𝕜)⁻¹ • v := by rw [hcv]
    _ = ((c⁻¹ : 𝕜ˣ) : 𝕜) • v := by rw [Units.val_inv_eq_inv_val]

private lemma rho_commutator_apply_self {i : Fin 6} (h1 : Module.finrank 𝕜 (W i) = 1)
    {x y : Γ} (hx : (W i).map (ρ x) = W i) (hy : (W i).map (ρ y) = W i)
    {v : V} (hv : v ∈ W i) : ρ (x * y * x⁻¹ * y⁻¹) v = v := by
  obtain ⟨a, ha⟩ := exists_scalar_of_map_line (ρ := ρ) (W := W) h1 hx
  obtain ⟨b, hb⟩ := exists_scalar_of_map_line (ρ := ρ) (W := W) h1 hy
  have hxa := rho_inv_apply_of_scalar (ρ := ρ) (W := W) hx ha
  have hyb := rho_inv_apply_of_scalar (ρ := ρ) (W := W) hy hb
  have h1' : ρ (x * y * x⁻¹ * y⁻¹) v = ρ x (ρ y (ρ x⁻¹ (ρ y⁻¹ v))) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [h1', hyb v hv, map_smul, hxa v hv, smul_smul,
    map_smul, hb v hv, smul_smul,
    map_smul, ha v hv, smul_smul]
  congr 1
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  field_simp
  simp

private lemma linearIndependent_four_of_swap_shape
    (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1) (hWind : iSupIndep W)
    (t : Γ) (ht2 : t * t = 1)
    (hmap01 : (W 0).map (ρ t) = W 1) (hmap23 : (W 2).map (ρ t) = W 3)
    {b0 b2 b4 b5 : V} (hb0W : b0 ∈ W 0) (hb2W : b2 ∈ W 2) (hb4W : b4 ∈ W 4)
    (hb5W : b5 ∈ W 5) (hb0 : b0 ≠ 0) (hb2 : b2 ≠ 0) (hb4 : b4 ≠ 0) (hb5 : b5 ≠ 0) :
    LinearIndependent 𝕜 ![b4, b5, b0 + ρ t b0, b2 + ρ t b2] := by
  classical
  have ht_inv : ρ t * ρ t = 1 := by rw [← map_mul, ht2, map_one]
  have ht0 : ρ t b0 ∈ W 1 := by
    rw [← hmap01]
    exact Submodule.mem_map_of_mem hb0W
  have ht2' : ρ t b2 ∈ W 3 := by
    rw [← hmap23]
    exact Submodule.mem_map_of_mem hb2W
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  rw [Fin.sum_univ_four] at hsum
  let c : Fin 6 → V :=
    ![g 2 • b0, g 2 • (ρ t b0), g 3 • b2, g 3 • (ρ t b2), g 0 • b4, g 1 • b5]
  have hc : ∑ i, c i = 0 := by
    simpa [c, Fin.sum_univ_six, smul_add, add_comm, add_left_comm, add_assoc] using hsum
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin 6)), c i ∈ W i := by
    intro i _
    fin_cases i
    · simpa [c] using Submodule.smul_mem (W 0) (g 2) hb0W
    · simpa [c] using Submodule.smul_mem (W 1) (g 2) ht0
    · simpa [c] using Submodule.smul_mem (W 2) (g 3) hb2W
    · simpa [c] using Submodule.smul_mem (W 3) (g 3) ht2'
    · simpa [c] using Submodule.smul_mem (W 4) (g 0) hb4W
    · simpa [c] using Submodule.smul_mem (W 5) (g 1) hb5W
  have hzero := (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero (p := W)).mp hWind
    Finset.univ c hmem hc
  have hcoef : ∀ (a : 𝕜) (b : V), b ≠ 0 → a • b = 0 → a = 0 := fun a b hb ha =>
    (smul_eq_zero.mp ha).resolve_right hb
  have hg0 : g 0 = 0 := hcoef _ _ hb4 (by simpa [c] using hzero 4 (Finset.mem_univ 4))
  have hg1 : g 1 = 0 := hcoef _ _ hb5 (by simpa [c] using hzero 5 (Finset.mem_univ 5))
  have hg2 : g 2 = 0 := hcoef _ _ hb0 (by simpa [c] using hzero 0 (Finset.mem_univ 0))
  have hg3 : g 3 = 0 := hcoef _ _ hb2 (by simpa [c] using hzero 2 (Finset.mem_univ 2))
  intro k
  fin_cases k
  · exact hg0
  · exact hg1
  · exact hg2
  · exact hg3

private lemma four_le_finrank_ker_of_swap_shape
    (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1) (hWind : iSupIndep W)
    (t : Γ) (ht2 : t * t = 1)
    (h4 : ∀ v ∈ W 4, ρ t v = v) (h5 : ∀ v ∈ W 5, ρ t v = v)
    (hmap01 : (W 0).map (ρ t) = W 1) (hmap23 : (W 2).map (ρ t) = W 3) :
    4 ≤ Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) := by
  classical
  obtain ⟨b0, hb0W, hb0⟩ := exists_nonzero_mem_line (W := W) h1 0
  obtain ⟨b2, hb2W, hb2⟩ := exists_nonzero_mem_line (W := W) h1 2
  obtain ⟨b4, hb4W, hb4⟩ := exists_nonzero_mem_line (W := W) h1 4
  obtain ⟨b5, hb5W, hb5⟩ := exists_nonzero_mem_line (W := W) h1 5
  have ht_inv : ρ t * ρ t = 1 := by rw [← map_mul, ht2, map_one]
  have hcomp (b : V) : ρ t (ρ t b) = b := by
    have := congrArg (fun f : Module.End 𝕜 V => f b) ht_inv
    simpa [Module.End.mul_apply] using this
  have hfix0 : ρ t (b0 + ρ t b0) = b0 + ρ t b0 := by
    rw [map_add, hcomp, add_comm]
  have hfix2 : ρ t (b2 + ρ t b2) = b2 + ρ t b2 := by
    rw [map_add, hcomp, add_comm]
  let u : Fin 4 → V := ![b4, b5, b0 + ρ t b0, b2 + ρ t b2]
  have hu : LinearIndependent 𝕜 u :=
    linearIndependent_four_of_swap_shape (ρ := ρ) (W := W) h1 hWind t ht2 hmap01 hmap23
      hb0W hb2W hb4W hb5W hb0 hb2 hb4 hb5
  have hfix : ∀ k : Fin 4, u k ∈ LinearMap.ker (ρ t - 1) := by
    intro k
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    fin_cases k <;> simp [u, h4 _ hb4W, h5 _ hb5W, hfix0, hfix2]
  have hli : LinearIndependent 𝕜
      (fun k : Fin 4 => (⟨u k, hfix k⟩ : LinearMap.ker (ρ t - 1))) :=
    hu.codRestrict _ hfix
  simpa using hli.fintype_card_le_finrank

private lemma rho_pow_apply_eq_self {i : Fin 6} {g : Γ}
    (h : ∀ v ∈ W i, ρ g v = v) (k : ℕ) : ∀ v ∈ W i, ρ (g ^ k) v = v := by
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ, map_mul, Module.End.mul_apply, h v hv, ih v hv]

private lemma exists_commutator_q (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hσ : σ.range = alternatingGroup (Fin 6)) :
    ∃ q : Γ, σ q = doubleTransposition ∧
      (∀ v ∈ W 4, ρ q v = v) ∧ (∀ v ∈ W 5, ρ q v = v) := by
  have hc1mem : cOne ∈ σ.range := by rw [hσ]; exact cOne_mem
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hc1mem
  have hc2mem : cTwo ∈ σ.range := by rw [hσ]; exact cTwo_mem
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hc2mem
  let q : Γ := x * y * x⁻¹ * y⁻¹
  have hσq : σ q = doubleTransposition := by
    rw [show q = x * y * x⁻¹ * y⁻¹ from rfl, map_mul, map_mul, map_mul, map_inv, map_inv,
      hx, hy, commutator_eq]
  have hx4 : (W 4).map (ρ x) = W 4 := by rw [hσW, hx, cOne_fix_four]
  have hy4 : (W 4).map (ρ y) = W 4 := by rw [hσW, hy, cTwo_fix_four]
  have hx5 : (W 5).map (ρ x) = W 5 := by rw [hσW, hx, cOne_fix_five]
  have hy5 : (W 5).map (ρ y) = W 5 := by rw [hσW, hy, cTwo_fix_five]
  refine ⟨q, hσq, fun v hv => ?_, fun v hv => ?_⟩
  · exact rho_commutator_apply_self (ρ := ρ) (W := W) (h1 4) hx4 hy4 hv
  · exact rho_commutator_apply_self (ρ := ρ) (W := W) (h1 5) hx5 hy5 hv

private lemma exists_odd_power_involution (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (t : Γ) (a : ℕ) (ha : 1 ≤ a) (ha2 : 2 ≤ a) (ht_order : orderOf t = 2 ^ a)
    (hσt : σ t = doubleTransposition) (ht4 : ∀ v ∈ W 4, ρ t v = v) :
    ∃ n : Γ, n * n = 1 ∧ n ∈ σ.ker ∧ n ≠ 1 ∧
      (∀ v ∈ W 4, ρ n v = v) ∧ n = t ^ (2 ^ (a - 1)) := by
  let n : Γ := t ^ (2 ^ (a - 1))
  have h2a : orderOf t / 2 = 2 ^ (a - 1) := by
    rw [ht_order, show a = (a - 1) + 1 by omega, pow_succ,
      Nat.mul_comm (2 ^ (a - 1)) 2]
    exact Nat.mul_div_right (2 ^ (a - 1)) (by norm_num : 0 < 2)
  have hn_eq : n = t ^ (orderOf t / 2) := by
    rw [show n = t ^ (2 ^ (a - 1)) from rfl, h2a]
  have hn_order : orderOf n = 2 := by
    rw [hn_eq]
    exact orderOf_pow_orderOf_div (x := t) (n := 2) (ne_of_gt (orderOf_pos t))
      (by rw [ht_order]; exact dvd_pow_self 2 (by omega : a ≠ 0))
  have hn_sq : n * n = 1 := by
    have hpow := pow_orderOf_eq_one n
    rw [hn_order] at hpow
    simpa [sq] using hpow
  have hn_ne : n ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hn_order
    norm_num at hn_order
  have hn_mem : n ∈ σ.ker := by
    rw [MonoidHom.mem_ker]
    calc σ n = (σ t) ^ (2 ^ (a - 1)) := by
          rw [show n = t ^ (2 ^ (a - 1)) from rfl, map_pow]
      _ = doubleTransposition ^ (2 ^ (a - 1)) := by rw [hσt]
      _ = 1 := by
          have heven : 2 ∣ 2 ^ (a - 1) := by
            rw [show a - 1 = (a - 2) + 1 by omega, pow_succ]
            exact dvd_mul_left 2 (2 ^ (a - 2))
          obtain ⟨k, hk⟩ := heven
          rw [hk, pow_mul, pow_two, doubleTransposition_sq, one_pow]
  have hn4 : ∀ v ∈ W 4, ρ n v = v :=
    rho_pow_apply_eq_self (ρ := ρ) (W := W) ht4 (2 ^ (a - 1))
  exact ⟨n, hn_sq, hn_mem, hn_ne, hn4, rfl⟩

private lemma two_part_sq_eq_one (h2 : (2 : 𝕜) ≠ 0)
    (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hWind : iSupIndep W) (hWtop : ⨆ i, W i = ⊤)
    (hfaith : Function.Injective ρ) (hσ : σ.range = alternatingGroup (Fin 6))
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3)
    (t : Γ) (a : ℕ) (ha : 1 ≤ a) (ht_order : orderOf t = 2 ^ a)
    (hσt : σ t = doubleTransposition) (ht_ne : t ≠ 1)
    (ht4 : ∀ v ∈ W 4, ρ t v = v) : t * t = 1 := by
  by_contra hne
  have ha2 : 2 ≤ a := by
    by_contra h
    have ha1 : a = 1 := by omega
    exact hne (by
      have hord : orderOf t = 2 := by rw [ht_order, ha1]; norm_num
      have hpow := pow_orderOf_eq_one t
      rw [hord] at hpow
      simpa [sq] using hpow)
  obtain ⟨n, hn_sq, hn_mem, hn_ne, hn4, -⟩ :=
    exists_odd_power_involution (ρ := ρ) (W := W) (σ := σ) h1 t a ha ha2 ht_order hσt ht4
  let nN : σ.ker := ⟨n, hn_mem⟩
  have hnN2 : nN * nN = 1 := by
    apply Subtype.ext
    exact hn_sq
  have hdich := involution_dichotomy (ρ := ρ) (W := W) (σ := σ) h2 h1 hσW hWind hWtop
    hfaith hσ hr3 nN hnN2
  rcases hdich with h1' | hminus
  · exact hn_ne (congrArg Subtype.val h1')
  · obtain ⟨v, hvW, hv0⟩ := exists_nonzero_mem_line (W := W) h1 4
    have hneg : ρ n v = (-1 : 𝕜) • v := by
      have h := chi_spec ρ W σ h1 hσW 4 nN v hvW
      rw [hminus 4] at h
      simpa using h
    have hpos := hn4 v hvW
    rw [hneg] at hpos
    have hnegv : -v = v := by simpa using hpos
    have h2v : (2 : 𝕜) • v = 0 := by
      have hsum : v + v = 0 := by
        calc v + v = (-v) + v := by rw [hnegv]
          _ = 0 := neg_add_cancel v
      simpa [two_smul] using hsum
    rcases smul_eq_zero.mp h2v with h | h
    · exact absurd h h2
    · exact hv0 h

private lemma exists_two_part_data (q : Γ) (hqσ : σ q = doubleTransposition)
    (hq4 : ∀ v ∈ W 4, ρ q v = v) (hq5 : ∀ v ∈ W 5, ρ q v = v) :
    ∃ (t : Γ) (a : ℕ), 1 ≤ a ∧ orderOf t = 2 ^ a ∧ σ t = doubleTransposition ∧
      t ≠ 1 ∧ (∀ v ∈ W 4, ρ t v = v) ∧ (∀ v ∈ W 5, ρ t v = v) := by
  obtain ⟨a, r, hrOdd, horder⟩ := Nat.exists_eq_two_pow_mul_odd
    (ne_of_gt (orderOf_pos q))
  let t : Γ := q ^ r
  have hrpos : 0 < r := by
    rcases hrOdd with ⟨k, hk⟩
    omega
  have hgcd : Nat.gcd (orderOf q) r = r := by
    rw [horder, Nat.mul_comm (2 ^ a) r]
    exact Nat.gcd_eq_right (dvd_mul_right r (2 ^ a))
  have hdiv : orderOf q / r = 2 ^ a := by
    rw [horder, Nat.mul_comm (2 ^ a) r]
    exact Nat.mul_div_right (2 ^ a) hrpos
  have ht_order : orderOf t = 2 ^ a := by
    rw [show t = q ^ r from rfl, orderOf_pow, hgcd, hdiv]
  have hσt : σ t = doubleTransposition := by
    rw [show t = q ^ r from rfl, map_pow, hqσ]
    rcases hrOdd with ⟨k, hk⟩
    rw [hk, pow_succ, pow_mul, pow_two, doubleTransposition_sq, one_pow, one_mul]
  have ht_ne : t ≠ 1 := by
    intro h
    rw [h, map_one] at hσt
    exact doubleTransposition_ne_one hσt.symm
  have ha_pos : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    apply ht_ne
    exact orderOf_eq_one_iff.mp (by rw [ht_order, ha0, pow_zero])
  have ht4 : ∀ v ∈ W 4, ρ t v = v := rho_pow_apply_eq_self (ρ := ρ) (W := W) hq4 r
  have ht5 : ∀ v ∈ W 5, ρ t v = v := rho_pow_apply_eq_self (ρ := ρ) (W := W) hq5 r
  exact ⟨t, a, ha_pos, ht_order, hσt, ht_ne, ht4, ht5⟩

private lemma exists_two_part_involution (h2 : (2 : 𝕜) ≠ 0)
    (h1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hWind : iSupIndep W) (hWtop : ⨆ i, W i = ⊤)
    (hfaith : Function.Injective ρ) (hσ : σ.range = alternatingGroup (Fin 6))
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3)
    (q : Γ) (hqσ : σ q = doubleTransposition)
    (hq4 : ∀ v ∈ W 4, ρ q v = v) (hq5 : ∀ v ∈ W 5, ρ q v = v) :
    ∃ t : Γ, t * t = 1 ∧ t ≠ 1 ∧ σ t = doubleTransposition ∧
      (∀ v ∈ W 4, ρ t v = v) ∧ (∀ v ∈ W 5, ρ t v = v) := by
  obtain ⟨t, a, ha, ht_order, hσt, ht_ne, ht4, ht5⟩ :=
    exists_two_part_data (ρ := ρ) (W := W) (σ := σ) q hqσ hq4 hq5
  have ht2 := two_part_sq_eq_one (ρ := ρ) (W := W) (σ := σ) h2 h1 hσW hWind hWtop
    hfaith hσ hr3 t a ha ht_order hσt ht_ne ht4
  exact ⟨t, ht2, ht_ne, hσt, ht4, ht5⟩

theorem false_of_monomial_six {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    {Γ : Type*} [Group Γ] [Finite Γ]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (hfaith : Function.Injective ρ)
    (W : Fin 6 → Submodule 𝕜 V) (hW1 : ∀ i, Module.finrank 𝕜 (W i) = 1)
    (hWind : iSupIndep W) (hWtop : ⨆ i, W i = ⊤)
    (σ : Γ →* Equiv.Perm (Fin 6)) (hσW : ∀ g i, (W i).map (ρ g) = W (σ g i))
    (hσ : σ.range = alternatingGroup (Fin 6))
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3) : False := by
  obtain ⟨q, hqσ, hq4, hq5⟩ := exists_commutator_q (ρ := ρ) (W := W) (σ := σ) hW1 hσW hσ
  obtain ⟨t, ht2, ht_ne, hσt, ht4, ht5⟩ :=
    exists_two_part_involution (ρ := ρ) (W := W) (σ := σ) h2 hW1 hσW hWind hWtop hfaith
      hσ hr3 q hqσ hq4 hq5
  have hmap01 : (W 0).map (ρ t) = W 1 := by
    rw [hσW, hσt, doubleTransposition_zero]
  have hmap23 : (W 2).map (ρ t) = W 3 := by
    rw [hσW, hσt, doubleTransposition_two]
  have hle := four_le_finrank_ker_of_swap_shape (ρ := ρ) (W := W) hW1 hWind t ht2 ht4
    ht5 hmap01 hmap23
  have hpg : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by simpa [sq] using ht2)
  have hle3 := hr3 t hpg ht_ne
  omega

end CFSG.RankThree.PartTwo.Sec16.Kcd166
