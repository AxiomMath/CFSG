module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private def ggQ2d6l_e (i : Fin 6) : Fin 6 → ZMod 3 := Pi.single i 1

private lemma ggQ2d6l_e_sum (i : Fin 6) :
    (∑ j : Fin 6, ggQ2d6l_e i j) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp [ggQ2d6l_e]
  · intro j _ hj
    simp [ggQ2d6l_e, Ne.symm hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2d6l_e_sub_mem (i : Fin 6) :
    (ggQ2d6l_e i - ggQ2d6l_e 0) ∈ d6SumZero := by
  rw [d6SumZero, LinearMap.mem_ker]
  simp only [LinearMap.sum_apply, LinearMap.proj_apply, Pi.sub_apply]
  have hsplit : (∑ d : Fin 6, (ggQ2d6l_e i d - ggQ2d6l_e 0 d)) =
      (∑ d : Fin 6, ggQ2d6l_e i d) - (∑ d : Fin 6, ggQ2d6l_e 0 d) :=
    Finset.sum_sub_distrib (s := Finset.univ) (f := fun d => ggQ2d6l_e i d)
      (g := fun d => ggQ2d6l_e 0 d)
  rw [hsplit, ggQ2d6l_e_sum i, ggQ2d6l_e_sum 0, sub_self]

private def ggQ2d6l_gen (i : Fin 6) : d6SumZero :=
  ⟨ggQ2d6l_e i - ggQ2d6l_e 0, ggQ2d6l_e_sub_mem i⟩

private lemma ggQ2d6l_decomp (v : Fin 6 → ZMod 3) (hv : v ∈ d6SumZero) :
    v = ∑ i : Fin 6, v i • (ggQ2d6l_e i - ggQ2d6l_e 0) := by
  have hsum : ∑ i : Fin 6, v i = 0 := by
    simpa [d6SumZero, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply] using hv
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub]
  have hsplit : (∑ x : Fin 6, (v x * ggQ2d6l_e x j - v x * ggQ2d6l_e 0 j)) =
      (∑ x : Fin 6, v x * ggQ2d6l_e x j) - (∑ x : Fin 6, v x * ggQ2d6l_e 0 j) :=
    Finset.sum_sub_distrib (s := Finset.univ) (f := fun x => v x * ggQ2d6l_e x j)
      (g := fun x => v x * ggQ2d6l_e 0 j)
  rw [hsplit]
  have h1 : ∑ i : Fin 6, v i * ggQ2d6l_e i j = v j := by
    rw [Finset.sum_eq_single j]
    · simp [ggQ2d6l_e]
    · intro i _ hij
      simp [ggQ2d6l_e, Ne.symm hij]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have h2 : ∑ i : Fin 6, v i * ggQ2d6l_e 0 j = 0 := by
    rw [← Finset.sum_mul, hsum, zero_mul]
  rw [h1, h2]
  ring

private lemma ggQ2d6l_gen_decomp (m : d6SumZero) :
    m = ∑ i : Fin 6, (m : Fin 6 → ZMod 3) i • ggQ2d6l_gen i := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, ggQ2d6l_gen]
  exact ggQ2d6l_decomp (m : Fin 6 → ZMod 3) m.2

private lemma ggQ2d6l_d6PermAct_e (σ : Equiv.Perm (Fin 6)) (a : Fin 6) :
    d6PermAct σ (ggQ2d6l_e a) = ggQ2d6l_e (σ a) := by
  funext j
  change (ggQ2d6l_e a) (σ.symm j) = (ggQ2d6l_e (σ a)) j
  rw [ggQ2d6l_e, ggQ2d6l_e, Pi.single_apply, Pi.single_apply]
  by_cases h : j = σ a
  · subst h
    simp
  · have h' : σ.symm j ≠ a := by
      intro hh
      have : j = σ a := by rw [← hh]; simp
      exact h this
    simp [h, h']

private lemma ggQ2d6l_arith (u v : ZMod 3) : u - v - (v - u) = v - u := by
  revert u v; decide +kernel

private lemma ggQ2d6l_swap_gen (i : Fin 6) :
    d6PermAct (Equiv.swap i 0) (ggQ2d6l_gen i : Fin 6 → ZMod 3) -
        (ggQ2d6l_gen i : Fin 6 → ZMod 3) = (ggQ2d6l_gen i : Fin 6 → ZMod 3) := by
  show d6PermAct (Equiv.swap i 0) (ggQ2d6l_e i - ggQ2d6l_e 0) -
      (ggQ2d6l_e i - ggQ2d6l_e 0) = ggQ2d6l_e i - ggQ2d6l_e 0
  rw [map_sub, ggQ2d6l_d6PermAct_e, ggQ2d6l_d6PermAct_e, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  ext j
  simp only [Pi.sub_apply]
  exact ggQ2d6l_arith (ggQ2d6l_e 0 j) (ggQ2d6l_e i j)

private lemma ggQ2d6l_z_diff_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V) (hzc : ∀ σ, z * Dm.ρ σ = Dm.ρ σ * z)
    (m : d6SumZero) (σ : Equiv.Perm (Fin 6)) :
    z (Dm.μ ⟨d6PermAct σ (m : Fin 6 → ZMod 3) - (m : Fin 6 → ZMod 3),
      Submodule.sub_mem _ (d6PermAct_mem σ m.2) m.2⟩) ∈ LinearMap.range Dm.μ := by
  let := Submodule.addCommGroup d6SumZero
  let m' : d6SumZero := ⟨d6PermAct σ (m : Fin 6 → ZMod 3) - (m : Fin 6 → ZMod 3),
    Submodule.sub_mem _ (d6PermAct_mem σ m.2) m.2⟩
  let a : d6SumZero := ⟨d6PermAct σ (m : Fin 6 → ZMod 3), d6PermAct_mem σ m.2⟩
  have hcomm : Dm.ρ σ (z (Dm.μ m)) = z (Dm.ρ σ (Dm.μ m)) := by
    have h := congrArg (fun (e : V ≃ₗ[ZMod 3] V) => e (Dm.μ m)) (hzc σ)
    simpa [LinearEquiv.mul_apply] using h.symm
  have hgoal : Dm.ρ σ (z (Dm.μ m)) - z (Dm.μ m) = z (Dm.μ m') := by
    rw [hcomm, Dm.μ_comm σ m]
    have hm' : m' = a - m := Subtype.ext rfl
    rw [hm', map_sub, ← map_sub]
  rw [← hgoal]
  exact Dm.triv σ (z (Dm.μ m))

private lemma ggQ2d6l_z_mem_range {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V) (hzc : ∀ σ, z * Dm.ρ σ = Dm.ρ σ * z)
    (m : d6SumZero) : z (Dm.μ m) ∈ LinearMap.range Dm.μ := by
  have hgen : ∀ i : Fin 6, z (Dm.μ (ggQ2d6l_gen i)) ∈ LinearMap.range Dm.μ := by
    intro i
    have h := ggQ2d6l_z_diff_mem Dm z hzc (ggQ2d6l_gen i) (Equiv.swap i 0)
    have heq : (⟨d6PermAct (Equiv.swap i 0) (ggQ2d6l_gen i : Fin 6 → ZMod 3) -
        (ggQ2d6l_gen i : Fin 6 → ZMod 3),
        Submodule.sub_mem _ (d6PermAct_mem (Equiv.swap i 0) (ggQ2d6l_gen i).2)
          (ggQ2d6l_gen i).2⟩ : d6SumZero) = ggQ2d6l_gen i :=
      Subtype.ext (ggQ2d6l_swap_gen i)
    rwa [heq] at h
  rw [ggQ2d6l_gen_decomp m]
  simp only [map_sum, map_smul]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hgen i))

private lemma ggQ2d6l_e_sub_mem' (i j : Fin 6) :
    (ggQ2d6l_e i - ggQ2d6l_e j) ∈ d6SumZero := by
  rw [d6SumZero, LinearMap.mem_ker]
  simp only [LinearMap.sum_apply, LinearMap.proj_apply, Pi.sub_apply]
  have hsplit : (∑ d : Fin 6, (ggQ2d6l_e i d - ggQ2d6l_e j d)) =
      (∑ d : Fin 6, ggQ2d6l_e i d) - (∑ d : Fin 6, ggQ2d6l_e j d) :=
    Finset.sum_sub_distrib (s := Finset.univ) (f := fun d => ggQ2d6l_e i d)
      (g := fun d => ggQ2d6l_e j d)
  rw [hsplit, ggQ2d6l_e_sum i, ggQ2d6l_e_sum j, sub_self]

private def ggQ2d6l_diff (i j : Fin 6) : d6SumZero :=
  ⟨ggQ2d6l_e i - ggQ2d6l_e j, ggQ2d6l_e_sub_mem' i j⟩

private noncomputable def ggQ2d6l_z0 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V)
    (h1 : ∀ m : d6SumZero, z (Dm.μ m) ∈ LinearMap.range Dm.μ) :
    d6SumZero →ₗ[ZMod 3] d6SumZero where
  toFun m := Classical.choose (LinearMap.mem_range.mp (h1 m))
  map_add' m n := by
    apply Dm.μ_inj
    have hL : Dm.μ (Classical.choose (LinearMap.mem_range.mp (h1 (m + n)))) =
        z (Dm.μ (m + n)) := Classical.choose_spec (LinearMap.mem_range.mp (h1 (m + n)))
    have hR : Dm.μ (Classical.choose (LinearMap.mem_range.mp (h1 m)) +
        Classical.choose (LinearMap.mem_range.mp (h1 n))) =
        z (Dm.μ m) + z (Dm.μ n) := by
      rw [map_add, Classical.choose_spec (LinearMap.mem_range.mp (h1 m)),
        Classical.choose_spec (LinearMap.mem_range.mp (h1 n))]
    rw [hL, hR, map_add, map_add]
  map_smul' c m := by
    apply Dm.μ_inj
    have hL : Dm.μ (Classical.choose (LinearMap.mem_range.mp (h1 (c • m)))) =
        z (Dm.μ (c • m)) := Classical.choose_spec (LinearMap.mem_range.mp (h1 (c • m)))
    have hR : Dm.μ (c • Classical.choose (LinearMap.mem_range.mp (h1 m))) =
        c • z (Dm.μ m) := by
      rw [map_smul, Classical.choose_spec (LinearMap.mem_range.mp (h1 m))]
    rw [hL]
    simp only [RingHom.id_apply]
    rw [hR, map_smul, map_smul]

private lemma ggQ2d6l_z0_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V)
    (h1 : ∀ m : d6SumZero, z (Dm.μ m) ∈ LinearMap.range Dm.μ) (m : d6SumZero) :
    Dm.μ (ggQ2d6l_z0 Dm z h1 m) = z (Dm.μ m) :=
  Classical.choose_spec (LinearMap.mem_range.mp (h1 m))

private lemma ggQ2d6l_z_rho {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V) (hzc : ∀ σ, z * Dm.ρ σ = Dm.ρ σ * z)
    (σ : Equiv.Perm (Fin 6)) (v : V) :
    Dm.ρ σ (z v) = z (Dm.ρ σ v) := by
  have h := congrArg (fun (e : V ≃ₗ[ZMod 3] V) => e v) (hzc σ)
  simpa [LinearEquiv.mul_apply] using h.symm

private lemma ggQ2d6l_z0_perm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V) (hzc : ∀ σ, z * Dm.ρ σ = Dm.ρ σ * z)
    (h1 : ∀ m : d6SumZero, z (Dm.μ m) ∈ LinearMap.range Dm.μ)
    (σ : Equiv.Perm (Fin 6)) (m : d6SumZero) :
    ggQ2d6l_z0 Dm z h1 ⟨d6PermAct σ (m : Fin 6 → ZMod 3),
        d6PermAct_mem σ m.2⟩ =
      ⟨d6PermAct σ ((ggQ2d6l_z0 Dm z h1 m : d6SumZero) : Fin 6 → ZMod 3),
        d6PermAct_mem σ (ggQ2d6l_z0 Dm z h1 m).2⟩ := by
  apply Dm.μ_inj
  rw [ggQ2d6l_z0_apply, ← Dm.μ_comm σ (ggQ2d6l_z0 Dm z h1 m), ggQ2d6l_z0_apply,
    ggQ2d6l_z_rho Dm z hzc, Dm.μ_comm]

private lemma ggQ2d6l_z0_involution {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V)
    (h1 : ∀ m : d6SumZero, z (Dm.μ m) ∈ LinearMap.range Dm.μ) (hz2 : z * z = 1)
    (m : d6SumZero) :
    ggQ2d6l_z0 Dm z h1 (ggQ2d6l_z0 Dm z h1 m) = m := by
  apply Dm.μ_inj
  rw [ggQ2d6l_z0_apply, ggQ2d6l_z0_apply]
  have h := congrArg (fun (e : V ≃ₗ[ZMod 3] V) => e (Dm.μ m)) hz2
  simpa [LinearEquiv.mul_apply] using h

private lemma ggQ2d6l_eq_neg_self (x : ZMod 3) : x = -x → x = 0 := by
  revert x; decide +kernel

private lemma ggQ2d6l_one_sub_zero : (1 : ZMod 3) - 0 = 1 := by
  decide +kernel

private lemma ggQ2d6l_neg_fixed (w : d6SumZero)
    (hw : d6PermAct (Equiv.swap 0 1) (w : Fin 6 → ZMod 3) = - (w : Fin 6 → ZMod 3)) :
    (w : Fin 6 → ZMod 3) = (w : Fin 6 → ZMod 3) 0 • (ggQ2d6l_e 0 - ggQ2d6l_e 1) := by
  funext j
  have h := congrFun hw j
  change (w : Fin 6 → ZMod 3) ((Equiv.swap 0 1) j) = - (w : Fin 6 → ZMod 3) j at h
  by_cases hj0 : j = 0
  · subst hj0
    simp [ggQ2d6l_e, ggQ2d6l_one_sub_zero]
  · by_cases hj1 : j = 1
    · subst hj1
      have h0 := congrFun hw 0
      change (w : Fin 6 → ZMod 3) ((Equiv.swap 0 1) 0) = - (w : Fin 6 → ZMod 3) 0 at h0
      rw [Equiv.swap_apply_left] at h0
      rw [h0]
      simp [ggQ2d6l_e]
      rfl
    · have hjj : (Equiv.swap 0 1) j = j :=
        Equiv.swap_apply_of_ne_of_ne hj0 hj1
      rw [hjj] at h
      have hzero : (w : Fin 6 → ZMod 3) j = 0 := ggQ2d6l_eq_neg_self _ h
      rw [hzero]
      simp [ggQ2d6l_e, hj0, hj1]

private lemma ggQ2d6l_z0_scalar {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V) (hzc : ∀ σ, z * Dm.ρ σ = Dm.ρ σ * z)
    (hz2 : z * z = 1)
    (h1 : ∀ m : d6SumZero, z (Dm.μ m) ∈ LinearMap.range Dm.μ) :
    ∃ a : ZMod 3, a * a = 1 ∧
      ∀ m : d6SumZero, ggQ2d6l_z0 Dm z h1 m = a • m := by
  classical
  let := Submodule.addCommGroup d6SumZero
  let w : d6SumZero := ggQ2d6l_z0 Dm z h1 (ggQ2d6l_diff 0 1)
  have hperm : (⟨d6PermAct (Equiv.swap 0 1) (ggQ2d6l_diff 0 1 : Fin 6 → ZMod 3),
      d6PermAct_mem (Equiv.swap 0 1) (ggQ2d6l_diff 0 1).2⟩ : d6SumZero) =
      - ggQ2d6l_diff 0 1 := by
    apply Subtype.ext
    show d6PermAct (Equiv.swap 0 1) (ggQ2d6l_e 0 - ggQ2d6l_e 1) =
      -(ggQ2d6l_e 0 - ggQ2d6l_e 1)
    rw [map_sub, ggQ2d6l_d6PermAct_e, ggQ2d6l_d6PermAct_e, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    funext j
    simp only [Pi.sub_apply, Pi.neg_apply]
    abel
  have hw : d6PermAct (Equiv.swap 0 1) (w : Fin 6 → ZMod 3) = - (w : Fin 6 → ZMod 3) := by
    have gz := ggQ2d6l_z0_perm Dm z hzc h1 (Equiv.swap 0 1) (ggQ2d6l_diff 0 1)
    rw [hperm, map_neg] at gz
    have hcoe : ((-w : d6SumZero) : Fin 6 → ZMod 3) = -(w : Fin 6 → ZMod 3) :=
      Submodule.coe_neg d6SumZero w
    rw [← hcoe]
    exact congrArg (fun x : d6SumZero => (x : Fin 6 → ZMod 3)) gz.symm
  have hw_extr := ggQ2d6l_neg_fixed w hw
  set a : ZMod 3 := (w : Fin 6 → ZMod 3) 0 with ha
  have hw_a : w = a • ggQ2d6l_diff 0 1 := by
    apply Subtype.ext
    simpa [ha, Submodule.coe_smul, ggQ2d6l_diff] using hw_extr
  have hgen : ∀ i : Fin 6, ggQ2d6l_z0 Dm z h1 (ggQ2d6l_gen i) = a • ggQ2d6l_gen i := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have hgen0 : ggQ2d6l_gen (0 : Fin 6) = 0 := Subtype.ext (sub_self (ggQ2d6l_e 0))
      rw [hgen0, map_zero, smul_zero]
    · let τ : Equiv.Perm (Fin 6) := Equiv.swap 0 i * Equiv.swap i 1
      have hτ0 : τ 0 = i := by
        show (Equiv.swap 0 i * Equiv.swap i 1) 0 = i
        rw [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (by decide : (0 : Fin 6) ≠ 1),
          Equiv.swap_apply_left]
      have hτ1 : τ 1 = 0 := by
        show (Equiv.swap 0 i * Equiv.swap i 1) 1 = 0
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
      have hd : d6PermAct τ (ggQ2d6l_diff 0 1 : Fin 6 → ZMod 3) = ggQ2d6l_gen i := by
        show d6PermAct τ (ggQ2d6l_e 0 - ggQ2d6l_e 1) = ggQ2d6l_e i - ggQ2d6l_e 0
        rw [map_sub, ggQ2d6l_d6PermAct_e, ggQ2d6l_d6PermAct_e, hτ0, hτ1]
        rfl
      have harg : (⟨d6PermAct τ (ggQ2d6l_diff 0 1 : Fin 6 → ZMod 3),
          d6PermAct_mem τ (ggQ2d6l_diff 0 1).2⟩ : d6SumZero) = ggQ2d6l_gen i :=
        Subtype.ext hd
      have hμτ : Dm.μ (ggQ2d6l_gen i) = Dm.ρ τ (Dm.μ (ggQ2d6l_diff 0 1)) := by
        rw [Dm.μ_comm τ (ggQ2d6l_diff 0 1)]
        exact (congrArg Dm.μ harg).symm
      have hμa : z (Dm.μ (ggQ2d6l_diff 0 1)) = a • Dm.μ (ggQ2d6l_diff 0 1) := by
        rw [← ggQ2d6l_z0_apply Dm z h1 (ggQ2d6l_diff 0 1)]
        rw [show ggQ2d6l_z0 Dm z h1 (ggQ2d6l_diff 0 1) = a • ggQ2d6l_diff 0 1 from hw_a,
          map_smul]
      apply Dm.μ_inj
      rw [ggQ2d6l_z0_apply, map_smul, hμτ,
        ← ggQ2d6l_z_rho Dm z hzc τ (Dm.μ (ggQ2d6l_diff 0 1)), hμa, map_smul]
  have hs : ∀ m : d6SumZero, ggQ2d6l_z0 Dm z h1 m = a • m := by
    intro m
    conv_lhs => rw [ggQ2d6l_gen_decomp m]
    rw [map_sum]
    conv_rhs => rw [ggQ2d6l_gen_decomp m]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hgen i, smul_comm]
  refine ⟨a, ?_, hs⟩
  have hzz := ggQ2d6l_z0_involution Dm z h1 hz2 (ggQ2d6l_diff 0 1)
  have hzz' : ggQ2d6l_z0 Dm z h1 (ggQ2d6l_z0 Dm z h1 (ggQ2d6l_diff 0 1)) =
      (a * a) • ggQ2d6l_diff 0 1 := by
    rw [hs (ggQ2d6l_z0 Dm z h1 (ggQ2d6l_diff 0 1)), hs (ggQ2d6l_diff 0 1), smul_smul]
  have hcoord := congrArg (fun x : d6SumZero => (x : Fin 6 → ZMod 3) 0) hzz
  rw [hzz'] at hcoord
  simpa [ggQ2d6l_diff, ggQ2d6l_e, Pi.smul_apply, smul_eq_mul, ggQ2d6l_one_sub_zero]
    using hcoord

private lemma ggQ2d6l_iter_neg_on {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Equiv.Perm ι) (m : ι → ZMod 3) (hc : ∀ a ∈ c.support, m (c a) = -m a) :
    ∀ (k : ℕ) {i : ι}, i ∈ c.support → m ((c ^ k) i) = (-1 : ZMod 3) ^ k * m i := by
  have hmem : ∀ (k : ℕ) {i : ι}, i ∈ c.support → (c ^ k) i ∈ c.support := by
    intro k
    induction k with
    | zero => intro i hi; simpa using hi
    | succ k ih =>
      intro i hi
      rw [pow_succ', Equiv.Perm.mul_apply]
      have hcne : c ((c ^ k) i) ≠ (c ^ k) i := Equiv.Perm.mem_support.mp (ih hi)
      rw [Equiv.Perm.mem_support]
      intro h
      exact hcne (c.injective h)
  intro k
  induction k with
  | zero => intro i _; simp
  | succ k ih =>
    intro i hi
    rw [pow_succ', Equiv.Perm.mul_apply]
    rw [hc _ (hmem k hi)]
    rw [ih hi]
    rw [pow_succ']
    rw [mul_assoc]
    exact (neg_one_mul ((-1 : ZMod 3) ^ k * m i)).symm

private lemma ggQ2d6l_odd_vanish {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Equiv.Perm ι) (m : ι → ZMod 3) (hm : ∀ i, m (g i) = -m i)
    (i : ι) (hi : i ∈ g.support) (hodd : Odd (g.cycleOf i).support.card) : m i = 0 := by
  have hcyc : (g.cycleOf i).IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp
      ((Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).mpr hi)).1
  have hL : (g ^ (g.cycleOf i).support.card) i = i := by
    rw [← Equiv.Perm.cycleOf_pow_apply_self g i]
    rw [← Equiv.Perm.IsCycle.orderOf hcyc]
    rw [pow_orderOf_eq_one]
    rfl
  have hiter := ggQ2d6l_iter_neg_on g m (fun a _ => hm a) (g.cycleOf i).support.card hi
  rw [hL] at hiter
  have h2 : ((-1 : ZMod 3)) ^ 2 = 1 := by decide +kernel
  have hneg : ((-1 : ZMod 3) ^ (g.cycleOf i).support.card) = -1 := by
    rcases hodd with ⟨k, hk⟩
    have h3 : ((-1 : ZMod 3) ^ (2 * k + 1)) = -1 := by
      rw [pow_add, pow_mul]
      rw [h2]
      simp
    rw [hk]
    exact h3
  have hm2 : m i = -m i := by
    calc m i = (-1 : ZMod 3) ^ (g.cycleOf i).support.card * m i := hiter
      _ = (-1 : ZMod 3) * m i := by rw [hneg]
      _ = -m i := neg_one_mul (m i)
  exact ggQ2d6l_eq_neg_self _ hm2

private lemma ggQ2d6l_C_card_le {ι : Type} [Fintype ι] [DecidableEq ι] (g : Equiv.Perm ι) :
    (g.cycleFactorsFinset.filter (fun c => Even c.support.card)).card ≤ Nat.card ι / 2 := by
  classical
  set C : Finset (Equiv.Perm ι) := g.cycleFactorsFinset.filter (fun c => Even c.support.card)
    with hC
  have hpair : (↑C : Set (Equiv.Perm ι)).PairwiseDisjoint (fun c => c.support) := by
    intro a ha b hb hab
    have ha' : a ∈ g.cycleFactorsFinset := (Finset.mem_filter.mp ha).1
    have hb' : b ∈ g.cycleFactorsFinset := (Finset.mem_filter.mp hb).1
    exact Equiv.Perm.disjoint_iff_disjoint_support.mp
      ((Equiv.Perm.cycleFactorsFinset_pairwise_disjoint g) ha' hb' hab)
  have hcard : (C.biUnion (fun c => c.support)).card = ∑ c ∈ C, c.support.card :=
    Finset.card_biUnion hpair
  have hle6 : (C.biUnion (fun c => c.support)).card ≤ Nat.card ι := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have h2 : ∀ c ∈ C, 2 ≤ c.support.card := by
    intro c hc
    have hcyc : c.IsCycle :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp hc).1).1
    exact hcyc.two_le_card_support
  have hsum : 2 * C.card ≤ ∑ c ∈ C, c.support.card := by
    have := Finset.card_nsmul_le_sum C (fun c => c.support.card) 2 h2
    simpa [smul_eq_mul, mul_comm] using this
  omega

private lemma ggQ2d6l_eig_card_le_27 (g : Equiv.Perm (Fin 6)) :
    Nat.card {m : Fin 6 → ZMod 3 // (∀ i, m (g i) = -m i)} ≤ 27 := by
  classical
  set C : Finset (Equiv.Perm (Fin 6)) := g.cycleFactorsFinset.filter (fun c => Even c.support.card)
    with hC
  have hC3 : C.card ≤ 3 := by
    have := ggQ2d6l_C_card_le g
    rw [Nat.card_fin] at this
    omega
  let Φ : {m : Fin 6 → ZMod 3 // (∀ i, m (g i) = -m i)} → (↥C → ZMod 3) :=
    fun m c => m.1 (c.1.support.min' (by
      have hc := Finset.mem_filter.mp c.2
      exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc.1).1.nonempty_support))
  have hΦinj : Function.Injective Φ := by
    intro m m' hmm
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ g.support
    · let c : Equiv.Perm (Fin 6) := g.cycleOf i
      have hcmem : c ∈ g.cycleFactorsFinset :=
        (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).mpr hi
      have hci : i ∈ c.support :=
        (Equiv.Perm.mem_support_cycleOf_iff).mpr ⟨Equiv.Perm.SameCycle.refl g i, hi⟩
      have hcyc : c.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcmem).1
      have hmin : c.support.Nonempty := hcyc.nonempty_support
      by_cases heven : Even c.support.card
      · have hcC : c ∈ C := Finset.mem_filter.mpr ⟨hcmem, heven⟩
        have hs : c.support.min' hmin ∈ c.support := Finset.min'_mem _ _
        obtain ⟨k, hk⟩ := hcyc.exists_pow_eq (Equiv.Perm.mem_support.mp hs)
          (Equiv.Perm.mem_support.mp hci)
        have hcm : ∀ a ∈ c.support, m.1 (c a) = -m.1 a := by
          intro a ha
          rw [(Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcmem).2 a ha, m.2 a]
        have hcm' : ∀ a ∈ c.support, m'.1 (c a) = -m'.1 a := by
          intro a ha
          rw [(Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcmem).2 a ha, m'.2 a]
        have hagg : m.1 (c.support.min' hmin) = m'.1 (c.support.min' hmin) := by
          have := congrFun hmm ⟨c, hcC⟩
          simpa [Φ] using this
        rw [← hk]
        rw [ggQ2d6l_iter_neg_on c m.1 hcm k hs, ggQ2d6l_iter_neg_on c m'.1 hcm' k hs, hagg]
      · have hodd : Odd c.support.card := Nat.not_even_iff_odd.mp heven
        rw [ggQ2d6l_odd_vanish g m.1 m.2 i hi hodd, ggQ2d6l_odd_vanish g m'.1 m'.2 i hi hodd]
    · have hfix : g i = i := by
        by_contra h
        exact hi (Equiv.Perm.mem_support.mpr h)
      have h1 : m.1 i = 0 := by
        have h := m.2 i
        rw [hfix] at h
        exact ggQ2d6l_eq_neg_self _ h
      have h2 : m'.1 i = 0 := by
        have h := m'.2 i
        rw [hfix] at h
        exact ggQ2d6l_eq_neg_self _ h
      rw [h1, h2]
  have hle : Fintype.card {m : Fin 6 → ZMod 3 // (∀ i, m (g i) = -m i)} ≤
      Fintype.card (↥C → ZMod 3) := Fintype.card_le_of_injective Φ hΦinj
  rw [Fintype.card_fun, Fintype.card_coe] at hle
  have hcard3 : Fintype.card (ZMod 3) = 3 := ZMod.card 3
  rw [hcard3] at hle
  calc Nat.card {m : Fin 6 → ZMod 3 // (∀ i, m (g i) = -m i)}
      = Fintype.card {m : Fin 6 → ZMod 3 // (∀ i, m (g i) = -m i)} := Nat.card_eq_fintype_card
    _ ≤ 3 ^ C.card := hle
    _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hC3
    _ = 27 := by norm_num

private lemma ggQ2d6l_exists_ne_two : ∀ a b : Fin 6, ∃ k : Fin 6, k ≠ a ∧ k ≠ b := by
  decide +kernel

private lemma ggQ2d6l_faithful (g : Equiv.Perm (Fin 6))
    (h : ∀ m : d6SumZero, (⟨d6PermAct g (m : Fin 6 → ZMod 3),
        d6PermAct_mem g m.2⟩ : d6SumZero) = m) : g = 1 := by
  by_contra hg
  obtain ⟨i, hi⟩ : ∃ i : Fin 6, g i ≠ i := by
    by_contra h'
    rw [not_exists] at h'
    simp only [not_not] at h'
    exact hg (Equiv.ext h')
  obtain ⟨k, hki, hksymi⟩ := ggQ2d6l_exists_ne_two i (g.symm i)
  have hsym_ne : g.symm i ≠ i := by
    intro hh
    have h1 : g (g.symm i) = g i := congrArg g hh
    rw [Equiv.apply_symm_apply] at h1
    exact hi h1.symm
  have hm := h (ggQ2d6l_diff i k)
  have heval := congrArg (fun x : d6SumZero => (x : Fin 6 → ZMod 3) i) hm
  change (↑(ggQ2d6l_diff i k) : Fin 6 → ZMod 3) (g.symm i) =
      (↑(ggQ2d6l_diff i k) : Fin 6 → ZMod 3) i at heval
  simp only [ggQ2d6l_diff, ggQ2d6l_e, Pi.sub_apply, Pi.single_apply] at heval
  simp only [hsym_ne, Ne.symm hksymi, Ne.symm hki, if_false, if_true, zero_sub] at heval
  exact absurd heval (by decide)

private def ggQ2d6l_fixA {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : V ≃ₗ[ZMod 3] V) : AddSubgroup V where
  carrier := {v | f v = v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    simp only [Set.mem_setOf_eq, map_add, hx, hy]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq, map_neg, hx]

private def ggQ2d6l_negA {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : V ≃ₗ[ZMod 3] V) : AddSubgroup V where
  carrier := {v | f v = -v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    simp only [Set.mem_setOf_eq, map_add, hx, hy, neg_add]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq, map_neg, hx, neg_neg]

private lemma ggQ2d6l_sq_eq_one : ∀ a : ZMod 3, a * a = 1 → a = 1 ∨ a = -1 := by
  decide +kernel

private instance ggQ2d6l_d6SumZero_addCommGroup : AddCommGroup d6SumZero :=
  Submodule.addCommGroup d6SumZero

private lemma ggQ2d6l_neg_comm (x y : ZMod 3) : x = -y → y = -x := by
  revert x y; decide +kernel

private lemma ggQ2d6l_neg_one_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (v : V) :
    (-1 : ZMod 3) • v = -v := neg_one_smul (ZMod 3) v

private lemma ggQ2d6l_eq_neg_self_vec {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (x : V) (h : x = -x) : x = 0 := by
  have hxx : x + x = 0 := (congrArg (fun y => x + y) h).trans (add_neg_cancel x)
  have h2 : (2 : ZMod 3) • x = 0 := by
    rw [show (2 : ZMod 3) = 1 + 1 from by decide +kernel, add_smul, one_smul]
    exact hxx
  rcases smul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 (by decide)
  · exact h0

private lemma ggQ2d6l_sumZero_card : Nat.card d6SumZero = 243 := by
  have h : (Finset.univ.filter (fun v : Fin 6 → ZMod 3 => ∑ i, v i = 0)).card = 243 := by
    decide +kernel
  have heq : d6SumZero ≃ {v : Fin 6 → ZMod 3 // ∑ i, v i = 0} :=
    Equiv.subtypeEquivRight (fun v => by
      simp [d6SumZero, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply])
  rw [Nat.card_congr heq, Nat.card_eq_fintype_card]
  change Fintype.card (↥{v : Fin 6 → ZMod 3 | ∑ i, v i = 0} : Type) = 243
  rw [Fintype.card_ofFinset (Finset.univ.filter (fun v : Fin 6 → ZMod 3 => ∑ i, v i = 0))
    (fun x => by simp)]
  exact h

private lemma ggQ2d6l_M0_card {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Dm : D6Mod V) : Nat.card (LinearMap.range Dm.μ).toAddSubgroup = 243 := by
  have he : d6SumZero ≃ (LinearMap.range Dm.μ).toAddSubgroup :=
    (LinearEquiv.ofInjective Dm.μ Dm.μ_inj).toEquiv
  rw [← Nat.card_congr he, ggQ2d6l_sumZero_card]

private lemma ggQ2d6l_eig_card_le_27_perm (g : Equiv.Perm (Fin 6)) :
    Nat.card {m : Fin 6 → ZMod 3 // d6PermAct g m = -m} ≤ 27 := by
  have heq : Nat.card {m : Fin 6 → ZMod 3 // d6PermAct g m = -m} =
      Nat.card {m : Fin 6 → ZMod 3 // (∀ i, m (g i) = -m i)} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun m => ?_)
    constructor
    · intro hm i
      have h := congrFun hm (g i)
      change m (g.symm (g i)) = -m (g i) at h
      rw [Equiv.symm_apply_apply] at h
      exact ggQ2d6l_neg_comm _ _ h
    · intro hm
      funext i
      change m (g.symm i) = -m i
      have h := hm (g.symm i)
      rw [Equiv.apply_symm_apply] at h
      exact ggQ2d6l_neg_comm _ _ h
  rw [heq]
  exact ggQ2d6l_eig_card_le_27 g

private def ggQ2d6l_embed (g : Equiv.Perm (Fin 6)) :
    {m : d6SumZero // (⟨d6PermAct g (m : Fin 6 → ZMod 3),
        d6PermAct_mem g m.2⟩ : d6SumZero) = -m} →
    {m : Fin 6 → ZMod 3 // d6PermAct g m = -m} :=
  fun m => ⟨(m.1 : Fin 6 → ZMod 3), by
    have h2 := congrArg (fun x : d6SumZero => (x : Fin 6 → ZMod 3)) m.2
    have hcoe : ((-m : d6SumZero) : Fin 6 → ZMod 3) = -(m.1 : Fin 6 → ZMod 3) :=
      Submodule.coe_neg d6SumZero m
    rwa [hcoe] at h2⟩

private lemma ggQ2d6l_embed_inj (g : Equiv.Perm (Fin 6)) :
    Function.Injective (ggQ2d6l_embed g) := by
  intro a b hab
  have h1 : (a.1 : Fin 6 → ZMod 3) = (b.1 : Fin 6 → ZMod 3) :=
    congrArg (fun x : {m : Fin 6 → ZMod 3 // d6PermAct g m = -m} =>
      (x.1 : Fin 6 → ZMod 3)) hab
  exact Subtype.ext (Subtype.ext h1)

private lemma ggQ2d6l_E_card_le_27 (g : Equiv.Perm (Fin 6)) :
    Nat.card {m : d6SumZero // (⟨d6PermAct g (m : Fin 6 → ZMod 3),
        d6PermAct_mem g m.2⟩ : d6SumZero) = -m} ≤ 27 :=
  le_trans (Nat.card_le_card_of_injective _ (ggQ2d6l_embed_inj g))
    (ggQ2d6l_eig_card_le_27_perm g)

theorem ggQ2d6l_refl_mul_central {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (Dm : D6Mod V) (z : V ≃ₗ[ZMod 3] V) (g : Equiv.Perm (Fin 6)) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzc : ∀ σ, z * Dm.ρ σ = Dm.ρ σ * z) (hs : IsRefl3 (Dm.ρ g * z)) : g = 1 := by
  classical
  let s : V ≃ₗ[ZMod 3] V := Dm.ρ g * z
  have hsz : s * z = z * s := by
    have h1 : s * z = Dm.ρ g := by rw [show s = Dm.ρ g * z from rfl, mul_assoc, hz2, mul_one]
    have h2 : z * s = Dm.ρ g := by
      rw [show s = Dm.ρ g * z from rfl, ← mul_assoc, hzc g, mul_assoc, hz2, mul_one]
    rw [h1, h2]
  let F : AddSubgroup V := ggQ2d6l_fixA s
  let Vp : AddSubgroup V := ggQ2d6l_fixA z
  let Vm : AddSubgroup V := ggQ2d6l_negA z
  let M0 : AddSubgroup V := (LinearMap.range Dm.μ).toAddSubgroup
  have h1 : ∀ m : d6SumZero, z (Dm.μ m) ∈ LinearMap.range Dm.μ :=
    fun m => ggQ2d6l_z_mem_range Dm z hzc m
  obtain ⟨a, ha_sq, ha⟩ := ggQ2d6l_z0_scalar Dm z hzc hz2 h1
  have hF_index : F.index = 3 := by
    have hFcard : Nat.card F = Nat.card {v : V // s v = v} := rfl
    have hcard : Nat.card F * 3 = Nat.card V := by rw [hFcard]; exact hs.2
    have hcm := AddSubgroup.card_mul_index F
    have hmul : Nat.card F * F.index = Nat.card F * 3 := by rw [hcm, hcard]
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F)) hmul
  have hzzv : ∀ v : V, z (z v) = v := by
    intro v
    have h := congrArg (fun (e : V ≃ₗ[ZMod 3] V) => e v) hz2
    simpa [LinearEquiv.mul_apply] using h
  rcases ggQ2d6l_sq_eq_one a ha_sq with ha1 | ha_neg
  ·
    have hzM : ∀ m : d6SumZero, z (Dm.μ m) = Dm.μ m := by
      intro m
      rw [← ggQ2d6l_z0_apply Dm z h1 m, ha m, ha1, one_smul]
    have hz_ne : ∃ v : V, z v ≠ v := by
      by_contra h
      rw [not_exists] at h
      simp only [not_not] at h
      exact hz1 (LinearEquiv.ext h)
    obtain ⟨v₀, hv₀⟩ := hz_ne
    let u : V := z v₀ - v₀
    have hu0 : u ≠ 0 := fun h => hv₀ (sub_eq_zero.mp h)
    have hzu : z u = -u := by
      show z (z v₀ - v₀) = -(z v₀ - v₀)
      rw [map_sub, hzzv v₀]
      abel
    have hu_Vm : u ∈ Vm := by
      show z u = -u
      exact hzu
    have hu_not_Vp : u ∉ Vp := by
      intro hu
      have hu' : z u = u := hu
      rw [hzu] at hu'
      exact hu0 (ggQ2d6l_eq_neg_self_vec u hu'.symm)
    have hρtriv : ∀ (σ : Equiv.Perm (Fin 6)) (w : V), w ∈ Vm → Dm.ρ σ w = w := by
      intro σ w hw
      have hw' : z w = -w := hw
      have hx : Dm.ρ σ w - w ∈ LinearMap.range Dm.μ := Dm.triv σ w
      have hzx : z (Dm.ρ σ w - w) = -(Dm.ρ σ w - w) := by
        have hzrw : z (Dm.ρ σ w) = -Dm.ρ σ w := by
          rw [← ggQ2d6l_z_rho Dm z hzc σ w, hw', map_neg]
        rw [map_sub, hzrw, hw']
        abel
      have hxzero : Dm.ρ σ w - w = 0 := by
        have hx' : z (Dm.ρ σ w - w) = Dm.ρ σ w - w := by
          obtain ⟨m0, hm0⟩ := LinearMap.mem_range.mp hx
          rw [← hm0, hzM m0]
        rw [hzx] at hx'
        exact ggQ2d6l_eq_neg_self_vec _ hx'.symm
      exact sub_eq_zero.mp hxzero
    have hsVm : ∀ w : V, w ∈ Vm → s w = -w := by
      intro w hw
      have hw' : z w = -w := hw
      rw [show s = Dm.ρ g * z from rfl, LinearEquiv.mul_apply, hw', map_neg, hρtriv g w hw]
    have hF_le_Vp : F ≤ Vp := by
      intro v hv
      have hv' : s v = v := hv
      have hzv_F : z v ∈ F := by
        show s (z v) = z v
        rw [← LinearEquiv.mul_apply, hsz, LinearEquiv.mul_apply, hv']
      have hsub_F : v - z v ∈ F := F.sub_mem hv hzv_F
      have hsub_F' : s (v - z v) = v - z v := hsub_F
      have hsub_Vm : v - z v ∈ Vm := by
        show z (v - z v) = -(v - z v)
        rw [map_sub, hzzv v]
        abel
      have hh : s (v - z v) = -(v - z v) := hsVm _ hsub_Vm
      rw [hsub_F'] at hh
      have hzero : v - z v = 0 := ggQ2d6l_eq_neg_self_vec _ hh
      show z v = v
      exact (sub_eq_zero.mp hzero).symm
    have hVp_ne_top : Vp ≠ ⊤ := by
      intro htop
      exact hu_not_Vp (htop ▸ AddSubgroup.mem_top u)
    have hFVp_eq : F = Vp := by
      have hdiv : Vp.index ∣ F.index := AddSubgroup.index_dvd_of_le hF_le_Vp
      have hdiv3 : Vp.index ∣ 3 := by rw [hF_index] at hdiv; exact hdiv
      have hne1 : Vp.index ≠ 1 := fun h1' => hVp_ne_top (AddSubgroup.index_eq_one.mp h1')
      have hVp_index : Vp.index = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h | h
        · exact absurd h hne1
        · exact h
      have : F.index ∣ Vp.index := by rw [hF_index, hVp_index]
      exact AddSubgroup.eq_of_index_dvd_index hF_le_Vp this
    have hM0_le_Vp : M0 ≤ Vp := by
      intro v hv
      obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hv
      show z (Dm.μ m) = Dm.μ m
      exact hzM m
    refine ggQ2d6l_faithful g (fun m => ?_)
    apply Dm.μ_inj
    rw [← Dm.μ_comm g m]
    have hmem : Dm.μ m ∈ Vp := hM0_le_Vp ⟨m, rfl⟩
    rw [← hFVp_eq] at hmem
    have hfix : s (Dm.μ m) = Dm.μ m := hmem
    rw [show s = Dm.ρ g * z from rfl, LinearEquiv.mul_apply, hzM m] at hfix
    exact hfix
  ·
    have hzM : ∀ m : d6SumZero, z (Dm.μ m) = -Dm.μ m := by
      intro m
      rw [← ggQ2d6l_z0_apply Dm z h1 m, ha m, ha_neg, map_smul]
      simpa only [RingHom.id_apply] using ggQ2d6l_neg_one_smul (Dm.μ m)
    have hsM : ∀ m : d6SumZero, s (Dm.μ m) =
        -Dm.μ (⟨d6PermAct g (m : Fin 6 → ZMod 3), d6PermAct_mem g m.2⟩ : d6SumZero) := by
      intro m
      rw [show s = Dm.ρ g * z from rfl, LinearEquiv.mul_apply, hzM m, map_neg, Dm.μ_comm g m]
    have hEiff : ∀ m : d6SumZero, Dm.μ m ∈ F ↔
        (⟨d6PermAct g (m : Fin 6 → ZMod 3), d6PermAct_mem g m.2⟩ : d6SumZero) = -m := by
      intro m
      have h := hsM m
      constructor
      · intro hm
        have hm' : s (Dm.μ m) = Dm.μ m := hm
        rw [h] at hm'
        apply Dm.μ_inj
        rw [map_neg]
        rw [← neg_neg (Dm.μ (⟨d6PermAct g (m : Fin 6 → ZMod 3),
          d6PermAct_mem g m.2⟩ : d6SumZero)), hm']
      · intro hm
        show s (Dm.μ m) = Dm.μ m
        rw [h, hm, map_neg, neg_neg]
    have hcard_le : Nat.card (F ⊓ M0 : AddSubgroup V) ≤ 27 := by
      have hsurj : Function.Surjective (fun m : {m : d6SumZero //
          (⟨d6PermAct g (m : Fin 6 → ZMod 3), d6PermAct_mem g m.2⟩ : d6SumZero) = -m} =>
          (⟨Dm.μ m.1, AddSubgroup.mem_inf.mpr ⟨(hEiff m.1).mpr m.2, ⟨m.1, rfl⟩⟩⟩ :
            (F ⊓ M0 : AddSubgroup V))) := by
        rintro ⟨v, hvF, hvM0⟩
        obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hvM0
        refine ⟨⟨m, ?_⟩, ?_⟩
        · rw [← hm] at hvF
          exact (hEiff m).mp hvF
        · apply Subtype.ext
          exact hm
      exact le_trans (Nat.card_le_card_of_surjective _
        (hsurj : Function.Surjective (fun m : {m : d6SumZero //
          (⟨d6PermAct g (m : Fin 6 → ZMod 3), d6PermAct_mem g m.2⟩ : d6SumZero) = -m} =>
          (⟨Dm.μ m.1, AddSubgroup.mem_inf.mpr ⟨(hEiff m.1).mpr m.2, ⟨m.1, rfl⟩⟩⟩ :
            (F ⊓ M0 : AddSubgroup V))))) (ggQ2d6l_E_card_le_27 g)
    have hrel : F.relIndex M0 * Nat.card (F ⊓ M0 : AddSubgroup V) = 243 := by
      have h := AddSubgroup.relIndex_mul_card F M0
      rw [h, ggQ2d6l_M0_card Dm]
    have hrel_dvd : F.relIndex M0 ∣ 3 := by
      have h3 : F.relIndex (F ⊔ M0) ∣ F.index :=
        AddSubgroup.relIndex_dvd_index_of_le (le_sup_left : F ≤ F ⊔ M0)
      rw [AddSubgroup.relIndex_sup_left M0 F] at h3
      rwa [hF_index] at h3
    have hrel_le : F.relIndex M0 ≤ 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hrel_dvd with h | h
      · rw [h]; norm_num
      · rw [h]
    have hle : 243 ≤ 81 := by
      rw [← hrel]
      calc F.relIndex M0 * Nat.card (F ⊓ M0 : AddSubgroup V) ≤ 3 * 27 :=
            Nat.mul_le_mul hrel_le hcard_le
        _ = 81 := by norm_num
    exact absurd hle (by norm_num)

end CFSG.StandardType

end
