module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestPerm
import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermAut
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Equiv

theorem qtwoDB32_sum_basis (m : ℕ) (v : DVec m) :
    (∑ i : Fin m, v i • dBasis m i) = v := by
  conv_rhs => rw [← Module.Basis.sum_repr (dBasis m) v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.basisFun_repr]

theorem qtwoDB32_dPerm_eval (m : ℕ) (σ : Equiv.Perm (Fin m)) (v : DVec m) (i : Fin m) :
    dPerm m σ v i = v (σ.symm i) := by
  have hlin : (LinearMap.proj i).comp (dPerm m σ : DVec m →ₗ[ZMod 3] DVec m) =
      LinearMap.proj (σ.symm i) := by
    refine (dBasis m).ext fun k => ?_
    change (dPerm m σ (dBasis m k)) i = (dBasis m k) (σ.symm i)
    rw [dPerm_apply]
    simp only [dBasis, Pi.basisFun_apply]
    by_cases h : σ k = i
    · have hk : σ.symm i = k := by rw [← h, Equiv.symm_apply_apply]
      rw [h, hk, Pi.single_eq_same, Pi.single_eq_same]
    · have hk : σ.symm i ≠ k := fun hh => h (by rw [← hh]; exact Equiv.apply_symm_apply σ i)
      rw [Pi.single_eq_of_ne (show i ≠ σ k from fun hh => h hh.symm),
        Pi.single_eq_of_ne hk]
  have := congrArg (fun f : DVec m →ₗ[ZMod 3] ZMod 3 => f v) hlin
  simpa [LinearMap.comp_apply, LinearMap.proj_apply] using this

theorem qtwoDB32_dPerm_apply_self (m : ℕ) (σ : Equiv.Perm (Fin m)) (v : DVec m)
    (i : Fin m) : dPerm m σ v (σ i) = v i := by
  rw [qtwoDB32_dPerm_eval, Equiv.symm_apply_apply]

theorem qtwoDB32_dTau_action (m : ℕ) (sgn : Bool) {a b : Fin m} (hab : a ≠ b) (i : Fin m) :
    dTau m sgn a b (dBasis m i) =
      (if sgn then (if i = a ∨ i = b then (-1 : ZMod 3) else 1) else 1) •
        dBasis m (Equiv.swap a b i) := by
  by_cases hia : i = a
  · subst hia
    rw [dTau_apply_left m sgn hab]
    cases sgn <;> simp [Equiv.swap_apply_left]
  · by_cases hib : i = b
    · subst hib
      rw [dTau_apply_right m sgn hab]
      cases sgn <;> simp [Equiv.swap_apply_right]
    · rw [dTau_apply_of_ne m sgn hia hib]
      cases sgn <;> simp [Equiv.swap_apply_of_ne_of_ne hia hib, hia, hib]

theorem qtwoDB32_smul_basis_inj {m : ℕ} {c c' : ZMod 3} {i j : Fin m}
    (hc : c ≠ 0) (h : c • dBasis m i = c' • dBasis m j) : i = j := by
  by_contra hne
  have hval := congrFun h i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hval
  simp only [dBasis, Pi.basisFun_apply] at hval
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, mul_zero, mul_one] at hval
  exact hc hval

@[expose] noncomputable def qtwoDB32_proj (m : ℕ) (g : dEven m) : Equiv.Perm (Fin m) :=
  Classical.choose g.2

theorem qtwoDB32_proj_spec (m : ℕ) (g : dEven m) :
    ∃ c : Fin m → ZMod 3, (∀ i, c i = 1 ∨ c i = -1) ∧ (∏ i, c i = 1) ∧
      ∀ i, (g : DVec m ≃ₗ[ZMod 3] DVec m) (dBasis m i) =
        c i • dBasis m (qtwoDB32_proj m g i) :=
  Classical.choose_spec g.2

theorem qtwoDB32_proj_eq_of (m : ℕ) (g : dEven m) (σ : Equiv.Perm (Fin m))
    (c : Fin m → ZMod 3) (hc : ∀ i, c i ≠ 0)
    (h : ∀ i, (g : DVec m ≃ₗ[ZMod 3] DVec m) (dBasis m i) = c i • dBasis m (σ i)) :
    qtwoDB32_proj m g = σ := by
  obtain ⟨d, hd1, _, hd⟩ := qtwoDB32_proj_spec m g
  refine Equiv.ext fun i => ?_
  have hdi : d i ≠ 0 := by
    rcases hd1 i with h' | h' <;> rw [h'] <;> decide
  have heq : d i • dBasis m (qtwoDB32_proj m g i) = c i • dBasis m (σ i) := by
    rw [← hd i, h i]
  exact qtwoDB32_smul_basis_inj hdi heq

theorem qtwoDB32_proj_mul (m : ℕ) (g h : dEven m) :
    qtwoDB32_proj m (g * h) = qtwoDB32_proj m g * qtwoDB32_proj m h := by
  obtain ⟨c, hc1, _, hc⟩ := qtwoDB32_proj_spec m g
  obtain ⟨d, hd1, _, hd⟩ := qtwoDB32_proj_spec m h
  refine qtwoDB32_proj_eq_of m (g * h) (qtwoDB32_proj m g * qtwoDB32_proj m h)
    (fun i => c (qtwoDB32_proj m h i) * d i) (fun i => ?_) (fun i => ?_)
  · exact mul_ne_zero (by rcases hc1 _ with h' | h' <;> rw [h'] <;> decide)
      (by rcases hd1 i with h' | h' <;> rw [h'] <;> decide)
  · change (g : DVec m ≃ₗ[ZMod 3] DVec m) ((h : DVec m ≃ₗ[ZMod 3] DVec m) (dBasis m i)) =
      (c (qtwoDB32_proj m h i) * d i) •
        dBasis m ((qtwoDB32_proj m g) (qtwoDB32_proj m h i))
    rw [hd i, map_smul, hc (qtwoDB32_proj m h i), smul_smul, mul_comm]

@[expose] noncomputable def qtwoDB32_projHom (m : ℕ) : dEven m →* Equiv.Perm (Fin m) where
  toFun := qtwoDB32_proj m
  map_one' := by
    refine qtwoDB32_proj_eq_of m 1 1 (fun _ => 1) (fun _ => one_ne_zero) fun i => ?_
    simp
  map_mul' := qtwoDB32_proj_mul m

theorem qtwoDB32_proj_dTau (m : ℕ) (sgn : Bool) {a b : Fin m} (hab : a ≠ b) :
    qtwoDB32_proj m ⟨dTau m sgn a b, dTau_mem_dEven m sgn hab⟩ = Equiv.swap a b := by
  refine qtwoDB32_proj_eq_of m _ (Equiv.swap a b)
    (fun i => if sgn then (if i = a ∨ i = b then (-1 : ZMod 3) else 1) else 1)
    (fun i => ?_) (fun i => ?_)
  · by_cases h : sgn
    · rw [if_pos h]
      by_cases hi : i = a ∨ i = b <;> simp [hi]
    · rw [if_neg h]
      exact one_ne_zero
  · change dTau m sgn a b (dBasis m i) = _
    rw [qtwoDB32_dTau_action m sgn hab i]

theorem qtwoDB32_phi_mem {m : ℕ}
    (φ : Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m))
    (hφ : ∀ a b : Fin m, a ≠ b → ∃ (sgn : Bool) (a' b' : Fin m), a' ≠ b' ∧
      φ (Equiv.swap a b) = dTau m sgn a' b') (σ : Equiv.Perm (Fin m)) : φ σ ∈ dEven m := by
  have hgen : Subgroup.closure {σ : Equiv.Perm (Fin m) | σ.IsSwap} ≤
      (dEven m).comap φ := by
    rw [Subgroup.closure_le]
    rintro σ ⟨a, b, hab, rfl⟩
    obtain ⟨sgn, a', b', hab', heq⟩ := hφ a b hab
    change φ (Equiv.swap a b) ∈ dEven m
    rw [heq]
    exact dTau_mem_dEven m sgn hab'
  rw [Equiv.Perm.closure_isSwap] at hgen
  exact hgen (Subgroup.mem_top σ)

@[expose] noncomputable def qtwoDB32_psi {m : ℕ}
    (φ : Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m))
    (hφ : ∀ a b : Fin m, a ≠ b → ∃ (sgn : Bool) (a' b' : Fin m), a' ≠ b' ∧
      φ (Equiv.swap a b) = dTau m sgn a' b') : Equiv.Perm (Fin m) →* Equiv.Perm (Fin m) :=
  (qtwoDB32_projHom m).comp (φ.codRestrict (dEven m) (qtwoDB32_phi_mem φ hφ))

theorem qtwoDB32_psi_swap {m : ℕ}
    (φ : Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m))
    (hφ : ∀ a b : Fin m, a ≠ b → ∃ (sgn : Bool) (a' b' : Fin m), a' ≠ b' ∧
      φ (Equiv.swap a b) = dTau m sgn a' b') {a b : Fin m} (hab : a ≠ b) :
    (qtwoDB32_psi φ hφ (Equiv.swap a b)).IsSwap := by
  obtain ⟨sgn, a', b', hab', heq⟩ := hφ a b hab
  have h1 : qtwoDB32_psi φ hφ (Equiv.swap a b) = Equiv.swap a' b' := by
    change qtwoDB32_proj m ⟨φ (Equiv.swap a b), qtwoDB32_phi_mem φ hφ _⟩ = Equiv.swap a' b'
    have helem : (⟨φ (Equiv.swap a b), qtwoDB32_phi_mem φ hφ _⟩ : dEven m) =
        ⟨dTau m sgn a' b', dTau_mem_dEven m sgn hab'⟩ := Subtype.ext heq
    rw [helem, qtwoDB32_proj_dTau m sgn hab']
  rw [h1]
  exact ⟨a', b', hab', rfl⟩

theorem qtwoDB32_psi_injective {m : ℕ} (hm : 5 ≤ m)
    (φ : Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m)) (hinj : Function.Injective φ)
    (hφ : ∀ a b : Fin m, a ≠ b → ∃ (sgn : Bool) (a' b' : Fin m), a' ≠ b' ∧
      φ (Equiv.swap a b) = dTau m sgn a' b') :
    Function.Injective (qtwoDB32_psi φ hφ) := by
  classical
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  set i2 : Fin m := ⟨2, by omega⟩ with hi2
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [hi0, hi2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [hi1, hi2, Fin.ext_iff]
  set c : Equiv.Perm (Fin m) := Equiv.swap i0 i1 * Equiv.swap i0 i2 with hc
  have hc3 : c.IsThreeCycle := by
    rw [hc]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12
  refine CFSG.EvenSmallLie.OddTranspAlt.injective_of_threeCycle hm (qtwoDB32_psi φ hφ) hc3 ?_
  intro hone
  have hproj : qtwoDB32_proj m ⟨φ c, qtwoDB32_phi_mem φ hφ c⟩ = 1 := by
    change (qtwoDB32_psi φ hφ) c = 1
    exact hone
  have hsq : (φ c) * (φ c) = 1 := by
    obtain ⟨d, hd1, _, hd⟩ := qtwoDB32_proj_spec m ⟨φ c, qtwoDB32_phi_mem φ hφ c⟩
    rw [hproj] at hd
    simp only [Subgroup.coe_mk, Equiv.Perm.one_apply] at hd
    refine (dBasis m).ext' fun i => ?_
    rw [LinearEquiv.mul_apply, hd i, map_smul, hd i, smul_smul]
    have hdd : d i * d i = 1 := by rcases hd1 i with h' | h' <;> rw [h'] <;> decide
    rw [hdd, one_smul]
    rfl
  have horder : orderOf (φ c) = 3 := by
    rw [orderOf_injective φ hinj, hc3.orderOf]
  have hdvd : orderOf (φ c) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
  rw [horder] at hdvd
  exact absurd hdvd (by decide)

theorem qtwoDB32_addHom_smul {m : ℕ} (T : DVec m →+ DVec m) (a : ZMod 3) (x : DVec m) :
    T (a • x) = a • T x := by
  have ha : a = 0 ∨ a = 1 ∨ a = -1 := by revert a; decide
  rcases ha with rfl | rfl | rfl <;> simp [neg_smul]

theorem qtwoDB32_dPerm_const {m : ℕ} (σ : Equiv.Perm (Fin m)) (c : ZMod 3) :
    dPerm m σ (fun _ => c) = fun _ => c := by
  funext j
  rw [qtwoDB32_dPerm_eval]

@[expose] noncomputable def qtwoDB32_dPermHom (m : ℕ) :
    Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m) where
  toFun := dPerm m
  map_one' := dPerm_one m
  map_mul' := dPerm_mul m

theorem qtwoDB32_dPerm_inv (m : ℕ) (ρ : Equiv.Perm (Fin m)) :
    (dPerm m ρ)⁻¹ = dPerm m ρ⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← dPerm_mul, mul_inv_cancel, dPerm_one]

@[expose] def qtwoDB32_dSgn (sgn : Bool) : ZMod 3 := if sgn then -1 else 1

@[expose] noncomputable def qtwoDB32_dTauZ (m : ℕ) (s : ZMod 3) (a b : Fin m) :
    DVec m ≃ₗ[ZMod 3] DVec m :=
  if s = -1 then dTau m true a b else dTau m false a b

theorem qtwoDB32_dSgn_cases (sgn : Bool) :
    qtwoDB32_dSgn sgn = 1 ∨ qtwoDB32_dSgn sgn = -1 := by
  cases sgn <;> simp [qtwoDB32_dSgn]

theorem qtwoDB32_dTauZ_dSgn (m : ℕ) (sgn : Bool) (a b : Fin m) :
    qtwoDB32_dTauZ m (qtwoDB32_dSgn sgn) a b = dTau m sgn a b := by
  cases sgn
  · show (if (qtwoDB32_dSgn false) = -1 then dTau m true a b else dTau m false a b) =
      dTau m false a b
    rw [if_neg (by decide)]
  · show (if (qtwoDB32_dSgn true) = -1 then dTau m true a b else dTau m false a b) =
      dTau m true a b
    rw [if_pos (by decide)]

theorem qtwoDB32_dTauZ_apply_left {m : ℕ} {s : ZMod 3} (hs : s = 1 ∨ s = -1)
    {a b : Fin m} (hab : a ≠ b) :
    qtwoDB32_dTauZ m s a b (dBasis m a) = s • dBasis m b := by
  rcases hs with rfl | rfl
  · show (if (1 : ZMod 3) = -1 then dTau m true a b else dTau m false a b) (dBasis m a) =
      1 • dBasis m b
    rw [if_neg (by decide), dTau_apply_left m false hab]
    simp
  · show (if (-1 : ZMod 3) = -1 then dTau m true a b else dTau m false a b) (dBasis m a) =
      -1 • dBasis m b
    rw [if_pos rfl, dTau_apply_left m true hab]
    simp

theorem qtwoDB32_dTauZ_apply_right {m : ℕ} {s : ZMod 3} (hs : s = 1 ∨ s = -1)
    {a b : Fin m} (hab : a ≠ b) :
    qtwoDB32_dTauZ m s a b (dBasis m b) = s • dBasis m a := by
  rcases hs with rfl | rfl
  · show (if (1 : ZMod 3) = -1 then dTau m true a b else dTau m false a b) (dBasis m b) =
      1 • dBasis m a
    rw [if_neg (by decide), dTau_apply_right m false hab]
    simp
  · show (if (-1 : ZMod 3) = -1 then dTau m true a b else dTau m false a b) (dBasis m b) =
      -1 • dBasis m a
    rw [if_pos rfl, dTau_apply_right m true hab]
    simp

theorem qtwoDB32_dTauZ_apply_of_ne {m : ℕ} {s : ZMod 3} (hs : s = 1 ∨ s = -1)
    {a b i : Fin m} (hia : i ≠ a) (hib : i ≠ b) :
    qtwoDB32_dTauZ m s a b (dBasis m i) = dBasis m i := by
  rcases hs with rfl | rfl
  · show (if (1 : ZMod 3) = -1 then dTau m true a b else dTau m false a b) (dBasis m i) =
      dBasis m i
    rw [if_neg (by decide), dTau_apply_of_ne m false hia hib]
  · show (if (-1 : ZMod 3) = -1 then dTau m true a b else dTau m false a b) (dBasis m i) =
      dBasis m i
    rw [if_pos rfl, dTau_apply_of_ne m true hia hib]

theorem qtwoDB32_pair_eq_of_swap_eq {m : ℕ} {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d)
    (h : Equiv.swap a b = Equiv.swap c d) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a = c ∨ a = d := by
    have h1 : Equiv.swap c d a ≠ a := by
      rw [← h, Equiv.swap_apply_left]
      exact Ne.symm hab
    exact Equiv.eq_or_eq_of_swap_apply_ne_self h1
  have hb : b = c ∨ b = d := by
    have h1 : Equiv.swap c d b ≠ b := by
      rw [← h, Equiv.swap_apply_right]
      exact hab
    exact Equiv.eq_or_eq_of_swap_apply_ne_self h1
  rcases ha with h' | h' <;> rcases hb with h'' | h''
  · exact absurd (h'.trans h''.symm) hab
  · exact Or.inl ⟨h', h''⟩
  · exact Or.inr ⟨h', h''⟩
  · exact absurd (h'.trans h''.symm) hab

@[expose] noncomputable def qtwoDB32_unitOfSign (s : ZMod 3) : (ZMod 3)ˣ :=
  if s = -1 then -1 else 1

theorem qtwoDB32_unitOfSign_val {s : ZMod 3} (hs : s = 1 ∨ s = -1) :
    (qtwoDB32_unitOfSign s : ZMod 3) = s := by
  rcases hs with rfl | rfl
  · show ((if (1 : ZMod 3) = -1 then (-1 : (ZMod 3)ˣ) else 1) : ZMod 3) = 1
    rw [if_neg (by decide)]
  · show ((if (-1 : ZMod 3) = -1 then (-1 : (ZMod 3)ˣ) else 1) : ZMod 3) = -1
    rw [if_pos rfl]
    rfl

end CFSG.StandardType.QTwo

end
