module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open Module

variable {K : Type*} [Field K] {H : Type*} [Group H]
  {X : Type*} [AddCommGroup X] [Module K X] {Y : Type*} [AddCommGroup Y] [Module K Y]

theorem injective_of_equivariant {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)}
    (hX : ∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρX h x ∈ S) → S = ⊥ ∨ S = ⊤)
    {T : X →ₗ[K] Y} (hT : ∀ h x, T (ρX h x) = ρY h (T x)) (hT0 : T ≠ 0) :
    Function.Injective T := by
  have hker : ∀ h : H, ∀ x ∈ LinearMap.ker T, ρX h x ∈ LinearMap.ker T := by
    intro h x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hT, hx, map_zero]
  rcases hX _ hker with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) hT0

theorem exists_equivariant_equiv_of_ne_zero [FiniteDimensional K X] [FiniteDimensional K Y]
    {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)}
    (hX : ∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρX h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hdim : finrank K X = finrank K Y)
    {T : X →ₗ[K] Y} (hT : ∀ h x, T (ρX h x) = ρY h (T x)) (hT0 : T ≠ 0) :
    ∃ e : X ≃ₗ[K] Y, (∀ x, e x = T x) ∧ ∀ h x, e (ρX h x) = ρY h (e x) := by
  refine ⟨T.linearEquivOfInjective (injective_of_equivariant hX hT hT0) hdim,
    fun x => LinearMap.linearEquivOfInjective_apply _ _ x, fun h x => ?_⟩
  simp only [LinearMap.linearEquivOfInjective_apply]
  exact hT h x

theorem eq_zero_of_not_equiv [FiniteDimensional K X] [FiniteDimensional K Y]
    {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)}
    (hX : ∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρX h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hdim : finrank K X = finrank K Y)
    (hne : ¬ ∃ e : X ≃ₗ[K] Y, ∀ h x, e (ρX h x) = ρY h (e x))
    {T : X →ₗ[K] Y} (hT : ∀ h x, T (ρX h x) = ρY h (T x)) : T = 0 := by
  by_contra hT0
  obtain ⟨e, -, he⟩ := exists_equivariant_equiv_of_ne_zero hX hdim hT hT0
  exact hne ⟨e, he⟩

theorem exists_equivariant_of_pairing [FiniteDimensional K Y]
    {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)}
    (q : QuadraticForm K Y) (hq : ∀ h y, q (ρY h y) = q y)
    (hnd : ∀ y, (∀ y', QuadraticMap.polar q y y' = 0) → y = 0)
    (P : X →ₗ[K] Y →ₗ[K] K) (hP : ∀ h x y, P (ρX h x) (ρY h y) = P x y) :
    ∃ T : X →ₗ[K] Y, (∀ h x, T (ρX h x) = ρY h (T x)) ∧
      ∀ x y, QuadraticMap.polar q (T x) y = P x y := by
  have hinj : Function.Injective (QuadraticMap.polarBilin q) := by
    refine (injective_iff_map_eq_zero _).mpr fun y hy => hnd y fun y' => ?_
    have h := LinearMap.congr_fun hy y'
    rwa [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] at h
  let e : Y ≃ₗ[K] Module.Dual K Y :=
    (QuadraticMap.polarBilin q).linearEquivOfInjective hinj Subspace.dual_finrank_eq.symm
  have he : ∀ (f : Module.Dual K Y) (y : Y), QuadraticMap.polar q (e.symm f) y = f y := by
    intro f y
    have h := LinearMap.congr_fun (e.apply_symm_apply f) y
    rwa [LinearMap.linearEquivOfInjective_apply, QuadraticMap.polarBilin_apply_apply] at h
  have hpol : ∀ (h : H) (a b : Y),
      QuadraticMap.polar q (ρY h a) (ρY h b) = QuadraticMap.polar q a b := by
    intro h a b
    simp only [QuadraticMap.polar, ← map_add, hq]
  have hinv : ∀ (h : H) (y : Y), ρY h (ρY h⁻¹ y) = y := by
    intro h y
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have key : ∀ a b : Y, (∀ y, QuadraticMap.polar q a y = QuadraticMap.polar q b y) → a = b := by
    intro a b hab
    refine sub_eq_zero.mp (hnd (a - b) fun y => ?_)
    rw [QuadraticMap.polar_sub_left, hab, sub_self]
  refine ⟨e.symm.toLinearMap ∘ₗ P, fun h x => key _ _ fun y => ?_, fun x y => he (P x) y⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  calc QuadraticMap.polar q (e.symm (P (ρX h x))) y = P (ρX h x) y := he _ _
    _ = P (ρX h x) (ρY h (ρY h⁻¹ y)) := by rw [hinv]
    _ = P x (ρY h⁻¹ y) := hP h x _
    _ = QuadraticMap.polar q (e.symm (P x)) (ρY h⁻¹ y) := (he _ _).symm
    _ = QuadraticMap.polar q (ρY h (e.symm (P x))) (ρY h (ρY h⁻¹ y)) := (hpol h _ _).symm
    _ = QuadraticMap.polar q (ρY h (e.symm (P x))) y := by rw [hinv]

theorem pairing_eq_zero_of_not_equiv [FiniteDimensional K X] [FiniteDimensional K Y]
    {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)}
    (hX : ∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρX h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hdim : finrank K X = finrank K Y)
    (hne : ¬ ∃ e : X ≃ₗ[K] Y, ∀ h x, e (ρX h x) = ρY h (e x))
    (q : QuadraticForm K Y) (hq : ∀ h y, q (ρY h y) = q y)
    (hnd : ∀ y, (∀ y', QuadraticMap.polar q y y' = 0) → y = 0)
    (P : X →ₗ[K] Y →ₗ[K] K) (hP : ∀ h x y, P (ρX h x) (ρY h y) = P x y) : P = 0 := by
  obtain ⟨T, hT, hTP⟩ := exists_equivariant_of_pairing q hq hnd P hP
  have hT0 : T = 0 := eq_zero_of_not_equiv hX hdim hne hT
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [← hTP, hT0, LinearMap.zero_apply, QuadraticMap.polar_zero_left, LinearMap.zero_apply,
    LinearMap.zero_apply]

theorem exists_eq_smul_polar [FiniteDimensional K X] {ρX : H →* (X ≃ₗ[K] X)}
    (hEnd : ∀ T : X →ₗ[K] X, (∀ h : H, T ∘ₗ (ρX h : X →ₗ[K] X) = (ρX h : X →ₗ[K] X) ∘ₗ T) →
      ∃ c : K, T = c • LinearMap.id)
    (q : QuadraticForm K X) (hq : ∀ h x, q (ρX h x) = q x)
    (hnd : ∀ x, (∀ x', QuadraticMap.polar q x x' = 0) → x = 0)
    (P : X →ₗ[K] X →ₗ[K] K) (hP : ∀ h x x', P (ρX h x) (ρX h x') = P x x') :
    ∃ c : K, ∀ x x', P x x' = c * QuadraticMap.polar q x x' := by
  obtain ⟨T, hT, hTP⟩ := exists_equivariant_of_pairing (ρX := ρX) (ρY := ρX) q hq hnd P hP
  obtain ⟨c, hc⟩ := hEnd T fun h => LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hT h x
  refine ⟨c, fun x x' => ?_⟩
  rw [← hTP, hc, LinearMap.smul_apply, LinearMap.id_apply, QuadraticMap.polar_smul_left,
    smul_eq_mul]

theorem exists_matrix_of_invariant [FiniteDimensional K X] {ρX : H →* (X ≃ₗ[K] X)}
    (hEnd : ∀ T : X →ₗ[K] X, (∀ h : H, T ∘ₗ (ρX h : X →ₗ[K] X) = (ρX h : X →ₗ[K] X) ∘ₗ T) →
      ∃ c : K, T = c • LinearMap.id)
    (q : QuadraticForm K X) (hq : ∀ h x, q (ρX h x) = q x)
    (hnd : ∀ x, (∀ x', QuadraticMap.polar q x x' = 0) → x = 0)
    (P : (Fin 2 → X) →ₗ[K] (Fin 2 → X) →ₗ[K] K)
    (hP : ∀ h m m', P (fun i => ρX h (m i)) (fun i => ρX h (m' i)) = P m m') :
    ∃ Φ : Matrix (Fin 2) (Fin 2) K, ∀ m m',
      P m m' = ∑ i, ∑ j, Φ i j * QuadraticMap.polar q (m i) (m' j) := by
  have hsingle : ∀ (h : H) (i : Fin 2) (x : X),
      (fun k => ρX h ((Pi.single i x : Fin 2 → X) k)) = (Pi.single i (ρX h x) : Fin 2 → X) := by
    intro h i x
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_apply, hk]
  have hblock : ∀ i j : Fin 2, ∃ c : K, ∀ x x' : X,
      P (Pi.single i x) (Pi.single j x') = c * QuadraticMap.polar q x x' := by
    intro i j
    obtain ⟨c, hc⟩ := exists_eq_smul_polar hEnd q hq hnd
      ((P.comp (LinearMap.single K (fun _ : Fin 2 => X) i)).compl₂
        (LinearMap.single K (fun _ : Fin 2 => X) j))
      fun h x x' => by
        simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.coe_single]
        rw [← hsingle, ← hsingle, hP]
    refine ⟨c, fun x x' => ?_⟩
    have h := hc x x'
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.coe_single] at h
    exact h
  choose Φ hΦ using hblock
  refine ⟨Matrix.of Φ, fun m m' => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single m, ← Finset.univ_sum_single m']
  simp only [map_sum, LinearMap.sum_apply, hΦ, Matrix.of_apply]
  exact Finset.sum_comm

@[expose] noncomputable def matrixActFin2 (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    (Fin 2 → X) ≃ₗ[K] (Fin 2 → X) :=
  LinearEquiv.ofLinear
    (LinearMap.pi fun i => ∑ j, A i j • LinearMap.proj j)
    (LinearMap.pi fun i => ∑ j, A⁻¹ i j • LinearMap.proj j)
    (LinearMap.ext fun m => funext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, Finset.smul_sum, smul_smul,
        LinearMap.id_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.mul_nonsing_inv A hA,
        Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true])
    (LinearMap.ext fun m => funext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, Finset.smul_sum, smul_smul,
        LinearMap.id_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul A hA,
        Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true])

theorem matrixActFin2_apply (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) (m : Fin 2 → X)
    (i : Fin 2) : matrixActFin2 A hA m i = ∑ j, A i j • m j := by
  simp [matrixActFin2, LinearMap.pi_apply, Finset.sum_apply]

theorem five_le_finrank_sup [FiniteDimensional K X] {A B : Submodule K X}
    (hA : finrank K A = 4) (hB : finrank K B = 4) (hodd : Odd (finrank K ↥(A ⊓ B))) :
    5 ≤ finrank K ↥(A ⊔ B) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h2 : finrank K ↥(A ⊓ B) ≤ finrank K A := Submodule.finrank_mono inf_le_left
  obtain ⟨k, hk⟩ := hodd
  omega

end CFSG.RankThree.GF2n.Stroth80.S715L
