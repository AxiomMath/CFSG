module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.ClassicalInvolution.Phan.PhanDn.DiagTorus
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
import CFSG.LocalAnalysis.StandardType.GGOrthRk1PairTriple
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pieces
import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
import CFSG.Mathlib.LinearAlgebra.QuadraticForm.OrthogonalSum

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits

section Span

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem iSup_pieces_eq_top {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (Δ : TBJOmData Q p A r) (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) :
    ⨆ j, Δ.F.U j = ⊤ :=
  Δ.iSup_U_eq_top hfix

end Span

section Family

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem TBJOmData.exists_normFamily {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r)
    {f : ℕ} (hf : Nat.card K = 2 ^ f) (hpq : p ∣ Nat.card K + 1) (K' : Type) [Field K']
    [Finite K'] [CharP K' 2] (hK' : Nat.card K' = (2 ^ f) ^ 2) :
    ∃ (_ : Algebra K K') (φ : Fin r → (K' →ₗ[K] V)) (ζ : K'),
      (∀ j x, algebraMap K K' (Q (φ j x)) = unitaryInvolution K' 2 f x * x) ∧
      (∀ j k, j ≠ k → ∀ x y, polar Q (φ j x) (φ k y) = 0) ∧
      (∀ j, LinearMap.range (φ j) = Δ.F.U j) ∧
      (∀ (g : Fin r → Multiplicative (ZMod p)) j x,
        Δ.τ g (φ j x) = φ j (ζ ^ (toAdd (g j)).val * x)) ∧
      unitaryInvolution K' 2 f ζ * ζ = 1 ∧ ζ ≠ 1 ∧ ζ ^ p = 1 := by
  classical
  obtain ⟨inst, ψ, ζ, t, ht, hψ, hspan, hζ, hσζ, hσ⟩ :=
    (Δ.rk1Block hp2).exists_algebra_linearEquiv hf hpq K' hK'
  letI := inst
  have hinj : Function.Injective (algebraMap K K') := (algebraMap K K').injective
  have hpow : ∀ n : ℕ, ∀ x : K', (Δ.c ^ n) (ψ x) = ψ (ζ ^ n * x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        calc (Δ.c ^ (n + 1)) (ψ x)
            = (Δ.c ^ n) (Δ.c (ψ x)) := by rw [pow_succ, LinearEquiv.mul_apply]
          _ = (Δ.c ^ n) (ψ (ζ * x)) := by rw [← hψ x]
          _ = ψ (ζ ^ n * (ζ * x)) := ih (ζ * x)
          _ = ψ (ζ ^ (n + 1) * x) := by rw [pow_succ, mul_assoc]
  have hqD : ∀ j : Fin r, ∀ y : Δ.D,
      (Q.comp (Δ.θ j)) (Δ.c y) = (Q.comp (Δ.θ j)) y := by
    intro j y
    let g₁ : Fin r → Multiplicative (ZMod p) := Pi.mulSingle j (ofAdd (1 : ZMod p))
    have hval : (toAdd (g₁ j)).val = 1 := by
      have h1 : toAdd (g₁ j) = (1 : ZMod p) := by simp [g₁]
      rw [h1]
      exact ZMod.val_one'' (Fact.out : p.Prime).ne_one
    have htheta : Δ.τ g₁ (Δ.θ j y) = Δ.θ j (Δ.c y) := by
      rw [Δ.tau_theta g₁ j y, hval, pow_one]
    have hmemA : Δ.τ g₁ ∈ A :=
      (le_of_eq Δ.τ_range) (MonoidHom.mem_range.mpr ⟨g₁, rfl⟩)
    have hiso : ∀ m : V, Q (Δ.τ g₁ m) = Q m :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q (hAΩ hmemA))
    calc (Q.comp (Δ.θ j)) (Δ.c y)
        = Q (Δ.θ j (Δ.c y)) := rfl
      _ = Q (Δ.τ g₁ (Δ.θ j y)) := by rw [htheta]
      _ = Q (Δ.θ j y) := hiso _
      _ = (Q.comp (Δ.θ j)) y := rfl
  have hnorm : ∀ j : Fin r, ∃ μ : K, ∀ x : K',
      algebraMap K K' (Q (Δ.θ j (ψ x))) =
        algebraMap K K' μ * (unitaryInvolution K' 2 f x * x) := by
    intro j
    exact exists_quadForm_eq_norm (unitaryInvolution K' 2 f) ψ Δ.c ζ t ht hψ hspan hζ hσζ hσ
      (Q.comp (Δ.θ j)) (hqD j)
  choose μ hμ using hnorm
  have hμne : ∀ j : Fin r, μ j ≠ 0 := by
    intro j h0
    have hzero : ∀ y : Δ.D, Q (Δ.θ j y) = 0 := by
      intro y
      obtain ⟨x, rfl⟩ := ψ.surjective y
      have h1 := hμ j x
      rw [h0, map_zero, zero_mul] at h1
      exact hinj (h1.trans (map_zero (algebraMap K K')).symm)
    have hbot : Δ.F.U j = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro u hu
      refine Δ.F.nondeg j u hu fun v hv => ?_
      rw [← Δ.θ_range j] at hu hv
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hu
      obtain ⟨y', rfl⟩ := LinearMap.mem_range.mp hv
      change Q (Δ.θ j y' + Δ.θ j y) - Q (Δ.θ j y')
        - Q (Δ.θ j y) = 0
      rw [← map_add, hzero (y' + y), hzero y', hzero y, sub_zero, sub_zero]
    exact Δ.F.ne_bot j hbot
  have hσU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution K' 2 f) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := K') (p := 2)
      (f := f) hK'
  have hlam_ex : ∀ j : Fin r, ∃ lam : K',
      unitaryInvolution K' 2 f lam * lam = (algebraMap K K' (μ j))⁻¹ := by
    intro j
    apply hσU.exists_norm
    simp [map_inv₀, hσ]
  choose lam hlam using hlam_ex
  have hlam_ne : ∀ j : Fin r, lam j ≠ 0 := by
    intro j h
    have h1 := hlam j
    rw [h, mul_zero] at h1
    have h2 : (algebraMap K K' (μ j))⁻¹ ≠ 0 :=
      inv_ne_zero fun hzero => hμne j (hinj (hzero.trans (map_zero (algebraMap K K')).symm))
    exact h2 h1.symm
  let φ : Fin r → (K' →ₗ[K] V) := fun j =>
    (Δ.θ j).comp (ψ.toLinearMap.comp (LinearMap.mulLeft K (lam j)))
  have hφ : ∀ j x, φ j x = Δ.θ j (ψ (lam j * x)) := fun j x => rfl
  have hQφ : ∀ j x, algebraMap K K' (Q (φ j x)) = unitaryInvolution K' 2 f x * x := by
    intro j x
    have hAmu_ne : algebraMap K K' (μ j) ≠ 0 :=
      fun h => hμne j (hinj (h.trans (map_zero (algebraMap K K')).symm))
    have hAc : algebraMap K K' (μ j) *
        (unitaryInvolution K' 2 f (lam j) * lam j) = 1 := by
      rw [hlam j, mul_inv_cancel₀ hAmu_ne]
    rw [hφ j x, hμ j (lam j * x), map_mul (unitaryInvolution K' 2 f) (lam j) x]
    rw [show algebraMap K K' (μ j) *
          ((unitaryInvolution K' 2 f (lam j) * unitaryInvolution K' 2 f x) * (lam j * x))
        = (algebraMap K K' (μ j) *
            (unitaryInvolution K' 2 f (lam j) * lam j)) *
          (unitaryInvolution K' 2 f x * x) by ring,
      hAc, one_mul]
  have horth : ∀ j k : Fin r, j ≠ k → ∀ x y, polar Q (φ j x) (φ k y) = 0 := by
    intro j k hjk x y
    exact Δ.F.orth j k hjk (φ j x)
      (by
        rw [← Δ.θ_range j]
        exact LinearMap.mem_range.mpr ⟨ψ (lam j * x), rfl⟩)
      (φ k y)
      (by
        rw [← Δ.θ_range k]
        exact LinearMap.mem_range.mpr ⟨ψ (lam k * y), rfl⟩)
  have hact_aux : ∀ (g : Fin r → Multiplicative (ZMod p)) (j : Fin r) (x : K'),
      Δ.τ g (Δ.θ j (ψ (lam j * x))) =
        Δ.θ j (ψ (lam j * (ζ ^ (toAdd (g j)).val * x))) := by
    intro g j x
    rw [Δ.tau_theta g j (ψ (lam j * x)),
      hpow (toAdd (g j)).val (lam j * x),
      mul_left_comm (ζ ^ (toAdd (g j)).val) (lam j) x]
  have hact : ∀ (g : Fin r → Multiplicative (ZMod p)) (j : Fin r) (x : K'),
      Δ.τ g (φ j x) = φ j (ζ ^ (toAdd (g j)).val * x) := by
    intro g j x
    rw [hφ j x, hφ j]
    exact hact_aux g j x
  have hrange_φ : ∀ j : Fin r, LinearMap.range (φ j) = Δ.F.U j := by
    intro j
    rw [← Δ.θ_range j]
    apply le_antisymm
    · calc LinearMap.range (φ j)
          = Submodule.map (Δ.θ j) (LinearMap.range
              (ψ.toLinearMap.comp (LinearMap.mulLeft K (lam j)))) := by
            dsimp only [φ]
            rw [LinearMap.range_comp]
        _ ≤ Submodule.map (Δ.θ j) ⊤ := Submodule.map_mono le_top
        _ = LinearMap.range (Δ.θ j) := Submodule.map_top _
    · intro v hv
      rw [LinearMap.mem_range] at hv ⊢
      obtain ⟨d, rfl⟩ := hv
      obtain ⟨x, rfl⟩ := ψ.surjective d
      refine ⟨(lam j)⁻¹ * x, ?_⟩
      rw [hφ j, mul_inv_cancel_left₀ (hlam_ne j)]
  have hζne : ζ ≠ 1 := by
    intro hζ1
    have hfix : Δ.c (ψ 1) = ψ 1 := by
      rw [← hψ 1]
      simp [hζ1]
    have hzero : ψ 1 = 0 := Δ.c_fix (ψ 1) hfix
    have h1 : (1 : K') = 0 := ψ.injective (by rw [hzero, map_zero])
    exact one_ne_zero h1
  have hζpow : ζ ^ p = 1 := by
    have h1 : ψ (ζ ^ p * 1) = ψ 1 := by
      rw [← hpow p 1, Δ.c_pow]
      rfl
    simpa using ψ.injective h1
  exact ⟨inst, φ, ζ, hQφ, horth, hrange_φ, hact, hσζ, hζne, hζpow⟩

end Family

theorem OrthFrameCore.p_eq_three {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2) : p = 3 := by
  have h : p ∣ 3 := by
    have := Φ.hpq
    rwa [hF] at this
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp h

theorem OrthFrameCore.exists_normIso {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2) :
    ∃ (_ : Algebra Φ.F (GaloisField 2 2))
      (E : QuadExt Φ.F (GaloisField 2 2) (unitaryInvolution (GaloisField 2 2) 2 1))
      (χ : Φ.V ≃ₗ[Φ.F] (Fin Φ.r → GaloisField 2 2))
      (ζ : normOne (unitaryInvolution (GaloisField 2 2) 2 1)),
      ζ ≠ 1 ∧ ζ ^ p = 1 ∧ (∀ v, Qn E Φ.r (χ v) = Φ.Q v) ∧
        ∀ (g : Fin Φ.r → Multiplicative (ZMod p)) (v : Φ.V),
          χ (Φ.Δ.τ g v) = diagHom Φ.F (unitaryInvolution (GaloisField 2 2) 2 1) Φ.r
            (fun i => ζ ^ (toAdd (g i)).val) (χ v) := by
  classical
  have hp2 : p ≠ 2 := by
    rw [Φ.p_eq_three hF]
    decide
  have hf : Nat.card Φ.F = 2 ^ 1 := by simpa using hF
  have hK' : Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨inst, φ, ζ', hQφ, horth, hrange, hact, hσζ, hζne, hζpow⟩ :=
    Φ.Δ.exists_normFamily hp2 Φ.hA hf Φ.hpq (GaloisField 2 2) hK'
  letI := inst
  let E : QuadExt Φ.F (GaloisField 2 2) (unitaryInvolution (GaloisField 2 2) 2 1) :=
    quadExt_of_card_of_char_two 1 hf hK'
  have hζ'0 : ζ' ≠ 0 := by
    intro h
    have h1 := hσζ
    rw [h, mul_zero] at h1
    exact one_ne_zero h1.symm
  let ζu : (GaloisField 2 2)ˣ := Units.mk0 ζ' hζ'0
  let ζ : normOne (unitaryInvolution (GaloisField 2 2) 2 1) :=
    ⟨ζu, (mem_normOne (unitaryInvolution (GaloisField 2 2) 2 1)).2 (by simpa [ζu] using hσζ)⟩
  have hζ_ne : ζ ≠ 1 := by
    intro h
    apply hζne
    have hval : ((ζ : (GaloisField 2 2)ˣ) : GaloisField 2 2) = 1 := by
      have := congrArg (fun u : normOne (unitaryInvolution (GaloisField 2 2) 2 1) =>
        ((u : (GaloisField 2 2)ˣ) : GaloisField 2 2)) h
      simpa using this
    simpa [ζ, ζu] using hval
  have hζ_pow : ζ ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    change (((ζ : (GaloisField 2 2)ˣ) : GaloisField 2 2)) ^ p = 1
    rw [show ((ζ : (GaloisField 2 2)ˣ) : GaloisField 2 2) = ζ' by rfl, hζpow]
  let incl : (Fin Φ.r → GaloisField 2 2) →ₗ[Φ.F] Φ.V :=
    ∑ j, (φ j).comp (LinearMap.proj j :
      (Fin Φ.r → GaloisField 2 2) →ₗ[Φ.F] GaloisField 2 2)
  have incl_apply : ∀ x : Fin Φ.r → GaloisField 2 2,
      incl x = ∑ j, φ j (x j) := by
    intro x
    simp [incl, LinearMap.sum_apply]
  have hinj : Function.Injective incl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext j
    have hxj : φ j (x j) = 0 := by
      refine Φ.Δ.F.nondeg j (φ j (x j)) ?_ ?_
      · rw [← hrange j]
        exact LinearMap.mem_range.mpr ⟨x j, rfl⟩
      · intro v hv
        rw [← hrange j] at hv
        obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hv
        have h0 : polar Φ.Q (φ j y) (incl x) = 0 := by rw [hx, polar_zero_right]
        have hsum : polar Φ.Q (φ j y) (incl x) =
            ∑ k, polar Φ.Q (φ j y) (φ k (x k)) := by
          rw [incl_apply]
          have := map_sum (polarBilin Φ.Q (φ j y)) (fun k => φ k (x k)) Finset.univ
          simpa only [polarBilin_apply_apply] using this
        have hsingle : (∑ k, polar Φ.Q (φ j y) (φ k (x k))) =
            polar Φ.Q (φ j y) (φ j (x j)) := by
          refine Finset.sum_eq_single j ?_ ?_
          · intro k _ hk
            exact horth j k (Ne.symm hk) y (x k)
          · intro hj
            exact absurd (Finset.mem_univ j) hj
        rw [hsum, hsingle] at h0
        exact h0
    have hprod : unitaryInvolution (GaloisField 2 2) 2 1 (x j) * x j = 0 := by
      have h := hQφ j (x j)
      rw [hxj, QuadraticMap.map_zero, map_zero] at h
      exact h.symm
    rcases mul_eq_zero.mp hprod with h | h
    · exact (map_eq_zero (unitaryInvolution (GaloisField 2 2) 2 1)).mp h
    · exact h
  have hsurj : Function.Surjective incl := by
    have htop : ⨆ j, Φ.Δ.F.U j = ⊤ := Φ.Δ.iSup_U_eq_top Φ.hfix
    have hle : (⨆ j, Φ.Δ.F.U j) ≤ LinearMap.range incl := by
      refine iSup_le fun j => ?_
      rw [← hrange j]
      rintro _ ⟨x, rfl⟩
      refine LinearMap.mem_range.mpr ⟨Pi.single j x, ?_⟩
      rw [incl_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk, map_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    exact LinearMap.range_eq_top.mp (top_le_iff.mp (by simpa only [htop] using hle))
  let e : (Fin Φ.r → GaloisField 2 2) ≃ₗ[Φ.F] Φ.V :=
    LinearEquiv.ofBijective incl ⟨hinj, hsurj⟩
  have hQincl : ∀ x : Fin Φ.r → GaloisField 2 2,
      Φ.Q (incl x) = Qn E Φ.r x := by
    intro x
    apply (algebraMap Φ.F (GaloisField 2 2)).injective
    have hsum : Φ.Q (∑ j, φ j (x j)) = ∑ j, Φ.Q (φ j (x j)) :=
      CFSG.QuadraticMap.map_sum_of_polar_eq_zero (Q := Φ.Q) Finset.univ
        (fun j => φ j (x j))
        (fun i _ j _ hij => horth i j hij (x i) (x j))
    rw [incl_apply, hsum, map_sum]
    simp_rw [hQφ]
    rw [algebraMap_Qn]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hiso : ∀ v : Φ.V, Qn E Φ.r (e.symm v) = Φ.Q v := by
    intro v
    have hx : incl (e.symm v) = v := e.apply_symm_apply v
    simpa [hx] using (hQincl (e.symm v)).symm
  have hcoe : ∀ n : ℕ,
      (((ζ ^ n : normOne (unitaryInvolution (GaloisField 2 2) 2 1)) :
        (GaloisField 2 2)ˣ) : GaloisField 2 2) = ζ' ^ n := by
    intro n
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    change (((ζ : (GaloisField 2 2)ˣ) : GaloisField 2 2)) ^ n = ζ' ^ n
    rw [show ((ζ : (GaloisField 2 2)ˣ) : GaloisField 2 2) = ζ' by rfl]
  have hact_incl : ∀ (g : Fin Φ.r → Multiplicative (ZMod p))
      (x : Fin Φ.r → GaloisField 2 2),
      Φ.Δ.τ g (incl x) = incl (fun j => ζ' ^ (toAdd (g j)).val * x j) := by
    intro g x
    calc Φ.Δ.τ g (incl x)
        = ∑ j, Φ.Δ.τ g (φ j (x j)) := by
          rw [incl_apply, map_sum]
      _ = ∑ j, φ j (ζ' ^ (toAdd (g j)).val * x j) :=
          Finset.sum_congr rfl fun j _ => hact g j (x j)
      _ = incl (fun j => ζ' ^ (toAdd (g j)).val * x j) := by
          rw [incl_apply]
  have hact_all : ∀ (g : Fin Φ.r → Multiplicative (ZMod p)) (v : Φ.V),
      e.symm (Φ.Δ.τ g v) = diagHom Φ.F (unitaryInvolution (GaloisField 2 2) 2 1) Φ.r
        (fun i => ζ ^ (toAdd (g i)).val) (e.symm v) := by
    intro g v
    apply e.injective
    rw [e.apply_symm_apply]
    have hdiag : diagHom Φ.F (unitaryInvolution (GaloisField 2 2) 2 1) Φ.r
        (fun i => ζ ^ (toAdd (g i)).val) (e.symm v) =
        (fun i => ζ' ^ (toAdd (g i)).val * (e.symm v) i) := by
      funext i
      rw [diagHom_apply, hcoe]
    rw [hdiag]
    change Φ.Δ.τ g v = incl (fun i => ζ' ^ (toAdd (g i)).val * (e.symm v) i)
    have hx : incl (e.symm v) = v := e.apply_symm_apply v
    rw [show Φ.Δ.τ g v = Φ.Δ.τ g (incl (e.symm v)) by rw [hx]]
    exact hact_incl g (e.symm v)
  exact ⟨inst, E, e.symm, ζ, hζ_ne, hζ_pow, hiso, hact_all⟩

end OrthTorus

end CFSG.StandardType

end
