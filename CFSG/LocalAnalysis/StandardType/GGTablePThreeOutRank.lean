module

public import Mathlib

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix
open Polynomial

noncomputable section

private lemma poly_cube_factor {K : Type} [Field K] (ω : K) (hω2 : ω^2 + ω + 1 = 0) :
    (X - C ω) * (X - C (ω^2)) = (X^2 + X + 1 : K[X]) := by
  have hω2KX : (C ω)^2 + C ω + 1 = 0 := by
    have h : (C (ω^2 + ω + 1) : K[X]) = 0 := by rw [hω2, map_zero]
    simpa [map_add, map_pow] using h
  rw [map_pow]
  linear_combination (C ω - 1 - X) * hω2KX

private lemma eigenspace_cube_eq_top {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) {ω : K} (hω3 : ω^3 = 1) (hω1 : ω ≠ 1) (hf3 : f^3 = 1) :
    Module.End.eigenspace f 1 ⊔ Module.End.eigenspace f ω ⊔ Module.End.eigenspace f (ω^2) = ⊤ := by
  have hω2 : ω^2 + ω + 1 = 0 := by
    have h : (ω - 1) * (ω^2 + ω + 1) = 0 := by
      have hh : ω^3 - 1 = (ω - 1) * (ω^2 + ω + 1) := by ring
      rw [← hh, hω3, sub_self]
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have hω2ne : ω^2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω * ω^2 := by rw [h, mul_one]
      _ = ω^3 := by ring
      _ = 1 := hω3
  have hω_ne : ω ≠ ω^2 := by
    intro h
    apply hω2ne
    calc ω^2 = ω * ω := by ring
      _ = ω * ω^2 := by rw [← h]
      _ = ω^3 := by ring
      _ = 1 := hω3
  set p1 : K[X] := X - C (1:K) with hp1
  set p2 : K[X] := X - C ω with hp2
  set p3 : K[X] := X - C (ω^2) with hp3
  have hcop12 : IsCoprime p1 p2 := by
    rw [hp1, hp2]
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hω1)))
  have hcop13 : IsCoprime p1 p3 := by
    rw [hp1, hp3]
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hω2ne)))
  have hcop23 : IsCoprime p2 p3 := by
    rw [hp2, hp3]
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hω_ne))
  have hcop1 : IsCoprime p1 (p2 * p3) := hcop12.mul_right hcop13
  have hpol2 : p2 * p3 = (X^2 + X + 1 : K[X]) := by
    rw [hp2, hp3]
    exact poly_cube_factor ω hω2
  have hpol1 : p1 * (X^2 + X + 1 : K[X]) = X^3 - 1 := by
    rw [hp1]
    simp only [Polynomial.C_1]
    ring
  have hmap1 : aeval f p1 = f - (1:K) • 1 := by
    rw [hp1, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have hmap2 : aeval f p2 = f - ω • 1 := by
    rw [hp2, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have hmap3 : aeval f p3 = f - (ω^2) • 1 := by
    rw [hp3, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have htop : LinearMap.ker (aeval f (X^3 - 1 : K[X])) = ⊤ := by
    have hae : aeval f (X^3 - 1 : K[X]) = 0 := by
      have h : aeval f (X^3 - 1 : K[X]) = f^3 - 1 := by simp
      rw [h, hf3, sub_self]
    rw [hae]
    exact LinearMap.ker_zero
  have h1 := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop1
  have h2 := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop23
  have hker1 : LinearMap.ker (aeval f p1) = Module.End.eigenspace f 1 := by
    rw [Module.End.eigenspace_def, hmap1]
  have hker2 : LinearMap.ker (aeval f p2) = Module.End.eigenspace f ω := by
    rw [Module.End.eigenspace_def, hmap2]
  have hker3 : LinearMap.ker (aeval f p3) = Module.End.eigenspace f (ω^2) := by
    rw [Module.End.eigenspace_def, hmap3]
  have hker23 : LinearMap.ker (aeval f (p2 * p3)) = LinearMap.ker (aeval f (X^2 + X + 1 : K[X])) := by
    rw [hpol2]
  have hker_top : LinearMap.ker (aeval f (p1 * (p2 * p3))) = ⊤ := by
    rw [show p1 * (p2 * p3) = X^3 - 1 by rw [hpol2, hpol1]]
    exact htop
  rw [hker1, hker23, hker_top] at h1
  rw [hker2, hker3, hker23] at h2
  rw [sup_assoc, h2]
  exact h1

private lemma iSup_maxGenEigenspace_eq_top_of_cube {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) {ω : K} (hω3 : ω^3 = 1) (hω1 : ω ≠ 1) (hf3 : f^3 = 1) :
    ⨆ μ : K, Module.End.maxGenEigenspace f μ = ⊤ := by
  have h3 := eigenspace_cube_eq_top f hω3 hω1 hf3
  refine le_antisymm le_top ?_
  calc (⊤ : Submodule K V)
      = Module.End.eigenspace f 1 ⊔ Module.End.eigenspace f ω ⊔ Module.End.eigenspace f (ω^2) := h3.symm
    _ ≤ Module.End.maxGenEigenspace f 1 ⊔ Module.End.maxGenEigenspace f ω ⊔
          Module.End.maxGenEigenspace f (ω^2) := by
        gcongr <;> exact Module.End.eigenspace_le_maxGenEigenspace
    _ ≤ ⨆ μ : K, Module.End.maxGenEigenspace f μ :=
        sup_le (sup_le (le_iSup _ 1) (le_iSup _ ω)) (le_iSup _ (ω^2))

private lemma exists_char_of_eigenvector {K V G : Type} [Field K] [AddCommGroup V] [Module K V]
    [Group G] (f : G → Module.End K V) (hf1 : f 1 = 1) (hfmul : ∀ x y, f (x*y) = f x * f y)
    (hinj : ∀ x, Function.Injective (f x)) (ψ : G → K) {v : V} (hv : v ≠ 0)
    (hvψ : ∀ x, f x v = ψ x • v) :
    ∃ χ : G →* Kˣ, ∀ x, (χ x : K) = ψ x := by
  have hne : ∀ x, ψ x ≠ 0 := fun x hx => by
    have : f x v = 0 := by rw [hvψ x, hx, zero_smul]
    exact hv (hinj x (by rw [this, map_zero]))
  have h1 : ψ 1 = 1 := by
    have h := hvψ 1
    rw [hf1] at h
    change v = ψ 1 • v at h
    have h2 : (ψ 1 - 1) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv
  have hmul : ∀ x y, ψ (x*y) = ψ x * ψ y := by
    intro x y
    have hxy : f x (f y v) = (ψ x * ψ y) • v := by
      rw [hvψ y, map_smul, hvψ x, smul_smul, mul_comm (ψ y) (ψ x)]
    have hxy2 : f (x*y) v = ψ (x*y) • v := hvψ (x*y)
    rw [hfmul, Module.End.mul_apply, hxy] at hxy2
    have h2 : (ψ (x*y) - ψ x * ψ y) • v = 0 := by rw [sub_smul, hxy2, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv
  refine ⟨{ toFun := fun x => Units.mk0 (ψ x) (hne x), map_one' := ?_, map_mul' := ?_ },
    fun x => rfl⟩
  · exact Units.ext (by simp [h1])
  · intro x y
    exact Units.ext (by simp [hmul x y])

private lemma cube_root_exists {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h : 3 ∣ (q + 1) * (q - 1) := dvd_mul_of_dvd_left hq3 _
    rw [← Nat.sq_sub_sq q 1] at h
    simpa using h
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvd
  exact ⟨ω, hω⟩

theorem outRank_bound {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    (E : Subgroup (GL (Fin n) K)) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (s : (Fin n → K) ≃+ (Fin n → K)) (hs : ∀ (c : K) (v : Fin n → K), s (c • v) = c ^ q • s v)
    (hsE : ∀ x ∈ E, ∀ v : Fin n → K,
      s ((x : Matrix (Fin n) (Fin n) K) *ᵥ v) = (x : Matrix (Fin n) (Fin n) K) *ᵥ s v)
    {r : ℕ} (hr : Nat.card E = 3 ^ r) : 2 * r ≤ n := by

  classical
  obtain ⟨ωu, hωu⟩ := cube_root_exists hK hq3
  let ω : K := ωu
  have hω3 : ω ^ 3 = 1 := by
    have : (ωu : K) ^ 3 = 1 := by
      have := IsPrimitiveRoot.pow_eq_one (IsPrimitiveRoot.iff_orderOf.mpr hωu)
      simpa using congrArg (fun u : Kˣ => (u : K)) this
    exact this
  have hω1 : ω ≠ 1 := by
    intro h
    have : (ωu : K) = 1 := h
    have : ωu = 1 := Units.ext this
    rw [this] at hωu
    simp at hωu
  let f : E → Module.End K (Fin n → K) :=
    fun x => Matrix.toLinAlgEquiv' (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
  have hf1 : f 1 = 1 := by simp [f]
  have hfmul : ∀ x y : E, f (x * y) = f x * f y := by
    intro x y
    simp only [f, Subgroup.coe_mul, Units.val_mul, map_mul]
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
        (((y : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) :=
      (Matrix.toLinAlgEquiv' (n := Fin n) (R := K)).injective hxy
    exact Subtype.ext (Units.ext h1)
  have hinj : ∀ x : E, Function.Injective (f x) := by
    intro x u v huv
    exact Matrix.mulVec_injective_of_isUnit (A := (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K))
      (x : GL (Fin n) K).isUnit (by simpa only [f, Matrix.toLinAlgEquiv'_apply] using huv)
  have hpow : ∀ x : E, (f x) ^ 3 = 1 := by
    intro x
    have hx : (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
      simpa using congrArg (Units.val) (hE3 (x : GL (Fin n) K) x.2)
    have := congrArg (Matrix.toLinAlgEquiv' (n := Fin n) (R := K)) hx
    simpa only [f, map_pow, map_one] using this
  have hx3 : ∀ x : E, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    simpa using hE3 (x : GL (Fin n) K) x.2
  have h3ne : (3 : K) ≠ 0 := by
    have h3eq : (3 : K) = 1 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      calc (3 : K) = (2 : K) + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
    rw [h3eq]
    exact one_ne_zero
  have hsep : (X ^ 3 - 1 : K[X]).Separable := by
    rw [X_pow_sub_one_separable_iff]
    exact h3ne
  have hss : ∀ x : E, Module.End.IsSemisimple (f x) := by
    intro x
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree ?_
    have h : aeval (f x) (X ^ 3 - 1 : K[X]) = (f x) ^ 3 - 1 := by simp
    rw [h, hpow x, sub_self]
  have hcomm' : ∀ x y : E, Commute (f x) (f y) := by
    intro x y
    rw [Commute, SemiconjBy]
    have hxy : (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * (((y : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
        (((y : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
      simpa using congrArg (Units.val) (hEc (x : GL (Fin n) K) x.2 (y : GL (Fin n) K) y.2)
    show f x * f y = f y * f x
    simp only [f, ← map_mul]
    rw [hxy]
  have hcomm : Pairwise (fun x y : E => Commute (f x) (f y)) := fun x y _ => hcomm' x y
  have hmax : ∀ x : E, ⨆ μ : K, Module.End.maxGenEigenspace (f x) μ = ⊤ :=
    fun x => iSup_maxGenEigenspace_eq_top_of_cube (f x) hω3 hω1 (hpow x)
  have hdecomp_max := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (ι := E) f hcomm hmax
  have hmaxeq : ∀ x : E, ∀ μ : K,
      Module.End.maxGenEigenspace (f x) μ = Module.End.eigenspace (f x) μ :=
    fun x μ => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (Module.End.IsSemisimple.isFinitelySemisimple (hss x)) μ
  let Wf : (E → K) → Submodule K (Fin n → K) :=
    fun ψ => ⨅ x : E, Module.End.eigenspace (f x) (ψ x)
  have hdecomp : ⨆ ψ : E → K, Wf ψ = ⊤ := by
    show (⨆ ψ : E → K, ⨅ x : E, Module.End.eigenspace (f x) (ψ x)) = ⊤
    simpa only [hmaxeq] using hdecomp_max
  have hmaps : ∀ i j : E, ∀ φ : K,
      Set.MapsTo (f i) (Module.End.maxGenEigenspace (f j) φ) (Module.End.maxGenEigenspace (f j) φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm' j i) φ
  have hindep_max := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (f := f) hmaps
  have hindep : iSupIndep Wf := by
    show iSupIndep (fun ψ : E → K => ⨅ x : E, Module.End.eigenspace (f x) (ψ x))
    simpa only [hmaxeq] using hindep_max
  have hfne : ∀ x : E, x ≠ 1 → f x ≠ 1 := by
    intro x hx h
    exact hx (hfinj (by rw [h, hf1]))
  have hsep_psi : ∀ x₀ : E, x₀ ≠ 1 → ∃ ψ : E → K, Wf ψ ≠ ⊥ ∧ ψ x₀ ≠ 1 := by
    intro x₀ hx₀
    by_contra h
    have h : ∀ ψ : E → K, Wf ψ ≠ ⊥ → ψ x₀ = 1 := by
      intro ψ hψ
      by_contra hψx
      exact h ⟨ψ, hψ, hψx⟩
    have hfm : f x₀ = 1 := by
      have hker : (⊤ : Submodule K (Fin n → K)) ≤ LinearMap.ker (f x₀ - 1) := by
        rw [← hdecomp]
        refine iSup_le fun ψ => ?_
        by_cases hψ : Wf ψ = ⊥
        · rw [hψ]; exact bot_le
        · intro v hv
          rw [LinearMap.mem_ker]
          have hvv : f x₀ v = ψ x₀ • v :=
            Module.End.mem_eigenspace_iff.mp
              ((Submodule.mem_iInf (fun x : E => Module.End.eigenspace (f x) (ψ x))).mp hv x₀)
          rw [LinearMap.sub_apply, hvv, h ψ hψ, one_smul]
          simp
      have : (f x₀ - 1) = 0 := LinearMap.ext fun v => by
        have := hker (Submodule.mem_top : v ∈ ⊤)
        simpa using this
      exact sub_eq_zero.mp this
    exact hfne x₀ hx₀ hfm
  have hsep_char : ∀ x₀ : E, x₀ ≠ 1 → ∃ χ : E →* Kˣ,
      (⨅ x : E, Module.End.eigenspace (f x) (((χ x : Kˣ) : K))) ≠ ⊥ ∧ (χ x₀ : K) ≠ 1 := by
    intro x₀ hx₀
    obtain ⟨ψ, hψ, hψx⟩ := hsep_psi x₀ hx₀
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (Wf ψ)).mp hψ
    have hvψ : ∀ x, f x v = ψ x • v := fun x =>
      Module.End.mem_eigenspace_iff.mp
        ((Submodule.mem_iInf (fun y : E => Module.End.eigenspace (f y) (ψ y))).mp hv x)
    obtain ⟨χ, hχ⟩ := exists_char_of_eigenvector f hf1 hfmul hinj ψ hv0 hvψ
    refine ⟨χ, ?_, ?_⟩
    · have : (⨅ x : E, Module.End.eigenspace (f x) (((χ x : Kˣ) : K))) = Wf ψ := by
        show (⨅ x : E, Module.End.eigenspace (f x) (((χ x : Kˣ) : K))) =
          (⨅ x : E, Module.End.eigenspace (f x) (ψ x))
        congr 1
        ext x
        rw [hχ x]
      rw [this]; exact hψ
    · rw [hχ x₀]; exact hψx
  let W : (E →* Kˣ) → Submodule K (Fin n → K) := fun χ => Wf (fun x => ((χ x : Kˣ) : K))
  let g : (E →* Kˣ) → (E → K) := fun χ x => ((χ x : Kˣ) : K)
  have hg_inj : Function.Injective g := by
    intro χ ψ h
    ext x
    exact congrFun h x
  have hindep_W : iSupIndep W := by
    show iSupIndep (fun χ : E →* Kˣ => Wf (fun x => ((χ x : Kˣ) : K)))
    exact hindep.comp hg_inj
  have hchi3 : ∀ (χ : E →* Kˣ) (x : E), (((χ x : Kˣ) : K)) ^ 3 = 1 := by
    intro χ x
    have : (χ x : Kˣ) ^ 3 = 1 := by rw [← map_pow, hx3 x, map_one]
    simpa using congrArg (fun u : Kˣ => (u : K)) this
  have hqinv : ∀ (ζ : Kˣ), (ζ : K) ^ 3 = 1 → (ζ : K) ^ q = ((ζ⁻¹ : Kˣ) : K) := by
    intro ζ hζ
    obtain ⟨k, hk⟩ := hq3
    have h1 : (ζ : K) ^ (q + 1) = 1 := by
      rw [hk, pow_mul, hζ, one_pow]
    have h2 : (ζ : K) ^ q * (ζ : K) = 1 := by rw [← pow_succ, h1]
    have hζ0 : (ζ : K) ≠ 0 := Units.ne_zero ζ
    have h3 : (ζ : K) ^ q = (ζ : K)⁻¹ :=
      mul_right_cancel₀ hζ0 (by rw [h2, inv_mul_cancel₀ hζ0])
    rw [h3]
    simp
  have hsW : ∀ χ : E →* Kˣ, ∀ v ∈ W χ, s v ∈ W (χ⁻¹) := by
    intro χ v hv
    rw [Submodule.mem_iInf]
    intro x
    rw [Module.End.mem_eigenspace_iff]
    have hvx : f x v = ((χ x : Kˣ) : K) • v :=
      Module.End.mem_eigenspace_iff.mp
        ((Submodule.mem_iInf (fun y : E => Module.End.eigenspace (f y) (((χ y : Kˣ) : K)))).mp hv x)
    have hsx : s (f x v) = f x (s v) := by
      simpa only [f, Matrix.toLinAlgEquiv'_apply] using hsE (x : GL (Fin n) K) x.2 v
    have hsq : s (((χ x : Kˣ) : K) • v) = ((χ x : Kˣ) : K) ^ q • s v := hs _ v
    rw [← hsx, hvx, hsq, hqinv (χ x) (hchi3 χ x)]
    simp
  haveI : Fintype (E →* Kˣ) := Fintype.ofFinite _
  let Λ : Finset (E →* Kˣ) := Finset.univ.filter (fun χ => W χ ≠ ⊥)
  let S : Finset (E →* Kˣ) := Λ.erase 1
  have hS_mem : ∀ χ : E →* Kˣ, χ ∈ S ↔ χ ≠ 1 ∧ W χ ≠ ⊥ := by
    intro χ
    simp only [S, Λ, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  have hS_inv : ∀ χ ∈ S, χ⁻¹ ∈ S := by
    intro χ hχ
    rw [hS_mem] at hχ ⊢
    obtain ⟨hχ1, hWχ⟩ := hχ
    refine ⟨?_, ?_⟩
    · intro h
      apply hχ1
      ext x
      have hx : (χ x)⁻¹ = 1 := by
        simpa using congrArg (fun ψ : E →* Kˣ => ψ x) h
      rw [inv_eq_one] at hx
      simpa using congrArg (fun u : Kˣ => (u : K)) hx
    · intro hbot
      apply hWχ
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv' := hsW χ v hv
      rw [hbot] at hv'
      have hs0 : s v = 0 := by simpa using hv'
      exact s.injective (by rw [hs0, map_zero])
  have hS_ne_inv : ∀ χ ∈ S, χ ≠ χ⁻¹ := by
    intro χ hχ h
    rw [hS_mem] at hχ
    obtain ⟨hχ1, _⟩ := hχ
    apply hχ1
    ext x
    have h1 : χ x = (χ x)⁻¹ := by
      simpa using congrArg (fun ψ : E →* Kˣ => ψ x) h
    have h3 : (χ x : Kˣ) ^ 3 = 1 := by rw [← map_pow, hx3 x, map_one]
    have h2 : (χ x : Kˣ) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      rw [mul_inv_cancel]
    have hone : (χ x : Kˣ) = 1 := by
      calc (χ x : Kˣ) = (χ x : Kˣ) ^ 3 * ((χ x : Kˣ) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2, inv_one, mul_one]
    simpa using congrArg (fun u : Kˣ => (u : K)) hone
  let idx : (E →* Kˣ) → ℕ := fun χ => (Fintype.equivFin (E →* Kˣ) χ).val
  have hidx_inj : Function.Injective idx := by
    intro a b h
    exact (Fintype.equivFin (E →* Kˣ)).injective (Fin.ext h)
  let P : Finset (E →* Kˣ) := S.filter (fun χ => idx χ < idx χ⁻¹)
  let P' : Finset (E →* Kˣ) := S.filter (fun χ => ¬ idx χ < idx χ⁻¹)
  have hP_mem : ∀ χ, χ ∈ P ↔ χ ∈ S ∧ idx χ < idx χ⁻¹ := by
    intro χ; simp only [P, Finset.mem_filter]
  have hP'_mem : ∀ χ, χ ∈ P' ↔ χ ∈ S ∧ ¬ idx χ < idx χ⁻¹ := by
    intro χ; simp only [P', Finset.mem_filter]
  have himage : P.image (fun χ => χ⁻¹) = P' := by
    ext χ
    rw [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hP_mem] at hy
      obtain ⟨hyS, hy⟩ := hy
      rw [hP'_mem]
      exact ⟨hS_inv y hyS, by rw [inv_inv y]; exact not_lt.mpr hy.le⟩
    · intro hχ
      rw [hP'_mem] at hχ
      obtain ⟨hχS, hχ⟩ := hχ
      refine ⟨χ⁻¹, ?_, by rw [inv_inv χ]⟩
      rw [hP_mem]
      refine ⟨hS_inv χ hχS, ?_⟩
      rw [inv_inv χ]
      exact lt_of_le_of_ne (not_lt.mp hχ) (fun h => hS_ne_inv χ hχS (hidx_inj h).symm)
  have hP'card : P'.card = P.card := by
    rw [← himage]
    exact Finset.card_image_of_injOn (fun a _ b _ h => inv_injective h)
  have hS_card : S.card = 2 * P.card := by
    have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun χ => idx χ < idx χ⁻¹)
    change P.card + P'.card = S.card at h
    rw [hP'card] at h
    omega
  have hroots : Nat.card (rootsOfUnity 3 K) = 3 :=
    IsPrimitiveRoot.card_rootsOfUnity
      (IsPrimitiveRoot.iff_orderOf.mpr (by rw [orderOf_units]; exact hωu))
  let Φ : E → (P → rootsOfUnity 3 K) := fun x χ =>
    rootsOfUnity.mkOfPowEq ((χ.1 x : Kˣ) : K) (hchi3 χ.1 x)
  have hΦ_inj : Function.Injective Φ := by
    intro x y hxy
    have hP' : ∀ χ ∈ P, χ x = χ y := by
      intro χ hχ
      apply Units.ext
      have h1 := congrArg (fun z : P → rootsOfUnity 3 K =>
        (((z ⟨χ, hχ⟩ : rootsOfUnity 3 K) : Kˣ) : K)) hxy
      simpa only [Φ, rootsOfUnity.coe_mkOfPowEq] using h1
    have hS' : ∀ ψ ∈ S, ψ x = ψ y := by
      intro ψ hψ
      by_cases hψP : ψ ∈ P
      · exact hP' ψ hψP
      · have hnot : ¬ idx ψ < idx ψ⁻¹ := by
          intro h; exact hψP ((hP_mem ψ).mpr ⟨hψ, h⟩)
        have hψinv : ψ⁻¹ ∈ P := by
          rw [hP_mem]
          refine ⟨hS_inv ψ hψ, ?_⟩
          rw [inv_inv ψ]
          exact lt_of_le_of_ne (not_lt.mp hnot) (fun h => hS_ne_inv ψ hψ (hidx_inj h).symm)
        have h2 := hP' ψ⁻¹ hψinv
        have h3 : (ψ x)⁻¹ = (ψ y)⁻¹ := by simpa using h2
        exact inv_injective h3
    have hmem : ∀ ψ ∈ Λ, ψ x = ψ y := by
      intro ψ hψΛ
      by_cases hψ1 : ψ = 1
      · rw [hψ1]; rfl
      · exact hS' ψ (Finset.mem_erase.mpr ⟨hψ1, hψΛ⟩)
    by_contra hne
    have hxy1 : x * y⁻¹ ≠ 1 := by
      intro h
      apply hne
      have : x = y := by
        calc x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
          _ = 1 * y := by rw [h]
          _ = y := by rw [one_mul]
      exact this
    obtain ⟨ψ, hψW, hψv⟩ := hsep_char (x * y⁻¹) hxy1
    have hψΛ : ψ ∈ Λ := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hψW⟩
    have hxy' := hmem ψ hψΛ
    have h1 : ((ψ (x * y⁻¹) : Kˣ) : K) = 1 := by
      have h2 : ψ (x * y⁻¹) = 1 := by rw [map_mul, hxy', map_inv, mul_inv_cancel]
      simpa using congrArg (fun u : Kˣ => (u : K)) h2
    exact hψv h1
  have hcard_le : Nat.card E ≤ Nat.card (P → rootsOfUnity 3 K) :=
    Nat.card_le_card_of_injective Φ hΦ_inj
  have hcardP : Nat.card P = P.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcard_fun : Nat.card (P → rootsOfUnity 3 K) = 3 ^ P.card := by
    rw [Nat.card_fun, hroots, hcardP]
  have hr_le : r ≤ P.card := by
    have h1 : 3 ^ r ≤ 3 ^ P.card := by
      calc 3 ^ r = Nat.card E := hr.symm
        _ ≤ Nat.card (P → rootsOfUnity 3 K) := hcard_le
        _ = 3 ^ P.card := hcard_fun
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
  have hS_le_n : S.card ≤ n := by
    let p : {χ : E →* Kˣ // χ ∈ S} → Submodule K (Fin n → K) := fun χ => W χ.1
    have hp : iSupIndep p := by
      show iSupIndep (W ∘ Subtype.val)
      exact hindep_W.comp Subtype.val_injective
    have hne : ∀ χ : {χ : E →* Kˣ // χ ∈ S}, W χ.1 ≠ ⊥ := fun χ => ((hS_mem χ.1).mp χ.2).2
    let v : {χ : E →* Kˣ // χ ∈ S} → (Fin n → K) := fun χ =>
      Classical.choose ((Submodule.ne_bot_iff (W χ.1)).mp (hne χ))
    have hv : ∀ χ, v χ ∈ p χ := fun χ =>
      (Classical.choose_spec ((Submodule.ne_bot_iff (W χ.1)).mp (hne χ))).1
    have hv0 : ∀ χ, v χ ≠ 0 := fun χ =>
      (Classical.choose_spec ((Submodule.ne_bot_iff (W χ.1)).mp (hne χ))).2
    have hlin : LinearIndependent K v := iSupIndep.linearIndependent p hp hv hv0
    have hcard := LinearIndependent.fintype_card_le_finrank hlin
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin] at hcard
    exact hcard
  omega

end

end CFSG.StandardType.TablePThreeKG

end
