module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1PairAlg
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1PairNorm
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Embed
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pieces
import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
import CFSG.Timmesfeld.Transvection.RelBuildField

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

private lemma q2cO4t_algebraMap_injective {K K' : Type} [Field K] [Field K'] [Algebra K K'] :
    Function.Injective (algebraMap K K') := by
  intro a b hab
  by_contra hne
  have hne0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h0 : algebraMap K K' (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h1 : (1 : K') = 0 := by
    calc (1 : K') = algebraMap K K' 1 := (map_one (algebraMap K K')).symm
      _ = algebraMap K K' ((a - b) * (a - b)⁻¹) := by rw [mul_inv_cancel₀ hne0]
      _ = algebraMap K K' (a - b) * algebraMap K K' ((a - b)⁻¹) :=
            map_mul (algebraMap K K') (a - b) ((a - b)⁻¹)
      _ = 0 := by rw [h0, zero_mul]
  exact one_ne_zero h1

theorem TBJOmData.exists_normTriple {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r)
    {f : ℕ} (hf : Nat.card K = 2 ^ f) (hpq : p ∣ Nat.card K + 1) (K' : Type) [Field K'] [Finite K']
    [CharP K' 2] (hK' : Nat.card K' = (2 ^ f) ^ 2) (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ∃ (_ : Algebra K K') (T : NormTriple Q (unitaryInvolution K' 2 f)) (ζ : K'),
      ∀ (g : Fin r → Multiplicative (ZMod p)) (z : Fin 3 → K'),
        Δ.τ g (T.incl z) = T.incl (fun l => ζ ^ (toAdd (g (![i, j, k] l))).val * z l) := by
  classical
  obtain ⟨inst, ψ, ζ, t, ht, hψ, hspan, hζ, hσζ, hσ⟩ :=
    (Δ.rk1Block hp2).exists_algebra_linearEquiv hf hpq K' hK'
  letI := inst
  have hinj : Function.Injective (algebraMap K K') := q2cO4t_algebraMap_injective
  let idx : Fin 3 → Fin r := ![i, j, k]
  have hidx : Function.Injective idx := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [idx]
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
  have hqD : ∀ l : Fin 3, ∀ y : Δ.D,
      (Q.comp (Δ.θ (idx l))) (Δ.c y) = (Q.comp (Δ.θ (idx l))) y := by
    intro l y
    let g₁ : Fin r → Multiplicative (ZMod p) := Pi.mulSingle (idx l) (ofAdd (1 : ZMod p))
    have hval : (toAdd (g₁ (idx l))).val = 1 := by
      have h1 : toAdd (g₁ (idx l)) = (1 : ZMod p) := by simp [g₁]
      rw [h1]
      exact ZMod.val_one'' (Fact.out : p.Prime).ne_one
    have htheta : Δ.τ g₁ (Δ.θ (idx l) y) = Δ.θ (idx l) (Δ.c y) := by
      rw [Δ.tau_theta g₁ (idx l) y, hval, pow_one]
    have hmemA : Δ.τ g₁ ∈ A :=
      (le_of_eq Δ.τ_range) (MonoidHom.mem_range.mpr ⟨g₁, rfl⟩)
    have hiso : ∀ m : V, Q (Δ.τ g₁ m) = Q m :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q (hAΩ hmemA))
    calc (Q.comp (Δ.θ (idx l))) (Δ.c y)
        = Q (Δ.θ (idx l) (Δ.c y)) := rfl
      _ = Q (Δ.τ g₁ (Δ.θ (idx l) y)) := by rw [htheta]
      _ = Q (Δ.θ (idx l) y) := hiso _
      _ = (Q.comp (Δ.θ (idx l))) y := rfl
  have hnorm : ∀ l : Fin 3, ∃ μ : K, ∀ x : K',
      algebraMap K K' (Q (Δ.θ (idx l) (ψ x))) =
        algebraMap K K' μ * (unitaryInvolution K' 2 f x * x) := by
    intro l
    exact exists_quadForm_eq_norm (unitaryInvolution K' 2 f) ψ Δ.c ζ t ht hψ hspan hζ hσζ hσ
      (Q.comp (Δ.θ (idx l))) (hqD l)
  choose μ hμ using hnorm
  have hμne : ∀ l : Fin 3, μ l ≠ 0 := by
    intro l h0
    have hzero : ∀ y : Δ.D, Q (Δ.θ (idx l) y) = 0 := by
      intro y
      obtain ⟨x, rfl⟩ := ψ.surjective y
      have h1 := hμ l x
      rw [h0, map_zero, zero_mul] at h1
      exact hinj (h1.trans (map_zero (algebraMap K K')).symm)
    have hbot : Δ.F.U (idx l) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro u hu
      refine Δ.F.nondeg (idx l) u hu fun v hv => ?_
      rw [← Δ.θ_range (idx l)] at hu hv
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hu
      obtain ⟨y', rfl⟩ := LinearMap.mem_range.mp hv
      change Q (Δ.θ (idx l) y' + Δ.θ (idx l) y) - Q (Δ.θ (idx l) y')
        - Q (Δ.θ (idx l) y) = 0
      rw [← map_add, hzero (y' + y), hzero y', hzero y, sub_zero, sub_zero]
    exact Δ.F.ne_bot (idx l) hbot
  have hσU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution K' 2 f) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := K') (p := 2)
      (f := f) hK'
  have hlam_ex : ∀ l : Fin 3, ∃ lam : K',
      unitaryInvolution K' 2 f lam * lam = (algebraMap K K' (μ l))⁻¹ := by
    intro l
    apply hσU.exists_norm
    simp [map_inv₀, hσ]
  choose lam hlam using hlam_ex
  let φ : Fin 3 → (K' →ₗ[K] V) := fun l =>
    (Δ.θ (idx l)).comp (ψ.toLinearMap.comp (LinearMap.mulLeft K (lam l)))
  have hφ : ∀ l x, φ l x = Δ.θ (idx l) (ψ (lam l * x)) := fun l x => rfl
  have hQφ : ∀ l x, algebraMap K K' (Q (φ l x)) = unitaryInvolution K' 2 f x * x := by
    intro l x
    have hAmu_ne : algebraMap K K' (μ l) ≠ 0 :=
      fun h => hμne l (hinj (h.trans (map_zero (algebraMap K K')).symm))
    have hAc : algebraMap K K' (μ l) * (unitaryInvolution K' 2 f (lam l) * lam l) = 1 := by
      rw [hlam l, mul_inv_cancel₀ hAmu_ne]
    rw [hφ l x, hμ l (lam l * x), map_mul (unitaryInvolution K' 2 f) (lam l) x]
    rw [show algebraMap K K' (μ l) *
          ((unitaryInvolution K' 2 f (lam l) * unitaryInvolution K' 2 f x) * (lam l * x))
        = (algebraMap K K' (μ l) *
            (unitaryInvolution K' 2 f (lam l) * lam l)) *
          (unitaryInvolution K' 2 f x * x) by ring,
      hAc, one_mul]
  have horth : ∀ j k : Fin 3, j ≠ k → ∀ x y, polar Q (φ j x) (φ k y) = 0 := by
    intro j k hjk x y
    exact Δ.F.orth (idx j) (idx k) (fun h => hjk (hidx h)) (φ j x)
      (by
        rw [← Δ.θ_range (idx j)]
        exact LinearMap.mem_range.mpr ⟨ψ (lam j * x), rfl⟩)
      (φ k y)
      (by
        rw [← Δ.θ_range (idx k)]
        exact LinearMap.mem_range.mpr ⟨ψ (lam k * y), rfl⟩)
  have hact_aux : ∀ (g : Fin r → Multiplicative (ZMod p)) (l : Fin 3) (x : K'),
      Δ.τ g (Δ.θ (idx l) (ψ (lam l * x))) =
        Δ.θ (idx l) (ψ (lam l * (ζ ^ (toAdd (g (idx l))).val * x))) := by
    intro g l x
    rw [Δ.tau_theta g (idx l) (ψ (lam l * x)),
      hpow (toAdd (g (idx l))).val (lam l * x),
      mul_left_comm (ζ ^ (toAdd (g (idx l))).val) (lam l) x]
  have hact : ∀ (g : Fin r → Multiplicative (ZMod p)) (l : Fin 3) (x : K'),
      Δ.τ g (φ l x) = φ l (ζ ^ (toAdd (g (idx l))).val * x) := by
    intro g l x
    rw [hφ l x, hφ l]
    exact hact_aux g l x
  let T : NormTriple Q (unitaryInvolution K' 2 f) := ⟨φ, hQφ, horth⟩
  have hTφ : T.φ = φ := rfl
  refine ⟨inst, T, ζ, fun g z => ?_⟩
  let z' : Fin 3 → K' := fun l => ζ ^ (toAdd (g (![i, j, k] l))).val * z l
  change Δ.τ g (T.incl z) = T.incl z'
  have h1 : T.incl z = φ 0 (z 0) + φ 1 (z 1) + φ 2 (z 2) := by
    simp only [NormTriple.incl_apply, hTφ]
  have h2 : T.incl z' = φ 0 (z' 0) + φ 1 (z' 1) + φ 2 (z' 2) := by
    simp only [NormTriple.incl_apply, hTφ]
  rw [h1, h2, map_add, map_add, hact g 0 (z 0), hact g 1 (z 1), hact g 2 (z 2)]
section SixDickson

variable {K' : Type} [Field K'] [Finite K'] [CharP K' 2] [Algebra K K'] {σ : K' ≃+* K'}
  {Q : QuadraticForm K V}

open CFSG.ClassicalGroups.Unitary CFSG.Timmesfeld.Transvection.RelBuild
open CFSG.LieType.Universal.Unitary
open CFSG.RankThree.OrthogonalInvolutions
  (commSpace mem_commSpace sub_mem_commSpace omegaGroup mem_omegaGroup omegaGroup_le
    relIndex_omegaGroup)

theorem six_finrank_K' {f : ℕ} (hK : Nat.card K = 2 ^ f) (hK' : Nat.card K' = (2 ^ f) ^ 2) :
    Module.finrank K K' = 2 := by
  haveI := Fintype.ofFinite K
  have hK2 : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hK
    omega
  have h2 : 2 ≤ Nat.card K := by
    rw [hK]
    exact Nat.succ_le_of_lt ((one_lt_pow_iff (x := 2) hf0).mpr (by decide))
  have hbase : Nat.card K' = Nat.card K ^ 2 := by
    rw [hK', hK]
  have hcard : Nat.card K' = Nat.card K ^ Module.finrank K K' := Module.natCard_eq_pow_finrank
  rw [hbase] at hcard
  exact Nat.pow_right_injective h2 hcard.symm

noncomputable def normTripleU : Submodule K (Fin 3 → K') where
  carrier := {z | z 0 = z 1 ∧ z 2 = 0}
  zero_mem' := by simp
  add_mem' hz hw := by
    refine ⟨?_, ?_⟩
    · simp [hz.1, hw.1]
    · simp [hz.2, hw.2]
  smul_mem' c z hz := by
    refine ⟨?_, ?_⟩
    · simp [hz.1]
    · simp [hz.2]

theorem normTripleU_finrank {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) :
    Module.finrank K (normTripleU (K := K) (K' := K')) = 2 := by
  let e : K' →ₗ[K] normTripleU (K := K) (K' := K') :=
    { toFun := fun u => ⟨![u, u, 0], by
        refine ⟨?_, ?_⟩
        · simp
        · simp⟩
      map_add' := by
        intro u w
        ext i
        fin_cases i <;> simp
      map_smul' := by
        intro c u
        ext i
        fin_cases i <;> simp }
  have he : Function.Bijective e := by
    constructor
    · intro u w h
      have := congrArg (fun z : normTripleU (K := K) (K' := K') => (z : Fin 3 → K') 0) h
      simpa [e] using this
    · intro z
      refine ⟨(z : Fin 3 → K') 0, ?_⟩
      apply Subtype.ext
      funext i
      fin_cases i
      · simp [e]
      · simp [e, z.2.1]
      · simp [e, z.2.2]
  have hfin : Module.finrank K (normTripleU (K := K) (K' := K')) = Module.finrank K K' :=
    (LinearEquiv.ofBijective e he).finrank_eq.symm
  rw [hfin]
  exact six_finrank_K' hK hK'

noncomputable def sixW (T : NormTriple Q σ) : Submodule K V := LinearMap.range T.incl

noncomputable def sixEW (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    (Fin 3 → K') ≃ₗ[K] sixW (Q := Q) T :=
  LinearEquiv.ofInjective T.incl (T.incl_injective hσ)

noncomputable def sixUW (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    Submodule K (sixW (Q := Q) T) :=
  normTripleU.map (sixEW (Q := Q) T hσ).toLinearMap

noncomputable abbrev sixQW (T : NormTriple Q σ) : QuadraticForm K (sixW (Q := Q) T) :=
  Q.comp (sixW (Q := Q) T).subtype

noncomputable abbrev sixBW (T : NormTriple Q σ) : LinearMap.BilinForm K (sixW (Q := Q) T) :=
  polarBilin (sixQW (Q := Q) T)

@[simp] theorem sixEW_apply (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (z : Fin 3 → K') : ((sixEW (Q := Q) T hσ z : sixW (Q := Q) T) : V) = T.incl z := by
  change ((LinearEquiv.ofInjective T.incl (T.incl_injective hσ)) z : V) = T.incl z
  exact LinearEquiv.ofInjective_apply (f := T.incl) (h := T.incl_injective hσ) z

@[simp] theorem sixQW_sixEW (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (z : Fin 3 → K') : sixQW (Q := Q) T (sixEW (Q := Q) T hσ z) = Q (T.incl z) := by
  change Q ↑(sixEW (Q := Q) T hσ z) = Q (T.incl z)
  rw [sixEW_apply]

@[simp] theorem sixBW_sixEW (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (z y : Fin 3 → K') :
    sixBW (Q := Q) T (sixEW (Q := Q) T hσ z) (sixEW (Q := Q) T hσ y) =
      polar Q (T.incl z) (T.incl y) := by
  change polar Q ↑(sixEW (Q := Q) T hσ z) ↑(sixEW (Q := Q) T hσ y) = polar Q (T.incl z) (T.incl y)
  rw [sixEW_apply, sixEW_apply]

theorem six_finrank {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    Module.finrank K ↥(sixW (Q := Q) T) = 6 := by
  rw [sixW, LinearMap.finrank_range_of_inj (T.incl_injective hσ)]
  rw [Module.finrank_pi_fintype]
  simp [six_finrank_K' hK hK']

theorem six_nondegenerate (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    (sixBW (Q := Q) T).Nondegenerate := by
  constructor
  · intro x hx
    obtain ⟨z, rfl⟩ := (sixEW (Q := Q) T hσ).surjective x
    have hz : z = 0 := T.eq_zero_of_polar hσ fun y => by
      have h := hx (sixEW (Q := Q) T hσ y)
      change polar Q (T.incl z) (T.incl y) = 0 at h
      exact h
    simp [hz]
  · intro x hx
    obtain ⟨z, rfl⟩ := (sixEW (Q := Q) T hσ).surjective x
    have hz : z = 0 := T.eq_zero_of_polar hσ fun y => by
      have h := hx (sixEW (Q := Q) T hσ y)
      change polar Q (T.incl y) (T.incl z) = 0 at h
      simpa only [polar_comm] using h
    simp [hz]

theorem six_U_finrank {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    Module.finrank K ↥(sixUW (Q := Q) T hσ) = 2 := by
  rw [sixUW, LinearEquiv.finrank_map_eq]
  exact normTripleU_finrank hK hK'

theorem six_U_perp_aniso (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    {x : sixW (Q := Q) T} (hx : x ∈ (sixBW (Q := Q) T).orthogonal (sixUW (Q := Q) T hσ))
    (hxnot : x ∉ sixUW (Q := Q) T hσ) : sixQW (Q := Q) T x ≠ 0 := by
  obtain ⟨z, rfl⟩ := (sixEW (Q := Q) T hσ).surjective x
  intro hQ0
  apply hxnot
  have hQz : Q (T.incl z) = 0 := by
    change Q (T.incl z) = 0 at hQ0
    exact hQ0
  have hS : z 0 = z 1 := by
    have htrace : ∀ v : K', σ (z 0 + z 1) * v + σ (σ (z 0 + z 1) * v) = 0 := by
      intro v
      have hy : sixEW (Q := Q) T hσ ![v, v, 0] ∈ sixUW (Q := Q) T hσ := by
        exact Submodule.mem_map.mpr ⟨![v, v, 0], by simp [normTripleU], rfl⟩
      have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) (sixEW (Q := Q) T hσ ![v, v, 0]) hy
      have hp := T.polar_incl hσ.invol ![v, v, 0] z
      have hherm : herm σ ![v, v, 0] z = σ v * (z 0 + z 1) := by
        simp [herm, Fin.sum_univ_three]
        ring
      have hp0 : polar Q (T.incl ![v, v, 0]) (T.incl z) = 0 := by
        change polar Q (T.incl ![v, v, 0]) (T.incl z) = 0 at h0
        exact h0
      have hzero : herm σ ![v, v, 0] z + σ (herm σ ![v, v, 0] z) = 0 := by
        rw [← hp, hp0, map_zero]
      rw [hherm] at hzero
      simpa [hσ.invol, mul_comm, mul_left_comm, mul_assoc, map_add, map_mul, add_comm, add_left_comm, add_assoc] using hzero
    have hκ : σ (z 0 + z 1) = 0 := eq_zero_of_trace_mul hσ.exists_ne htrace
    exact CharTwo.add_eq_zero.mp ((map_eq_zero σ).mp hκ)
  have hz2 : z 2 = 0 := by
    have hherm_self : herm σ z z = 0 := by
      have hp := T.Q_incl z
      rw [hQz, map_zero] at hp
      exact hp.symm
    rw [herm, Fin.sum_univ_three] at hherm_self
    rw [hS] at hherm_self
    have hN : σ (z 2) * z 2 = 0 := by
      simpa [CharTwo.add_self_eq_zero] using hherm_self
    by_contra hz2
    exact (mul_ne_zero ((map_ne_zero σ).mpr hz2) hz2) hN
  exact Submodule.mem_map.mpr ⟨z, ⟨hS, hz2⟩, rfl⟩

theorem noTS_of_totally_singular_plane {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (R : QuadraticForm K W)
    (hB : (polarBilin R).Nondegenerate) (hWdim : finrank K W = 6)
    (U : Submodule K W) (hUdim : finrank K U = 2)
    (hAniso : ∀ x, x ∈ LinearMap.BilinForm.orthogonal (polarBilin R) U → x ∉ U → R x ≠ 0) :
    ∀ U₀ : Submodule K W, finrank K U₀ = 3 → ∃ u ∈ U₀, R u ≠ 0 := by
  intro U₀ hdim
  by_contra h
  push Not at h
  set P := LinearMap.BilinForm.orthogonal (polarBilin R) U with hP
  have hPdim : finrank K ↥P = 4 := by
    rw [hP, LinearMap.BilinForm.finrank_orthogonal hB U, hUdim, hWdim]
  have hinter_ne : U₀ ⊓ P ≠ ⊥ := by
    intro hbot
    have hsupdim : finrank K ↥(U₀ ⊔ P) + finrank K ↥(U₀ ⊓ P) =
        finrank K ↥U₀ + finrank K ↥P :=
      Submodule.finrank_sup_add_finrank_inf_eq U₀ P
    rw [hbot, hdim, hPdim, finrank_bot] at hsupdim
    have hle : finrank K ↥(U₀ ⊔ P) ≤ finrank K W := Submodule.finrank_le _
    rw [hWdim] at hle
    omega
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff (U₀ ⊓ P)).mp hinter_ne
  obtain ⟨huU₀, huP⟩ := hu
  have huU : u ∈ U := by
    by_contra huU
    exact (hAniso u huP huU) (h u huU₀)
  have hI_le_U : U₀ ⊓ P ≤ U := by
    intro x hx
    by_contra hxU
    exact (hAniso x hx.2 hxU) (h x hx.1)
  have hI_ne_two : finrank K ↥(U₀ ⊓ P) ≠ 2 := by
    intro h2
    have hI_eq_U : U₀ ⊓ P = U := by
      apply Submodule.eq_of_le_of_finrank_eq hI_le_U
      rw [h2, hUdim]
    have hU₀_le_P : U₀ ≤ P := by
      intro t ht
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      have hyU₀ : y ∈ U₀ := by
        rw [← hI_eq_U] at hy
        exact hy.1
      have hpol : polarBilin R t y = 0 := by
        have hsing := h (t + y) (U₀.add_mem ht hyU₀)
        have hq := QuadraticMap.map_add R t y
        rw [hsing, h t ht, h y hyU₀] at hq
        rw [zero_add, zero_add] at hq
        exact hq.symm
      simpa only [polarBilin_apply_apply, polar_comm] using hpol
    have hI_eq_T : U₀ ⊓ P = U₀ := inf_eq_left.mpr hU₀_le_P
    have hUW_eq : U = U₀ := by rw [← hI_eq_U, hI_eq_T]
    rw [hUW_eq] at hUdim
    omega
  have hI_dim : finrank K ↥(U₀ ⊓ P) = 1 := by
    have hle : finrank K ↥(U₀ ⊓ P) ≤ 2 := by
      calc finrank K ↥(U₀ ⊓ P) ≤ finrank K ↥U := Submodule.finrank_mono hI_le_U
        _ = 2 := hUdim
    have hpos : 0 < finrank K ↥(U₀ ⊓ P) := by
      haveI : Nontrivial ↥(U₀ ⊓ P) := Submodule.nontrivial_iff_ne_bot.mpr hinter_ne
      exact Module.finrank_pos
    omega
  have hsup_top : U₀ ⊔ P = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hWdim]
    have hsum : finrank K ↥(U₀ ⊔ P) + finrank K ↥(U₀ ⊓ P) = 7 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq U₀ P
      rw [hdim, hPdim] at h
      omega
    omega
  have hu_zero : u = 0 := by
    apply hB.2 u
    intro v
    have hv : v ∈ U₀ ⊔ P := by rw [hsup_top]; exact Submodule.mem_top
    obtain ⟨t, ht, w, hw, htw⟩ := Submodule.mem_sup.mp hv
    rw [← htw]
    have htu : polarBilin R t u = 0 := by
      have hsing := h (t + u) (U₀.add_mem ht huU₀)
      have hq := QuadraticMap.map_add R t u
      rw [hsing, h t ht, h u huU₀] at hq
      rw [zero_add, zero_add] at hq
      exact hq.symm
    have hwu : polarBilin R w u = 0 := by
      have huw : polarBilin R u w = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) u huU
      simpa only [polarBilin_apply_apply, polar_comm] using huw
    rw [map_add, LinearMap.add_apply, htu, hwu, add_zero]
  exact hu0 hu_zero

theorem six_noTS {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    ∀ U₀ : Submodule K (sixW (Q := Q) T), finrank K U₀ = 3 →
      ∃ u ∈ U₀, sixQW (Q := Q) T u ≠ 0 :=
  noTS_of_totally_singular_plane (sixQW (Q := Q) T) (six_nondegenerate T hσ)
    (six_finrank hK hK' T hσ) (sixUW (Q := Q) T hσ) (six_U_finrank hK hK' T hσ)
    (fun x hx hxnot => six_U_perp_aniso T hσ (by simpa [sixBW] using hx) hxnot)

theorem omegaGroup_le_orthDerived_of_six_extract {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (polarBilin R).Nondegenerate) (hdim : finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = 3 → ∃ u ∈ U, R u ≠ 0) :
    omegaGroup R hR ≤ orthDerived R := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction R hR hdim hts
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hNΩ : orthDerived R ≤ omegaGroup R hR :=
    CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR
  have hΩO : omegaGroup R hR ≤ TauCeti.QuadraticMap.orthogonalGroup R := omegaGroup_le R hR
  have hmul := Subgroup.relIndex_mul_relIndex (orthDerived R) (omegaGroup R hR)
    (TauCeti.QuadraticMap.orthogonalGroup R) hNΩ hΩO
  rw [relIndex_omegaGroup R hR] at hmul
  have hNO : (orthDerived R).relIndex (TauCeti.QuadraticMap.orthogonalGroup R) = 2 := by
    rw [Subgroup.relIndex]
    have h : orthDerived R = ρ.range := hcomm
    rw [h]
    exact hidx
  have hne : (orthDerived R).relIndex (omegaGroup R hR) ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem finrank_commSpace_conj_trans {M N : Type} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (e : M ≃ₗ[K] N) (t : M ≃ₗ[K] M) :
    finrank K (commSpace (e.symm.trans (t.trans e))) = finrank K (commSpace t) := by
  have hmap : (commSpace (e.symm.trans (t.trans e))).map (e.symm : N →ₗ[K] M) = commSpace t := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, hv⟩ := mem_commSpace.mp hx
      refine mem_commSpace.mpr ⟨e.symm v, ?_⟩
      rw [← hv]
      simp only [LinearEquiv.trans_apply, map_sub]
      have hsymm : e.symm (e (t (e.symm v))) = t (e.symm v) :=
        LinearEquiv.symm_apply_apply e _
      change t (e.symm v) - e.symm v = e.symm (e (t (e.symm v))) - e.symm v
      rw [hsymm]
    · intro hy
      obtain ⟨v, hv⟩ := mem_commSpace.mp hy
      refine ⟨e y, ?_, ?_⟩
      · refine mem_commSpace.mpr ⟨e v, ?_⟩
        simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_sub]
        rw [← map_sub, hv]
      · exact LinearEquiv.symm_apply_apply e y
  rw [← hmap]
  exact (LinearEquiv.finrank_map_eq e.symm (commSpace (e.symm.trans (t.trans e)))).symm

noncomputable def suEquiv (g : SUid σ 3) : (Fin 3 → K') ≃ₗ[K] (Fin 3 → K') where
  toFun := suEnd (K := K) g
  invFun := suEnd (K := K) g⁻¹
  left_inv v := by
    have h : suEnd (K := K) g⁻¹ * suEnd (K := K) g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    simpa only [Module.End.mul_apply, Module.End.one_apply] using congrArg (fun f : Module.End K (Fin 3 → K') => f v) h
  right_inv v := by
    have h : suEnd (K := K) g * suEnd (K := K) g⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    simpa only [Module.End.mul_apply, Module.End.one_apply] using congrArg (fun f : Module.End K (Fin 3 → K') => f v) h
  map_add' := map_add (suEnd (K := K) g)
  map_smul' := map_smul (suEnd (K := K) g)

@[simp] theorem suEquiv_apply (g : SUid σ 3) (v : Fin 3 → K') :
    suEquiv (K := K) g v = g • v := suEnd_apply g v

theorem suEnd_smul_K' (g : SUid σ 3) (c : K') (v : Fin 3 → K') :
    g • (c • v) = c • (g • v) := by
  exact smul_comm g c v

noncomputable def suEndK' (g : SUid σ 3) : (Fin 3 → K') →ₗ[K'] (Fin 3 → K') where
  toFun v := g • v
  map_add' v w := smul_add g v w
  map_smul' c v := by
    simpa only [RingHom.id_apply] using suEnd_smul_K' g c v

theorem suEndK'_restrictScalars (g : SUid σ 3) :
    (suEndK' g).restrictScalars K = suEnd (K := K) g := by
  ext v
  rfl

theorem even_commSpace_suEquiv {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (g : SUid σ 3) :
    Even (finrank K (commSpace (suEquiv (K := K) g))) := by
  let N : Submodule K' (Fin 3 → K') := LinearMap.range (suEndK' g - 1)
  have hN : N.restrictScalars K = LinearMap.range (suEnd (K := K) g - 1) := by
    change (LinearMap.range (suEndK' g - 1)).restrictScalars K = _
    rw [← suEndK'_restrictScalars g]
    rfl
  have hcomm : commSpace (suEquiv (K := K) g) = LinearMap.range (suEnd (K := K) g - 1) := rfl
  rw [hcomm, ← hN]
  change Even (finrank K ↥N)
  rw [← Module.finrank_mul_finrank K K' N, six_finrank_K' hK hK']
  rw [two_mul]
  exact ⟨finrank K' N, rfl⟩

@[simp] theorem toEmbedding_incl (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    (T.toEmbedding hσ).incl = T.incl := rfl

noncomputable def thetaRestrict (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) : sixW (Q := Q) T ≃ₗ[K] sixW (Q := Q) T where
  toFun w := ⟨(T.toEmbedding hσ).theta g w, by
    obtain ⟨z, hz⟩ := w.2
    refine ⟨g • z, ?_⟩
    rw [← hz]
    simpa [toEmbedding_incl] using (UnitaryEmbedding.theta_incl (D := T.toEmbedding hσ) g z).symm⟩
  invFun w := ⟨((T.toEmbedding hσ).theta g)⁻¹ w, by
    obtain ⟨z, hz⟩ := w.2
    refine ⟨g⁻¹ • z, ?_⟩
    rw [show ((T.toEmbedding hσ).theta g)⁻¹ = (T.toEmbedding hσ).theta g⁻¹ by simp,
      ← hz]
    simpa [toEmbedding_incl] using (UnitaryEmbedding.theta_incl (D := T.toEmbedding hσ) g⁻¹ z).symm⟩
  left_inv w := by ext; simp
  right_inv w := by ext; simp
  map_add' w₁ w₂ := by ext; simp
  map_smul' c w := by ext; simp

@[simp] theorem thetaRestrict_apply (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) (w : sixW (Q := Q) T) :
    ((thetaRestrict (Q := Q) T hσ g w : sixW (Q := Q) T) : V) =
      (T.toEmbedding hσ).theta g w := by simp [thetaRestrict]

theorem thetaRestrict_eq_conj (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) :
    thetaRestrict (Q := Q) T hσ g =
      (sixEW (Q := Q) T hσ).symm.trans
        ((suEquiv (K := K) g).trans (sixEW (Q := Q) T hσ)) := by
  ext w
  obtain ⟨z, rfl⟩ := (sixEW (Q := Q) T hσ).surjective w
  simp only [thetaRestrict_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    suEquiv_apply, sixEW_apply]
  exact UnitaryEmbedding.theta_incl (D := T.toEmbedding hσ) g z

theorem thetaRestrict_mem_orthogonalGroup (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) :
    thetaRestrict (Q := Q) T hσ g ∈
      TauCeti.QuadraticMap.orthogonalGroup (sixQW (Q := Q) T) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (UnitaryEmbedding.theta_mem_orthogonalGroup (D := T.toEmbedding hσ) g)) w
  simpa [sixQW, thetaRestrict_apply] using h

theorem even_commSpace_thetaRestrict {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) :
    Even (finrank K (commSpace (thetaRestrict (Q := Q) T hσ g))) := by
  rw [thetaRestrict_eq_conj, finrank_commSpace_conj_trans]
  exact even_commSpace_suEquiv hK hK' g

theorem thetaRestrict_mem_omega {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) :
    thetaRestrict (Q := Q) T hσ g ∈ omegaGroup (sixQW (Q := Q) T) (six_nondegenerate T hσ) := by
  rw [mem_omegaGroup]
  exact ⟨thetaRestrict_mem_orthogonalGroup T hσ g, even_commSpace_thetaRestrict hK hK' T hσ g⟩

theorem thetaRestrict_mem_orthDerived {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) :
    thetaRestrict (Q := Q) T hσ g ∈ orthDerived (sixQW (Q := Q) T) :=
  omegaGroup_le_orthDerived_of_six_extract (sixQW (Q := Q) T) (six_nondegenerate T hσ)
    (six_finrank hK hK' T hσ) (six_noTS hK hK' T hσ)
    (thetaRestrict_mem_omega hK hK' T hσ g)

noncomputable abbrev sixPerp (T : NormTriple Q σ) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) (sixW (Q := Q) T)

noncomputable def sixProd (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    (sixW (Q := Q) T × sixPerp (Q := Q) T) ≃ₗ[K] V :=
  Submodule.prodEquivOfIsCompl (sixW (Q := Q) T) (sixPerp (Q := Q) T) (T.isCompl hσ)

noncomputable def extendHom (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ) :
    (sixW (Q := Q) T ≃ₗ[K] sixW (Q := Q) T) →* (V ≃ₗ[K] V) where
  toFun a :=
    (sixProd T hσ).symm.trans
      ((a.prodCongr (LinearEquiv.refl K (sixPerp (Q := Q) T))).trans (sixProd T hσ))
  map_one' := by
    ext v
    obtain ⟨⟨w, w'⟩, rfl⟩ := (sixProd T hσ).surjective v
    simp [sixProd, LinearEquiv.prodCongr_apply]
  map_mul' a b := by
    ext v
    obtain ⟨⟨w, w'⟩, rfl⟩ := (sixProd T hσ).surjective v
    simp [sixProd, LinearEquiv.prodCongr_apply, add_assoc]

theorem extendHom_apply (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (a : sixW (Q := Q) T ≃ₗ[K] sixW (Q := Q) T) (w : sixW (Q := Q) T)
    (w' : sixPerp (Q := Q) T) :
    extendHom T hσ a (sixProd T hσ (w, w')) =
      sixProd T hσ (a w, w') := by
  simp [extendHom, sixProd, LinearEquiv.prodCongr_apply]

theorem extendHom_mem_orthogonalGroup (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    {a : sixW (Q := Q) T ≃ₗ[K] sixW (Q := Q) T}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup (sixQW (Q := Q) T)) :
    extendHom T hσ a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨⟨w, w'⟩, rfl⟩ := (sixProd T hσ).surjective v
  have hperp : polar Q (w : V) (w' : V) = 0 := by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp w'.2) w w.2
    simpa [sixPerp, polarBilin_apply_apply] using this
  have hperp' : polar Q ((a w : sixW (Q := Q) T) : V) (w' : V) = 0 := by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp w'.2) (a w) (a w).2
    simpa [sixPerp, polarBilin_apply_apply] using this
  have haQ : Q ((a w : sixW (Q := Q) T) : V) = Q (w : V) :=
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp ha) w
  rw [extendHom_apply]
  change Q (((a w : sixW (Q := Q) T) : V) + (w' : V)) =
    Q ((w : V) + (w' : V))
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, hperp, hperp', haQ]

theorem extendHom_thetaRestrict (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) :
    extendHom T hσ (thetaRestrict (Q := Q) T hσ g) = (T.toEmbedding hσ).theta g := by
  have hcompl : IsCompl (sixW (Q := Q) T) (sixPerp (Q := Q) T) := by
    simpa [sixW, sixPerp] using T.isCompl hσ
  ext v
  obtain ⟨⟨w, w'⟩, rfl⟩ := (sixProd T hσ).surjective v
  have hfix : ∀ w' : sixPerp (Q := Q) T,
      (T.toEmbedding hσ).theta g (w' : V) = w' := by
    intro w'
    rw [UnitaryEmbedding.theta_apply]
    have hcoords : (T.toEmbedding hσ).coords (w' : V) = 0 := by
      change (LinearEquiv.ofInjective T.incl (T.incl_injective hσ)).symm
        ((sixW (Q := Q) T).projectionOnto (sixPerp (Q := Q) T) hcompl (w' : V)) = 0
      rw [Submodule.projectionOnto_apply_of_mem_right hcompl w'.2]
      exact map_zero _
    rw [hcoords]
    simp
  rw [extendHom_apply]
  have hP : ∀ (x : sixW (Q := Q) T) (y : sixPerp (Q := Q) T),
      (sixProd T hσ (x, y) : V) = (x : V) + (y : V) := fun x y => rfl
  rw [hP, hP]
  rw [map_add, hfix w']
  rw [thetaRestrict_apply]

theorem extendHom_mem_orthDerived (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    {a : sixW (Q := Q) T ≃ₗ[K] sixW (Q := Q) T}
    (ha : a ∈ orthDerived (sixQW (Q := Q) T)) :
    extendHom T hσ a ∈ orthDerived Q := by
  let OW := TauCeti.QuadraticMap.orthogonalGroup (sixQW (Q := Q) T)
  let OV := TauCeti.QuadraticMap.orthogonalGroup Q
  have hmap : OW.map (extendHom T hσ) ≤ OV := by
    rintro _ ⟨b, hb, rfl⟩
    exact extendHom_mem_orthogonalGroup T hσ hb
  have hcomm : ⁅OW, OW⁆ ≤ (⁅OV, OV⁆).comap (extendHom T hσ) := by
    rw [← Subgroup.map_le_iff_le_comap]
    calc
      (⁅OW, OW⁆).map (extendHom T hσ) =
          ⁅OW.map (extendHom T hσ), OW.map (extendHom T hσ)⁆ :=
        Subgroup.map_commutator OW OW (extendHom T hσ)
      _ ≤ ⁅OV, OV⁆ := Subgroup.commutator_mono hmap hmap
  exact hcomm ha

theorem theta_mem_orthDerived {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (T : NormTriple Q σ) (hσ : IsUnitaryInvolution σ)
    (g : SUid σ 3) :
    (T.toEmbedding hσ).theta g ∈ orthDerived Q := by
  rw [← extendHom_thetaRestrict T hσ g]
  exact extendHom_mem_orthDerived T hσ (thetaRestrict_mem_orthDerived hK hK' T hσ g)

end SixDickson

end OrthTorus

end CFSG.StandardType

end
