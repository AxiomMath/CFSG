module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.RankThree.GF2n.Stroth80
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def s16gSMul (c : K) (v : Multiplicative (ι → K)) : Multiplicative (ι → K) :=
  Multiplicative.ofAdd (c • Multiplicative.toAdd v)

theorem s16g_exists_semilinear [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) {g : MulAut (Multiplicative (ι → K))} (hg : g ∈ s16gNorm Γ) :
    ∃ θ : RingAut K, ∀ (c : K) (v : Multiplicative (ι → K)),
      g (s16gSMul c v) = s16gSMul (θ c) (g v) := by
  let ψ : (ι → K) ≃+ (ι → K) :=
    { toFun := fun v => Multiplicative.toAdd (g (Multiplicative.ofAdd v))
      invFun := fun v => Multiplicative.toAdd (g⁻¹ (Multiplicative.ofAdd v))
      left_inv := fun v => by
        change Multiplicative.toAdd (g⁻¹ (Multiplicative.ofAdd
          (Multiplicative.toAdd (g (Multiplicative.ofAdd v))))) = v
        rw [ofAdd_toAdd, MulAut.inv_apply_self, toAdd_ofAdd]
      right_inv := fun v => by
        change Multiplicative.toAdd (g (Multiplicative.ofAdd
          (Multiplicative.toAdd (g⁻¹ (Multiplicative.ofAdd v))))) = v
        rw [ofAdd_toAdd, MulAut.apply_inv_self, toAdd_ofAdd]
      map_add' := fun v w => by
        change Multiplicative.toAdd (g (Multiplicative.ofAdd (v + w))) =
          Multiplicative.toAdd (g (Multiplicative.ofAdd v)) +
            Multiplicative.toAdd (g (Multiplicative.ofAdd w))
        rw [ofAdd_add, map_mul, toAdd_mul] }
  have hcomm : ∀ (c : K), ∀ B ∈ Γ, ∀ v : ι → K,
      ψ (c • ψ.symm ((B : Matrix ι ι K) *ᵥ v)) =
        (B : Matrix ι ι K) *ᵥ ψ (c • ψ.symm v) := by
    intro c B hB v
    have hconj : ∃ γ ∈ Γ, s16gNatHom ι K γ = g⁻¹ * s16gNatHom ι K B * g := by
      have hginv : g⁻¹ ∈ s16gNorm Γ := inv_mem hg
      rw [s16gNorm, Subgroup.mem_normalizer_iff] at hginv
      have hmem : g⁻¹ * s16gNatHom ι K B * (g⁻¹)⁻¹ ∈ Γ.map (s16gNatHom ι K) :=
        (hginv _).1 (Subgroup.mem_map_of_mem _ hB)
      rw [inv_inv, Subgroup.mem_map] at hmem
      exact hmem
    obtain ⟨γ, -, hγ⟩ := hconj
    have hrel : ∀ u : ι → K, ψ (γ *ᵥ u) = (B : Matrix ι ι K) *ᵥ ψ u := by
      intro u
      have h1 := congrArg (fun F : MulAut (Multiplicative (ι → K)) =>
        F (Multiplicative.ofAdd u)) hγ
      simp only [s16gNatHom_apply, MulAut.mul_apply, toAdd_ofAdd] at h1
      have h2 := congrArg (fun x => Multiplicative.toAdd (g x)) h1
      rw [MulAut.apply_inv_self] at h2
      exact h2
    have hBv : (B : Matrix ι ι K) *ᵥ v = ψ (γ *ᵥ ψ.symm v) := by
      conv_lhs => rw [← ψ.apply_symm_apply v]
      exact (hrel (ψ.symm v)).symm
    rw [hBv, ψ.symm_apply_apply, ← Matrix.mulVec_smul, hrel]
  obtain ⟨θ, hθ⟩ :=
    exists_ringEquiv_of_scalar_commutant (K := K) (K' := K) rfl hΓ ψ hcomm
  refine ⟨θ, fun c v => ?_⟩
  have h := hθ c (Multiplicative.toAdd v)
  change Multiplicative.ofAdd (ψ (c • Multiplicative.toAdd v)) =
    Multiplicative.ofAdd (θ c • Multiplicative.toAdd (g v))
  rw [h]
  rfl

private theorem s16g_theta_unique [Nonempty ι] {g : MulAut (Multiplicative (ι → K))}
    {θ₁ θ₂ : RingAut K}
    (h₁ : ∀ (c : K) (v : Multiplicative (ι → K)),
      g (s16gSMul c v) = s16gSMul (θ₁ c) (g v))
    (h₂ : ∀ (c : K) (v : Multiplicative (ι → K)),
      g (s16gSMul c v) = s16gSMul (θ₂ c) (g v)) : θ₁ = θ₂ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine RingEquiv.ext fun c => ?_
  have h := (h₁ c (g.symm (Multiplicative.ofAdd (Pi.single i (1 : K))))).symm.trans
    (h₂ c (g.symm (Multiplicative.ofAdd (Pi.single i (1 : K)))))
  rw [MulEquiv.apply_symm_apply] at h
  have h2 := congrArg (fun w : Multiplicative (ι → K) => Multiplicative.toAdd w) h
  simp only [s16gSMul, toAdd_ofAdd] at h2
  have h3 := congrFun h2 i
  simpa using h3

theorem s16g_exists_theta [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) :
    ∃ θ : ↥(s16gNorm Γ) →* RingAut K,
      (∀ (g : ↥(s16gNorm Γ)) (c : K) (v : Multiplicative (ι → K)),
        (g : MulAut (Multiplicative (ι → K))) (s16gSMul c v) =
          s16gSMul (θ g c) ((g : MulAut (Multiplicative (ι → K))) v)) ∧
      ∀ g : ↥(s16gNorm Γ), θ g = 1 ↔ (g : MulAut (Multiplicative (ι → K))) ∈ s16gLin ι K := by
  classical
  let θfun : ↥(s16gNorm Γ) → RingAut K :=
    fun g => Classical.choose (s16g_exists_semilinear hΓ g.2)
  have hθfun : ∀ g : ↥(s16gNorm Γ), ∀ (c : K) (v : Multiplicative (ι → K)),
      (g : MulAut (Multiplicative (ι → K))) (s16gSMul c v) =
        s16gSMul (θfun g c) ((g : MulAut (Multiplicative (ι → K))) v) :=
    fun g => Classical.choose_spec (s16g_exists_semilinear hΓ g.2)
  let θ : ↥(s16gNorm Γ) →* RingAut K :=
    { toFun := θfun
      map_one' := s16g_theta_unique (hθfun 1) (fun c v => by
        simp only [Subgroup.coe_one, MulAut.one_apply, RingAut.one_apply])
      map_mul' := fun g h => s16g_theta_unique (hθfun (g * h)) (fun c v => by
        simp only [Subgroup.coe_mul, MulAut.mul_apply, hθfun h, hθfun g, RingAut.mul_apply]) }
  refine ⟨θ, ?_, ?_⟩
  · intro g c v
    exact hθfun g c v
  · intro g
    constructor
    · intro hg
      have hlin : ∀ (c : K) (v : Multiplicative (ι → K)),
          (g : MulAut (Multiplicative (ι → K))) (s16gSMul c v) =
            s16gSMul c ((g : MulAut (Multiplicative (ι → K))) v) := by
        intro c v
        have h := hθfun g c v
        rw [show θfun g = 1 from hg, RingAut.one_apply] at h
        exact h
      have hlin' : ∀ (c : K) (v : Multiplicative (ι → K)),
          (g : MulAut (Multiplicative (ι → K)))⁻¹ (s16gSMul c v) =
            s16gSMul c ((g : MulAut (Multiplicative (ι → K)))⁻¹ v) := by
        intro c v
        have hw := hlin c ((g : MulAut (Multiplicative (ι → K)))⁻¹ v)
        rw [MulAut.apply_inv_self] at hw
        have h2 := congrArg (fun x => (g : MulAut (Multiplicative (ι → K)))⁻¹ x) hw
        rw [MulAut.inv_apply_self] at h2
        exact h2.symm
      let L : (ι → K) →ₗ[K] (ι → K) :=
        { toFun := fun v => Multiplicative.toAdd ((g : MulAut _) (Multiplicative.ofAdd v))
          map_add' := fun v w => by
            change Multiplicative.toAdd ((g : MulAut _) (Multiplicative.ofAdd (v + w))) =
              Multiplicative.toAdd ((g : MulAut _) (Multiplicative.ofAdd v)) +
                Multiplicative.toAdd ((g : MulAut _) (Multiplicative.ofAdd w))
            rw [ofAdd_add, map_mul, toAdd_mul]
          map_smul' := fun c v => by
            change Multiplicative.toAdd ((g : MulAut _)
                (s16gSMul c (Multiplicative.ofAdd v))) =
              c • Multiplicative.toAdd ((g : MulAut _) (Multiplicative.ofAdd v))
            rw [hlin c (Multiplicative.ofAdd v), s16gSMul, toAdd_ofAdd]
        }
      let L' : (ι → K) →ₗ[K] (ι → K) :=
        { toFun := fun v => Multiplicative.toAdd ((g : MulAut _)⁻¹ (Multiplicative.ofAdd v))
          map_add' := fun v w => by
            change Multiplicative.toAdd ((g : MulAut _)⁻¹ (Multiplicative.ofAdd (v + w))) =
              Multiplicative.toAdd ((g : MulAut _)⁻¹ (Multiplicative.ofAdd v)) +
                Multiplicative.toAdd ((g : MulAut _)⁻¹ (Multiplicative.ofAdd w))
            rw [ofAdd_add, map_mul, toAdd_mul]
          map_smul' := fun c v => by
            change Multiplicative.toAdd ((g : MulAut _)⁻¹
                (s16gSMul c (Multiplicative.ofAdd v))) =
              c • Multiplicative.toAdd ((g : MulAut _)⁻¹ (Multiplicative.ofAdd v))
            rw [hlin' c (Multiplicative.ofAdd v), s16gSMul, toAdd_ofAdd]
        }
      have hLL' : LinearMap.toMatrix' L * LinearMap.toMatrix' L' = 1 := by
        rw [← LinearMap.toMatrix'_comp]
        have hcomp : L ∘ₗ L' = LinearMap.id := LinearMap.ext fun v => by
          change Multiplicative.toAdd ((g : MulAut _) (Multiplicative.ofAdd
            (Multiplicative.toAdd ((g : MulAut _)⁻¹ (Multiplicative.ofAdd v))))) = v
          rw [ofAdd_toAdd, MulAut.apply_inv_self, toAdd_ofAdd]
        rw [hcomp, LinearMap.toMatrix'_id]
      have hL'L : LinearMap.toMatrix' L' * LinearMap.toMatrix' L = 1 := by
        rw [← LinearMap.toMatrix'_comp]
        have hcomp : L' ∘ₗ L = LinearMap.id := LinearMap.ext fun v => by
          change Multiplicative.toAdd ((g : MulAut _)⁻¹ (Multiplicative.ofAdd
            (Multiplicative.toAdd ((g : MulAut _) (Multiplicative.ofAdd v))))) = v
          rw [ofAdd_toAdd, MulAut.inv_apply_self, toAdd_ofAdd]
        rw [hcomp, LinearMap.toMatrix'_id]
      refine ⟨⟨LinearMap.toMatrix' L, LinearMap.toMatrix' L', hLL', hL'L⟩, ?_⟩
      refine MulEquiv.ext fun x => ?_
      obtain ⟨v, rfl⟩ : ∃ v : ι → K, Multiplicative.ofAdd v = x :=
        ⟨Multiplicative.toAdd x, ofAdd_toAdd x⟩
      rw [s16gNatHom_apply, toAdd_ofAdd, LinearMap.toMatrix'_mulVec]
      rfl
    · intro hg
      obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp
        (show (g : MulAut (Multiplicative (ι → K))) ∈ (s16gNatHom ι K).range from hg)
      exact s16g_theta_unique (hθfun g) (fun c v => by
        rw [← hh]
        simp only [s16gNatHom_apply, s16gSMul, toAdd_ofAdd, RingAut.one_apply,
          Matrix.mulVec_smul])

theorem s16g_card_ringAut_eight [Finite K] (hK : Nat.card K = 8) : Nat.card (RingAut K) = 3 :=
  (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    (n := 3) (by rw [hK]; norm_num)).1

theorem s16g_le_lin_of_hom_trivial [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) {E : Subgroup (MulAut (Multiplicative (ι → K)))}
    (hEN : E ≤ s16gNorm Γ) (hE : ∀ φ : ↥E →* RingAut K, φ = 1) : E ≤ s16gLin ι K := by
  obtain ⟨θ, -, hker⟩ := s16g_exists_theta hΓ
  intro g hg
  have h1 := congrArg (fun φ : ↥E →* RingAut K => φ ⟨g, hg⟩) (hE (θ.comp (Subgroup.inclusion hEN)))
  exact (hker ⟨g, hEN hg⟩).1 h1

theorem s16g_le_lin_of_coprime [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card (RingAut K))
    {E : Subgroup (MulAut (Multiplicative (ι → K)))} (hEN : E ≤ s16gNorm Γ)
    (hEp : IsPGroup p E) : E ≤ s16gLin ι K := by
  refine s16g_le_lin_of_hom_trivial hΓ hEN fun φ => MonoidHom.ext fun x => ?_
  obtain ⟨k, hk⟩ := hEp x
  have h1 : orderOf (φ x) ∣ p ^ k := (orderOf_map_dvd φ x).trans (orderOf_dvd_of_pow_eq_one hk)
  have h2 : orderOf (φ x) ∣ Nat.card (RingAut K) := orderOf_dvd_natCard _
  have hc : Nat.Coprime (p ^ k) (Nat.card (RingAut K)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
  rw [MonoidHom.one_apply]
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hc h1 h2)

theorem s16g_card_le_of_norm [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) {E : Subgroup (MulAut (Multiplicative (ι → K)))}
    (hEN : E ≤ s16gNorm Γ) :
    Nat.card E ≤ Nat.card (RingAut K) * Nat.card ↥(E ⊓ s16gLin ι K) := by
  obtain ⟨θ, -, hker⟩ := s16g_exists_theta hΓ
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun f : RingAut K => (f : K → K)) DFunLike.coe_injective
  let φ : ↥E →* RingAut K := θ.comp (Subgroup.inclusion hEN)
  have h2 : Nat.card φ.range ≤ Nat.card (RingAut K) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have h3 : Nat.card φ.ker = Nat.card ↥(E ⊓ s16gLin ι K) := Nat.card_congr
    { toFun := fun x => ⟨(x.1 : MulAut (Multiplicative (ι → K))), x.1.2,
        (hker ⟨x.1.1, hEN x.1.2⟩).1 (MonoidHom.mem_ker.1 x.2)⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, MonoidHom.mem_ker.2 ((hker ⟨y.1, hEN y.2.1⟩).2 y.2.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card φ.ker * Nat.card (RingAut K) := Nat.mul_le_mul_left _ h2
    _ = Nat.card (RingAut K) * Nat.card ↥(E ⊓ s16gLin ι K) := by rw [h3, mul_comm]

theorem s16g_exists_matrix_subgroup {Γ : Subgroup (GL ι K)}
    {E : Subgroup (MulAut (Multiplicative (ι → K)))} (hEN : E ≤ s16gNorm Γ)
    (hEL : E ≤ s16gLin ι K) :
    ∃ F : Subgroup (GL ι K), F ≤ Subgroup.normalizer (Γ : Set (GL ι K)) ∧
      F.map (s16gNatHom ι K) = E := by
  refine ⟨E.comap (s16gNatHom ι K), fun g hg => ?_, ?_⟩
  · exact (s16g_mem_norm_natHom_iff Γ g).1 (hEN hg)
  · rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hEL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
