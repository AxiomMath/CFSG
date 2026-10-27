module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec717KleinRel
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.RankThree.GF2n.Stroth80.Sec717LayersRoot
public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import CFSG.RankThree.GF2n.Stroth80.SL4AutTransport
public import CFSG.RankThree.GF2n.Stroth80.Sec717OrbitOddProof
public import CFSG.RankThree.GF2n.Stroth80.Sec717QLayersW1
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.RankThree.GF2n.Stroth80.Sec79MinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSixSimple
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem exists_ringEquiv_of_transport {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K']
    {E X H : Type*} [AddCommGroup E] [Module K E] [Group X] [Group H]
    (hKK : Nat.card K = Nat.card K') (ρ : H →* GL (Fin 3 ⊕ Fin 3) K')
    (hρ : ρ.range = StatedOmega (StatedQuadPlus 3 K')) (φ : X →* (E ≃ₗ[K] E)) (π : H →* X)
    (T : Submodule K E) (e : (Fin 3 ⊕ Fin 3 → K') ≃+ ↥T)
    (he : ∀ h u, (e ((ρ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) : E) =
      φ (π h) (e u)) :
    ∃ σ : K ≃+* K', ∀ (c : K) (u : Fin 3 ⊕ Fin 3 → K'), c • e u = e (σ c • u) := by
  classical
  have hsc : ∀ c : K, ∃ κ : K', ∀ u, c • e u = e (κ • u) := by
    intro c
    let f : (Fin 3 ⊕ Fin 3 → K') →+ (Fin 3 ⊕ Fin 3 → K') :=
      (e.symm.toAddMonoidHom.comp (AddMonoidHom.mk' (fun w : ↥T => c • w) (smul_add c))).comp
        e.toAddMonoidHom
    have hf : ∀ A ∈ StatedOmega (StatedQuadPlus 3 K'), ∀ u,
        f ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) =
          (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ f u := by
      intro A hA u
      obtain ⟨h, rfl⟩ : A ∈ ρ.range := by rw [hρ]; exact hA
      apply e.injective
      apply Subtype.ext
      have e1 : (e (f ((ρ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u)) : E) =
          c • (e ((ρ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) : E) := by
        simp [f]
      have e2 : (e ((ρ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ f u) : E) =
          φ (π h) (e (f u)) := he h (f u)
      have e3 : (e (f u) : E) = c • (e u : E) := by simp [f]
      rw [e1, e2, e3, he, map_smul]
    obtain ⟨κ, hκ⟩ := addCommutantScalar_statedOmegaPlus (m := 3) (K := K') le_rfl f hf
    refine ⟨κ, fun u => ?_⟩
    have h1 := congrArg e (hκ u)
    simpa [f] using h1
  choose σ hσ using hsc
  have hne : ∃ u : Fin 3 ⊕ Fin 3 → K', u ≠ 0 := ⟨Pi.single (Sum.inl 0) 1, by simp⟩
  obtain ⟨u₀, hu₀⟩ := hne
  have hinj : ∀ κ κ' : K', (∀ u, e (κ • u) = e (κ' • u)) → κ = κ' := by
    intro κ κ' h
    have h1 := e.injective (h u₀)
    exact smul_left_injective K' hu₀ h1
  have hσ1 : σ 1 = 1 := hinj _ _ fun u => by rw [← hσ, one_smul, one_smul]
  have hσmul : ∀ c d, σ (c * d) = σ c * σ d := fun c d => hinj _ _ fun u => by
    rw [← hσ, mul_smul, hσ, hσ, ← mul_smul]
  have hσadd : ∀ c d, σ (c + d) = σ c + σ d := fun c d => hinj _ _ fun u => by
    rw [← hσ, add_smul, hσ, hσ, ← map_add, ← add_smul]
  let σr : K →+* K' :=
    { toFun := σ
      map_one' := hσ1
      map_mul' := hσmul
      map_zero' := by
        have h := hσadd 0 0
        rw [add_zero] at h
        exact (add_eq_left.mp h.symm)
      map_add' := hσadd }
  have hbij : Function.Bijective σr :=
    σr.injective.bijective_of_nat_card_le hKK.ge
  exact ⟨RingEquiv.ofBijective σr hbij, fun c u => hσ c u⟩

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.sec717_transport_hom (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {K' : Type} [Field K']
    (ρ : ↥(Rt M (LB M Q B) t) →* GL (Fin 3 ⊕ Fin 3) K')
    (hsec : SectionAct K' (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z ρ
      (fun g => (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')))
    {K : Type} [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    ∃ e : (Fin 3 ⊕ Fin 3 → K') ≃+ ↥T, ∀ (x : ↥(Rt M (LB M Q B) t))
      (hx : QuotientGroup.mk' (Q.subgroupOf M) ⟨(x : G), hc.Rt_le_M t x.2⟩ ∈ bar M Q (H0 M Z))
      (u : Fin 3 ⊕ Fin 3 → K'),
      (e ((ρ x : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) : M₀.E) = φ ⟨_, hx⟩ (e u) := by
  classical
  have hVtQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hTset := hc.sec717_T_eq_image hZcard hZc hZV hs hZ0 M₀ φ hφπ T hT
  have hπVt : ∀ v ∈ Vt M (LB M Q B) B Z t, M₀.π v ∈ T := fun v hv => by
    have : M₀.π v ∈ (T : Set M₀.E) := by
      rw [hTset]
      exact ⟨v, hv, rfl⟩
    exact this
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hsec
  let f : ↥(Vt M (LB M Q B) B Z t) →* Multiplicative ↥T :=
    MonoidHom.mk' (fun v => Multiplicative.ofAdd ⟨M₀.π v, hπVt v v.2⟩) fun v w => by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (M₀.π_mul _ (hVtQ v.2) _ (hVtQ w.2))
  have hfZ : Z.subgroupOf (Vt M (LB M Q B) B Z t) ≤ f.ker := fun v hv => by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    exact Subtype.ext ((M₀.π_ker _ (hVtQ v.2)).mpr (Subgroup.mem_subgroupOf.mp hv))
  let Λ := QuotientGroup.lift (Z.subgroupOf (Vt M (LB M Q B) B Z t)) f hfZ
  have hΛ : ∀ v : ↥(Vt M (LB M Q B) B Z t), Λ (QuotientGroup.mk v) = f v := fun v => rfl
  have hΛinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hΛ] at hq
    have h0 : M₀.π v = 0 := congrArg Subtype.val (congrArg Multiplicative.toAdd hq)
    exact (QuotientGroup.eq_one_iff v).mpr
      (Subgroup.mem_subgroupOf.mpr ((M₀.π_ker _ (hVtQ v.2)).mp h0))
  have hΛsurj : Function.Surjective Λ := by
    intro y
    have hy : ((Multiplicative.toAdd y : ↥T) : M₀.E) ∈ (T : Set M₀.E) := (Multiplicative.toAdd y).2
    rw [hTset] at hy
    obtain ⟨v, hv, hvy⟩ := hy
    refine ⟨QuotientGroup.mk ⟨v, hv⟩, ?_⟩
    rw [hΛ]
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hvy
  let E' : Multiplicative (Fin 3 ⊕ Fin 3 → K') ≃* Multiplicative ↥T :=
    ψ.symm.trans (MulEquiv.ofBijective Λ ⟨hΛinj, hΛsurj⟩)
  let e : (Fin 3 ⊕ Fin 3 → K') ≃+ ↥T := AddEquiv.toMultiplicative.symm E'
  have he_rep : ∀ (v : ↥(Vt M (LB M Q B) B Z t)) (u : Fin 3 ⊕ Fin 3 → K'),
      Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = u → (e u : M₀.E) = M₀.π v := by
    intro v u hvu
    have hq : ψ.symm (Multiplicative.ofAdd u) = QuotientGroup.mk v := by
      rw [MulEquiv.symm_apply_eq, ← hvu]
      rfl
    show ((Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd u))) : ↥T) : M₀.E) = M₀.π v
    rw [hq, hΛ]
    rfl
  refine ⟨e, fun x hx u => ?_⟩
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd u))
  have hvu : Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = u := by
    rw [hv, MulEquiv.apply_symm_apply]
    rfl
  have hxv : (x : G) * v * (x : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hnorm x.2) v).mp v.2
  have h1 := hψ x v ⟨_, hxv⟩ rfl
  beta_reduce at h1
  rw [hvu] at h1
  rw [he_rep ⟨_, hxv⟩ _ h1, he_rep v u hvu]
  exact hφπ ⟨(x : G), hc.Rt_le_M t x.2⟩ hx v (hVtQ v.2)

end CFSG.RankThree.GF2n.Stroth80
