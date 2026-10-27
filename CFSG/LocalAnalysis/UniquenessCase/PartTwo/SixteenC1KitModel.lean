module

public import CFSG.LargeExtraspecial.O62Model
public import CFSG.LargeExtraspecial.O62Transport
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62
open Matrix
open QuadraticMap CFSG.RankThree.OrthogonalInvolutions

@[expose] def IsOmegaModel {W : Type} [CommGroup W] (H : Subgroup (MulAut W))
    (β : W ≃* Multiplicative V₀) : Prop :=
  ∀ φ : MulAut W, φ ∈ H ↔ ∃ g ∈ Ω₀ true, ∀ x : W,
    β (φ x) = Multiplicative.ofAdd (g (Multiplicative.toAdd (β x)))

theorem s16c1_natOmegaMinus_unpack {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (h : NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K), Nat.card K = 2 ∧
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ β : W ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
        ∀ φ : MulAut W, φ ∈ H ↔
          ∃ γ ∈ StatedOmega (StatedQuadMinus 3 K b c), ∀ x : W,
            β (φ x) = Multiplicative.ofAdd
              (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K γ
                (Multiplicative.toAdd (β x))) := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := h
  letI := hK
  haveI : Finite K := hKf
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) :=
      (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let β' : W ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    (Subgroup.topEquiv (G := W)).symm.trans (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
  have hβ' : ∀ y : W, β' y = β ⟨y, Subgroup.mem_top y⟩ := fun _ => rfl
  have hnat : ∀ (γ : ↥(StatedOmega (StatedQuadMinus (6 / 2) K b c))) (x : W),
      β' (((π γ : ↥H) : MulAut W) x) =
        Multiplicative.ofAdd
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K (γ : GL _ K)
            (Multiplicative.toAdd (β' x))) := by
    intro γ x
    have hx := hβe γ ⟨x, Subgroup.mem_top x⟩ (Subgroup.mem_top _)
    simp only [hβ', Subtype.coe_mk] at hx ⊢
    refine hx.trans ?_
    rw [CFSG.Quasithin.natAct, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  refine ⟨K, hK, hKf, b, c, hK2, hpoly, β', ?_⟩
  intro φ
  constructor
  · intro hφ
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨φ, hφ⟩
    let γs : ↥(StatedOmega (StatedQuadMinus (6 / 2) K b c)) := γ
    refine ⟨(γs : GL _ K), γs.2, fun x => ?_⟩
    have hφγ : ((π γs : ↥H) : MulAut W) = φ := by rw [hγ]
    rw [← hφγ]
    exact hnat γs x
  · rintro ⟨γ, hγ, hx⟩
    let γ' : ↥(StatedOmega (StatedQuadMinus (6 / 2) K b c)) := ⟨γ, hγ⟩
    have hsame : ∀ x : W, φ x = ((π γ' : ↥H) : MulAut W) x := by
      intro x
      apply β'.injective
      rw [hx x, hnat γ' x]
    have hφeq : φ = ((π γ' : ↥H) : MulAut W) := MulEquiv.ext hsame
    rw [hφeq]
    exact (π γ').2

private theorem s16c1_minusQuadCore_map {K : Type} [Field K] (e : ZMod 2 ≃+* K) (b c : K)
    (hb : e.symm b = 1) (hc : e.symm c = 1) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K) :
    CFSG.MatrixModel.minusQuadCore 2 (ZMod 2) 1 1 (fun i => e.symm (v i)) =
      e.symm (CFSG.MatrixModel.minusQuadCore 2 K b c v) := by
  simp only [CFSG.MatrixModel.minusQuadCore, map_add, map_mul, map_pow, map_sum, map_one, hb,
    hc, Fin.sum_univ_two]

theorem s16c1_statedOmega_minus_zmod2 {K : Type} [Field K] [Finite K] {b c : K}
    (hK : Nat.card K = 2) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (θ : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2))
      (ψ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K ≃*
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)),
      (∀ (γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
          (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
        θ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K γ v) =
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (ZMod 2) (ψ γ) (θ v)) ∧
      ∀ γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K,
        γ ∈ StatedOmega (StatedQuadMinus 3 K b c) ↔
          ψ γ ∈ StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hK'
  let θ : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃+
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) :=
    AddEquiv.piCongrRight (fun _ => (e.symm : K ≃+ ZMod 2))
  let ψ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K ≃*
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2) :=
    Units.mapEquiv (RingEquiv.mapMatrix e.symm).toMulEquiv
  have hθ : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
      θ v = fun i => e.symm (v i) := fun _ => rfl
  have hψ : ∀ A : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K,
      ((ψ A : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (ZMod 2)) =
        (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          K).map e.symm := fun _ => rfl
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + e.symm b * t + e.symm c ≠ 0 := by
    intro t h0
    apply hpoly (e t)
    have h1 : e.symm ((e t) ^ 2 + b * e t + c) = 0 := by
      rw [map_add, map_add, map_mul, map_pow]
      simpa using h0
    have h2 : (e t) ^ 2 + b * e t + c = 0 := by
      have := congrArg e h1
      rwa [e.apply_symm_apply, map_zero] at this
    exact h2
  have hc1 : e.symm c = 1 := by
    rcases zmod2_eq_zero_or_eq_one (e.symm c) with h | h
    · exfalso
      have hzero : (0 : ZMod 2) ^ 2 + e.symm b * 0 + e.symm c = 0 := by
        rw [h]; simp
      exact hpoly' 0 hzero
    · exact h
  have hb1 : e.symm b = 1 := by
    rcases zmod2_eq_zero_or_eq_one (e.symm b) with h | h
    · exfalso
      have hzero : (1 : ZMod 2) ^ 2 + e.symm b * 1 + e.symm c = 0 := by
        rw [h, hc1]; decide
      exact hpoly' 1 hzero
    · exact h
  have hbc : e.symm b = 1 ∧ e.symm c = 1 := ⟨hb1, hc1⟩
  have hQrel : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
      StatedQuadMinus 3 (ZMod 2) 1 1 (θ v) = e.symm (StatedQuadMinus 3 K b c v) := by
    intro v
    rw [hθ]
    exact s16c1_minusQuadCore_map e b c hbc.1 hbc.2 v
  have hconj : ∀ (A : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
      (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
      θ ((A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v) =
        ((ψ A : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ θ v := by
    intro A v
    funext i
    rw [hθ, hψ, hθ]
    exact RingHom.map_mulVec (e.symm : K →+* ZMod 2) (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) v i
  have hset : ∀ A : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K,
      (∀ v, StatedQuadMinus 3 K b c
          ((A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v) =
        StatedQuadMinus 3 K b c v) ↔
      (∀ w, StatedQuadMinus 3 (ZMod 2) 1 1
          (((ψ A : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ w) =
        StatedQuadMinus 3 (ZMod 2) 1 1 w) := by
    intro A
    constructor
    · intro hA w
      obtain ⟨v, rfl⟩ := θ.surjective w
      calc StatedQuadMinus 3 (ZMod 2) 1 1
              (((ψ A : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
                Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                  (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ θ v)
          = StatedQuadMinus 3 (ZMod 2) 1 1
              (θ ((A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v)) := by rw [hconj]
        _ = e.symm (StatedQuadMinus 3 K b c ((A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v)) := hQrel _
        _ = e.symm (StatedQuadMinus 3 K b c v) := by rw [hA]
        _ = StatedQuadMinus 3 (ZMod 2) 1 1 (θ v) := (hQrel v).symm
    · intro hA v
      apply e.symm.injective
      rw [← hQrel ((A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v), ← hQrel v, hconj]
      exact hA (θ v)
  have hcore : CFSG.MatrixModel.isometryCore (StatedQuadMinus 3 (ZMod 2) 1 1) =
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus 3 K b c)).map ψ.toMonoidHom := by
    apply le_antisymm
    · rw [CFSG.MatrixModel.isometryCore, Subgroup.closure_le]
      intro B hB
      refine Subgroup.mem_map.2 ⟨ψ.symm B, ?_, by simp⟩
      rw [CFSG.MatrixModel.isometryCore]
      exact Subgroup.subset_closure ((hset (ψ.symm B)).2 (by simpa using hB))
    · rw [CFSG.MatrixModel.isometryCore, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      intro A hA
      change ψ A ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 3 (ZMod 2) 1 1)
      rw [CFSG.MatrixModel.isometryCore]
      exact Subgroup.subset_closure ((hset A).1 hA)
  refine ⟨θ, ψ, hconj, ?_⟩

  · intro γ
    have hOmega : StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1) =
        (StatedOmega (StatedQuadMinus 3 K b c)).map ψ.toMonoidHom := by
      change ⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus 3 (ZMod 2) 1 1),
          CFSG.MatrixModel.isometryCore (StatedQuadMinus 3 (ZMod 2) 1 1)⁆ =
        (⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus 3 K b c),
          CFSG.MatrixModel.isometryCore (StatedQuadMinus 3 K b c)⁆).map ψ.toMonoidHom
      rw [hcore, Subgroup.map_commutator]
    rw [hOmega, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem s16c1_statedOmega_zmod2_model :
    ∃ (θ : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) ≃+ V₀)
      (ψ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2) ≃* (V₀ ≃ₗ[ZMod 2] V₀)),
      (∀ (γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2))
          (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2),
        θ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (ZMod 2) γ v) = ψ γ (θ v)) ∧
      ∀ g : V₀ ≃ₗ[ZMod 2] V₀, g ∈ Ω₀ true ↔
        ∃ γ ∈ StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1), ψ γ = g := by
  classical
  let s : Fin 6 → (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) :=
    ![Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inl 1, Sum.inr (Sum.inl 1), Sum.inr (Sum.inr 0),
      Sum.inr (Sum.inr 1)]
  let r : Fin 6 ≃ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) := Equiv.ofBijective s (by decide)
  let L : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] V₀ :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) r
  let Q : QuadraticForm (ZMod 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) :=
    CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1
  have hQ : (polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (K := ZMod 2)
      (n := 3) (b := 1) (c := 1) (by decide)
  have hQ' : (qModel true).polarBilin.Nondegenerate := qModel_nondegenerate true
  have h6 : 6 ≤ Module.finrank (ZMod 2)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  have hL : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2, qMinus (L v) =
      CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1 v := by
    have hr0 : r 0 = Sum.inl 0 := by decide
    have hr1 : r 1 = Sum.inr (Sum.inl 0) := by decide
    have hr2 : r 2 = Sum.inl 1 := by decide
    have hr3 : r 3 = Sum.inr (Sum.inl 1) := by decide
    have hr4 : r 4 = Sum.inr (Sum.inr 0) := by decide
    have hr5 : r 5 = Sum.inr (Sum.inr 1) := by decide
    intro v
    have hv : ∀ j : Fin 6, (L v) j = v (r j) := fun j => by
      simp only [L, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    rw [qMinus_apply, CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp only [hv, hr0, hr1, hr2, hr3, hr4, hr5, Fin.sum_univ_two, Nat.reduceSub]
    ring
  have hLq : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2, qModel true (L v) = Q v := by
    intro v
    rw [qModel_true]
    exact hL v
  let θ : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) ≃+ V₀ := L.toAddEquiv
  let ψ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2) ≃* (V₀ ≃ₗ[ZMod 2] V₀) :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
      (ZMod 2)).trans (conjL L)
  refine ⟨θ, ψ, ?_, ?_⟩
  · intro γ v
    have h : ψ γ = conjL L (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2) γ) := rfl
    rw [h, conjL_apply]
    change L ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (ZMod 2) γ) v) =
      L ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (ZMod 2) γ) (L.symm (L v)))
    rw [LinearEquiv.symm_apply_apply]
  · intro g
    have hΩ : StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1) =
        (omegaGroup Q hQ).comap (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)).toMonoidHom := by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
          (CFSG.LieType.Universal.Spin.coe_quadMinus 3 (ZMod 2) 1 1),
        CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6]
    constructor
    · intro hg
      let d : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) := (conjL L).symm g
      have hd : d ∈ omegaGroup Q hQ :=
        (mem_omegaGroup_conjL (L := L) hQ hQ' hLq).1 (by
          show conjL L d ∈ omegaGroup (qModel true) hQ'
          rw [show conjL L d = g from MulEquiv.apply_symm_apply (conjL L) g]
          exact hg)
      refine ⟨(CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (ZMod 2)).symm d, ?_, ?_⟩
      · rw [hΩ, Subgroup.mem_comap]
        simpa using hd
      · show ψ ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (ZMod 2)).symm d) = g
        simp only [ψ, MulEquiv.trans_apply]
        rw [MulEquiv.apply_symm_apply]
        exact MulEquiv.apply_symm_apply (conjL L) g
    · rintro ⟨γ, hγ, rfl⟩
      rw [hΩ, Subgroup.mem_comap] at hγ
      have hconj := (mem_omegaGroup_conjL (L := L) hQ hQ' hLq).2 hγ
      change (conjL L (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2) γ)) ∈ omegaGroup (qModel true) hQ'
      exact hconj

theorem s16c1_statedOmega_minus_model {K : Type} [Field K] [Finite K] {b c : K}
    (hK : Nat.card K = 2) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (θ : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃+ V₀)
      (ψ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K ≃* (V₀ ≃ₗ[ZMod 2] V₀)),
      (∀ (γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
          (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
        θ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K γ v) =
          ψ γ (θ v)) ∧
      ∀ g : V₀ ≃ₗ[ZMod 2] V₀, g ∈ Ω₀ true ↔
        ∃ γ ∈ StatedOmega (StatedQuadMinus 3 K b c), ψ γ = g := by
  obtain ⟨θ₁, ψ₁, h1θ, h1Ω⟩ := s16c1_statedOmega_minus_zmod2 hK hpoly
  obtain ⟨θ₂, ψ₂, h2θ, h2Ω⟩ := s16c1_statedOmega_zmod2_model
  refine ⟨θ₁.trans θ₂, ψ₁.trans ψ₂, fun γ v => ?_, fun g => ?_⟩
  · show θ₂ (θ₁ _) = ψ₂ (ψ₁ γ) (θ₂ (θ₁ v))
    rw [h1θ, h2θ]
  · rw [h2Ω g]
    constructor
    · rintro ⟨γ', hγ', rfl⟩
      exact ⟨ψ₁.symm γ', (h1Ω _).2 (by simpa using hγ'), by simp⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨ψ₁ γ, (h1Ω γ).1 hγ, rfl⟩

theorem natOmegaMinus_exists_model {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    (h : NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1) :
    ∃ β : W ≃* Multiplicative V₀, IsOmegaModel H β := by
  obtain ⟨K, hK, hKf, b, c, hK2, hpoly, β, hβ⟩ := s16c1_natOmegaMinus_unpack h
  letI := hK
  haveI := hKf
  obtain ⟨θ, ψ, hψθ, hψΩ⟩ := s16c1_statedOmega_minus_model hK2 hpoly
  refine ⟨β.trans (AddEquiv.toMultiplicative θ), fun φ => ?_⟩
  rw [hβ φ]
  constructor
  · rintro ⟨γ, hγ, hx⟩
    refine ⟨ψ γ, (hψΩ _).2 ⟨γ, hγ, rfl⟩, fun x => ?_⟩
    show Multiplicative.ofAdd (θ (Multiplicative.toAdd (β (φ x)))) =
      Multiplicative.ofAdd (ψ γ (θ (Multiplicative.toAdd (β x))))
    rw [hx x, toAdd_ofAdd, hψθ]
  · rintro ⟨g, hg, hx⟩
    obtain ⟨γ, hγ, rfl⟩ := (hψΩ g).1 hg
    refine ⟨γ, hγ, fun x => ?_⟩
    have h1 : θ (Multiplicative.toAdd (β (φ x))) = ψ γ (θ (Multiplicative.toAdd (β x))) :=
      congrArg Multiplicative.toAdd (hx x)
    have h2 : Multiplicative.toAdd (β (φ x)) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K γ
          (Multiplicative.toAdd (β x)) :=
      θ.injective (by rw [h1, hψθ])
    exact congrArg Multiplicative.ofAdd h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
