module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Model
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Iso
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Theta
import CFSG.LocalAnalysis.StandardType.GGOrthRk1ModelTwo
import CFSG.Adapters.SpecialLinearPerfect

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] in
private theorem sl2_closure_involutions_eq_top :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 2) K | g ^ 2 = 1} = ⊤ := by
  rw [eq_top_iff]
  rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (K := K) (ι := Fin 2)]
  refine Subgroup.closure_mono ?_
  rintro g ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  change (Matrix.SpecialLinearGroup.transvection hij c) ^ 2 = 1
  have h := Matrix.SpecialLinearGroup.transvection_add (F := K) hij c c
  rw [CharTwo.add_self_eq_zero, Matrix.SpecialLinearGroup.transvection_coeff_zero] at h
  rw [pow_two]
  exact h.symm

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem orthDerived_le_orthogonalGroup (Q : QuadraticForm K V) :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [orthDerived, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
    ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
      ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem h₁ h₂)
      ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem h₁))
    ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem h₂)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem exists_end_of_mapsTo {M : Type*} [AddCommGroup M] [Module K M]
    {φ : M →ₗ[K] V} (hφ : Function.Injective φ) {y : V ≃ₗ[K] V}
    (hy : ∀ v : M, y (φ v) ∈ LinearMap.range φ) :
    ∃ h : M →ₗ[K] M, ∀ v, φ (h v) = y (φ v) := by
  refine ⟨((LinearEquiv.ofInjective φ hφ).symm : LinearMap.range φ →ₗ[K] M) ∘ₗ
    LinearMap.codRestrict (LinearMap.range φ) (y.toLinearMap ∘ₗ φ) hy, ?_⟩
  intro v
  simp

omit [Finite K] in
theorem TBJOmData.rankOne_le_range {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r)
    (φ : (Δ.D × Δ.D) →ₗ[K] V) (hφinj : Function.Injective φ)
    (hφrange : LinearMap.range φ = Δ.F.U i ⊔ Δ.F.U j)
    (hφQ : ∀ v : Δ.D × Δ.D, Q (φ v) = rk1Omega Δ.finrank_D v.1 v.2)
    (hφτ : ∀ f ∈ reflFixedCoord p r i j, ∀ v : Δ.D × Δ.D,
      Δ.τ f (φ v) = φ ((Δ.c ^ (toAdd (f i)).val) v.1, (Δ.c ^ (toAdd (f i)).val) v.2))
    (θ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V))
    (hθuniq : ∀ (y : V ≃ₗ[K] V) (g : Matrix.SpecialLinearGroup (Fin 2) K),
      (∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, y u = u) →
      (∀ v, y (φ v) = φ (rk1ModelAct g v)) → y = θ g) :
    Δ.rankOne i j ≤ θ.range := by
  change CFSG.StandardType.ggOTwoPrime
    (Subgroup.centralizer (Δ.reflFixed i j : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q) ≤ θ.range
  rw [ggOTwoPrime]
  rw [Subgroup.closure_le]
  rintro y ⟨⟨hyC, hyΩ⟩, hym⟩
  obtain ⟨m, hym⟩ := hym
  have hc : Rk1Block Δ.c p := TBJOmData.rk1Block hp2 Δ
  have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup Q hyΩ
  have hmapsto := (TBJOmData.centralizer_mapsTo Δ hfix i j hyC).2
  have hfix2 : ∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, y u = u :=
    fun k hki hkj => TBJOmData.centralizer_two_fix hp2 Δ hfix i j hyC hym k hki hkj
  have hmem : ∀ v : Δ.D × Δ.D, (y.toLinearMap ∘ₗ φ) v ∈ LinearMap.range φ := by
    intro v
    rw [hφrange]
    exact hmapsto (φ v) (by rw [← hφrange]; exact LinearMap.mem_range_self φ v)
  obtain ⟨h, hφh⟩ := exists_end_of_mapsTo hφinj hmem
  let f : Fin r → Multiplicative (ZMod p) := fun _ => Multiplicative.ofAdd (1 : ZMod p)
  have hf0 : f ∈ reflFixedCoord p r i j := by
    rw [reflFixedCoord, MonoidHom.mem_ker, MonoidHom.div_apply]
    exact div_self' _
  have hfval : (toAdd (f i)).val = 1 := by
    change (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = 1
    rw [toAdd_ofAdd, ZMod.val_one'' (Nat.Prime.ne_one Fact.out)]
  have hτeq : ∀ w : Δ.D × Δ.D, Δ.τ f (φ w) = φ (Δ.c w.1, Δ.c w.2) := by
    intro w
    rw [hφτ f hf0 w, hfval, pow_one]
  have hcomm : ∀ v : Δ.D × Δ.D, h (Δ.c v.1, Δ.c v.2) = (Δ.c (h v).1, Δ.c (h v).2) := by
    intro v
    apply hφinj
    rw [hφh (Δ.c v.1, Δ.c v.2), ← hτeq v, ← hτeq (h v), hφh v]
    have hcommτ : Δ.τ f * y = y * Δ.τ f :=
      (Subgroup.mem_centralizer_iff.mp hyC) (Δ.τ f) ⟨f, hf0, rfl⟩
    calc y (Δ.τ f (φ v)) = (y * Δ.τ f) (φ v) := rfl
      _ = (Δ.τ f * y) (φ v) := by rw [hcommτ]
      _ = Δ.τ f (y (φ v)) := rfl
  have hrk : rk1Omega hc.finrank_eq = rk1Omega Δ.finrank_D :=
    congrArg rk1Omega (Subsingleton.elim _ _)
  have hiso : ∀ v : Δ.D × Δ.D,
      rk1Omega hc.finrank_eq (h v).1 (h v).2 = rk1Omega hc.finrank_eq v.1 v.2 := by
    intro v
    rw [hrk]
    rw [← hφQ (h v), hφh v,
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hyO) (φ v), hφQ v]
  have hpow : ∀ n : ℕ, ∀ v : Δ.D × Δ.D, φ ((h ^ n) v) = (y ^ n) (φ v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, LinearEquiv.mul_apply, ih (h v), hφh v]
  have hk : h ^ (2 ^ m) = 1 := by
    apply LinearMap.ext
    intro v
    apply hφinj
    rw [hpow (2 ^ m) v, hym]
    simp
  obtain ⟨g, hg⟩ := Rk1Block.exists_rk1ModelAct hc hcomm hiso hk
  have hφy : ∀ v, y (φ v) = φ (rk1ModelAct g v) := by
    intro v
    rw [← hg v, hφh v]
  have hyθ : y = θ g := hθuniq y g hfix2 hφy
  exact ⟨g, hyθ.symm⟩

theorem TBJOmData.exists_rankOne_model {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r)
    (hq : 4 ≤ Nat.card K) (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r) (hij : i ≠ j) :
    ∃ φ : (Δ.D × Δ.D) →ₗ[K] V, Function.Injective φ ∧
      LinearMap.range φ = Δ.F.U i ⊔ Δ.F.U j ∧
      (∀ v : Δ.D × Δ.D, Q (φ v) = rk1Omega Δ.finrank_D v.1 v.2) ∧
      ∃ θ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V), Function.Injective θ ∧
        θ.range = Δ.rankOne i j ∧
        (∀ g v, θ g (φ v) = φ (rk1ModelAct g v)) ∧
        ∀ g, ∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, θ g u = u := by
  obtain ⟨φ, hφinj, hφrange, hφQ, hφτ⟩ := Δ.exists_rk1_isometry hp2 hAΩ i j hij
  obtain ⟨θ, hθφ, hθfix, hθinj, hθorth, hθC, hθuniq⟩ :=
    Δ.exists_rk1_theta hfix i j hij φ hφinj hφrange hφQ hφτ
  refine ⟨φ, hφinj, hφrange, hφQ, θ, hθinj, ?_, hθφ, hθfix⟩
  · apply le_antisymm
    ·
      have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
        CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hq
      have hleO : θ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
        rintro x ⟨g, rfl⟩
        exact hθorth g
      have hrangeΩ : θ.range ≤ orthDerived Q := by
        have hmap : θ.range = ⁅θ.range, θ.range⁆ := by
          have h1 : (commutator (Matrix.SpecialLinearGroup (Fin 2) K)).map θ = θ.range := by
            rw [hperf.commutator_eq_top, MonoidHom.range_eq_map]
          have h2 : (commutator (Matrix.SpecialLinearGroup (Fin 2) K)).map θ =
              ⁅θ.range, θ.range⁆ := by
            rw [commutator_def, Subgroup.map_commutator, MonoidHom.range_eq_map]
          rw [← h2, h1]
        rw [hmap]
        exact Subgroup.commutator_mono hleO hleO
      change θ.range ≤ CFSG.StandardType.ggOTwoPrime
        (Subgroup.centralizer (Δ.reflFixed i j : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q)
      rw [ggOTwoPrime, MonoidHom.range_eq_map, ← sl2_closure_involutions_eq_top,
        MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro y ⟨g, hg, rfl⟩
      rw [Set.mem_setOf_eq] at hg
      refine ⟨⟨hθC g, hrangeΩ ⟨g, rfl⟩⟩, ⟨1, ?_⟩⟩
      show (θ g) ^ 2 = 1
      rw [← map_pow, hg, map_one]
    · exact Δ.rankOne_le_range hp2 hfix i j φ hφinj hφrange hφQ hφτ θ hθuniq

theorem tbjOm_rankOne_model {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r) (_hr : 3 ≤ r)
    (hq : 4 ≤ Nat.card K) (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r) (hij : i ≠ j) :
    ∃ θ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V), Function.Injective θ ∧
      θ.range = Δ.rankOne i j ∧
      ∀ g ∈ θ.range, ∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, g u = u := by
  obtain ⟨_φ, _hφinj, _hφrange, _hφQ, θ, hθinj, hθrange, _hθφ, hθfix⟩ :=
    Δ.exists_rankOne_model hp2 hAΩ hq hfix i j hij
  refine ⟨θ, hθinj, hθrange, ?_⟩
  rintro g ⟨g₀, rfl⟩ k hki hkj u hu
  exact hθfix g₀ k hki hkj u hu

end OrthTorus

end CFSG.StandardType

end
