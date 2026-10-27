module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Iso
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Theta
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Centralizer
import CFSG.LocalAnalysis.StandardType.GGOrthRk1PiecesPos
import CFSG.LocalAnalysis.StandardType.GGOrthRk1ModelDual

public section

open Module Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

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

theorem tbjOm_rankOne_commute_rankOnePos {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ}
    (Δ : TBJOmData Q p A r) (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r)
    (hij : i ≠ j) :
    ∀ x ∈ Δ.rankOne i j, ∀ y ∈ Δ.rankOnePos i j, x * y = y * x := by
  obtain ⟨φ, hφinj, hφrange, hφQ, hφτ, M, hM1, hMp, hMτ⟩ :=
    Δ.exists_rk1_isometry_pos hp2 hAΩ i j hij
  obtain ⟨θ, hθφ, hθfix, _hθinj, _hθorth, _hθC, hθuniq⟩ :=
    Δ.exists_rk1_theta hfix i j hij φ hφinj hφrange hφQ hφτ
  have hle := Δ.rankOne_le_range hp2 hfix i j φ hφinj hφrange hφQ hφτ θ hθuniq
  intro x hx
  obtain ⟨g, hgx⟩ := hle hx
  have hlePos : Δ.rankOnePos i j ≤
      Subgroup.centralizer ({θ g} : Set (V ≃ₗ[K] V)) := by
    change CFSG.StandardType.ggOTwoPrime
      (Subgroup.centralizer (Δ.reflFixedPos i j : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q) ≤ _
    rw [ggOTwoPrime, Subgroup.closure_le]
    rintro y ⟨⟨hyC, hyΩ⟩, m, hym⟩
    change y ∈ Subgroup.centralizer ({θ g} : Set (V ≃ₗ[K] V))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      orthDerived_le_orthogonalGroup Q hyΩ
    have hmapsto := (TBJOmData.centralizerPos_mapsTo Δ hfix i j hij hyC).2
    have hfix2 : ∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, y u = u :=
      fun k hki hkj => TBJOmData.centralizerPos_two_fix hp2 Δ hfix i j hyC hym k hki hkj
    have hmem : ∀ v : Δ.D × Δ.D, (y.toLinearMap ∘ₗ φ) v ∈ LinearMap.range φ := by
      intro v
      rw [hφrange]
      exact hmapsto (φ v) (by rw [← hφrange]; exact LinearMap.mem_range_self φ v)
    obtain ⟨h, hφh⟩ := exists_end_of_mapsTo hφinj hmem
    let fW : Fin r → Multiplicative (ZMod p) :=
      fun l => if l = i then Multiplicative.ofAdd (1 : ZMod p)
        else if l = j then Multiplicative.ofAdd (-1 : ZMod p) else 1
    have hfWi : fW i = Multiplicative.ofAdd (1 : ZMod p) := by simp [fW]
    have hfWj : fW j = Multiplicative.ofAdd (-1 : ZMod p) := by
      simp [fW, Ne.symm hij]
    have hfWmem : fW ∈ reflFixedCoordPos p r i j := by
      rw [reflFixedCoordPos, MonoidHom.mem_ker, MonoidHom.mul_apply]
      change fW i * fW j = 1
      rw [hfWi, hfWj]
      simp
    have hfWval : (toAdd (fW i)).val = 1 := by
      rw [hfWi, toAdd_ofAdd, ZMod.val_one'' (Nat.Prime.ne_one Fact.out)]
    have hτeq : ∀ w : Δ.D × Δ.D, Δ.τ fW (φ w) = φ (rk1ModelAct M w) := by
      intro w
      rw [hMτ fW hfWmem w, hfWval, pow_one]
    have hcomm : ∀ v : Δ.D × Δ.D, h (rk1ModelAct M v) = rk1ModelAct M (h v) := by
      intro v
      apply hφinj
      rw [hφh (rk1ModelAct M v), ← hτeq v, ← hτeq (h v), hφh v]
      have hcommτ : Δ.τ fW * y = y * Δ.τ fW :=
        (Subgroup.mem_centralizer_iff.mp hyC) (Δ.τ fW) ⟨fW, hfWmem, rfl⟩
      calc y (Δ.τ fW (φ v)) = (y * Δ.τ fW) (φ v) := rfl
        _ = (Δ.τ fW * y) (φ v) := by rw [hcommτ]
        _ = Δ.τ fW (y (φ v)) := rfl
    have hiso : ∀ v : Δ.D × Δ.D,
        rk1Omega Δ.finrank_D (h v).1 (h v).2 = rk1Omega Δ.finrank_D v.1 v.2 := by
      intro v
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
    obtain ⟨e, he⟩ := rk1ModelAct_commute_eq (D := Δ.D) Δ.finrank_D Fact.out hp2 hMp hM1
      hcomm hiso hk
    let y' : V ≃ₗ[K] V := y⁻¹ * θ g * y
    have hy'fix : ∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, y' u = u := by
      intro k hki hkj u hu
      have hyu : y u = u := hfix2 k hki hkj u hu
      have hθu : θ g u = u := hθfix g k hki hkj u hu
      have hyinv : y⁻¹ u = u := by
        simpa using (congrArg (fun z => y⁻¹ z) hyu).symm
      simp only [y', LinearEquiv.mul_apply]
      rw [hyu, hθu, hyinv]
    have hy'φ : ∀ v : Δ.D × Δ.D, y' (φ v) = φ (rk1ModelAct g v) := by
      intro v
      have hmap : rk1ModelAct g (h v) = h (rk1ModelAct g v) := by
        rw [he v, rk1ModelAct_map, he]
      simp only [y', LinearEquiv.mul_apply]
      rw [← hφh v, hθφ g (h v), hmap, hφh (rk1ModelAct g v)]
      simp
    have hy' : y' = θ g := hθuniq y' g hy'fix hy'φ
    exact (calc θ g * y = y * (y⁻¹ * θ g * y) := by group
      _ = y * θ g := by change y * y' = y * θ g; rw [hy']).symm
  intro y hy
  rw [← hgx]
  exact (Subgroup.mem_centralizer_iff.mp (hlePos hy)) (θ g) (Set.mem_singleton _)

theorem tbjOm_rankOneModel {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r)
    (hr : 3 ≤ r) (hq : 4 ≤ Nat.card K) (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) :
    Δ.RankOneModel := fun i j hij =>
  ⟨tbjOm_rankOne_model hp2 hAΩ Δ hr hq hfix i j hij,
    tbjOm_rankOne_commute_rankOnePos hp2 hAΩ Δ hfix i j hij⟩

end OrthTorus

end CFSG.StandardType

end
