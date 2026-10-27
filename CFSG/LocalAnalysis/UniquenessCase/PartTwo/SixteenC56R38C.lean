module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56EigC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56TorB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56NormA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56NormB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open scoped Matrix MatrixGroups

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem exists_matrix_of_singular_fixed {a : MulAut W}
    (ha : a ∈ Subgroup.normalizer (S.omega : Set (MulAut W)))
    (haq : a ^ (Nat.card S.K - 1) = 1) {e : W} (he1 : e ≠ 1)
    (hfix : ∀ w : W, a w = w ↔ ∃ c : S.K, w = S.smul c e) :
    ∃ (A : GL OmI S.K) (c : S.K), S.actHom A = a ∧ A ^ (Nat.card S.K - 1) = 1 ∧
      (∀ v, OmegaEig.quad ((A : Matrix OmI OmI S.K) *ᵥ v) = c * OmegaEig.quad v) ∧
      ∀ v, (A : Matrix OmI OmI S.K) *ᵥ v = v ↔ ∃ t : S.K, v = t • S.vec e := by
  obtain ⟨σ, hσ⟩ := S.exists_ringEquiv_of_mem_normalizer ha
  have he : a e = e := (hfix e).mpr ⟨1, (S.smul_one_eq e).symm⟩
  have hσid : σ = RingEquiv.refl S.K := by
    ext c
    have hfixc : a (S.smul c e) = S.smul c e := (hfix (S.smul c e)).mpr ⟨c, rfl⟩
    have h1 : S.smul (σ c) e = S.smul c e := by
      calc S.smul (σ c) e = S.smul (σ c) (a e) := by rw [he]
        _ = a (S.smul c e) := (hσ c e).symm
        _ = S.smul c e := hfixc
    have hve : S.vec e ≠ 0 := by
      intro h
      exact he1 (S.vec_injective (by rw [h, S.vec_one]))
    have h2 : (σ c - c) • S.vec e = 0 := by
      have h := congrArg S.vec h1
      rw [S.vec_smul, S.vec_smul] at h
      rw [sub_smul, h, sub_self]
    have hzero : σ c - c = 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hve
      have h3 : (σ c - c) * S.vec e i = 0 := by
        simpa [Pi.smul_apply, smul_eq_mul] using congrFun h2 i
      exact (mul_eq_zero.mp h3).resolve_right hi
    exact sub_eq_zero.mp hzero
  have hlin : ∀ (c : S.K) (w : W), a (S.smul c w) = S.smul c (a w) := by
    intro c w
    rw [hσ c w, hσid]
    rfl
  obtain ⟨A, hAa⟩ := S.exists_actHom_of_smul_comm hlin
  have hAq : A ^ (Nat.card S.K - 1) = 1 := by
    apply S.actHom_injective
    rw [map_pow, hAa, haq, map_one]
  obtain ⟨c, hc0, hcQ⟩ := S.exists_similitude_of_linear ha hlin
  have hAQ : ∀ v : OmI → S.K,
      OmegaEig.quad ((A : Matrix OmI OmI S.K) *ᵥ v) = c * OmegaEig.quad v := by
    intro v
    have h1 : S.Q (S.actHom A (S.ofVec v)) = OmegaEig.quad ((A : Matrix OmI OmI S.K) *ᵥ v) := by
      change StatedQuadPlus 2 S.K (S.vec (S.actHom A (S.ofVec v))) =
        StatedQuadPlus 2 S.K ((A : Matrix OmI OmI S.K) *ᵥ v)
      rw [S.actHom_vec, S.vec_ofVec]
    have h2 : S.Q (S.ofVec v) = OmegaEig.quad v := by
      change StatedQuadPlus 2 S.K (S.vec (S.ofVec v)) = StatedQuadPlus 2 S.K v
      rw [S.vec_ofVec]
    have h := hcQ (S.ofVec v)
    rw [← hAa] at h
    rw [h1, h2] at h
    exact h
  have hAfix : ∀ v, (A : Matrix OmI OmI S.K) *ᵥ v = v ↔ ∃ t : S.K, v = t • S.vec e := by
    intro v
    constructor
    · intro hv
      have h1 : S.vec (S.actHom A (S.ofVec v)) = S.vec (S.ofVec v) := by
        rw [S.actHom_vec, S.vec_ofVec, hv]
      have h2 : S.actHom A (S.ofVec v) = S.ofVec v := S.vec_injective h1
      rw [hAa] at h2
      obtain ⟨t, ht⟩ := (hfix (S.ofVec v)).mp h2
      refine ⟨t, ?_⟩
      have h3 := congrArg S.vec ht
      rwa [S.vec_ofVec, S.vec_smul] at h3
    · rintro ⟨t, rfl⟩
      have h2 : a (S.ofVec (t • S.vec e)) = S.ofVec (t • S.vec e) := by
        have ht : S.ofVec (t • S.vec e) = S.smul t e := rfl
        rw [ht]
        exact (hfix (S.smul t e)).mpr ⟨t, rfl⟩
      have h3 : S.actHom A (S.ofVec (t • S.vec e)) = S.ofVec (t • S.vec e) := by
        rw [hAa]; exact h2
      have h4 := congrArg S.vec h3
      rwa [S.actHom_vec, S.vec_ofVec] at h4
  exact ⟨A, c, hAa, hAq, hAQ, hAfix⟩

theorem actHom_mem_normalizer_omega {γ : GL OmI S.K}
    (hγ : ∀ v, OmegaEig.quad ((γ : Matrix OmI OmI S.K) *ᵥ v) = OmegaEig.quad v) :
    S.actHom γ ∈ Subgroup.normalizer (S.omega : Set (MulAut W)) := by
  let I : Subgroup (GL OmI S.K) := CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)
  have hγI : γ ∈ I := Subgroup.subset_closure hγ
  have hconj : ∀ δ ∈ I, ∀ x ∈ (⁅I, I⁆ : Subgroup (GL OmI S.K)), δ * x * δ⁻¹ ∈ ⁅I, I⁆ := by
    intro δ hδ x hx
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.normalizer_commutator_ge_left I I hδ) x).mp hx
  have homega : S.omega = (⁅I, I⁆).map S.actHom := rfl
  rw [Subgroup.mem_normalizer_iff, homega]
  intro h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.mpr ⟨γ * x * γ⁻¹, hconj γ hγI x hx,
      by rw [map_mul, map_mul, map_inv]⟩
  · intro hh
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨γ⁻¹ * y * γ, hconj γ⁻¹ (I.inv_mem hγI) y hy, ?_⟩
    rw [map_mul, map_mul, map_inv, hyeq]
    group

theorem exists_elemAbelian_of_singular_fixed {m : ℕ} (hSK : Nat.card S.K = 2 ^ m)
    (hq : (2 ^ m - 1).Prime) {a : MulAut W}
    (ha : a ∈ Subgroup.normalizer (S.omega : Set (MulAut W))) (haq : a ^ (2 ^ m - 1) = 1)
    {e : W} (he1 : e ≠ 1) (heQ : S.Q e = 0)
    (hfix : ∀ w : W, a w = w ↔ ∃ c : S.K, w = S.smul c e) :
    ∃ E : Subgroup (MulAut W), a ∈ E ∧ E ≤ S.omega ⊔ Subgroup.zpowers a ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ (2 ^ m - 1) = 1) ∧
      Nat.card E = (2 ^ m - 1) ^ 3 := by
  classical
  letI : Fintype S.K := Fintype.ofFinite S.K
  have hq1 : Nat.card S.K - 1 = 2 ^ m - 1 := by rw [hSK]
  obtain ⟨A, c, hAa, hAq, hAQ, hAfix⟩ :=
    S.exists_matrix_of_singular_fixed ha (by rw [hq1]; exact haq) he1 hfix
  have hve : S.vec e ≠ 0 := fun h => he1 (S.vec_injective (by rw [h, S.vec_one]))
  obtain ⟨γ, l, μ, hγ, hlμ, hAγ⟩ := OmegaEig.exists_isometry_diag A
    (by rw [Fintype.card_eq_nat_card]; exact hAq) hAQ hve heQ hAfix
  obtain ⟨E₀, hDE, hE₀le, hcomm, hexp, hcard⟩ := S.exists_elemAbelian_of_diag hSK hq l μ hlμ
  obtain ⟨g, hg⟩ : ∃ g : MulAut W, g = S.actHom γ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : MulAut W,
      D = S.actHom (OmegaEig.diagGL (OmegaEig.diagVals l μ)) := ⟨_, rfl⟩
  rw [← hD] at hDE hE₀le
  have hgN : g ∈ Subgroup.normalizer (S.omega : Set (MulAut W)) := by
    rw [hg]; exact S.actHom_mem_normalizer_omega hγ
  have hagD : a = (MulAut.conj g) D := by
    rw [MulAut.conj_apply, ← hAa, hg, hD, eq_mul_inv_iff_mul_eq, ← map_mul, hAγ, map_mul]
  have hωmap : S.omega.map (MulAut.conj g).toMonoidHom = S.omega := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by group⟩
      exact (Subgroup.mem_set_normalizer_iff''.mp hgN y).mp hy
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := MulEquiv.injective _
  refine ⟨E₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hagD]; exact Subgroup.mem_map_of_mem _ hDE
  · calc E₀.map (MulAut.conj g).toMonoidHom
        ≤ (S.omega ⊔ Subgroup.zpowers D).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hE₀le
      _ = S.omega ⊔ Subgroup.zpowers a := by
          rw [Subgroup.map_sup, hωmap, MonoidHom.map_zpowers, hagD]
          rfl
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  · exact (Nat.card_congr (Subgroup.equivMapOfInjective E₀ _ hinj).toEquiv).symm.trans hcard

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
