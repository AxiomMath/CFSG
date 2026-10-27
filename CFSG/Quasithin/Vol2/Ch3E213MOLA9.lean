module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem exists_theta_lin {K : Type} [Group K] {p : ℕ} [Fact p.Prime] (hL : IsPSL 3 p 1 K) :
    ∃ θ : SL(3, GaloisField p 1) →* K, Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center SL(3, GaloisField p 1) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hL
  have := Fintype.ofFinite F
  have := Fintype.ofFinite (GaloisField p 1)
  have hcG : Fintype.card (GaloisField p 1) = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card p 1 one_ne_zero,
      hcard]
  let ρ : GaloisField p 1 ≃+* F := FiniteField.ringEquivOfCardEq hcG
  let ψ : SL(3, GaloisField p 1) →* SL(3, F) :=
    Matrix.SpecialLinearGroup.map (ρ : GaloisField p 1 →+* F)
  have hψi : Function.Injective ψ := fun x y h => Subtype.ext (Matrix.ext fun i j =>
    ρ.injective (by
      have h1 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) i j) h
      simpa [ψ, Matrix.SpecialLinearGroup.map_apply_coe] using h1))
  have hψs : Function.Surjective ψ := fun B =>
    ⟨Matrix.SpecialLinearGroup.map (ρ.symm : F →+* GaloisField p 1) B,
      Subtype.ext (by ext i j; simp [ψ, Matrix.SpecialLinearGroup.map_apply_coe])⟩
  set φ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F
  let π : SL(3, F) →* K := e.symm.toMonoidHom.comp
    (φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(3, F))))
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))
  refine ⟨π.comp ψ, hπ.comp hψs, fun x hx => ?_⟩
  rw [MonoidHom.mem_ker] at hx
  have h1 : ψ x ∈ Subgroup.center SL(3, F) := by
    have h2 : (QuotientGroup.mk (ψ x) : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 1 := by
      apply φ.injective
      apply e.symm.injective
      rw [map_one, map_one]
      exact hx
    exact (QuotientGroup.eq_one_iff (ψ x)).mp h2
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro y
  apply hψi
  rw [map_mul, map_mul, h1]

theorem exists_theta_uni {K : Type} [Group K] {p : ℕ} [Fact p.Prime] (hU : IsPSU 3 p 1 K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p), Nat.card F = (p ^ 1) ^ 2 ∧
      ∃ θ : Phan.Su F p 1 3 →* K, Function.Surjective θ ∧
        θ.ker ≤ Subgroup.center (Phan.Su F p 1 3) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hU
  have hch : CharP F p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hcard
  let ι : Phan.Su F p 1 3 ≃* StatedSU 3 (p ^ 1) F :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hcard 3)
  let θ : Phan.Su F p 1 3 →* K := e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp ι.toMonoidHom)
  refine ⟨F, inferInstance, inferInstance, hch, hcard, θ,
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp ι.surjective), fun x hx => ?_⟩
  rw [MonoidHom.mem_ker] at hx
  have h1 : (QuotientGroup.mk (ι x) : StatedProj (StatedSU 3 (p ^ 1) F)) = 1 := by
    apply e.symm.injective
    rw [map_one]
    exact hx
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have hc : ((x : Phan.Su F p 1 3) : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact h1
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  exact Subtype.ext (hc y)

end CFSG.Quasithin.Ch3E213M.OLA
