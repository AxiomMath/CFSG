module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.F918X4

import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

namespace NatSL2

variable {K : Type} [Field K]

theorem charP_two_of_card [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem exists_matrix_form [Finite K] [CharP K 2] (θ : MulAut ↥(StatedSL 2 K)) :
    ∃ (A : GL (Fin 2) K) (σ : K ≃+* K), ∀ γ : ↥(StatedSL 2 K),
      (((θ γ : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) * ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ *
          ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  let e := specialLinearGroupEquivStatedSL 2 K
  obtain ⟨M, σ, hM⟩ := KCRootAxis.exists_conj_mul_slFieldAut ((e.trans θ).trans e.symm)
  refine ⟨Matrix.SpecialLinearGroup.toGL M, σ, fun γ => ?_⟩
  obtain ⟨b, rfl⟩ := e.surjective γ
  have h1 : ((e.symm (θ (e b)) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) =
      ((M * KCRootAxis.slFieldAut K σ b * M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) :=
    congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 2) K) =>
      ((φ b : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hM
  have h2 : ((e.symm (θ (e b)) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) =
      (((θ (e b) : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← specialLinearGroupEquivStatedSL_coe 2 K (e.symm (θ (e b))), MulEquiv.apply_symm_apply]
  have h3 : (((KCRootAxis.slFieldAut K σ b : Matrix.SpecialLinearGroup (Fin 2) K)) :
      Matrix (Fin 2) (Fin 2) K) =
      ((b : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ := by
    ext i j
    exact KCRootAxis.slFieldAut_apply σ b i j
  have h4 : (((Matrix.SpecialLinearGroup.toGL M)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← map_inv Matrix.SpecialLinearGroup.toGL M]
    rfl
  rw [← h2, h1, specialLinearGroupEquivStatedSL_coe, h4, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, h3]
  rfl

theorem stableMod_of_bijective [Finite K] [CharP K 2] {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {π : ↥(StatedSL 2 K) →* ↥H}
    (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia H ⊤ ⊥ π) (hb : Function.Bijective π) :
    StableMod H := by
  refine stableMod_of_forall fun α => ?_
  obtain ⟨θ, hθ⟩ := exists_theta_of_bijective (D := FFModel.nat (StatedSL 2 K)) (π := π) hb α
  obtain ⟨A, σ, hA⟩ := exists_matrix_form θ
  exact mem_realized_of_semilinear hπ α θ hθ A σ hA

theorem center_eq_bot_of_bijective [CharP K 2] {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {π : ↥(StatedSL 2 K) →* ↥H} (hb : Function.Bijective π) :
    Subgroup.center ↥H = ⊥ := by
  let E : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥H :=
    (specialLinearGroupEquivStatedSL 2 K).trans (MulEquiv.ofBijective π hb)
  rw [← Subgroup.map_center_eq E, KCRootAxis.sl2_center_eq_bot, Subgroup.map_bot]

end NatSL2

theorem case1Twist_holds : Case1Twist := by
  intro V _ _ _ G L A _ hC
  obtain ⟨-, ⟨n, K, hKf, hKfin, hcard, π, hπ⟩, -, -⟩ := hC
  have : CharP K 2 := NatSL2.charP_two_of_card hcard
  have hb : Function.Bijective π := ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
  exact ⟨NatSL2.stableMod_of_bijective hπ hb, Or.inl (NatSL2.center_eq_bot_of_bijective hb)⟩

end CFSG.Quasithin.F918X
