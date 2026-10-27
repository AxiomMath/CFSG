module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Field
public import CFSG.LocalAnalysis.UniquenessCase.UCInspConjN
public import CFSG.LocalAnalysis.UniquenessCase.UCInspPair2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Abs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Core

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem center_SL3_eq_bot (hcube : ∀ c : K, c ^ 3 = 1 → c = 1) :
    Subgroup.center SL(3, K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  have hr1 : r = 1 := hcube r hr
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

theorem inspL3_core_L {f : ℕ} (hf : 1 ≤ f) (hpf : Nat.card K = p ^ f)
    (hq : Nat.card K % 3 = 2) (D : Subgroup SL(3, K)) (hD : Nat.card D = 3) :
    ∃ (ℓ : ℕ) (R : Subgroup SL(3, K)), ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ InspPair ℓ D R := by
  have hcube := cube_roots_trivial hq
  have h3 := three_ne_zero_of_card_mod hf hpf hq
  have hω := no_root_of_cube_trivial h3 hcube
  obtain ⟨ℓ, b, z, hℓ, hℓ2, hℓ3, hℓq, hb3, hbns, hzℓ, hz1, hbz⟩ := exists_model_L hf hpf hq
  have hpair : InspPair ℓ (Subgroup.zpowers b) (Subgroup.zpowers z) :=
    inspPair_of_triple hℓ hb3 hzℓ hz1 hbz hℓq
  obtain ⟨d, hDd, hd3, hd1⟩ := exists_gen_of_card_three D hD
  have hmul3 : ∀ x : SL(3, K), x ^ 3 = 1 →
      (x : Matrix (Fin 3) (Fin 3) K) * x * x = 1 := by
    intro x hx
    have := congrArg (fun y : SL(3, K) => (y : Matrix (Fin 3) (Fin 3) K)) hx
    simpa [pow_succ] using this
  have hdns : ∀ c : K, (d : Matrix (Fin 3) (Fin 3) K) ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hc
    have h1 := hmul3 d hd3
    rw [hc] at h1
    have hc3 : c ^ 3 = 1 := by
      have h2 := congrFun (congrFun h1 0) 0
      have h2' : c * (c * c) = 1 := by
        simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_apply] using h2
      linear_combination h2'
    have hc1 : c = 1 := hcube c hc3
    apply hd1
    apply Subtype.ext
    rw [hc, hc1, one_smul]
    rfl
  obtain ⟨Q, hQ⟩ := exists_conj3 h3 hω (b : Matrix (Fin 3) (Fin 3) K) (d : Matrix (Fin 3) (Fin 3) K)
    (hmul3 b hb3) b.2 hbns (hmul3 d hd3) d.2 hdns
  have hcb : conjSLnEquiv Q b = d := conjSLnEquiv_eq_of_mul_eq Q hQ
  refine ⟨ℓ, (Subgroup.zpowers z).map (conjSLnEquiv Q).toMonoidHom, hℓ, hℓ2, hℓ3, ?_⟩
  have := hpair.map (conjSLnEquiv Q)
  rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hcb, ← hDd] at this

end Core

theorem inspL3_L {G : Type} [Group G] [Finite G] {p f : ℕ} (hq : p ^ f % 3 = 2)
    (hL : LieModel G .PSL 3 p f) (D : Subgroup G) (hD : Nat.card D = 3) :
    ∃ (ℓ : ℕ) (R : Subgroup G), ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ InspPair ℓ D R := by
  have hadm := hL.admissible
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype K := Fintype.ofFinite K
    have hKc : CharP K p :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
    have hq' : Nat.card K % 3 = 2 := by rw [hK]; exact hq
    let e₁ : G ≃* PSL(3, K) := e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
    let e₂ : PSL(3, K) ≃* SL(3, K) :=
      (QuotientGroup.quotientMulEquivOfEq (center_SL3_eq_bot (cube_roots_trivial hq'))).trans
        QuotientGroup.quotientBot
    let e' : G ≃* SL(3, K) := e₁.trans e₂
    obtain ⟨ℓ, R', hℓ, hℓ2, hℓ3, hpair⟩ := inspL3_core_L hf hK hq' (D.map e'.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e'.injective, hD])
    exact ⟨ℓ, R'.map e'.symm.toMonoidHom, hℓ, hℓ2, hℓ3, InspPair.of_map_equiv e' hpair⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
