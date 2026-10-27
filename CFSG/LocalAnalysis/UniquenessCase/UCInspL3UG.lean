module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UMain
public import CFSG.LocalAnalysis.UniquenessCase.UCInspPair2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

section Center

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem scalars_subgroupOf_statedSU_eq_bot (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 3 = 1) :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxS : (x : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hx
  obtain ⟨c, hc⟩ := hxS
  have hxU : (x : GL (Fin 3) K) ∈ SUid (unitaryInvolution K p f) 3 := by
    rw [SUid_eq_statedSU hK 3]
    exact x.2
  obtain ⟨hdet, hiso⟩ := mem_SUid.1 hxU
  have hmat : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (c : K) • 1 := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  rw [hmat] at hdet hiso
  have hc3 : (c : K) ^ 3 = 1 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    exact hdet
  have hnorm : (c : K) ^ (p ^ f + 1) = 1 := by
    have e : conjTr (unitaryInvolution K p f) ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)) =
        (unitaryInvolution K p f (c : K)) • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [conjTr]
      · simp [conjTr, Matrix.one_apply, hij, Ne.symm hij]
    rw [e, smul_mul_smul_comm, Matrix.one_mul] at hiso
    have h0 := congrFun (congrFun hiso 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
    rw [pow_succ, ← unitaryInvolution_apply K p f]
    exact h0
  have hcop : Nat.Coprime 3 (p ^ f + 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  have hc1 : (c : K) = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hc3, hnorm⟩
  have hc1' : c = 1 := Units.ext hc1
  apply Subtype.ext
  rw [← hc, hc1', map_one]
  rfl

end Center

theorem inspL3_U {G : Type} [Group G] [Finite G] {p f : ℕ} (hq : p ^ f % 3 = 1)
    (hL : LieModel G .PSU 3 p f) (D : Subgroup G) (hD : Nat.card D = 3) :
    ∃ (ℓ : ℕ) (R : Subgroup G), ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ InspPair ℓ D R := by
  have hadm := hL.admissible
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype K := Fintype.ofFinite K
    have hKc : CharP K p :=
      charP_of_card_eq_prime_pow (f := 2 * f)
        (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
    let e₁ : G ≃* StatedSU 3 (p ^ f) K :=
      (e.trans (QuotientGroup.quotientMulEquivOfEq
        (scalars_subgroupOf_statedSU_eq_bot hK hq))).trans QuotientGroup.quotientBot
    let e' : G ≃* SU (unitaryInvolution K p f) 3 := e₁.trans (equivStatedSU hK 3).symm
    obtain ⟨ℓ, R', hℓ, hℓ2, hℓ3, hpair⟩ := inspL3_core_U (unitaryInvolution K p f)
      (unitaryInvolution_apply K p f) (unitaryInvolution_involutive hK) hf hK hq
      (D.map e'.toMonoidHom) (by rw [Subgroup.card_map_of_injective e'.injective, hD])
    exact ⟨ℓ, R'.map e'.symm.toMonoidHom, hℓ, hℓ2, hℓ3, InspPair.of_map_equiv e' hpair⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
