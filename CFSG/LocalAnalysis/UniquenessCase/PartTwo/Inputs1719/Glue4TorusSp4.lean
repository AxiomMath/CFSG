module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusReduction
import CFSG.LocalAnalysis.UniquenessCase.Lie.Sp4
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent borelSubgroup diagHom
  ker_diagHom torus_le_borelSubgroup exists_sylow_unipotent)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (normalizer_unipotent)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torus torusHom_injective)

private theorem g4sp_isSylowOf_unipotent {K : Type} [Field K] [Finite K] [CharP K 2]
    [Finite (StatedSp 2 K)] : CFSG.ABGLocalTools.IsSylowOf 2 (unipotent 2 K) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hP ▸ P.isPGroup', ?_⟩
  rw [relIndex_top_right, ← hP]
  exact P.not_dvd_index

private theorem g4sp_units_equiv {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : Nonempty (Kˣ ≃* Multiplicative (ZMod (2 ^ n - 1))) := by
  have e := (zmodCyclicMulEquiv (inferInstance : IsCyclic Kˣ)).symm
  rw [Nat.card_units, hK] at e
  exact ⟨e⟩

private theorem g4sp_torus_equiv {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    Nonempty (torus 2 K ≃* Multiplicative (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1))) := by
  obtain ⟨u⟩ := g4sp_units_equiv hK
  let p : (Fin 2 → Kˣ) ≃* Kˣ × Kˣ :=
    { piFinTwoEquiv fun _ => Kˣ with map_mul' := fun _ _ => rfl }
  exact ⟨(MonoidHom.ofInjective (torusHom_injective (r := 2) (k := K))).symm.trans
    (p.trans ((u.prodCongr u).trans (MulEquiv.prodMultiplicative _ _).symm))⟩

private theorem g4sp_pow_mem_unipotent {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {x : StatedSp 2 K} (hx : x ∈ borelSubgroup 2 K) :
    x ^ (2 ^ n - 1) ∈ unipotent 2 K := by
  have h : (⟨x, hx⟩ : borelSubgroup 2 K) ^ (2 ^ n - 1) ∈ (diagHom 2 K).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  rw [ker_diagHom, Subgroup.mem_subgroupOf] at h
  simpa using h

private theorem g4sp_orderOf_weyl {K : Type} [Field K] [CharP K 2] :
    ∃ k : ℕ, orderOf (uc22pwI2Weyl K) = 2 ^ k := by
  have h : orderOf (uc22pwI2Weyl K) ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one uc22pwI2_weyl_sq
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨k, hk⟩

private theorem g4sp_cartanAt_unipotent {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    CartanAt (unipotent 2 K) n (Multiplicative (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1))) := by
  refine ⟨torus 2 K, uc22pwI2Weyl K, ?_, g4sp_torus_equiv hK, ?_, g4sp_orderOf_weyl, ?_⟩
  · rw [normalizer_unipotent]
    exact torus_le_borelSubgroup
  · intro x hx
    rw [normalizer_unipotent] at hx
    refine iff_of_true (g4sp_pow_mem_unipotent hK hx) ?_
    rw [sup_comm, ← (uc22pwI2_sp4_borel (K := K)).1]
    exact hx
  · rintro _ ⟨s, rfl⟩
    exact uc22pwI2_weyl_inv_torus s

theorem cartanAt_of_isSp4 {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsSp4 X n) :
    ∃ U : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
      CartanAt U n (Multiplicative (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1))) := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel h
  haveI : Finite (StatedSp 2 K) := Finite.of_equiv X e.toEquiv
  exact ⟨_, isSylowOf_map_equiv g4sp_isSylowOf_unipotent e.symm,
    (g4sp_cartanAt_unipotent hK).map e.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
