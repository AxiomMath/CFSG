module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34
open Matrix

theorem hSL_mem_upperTriangular {k : Type} [Field k] (u : kˣ) : hSL u ∈ upperTriangular 3 k := by
  intro i j hij
  rw [hSL, LinearThreeFourFixedNine.coe_dHom, diagonal_apply_ne _ (ne_of_gt hij)]

theorem exists_orderOf_eq_three_mem_normalizer {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSL 3 2 2) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) :
    ∃ y ∈ Subgroup.normalizer (S : Set X), orderOf y = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP k 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card (n := 2)
      (by rw [hk]; norm_num)
  set P := projectiveSL 3 k
  have hS2 : IsPGroup 2 (S.map e.toMonoidHom) := hS.2.1.map _
  have hSi : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    have := hS.2.2
    change ¬ 2 ∣ S.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  let PS : Sylow 2 P := hS2.toSylow hSi
  obtain ⟨PU, hPU⟩ := exists_sylow_projUnitriangular (K := k) 2 (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq P PU PS
  have hPS : (PS : Subgroup P) = (projUnitriangular 3 k).map (MulAut.conj x : P →* P) := by
    rw [← hx, coe_sylow_smul, hPU]
  have hu3 : Nat.card kˣ = 3 := by rw [Nat.card_units, hk]
  obtain ⟨u, hu⟩ : ∃ u : kˣ, u ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Subsingleton kˣ := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  have ha : orderOf (aP u) = 3 := orderOf_eq_prime (pow_three_of_mem_eZero hk aP_mem_eZero)
    (aP_ne_one hk hu)
  have haB : aP u ∈ projUpperTriangular 3 k := ⟨_, hSL_mem_upperTriangular u, rfl⟩
  have hmem : MulAut.conj x (aP u) ∈
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup P) : Set P) := by
    have h1 : (S.map e.toMonoidHom : Subgroup P) = (PS : Subgroup P) := rfl
    rw [h1, hPS, normalizer_map_conj, normalizer_projUnitriangular 2]
    exact ⟨aP u, haB, rfl⟩
  rw [← Subgroup.map_equiv_normalizer_eq S e] at hmem
  obtain ⟨y, hy, hye⟩ := hmem
  refine ⟨y, hy, ?_⟩
  have h1 : orderOf (e y) = orderOf y := MulEquiv.orderOf_eq e y
  have h2 : orderOf (MulAut.conj x (aP u)) = orderOf (aP u) := MulEquiv.orderOf_eq _ _
  have h3 : e y = MulAut.conj x (aP u) := hye
  rw [← h1, h3, h2, ha]

end CFSG.Quasithin.H13
