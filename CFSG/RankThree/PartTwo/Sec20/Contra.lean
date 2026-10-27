module

public import CFSG.RankThree.PartTwo.Sec20.Statements
import CFSG.RankThree.PartTwo.Sec18.Item181b

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem exists_ctx20 {A M L N : Subgroup G} {c : G} (h : Hyp201 G A M L N c) :
    ∃ T : Subgroup G, Ctx20 G A M L N c T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sc, hSc⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (M ⊓ Subgroup.centralizer {c})
  have hScM : Sc ≤ M := hSc.le.trans inf_le_left
  obtain ⟨Q, hQ⟩ := (hSc.isPGroup.comap_subtype (K := M)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup M).map M.subtype with hT
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T M := ⟨Q, rfl⟩
  have hScT : Sc ≤ T := by
    rw [hT, ← Subgroup.map_subgroupOf_eq_of_le hScM]
    exact Subgroup.map_mono hQ
  refine ⟨T, h, hTsyl, ?_⟩
  have heq : T ⊓ Subgroup.centralizer {c} = Sc := by
    refine (hSc.eq_of_le (le_inf hScT (hSc.le.trans inf_le_right)) ?_ ?_).symm.symm
    · exact inf_le_inf_right _ hTsyl.le
    · exact hTsyl.isPGroup.to_le inf_le_left
  rw [heq]
  exact hSc

omit [Finite G] in
theorem le_normalizer_normalClosureIn (M : Subgroup G) (c : G) :
    M ≤ Subgroup.normalizer (normalClosureIn M c : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ normalClosureIn M c, m * x * m⁻¹ ∈ normalClosureIn M c := by
    intro m hm x hx
    have hle : normalClosureIn M c ≤
        (normalClosureIn M c).comap (MulAut.conj m).toMonoidHom := by
      rw [normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m', hm', rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine Subgroup.subset_closure ⟨m * m', M.mul_mem hm hm', ?_⟩
      change m * (m' * c * m'⁻¹) * m⁻¹ = m * m' * c * (m * m')⁻¹
      group
    exact hle hx
  intro m hm
  exact Sec18.mem_normalizer_of_conj_mem (key m hm) (key m⁻¹ (M.inv_mem hm))

theorem rank3II_20_1_contra (h204 : Item204) (h205 : Item205) (h208 : Item208)
    (h209 : Item209) : Item201Contra1 := by
  rintro G _ _ A M L N c ⟨h, H, hH, -, hL, -, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h18 : Sec18Std G A M := ⟨h.toPartTwoStanding, h.partTwoS_eq, h.mem_partTwoE,
    h.mem_scriptM⟩
  obtain ⟨T₀, hT₀⟩ := exists_ctx20 h
  obtain ⟨-, -, -, -, T, hT, hTN⟩ := h205 G A M L N c T₀ hT₀
  obtain ⟨-, hVeq, n, -, -, F, _, _, hF, -, -, -, β, -⟩ := h208 G A M L N c T hT hTN
  have h209' := h209 G A M L N c T hT hTN
  have hV2 : IsPGroup 2 (vTwenty M c T) :=
    hVeq ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c)
  have hV1 : vTwenty M c T ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (vTwenty M c T) :=
      Nat.card_congr β.symm.toEquiv
    rw [hbot, Subgroup.card_bot] at hcard
    have h3 : Nat.card (Multiplicative (Fin 3 → F)) = (2 ^ n) ^ 3 := by
      rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_eq_fintype_card,
        Fintype.card_fun, Fintype.card_fin, hF]
    rw [h3] at hcard
    have h1 : 1 < (2 ^ n) ^ 3 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow_iff.mpr (by
        rintro rfl
        have : Fintype.card F = 1 := by rw [hF, pow_zero]
        exact absurd this (Fintype.one_lt_card).ne'))
    omega
  have hKT : kTwenty M c ⊔ T ≤ Subgroup.normalizer (vTwenty M c T : Set G) := by
    rw [hVeq]
    refine (sup_le ?_ (hT.sylow.le.trans (le_normalizer_normalClosureIn M c))).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    exact Subgroup.le_normalizer
  obtain ⟨M', hM', hNM'⟩ := exists_mem_scriptM_of_isTwoLocal (X := ((kTwenty M c ⊔ T :
    Subgroup G) : Set G)) ⟨_, hV1, hV2, rfl⟩ hKT
  have hM'M : M' = M := by
    have := h204 G A M L N c T hT
    rw [this] at hM'
    exact hM'
  have hLN : L ≤ Subgroup.normalizer (vTwenty M c T : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h209'
  apply Sec18.perfectResidual_not_le_of_mem_scriptH h18 (scriptHStar_subset A M hH)
  rw [← hL, ← hM'M]
  exact hLN.trans hNM'

end CFSG.RankThree.PartTwo.Sec20
