module

public import CFSG.Quasithin.EmptyFaithful.S153I38
public import CFSG.Quasithin.EmptyFaithful.R3cSL2

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace R3c

theorem isCyclic_isPGroup_three_statedSU {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Even n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {R : Subgroup ↥(StatedSU 3 (2 ^ n) K)} (hR : IsPGroup 3 R) :
    IsCyclic R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcharP : CharP K 2 :=
    charP_two_of_natCard_eq_two_pow (f := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  let e := CFSG.LieType.Universal.Unitary.equivStatedSU hK 3
  set T := CFSG.LieType.Universal.Unitary.levelTorus
    (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) (0 : Fin (3 / 2)) with hT
  have hTc : IsCyclic T := CFSG.SectionRank.OddCover.isCyclic_levelTorus_three
  set Z : Subgroup ↥(StatedSU 3 (2 ^ n) K) := T.map e.toMonoidHom with hZdef
  have hZc : IsCyclic Z := isCyclic_of_surjective (e.toMonoidHom.subgroupMap T)
    (MonoidHom.subgroupMap_surjective _ _)
  have hZ : Nat.card Z = (2 ^ n) ^ 2 - 1 := by
    rw [hZdef, Subgroup.card_map_of_injective e.injective,
      CFSG.LieType.Steinberg.card_levelTorus_three hK]
  have hG : Nat.card ↥(StatedSU 3 (2 ^ n) K) = Nat.card Z * ((2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1)) := by
    rw [CFSG.SectionRank.OddCover.card_statedSU_three hK, hZ]
    ring
  have hq : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even hn
  have hm : ¬ 3 ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1) := by
    intro h3
    have hq3 : (2 ^ n) ^ 3 % 3 = 1 := by
      rw [Nat.pow_mod, hq]
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · omega
    · omega
  exact CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_of_card_eq_mul hG hm hR

theorem noElemNine_statedProj_statedSU {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Even n)
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    CFSG.Quasithin.F134.NoElemNine (StatedProj (StatedSU 3 (2 ^ n) K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.Quasithin.F134.noElemNine_of_isCyclic fun Q hQ => ?_
  exact CFSG.Quasithin.F134.isCyclic_of_isPGroup_of_surjective (QuotientGroup.mk'_surjective _)
    (fun S => isCyclic_isPGroup_three_statedSU hn hK S.isPGroup') Q hQ

theorem noElemNine_of_isPSL_three_one {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    CFSG.Quasithin.F134.NoElemNine X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK2 : Nat.card K = 2 := by simpa using hK
  refine CFSG.Quasithin.F134.NoElemNine.of_mulEquiv e
    (CFSG.Quasithin.F134.noElemNine_of_isCyclic fun Q hQ => ?_)
  exact CFSG.Quasithin.F134.isCyclic_of_isPGroup_of_surjective (QuotientGroup.mk'_surjective _)
    (fun S => CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_of_le_GL_three (by omega) (by omega)
      S.isPGroup') Q hQ

theorem noElemNine_of_isPSL_two_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    CFSG.Quasithin.F134.NoElemNine X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact CFSG.Quasithin.F134.NoElemNine.of_mulEquiv e (noElemNine_statedProj_statedSL_two hK)

theorem noElemNine_of_isPSU_two_even {X : Type} [Group X] {n : ℕ} (hn : Even n)
    (h : IsPSU 3 2 n X) : CFSG.Quasithin.F134.NoElemNine X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact CFSG.Quasithin.F134.NoElemNine.of_mulEquiv e (noElemNine_statedProj_statedSU hn hK)

end R3c

theorem rankOneFamilies153_holds : RankOneFamilies153 := by
  intro X _ _ hZ hcases
  rw [R3c.pRank_three_top_eq_center_quotient hZ]
  refine R3c.pRank_three_le_one_of_noElemNine ?_
  rcases hcases with ⟨n, -, h⟩ | ⟨n, hn, h⟩ | h
  · exact R3c.noElemNine_of_isPSL_two_two h
  · exact R3c.noElemNine_of_isPSU_two_even hn h
  · exact R3c.noElemNine_of_isPSL_three_one h

end CFSG.Quasithin
