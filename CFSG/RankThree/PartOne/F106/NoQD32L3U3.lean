module

public import CFSG.RankThree.PartOne.F106.QD32Class
public import CFSG.RankThree.PartOne.F106.NoQD32L3U3Count

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143X
  CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartOne.BRANCH

theorem card_ge_eighty_one_of_induces {T : Type} [Group T] {E R : Subgroup T} [Finite E]
    (hE : IsElementaryAbelian 3 E) (h : InducesQD32 E R) : 3 ^ 4 ≤ Nat.card E := by
  obtain ⟨ψ, hψs, hψc⟩ := h.hom
  exact card_ge_pow_four_of_normalizer_qd32 Nat.prime_three (by norm_num) hE h.normalizes ψ hψs hψc

theorem false_psl3_qd32 {T : Type} [Group T] {f : ℕ} (hmod : StatedClassicalModel T .PSL 3 2 f)
    {E R : Subgroup T} (hE : IsElementaryAbelian 3 E) (h : InducesQD32 E R) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : CharP K 2 := charP_two_of_card hK
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have h4 := card_ge_eighty_one_of_induces hE h
  have h27 := card_le_of_statedProj_three
    (by simpa using natCast_ne_zero_of_charTwo (K := K) (m := 3) rfl) (StatedSL 3 K)
    (fun g hg => det_eq_one_of_mem_statedSL' hg) e hE
  have := h4.trans h27
  norm_num at this

theorem false_psu3_qd32 {T : Type} [Group T] {f : ℕ} (hmod : StatedClassicalModel T .PSU 3 2 f)
    {E R : Subgroup T} (hE : IsElementaryAbelian 3 E) (h : InducesQD32 E R) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : CharP K 2 := charP_two_of_card (g := 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have h4 := card_ge_eighty_one_of_induces hE h
  have h27 := card_le_of_statedProj_three
    (by simpa using natCast_ne_zero_of_charTwo (K := K) (m := 3) rfl) (StatedSU 3 (2 ^ f) K)
    (fun g hg => det_eq_one_of_mem_statedSU' hg) e hE
  have := h4.trans h27
  norm_num at this

end CFSG.RankThree.PartOne.F106
