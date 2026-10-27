module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeA
public import CFSG.GH74.Filter.Small.Wrappers
public import CFSG.GH74.Filter.Small.Alternating
public import CFSG.GH74.Filter.Small.RankThree

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Equiv

theorem card_le_of_twoRank_le {X : Type} [Group X] [Finite X] {r : ℕ} (h : twoRank X ≤ r)
    {E : Subgroup X} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE).exists_card_eq
  have h1 := CFSG.SectionRank.le_pRank Nat.one_lt_two le_top hE hk
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (h1.trans h)

theorem twoRankLtSix_of_twoRank_le {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r ≤ 5)
    (h : twoRank X ≤ r) : TwoRankLtSix X := fun _ hE =>
  lt_of_le_of_lt (card_le_of_twoRank_le h hE) (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem TwoRankLtSix.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : TwoRankLtSix Y) : TwoRankLtSix X := by
  intro E hE
  have h1 := h (E.map e.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective e.injective] at h1

theorem alt8_elt_mem : (c[0, 1, 2, 3] * swap 4 5 : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem twoRankLtSix_alt8 : TwoRankLtSix (alternatingGroup (Fin 8)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hE
  have hE2 := CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have hcard : Nat.card (alternatingGroup (Fin 8)) = 2 ^ 6 * 315 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hmul := E.card_mul_index
  rw [hk, hcard] at hmul
  have hk6 : k ≤ 6 := by
    have hA : 2 ^ k ∣ 2 ^ 6 :=
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 315)).dvd_of_dvd_mul_right
        ⟨E.index, hmul.symm⟩
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hA
  rw [hk]
  rcases Nat.lt_or_ge k 6 with h | h
  · exact Nat.pow_lt_pow_right (by norm_num) h
  · exfalso
    have hk6' : k = 6 := by omega
    subst hk6'
    have hidx : E.index = 315 := by omega
    let P : Sylow 2 (alternatingGroup (Fin 8)) := hE2.toSylow (by rw [hidx]; decide)
    set g : alternatingGroup (Fin 8) := ⟨c[0, 1, 2, 3] * swap 4 5, alt8_elt_mem⟩ with hgdef
    have hg2 : g ^ 2 ≠ 1 := by
      intro h
      have := congrArg Subtype.val h
      exact absurd this (by decide)
    have hg4 : g ^ 4 = 1 := Subtype.ext (by decide)
    have hord : orderOf g = 2 ^ 2 :=
      orderOf_eq_prime_pow (by rw [pow_one]; exact hg2) (by norm_num; exact hg4)
    have hgp : IsPGroup 2 (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord])
    obtain ⟨T, hT⟩ := hgp.exists_le_sylow
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) T P
    have hmem : x * g * x⁻¹ ∈ E := by
      have h1 : (x • T : Sylow 2 _) = P := hx
      have h2 : x * g * x⁻¹ ∈ ((x • T : Sylow 2 _) : Subgroup (alternatingGroup (Fin 8))) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul g (MulAut.conj x) _ (hT (Subgroup.mem_zpowers g))
      rw [h1, IsPGroup.toSylow_coe] at h2
      exact h2
    have h3 := hE.2 _ hmem
    rw [conj_pow] at h3
    apply hg2
    have h4 := congrArg (fun y => x⁻¹ * y * x) h3
    simpa [mul_assoc] using h4

theorem heInspRankAlt_holds : HeInspRankAlt := by
  refine ⟨fun n h5 h8 => ?_, fun X _ _ h => ?_⟩
  · rcases (by omega : n ≤ 7 ∨ n = 8) with h7 | rfl
    · exact twoRankLtSix_of_twoRank_le (by norm_num)
        (CFSG.GH74.Filter.t_alt_small (alternatingGroup (Fin n)) n h5 h7 ⟨MulEquiv.refl _⟩)
    · exact twoRankLtSix_alt8
  · obtain ⟨e⟩ := CFSG.GH74.Filter.t_iso_L4_two X h
    exact twoRankLtSix_alt8.of_mulEquiv e

theorem heInspRankOdd_holds : HeInspRankOdd := by
  intro X _ _ p _ hp2 h
  rcases h with ⟨f, -, hf⟩ | h | h
  · exact twoRankLtSix_of_twoRank_le (by norm_num) (CFSG.GH74.Filter.t_PSL_two_odd X p f hp2 hf)
  · exact twoRankLtSix_of_twoRank_le (by norm_num) (CFSG.GH74.Filter.t_PSL_three_odd X p 1 hp2 h)
  · exact twoRankLtSix_of_twoRank_le (by norm_num) (CFSG.GH74.Filter.t_PSU_three_odd X p 1 hp2 h)

end CFSG.Quasithin.H13
