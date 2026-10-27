module

public import Mathlib.GroupTheory.Perm.Subgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

def s16t3_partStab : Subgroup (Equiv.Perm (Fin 7)) :=
  (Equiv.Perm.subtypeCongrHom
    (fun x : Fin 7 => x ∈ ({0, 1, 2, 3} : Finset (Fin 7)))).range

theorem s16t3_partStab_card : Nat.card ↥s16t3_partStab = 144 := by
  change Nat.card ↥(Equiv.Perm.subtypeCongrHom
    (fun x : Fin 7 => x ∈ ({0, 1, 2, 3} : Finset (Fin 7)))).range = 144
  rw [Nat.card_eq_fintype_card, Equiv.Perm.subtypeCongrHom.card_range,
    Fintype.card_prod, Fintype.card_perm, Fintype.card_perm]
  have h1 : Fintype.card ↥({0, 1, 2, 3} : Finset (Fin 7)) = 4 := by
    rw [Fintype.card_coe]; decide
  have h2 : Fintype.card {x : Fin 7 // x ∉ ({0, 1, 2, 3} : Finset (Fin 7))} = 3 := by
    rw [Fintype.card_subtype]; decide
  rw [h1, h2]
  decide

theorem s16t3_partStab_swap_mem : Equiv.swap (0 : Fin 7) 1 ∈ s16t3_partStab := by
  rw [s16t3_partStab, MonoidHom.mem_range]
  refine ⟨(Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩, 1), ?_⟩
  ext x
  fin_cases x <;> decide

theorem s16t3_partStab_inf_alt_card :
    Nat.card ↥(s16t3_partStab ⊓ alternatingGroup (Fin 7)) = 72 := by
  have hrel : (s16t3_partStab ⊓ alternatingGroup (Fin 7)).relIndex s16t3_partStab = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
    refine ⟨Equiv.swap (0 : Fin 7) 1, s16t3_partStab_swap_mem, ?_, ?_⟩
    · intro h
      have h1 : Equiv.Perm.sign (Equiv.swap (0 : Fin 7) 1) = 1 :=
        Equiv.Perm.mem_alternatingGroup.1 h.2
      rw [Equiv.Perm.sign_swap (by decide)] at h1
      norm_num at h1
    · intro b hb
      by_cases hbA : b ∈ alternatingGroup (Fin 7)
      · exact Or.inr ⟨hb, hbA⟩
      · refine Or.inl ⟨s16t3_partStab.mul_mem s16t3_partStab_swap_mem hb, ?_⟩
        show Equiv.Perm.sign (Equiv.swap (0 : Fin 7) 1 * b) = 1
        have hb1 : Equiv.Perm.sign b = 1 ∨ Equiv.Perm.sign b = -1 :=
          Int.units_eq_one_or _
        rcases hb1 with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hbA
        · rw [map_mul, Equiv.Perm.sign_swap (by decide), h]
          norm_num
  have h := Subgroup.card_mul_index
    ((s16t3_partStab ⊓ alternatingGroup (Fin 7)).subgroupOf s16t3_partStab)
  rw [show ((s16t3_partStab ⊓ alternatingGroup (Fin 7)).subgroupOf s16t3_partStab).index = 2
      from hrel, s16t3_partStab_card] at h
  have hc : Nat.card ↥((s16t3_partStab ⊓ alternatingGroup (Fin 7)).subgroupOf s16t3_partStab) =
      Nat.card ↥(s16t3_partStab ⊓ alternatingGroup (Fin 7)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hc] at h
  omega

private theorem s16t3_eq_alt_or_top (N' : Subgroup (Equiv.Perm (Fin 7)))
    (hA : alternatingGroup (Fin 7) ≤ N') :
    N' = alternatingGroup (Fin 7) ∨ N' = ⊤ := by
  have h := Subgroup.relIndex_mul_index hA
  rw [alternatingGroup.index_eq_two] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 ⟨N'.index, h.symm⟩ with h1 | h2
  · left
    have hsub : (alternatingGroup (Fin 7)).subgroupOf N' = ⊤ := by
      rw [← Subgroup.index_eq_one]; exact h1
    exact le_antisymm (fun x hx => by
      have hmem : (⟨x, hx⟩ : ↥N') ∈ (alternatingGroup (Fin 7)).subgroupOf N' := by
        rw [hsub]; trivial
      exact Subgroup.mem_subgroupOf.mp hmem) hA
  · right
    have : N'.index = 1 := by rw [h2] at h; omega
    rwa [Subgroup.index_eq_one] at this

theorem s16t3_isSylowOf_exists_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H P Q : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P H)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    ∃ g ∈ H, P = Q.map (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨QP, hQP⟩ := hP.exists_sylow_eq_subgroupOf
  obtain ⟨QQ, hQQ⟩ := hQ.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := ↥H) QQ QP
  refine ⟨(g : G), g.2, ?_⟩
  have hQPmap : (QP : Subgroup ↥H).map H.subtype = P := by
    rw [hQP, Subgroup.map_subgroupOf_eq_of_le hP.le]
  have hQQmap : (QQ : Subgroup ↥H).map H.subtype = Q := by
    rw [hQQ, Subgroup.map_subgroupOf_eq_of_le hQ.le]
  have hconj : (QP : Subgroup ↥H) = (QQ : Subgroup ↥H).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hnat : H.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  calc P = (QP : Subgroup ↥H).map H.subtype := hQPmap.symm
    _ = ((QQ : Subgroup ↥H).map (MulAut.conj g).toMonoidHom).map H.subtype := by rw [hconj]
    _ = (QQ : Subgroup ↥H).map (H.subtype.comp (MulAut.conj g).toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (QQ : Subgroup ↥H).map ((MulAut.conj (g : G)).toMonoidHom.comp H.subtype) := by rw [hnat]
    _ = ((QQ : Subgroup ↥H).map H.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = Q.map (MulAut.conj (g : G)).toMonoidHom := by rw [hQQmap]

theorem s16t3_exists_sylow_le_perm_seven (N' : Subgroup (Equiv.Perm (Fin 7)))
    (hA : alternatingGroup (Fin 7) ≤ N') {P : Subgroup (Equiv.Perm (Fin 7))}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P N') :
    ∃ J : Subgroup (Equiv.Perm (Fin 7)), J ≤ N' ∧ P ≤ J ∧
      Nat.card ↥J = 9 * Nat.card ↥P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases s16t3_eq_alt_or_top N' hA with hAlt | hTop
  ·
    subst hAlt
    have hcardA7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hcardP : Nat.card ↥P = 8 := by
      rw [hP.card_eq, hcardA7]
      rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
        Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 315)]
      norm_num
    have hcardKN : Nat.card ↥(s16t3_partStab ⊓ alternatingGroup (Fin 7)) = 9 * Nat.card ↥P := by
      rw [s16t3_partStab_inf_alt_card, hcardP]
    obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥(s16t3_partStab ⊓ alternatingGroup (Fin 7))) := inferInstance
    let S : Subgroup (Equiv.Perm (Fin 7)) :=
      (Q : Subgroup ↥(s16t3_partStab ⊓ alternatingGroup (Fin 7))).map
        (s16t3_partStab ⊓ alternatingGroup (Fin 7)).subtype
    have hSle : S ≤ s16t3_partStab ⊓ alternatingGroup (Fin 7) := Subgroup.map_subtype_le _
    have hSleN : S ≤ alternatingGroup (Fin 7) := hSle.trans inf_le_right
    have hSis : CFSG.ABGLocalTools.IsSylowOf 2 S (s16t3_partStab ⊓ alternatingGroup (Fin 7)) :=
      ⟨Q, rfl⟩
    have hScard : Nat.card ↥S = 8 := by
      rw [Subgroup.card_map_of_injective
        (s16t3_partStab ⊓ alternatingGroup (Fin 7)).subtype_injective]
      rw [Q.card_eq_multiplicity, hcardKN, hcardP,
        show (9 * 8 : ℕ) = 2 ^ 3 * 9 by norm_num,
        Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 9)]
      norm_num
    have hSisN : CFSG.ABGLocalTools.IsSylowOf 2 S (alternatingGroup (Fin 7)) := by
      apply CFSG.ABGLocalTools.isSylowOf_of_card hSleN
      rw [hScard, hcardA7]
      rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
        Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 315)]
      norm_num
    obtain ⟨g, hgH, hg⟩ := s16t3_isSylowOf_exists_conj hP hSisN
    refine ⟨(s16t3_partStab ⊓ alternatingGroup (Fin 7)).map
      (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact (alternatingGroup (Fin 7)).mul_mem
        ((alternatingGroup (Fin 7)).mul_mem hgH hy.2)
        ((alternatingGroup (Fin 7)).inv_mem hgH)
    · rw [hg]
      exact Subgroup.map_mono hSle
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardKN]
  ·
    subst hTop
    have hcardTop : Nat.card ↥(⊤ : Subgroup (Equiv.Perm (Fin 7))) = 5040 := by
      rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
      decide
    have hcardP : Nat.card ↥P = 16 := by
      rw [hP.card_eq, hcardTop]
      rw [show (5040 : ℕ) = 2 ^ 4 * 315 by norm_num,
        Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 315)]
      norm_num
    have hcardKN : Nat.card ↥(s16t3_partStab ⊓ (⊤ : Subgroup (Equiv.Perm (Fin 7)))) =
        9 * Nat.card ↥P := by
      rw [inf_top_eq, s16t3_partStab_card, hcardP]
    obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥(s16t3_partStab ⊓ (⊤ : Subgroup (Equiv.Perm (Fin 7))))) :=
      inferInstance
    let S : Subgroup (Equiv.Perm (Fin 7)) :=
      (Q : Subgroup ↥(s16t3_partStab ⊓ (⊤ : Subgroup (Equiv.Perm (Fin 7))))).map
        (s16t3_partStab ⊓ (⊤ : Subgroup (Equiv.Perm (Fin 7)))).subtype
    have hSle : S ≤ s16t3_partStab ⊓ (⊤ : Subgroup (Equiv.Perm (Fin 7))) :=
      Subgroup.map_subtype_le _
    have hSleN : S ≤ (⊤ : Subgroup (Equiv.Perm (Fin 7))) := le_top
    have hSis : CFSG.ABGLocalTools.IsSylowOf 2 S
        (s16t3_partStab ⊓ (⊤ : Subgroup (Equiv.Perm (Fin 7)))) := ⟨Q, rfl⟩
    have hScard : Nat.card ↥S = 16 := by
      rw [Subgroup.card_map_of_injective
        (s16t3_partStab ⊓ (⊤ : Subgroup (Equiv.Perm (Fin 7)))).subtype_injective]
      rw [Q.card_eq_multiplicity, hcardKN, hcardP,
        show (9 * 16 : ℕ) = 2 ^ 4 * 9 by norm_num,
        Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 9)]
      norm_num
    have hSisN : CFSG.ABGLocalTools.IsSylowOf 2 S (⊤ : Subgroup (Equiv.Perm (Fin 7))) := by
      apply CFSG.ABGLocalTools.isSylowOf_of_card hSleN
      rw [hScard, hcardTop]
      rw [show (5040 : ℕ) = 2 ^ 4 * 315 by norm_num,
        Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 315)]
      norm_num
    obtain ⟨g, hgH, hg⟩ := s16t3_isSylowOf_exists_conj hP hSisN
    refine ⟨s16t3_partStab.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
    · exact le_top
    · rw [hg]
      exact Subgroup.map_mono (hSle.trans inf_le_left)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        s16t3_partStab_card, hcardP]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
