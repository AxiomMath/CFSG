module

public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.HL3WrNPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem exists_permutes_of_invariant_member {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [hK : K.Normal] {Γ : Type} [Group Γ] [Finite Γ] {U P Q : Subgroup Γ}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUP : U ≤ P)
    (hP : Nat.card P = 9 * Nat.card U)
    (hinv : ∀ α : MulAut Γ, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P)
    (hQP : Q ≤ P) (hQ : Nat.card Q = 9) (hQ3 : ∀ q ∈ Q, q ^ 3 = 1)
    (e : ↥K ≃* Γ) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e hSK hU
  have hα : ∀ t ∈ S, U.map (autK e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (SporB.le_normalizer_inf hK ht)
  set H₀ : Subgroup Y := (P.map e'.symm.toMonoidHom).map K.subtype with hH₀
  have hSH₀ : S ⊓ K ≤ H₀ := (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
  have hnorm : S ≤ Subgroup.normalizer (H₀ : Set Y) := fun t ht =>
    mem_normalizer_pull e' (hinv _ (hα t ht))
  have hH₀K : H₀ ≤ K := pull_le e' P
  have hinf : S ⊓ H₀ = S ⊓ K :=
    le_antisymm (inf_le_inf_left _ hH₀K) (le_inf inf_le_left hSH₀)
  have hcardH₀ : Nat.card H₀ = Nat.card P := by
    rw [hH₀, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e'.symm.injective]
  have hcardSK : Nat.card ↥(S ⊓ K) = Nat.card U := by
    rw [← he', Subgroup.card_map_of_injective e'.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hnorm
  rw [hinf, hcardSK, hcardH₀, hP] at h
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have hH : Nat.card ↥(S ⊔ H₀) = 9 * Nat.card S := by
    have h2 : Nat.card ↥(S ⊔ H₀) * Nat.card U = (9 * Nat.card S) * Nat.card U := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hU0 h2
  set E : Subgroup Y := (Q.map e'.symm.toMonoidHom).map K.subtype with hE
  have hEH₀ : E ≤ H₀ := Subgroup.map_mono (Subgroup.map_mono hQP)
  have hEcard : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e'.symm.injective, hQ]
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow, ← map_pow, hQ3 q hq, map_one, map_one]
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hcop : Nat.Coprime (Nat.card E) (Nat.card S) := by
    rw [hEcard, hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hinfES : E ⊓ S = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hperm : CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
    refine CFSG.Quasithin.H.L3Wr.permute_of_card hinfES ?_
    calc Nat.card ↥(E ⊔ S) ≤ Nat.card ↥(S ⊔ H₀) :=
          Subgroup.card_le_of_le (sup_le (hEH₀.trans le_sup_right) le_sup_left)
      _ = 9 * Nat.card S := hH
      _ = Nat.card E * Nat.card S := by rw [hEcard]
  refine ⟨E, hEH₀.trans hH₀K, ?_, IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num), hE3, ?_,
    hperm⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hEcard
    norm_num at hEcard
  · intro hcyc
    have hexpdvd : Monoid.exponent ↥E ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hE3 g g.2)
    rw [IsCyclic.exponent_eq_card, hEcard] at hexpdvd
    norm_num at hexpdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
