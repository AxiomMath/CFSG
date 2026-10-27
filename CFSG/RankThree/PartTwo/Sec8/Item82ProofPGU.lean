module

public import CFSG.RankThree.PartTwo.Sec8.Item82ProofDefs
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K] [Finite K] {f : ℕ}

theorem two_pow_even_mod_three (hf : Even f) : 2 ^ f % 3 = 1 := by
  obtain ⟨m, rfl⟩ := hf
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

omit [Finite K] in
theorem det_eq_one_of_mem_sylow_three_gu (hf : Even f) (h : UnitaryFieldData 2 f K)
    {x : GL (Fin 3) K} (hx : x ∈ Sec4.glPi false 3 (2 ^ f) K) {k : ℕ} (hk : x ^ 3 ^ k = 1) :
    (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have hu := (Sec4.mem_glPi_false h).1 hx
  have hdq : (x : Matrix (Fin 3) (Fin 3) K).det ^ (2 ^ f + 1) = 1 := by
    have h1 := congrArg Matrix.det hu
    have hbar : ((x : Matrix (Fin 3) (Fin 3) K).map h.bar).det =
        h.bar (x : Matrix (Fin 3) (Fin 3) K).det := (RingHom.map_det h.bar _).symm
    rw [Matrix.det_mul, Matrix.det_transpose, hbar, Matrix.det_one,
      UnitaryFieldData.bar_apply] at h1
    rw [pow_succ]
    exact h1
  have hd3 : (x : Matrix (Fin 3) (Fin 3) K).det ^ 3 ^ k = 1 := by
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hk, Units.val_one, Matrix.det_one]
  have hcop : Nat.Coprime (3 ^ k) (2 ^ f + 1) := by
    refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
    have := two_pow_even_mod_three hf
    omega
  have h1 : (x : Matrix (Fin 3) (Fin 3) K).det ^ Nat.gcd (3 ^ k) (2 ^ f + 1) = 1 :=
    pow_gcd_eq_one.mpr ⟨hd3, hdq⟩
  rwa [hcop.gcd_eq_one, pow_one] at h1

theorem isCyclic_of_le_of_forall_sylow {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {M D : Subgroup G} (hM : ∀ P : Sylow p M, IsCyclic P) (hD : IsPGroup p D) (hDM : D ≤ M) :
    IsCyclic D := by
  have hTD : D.subgroupOf M ≃* D := Subgroup.subgroupOfEquivOfLe hDM
  obtain ⟨P, hTP⟩ := (hD.of_equiv hTD.symm).exists_le_sylow
  have : IsCyclic P := hM P
  have : IsCyclic (D.subgroupOf M) := Subgroup.isCyclic_of_le hTP
  exact isCyclic_of_surjective hTD hTD.surjective

theorem isCyclic_of_map_subtype_le {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {H M : Subgroup G} (hM : ∀ P : Sylow p M, IsCyclic P) {S : Subgroup H} (hS : IsPGroup p S)
    (hle : S.map H.subtype ≤ M) : IsCyclic S := by
  have hSS : S ≃* S.map H.subtype := Subgroup.equivMapOfInjective S H.subtype H.subtype_injective
  have := isCyclic_of_le_of_forall_sylow hM (hS.of_equiv hSS) hle
  exact isCyclic_of_surjective hSS.symm hSS.symm.surjective

theorem card_le_three_of_isCyclic {X : Type*} [Group X] {E : Subgroup X} [IsCyclic E]
    (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 := by
  have hexp : Monoid.exponent E ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hE x x.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

theorem isCyclic_sylow_three_gu (hf : Even f) (h : UnitaryFieldData 2 f K)
    (S : Sylow 3 (Sec4.glPi false 3 (2 ^ f) K)) : IsCyclic S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have hq : ¬ 3 ∣ 2 ^ f + 1 := by
    have := two_pow_even_mod_three hf
    omega
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  refine isCyclic_of_map_subtype_le (M := Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K)
    (fun P => ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow hK
      (by norm_num) (by norm_num) hq P) S.isPGroup' ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
  have hk' : (x : GL (Fin 3) K) ^ 3 ^ k = 1 := by
    have := congrArg (fun y : (S : Subgroup (Sec4.glPi false 3 (2 ^ f) K)) =>
      ((y : Sec4.glPi false 3 (2 ^ f) K) : GL (Fin 3) K)) hk
    simpa using this
  have hmem : (x : GL (Fin 3) K) ∈ Sec4.slPi false 3 (2 ^ f) K :=
    (Sec4.mem_slPi_iff (fun _ => h)).2 ⟨x.2, det_eq_one_of_mem_sylow_three_gu hf h x.2 hk'⟩
  exact hmem

theorem kF82TwoNoE9PGU : KF82TwoNoE9PGU := by
  intro X _ f hf hX E hE
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      rw [pow_zero, one_pow] at hK
      omega
    · exact h0
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  have hpg : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨Q, hEQ⟩ := hpg.exists_le_sylow
  have : IsCyclic Q :=
    KFacts.isCyclic_sylow_of_mulEquiv_projImage e (isCyclic_sylow_three_gu hf h) Q
  have : IsCyclic E := Subgroup.isCyclic_of_le hEQ
  exact card_le_three_of_isCyclic hE.2

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
