module

public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofExcl
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU33Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Item434CharThree CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits

@[expose] def KS176GTwoChev : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (∃ p f : ℕ, Blueprint.ChevalleyExceptionalModel X .G2 p f) →
    ∀ Z : Subgroup X, Nat.card Z = 3 →
    (∀ g : X, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) →
      Z.map (MulAut.conj g).toMonoidHom = Z) →
    Proof176Steps.HasCommOfZ Z

namespace Proof17Res5

@[expose] def IsExtraThree (H : Type*) [Group H] : Prop :=
  commutator H = Subgroup.center H ∧ Nat.card (Subgroup.center H) = 3 ∧ ∀ x : H, x ^ 3 = 1

theorem IsExtraThree.of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (h : IsExtraThree H) : IsExtraThree K := by
  obtain ⟨hc, hz, hx⟩ := h
  have hcen : (Subgroup.center H).map (e : H →* K) = Subgroup.center K := Subgroup.map_center_eq e
  have hcom : (commutator H).map (e : H →* K) = commutator K := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  refine ⟨?_, ?_, fun x => ?_⟩
  · rw [← hcen, ← hcom, hc]
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hz]
  · obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_pow, hx, map_one]

theorem isExtraThree_of_card {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 27)
    (hnab : ∃ x y : H, x * y ≠ y * x) (hexp : ∀ x : H, x ^ 3 = 1) : IsExtraThree H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, hxy⟩ := hnab
  have hc27 : Nat.card H = 3 ^ 3 := by rw [hcard]; norm_num
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hc27 (by norm_num)
  have hZtop : Subgroup.center H ≠ ⊤ := fun h =>
    hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
  rw [hk, hc27] at hquot
  have hk3 : k < 3 := by
    have hdvd : 3 ^ k ∣ 3 ^ 3 := ⟨_, hquot.trans (mul_comm _ _)⟩
    have hle : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hZtop
      apply Subgroup.eq_top_of_card_eq
      rw [hk, h, hc27]
  have hk2 : k ≠ 2 := by
    intro h2
    rw [h2] at hquot
    have hq : Nat.card (H ⧸ Subgroup.center H) = 3 := by omega
    have : IsCyclic (H ⧸ Subgroup.center H) := isCyclic_of_prime_card hq
    have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center H)) (by rw [QuotientGroup.ker_mk'])
    exact hxy (hcomm.is_comm.comm x y)
  have hk1 : k = 1 := by omega
  have hZ3 : Nat.card (Subgroup.center H) = 3 := by rw [hk, hk1, pow_one]
  rw [hk1, pow_one] at hquot
  have hq9 : Nat.card (H ⧸ Subgroup.center H) = 3 ^ 2 := by omega
  have hab := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hq9).is_comm.comm
  have hle : commutator H ≤ Subgroup.center H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hab _ _
  have hne : commutator H ≠ ⊥ := fun h =>
    hZtop ((commutator_eq_bot_iff_center_eq_top H).mp h)
  refine ⟨le_antisymm hle ?_, hZ3, hexp⟩
  have hdvd : Nat.card (commutator H) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le hle
  have h3 : Nat.card (commutator H) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne
    · exact h
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hZ3])).ge

section U33

abbrev F9 : Type := GaloisField 3 (2 * 1)

theorem card_F9 : Nat.card F9 = (3 ^ 1) ^ 2 := card_galois_two_mul one_ne_zero

theorem isExtraThree_heisU :
    IsExtraThree (heisU (unitaryInvolution_involutive card_F9)) := by
  have hcard : Nat.card (heisU (unitaryInvolution_involutive card_F9)) = 27 := by
    rw [card_heisU card_F9]
    norm_num
  refine isExtraThree_of_card hcard ?_ fun x => Subtype.ext ?_
  · by_contra hc
    push Not at hc
    obtain ⟨a₀, ha₀, hle⟩ := exists_le_lineU (P := heisU (unitaryInvolution_involutive card_F9))
      le_rfl fun x hx y hy => congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_lineU_le card_F9 ha₀
    rw [hcard] at h1
    norm_num at h2
    omega
  · rw [Subgroup.coe_pow, pow_three_eq_one_of_mem_heisU x.2, Subgroup.coe_one]

theorem isExtraThree_sylow_of_projSU {X : Type} [Group X] [Finite X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSU 3 3 1) (P : Sylow 3 X) :
    IsExtraThree (P : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := e.trans (suEquivProjSU (e := 1) one_ne_zero).symm with hψ
  set U := heisU (unitaryInvolution_involutive card_F9) with hU
  set Q : Subgroup X := U.map ψ.symm.toMonoidHom with hQ
  have hQcard : Nat.card Q = 3 ^ (Nat.card X).factorization 3 := by
    rw [hQ, Subgroup.card_map_of_injective ψ.symm.injective, hU, card_heisU card_F9,
      Nat.card_congr ψ.toEquiv, factorization_card_SU_three one_ne_zero]
    norm_num
  set Q' : Sylow 3 X := Sylow.ofCard Q hQcard with hQ'
  have e1 : (P : Subgroup X) ≃* (Q' : Subgroup X) := Sylow.equiv P Q'
  have e2 : (Q' : Subgroup X) ≃* U :=
    (U.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).symm
  exact isExtraThree_heisU.of_mulEquiv (e1.trans e2).symm

end U33

end Proof17Res5

theorem ks176GTwo_of_chev (h : KS176GTwoChev) : KS176GTwo := by
  intro X _ _ hX Z hZ3 hwc
  rcases hX with hC | he
  · exact h X hC Z hZ3 hwc
  · obtain ⟨e⟩ := he
    refine Proof176Steps.hasCommOfZ_of_sylow (fun P => ?_) hZ3 hwc
    obtain ⟨hc, hz, hx⟩ := Proof17Res5.isExtraThree_sylow_of_projSU e P
    exact ⟨hc, hz, fun x hxP => congrArg Subtype.val (hx ⟨x, hxP⟩)⟩

end CFSG.RankThree.PartTwo.Sec17
