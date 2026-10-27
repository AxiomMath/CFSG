module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.Quasithin.Background.BlueprintB2Thompson

public section

namespace CFSG.Quasithin.SteinbergBK

open Subgroup CFSG CFSG.SectionRank.Ccomm

variable {H : Type*} [Group H] [Finite H]

theorem card_GL_two_dvd_of_le_four {d : ℕ} (hd : d ≤ 4) :
    Nat.card (GL (Fin d) (ZMod 2)) ∣ 2 ^ 6 * 315 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_GL_zmod]
  interval_cases d <;> simp [Fin.prod_univ_succ]

theorem characteristic_two_core_frattini_action_and_small_ranks (hH : IsCharacteristicP 2 H) :
    ((autQuotient (frattini (pCore 2 H))).comp (MulAut.conjNormal (H := pCore 2 H))).ker =
        pCore 2 H ∧
      (∃ ι : H ⧸ pCore 2 H →* MulAut (pCore 2 H ⧸ frattini (pCore 2 H)), Function.Injective ι ∧
        ∀ h : H, ι h = (autQuotient (frattini (pCore 2 H))).comp MulAut.conjNormal h) ∧
      ∃ d : ℕ, Nat.card (pCore 2 H ⧸ frattini (pCore 2 H)) = 2 ^ d ∧
        Nonempty (Additive (pCore 2 H ⧸ frattini (pCore 2 H)) ≃+ (Fin d → ZMod 2)) ∧
        Nonempty (MulAut (pCore 2 H ⧸ frattini (pCore 2 H)) ≃* GL (Fin d) (ZMod 2)) ∧
        (d ≤ 4 → ordCompl[2] (Nat.card H) ∣ 315 ∧ pRank 3 H ≤ 2 ∧ pRank 5 H ≤ 1 ∧
          pRank 7 H ≤ 1 ∧ (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → p ≠ 5 → p ≠ 7 → pRank p H = 0) ∧
          IsStronglyQuasithin H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup H := pCore 2 H with hQ
  have hQ2 : IsPGroup 2 Q := pCore_isPGroup
  set ρ : H →* MulAut (Q ⧸ frattini Q) :=
    (autQuotient (frattini Q)).comp (MulAut.conjNormal (H := Q)) with hρ
  obtain ⟨-, hcomm, hpow, -, d, hd, hdeq⟩ := GroupTheory.frattini_elementary_quotient hQ2
  have hQK : Q ≤ ρ.ker := by
    intro q hq
    rw [hρ, ← MonoidHom.comap_ker, mem_comap, mem_ker_autQuotient]
    intro x
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hx : (MulAut.conjNormal q x : Q) = ⟨q, hq⟩ * x * (⟨q, hq⟩ : Q)⁻¹ :=
      Subtype.ext (MulAut.conjNormal_apply q x)
    rw [hx, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      hcomm.is_comm.comm (((⟨q, hq⟩ : Q) : Q ⧸ frattini Q)) (x : Q ⧸ frattini Q)]
    group
  have hKQ : ρ.ker ≤ Q := by
    set K := ρ.ker with hK
    set c : K →* MulAut Q := (MulAut.conjNormal (H := Q)).comp K.subtype with hc
    have hA : IsPGroup 2 (autQuotient (frattini Q)).ker := isPGroup_ker_autQuotient_frattini hQ2
    have hcker : IsPGroup 2 c.ker := by
      intro g
      have hgC : ((g : K) : H) ∈ centralizer (Q : Set H) := by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := congrArg (fun σ : MulAut Q => ((σ ⟨x, hx⟩ : Q) : H)) g.2
        simp only [hc, MonoidHom.comp_apply, MulAut.one_apply, coe_subtype,
          MulAut.conjNormal_apply] at h1
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      obtain ⟨n, hn⟩ := hQ2 ⟨_, hH hgC⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hn
    have hcomap : (autQuotient (frattini Q)).ker.comap c = ⊤ := by
      rw [eq_top_iff]
      intro k _
      rw [mem_comap, MonoidHom.mem_ker]
      have h1 : ρ k = 1 := k.2
      exact h1
    have hK2 : IsPGroup 2 K := by
      have h := hA.comap_of_ker_isPGroup c hcker
      rw [hcomap] at h
      exact h.of_equiv Subgroup.topEquiv
    exact le_sSup ⟨ρ.normal_ker, hK2⟩
  have hker : ρ.ker = Q := le_antisymm hKQ hQK
  set ι : H ⧸ Q →* MulAut (Q ⧸ frattini Q) :=
    (QuotientGroup.kerLift ρ).comp (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom
    with hι
  have hιinj : Function.Injective ι :=
    (QuotientGroup.kerLift_injective ρ).comp (QuotientGroup.quotientMulEquivOfEq _).injective
  refine ⟨hker, ⟨ι, hιinj, fun h => rfl⟩, d, hd, hdeq, ?_, fun hd4 => ?_⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 2) (fun a b => hcomm.is_comm.comm a b)
      hpow hd
    exact ⟨elemAutEquivGL e⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 2) (fun a b => hcomm.is_comm.comm a b)
    hpow hd
  have hAut : Nat.card (MulAut (Q ⧸ frattini Q)) ∣ 2 ^ 6 * 315 := by
    rw [card_mulAut_eq_card_GL e]
    exact card_GL_two_dvd_of_le_four hd4
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQ2
  have hcardH : Nat.card H ∣ 315 * 2 ^ (6 + a) := by
    rw [card_eq_card_quotient_mul_card_subgroup Q, ha,
      show 315 * 2 ^ (6 + a) = 2 ^ 6 * 315 * 2 ^ a by rw [pow_add]; ring]
    exact Nat.mul_dvd_mul_right ((card_dvd_of_injective ι hιinj).trans hAut) _
  have hodd : ordCompl[2] (Nat.card H) ∣ 315 := by
    have hcop : Nat.Coprime (ordCompl[2] (Nat.card H)) (2 ^ (6 + a)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_ordCompl Nat.prime_two Nat.card_pos.ne').symm
    exact hcop.dvd_of_dvd_mul_right ((Nat.ordCompl_dvd _ 2).trans hcardH)
  have hpr : ∀ p : ℕ, p.Prime → p ≠ 2 → p ^ pRank p H ∣ 315 := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨A, -, hA⟩ := Quasithin.BlueprintB2.exists_card_eq_pow_pRank H p
    have h1 : p ^ pRank p H ∣ Nat.card H := hA ▸ card_subgroup_dvd_card A
    have hcop : Nat.Coprime (p ^ pRank p H) (ordProj[2] (Nat.card H)) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    rw [← Nat.ordProj_mul_ordCompl_eq_self (Nat.card H) 2] at h1
    exact (hcop.dvd_of_dvd_mul_left h1).trans hodd
  have h3 : pRank 3 H ≤ 2 := by
    by_contra h
    have h' := (Nat.pow_dvd_pow 3 (show 3 ≤ pRank 3 H by omega)).trans
      (hpr 3 Nat.prime_three (by norm_num))
    norm_num at h'
  have h5 : pRank 5 H ≤ 1 := by
    by_contra h
    have h' := (Nat.pow_dvd_pow 5 (show 2 ≤ pRank 5 H by omega)).trans
      (hpr 5 (by norm_num) (by norm_num))
    norm_num at h'
  have h7 : pRank 7 H ≤ 1 := by
    by_contra h
    have h' := (Nat.pow_dvd_pow 7 (show 2 ≤ pRank 7 H by omega)).trans
      (hpr 7 (by norm_num) (by norm_num))
    norm_num at h'
  have hother : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → p ≠ 5 → p ≠ 7 → pRank p H = 0 := by
    intro p hp hp2 hp3 hp5 hp7
    by_contra h
    have hdvd : p ∣ 3 * (3 * (5 * 7)) := (dvd_pow_self p h).trans (hpr p hp hp2)
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h' | h'
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
    rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
    rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h')
    · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h')
  refine ⟨hodd, h3, h5, h7, hother, fun p hp hp2 => ?_⟩
  by_cases hp3 : p = 3
  · subst hp3; exact h3
  by_cases hp5 : p = 5
  · subst hp5; omega
  by_cases hp7 : p = 7
  · subst hp7; omega
  rw [hother p hp hp2 hp3 hp5 hp7]
  omega

end CFSG.Quasithin.SteinbergBK
