module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial (pointwiseFixingAut)
open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism)

theorem card_mulAut_dvd_pow_mul_card_GL {q : ℕ} [Fact q.Prime] {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup q P) {d : ℕ} (hd : Nat.card (P ⧸ frattini P) = q ^ d) :
    ∃ k : ℕ, Nat.card (MulAut P) ∣ q ^ k * Nat.card (GL (Fin d) (ZMod q)) := by
  have : Finite (MulAut P) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut P))
  obtain ⟨-, hcomm, hpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hP
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (fun a b => hcomm.is_comm.comm a b) hpow hd
  set ρ := quotientAutomorphism (frattini P) with hρ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker
  refine ⟨k, ?_⟩
  have h1 : Nat.card (MulAut P) = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  rw [h1, hk, ← CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e]
  exact mul_dvd_mul_left _ (Subgroup.card_subgroup_dvd_card _)

theorem pow_factorization_card_mulAut_dvd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup q P) {d : ℕ}
    (hd : Nat.card (P ⧸ frattini P) = q ^ d) :
    p ^ (Nat.card (MulAut P)).factorization p ∣
      p ^ (Nat.card (GL (Fin d) (ZMod q))).factorization p := by
  have : Finite (MulAut P) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut P))
  obtain ⟨k, hk⟩ := card_mulAut_dvd_pow_mul_card_GL hP hd
  have hGL : Nat.card (GL (Fin d) (ZMod q)) ≠ 0 := Nat.card_pos.ne'
  have hq0 : q ^ k ≠ 0 := pow_ne_zero _ (Fact.out : q.Prime).ne_zero
  have hA0 : Nat.card (MulAut P) ≠ 0 := Nat.card_pos.ne'
  refine pow_dvd_pow p ?_
  have h := (Nat.factorization_le_iff_dvd hA0 (mul_ne_zero hq0 hGL)).mpr hk p
  rw [Nat.factorization_mul hq0 hGL, Finsupp.add_apply, Nat.factorization_pow,
    (Fact.out : q.Prime).factorization] at h
  simpa [hpq] using h

end CFSG.RankThree.GroupTheory.SteinbergBK
