module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KSp6G
public import CFSG.RankThree.PartTwo.Sec21.Hering214KSporRest
import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.Schreier.PairJ3Faithful

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def J3SylowDichotomy : Prop :=
  ∃ P₀ : Sylow 3 NativeSporadic.J3, ∀ x y : NativeSporadic.J3, x ∈ (P₀ : Subgroup _) →
    y ∈ (P₀ : Subgroup _) → x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ≠ 1 →
    y ∉ Subgroup.zpowers x →
    FourDatum x y ∨ ∀ τ : MulAut NativeSporadic.J3, τ * τ = 1 → τ ≠ 1 →
      ¬ (τ * MulAut.conj x = MulAut.conj x * τ ∧ τ * MulAut.conj y = MulAut.conj y * τ)

theorem exists_conj_of_pow_three_j3
    {M : Type} [Group M] (e : M ≃* NativeSporadic.J3)
    (α : MulAut M) (hα : α ^ 3 = 1) : ∃ y : M, α = MulAut.conj y := by
  have hfin : Finite NativeSporadic.J3 := (CFSG.Sporadic.J3.fam_j3_simplicity).1
  have : Finite M := Finite.of_equiv _ e.symm.toEquiv
  have hOut : Nat.card (Outer M) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (e.trans CFSG.Sporadic.Schreier.j3PermEquiv)).toEquiv]
    exact CFSG.Sporadic.SmallOddCore.j3_outer_card_le
  have h3 : (QuotientGroup.mk α : Outer M) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hord : orderOf (QuotientGroup.mk α : Outer M) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hord2 : orderOf (QuotientGroup.mk α : Outer M) ∣ Nat.card (Outer M) :=
    orderOf_dvd_natCard _
  have hle := (Nat.le_of_dvd Nat.card_pos hord2).trans hOut
  have h1 : orderOf (QuotientGroup.mk α : Outer M) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact h
    · omega
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  obtain ⟨y, hy⟩ := h1
  exact ⟨y, hy.symm⟩

theorem eInvFourFact_j3_of_dichotomy
    (h : J3SylowDichotomy) : EInvFourFact NativeSporadic.J3 := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.J3.fam_j3_simplicity
  haveI := hfin
  have hZ : Subgroup.center NativeSporadic.J3 = ⊥ :=
    center_eq_bot_of_simple_of_not_prime hsimple (by rw [CFSG.Sporadic.J3.card_J3]; norm_num)
  obtain ⟨P₀, hP₀⟩ := h
  exact @eInvFourFact_of_sylow_dichotomy_aut NativeSporadic.J3 Units.instGroup hfin hZ
    (fun α hα => @exists_conj_of_pow_three_j3 NativeSporadic.J3 Units.instGroup
      (@MulEquiv.refl NativeSporadic.J3 _) α hα) P₀ hP₀

theorem item214BarJ3Simple_of_dichotomy
    (h : J3SylowDichotomy) : Item214BarJ3Simple := by
  intro X _ _ ⟨e⟩ Ē Ū hd
  exact (@EInvFourFact.of_mulEquiv X NativeSporadic.J3 _ Units.instGroup e
    (eInvFourFact_j3_of_dichotomy h)) Ē Ū hd

end CFSG.RankThree.PartTwo.Sec21.Hering214
