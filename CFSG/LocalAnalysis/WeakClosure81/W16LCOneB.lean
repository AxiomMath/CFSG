module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeKerAbs
public import CFSG.Open.FusionDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_16

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open
open scoped commutatorElement

theorem w16l_one_shape' {L : Type} [Group L] [Finite L] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) L W) {t : L}
    (ht2 : t * t = 1)
    (hE : Subgroup.zpowers t ⊔ fusionOddCore L = ⊤) (hne : fusionOddCore L ≠ ⊥)
    (hgen : fusionOddCore L ≤ ⁅fusionOddCore L, Subgroup.zpowers t⁆)
    (hexp : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∀ x ∈ fusionOddCore L, x ^ p = 1) ∧
      ∀ x ∈ fusionOddCore L, ∀ y ∈ fusionOddCore L, ∀ z ∈ fusionOddCore L, ⁅⁅x, y⁆, z⁆ = 1)
    (htr : traceSpace ρ t ≠ ⊥)
    (hTI : ∀ y ∈ fusionOddCore L,
      traceSpace ρ t ⊓ (traceSpace ρ t).map (ρ y) ≠ ⊥ → y * t = t * y) :
    ∃ p : ℕ, p.Prime ∧ (Nat.card (fusionOddCore L) = p ∨
      (CFSG.IsExtraspecial p ↥(fusionOddCore L) ∧ Nat.card (fusionOddCore L) = p ^ 3)) := by
  obtain ⟨p, hp, hp2, hexpE, hclass⟩ := hexp
  have hnorm : t ∈ Subgroup.normalizer (fusionOddCore L : Set L) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top t
  have h : PInvol p (fusionOddCore L) t :=
    ⟨hp, hp2, hexpE, hclass, ht2, hnorm, hgen⟩
  have hsup : fusionOddCore L ⊔ Subgroup.zpowers t = ⊤ := by
    rw [sup_comm]
    exact hE
  have hmain := PInvol.card_main_of_rep ρ h hsup hne htr hTI
  refine ⟨p, hp, ?_⟩
  rcases hmain with h1 | ⟨h3, x, hx, y, hy, hxy⟩
  · exact Or.inl h1
  · refine Or.inr ⟨?_, h3⟩
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact (IsPGroup p ↥(fusionOddCore L)) := ⟨IsPGroup.of_card h3⟩
    have hpow : ∀ g : ↥(fusionOddCore L), g ^ p = 1 :=
      fun g => Subtype.ext (by simpa using hexpE g.1 g.2)
    have hexpK : Monoid.exponent ↥(fusionOddCore L) = p := by
      rcases (Nat.dvd_prime hp).1
          (Monoid.exponent_dvd_of_forall_pow_eq_one hpow) with h | h
      · exfalso
        have hone : ∀ g : ↥(fusionOddCore L), g = 1 :=
          fun g => by simpa [h] using Monoid.pow_exponent_eq_one g
        have hsub : Subsingleton ↥(fusionOddCore L) :=
          ⟨fun a b => (hone a).trans (hone b).symm⟩
        have hc : Nat.card ↥(fusionOddCore L) = 1 :=
          Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
        rw [h3] at hc
        exact (Nat.one_lt_pow (by norm_num) hp.one_lt).ne' hc
      · exact h
    have hnc : ¬ IsMulCommutative ↥(fusionOddCore L) := by
      intro hcomm
      apply hxy
      rw [commutatorElement_eq_one_iff_mul_comm]
      simpa using congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    exact CFSG.isExtraspecial_of_noncommutative_card_p3_exponent_p h3 hexpK hnc

end CFSG.LocalAnalysis.WeakClosure81

end
