module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

@[expose] def NotC31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k → CFSG.Open.IsComponentOf K H →
      C31Conclusion H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K →
        False

@[expose] def C41Case4Of : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k →
      (K ∈ cComp H ∧ CharTwo K ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ K ≤ H ⊓ M ∧
        C41Conclusion H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) →
      H ≤ Subgroup.normalizer (K : Set G) ∧ pCoreOf 2 K ≠ ⊥ ∧
        ∃ n : ℕ, ((n = 4 ∧ m = 3) ∨ (n = 5 ∧ m = 3) ∨ (n = 5 ∧ m = 4)) ∧
          IsPSL n 2 1 (ModO2 K)

theorem lemma32_of (h31 : NotC31) (h41 : C41Case4Of) : Lemma32 := by
  intro G _ _ T M L Mm I H K m k hd
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  rcases hc.described with ⟨hcomp, h31'⟩ | ⟨hKc, hCT, hqs, hKM, h41'⟩
  · exact (h31 G T M L Mm I H K m k hd hcomp h31').elim
  · exact h41 G T M L Mm I H K m k hd ⟨hKc, hCT, hqs, hKM, h41'⟩

end CFSG.Quasithin.H13.Ch4.NSB
