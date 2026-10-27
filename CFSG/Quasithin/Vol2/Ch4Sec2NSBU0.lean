module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBC41
public import CFSG.Quasithin.Background.C48PfA

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

theorem c41Case4_of_conclusion {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G}
    {m k : ℕ} (hd : NoSumBigData G T M L Mm I H K m k)
    (h41 : C41Conclusion H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H))
      ⁅reducedAggregate (L ⊔ T), L⁆ K) :
    C41Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K := by
  obtain ⟨hy, -, hc, hm, -, -, hPSLLH, -⟩ := hd
  have hcc : conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) :=
    conjClosure_eq_self hc.LH_normal
  have hLHcard : (Nat.card (ModO2 (perfectCore (L ⊓ H))) = 168 ∧ m = 3) ∨
      (Nat.card (ModO2 (perfectCore (L ⊓ H))) = 20160 ∧ m = 4) := by
    rcases hm with rfl | rfl
    · exact Or.inl ⟨card_psl3_nsb41 hPSLLH, rfl⟩
    · exact Or.inr ⟨F420.card_of_l42 hPSLLH, rfl⟩
  rcases h41.2.2.2 with h1 | h2 | h3 | h4
  · exfalso
    obtain ⟨n, hn, hAlt, -⟩ := h1
    rw [hcc] at hAlt
    obtain ⟨-, α, hα, hker, -⟩ := hAlt
    have hcardA : Nat.card (ModO2 (perfectCore (L ⊓ H))) = Nat.card (alternatingGroup (Fin n)) := by
      have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
      exact Nat.card_congr e.toEquiv
    rcases hn with rfl | rfl
    · rw [card_alt5_nsb41] at hcardA
      rcases hLHcard with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · rw [C489.card_alt6] at hcardA
      rcases hLHcard with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpsl⟩ := h2
    have hpsl' := isPSL_modO2_of_eq_nsb41 hcc hpsl
    have hcard := C489.card_of_isPSL_two_two hpsl'
    rcases hLHcard with ⟨h, -⟩ | ⟨h, -⟩
    · exact (psl22_ne_nsb41 2).1 (hcard.symm.trans h)
    · exact (psl22_ne_nsb41 2).2 (hcard.symm.trans h)
  · exfalso
    obtain ⟨n, _, _, _, -, -, -, -, -, -, hpsl, -⟩ := h3
    have hpsl' := isPSL_modO2_of_eq_nsb41 hcc hpsl
    have hcard := C489.card_of_isPSL_two_two hpsl'
    rcases hLHcard with ⟨h, -⟩ | ⟨h, -⟩
    · exact (psl22_ne_nsb41 n).1 (hcard.symm.trans h)
    · exact (psl22_ne_nsb41 n).2 (hcard.symm.trans h)
  · exact h4

theorem uZeroNeBot_of (hN31 : NotC31) (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) : UZeroNeBot := by
  intro G _ _ T M L Mm I H K m k hd
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  rcases hc.described with ⟨hcomp, h31'⟩ | ⟨hKc, hCT, hqs, hKM, h41'⟩
  · exact (hN31 G T M L Mm I H K m k hd hcomp h31').elim
  · have h4 := c41Case4_of_conclusion hd h41'
    have hV := (C48Pf.le_commutator (h22 G) (h27 G) hc.hypC28 hKc hCT hqs hKM h41' h4).1
    intro h0
    exact hc.hypC28.V_ne (le_bot_iff.mp (h0 ▸ hV))

end CFSG.Quasithin.H13.Ch4.NSB
