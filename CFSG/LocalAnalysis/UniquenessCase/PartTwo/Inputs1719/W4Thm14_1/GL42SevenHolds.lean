module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.GL42SevenCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.GL42SevenL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.GL42SevenAlt8
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6EvenSymplecticCore
import CFSG.Sporadic.Schreier.RuElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin

theorem kGL42Seven_holds : KGL42Seven := by
  intro U _ _ hU2 hU16 M hO2 hB h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨g, hgM⟩, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 7 h7
  have hg7 : orderOf g = 7 := by rwa [Subgroup.orderOf_mk] at hg
  obtain ⟨F, hF⟩ := CFSG.GH72.exists_subgroup_eq_fixedBy g
  obtain ⟨V, hV8, hgV⟩ := GL42Seven.exists_invariant_card_eight hU16 hg7
  have hidx : V.index = 2 := by
    have := V.card_mul_index
    rw [hV8, hU16] at this
    omega
  have hMV := GL42Seven.not_stableUnder_of_index_eq_two hU2 hO2 hB hidx
  by_cases hMF : StableUnder M F
  · right; right
    obtain ⟨e⟩ := GL42Seven.nonempty_mulEquiv_GL32 hU2 hU16 hO2 hgM hg7 hF hMF hV8 hgV hMV
    refine ⟨CFSG.LocalAnalysis.ComponentInitial.SteinbergBI.lieModel_PSL_three_two_of_mulEquiv e,
      GL42Seven.fixV_ne_bot_of_stableUnder_of_card hMF ?_⟩
    rw [← GL42Seven.card_fixedBy_eq_two hU16 hg7, ← hF]
    rfl
  · have h15 := GL42Seven.fifteen_dvd_card hU16 hgM hg7 hF hV8 hgV hMF hMV
    have h5 : 5 ∣ Nat.card M := dvd_trans (by norm_num) h15
    have h35 : 35 ∣ Nat.card M :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 7) h5 h7
    obtain ⟨φU⟩ := CFSG.Sporadic.RuSchreier.ru_nonempty_mulEquiv_of_elementary (p := 2)
      (W := U) mul_comm hU2 (n := 4) (by rw [hU16]; norm_num)
    let e : MulAut U ≃* GL (Fin 4) (ZMod 2) :=
      (MulAut.congr φU).trans (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL 4)
    let φ : MulAut U →* Equiv.Perm (Fin 8) :=
      (alternatingGroup (Fin 8)).subtype.comp
        (CFSG.Quasithin.H.L4.alpha8.symm.toMonoidHom.comp e.toMonoidHom)
    have hφ : Function.Injective φ :=
      Subtype.val_injective.comp (CFSG.Quasithin.H.L4.alpha8.symm.injective.comp e.injective)
    have hH : M.map φ ≤ alternatingGroup (Fin 8) := by
      rintro _ ⟨x, -, rfl⟩
      exact (CFSG.Quasithin.H.L4.alpha8.symm (e x)).2
    let eMH : ↥M ≃* ↥(M.map φ) := M.equivMapOfInjective φ hφ
    have hcard : Nat.card (M.map φ) = Nat.card M := (Nat.card_congr eMH.toEquiv).symm
    rcases GL42Seven.nonempty_mulEquiv_alt_of_thirtyFive_dvd hH (hcard ▸ h35) with h8 | h7'
    · obtain ⟨e8⟩ := h8
      exact Or.inr (Or.inl (⟨eMH.trans e8⟩ : Nonempty (↥M ≃* alternatingGroup (Fin 8))))
    · obtain ⟨e7⟩ := h7'
      exact Or.inl (⟨eMH.trans e7⟩ : Nonempty (↥M ≃* alternatingGroup (Fin 7)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
