module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGStdPosC24Signed
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp

theorem largeEvenLabelAll_reflGenW_spNonsplit
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGSpNonsplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  dsimp only at htag hpn
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  rcases htag with rfl | rfl <;>
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have : NeZero l := ⟨by omega⟩
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have : Finite (LargeEvenSpGroup K l) := Subtype.finite
    have : Finite (LargeEvenProj (LargeEvenSpGroup K l)) :=
      Finite.of_equiv _ (spProjEquivSp (K := K) (m := l)).symm.toEquiv
    have h2 : 2 ∣ Nat.card (LargeEvenProj (LargeEvenSpGroup K l)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let i₀ : Fin l := ⟨0, by omega⟩
      rcases (spRootGroup_isPGroup (K := K) i₀).card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) (spRootGroup_ne_bot i₀)
      · exact h1.trans (Subgroup.card_subgroup_dvd_card _)
    obtain ⟨hT, hcp⟩ := ggSpNonsplitTorusInput_holds K l p hl2 hp hpK
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 0, TypeA.ggTorusLift_zero h2,
      ggTorusReflGenW_of_signedEltSC hp hp2 center_spProj_eq_bot
        (fun φ hφ _ => sp_I_subset_inn hφ) hcp hT⟩

end CFSG.StandardType

end
