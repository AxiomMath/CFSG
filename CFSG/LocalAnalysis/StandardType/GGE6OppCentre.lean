module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetRow
public import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcGlue

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem centerPrime_three_of_rowFact {R : Type} [Group R] {I : Set (MulAut R)}
    (hR : GGR4RowFact R I) : GGCenterPrime 3 R := by
  intro L' _ _ ψ hψ hker hperf h3dvd
  obtain ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' (Subgroup.center L') _ _ 3
    ⟨Nat.prime_three⟩ h3dvd
  have hcop := hR.2 L' ψ hψ hker hperf (x : L') x.2
  rw [Subgroup.orderOf_coe, hx] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop (dvd_refl 3)

private theorem not_three_dvd_card_center_of_rowFact {Y : Type} [Group Y] [Finite Y]
    [Group.IsPerfect Y] {lab : LargeEvenLabel}
    (hAll : LargeEvenLabelAll lab fun R _ I _ => GGR4RowFact R I)
    (hlab : GGHasLabel lab (Y ⧸ Subgroup.center Y)) :
    ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  have hcent : LargeEvenLabelAll lab fun R _ I _ => GGCenterPrime 3 R :=
    hAll.mono fun R _ I _ hR => centerPrime_three_of_rowFact hR
  obtain ⟨R, _, I, F, hQe, hcentR⟩ := largeEvenRawDatum_exists (hcent _ hlab)
  obtain ⟨e⟩ := hQe
  have hcomm : commutator Y = ⊤ := Group.IsPerfect.commutator_eq_top
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (kgLang_coprime_of_centerPrime Nat.prime_three hcentR e hcomm).symm

theorem not_three_dvd_card_center_of_e6Opp
    {H : Type} [Group H] [Finite H]
    [Group.IsPerfect H] {f : ℕ} (hf : 1 ≤ f)
    (hH : (GGHasLabel ⟨.E6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f + 1) ∨
      (GGHasLabel ⟨.twE6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f - 1)) :
    ¬ 3 ∣ Nat.card (Subgroup.center H) := by
  rcases hH with ⟨hE6, h3⟩ | ⟨htwE6, h3⟩
  · exact not_three_dvd_card_center_of_rowFact (ggR4RowFact_E6 (f := f) h3) hE6
  · exact not_three_dvd_card_center_of_rowFact (ggR4RowFact_twE6 (f := f) hf h3) htwE6

end CFSG.StandardType

end
