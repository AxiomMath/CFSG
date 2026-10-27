module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

inductive GGSixRCKRow
  | I | II | III | IIp | IV | A6 | L32 | U33
  deriving DecidableEq

@[expose] def ggSixRCKLabelRow (lab : LargeEvenLabel) : GGSixRCKRow :=
  match lab.tag with
  | .A => if 2 ≤ lab.n then .I else if lab.rank = 3 then .IIp else if 4 ≤ lab.rank then .II else .L32
  | .twA => if 2 ≤ lab.n then .I else .III
  | .B | .C => if 2 ≤ lab.n then .I else .III
  | .D => if 2 ≤ lab.n then .I else if lab.rank = 3 then .IIp else .II
  | .twD => if 2 ≤ lab.n then .I else if lab.rank = 2 then .I else if lab.rank = 3 then .III else .II
  | .E6 | .E7 | .E8 | .F4 | .twE6 | .triD4 => if 2 ≤ lab.n then .I else .II
  | .G2 | .twB2 | .twF4 => .I
  | .twF4der => .IV
  | .B2der => .A6
  | .G2der => .U33

@[expose] def GGSixRCKJRow (i : GGSixRCKRow) {X : Type} [Group X] (J : Subgroup X) : Prop :=
  LargeEvenMarking ↥J (fun lab _ _ _ _ _ => ggSixRCKLabelRow lab = i)

theorem ggSixRCKLabelRow_field_two {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .III ∨ ggSixRCKLabelRow lab = .IIp) :
    lab.n = 1 ∧ markDeg lab = 1 := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [ggSixRCKLabelRow] at hrow
  all_goals try split_ifs at hrow
  all_goals simp_all [LargeEvenInLambda2, markDeg]
  all_goals omega

theorem ggSixRCKLabelRow_III_parameters {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hrow : ggSixRCKLabelRow lab = .III) :
    markChar lab = 2 ∧ markDeg lab = 1 ∧
      ((markTag lab = .PSp ∧ 3 ≤ markRank lab) ∨
        (markTag lab = .PSU ∧ 4 ≤ markRank lab)) := by
  have hn := (ggSixRCKLabelRow_field_two hlab (Or.inl hrow)).1
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [ggSixRCKLabelRow] at hrow
  all_goals try split_ifs at hrow
  all_goals try { simp_all [LargeEvenInLambda2, markTag, markRank, markChar, markDeg]; done }
  all_goals
    have hlow : 2 ≤ rank := by simpa [LargeEvenInLambda2] using hlab.2.1
    have hnot : rank ≠ 2 := by
      intro h2
      have h := hlab.2.2 h2
      omega
    simp_all [markTag, markRank, markChar, markDeg]
    omega


theorem ggSixRCKJRow_of_marking {X : Type} [Group X] {J : Subgroup X}
    (h : LargeEvenMarking ↥J (fun _ _ _ _ _ _ => True)) : ∃ i, GGSixRCKJRow i J := by
  obtain ⟨hc, lab, hlab, hraw⟩ := h
  refine ⟨ggSixRCKLabelRow lab, hc, lab, hlab, ?_⟩
  exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw

end CFSG.StandardType
