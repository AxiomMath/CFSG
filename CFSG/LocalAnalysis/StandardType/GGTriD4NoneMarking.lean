module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem largeEvenMarking_and_labelAll_simple_imp {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {S : LargeEvenLabel → Prop} {P' : LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard P'))
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ (S lab → P' R I F) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  by_cases hS : S lab
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (hall lab hlab hS _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
    exact ⟨hs, hna, θ, hθ, fun _ => hP' hs hna⟩
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, hθ, fun h => absurd h hS⟩

theorem largeEvenLabelAll_triD4_known (h : GGTriD4KnownInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .triD4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      GGTriD4InnDiag R I ∧ GGTriD4Schur R ∧ GGTriD4AutRank R ∧ GGTriD4Components R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ I _ =>
      GGTriD4InnDiag R I ∧ GGTriD4Schur R ∧ GGTriD4AutRank R ∧ GGTriD4Components R)
    (fun K _ _ hK hs _ => ⟨h.1 n hn K hK hs, h.2.1 n hn K hK hs, h.2.2.1 n hn K hK hs,
      h.2.2.2 n hn K hK hs⟩) hQ

theorem three_dvd_of_split_twE6 {lab : LargeEvenLabel} (ht : lab.tag = .twE6)
    (hs : LargeEvenSplit 3 lab) : 3 ∣ 2 ^ lab.n + 1 := by
  rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨hn, -⟩
  · rw [ht] at h
    exact absurd h (by simp [LargeEvenUntwisted])
  · exact h
  · rw [ht] at h
    rcases h with h | h <;> exact absurd h (by simp)
  · rw [hn]
    norm_num

theorem largeEvenLabelAll_twE6_rank (h : GGTwE6LocalRankInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6) (hs : LargeEvenSplit 3 lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ _ _ => GGTwE6LocalRank R) := by
  have h3 := three_dvd_of_split_twE6 ht hs
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht h3
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ _ _ => GGTwE6LocalRank R)
    (fun K _ _ hK hs' _ => h n hn h3 K hK hs') hQ

theorem largeEvenMarking_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {S : LargeEvenLabel → Prop} (h : LargeEvenMarking Y fun lab _ _ _ _ _ => S lab) :
    LargeEvenMarking X fun lab _ _ _ _ _ => S lab := by
  obtain ⟨hY, lab, hlab, hraw⟩ := h
  have hperf : Group.IsPerfect Y := ⟨hY⟩
  have hX : commutator X = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective).commutator_eq_top
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna,
    (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)).trans
      θ, hθ⟩

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  have h1 := Subgroup.map_center_eq e
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ (f := (e : X →* Y)) e.injective).mp h1

end CFSG.StandardType
