module

import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch11SecBL2OPSL
public import CFSG.Quasithin.Vol2.Ch11SecBNPCase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem card_le_of_surjective {K Y X : Type} [Group K] [Group Y] [Group X] [Finite Y]
    [Finite X] [Nontrivial X] [IsSimpleGroup Y] [Group.IsPerfect K]
    (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup K} [N.Normal] (hN : IsPGroup 2 N)
    (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (ψ : K →* Y) (hψ : Function.Surjective ψ)
    (f : K →* X) (hf : Function.Surjective f) : Nat.card Y ≤ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup X := N.map f with hM
  have hMn : M.Normal := Subgroup.Normal.map inferInstance f hf
  have hM2 : IsPGroup 2 M := hN.map f
  have hXM : M ≠ ⊤ := by
    intro htop
    have hP : IsPGroup 2 X := by
      intro x
      have hx : x ∈ M := by rw [htop]; trivial
      obtain ⟨e, he⟩ := hM2 ⟨x, hx⟩
      exact ⟨e, by simpa using congrArg Subtype.val he⟩
    have : Group.IsPerfect X := Group.IsPerfect.ofSurjective hf
    exact Group.IsPerfect.not_isNilpotent X hP.isNilpotent
  have : Nontrivial (X ⧸ M) := QuotientGroup.nontrivial_iff.mpr hXM
  obtain ⟨M', hM'n, hMM', hM'top, hmax⟩ : ∃ M' : Subgroup X, M'.Normal ∧ M ≤ M' ∧ M' ≠ ⊤ ∧
      ∀ M'' : Subgroup X, M''.Normal → M' ≤ M'' → M'' = M' ∨ M'' = ⊤ := by
    obtain ⟨M', ⟨hM'n, hMM', hM'top⟩, hmax⟩ := Set.exists_max_image
      {M' : Subgroup X | M'.Normal ∧ M ≤ M' ∧ M' ≠ ⊤} (fun J => Nat.card ↥J) (Set.toFinite _)
      ⟨M, hMn, le_rfl, hXM⟩
    refine ⟨M', hM'n, hMM', hM'top, fun M'' hM''n hle => ?_⟩
    by_cases htop : M'' = ⊤
    · exact Or.inr htop
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hle
        (hmax M'' ⟨hM''n, hMM'.trans hle, htop⟩)).symm
  have hS : IsSimpleGroup (X ⧸ M') := by
    have : Nontrivial (X ⧸ M') := QuotientGroup.nontrivial_iff.mpr hM'top
    refine ⟨fun H hH => ?_⟩
    set H' := H.comap (QuotientGroup.mk' M') with hH'
    have hH'n : H'.Normal := hH.comap _
    have hle : M' ≤ H' := fun x hx => by
      rw [hH', Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact H.one_mem
    rcases hmax H' hH'n hle with h | h
    · left
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M' q
      have : x ∈ H' := hq
      rw [h] at this
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff x).mpr this
    · right
      rw [eq_top_iff]
      intro q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M' q
      have : x ∈ H' := by rw [h]; trivial
      exact this
  set g : K →* X ⧸ M' := (QuotientGroup.mk' M').comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective M').comp hf
  have hgab : ∃ a b : X ⧸ M', a * b ≠ b * a := nonabelian_of_perfect_surjective g hgs
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY hgab hN hQ ψ hψ g hgs
  rw [Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card M' |> Nat.le_of_dvd Nat.card_pos

theorem card_alt {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_isPSL_three_two_one {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_isPSL_four_two_one {X : Type} [Group X] (h : IsPSL 4 2 1 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_isPSL_three_two_two {X : Type} [Group X] (h : IsPSL 3 2 2 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

end CFSG.Quasithin.Vol2.Ch11.SecB
