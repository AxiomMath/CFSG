module

public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.RankThree.PartOne

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsStronglyPEmbedded.rankThreeGamma_one_le_of_le {p : ℕ} {M X : Subgroup G}
    (hsp : IsStronglyPEmbedded p M) (hp : p.Prime) (hX : IsPGroup p X) (hXM : X ≤ M) :
    rankThreeGamma 1 p X ≤ M := by
  rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
  intro Y hYX hYrank
  obtain ⟨A, hAY, hAel, hAcard⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained p Y (by omega)
  have hAM : A ≤ M := (hAY.trans hYX).trans hXM
  have hYM : Y ≤ M := hYX.trans hXM
  have hpdvdA : p ∣ Nat.card A := by
    rw [hAcard]
    exact dvd_pow_self p (by omega)
  intro g hg
  by_contra hgM
  apply hsp.2.2 g hgM
  refine hpdvdA.trans (Subgroup.card_dvd_of_le ?_)
  refine le_inf hAM ?_
  intro a ha
  have hg' : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) := Subgroup.inv_mem _ hg
  have h1 : g⁻¹ * a * g ∈ Y := by
    simpa using (Subgroup.mem_normalizer_iff.1 hg' a).1 (hAY ha)
  exact ⟨g⁻¹ * a * g, hYM h1, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem IsStronglyPEmbedded.inf_map_conj_eq_bot {p : ℕ} {M Q : Subgroup G}
    (hsp : IsStronglyPEmbedded p M) (hp : p.Prime) (hQM : Q ≤ M) (hQp : IsPGroup p Q) :
    ∀ g : G, g ∉ M → Q ⊓ M.map (MulAut.conj g).toMonoidHom = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro g hg
  let C : Subgroup G := M.map (MulAut.conj g).toMonoidHom
  change Q ⊓ C = ⊥
  by_contra hne
  have hpdvd : p ∣ Nat.card ↥(Q ⊓ C) := by
    have hQC : IsPGroup p ↥(Q ⊓ C) := hQp.to_inf_left
    obtain ⟨k, hk⟩ := hQC.exists_card_eq
    rw [hk]
    exact dvd_pow_self p (by
      rintro rfl
      rw [pow_zero] at hk
      exact hne (Subgroup.eq_bot_of_card_eq _ hk))
  exact hsp.2.2 g hg
    (hpdvd.trans (Subgroup.card_dvd_of_le (le_inf (inf_le_left.trans hQM) inf_le_right)))

end CFSG.RankThree.PartOne
