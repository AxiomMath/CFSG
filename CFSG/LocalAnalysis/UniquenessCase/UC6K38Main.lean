module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K38A
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36StrongEmb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)


variable {G : Type} [Group G] [Finite G]

theorem k38_of_star
    (hG : CFSG.Open.IsKGroup G)
    (hstar : ∀ q : ℕ, q.Prime → q ≠ 2 → 3 < CFSG.Open.twoLocalPrimeRank q G →
      ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q S ⊤ →
        star36Sup q S ≠ ⊤ ∨ (3 < q ∧ (3 ∣ Nat.card G → ∃ N : Subgroup G, IsStronglyPEmbedded 3 N))) :
    (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.twoLocalPrimeRank q G ≤ 3) ∨ ¬ 3 ∣ Nat.card G ∨
      ∃ N : Subgroup G, IsStronglyPEmbedded 3 N := by
  by_contra hneg
  push Not at hneg
  obtain ⟨⟨q, hq, hq2, h4⟩, h3, hno⟩ := hneg
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd : q ∣ Nat.card G := by
    have hne : {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank q H = k}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      unfold CFSG.Open.twoLocalPrimeRank at h4
      simp [hemp] at h4
    have hbdd : BddAbove {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank q H = k} := by
      refine ⟨Nat.card G, ?_⟩
      rintro _ ⟨H, -, rfl⟩
      exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt H
    obtain ⟨H, -, hH⟩ := Nat.sSup_mem hne hbdd
    obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
    have hk : 1 ≤ CFSG.Open.pRank q H := by
      have : 3 < CFSG.Open.pRank q H := by
        unfold CFSG.Open.twoLocalPrimeRank at h4
        rw [← hH] at h4
        exact h4
      omega
    refine (dvd_pow_self q (by omega : CFSG.Open.pRank q H ≠ 0)).trans (hEc ▸ ?_)
    exact Subgroup.card_subgroup_dvd_card E
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf q (⊤ : Subgroup G)
  have hS1 : S ≠ ⊥ := by
    intro hb
    have hc := hS.card_eq
    rw [hb, Subgroup.card_bot, Subgroup.card_top] at hc
    have hpos : 0 < (Nat.card G).factorization q :=
      Nat.Prime.factorization_pos_of_dvd hq (Nat.card_pos).ne' hqdvd
    have : 1 < q ^ (Nat.card G).factorization q := Nat.one_lt_pow hpos.ne' hq.one_lt
    omega
  rcases hstar q hq hq2 h4 S hS with ha | ⟨-, hb⟩
  · have hH : IsStronglyPEmbedded q (star36Sup q S) := isStronglyPEmbedded_star36Sup hS hS1 ha
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact hno _ hH
    obtain ⟨N, hNmax, hN1, hNg⟩ :=
      K38A.exists_maxTwoLocal_not_le_holds hG hq2 hq3 hH (by omega)
    obtain ⟨Y, hYN, hY, hYc⟩ := CFSG.SectionRank.exists_pRank hq.one_lt N
    have hYrank : 1 < CFSG.Open.pRank q Y :=
      hN1.trans_le (CFSG.SectionRank.le_pRank hq.one_lt le_rfl hY hYc)
    obtain ⟨S', hYS'⟩ := hY.isPGroup.exists_le_sylow
    have hS' : CFSG.ABGLocalTools.IsSylowOf q (S' : Subgroup G) ⊤ :=
      (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, S'.isPGroup', by
        rw [Subgroup.relIndex_top_right]
        exact S'.not_dvd_index⟩
    obtain ⟨k, -, hk⟩ := hS.exists_mem_conj hS'
    set f : G →* G := (MulAut.conj k⁻¹).toMonoidHom with hf
    have hfx : ∀ x, f x = k⁻¹ * x * k := fun x => by simp [hf, MulAut.conj_apply]
    have hYS : Y.map f ≤ S := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hfx]
      exact (hk y).1 (hYS' hy)
    have hN' : N.map f ∈ calMOf (Y.map f) :=
      ⟨UC6.isMaxTwoLocal_conj hNmax k, Subgroup.map_mono hYN⟩
    have hrank : 1 < CFSG.Open.pRank q (Y.map f) :=
      hYrank.trans_le (CFSG.SectionRank.pRank_le_map hq.one_lt f (MulAut.conj k⁻¹).injective Y)
    have hle := le_star36Sup_of_mem_calMOf hYS hrank hN'
    apply hNg k
    intro x hx
    refine ⟨k⁻¹ * x * k, hle ⟨x, hx, hfx x⟩, ?_⟩
    show k * (k⁻¹ * x * k) * k⁻¹ = x
    group
  · exact hno _ (hb h3).choose_spec

end CFSG.LocalAnalysis.UniquenessCase.UCK
