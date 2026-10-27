module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieRows
public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Sz


theorem seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
  intro m hm
  refine rowSOf429_of_noCfg fun S _ _ _ _ ⟨e⟩ => ?_
  intro A σ K hc
  obtain ⟨-, a, -, F, _, _, hf, hK', ⟨θ⟩⟩ := Census.suzukiModel_of_index m hm
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3 : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr (e.trans θ).toEquiv]
    exact not_three_dvd_card_suzukiGroup hK
  haveI := hc.isPerfect
  obtain ⟨E, -, -, -, hE9, -⟩ := exists_e9_of_type429 hc.isType
  apply h3
  have h9 : 9 ∣ Nat.card S := hE9 ▸ Subgroup.card_subgroup_dvd_card E
  exact (show 3 ∣ 9 by norm_num).trans h9

end Sz

section Tits


theorem isInnerAut_of_not_three_dvd_outer {S : Type} [Group S] [Finite S]
    (hout : ¬ 3 ∣ Nat.card (Outer S)) {σ : MulAut S} (hσ3 : σ ^ 3 = 1) : IsInnerAut σ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
  have := CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.finite_outer S
  set x : Outer S := QuotientGroup.mk' (inner S) σ with hx
  have h1 : x ^ 3 = 1 := by rw [hx, ← map_pow, hσ3, map_one]
  have h2 : orderOf x ∣ Nat.card (Outer S) := orderOf_dvd_natCard x
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h1
  have hx1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact h
    · exact absurd (h ▸ h2) hout
  rw [orderOf_eq_one_iff, hx, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  exact hx1

theorem seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := by
  intro ht
  refine rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => ?_
  intro A σ K hc
  haveI := hc.isPerfect
  have hσ3 := cfgS429_pow_three hc
  obtain ⟨E, hEK, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 hc.isType
  have hfix : ∀ k ∈ K, σ k = k := fun k hk => Sec4.mem_autFix.mp (hc.le_autFix hk)
  have hm : CFSG.Blueprint.ReeTitsModel S .Tits 2 1 :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e (Census.bridgeExceptional46.tits ht)
  have hin : IsInnerAut σ := isInnerAut_of_not_three_dvd_outer
    (CFSG.Quasithin.A318P.not_dvd_outer_tits hm Nat.prime_three (by norm_num)) hσ3
  have hZ := center_trivial_of_isSimpleGroup hs hna
  refine false_of_fix_e9 (MulAut.conj : S →* MulAut S).range ?_ (fun s => ⟨s, rfl⟩) hZ hin hσ3
    hc.ne_one hEK hEc hE3 hE9 hfix hEZ
  intro B hB h3B hcB
  refine card_le_nine_inn (fun E' hE' h27 => ?_) hZ hB h3B hcB
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits ht
    (E := E'.map e.toMonoidHom) ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩ ?_
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg e (congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE'.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, h27]

end Tits

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
