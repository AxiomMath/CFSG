module

public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

namespace CFSG.Quasithin.H13.SLMult

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier Subgroup

theorem isPSL_of_statedSL_two {m : ℕ} (hm : 3 ≤ m) {X : Type} [Group X]
    (e : X ≃* ↥(StatedSL m (ZMod 2))) : StatedClassicalModel X .PSL m 2 1 := by
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hm2 : m ≠ 2 := by omega
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, ZMod 2, inferInstance, inferInstance,
    by simp, ⟨e.trans ?_⟩⟩
  · intro h
    exact hm2 (congrArg Prod.fst h)
  · intro h
    exact hm2 (congrArg Prod.fst h)
  · exact ((MulEquiv.subgroupCongr (CFSG.GH74.Exceptional.statedSL_eq_top_of_card_two h2 m)).trans
      Subgroup.topEquiv).trans (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo h2 m).symm

theorem card_center_dvd_multiplier {S : Type} [Group S] {Q : Type} [Group Q]
    [Group.IsPerfect Q] (e : Q ⧸ center Q ≃* S) :
    Nat.card (center Q) ∣ Nat.card (CFSG.Open.griessHopfMultiplier S) := by
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq hker.le)

theorem card_table_dvd_two {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5) :
    Nat.card (generic .PSL m 2 1 × exceptional .PSL m 2 1) ∣ 2 := by
  simp only [generic, exceptional, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod]
  rcases hm with rfl | rfl | rfl <;> decide

theorem card_multiplier_dvd_two
    {m : ℕ}
    (hm : m = 3 ∨ m = 4 ∨ m = 5) {X : Type} [Group X] (e : X ≃* ↥(StatedSL m (ZMod 2))) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 2 := by
  have h3 : 3 ≤ m := by omega
  have hX := isPSL_of_statedSL_two h3 e
  obtain ⟨-, ⟨e'⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.griess_classical_of_large
    .PSL ⟨hX.1, .inl hX⟩ (Or.inl rfl)
  rw [Nat.card_congr e'.toEquiv]
  exact card_table_dvd_two hm

theorem center_eq_bot_of_quot_statedSL
    {Q : Type} [Group Q] [Group.IsPerfect Q] {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (e : Q ⧸ center Q ≃* ↥(StatedSL m (ZMod 2))) (hO2 : CFSG.pCore 2 Q = ⊥) :
    center Q = ⊥ := by
  have h1 := (card_center_dvd_multiplier e).trans
    (card_multiplier_dvd_two hm (MulEquiv.refl ↥(StatedSL m (ZMod 2))))
  have h2 : IsPGroup 2 ↥(center Q) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
  have h3 : center Q ≤ CFSG.pCore 2 Q := le_sSup ⟨inferInstance, h2⟩
  rw [hO2] at h3
  exact le_bot_iff.mp h3

end CFSG.Quasithin.H13.SLMult
