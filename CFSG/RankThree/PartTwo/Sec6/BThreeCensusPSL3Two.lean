module

public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofMain
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3
public import CFSG.RankThree.PartOne.KC.LinearSubfieldDescent

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem eq_bot_of_perfect_threePrime_glThree_two
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (Y : Subgroup (GL (Fin 3) F)) (hYp : Group.IsPerfect Y)
    (hY3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  classical
  by_cases hirr : ∀ W : Submodule F (Fin 3 → F),
      (∀ g ∈ Y, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  · exact (hY3 (CFSG.RankThree.PartTwo.Sec16.KL3SubProof.ksl3TwoIrrPerfect F Y hirr hYp)).elim
  · push Not at hirr
    obtain ⟨W, hW, hW0, hWt⟩ := hirr
    exact CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two.eq_bot_of_perfect_of_invariant
      Y hYp hY3 W hW hW0 hWt

theorem map_eq_one_of_perfect_threePrime_projectiveSL_three_two
    {G F : Type} [Group G] [Finite G] [Group.IsPerfect G]
    [Field F] [Finite F] [CharP F 2]
    (ρ : G →* projectiveSL 3 F) (hG3 : ¬ 3 ∣ Nat.card G) (g : G) : ρ g = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y := ρ.range
  have hYp : Group.IsPerfect Y := Group.IsPerfect.range ρ
  have hY3 : ¬ 3 ∣ Nat.card Y := fun hd => hG3 (hd.trans (Subgroup.card_range_dvd ρ))
  have hpk : IsPGroup 3 (proj 3 F).ker := fun z => ⟨1, Subtype.ext (by
    simpa only [pow_one, Subgroup.coe_pow, Subgroup.coe_one] using pow_three_eq_one_of_mem_scalars
      (show (z : SpecialLinearGroup (Fin 3) F) ∈ scalars 3 F from
        (ker_proj 3 F).le z.2))⟩
  obtain ⟨m, hm⟩ := hpk.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (proj 3 F).ker) (Nat.card Y) := by
    rw [hm]
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr hY3).pow_left m
  obtain ⟨Y', hmap, hdisj⟩ := exists_lift_of_coprime (proj_surjective 3 F) Y hcop
  let f : Y' →* Y := ((proj 3 F).comp Y'.subtype).codRestrict Y fun y => by
    rw [← hmap]
    exact ⟨y, y.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      have hyk : (y : SpecialLinearGroup (Fin 3) F) ∈ (proj 3 F).ker :=
        congrArg Subtype.val (show f y = 1 from hy)
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.disjoint_def.mp hdisj y.2 hyk))
    · rintro ⟨y, hy⟩
      rw [← hmap] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
  let e : Y' ≃* Y := MulEquiv.ofBijective f hf
  have hY'p : Group.IsPerfect Y' :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hY'3 : ¬ 3 ∣ Nat.card Y' := by
    rw [Nat.card_congr e.toEquiv]
    exact hY3
  let Z := Y'.map (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F)
  have hZp : Group.IsPerfect Z := Group.IsPerfect.map _
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun hd =>
    hY'3 (hd.trans (Subgroup.card_map_dvd Y' SpecialLinearGroup.toGL))
  have hZbot := eq_bot_of_perfect_threePrime_glThree_two Z hZp hZ3
  have hY'bot : Y' = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hz : SpecialLinearGroup.toGL y ∈ Z := ⟨y, hy, rfl⟩
    rw [hZbot, Subgroup.mem_bot] at hz
    exact SpecialLinearGroup.toGL_injective (hz.trans (map_one _).symm)
  have hg : ρ g ∈ Y := ⟨g, rfl⟩
  simpa only [← hmap, hY'bot, Subgroup.map_bot, Subgroup.mem_bot] using hg

theorem isSolvable_of_projectiveSL_three_two_and_complement_derived
    {G F : Type} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    (ρ : G →* projectiveSL 3 F) (hker : ρ.ker ≤ Subgroup.center G)
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator G)) : Group.IsSolvable G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  rw [Group.isSolvable_iff_commutator_lt]
  intro Y hY
  refine lt_of_le_of_ne (Subgroup.commutator_le.2 ?_) ?_
  · intro a ha b hb
    rw [_root_.commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  · intro hperf
    have : Group.IsPerfect Y := Subgroup.isPerfect_iff.mpr hperf
    have hYle : Y ≤ _root_.commutator G := by
      rw [← Subgroup.commutator_eq_self (H := Y), _root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    have hY3 : ¬ 3 ∣ Nat.card Y := Nat.prime_three.coprime_iff_not_dvd.mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.coprime_card_of_perfect
        (CFSG.hasNormalPComplement_of_le 3 hYle hNPC))
    have hYs : Group.IsSolvable Y := Group.isSolvable_of_comm fun x y => by
      have hx : ρ (x : G) = 1 :=
        map_eq_one_of_perfect_threePrime_projectiveSL_three_two (ρ.comp Y.subtype) hY3 x
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker hx)) (y : G)).symm
    exact hY (eq_bot_of_isPerfect_of_isSolvable inferInstance hYs)

theorem isSolvable_of_projectiveSL_three_two_algebraic_and_complement_derived
    {G K Ω : Type} [Group G] [Finite G] [Field K] [Finite K]
    [Field Ω] [CharP Ω 2] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (ρ : G →* projectiveSL 3 Ω) (hker : ρ.ker ≤ Subgroup.center G)
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator G)) : Group.IsSolvable G := by
  obtain ⟨E, hE, -, κ, hκ, hcard, ρE, hcomp, hkerE⟩ :=
    CFSG.RankThree.PartOne.exists_finite_subfield_projectiveSL_lift
      (K := K) (by decide : 0 < 3) ρ ∅
  let : Finite E := hE
  exact isSolvable_of_projectiveSL_three_two_and_complement_derived ρE
    (hkerE ▸ hker) hNPC

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
