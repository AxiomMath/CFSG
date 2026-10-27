module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeAlt6A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {W : Type} [CommGroup W]

private theorem s168e3_alt6_subgroupOf_le_ker {X H : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X H J₀ J₁) (hHX : H ≤ X) :
    H.subgroupOf X ≤ (s16e_two_irrAct F).ker := by
  intro h hh
  rw [Subgroup.mem_subgroupOf] at hh
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro I
  apply Subtype.ext
  have hstab : StableUnder H (I : Subgroup W) := (s16e_two_isIrrOn_of_mem F I.2).2.1
  apply le_antisymm
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hu
    exact hstab (h : MulAut W) hh v hv
  · intro u hu
    refine Subgroup.mem_map.2
      ⟨(h : MulAut W)⁻¹ u, hstab (h : MulAut W)⁻¹ (H.inv_mem hh) u hu, ?_⟩
    simp

theorem s168e3_alt6_three_dvd_of_equiv [Finite W] {X H : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X H J₀ J₁) (hHX : H ≤ X) (hA : UC22.IsAlt ↥H 6)
    (hE₀ : Z391.EndUnitsTrivial H J₀)
    (htrans : ∀ I₁ ∈ irrSet H, ∀ I₂ ∈ irrSet H, ∃ g ∈ X, I₂ = I₁.map g.toMonoidHom)
    (h9 : 3 ^ 2 ∣ Nat.card ↥X) {ψ : MulAut W}
    (hψ : ψ ∈ Subgroup.centralizer (H : Set (MulAut W))) (hψJ : J₀.map ψ.toMonoidHom = J₁) :
    3 ∣ Nat.card ↥(s16e_two_cent X H) := by
  by_contra h3
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite ↥(irrSet H) := Finite.of_injective _ Subtype.coe_injective
  let φ : ↥X →* Equiv.Perm ↥(irrSet H) := s16e_two_irrAct F
  have hcardH : Nat.card ↥H = 360 := by
    rw [s15k_six_alt_card hA (by norm_num)]
    norm_num
  have hcardHsub : Nat.card ↥(H.subgroupOf X) = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv, hcardH]
  have hker9 : 3 ^ 2 ∣ Nat.card ↥φ.ker :=
    (show 3 ^ 2 ∣ 360 by norm_num).trans
      (hcardHsub ▸ Subgroup.card_dvd_of_le (s168e3_alt6_subgroupOf_le_ker F hHX))
  have h27X : ¬ 3 ^ 3 ∣ Nat.card ↥X := fun hX27 =>
    h3 (s16e_two_three_dvd_of_cube hX27 (s16e_two_card_dvd_mul_aut F)
      (s16e_two_alt6_not_cube_aut hA))
  have hrange3 : ¬ 3 ∣ Nat.card ↥φ.range := by
    intro h3r
    have hprod : 3 ^ 3 ∣ Nat.card ↥φ.ker * Nat.card ↥φ.range := by
      have hmul : 3 ^ 2 * 3 ∣ Nat.card ↥φ.ker * Nat.card ↥φ.range := Nat.mul_dvd_mul hker9 h3r
      have heq : 3 ^ 2 * 3 = 3 ^ 3 := by norm_num
      rwa [heq] at hmul
    exact h27X (Subgroup.card_ker_mul_card_range φ ▸ hprod)
  haveI : MulAction.IsPretransitive ↥φ.range ↥(irrSet H) :=
    ⟨fun I₁ I₂ => by
      obtain ⟨g, hgX, hgI⟩ := htrans (I₁ : Subgroup W) I₁.2 (I₂ : Subgroup W) I₂.2
      refine ⟨⟨φ ⟨g, hgX⟩, ⟨g, hgX⟩, rfl⟩, ?_⟩
      change (φ ⟨g, hgX⟩ : Equiv.Perm ↥(irrSet H)) I₁ = I₂
      apply Subtype.ext
      rw [s16e_two_irrAct_apply]
      exact hgI.symm⟩
  have h3range : 3 ∣ Nat.card ↥φ.range := by
    let I₀ : ↥(irrSet H) := ⟨J₀, F.irr₀⟩
    have hdiv := (MulAction.stabilizer ↥φ.range I₀).index_dvd_card
    rw [MulAction.index_stabilizer_of_transitive ↥φ.range I₀,
      s168e3_alt6_irr_card_three F hE₀ hψ hψJ] at hdiv
    exact hdiv
  exact hrange3 h3range

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
