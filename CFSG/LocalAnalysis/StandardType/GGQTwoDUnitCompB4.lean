module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.StandardType.QTwo

open CFSG CFSG.ClassicalInvolution.Phan

private theorem qtwoDB7_b4_ggTorusLift_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R]
    [Group R'] (e : R ≃* R') (h : GGTorusLift p r R') : GGTorusLift p r R := by
  intro L' _ _ ψ hψ hker hperf
  have hker' : (e.toMonoidHom.comp ψ).ker = ψ.ker := by
    ext l
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact e.map_eq_one_iff
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard, hEker⟩ :=
    h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) (hker' ▸ hker) hperf
  exact ⟨U, E, hU, hU2, hEU, hE, hcard, hker' ▸ hEker⟩

theorem qtwoDB7_torusLift_quot
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) {d : ℕ} (hd : 5 ≤ d) {Jb : Type} [Group Jb]
    (e : Jb ⧸ Subgroup.center Jb ≃* Su F0 2 1 d ⧸ Subgroup.center (Su F0 2 1 d)) :
    CFSG.StandardType.GGTorusLift 3 (CFSG.StandardType.ggUnitaryTorusRank 3 d)
      (Jb ⧸ Subgroup.center Jb) := by
  have hK : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hF0]; norm_num
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have : d = 3 := (Prod.mk.inj h).1
    omega
  have hlift := ggTorusLift_unitary (K := F0) (n := 1) (d := d) (p := 3) hK le_rfl hd3 hdq
    Nat.prime_three (by norm_num)
  have e1 : Su F0 2 1 d ⧸ Subgroup.center (Su F0 2 1 d) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ 1) F0) :=
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr
        (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK d))
        (CFSG.LieType.Universal.Unitary.map_center_mulEquiv _)).trans
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK hd3 hdq).2)
  exact qtwoDB7_b4_ggTorusLift_of_mulEquiv (e := e.trans e1) hlift

theorem qtwoDB7_three_dvd_su
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) {d : ℕ} (hd : 5 ≤ d) :
    3 ∣ Nat.card (Su F0 2 1 d ⧸ Subgroup.center (Su F0 2 1 d)) := by
  have hK : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hF0]; norm_num
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have : d = 3 := (Prod.mk.inj h).1
    omega
  have hquasi : CFSG.IsQuasisimple (Su F0 2 1 d) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupCongr
        (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK d)).symm
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK hd3 hdq).1
  have hlift := qtwoDB7_torusLift_quot (Jb := Su F0 2 1 d) hF0 hd (MulEquiv.refl _)
  have : Group.IsPerfect (Su F0 2 1 d) := hquasi.1
  have hperf : commutator (Su F0 2 1 d ⧸ Subgroup.center (Su F0 2 1 d)) = ⊤ :=
    (Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk' (Subgroup.center (Su F0 2 1 d)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard, _⟩ :=
    hlift (Su F0 2 1 d ⧸ Subgroup.center (Su F0 2 1 d)) (MonoidHom.id _)
      Function.surjective_id bot_le hperf
  have hr : 1 ≤ ggUnitaryTorusRank 3 d := by
    rw [ggUnitaryTorusRank]
    split_ifs <;> omega
  have h3dvd : 3 ∣ Nat.card E := by
    rw [hcard]
    exact pow_dvd_pow 3 hr
  exact dvd_trans h3dvd (Subgroup.card_subgroup_dvd_card E)

end CFSG.StandardType.QTwo

end
