module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.CGT.PushingUpLit.CGT6
open CFSG.CGT.Timmesfeld75 (conjSubgroup ConjTwoTransitive conjSubgroup_conjSubgroup
  conjSubgroup_one conjSubgroup_sup_eq_sup)
open scoped MatrixGroups

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F)

private theorem w16l_conjTwoTransitive_conjSubgroup {G : Type} [Group G] {T : Subgroup G}
    (h : ConjTwoTransitive G T) (k : G) : ConjTwoTransitive G (conjSubgroup k T) := by
  intro a b c d hab hcd
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup] at hab hcd
  have h' := h (a * k) (b * k) (c * k) (d * k) hab hcd
  obtain ⟨x, hx1, hx2⟩ := h'
  refine ⟨x, ?_, ?_⟩
  · rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    simpa only [mul_assoc] using hx1
  · rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    simpa only [mul_assoc] using hx2

theorem w16l_exists_conj_eq_map_Sig01 (hs : 2 ≤ s)
    {T : Subgroup (unitaryPSU h 3)} (hT : ∃ S : Sylow 2 (unitaryPSU h 3), T = cenS S)
    {g : unitaryPSU h 3} (hne : conjSubgroup g T ≠ T)
    (hcard : Nat.card ↥(T ⊔ conjSubgroup g T) = 2 ^ s * ((2 ^ s) ^ 2 - 1)) :
    ∃ x : unitaryPSU h 3,
      conjSubgroup x (T ⊔ conjSubgroup g T) = (Sig01 h).map (unitaryProj h 3) := by
  classical
  haveI : Finite F := h.finite
  haveI : Finite (unitaryPSU h 3) :=
    Finite.of_surjective (unitaryProj h 3) (unitaryProj_surjective h 3)
  have hmodel := stated_model_pu h hs
  obtain ⟨⟨-, ⟨S₀, hS₀⟩, hBor⟩, -⟩ :=
    CFSG.CGT.Timmesfeld75.psu3_wc hs hmodel (T0_isWC h) (T0_ne_bot h)
  obtain ⟨S, hS⟩ := hT
  obtain ⟨k, hk⟩ := exists_conj_cenS S S₀
  have hcen₀ : T0 h = cenS S₀ := hS₀
  have hTk : T = conjSubgroup k (T0 h) := by rw [hS, hk, hcen₀]
  have h2 : ConjTwoTransitive (unitaryPSU h 3) T := by
    rw [hTk]
    exact w16l_conjTwoTransitive_conjSubgroup hBor.1 k
  obtain ⟨κ, hκ, hκq, hκ6⟩ := exists_kappa h hs
  have hκ1 : κ ≠ 1 := fun e => hκ6 (by rw [e, one_pow])
  set π := unitaryProj h 3 with hπ
  set w := dg h hκ 0 1 (-1) (by norm_num) with hw
  have hT1 := conj_T0_eq h hκ
  have hne10 : conjSubgroup (π w) (T0 h) ≠ T0 h := by
    rw [hT1]
    exact map_TGsub_b₀_ne h hκ hκ1
  have hA : conjSubgroup 1 T ≠ conjSubgroup g T := by
    rw [conjSubgroup_one]
    exact hne.symm
  have e1 : conjSubgroup k⁻¹ T = T0 h := by
    rw [hTk, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have e2 : conjSubgroup (π w * k⁻¹) T = conjSubgroup (π w) (T0 h) := by
    rw [hTk, conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one]
  have hB : conjSubgroup k⁻¹ T ≠ conjSubgroup (π w * k⁻¹) T := by
    rw [e1, e2]
    exact hne10.symm
  obtain ⟨x, hx1, hx2⟩ := h2 1 g k⁻¹ (π w * k⁻¹) hA hB
  have hxT : conjSubgroup x T = T0 h := by
    rw [mul_one, e1] at hx1
    exact hx1
  have hxgT : conjSubgroup (x * g) T = conjSubgroup (π w) (T0 h) := by
    rw [← e2]
    exact hx2
  have hL : conjSubgroup x (T ⊔ conjSubgroup g T) = T0 h ⊔ conjSubgroup (π w) (T0 h) := by
    rw [conjSubgroup_sup_eq_sup, hxT, conjSubgroup_conjSubgroup, hxgT]
  have hle : T0 h ⊔ conjSubgroup (π w) (T0 h) ≤ (Sig01 h).map π := by
    refine sup_le (Subgroup.map_mono (TGsub_le_Sig01 h _ _ (by simp [a₀]))) ?_
    rw [hT1]
    exact Subgroup.map_mono (TGsub_le_Sig01 h _ _ (by simp [b₀]))
  have hcardL : Nat.card ↥(conjSubgroup x (T ⊔ conjSubgroup g T)) =
      2 ^ s * ((2 ^ s) ^ 2 - 1) := by
    unfold conjSubgroup
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hcard
  refine ⟨x, ?_⟩
  rw [hL]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_map_Sig01 h, ← hL, hcardL]


end CFSG.LocalAnalysis.WeakClosure81

end
