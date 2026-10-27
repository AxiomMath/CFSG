module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Rk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3TDataA
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem s16h_e3_z3_t_data {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hL : Nat.card ↥L = 3) (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    {t : MulAut W} (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3)
    (htL : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) :
    t ∈ centSub (commSub (⊤ : Subgroup W) L₂) ∧ ∀ l ∈ L, t * l * t⁻¹ = l⁻¹ := by
  let U := commSub (⊤ : Subgroup W) L
  let U₂ := commSub (⊤ : Subgroup W) L₂
  have htN : t ∈ normalizer (L : Set (MulAut W)) := s16h_e3_z3_t_normalizer hB hrk htA htr
  have hLmap : L.map (MulAut.conj t).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
  have hL2map : L₂.map (MulAut.conj t).toMonoidHom = L₂ := by
    rcases hB.perm t htA with h | h
    · exact h.2
    · exfalso
      rw [h.1] at hLmap
      exact hB.ne hLmap
  have ht_inv : ∀ l ∈ L, t * l * t⁻¹ = l⁻¹ := s16h_e3_z3_inverts_of_normalizes hL htN htL
  have ht_stabU : Subgroup.zpowers t ≤ stabSub U :=
    Subgroup.zpowers_le.mpr (hB.stab t htA hLmap).1
  have ht_stabU₂ : Subgroup.zpowers t ≤ stabSub U₂ :=
    Subgroup.zpowers_le.mpr (hB.stab t htA hLmap).2
  have h3 : 3 ≤ rk ↥(commSub U (Subgroup.zpowers t)) :=
    s16h_three_le_rk_of_inverts_Z3 hW hL hrk hfix ht_inv
  have h_inf : commSub U (Subgroup.zpowers t) ⊓ commSub U₂ (Subgroup.zpowers t) = ⊥ := by
    have hYU : commSub U (Subgroup.zpowers t) ≤ U := by
      apply commSub_le_of_invariant
      intro y hy w hw
      exact (mem_stabSub.mp (ht_stabU hy) w).2 hw
    have hYU₂ : commSub U₂ (Subgroup.zpowers t) ≤ U₂ := by
      apply commSub_le_of_invariant
      intro y hy w hw
      exact (mem_stabSub.mp (ht_stabU₂ hy) w).2 hw
    have hle : commSub U (Subgroup.zpowers t) ⊓ commSub U₂ (Subgroup.zpowers t) ≤ U ⊓ U₂ :=
      le_inf (inf_le_left.trans hYU) (inf_le_right.trans hYU₂)
    rw [hB.inf] at hle
    exact le_bot_iff.mp hle
  have h_le : commSub U (Subgroup.zpowers t) ⊔ commSub U₂ (Subgroup.zpowers t) ≤
      commSub (⊤ : Subgroup W) (Subgroup.zpowers t) :=
    sup_le (commSub_mono le_top le_rfl) (commSub_mono le_top le_rfl)
  have h_sum : rk ↥(commSub U (Subgroup.zpowers t)) +
      rk ↥(commSub U₂ (Subgroup.zpowers t)) ≤ 3 := by
    have hs := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers t))
      (commSub U₂ (Subgroup.zpowers t))
    rw [h_inf, rk_bot, add_zero] at hs
    rw [← hs]
    exact le_trans (rk_mono h_le) htr
  have h_zero : rk ↥(commSub U₂ (Subgroup.zpowers t)) = 0 := by omega
  have h_bot : commSub U₂ (Subgroup.zpowers t) = ⊥ := (rk_eq_zero_iff hW).mp h_zero
  have h_cent : t ∈ centSub U₂ := by
    rw [mem_centSub]
    intro u hu
    exact mem_fixV_zpowers_iff_apply.mp ((commSub_eq_bot_iff.mp h_bot) hu)
  exact ⟨h_cent, ht_inv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
