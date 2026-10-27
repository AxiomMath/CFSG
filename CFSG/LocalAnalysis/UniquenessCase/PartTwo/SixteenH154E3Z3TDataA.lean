module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Blk
public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterFiveTorusNormalizerSupport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Blocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem s16h_e3_z3_t_normalizer {W : Type} [CommGroup W] [Finite W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    {t : MulAut W} (htA : t ∈ A)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3) :
    t ∈ normalizer (L : Set (MulAut W)) := by
  rcases hB.perm t htA with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  · exfalso
    set U := commSub (⊤ : Subgroup W) L with hU
    set U₂ := commSub (⊤ : Subgroup W) L₂ with hU₂
    have hinfB : U ⊓ U₂ = ⊥ := by rw [hU, hU₂]; exact hB.inf
    have hmem : ∀ l ∈ L, t * l * t⁻¹ ∈ L₂ := by
      intro l hl
      have h := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hl
      rwa [h1] at h
    have hmap : U.map t.toMonoidHom ≤ U₂ := by
      rintro v ⟨u, hu, rfl⟩
      exact commSub_top_map151b (X := L) (Y := L₂) (g := t) hmem u hu
    have hbot : U ⊓ U.map t.toMonoidHom = ⊥ := by
      refine le_bot_iff.mp ?_
      calc U ⊓ U.map t.toMonoidHom ≤ U ⊓ U₂ := le_inf inf_le_left (inf_le_right.trans hmap)
        _ = ⊥ := hinfB
    have hle : rk ↥U ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) :=
      s16h_bl_rk_le_of_inf_eq_bot (U := U) (t := t) hbot
    have hrkU : rk ↥U = 6 := by rw [hU]; exact hrk
    omega

theorem s16h_e3_z3_inverts_of_normalizes {G : Type} [Group G] {L : Subgroup G} {t : G}
    (hL : Nat.card ↥L = 3) (htn : t ∈ normalizer (L : Set G))
    (htL : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∀ l ∈ L, t * l * t⁻¹ = l⁻¹ := by
  rcases CFSG.Semidihedral.Principal.conj_eq_or_inv_of_mem_normalizer_of_card_three hL htn with
    hcent | hinv
  · exfalso
    apply htL
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk_comm : k * l = l * k := by
      have ht_comm_l : t * l = l * t := by
        calc t * l = (t * l * t⁻¹) * t := by group
          _ = l * t := by rw [hcent l hl]
      have hzl : Subgroup.zpowers t ≤ Subgroup.centralizer ({l} : Set G) := by
        rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact ht_comm_l.symm
      have hk' : l * k = k * l := by
        have := hzl hk
        rw [Subgroup.mem_centralizer_iff] at this
        exact this l (Set.mem_singleton l)
      exact hk'.symm
    exact hk_comm
  · exact hinv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
