module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique

theorem isSylowTwoOf_top_iff {Γ : Type*} [Group Γ] {S : Subgroup Γ} :
    IsSylowTwoOf S ⊤ ↔ IsPGroup 2 S ∧ ¬ 2 ∣ S.index := by
  have h : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right (H := S)
  unfold IsSylowTwoOf
  rw [h]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨le_top, h1, h2⟩⟩

@[expose] def NoFiveIndex (Γ : Type*) [Group Γ] : Prop :=
  ∀ S₀ U : Subgroup Γ, IsSylowTwoOf S₀ ⊤ → S₀ ≤ U → ∀ b : ℕ, S₀.relIndex U = 5 ^ b → b = 0

theorem NoFiveIndex.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoFiveIndex Y) : NoFiveIndex X := by
  intro S₀ U hS hle b hb
  refine h (S₀.map (e : X →* Y)) (U.map (e : X →* Y)) ?_ (Subgroup.map_mono hle) b ?_
  · rw [isSylowTwoOf_top_iff] at hS ⊢
    exact ⟨hS.1.map _, by rw [Subgroup.index_map_equiv]; exact hS.2⟩
  · rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hb

theorem NoFiveIndex.of_not_dvd_card {X : Type*} [Group X] [Finite X]
    (h : ¬ 5 ∣ Nat.card X) : NoFiveIndex X := by
  intro S₀ U _ hle b hb
  by_contra hb0
  apply h
  have h1 : 5 ∣ S₀.relIndex U := by
    rw [hb]
    exact dvd_pow_self 5 hb0
  have h2 : S₀.relIndex U ∣ Nat.card U := by
    rw [← Subgroup.relIndex_mul_card (H := S₀) (K := U)]
    exact dvd_mul_right _ _
  have h3 : Nat.card U ∣ Nat.card X := Subgroup.card_subgroup_dvd_card U
  exact h1.trans (h2.trans h3)

structure RowOK (Γ : Type*) [Group Γ] : Prop where
  center : Subgroup.center Γ = ⊥
  out : CFSG.Quasithin.H23Out.Out5Pow Γ
  idx : NoFiveIndex Γ

theorem RowOK.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : RowOK X) :
    RowOK Y where
  center := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    have h1 : e.symm g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := Subgroup.mem_center_iff.1 hg (e x)
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact this
    rw [h.center, Subgroup.mem_bot] at h1
    simpa using congrArg e h1
  out := CFSG.Quasithin.H23Out.Out5Pow.of_mulEquiv e h.out
  idx := NoFiveIndex.of_mulEquiv e.symm h.idx

end CFSG.Quasithin.H23P4
