module

public import CFSG.RankThree.PartTwo.Sec21.FF84S35Inv

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

@[expose] def F5Contra : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G),
    FF84Sec3 b L B b₁ b₂ → Subgroup.zpowers b ⊔ L = Cen b → ∀ t : G, orderOf t = 2 →
      t * b * t⁻¹ = b⁻¹ → t * b₁ * t⁻¹ = b₁ → t * b₂ * t⁻¹ = b₂ → t ∈ CenS L

variable {G : Type} [Group G] [Finite G]

theorem ff84_3_5_of (h31 : FF84_3_1) (h34 : FF84_3_4) (h5 : F5Contra) : FF84_3_5 := by
  intro G _ _ b L B b₁ b₂ hs
  obtain ⟨hC, -, hCB⟩ := h34 G b L B b₁ b₂ hs
  obtain ⟨t, ht, htb, htb₁, htb₂, -⟩ := exists_inverting_involution hs hCB
  have htL : t ∈ CenS L := h5 G b L B b₁ b₂ hs hC t ht htb htb₁ htb₂
  have hbt : Subgroup.closure {b, t} = Subgroup.zpowers b ⊔ Subgroup.zpowers t := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  have hbL : b ∈ CenS L := fun l hl => (hs.hyp.hLC hl b rfl).symm
  refine ⟨t, ht, htL, htb, ?_, ?_⟩
  · rw [nor_zpowers_eq hs htb, ← hC, hbt]
    rw [sup_assoc, sup_assoc, sup_comm L]
  · have hle : Subgroup.closure {b, t} ≤ CenS L := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hbL
      · exact htL
    have hZ := (h31 G b L B b₁ b₂ hs).2
    rw [eq_bot_iff]
    intro x ⟨hx, hxL⟩
    have hxc : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hle hx y y.2)
    rw [hZ] at hxc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxc))

end CFSG.RankThree.PartTwo.Sec21.FF84
