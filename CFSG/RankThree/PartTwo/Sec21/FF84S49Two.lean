module

public import CFSG.RankThree.PartTwo.Sec21.FF84S49Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

section Tr

variable {G H : Type} [Group G] [Group H] {L : Subgroup G} {A : Subgroup H}

theorem trX_comm (e : ↥L ≃* ↥A) {X Z : Subgroup G} (hX : X ≤ L) (hZ : Z ≤ L) :
    trX e ⁅X, Z⁆ = ⁅trX e X, trX e Z⁆ := by
  have h3 : (⁅X.subgroupOf L, Z.subgroupOf L⁆).map L.subtype = ⁅X, Z⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
      Subgroup.map_subgroupOf_eq_of_le hZ]
  rw [← h3, trX_map, Subgroup.map_commutator]
  rfl

end Tr

@[expose] def A_transv_stmt : Prop :=
  ∀ Y : Subgroup P8, (Y = Ua ∨ Y = Ub) → ∀ x ∈ Y, x ≠ 1 → x ∉ ⁅Y, Subgroup.zpowers cc⁆ →
    x ∉ Y ⊓ Cen cc → ¬ (Cen x ⊓ A8s ≤ Nor Y)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

namespace S48Ctx

variable (c : S48Ctx b L B K b₁ b₂) {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2)

include c hU

theorem comm_b₂_eq : ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆ = U ⊓ Cen b₁ := by
  have hiso := c.S_iso hU
  have hbE : b ∈ Subgroup.closure ({b, b₁} : Set G) := Subgroup.subset_closure (by simp)
  have hb₁E : b₁ ∈ Subgroup.closure ({b, b₁} : Set G) := Subgroup.subset_closure (by simp)
  have hle : ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆ ≤ U ⊓ Cen b₁ := by
    intro w hw
    have hcen := hiso.2.2.2.2.2.2 hw
    have h1 : w ∈ Cen b :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hcen b hbE).symm
    have h2 : w ∈ Cen b₁ :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hcen b₁ hb₁E).symm
    refine ⟨?_, h2⟩
    rw [← c.S48_CSb hU]
    exact ⟨c.comm_le_S hU (mem_b₂ c.sec) hw, h1⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h4 : Nat.card ↥(U ⊓ Cen b₁) = 4 := by
    rw [(c.piU hU).2.1.2]; norm_num
  rw [h4, hiso.2.2.1]

end S48Ctx

theorem S48Ctx.S49_two_comp (c : S48Ctx b L B K b₁ b₂)
    {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2) (hA : A8Model L) (hP : A_PiStar_stmt)
    (hT : A_transv_stmt) {x : G} (hx : x ∈ U) (h1 : x ∉ ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆)
    (h2 : x ∉ ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆) (hx1 : x ≠ 1) :
    ¬ Cen x ≤ Nor (Op 2 (Nor U)) := by
  have hpost := c.post
  obtain ⟨e, he₁, he₂⟩ := M0_model hA hpost
  have hBP := trX_inf_B_L hpost e he₁ he₂
  have hUL : U ≤ L := ((S47_PiStar_eq hpost U).1 hU).1
  have hxL : x ∈ L := hUL hx
  have hb₁ : b₁ ∈ L := (Subgroup.mem_inf.1 hpost.sec.hb₁).2
  have hY : trX e U ∈ PiStar A8s Pm 2 := by
    have := (trX_piStar_iff e (inf_le_right : B ⊓ L ≤ L) hUL).1 ((S47_PiStar_eq hpost U).1 hU)
    rwa [hBP] at this
  rw [hP] at hY
  have hY' : trX e U = Ua ∨ trX e U = Ub := hY
  have eb₁ : ((e ⟨b₁, hb₁⟩ : A8s) : P8) = cc := he₁ ⟨b₁, hb₁⟩ rfl
  have hyY : ((e ⟨x, hxL⟩ : A8s) : P8) ∈ trX e U := (mem_trX e).2 ⟨⟨x, hxL⟩, hx, rfl⟩
  have hy1 : ((e ⟨x, hxL⟩ : A8s) : P8) ≠ 1 := by
    intro h
    apply hx1
    have h' : e ⟨x, hxL⟩ = 1 := Subtype.ext h
    have := e.injective (h'.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hz : Subgroup.zpowers b₁ ≤ L := (Subgroup.zpowers_le).2 hb₁
  have hyc : ((e ⟨x, hxL⟩ : A8s) : P8) ∉ ⁅trX e U, Subgroup.zpowers cc⁆ := by
    intro hm
    have hcomm : ⁅trX e U, Subgroup.zpowers cc⁆ = trX e ⁅U, Subgroup.zpowers b₁⁆ := by
      rw [trX_comm e hUL hz, trX_zpowers e hb₁, eb₁]
    rw [hcomm, mem_trX] at hm
    obtain ⟨x', hx', hxx'⟩ := hm
    have hx'x : x' = ⟨x, hxL⟩ := e.injective (Subtype.ext hxx')
    apply h1
    have : x ∈ ⁅U, Subgroup.zpowers b₁⁆ := by
      have := hx'
      rw [hx'x] at this
      exact this
    exact Subgroup.commutator_mono (c.U_le_S hU) le_rfl this
  have hyc2 : ((e ⟨x, hxL⟩ : A8s) : P8) ∉ trX e U ⊓ Cen cc := by
    intro hm
    have hinf := trX_inf_cen e U hb₁
    rw [eb₁] at hinf
    rw [← hinf, mem_trX] at hm
    obtain ⟨x', hx', hxx'⟩ := hm
    have hx'x : x' = ⟨x, hxL⟩ := e.injective (Subtype.ext hxx')
    apply h2
    rw [c.comm_b₂_eq hU]
    have := hx'
    rw [hx'x] at this
    exact this
  have hne : ¬ (Cen ((e ⟨x, hxL⟩ : A8s) : P8) ⊓ A8s ≤ Nor (trX e U)) :=
    hT _ hY' _ hyY hy1 hyc hyc2
  intro hcen
  apply hne
  intro z hz'
  obtain ⟨hzc, hzA⟩ := hz'
  set ℓ : ↥L := e.symm ⟨z, hzA⟩ with hℓ
  have hℓe : e ℓ = ⟨z, hzA⟩ := by simp [hℓ]
  have hℓx : (ℓ : G) ∈ Cen x := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have hzc' : z * ((e ⟨x, hxL⟩ : A8s) : P8) = ((e ⟨x, hxL⟩ : A8s) : P8) * z :=
      Subgroup.mem_centralizer_singleton_iff.1 hzc
    have h5 : e (ℓ * ⟨x, hxL⟩) = e (⟨x, hxL⟩ * ℓ) := by
      rw [map_mul, map_mul, hℓe]
      exact Subtype.ext hzc'
    have := e.injective h5
    exact congrArg Subtype.val this
  have hℓS : (ℓ : G) ∈ Nor (Op 2 (Nor U)) := hcen hℓx
  have hℓb : (ℓ : G) ∈ Cen b := hpost.sec.hyp.hLC ℓ.2
  have hℓU : (ℓ : G) ∈ Nor U := by
    have := nor_inf hℓS (Subgroup.le_normalizer hℓb)
    rwa [c.S48_CSb hU] at this
  rw [mem_nor_trX_iff e ℓ.2 hUL] at hℓU
  have h6 : e ⟨(ℓ : G), ℓ.2⟩ = ⟨z, hzA⟩ := hℓe
  rw [h6] at hℓU
  exact hℓU

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
