module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MSetup
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MStruct

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

variable {G : Type} [Group G] [Finite G] {b : G} {J B : Subgroup G} {b₁ b₂ : G}

namespace FF79Sec4

variable (h : FF79Sec4 b J B b₁ b₂)
include h

theorem sit_main (h14 : FF79_1_4) (h41 : FF79_4_1)
    (hsyl : IsSylowOf 3 (Subgroup.closure ({b, b₁ ^ 2 * b₂} : Set G)) (OUp 3 (Cen (b₁ * b₂))))
    (hbL : b ∈ Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂)))
    (hγK : b₁ ^ 2 * b₂ ∈ Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen b))
    (hK : IsLnq 2 2 2 (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen b)))
    (hL : IsLnq 3 2 1 (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂)))) :
    M42Sit (b₁ * b₂) (b₁ ^ 2 * b₂) b (OUp 3 (Cen (b₁ * b₂)))
      (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂)))
      (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen b)) (Opp 3 (Cen b)) where
  cenβ := m42_OUp_le 3 _
  Hnorm := fun g hg x hx => m42_OUp_conj_mem hg hx
  H3 := fun g hg hc => m42_mem_OUp hg hc
  e_mem := (m42_Lay_le _ hγK).1
  f_mem := (m42_Lay_le _ hbL).1
  ord_e := h.ord_γ
  ord_f := h.ord_b
  comm := h.comm_bγ.symm
  syl := by rwa [Set.pair_comm]
  Λdef := rfl
  Δdef := rfl
  f_Λ := hbL
  e_Δ := hγK
  Λiso := M42GL3.of_IsLnq hL
  Δiso := M42A5.of_IsLnq hK
  Xe := h.X_γ h14 h41
  Xf := h.X_b h14 h41
  Xodd := h41 G b J B b₁ b₂ h
  kgn := fun M hM => h.kgn_H hM

theorem sit_sym (h14 : FF79_1_4) (h41 : FF79_4_1)
    (hsyl : IsSylowOf 3 (Subgroup.closure ({b, b₁ ^ 2 * b₂} : Set G)) (OUp 3 (Cen (b₁ * b₂))))
    (hbL : b ∈ Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂)))
    (hγK : b₁ ^ 2 * b₂ ∈ Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen b))
    (hK : IsLnq 3 2 1 (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen b)))
    (hL : IsLnq 2 2 2 (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂)))) :
    M42Sit (b₁ * b₂) b (b₁ ^ 2 * b₂) (OUp 3 (Cen (b₁ * b₂)))
      (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen b))
      (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂))) (Opp 3 (Cen b)) where
  cenβ := m42_OUp_le 3 _
  Hnorm := fun g hg x hx => m42_OUp_conj_mem hg hx
  H3 := fun g hg hc => m42_mem_OUp hg hc
  e_mem := (m42_Lay_le _ hbL).1
  f_mem := (m42_Lay_le _ hγK).1
  ord_e := h.ord_b
  ord_f := h.ord_γ
  comm := h.comm_bγ
  syl := hsyl
  Λdef := rfl
  Δdef := rfl
  f_Λ := hγK
  e_Δ := hbL
  Λiso := M42GL3.of_IsLnq hK
  Δiso := M42A5.of_IsLnq hL
  Xe := h.X_b h14 h41
  Xf := h.X_γ h14 h41
  Xodd := h41 G b J B b₁ b₂ h
  kgn := fun M hM => h.kgn_H hM

end FF79Sec4

end CFSG.RankThree.PartTwo.Sec21.FF79
