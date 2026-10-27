module

public import CFSG.Quasithin.H13.GoldschmidtM22EndMul
public import CFSG.Quasithin.H13.GoldschmidtM22EndN3e

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

omit [Finite G] in
include hk in
theorem D_le_CHU : D ≤ CHU T L V := hk.D_eq ▸ inf_le_right

omit [Finite G] in
include hk in
theorem D_le_HH : D ≤ HH T := hk.D_le_K.trans hk.K_le_HH

include h in
theorem card_V : Nat.card V = 16 := by
  have := h.natural.card_eq
  simpa using this

include h in
theorem card_V0 (h6211 : Stmt6_2_11) : Nat.card ↥(V ⊓ CHU T L V) = 8 := by
  have h1 := Subgroup.relIndex_mul_card (H := V ⊓ CHU T L V) (K := V)
  rw [inf_eq_left.mpr (inf_le_left : V ⊓ CHU T L V ≤ V), relIndex_V_CHU h h6211,
    card_V h] at h1
  omega

omit [Finite G] in
include hk in
theorem V0_le_D : V ⊓ CHU T L V ≤ D := by
  rw [hk.D_eq]
  exact inf_le_inf_right _ le_sup_left

include hk h hZ in
theorem V1_eq : conjSubgroup V g ⊓ CHU T L V = conjSubgroup (V ⊓ CHU T L V) g := by
  rw [CFSG.QuasithinUnique.C5.conjSubgroup_inf,
    conjSubgroup_eq_iff_mem_normalizer.mpr (HH_le_normalizer_CHU h hZ hk.g_mem)]

include hk h hZ in
theorem card_V1 (h6211 : Stmt6_2_11) : Nat.card ↥(conjSubgroup V g ⊓ CHU T L V) = 8 := by
  rw [hk.V1_eq h hZ, CFSG.QuasithinUnique.C5.card_conjSubgroup, card_V0 h h6211]

omit [Finite G] in
include hk in
theorem V1_le_D : conjSubgroup V g ⊓ CHU T L V ≤ D := by
  rw [hk.D_eq]
  exact inf_le_inf_right _ le_sup_right

include hk h hZ in
theorem Z_le_V0 : quasithinOmegaOneCenter T ≤ V ⊓ CHU T L V :=
  le_inf (Z_le_V h hZ) (hk.Z_le_D.trans hk.D_le_CHU)

include hk h hZ in
theorem V0_inf_V1 : (V ⊓ CHU T L V) ⊓ (conjSubgroup V g ⊓ CHU T L V) =
    quasithinOmegaOneCenter T := by
  refine le_antisymm ?_ (le_inf (hk.Z_le_V0 h hZ) ?_)
  · rw [← hk.inter_eq]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  · exact le_inf (hk.inter_eq.symm.le.trans inf_le_right) (hk.Z_le_D.trans hk.D_le_CHU)

include hk h hZ in
theorem exists_mul_V0_V1 (h6211 : Stmt6_2_11) :
    ∀ d ∈ D, ∃ u ∈ V ⊓ CHU T L V, ∃ w ∈ conjSubgroup V g ⊓ CHU T L V, d = u * w := by
  refine exists_mul_eq_of_card_mul hk.V0_le_D hk.V1_le_D ?_
  rw [card_V0 h h6211, hk.card_V1 h hZ h6211, hk.V0_inf_V1 h hZ, hZ, hk.extra.2.1]
  norm_num

end KData

end CFSG.Quasithin.H13.GM22
