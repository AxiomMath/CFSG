module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.L81

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem thirtytwo_le_card_Vn (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    32 ≤ Nat.card (Vn δ) := by
  have h1 : (S34.Cb δ).relIndex (Vn δ) = 16 := (hS.orth δ hδ).relIndex_eq
  have h2 := Subgroup.relIndex_mul_card (H := S34.Cb δ) (K := Vn δ)
  rw [h1, inf_eq_left.mpr (S34.Cb_le_Vn δ)] at h2
  have h3 : Nat.card (Zv δ) ≤ Nat.card (S34.Cb δ) :=
    Subgroup.card_le_of_le (S34.Zv_le_Cb hS.glob hδ)
  rw [hS.cardZ5 δ hδ] at h3
  omega

theorem relIndex_ge_eight (hS : Sit H M S) (hII : CaseII H M) {β l δ : Geo H M}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδ : δ ≠ β) :
    8 ≤ (Vn δ ⊓ Vn β).relIndex (Vn δ) := by
  have hlt : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hvδ : vtype δ = false := Std.vtype_nbr_S3 hlt (Std.mem_nbrs_symm.mp hlδ)
  have hc : Vn δ ⊓ Vn β = Zv l := by rw [inf_comm]; exact hII β l δ hβ hl hlδ hδ
  have h1 := thirtytwo_le_card_Vn hS hvδ
  have h2 := Subgroup.relIndex_mul_card (H := Vn δ ⊓ Vn β) (K := Vn δ)
  have h3 : Nat.card ↥(Vn δ ⊓ Vn β ⊓ Vn δ) = 4 := by
    rw [inf_eq_left.mpr inf_le_left, hc]
    exact hS.cardZ3 l hlt
  rw [h3] at h2
  omega

end S35.L81

end F53.Stellmacher

end CFSG.Quasithin
