module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Disc
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Notation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 CFSG.Quasithin.EmptyFaithful.Stellmacher

namespace S35.C1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem inter_dichotomy (hS : Sit H M S) {β l δ : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδβ : δ ≠ β) :
    Vn β ⊓ Vn δ = Zv l ∨ (Zv l < Vn β ⊓ Vn δ ∧ Nat.card ↥(Vn β ⊓ Vn δ) = 8 ∧
      Nat.card ↥(Vn β) = 32) := by
  rcases inter_dichotomy_aux hS hβ hl hlδ hδβ with h | ⟨h1, h2, h3, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

theorem exists_arc (hS : Sit H M S) :
    ∃ β l δ : Geo H M, vtype β = false ∧ l ∈ nbrs β ∧ l ∈ nbrs δ ∧ δ ≠ β := by
  obtain ⟨β, hβ⟩ : ∃ β : Geo H M, vtype β = false := by
    obtain ⟨e, he⟩ := exists_adj (γ₀ (H ⊔ M) H M)
    have hne := vtype_ne_of_adj he
    by_cases hv : vtype (γ₀ (H ⊔ M) H M) = false
    · exact ⟨_, hv⟩
    · refine ⟨e, ?_⟩
      cases h : vtype e
      · rfl
      · exfalso
        apply hne
        rw [h]
        simpa using hv
  obtain ⟨l, hl⟩ := exists_adj β
  have hl' : l ∈ nbrs β := hl
  have hlt := Std.vtype_nbr_S5 hβ hl'
  obtain ⟨δ, hδ, hne⟩ := exists_mem_nbrs_ne hS.glob.amalg l (Std.mem_nbrs_symm.mpr hl')
  exact ⟨β, l, δ, hβ, hl', Std.mem_nbrs_symm.mpr hδ, hne⟩

theorem claim1 (hS : Sit H M S) : CaseII H M ∨ CaseI H M := by
  obtain ⟨β0, l0, δ0, hβ0, hl0, hlδ0, hne0⟩ := exists_arc hS
  rcases inter_dichotomy hS hβ0 hl0 hlδ0 hne0 with h | ⟨-, h8, h32⟩
  · left
    intro β l δ hβ hl hlδ hδβ
    have hc := card_inter_eq hS hβ0 hl0 hlδ0 hne0 hβ hl hlδ hδβ
    rw [h] at hc
    have hlt := Std.vtype_nbr_S5 hβ hl
    exact (Subgroup.eq_of_le_of_card_ge (Zv_le_inter hl hlδ)
      (by rw [hc, hS.cardZ3 _ (Std.vtype_nbr_S5 hβ0 hl0), hS.cardZ3 l hlt])).symm
  · right
    intro β l δ hβ hl hlδ hδβ
    exact ⟨(card_inter_eq hS hβ0 hl0 hlδ0 hne0 hβ hl hlδ hδβ).trans h8,
      (card_Vn_eq hβ0 hβ).trans h32⟩

theorem caseI_orthSec (hS : Sit H M S) (hI : CaseI H M) {δ : Geo H M} (hδ : vtype δ = false) :
    S34.Cb δ = Zv δ ∧ IsOrthSec (stab δ) (Zv δ) (Vn δ) := by
  obtain ⟨β0, l0, δ0, hβ0, hl0, hlδ0, hne0⟩ := exists_arc hS
  have h32 : Nat.card ↥(Vn δ) = 32 := (card_Vn_eq hβ0 hδ).trans (hI β0 l0 δ0 hβ0 hl0 hlδ0 hne0).2
  have h16 := IsOrthSec.relIndex_eq (hS.orth δ hδ)
  have hm := Subgroup.relIndex_mul_card (H := S34.Cb δ) (K := Vn δ)
  rw [inf_eq_left.mpr (S34.Cb_le_Vn δ), h16, h32] at hm
  have hc : Nat.card ↥(S34.Cb δ) = 2 := by omega
  have hCb : S34.Cb δ = Zv δ := by
    refine (Subgroup.eq_of_le_of_card_ge (S34.Zv_le_Cb hS.glob hδ) ?_).symm
    rw [hc, hS.cardZ5 δ hδ]
  exact ⟨hCb, hCb ▸ hS.orth δ hδ⟩

end S35.C1

end F53.Stellmacher

end CFSG.Quasithin
