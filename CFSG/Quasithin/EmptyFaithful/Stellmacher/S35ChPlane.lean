module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChZl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Rl (δ l : Geo H M) : Subgroup G :=
  ⨅ ε ∈ nbrs l, ⨅ (_ : ε ≠ δ), Vn δ ⊓ Vn ε

theorem exists_arc_end (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) : ∃ ε ∈ nbrs l, ε ≠ δ := by
  have hlv : vtype l = true := vtype_nbr_S5 hδ hl
  obtain ⟨a, b, c, h, hab, hac, hbc⟩ := nbrs_S3 hS hlv
  have hδl : δ ∈ nbrs l := mem_nbrs_symm.mp hl
  rw [h] at hδl
  have : ∃ ε ∈ nbrs l, ε ≠ δ := by
    rcases hδl with rfl | rfl | rfl
    · exact ⟨b, by rw [h]; simp, hab.symm⟩
    · exact ⟨a, by rw [h]; simp, hab⟩
    · exact ⟨a, by rw [h]; simp, hac⟩
  exact this

namespace Ctx

variable (hC : Ctx H M S)
include hC

theorem stab_le_normalizer_Rl {δ l ε : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ)
    (hε : ε ∈ nbrs l) (hne : ε ≠ δ) :
    stab l ≤ Subgroup.normalizer ((Vn δ ⊓ Vn ε : Subgroup G) : Set G) := by
  have hlv : vtype l = true := vtype_nbr_S5 hδ hl
  obtain ⟨δ3, h3, h31, h32, -⟩ := nbrs_S3_third hC.sit hlv (mem_nbrs_symm.mp hl) hε hne.symm
  exact (hC.hR δ l ε δ3 hδ hl (mem_nbrs_symm.mpr hε) (mem_nbrs_symm.mpr h3) hne h31 h32).2.2

theorem Rl_eq {δ l ε : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) (hε : ε ∈ nbrs l)
    (hne : ε ≠ δ) : Rl δ l = Vn δ ⊓ Vn ε := by
  have hlv : vtype l = true := vtype_nbr_S5 hδ hl
  apply le_antisymm
  · exact iInf₂_le_of_le ε hε (iInf_le_of_le hne le_rfl)
  · refine le_iInf₂ fun ε' hε' => le_iInf fun hne' => ?_
    by_cases h : ε' = ε
    · subst h; exact le_rfl
    · obtain ⟨δ3, h3, h31, h32, hall⟩ :=
        nbrs_S3_third hC.sit hlv (mem_nbrs_symm.mp hl) hε hne.symm
      rcases hall ε' hε' with h1 | h1 | h1
      · exact absurd h1 hne'
      · exact absurd h1 h
      · subst h1
        exact (hC.hR δ l ε ε' hδ hl (mem_nbrs_symm.mpr hε) (mem_nbrs_symm.mpr hε') hne hne'
          h).1.le

theorem Rl_le_Vn {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    Rl δ l ≤ Vn δ := by
  obtain ⟨ε, hε, hne⟩ := exists_arc_end hC.sit hδ hl
  rw [hC.Rl_eq hδ hl hε hne]
  exact inf_le_left

theorem Zv_nbr_le_Rl {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    Zv l ≤ Rl δ l := by
  obtain ⟨ε, hε, hne⟩ := exists_arc_end hC.sit hδ hl
  rw [hC.Rl_eq hδ hl hε hne]
  exact le_inf (Zv_le_Vn hl) (Zv_le_Vn (mem_nbrs_symm.mpr hε))

theorem Zv_le_Rl {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    Zv δ ≤ Rl δ l := (Zv_le_Zv_of_nbr hC.sit hδ hl).trans (hC.Zv_nbr_le_Rl hδ hl)

theorem card_Rl {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    Nat.card (Rl δ l) = 8 := by
  obtain ⟨ε, hε, hne⟩ := exists_arc_end hC.sit hδ hl
  rw [hC.Rl_eq hδ hl hε hne]
  exact (hC.caseI δ l ε hδ hl (mem_nbrs_symm.mpr hε) hne).1

theorem inf_le_normalizer_Rl {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    stab δ ⊓ stab l ≤ Subgroup.normalizer ((Rl δ l : Subgroup G) : Set G) := by
  obtain ⟨ε, hε, hne⟩ := exists_arc_end hC.sit hδ hl
  rw [hC.Rl_eq hδ hl hε hne]
  exact inf_le_right.trans (hC.stab_le_normalizer_Rl hδ hl hε hne)

end Ctx

namespace Chart

variable {δ : Geo H M} (c : Chart δ)

include c

theorem isInvSub_img_Rl (hC : Ctx H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) : IsInvSub orth (c.Dl l) (c.img (Rl δ l)) :=
  (c.le_normalizer_iff inf_le_left (hC.Zv_le_Rl hδ hl) (hC.Rl_le_Vn hδ hl)).mp
    (hC.inf_le_normalizer_Rl hδ hl)

theorem card_img_Rl (hC : Ctx H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    Nat.card (c.img (Rl δ l)) = 4 := by
  rw [c.card_img (hC.Zv_le_Rl hδ hl) (hC.Rl_le_Vn hδ hl)]
  have := card_eq_relIndex_mul (hC.Zv_le_Rl hδ hl)
  rw [hC.card_Rl hδ hl, hC.sit.cardZ5 δ hδ] at this
  omega

end Chart

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin
