module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Inter
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E14Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin5
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E14

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem img_inter_eq (hS : Sit H M S) (hI : CaseI H M) {δ l ε : Geo H M} (c : Ch.Chart δ)
    (hδ : vtype δ = false) (hl : l ∈ nbrs δ) (hε : ε ∈ nbrs l) (hne : ε ≠ δ) :
    c.img (Vn δ ⊓ Vn ε) = commW orth (Subgroup.zpowers (zc (c.Dl l))) ⊤ := by
  have hD : Nat.card (c.Dl l) = 8 := c.card_Dl hS hl
  have hlδ : l ∈ nbrs δ := hl
  have hlε : l ∈ nbrs ε := mem_nbrs_symm.mpr hε
  have hZU : Zv δ ≤ Vn δ ⊓ Vn ε :=
    le_inf (Zv_le_Vn_S5 hS hδ)
      ((Zv_le_Zv_of_nbr hS hδ hl).trans (Zv_le_Vn hlε))
  have hUV : Vn δ ⊓ Vn ε ≤ Vn δ := inf_le_left
  have hnorm : stab l ≤ Subgroup.normalizer ((Vn δ ⊓ Vn ε : Subgroup G) : Set G) :=
    C1.stab_le_normalizer_inter hS hδ hl hlε hne
  have hcard : Nat.card ↥(Vn δ ⊓ Vn ε) = 8 := (hI δ l ε hδ hl hlε hne).1
  have hinv : IsInvSub orth (c.Dl l) (c.img (Vn δ ⊓ Vn ε)) := by
    intro b hb u hu
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hb
    obtain ⟨x, hx, rfl⟩ := (c.mem_img_iff').mp hu
    rw [← c.π_conj]
    refine (c.mem_img_iff').mpr ⟨Ch.conjV a x, ?_, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm ha.2) (x : G)).mp hx
    exact h1
  have hc4 : Nat.card (c.img (Vn δ ⊓ Vn ε)) = 4 := by
    rw [c.card_img hZU hUV]
    have hm := Subgroup.relIndex_mul_card (H := Zv δ) (K := Vn δ ⊓ Vn ε)
    rw [inf_eq_left.mpr hZU, hcard, hS.cardZ5 δ hδ] at hm
    omega
  exact eq_commW_z_of_card_four hD (isCentInv_zc hD) hinv hc4

theorem mem_stab_of_centralizes (hS : Sit H M S) (hI : CaseI H M) {δ l ε : Geo H M}
    (c : Ch.Chart δ) (hδ : vtype δ = false) (hl : l ∈ nbrs δ) (hε : ε ∈ nbrs l) (hne : ε ≠ δ)
    {x : G} (hx : x ∈ stab δ) (hcen : ∀ r ∈ Vn δ ⊓ Vn ε, x * r * x⁻¹ = r) : x ∈ stab l := by
  have hD : Nat.card (c.Dl l) = 8 := c.card_Dl hS hl
  have h1 : c.θ ⟨x, hx⟩ ∈ cenW (commW orth (Subgroup.zpowers (zc (c.Dl l))) ⊤) := by
    rw [← img_inter_eq hS hI c hδ hl hε hne]
    intro w hw
    obtain ⟨r, hr, rfl⟩ := (c.mem_img_iff').mp hw
    refine (c.comm_mem_iff ⟨x, hx⟩ r).mp ?_
    have e : x * (r : G) * x⁻¹ * (r : G)⁻¹ = 1 := by rw [hcen r hr]; simp
    show x * (r : G) * x⁻¹ * (r : G)⁻¹ ∈ Zv δ
    rw [e]
    exact (Zv δ).one_mem
  have h2 : c.θ ⟨x, hx⟩ ∈ c.Dl l := That_le (cenW_commW_le_That hD h1)
  have h3 : x ∈ c.preθ (c.Dl l) := (c.mem_preθ_iff ⟨x, hx⟩).mpr h2
  rw [c.preθ_Dl hS hδ hl] at h3
  exact h3.2

end S35.E14

end F53.Stellmacher

end CFSG.Quasithin
