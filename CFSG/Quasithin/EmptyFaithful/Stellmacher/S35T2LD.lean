module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColFacts
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Plane
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T2LA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.T2L

open S35.Std S35.Col S35.Ch2 S35.Fin
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem maximal_input (hS : Sit H M S) : ∀ β l : Geo H M, vtype β = false → l ∈ nbrs β →
    ∀ P : Subgroup G, P ≤ stab β → stab β ⊓ stab l ≤ P →
      P = stab β ∨ P ≤ Subgroup.normalizer (Zv l : Set G) := fun β l hβ hl P hP hinf => by
  rcases (Mbl_maximal hS hβ hl).2.2 P hP hinf with h | h
  · exact Or.inl h
  · exact Or.inr fun g hg => (h hg).1

theorem vp_mem_commW_dl {δ l : Geo H M} (c : Chart2 δ) (hS : Sit H M S) (hl : l ∈ nbrs δ) :
    vp (c.pt l) ∈ commW orth (c.Dl l) ⊤ := by
  have hD := c.card_Dl hS hl
  have hp := c.isFixPt_pt hS hl
  have hz := isCentInv_zc hD
  have h1 : vp (c.pt l) ∈ fixW orth (c.Dl l) := by
    rw [fixW_sylow hD hp]; exact Subgroup.mem_zpowers _
  exact commW_z_le_commW hD hz (fixW_le_commW_z hD hz h1)

theorem plane_input (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    (⁅Vn δ, stab δ ⊓ stab l⁆ ⊔ Zv l).relIndex (Vn δ) ≤ 2 := by
  obtain ⟨c⟩ := exists_chart2 hS hδ
  set D : Subgroup G := stab δ ⊓ stab l with hD
  set X : Subgroup G := ⁅Vn δ, D⁆ ⊔ Cb δ with hX
  have hCX : Cb δ ≤ X := le_sup_right
  have hDV : ⁅Vn δ, D⁆ ≤ Vn δ := comm_le_Vn le_rfl inf_le_left
  have hXV : X ≤ Vn δ := sup_le hDV (S34.Cb_le_Vn δ)
  have himg : c.img X = commW orth (c.Dl l) ⊤ := by
    rw [hX, c.img_comm le_rfl inf_le_left, c.img_Vn]; rfl
  have hcardX : (Cb δ).relIndex X = 8 := by
    rw [← c.card_img hCX hXV, himg]; exact card_commW_sylow (c.card_Dl hS hl)
  have hX2 : X.relIndex (Vn δ) = 2 := by
    have h := Subgroup.relIndex_mul_relIndex (Cb δ) X (Vn δ) hCX hXV
    rw [hcardX, c.relIndex_Cb_Vn] at h
    omega
  set A : Subgroup G := ⁅Vn δ, D⁆ ⊔ Zv l with hA
  have hZA : Zv l ≤ A := le_sup_right
  have hDA : ⁅Vn δ, D⁆ ≤ A := le_sup_left
  have hCA : Cb δ ≤ A := by
    rcases eq_or_ne (Cb δ) (Zv δ) with hCZ | hCZ
    · rw [hCZ]; exact (Zv_le_Zv_of_nbr hS hδ hl).trans hZA
    have h2 : (Zv δ).relIndex (Zv l) = 2 := relIndex_Zv_Zv_nbr hS hδ hl
    obtain ⟨z, hz, hzZ⟩ : ∃ z ∈ Zv l, z ∉ Zv δ := by
      by_contra hcon
      have hle : Zv l ≤ Zv δ := fun z hz => by
        by_contra h; exact hcon ⟨z, hz, h⟩
      have := Subgroup.relIndex_eq_one.mpr hle
      omega
    have hπz : c.π ⟨z, Zv_le_Vn hl hz⟩ = vp (c.pt l) := π_eq_vp_of_mem_Zv_nbr c hS hδ hl hz hzZ
    have hvp : vp (c.pt l) ∈ c.img X := himg ▸ vp_mem_commW_dl c hS hl
    obtain ⟨x0, hx0⟩ := c.π_surj (vp (c.pt l))
    have hx0X : (x0 : G) ∈ X := (c.mem_img_iff hCX x0).mp (hx0 ▸ hvp)
    have hN : Cb δ ≤ Subgroup.normalizer ((⁅Vn δ, D⁆ : Subgroup G) : Set G) :=
      le_normalizer_of_comm fun k hk q hq =>
        Vn_comm hS δ (S34.Cb_le_Vn δ hk) (hDV hq)
    obtain ⟨u, hu, b, hb, hub⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp hx0X
    have hπu : c.π ⟨u, hDV hu⟩ = vp (c.pt l) := by
      have h1 : c.π ⟨b, S34.Cb_le_Vn δ hb⟩ = 1 := (c.π_eq_one _).mpr hb
      have e : x0 = ⟨u, hDV hu⟩ * ⟨b, S34.Cb_le_Vn δ hb⟩ := Subtype.ext hub
      rw [← hx0, e, map_mul, h1, mul_one]
    set w : G := z * u⁻¹ with hw
    have hwV : w ∈ Vn δ := (Vn δ).mul_mem (Zv_le_Vn hl hz) ((Vn δ).inv_mem (hDV hu))
    have hwC : w ∈ Cb δ := by
      refine (c.π_eq_one ⟨w, hwV⟩).mp ?_
      have e : (⟨w, hwV⟩ : ↥(Vn δ)) = ⟨z, Zv_le_Vn hl hz⟩ * (⟨u, hDV hu⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv, hπz, hπu, mul_inv_cancel]
    have hwZ : w ∉ Zv δ := by
      intro hwZ
      have hzU : z ∈ Uc δ := by
        have e : z = w * u := by rw [hw]; group
        rw [e]
        refine (Uc δ).mul_mem (Zv_le_Uc δ hwZ) ?_
        rw [Uc_eq_comm_stab hS hδ]
        exact Subgroup.commutator_mono le_rfl inf_le_left hu
      exact hCZ ((mem_Uc_iff_of_mem_Zv_nbr hS hδ hl hz hzZ).mp hzU)
    have hr1 : (Zv δ).relIndex (Cb δ) = 2 := by
      have hle := relIndex_Zv_Cb_le hS hδ
      have h1 : (Zv δ).relIndex (Cb δ) ≠ 1 := fun h =>
        hCZ (le_antisymm (Subgroup.relIndex_eq_one.mp h) (S34.Zv_le_Cb hS.glob hδ))
      have h0 := relIndex_ne_zero' (Zv δ) (Cb δ)
      omega
    have hwA : w ∈ A := A.mul_mem (hZA hz) (A.inv_mem (hDA hu))
    intro y hy
    by_cases hyZ : y ∈ Zv δ
    · exact hZA (Zv_le_Zv_of_nbr hS hδ hl hyZ)
    · have hyw : y * w⁻¹ ∈ Zv δ := by
        rw [mul_mem_iff_relIndex_two hr1 hy ((Cb δ).inv_mem hwC)]
        exact iff_of_false hyZ (fun h => hwZ (by simpa using (Zv δ).inv_mem h))
      have e : y = (y * w⁻¹) * w := by group
      rw [e]
      exact A.mul_mem (hZA (Zv_le_Zv_of_nbr hS hδ hl hyw)) hwA
  have hXA : X ≤ A := sup_le hDA hCA
  have hAV : A ≤ Vn δ := sup_le hDV (Zv_le_Vn hl)
  have h := Subgroup.relIndex_mul_relIndex X A (Vn δ) hXA hAV
  rw [hX2] at h
  exact Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ h)

end S35.T2L

end F53.Stellmacher

end CFSG.Quasithin
