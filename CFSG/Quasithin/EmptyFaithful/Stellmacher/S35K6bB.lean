module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56bB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.K6b

open S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem comm_mem_inter (hS : Sit H M S) {β l δ : Geo H M} (hlδ : l ∈ nbrs δ) {E : Subgroup G}
    (hbV : ∀ b ∈ Vn δ ⊓ E, ∀ q ∈ ⁅Qv β, Lr β⁆, ⁅b, q⁆ ∈ Vn β) {b q : G}
    (hb : b ∈ Vn δ ⊓ E) (hq : q ∈ ⁅Qv β, Lr β⁆) (hql : q ∈ Qv l) :
    ⁅b, q⁆ ∈ Vn β ⊓ Vn δ := by
  refine ⟨hbV b hb q hq, ?_⟩
  have hqs : q ∈ stab δ := Std.Qv_le_stab hS (Std.mem_nbrs_symm.mpr hlδ) hql
  have h1 : q * b⁻¹ * q⁻¹ ∈ Vn δ :=
    conj_mem_of_le_normalizer (Std.Vn_normal δ) hqs ((Vn δ).inv_mem hb.1)
  have e : ⁅b, q⁆ = b * (q * b⁻¹ * q⁻¹) := by
    simp only [commutatorElement_def, mul_assoc]
  rw [e]
  exact (Vn δ).mul_mem hb.1 h1

theorem comm_mem_Cb (hS : Sit H M S) (hII : CaseII H M) {β l δ : Geo H M}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδ : δ ≠ β) {E : Subgroup G}
    (hE : stab β ≤ Subgroup.normalizer (E : Set G)) (hEW : E ≤ Wb β) (hEL : ⁅E, Lr β⁆ ≤ Vn β)
    {t : G} (ht : t ∈ ⁅Qv β, Lr β⁆) (htl : t ∉ Qv l) {b : G} (hb : b ∈ Vn δ ⊓ E) :
    ∀ q ∈ ⁅Qv β, Lr β⁆, ⁅b, q⁆ ∈ S34.Cb β := by
  have hlt : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hRl : Vn β ⊓ Vn δ = Zv l := hII β l δ hβ hl hlδ hδ
  have hR4 : Nat.card ↥(Vn β ⊓ Vn δ) = 4 := by rw [hRl]; exact hS.cardZ3 l hlt
  have hZR : Zv β ≤ Vn β ⊓ Vn δ := by
    rw [hRl]
    exact Std.Zv_le_Zv_of_nbr hS hβ hl
  have hbV : ∀ b ∈ Vn δ ⊓ E, ∀ q ∈ ⁅Qv β, Lr β⁆, ⁅b, q⁆ ∈ Vn β :=
    fun b hb q hq => comm_mem_Vn hS hE hEW hEL inf_le_right hb hq
  have hc : ⁅b, t⁆ ∈ Vn β := hbV b hb t ht
  obtain ⟨K, hRK, hcK, hK⟩ := exists_card_le (R := Vn β ⊓ Vn δ) (V := Vn β)
    (fun u hu w hw => Vn_comm hS β hu hw) inf_le_left hc (Vn_mul_self hS β hc)
  have hR : ∀ r ∈ Vn β ⊓ Vn δ, t * r * t⁻¹ ∈ Vn β ⊓ Vn δ := by
    intro r hr
    have hz : ⁅r, t⁆ ∈ Zv β :=
      S34.comm_Vn_Qv_le hS.glob hβ (Subgroup.commutator_mem_commutator hr.1 (Q_le_Qv β ht))
    have e : t * r * t⁻¹ = ⁅r, t⁆⁻¹ * r := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Vn β ⊓ Vn δ).mul_mem ((Vn β ⊓ Vn δ).inv_mem (hZR hz)) hr
  have hgen : ∀ q ∈ ⁅Qv β, Lr β⁆, ⁅b, q⁆ ∈ K := by
    intro q hq
    by_cases hql : q ∈ Qv l
    · exact hRK (comm_mem_inter hS hlδ hbV hb hq hql)
    · have h0 : t⁻¹ * q ∈ Qv β ⊓ Qv l :=
        inv_mul_mem_of_relIndex_eq_two (Std.relIndex_Qv hS hβ hl) (Q_le_Qv β hq) (Q_le_Qv β ht)
          (fun h => hql h.2) (fun h => htl h.2)
      have hq0 : t⁻¹ * q ∈ ⁅Qv β, Lr β⁆ := Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hq
      have h1 := hR _ (comm_mem_inter hS hlδ hbV hb hq0 h0.2)
      have e : ⁅b, q⁆ = ⁅b, t⁆ * (t * ⁅b, t⁻¹ * q⁆ * t⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact K.mul_mem hcK (hRK h1)
  have hU : commSpan (Zv β) ⁅Qv β, Lr β⁆ b ≤ K := commSpan_le (hZR.trans hRK) hgen
  have hle : commSpan (Zv β) ⁅Qv β, Lr β⁆ b ≤ Vn β :=
    commSpan_le (Std.Zv_le_Vn_S5 hS hβ) (hbV b hb)
  have horth := hS.orth β hβ
  have hCV : S34.Cb β ≤ Vn β := S34.Cb_le_Vn β
  have hcomm : ∀ c ∈ S34.Cb β, ∀ y ∈ commSpan (Zv β) ⁅Qv β, Lr β⁆ b, y * c = c * y :=
    fun c hc y hy => Vn_comm hS β (hle hy) (hCV hc)
  have hCkey : ∀ y ∈ Lr β, ∀ u ∈ S34.Cb β, y * u * y⁻¹ ∈ S34.Cb β := by
    intro y hy u hu
    have : y * u = u * y := (Subgroup.mem_centralizer_iff.mp hu.2) y hy
    rwa [this, mul_assoc, mul_inv_cancel, mul_one]
  have hnorm : Lr β ≤ Subgroup.normalizer
      ((commSpan (Zv β) ⁅Qv β, Lr β⁆ b ⊔ S34.Cb β : Subgroup G) : Set G) := by
    refine fun x hx => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, ?_⟩
    · exact normalizer_commSpan hS hβ hE hEW hEL inf_le_right hb hx
    · refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨hCkey x hx u, fun hu => ?_⟩
      have := hCkey x⁻¹ ((Lr β).inv_mem hx) _ hu
      simpa [mul_assoc] using this
  rcases horth.eq_or_eq_of_oTwoRes (U := commSpan (Zv β) ⁅Qv β, Lr β⁆ b ⊔ S34.Cb β)
      le_sup_right (sup_le hle hCV) hnorm with h | h
  · intro q hq
    have : ⁅b, q⁆ ∈ commSpan (Zv β) ⁅Qv β, Lr β⁆ b ⊔ S34.Cb β :=
      Subgroup.mem_sup_left (comm_mem_commSpan hq)
    rwa [h] at this
  · exfalso
    have h1 :=
      EmptyFaithful.Stellmacher.OrdinaryProofs.card_sup_mul_card_inf_of_centralizes hcomm
    have h2 : Nat.card ↥(S34.Cb β) * 16 = Nat.card ↥(Vn β) := by
      have := Subgroup.relIndex_mul_card (H := S34.Cb β) (K := Vn β)
      rw [horth.relIndex_eq, inf_eq_left.mpr hCV] at this
      linarith
    have h3 : Nat.card ↥(commSpan (Zv β) ⁅Qv β, Lr β⁆ b) ≤ 8 := by
      have := Subgroup.card_le_of_le hU
      omega
    have h4 : 0 < Nat.card ↥(commSpan (Zv β) ⁅Qv β, Lr β⁆ b ⊓ S34.Cb β) := Nat.card_pos
    have h5 : 0 < Nat.card ↥(S34.Cb β) := Nat.card_pos
    rw [h] at h1
    nlinarith

end S35.K6b

end F53.Stellmacher

end CFSG.Quasithin
