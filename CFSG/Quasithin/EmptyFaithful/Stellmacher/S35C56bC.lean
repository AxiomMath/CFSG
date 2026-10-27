module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56bB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Inter

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C56

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

theorem comm_mem_Zv (hS : Sit H M S) (hI : CaseI H M) {β l δ : Geo H M}
    (hirr : ∀ U : Subgroup G, Zv β ≤ U → U ≤ Vn β → Lr β ≤ Subgroup.normalizer (U : Set G) →
      U = Zv β ∨ U = Vn β)
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδ : δ ≠ β) {E : Subgroup G}
    (hE : stab β ≤ Subgroup.normalizer (E : Set G)) (hEW : E ≤ Wb β) (hEL : ⁅E, Lr β⁆ ≤ Vn β)
    {t : G} (ht : t ∈ ⁅Qv β, Lr β⁆) (htl : t ∉ Qv l) {b : G} (hb : b ∈ Vn δ ⊓ E) :
    ∀ q ∈ ⁅Qv β, Lr β⁆, ⁅b, q⁆ ∈ Zv β := by
  obtain ⟨hR8, hV32⟩ := hI β l δ hβ hl hlδ hδ
  have hZR : Zv β ≤ Vn β ⊓ Vn δ := (Std.Zv_le_Zv_of_nbr hS hβ hl).trans (C1.Zv_le_inter hl hlδ)
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
  have hne : commSpan (Zv β) ⁅Qv β, Lr β⁆ b ≠ Vn β := by
    intro h
    have h1 : Nat.card (Vn β) ≤ Nat.card K := h ▸ Subgroup.card_le_of_le hU
    omega
  have hle : commSpan (Zv β) ⁅Qv β, Lr β⁆ b ≤ Vn β :=
    commSpan_le (Std.Zv_le_Vn_S5 hS hβ) (hbV b hb)
  rcases hirr _ (le_commSpan _ _ _) hle
      (normalizer_commSpan hS hβ hE hEW hEL inf_le_right hb) with h | h
  · intro q hq
    rw [← h]
    exact comm_mem_commSpan hq
  · exact absurd h hne

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
