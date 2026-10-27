module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpPair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp

open S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  {β α' m γ' : Geo H M}

theorem le_zpowers_of_card_two {Z : Subgroup G} (hZ : Nat.card Z = 2) {z : G} (hz : z ∈ Z)
    (hne : z ≠ 1) : Z ≤ Subgroup.zpowers z := by
  have hle : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.mpr hz
  have h1 : orderOf z ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have h2 : 0 < orderOf z := orderOf_pos z
  have h3 : Nat.card Z ≤ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, hZ]
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle h3).symm.le

theorem Vn_mem_or (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Ch.Chart α') (hpl : PlaneAt c m) {v : G}
    (hvs : v ∈ stab α') (hθ : c.θ ⟨v, hvs⟩ = zc (c.Dl m)) {w : G} (hw : w ∈ Vn β) :
    w ∈ Qv α' ∨ v⁻¹ * w ∈ Qv α' := by
  have hws : w ∈ stab α' := (Std.PD_Vn_le_stab hS hp).1 hw
  rcases imageA hS hneg hp hb c hpl hw hws with h | h
  · exact Or.inl ((c.ker_iff hS hp.vδ' ⟨w, hws⟩).mp h)
  · refine Or.inr ?_
    have h1 : c.θ (⟨v, hvs⟩⁻¹ * ⟨w, hws⟩) = 1 := by
      rw [map_mul, map_inv, hθ, h]
      exact inv_mul_cancel _
    exact (c.ker_iff hS hp.vδ' _).mp h1

theorem Zv_le_comm (hS : Sit H M S) (hneg : ¬ ClaimLP H M) {β α' m γ' m' γ'' : Geo H M}
    (hp : S34.PD β α') (hb : Back H M β α' m γ') (hp' : S34.PD α' β)
    (hb' : Back H M α' β m' γ'') (c : Ch.Chart α') (c' : Ch.Chart β) (hpl : PlaneAt c m)
    (hpl' : PlaneAt c' m') : Zv α' ≤ ⁅Vn β, Vn α'⁆ := by
  by_contra hZ
  have hs := Std.PD_Vn_le_stab hS hp
  obtain ⟨v, hv, hvs, hθv⟩ := exists_zc hS hneg hp hb c hpl
  obtain ⟨u, hu, hus', hθu⟩ := exists_zc hS hneg hp' hb' c' hpl'
  have hus : u ∈ stab β := hs.2 hu
  have h1 : ∀ w ∈ Vn β, w ∈ Qv α' → ∀ x ∈ Vn α', w * x * w⁻¹ * x⁻¹ = 1 := by
    intro w hw hwQ x hx
    by_contra hne
    have hzZ := Ch.comm_mem_Zv_of_Qv hS hp.vδ' hwQ hx
    have hzR : w * x * w⁻¹ * x⁻¹ ∈ ⁅Vn β, Vn α'⁆ := Subgroup.commutator_mem_commutator hw hx
    exact hZ ((le_zpowers_of_card_two (hS.cardZ5 α' hp.vδ') hzZ hne).trans
      (Subgroup.zpowers_le.mpr hzR))
  have hc0V : v * u * v⁻¹ * u⁻¹ ∈ Vn β := by
    have : v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹) := by group
    rw [this]
    exact mul_mem hv (Ch.conj_mem_Vn hus (inv_mem hv))
  have hVstab : ∀ y ∈ Vn β, y ∈ stab β := fun y hy => Ch.Qv_le_stab' β (Std.Vn_le_Qv_self hS β hy)
  set K2 : Subgroup G := Subgroup.zpowers (v * u * v⁻¹ * u⁻¹) ⊔ Zv β with hK2
  have hvx : ∀ x ∈ Vn α', v * x * v⁻¹ * x⁻¹ ∈ K2 := by
    intro x hx
    have hZc : ∀ y ∈ Qv β, ∀ t ∈ Vn β, t * y * t⁻¹ * y⁻¹ ∈ Zv β := by
      intro y hy t ht
      have h := Ch.comm_mem_Zv_of_Qv hS hp.vδ hy ht
      have e : t * y * t⁻¹ * y⁻¹ = (y * t * y⁻¹ * t⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h
    rcases Vn_mem_or hS hneg hp' hb' c' hpl' hus' hθu hx with hxQ | hxQ
    · exact Subgroup.mem_sup_right (hZc x hxQ v hv)
    · obtain ⟨x0, hx0⟩ : ∃ x0, x0 = u⁻¹ * x := ⟨_, rfl⟩
      have hxe : x = u * x0 := by rw [hx0]; group
      rw [← hx0] at hxQ
      have hx0V : x0 ∈ Vn α' := by rw [hx0]; exact mul_mem (inv_mem hu) hx
      subst hxe
      have hz0 := hZc x0 hxQ v hv
      have e : u * (v * x0 * v⁻¹ * x0⁻¹) * u⁻¹ = v * x0 * v⁻¹ * x0⁻¹ := by
        rw [central_comm hS hp.vδ hz0 hus]
        group
      have e2 : v * (u * x0) * v⁻¹ * (u * x0)⁻¹ =
          (v * u * v⁻¹ * u⁻¹) * (u * (v * x0 * v⁻¹ * x0⁻¹) * u⁻¹) := by group
      rw [e2, e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) hz0
  have hkey : ∀ x ∈ Vn α', ∀ w ∈ Vn β, w * x * w⁻¹ * x⁻¹ ∈ K2 := by
    intro x hx w hw
    rcases Vn_mem_or hS hneg hp hb c hpl hvs hθv hw with hwQ | hwQ
    · rw [h1 w hw hwQ x hx]
      exact K2.one_mem
    · have hv0 : v⁻¹ * w ∈ Vn β := mul_mem (inv_mem hv) hw
      have e := h1 _ hv0 hwQ x hx
      have hconj : v⁻¹ * w * x * (v⁻¹ * w)⁻¹ = x := mul_inv_eq_one.mp e
      have e2 : w * x * w⁻¹ * x⁻¹ = v * (v⁻¹ * w * x * (v⁻¹ * w)⁻¹) * v⁻¹ * x⁻¹ := by group
      rw [e2, hconj]
      exact hvx x hx
  have hA : Subgroup.zpowers u ≤ stab β := Subgroup.zpowers_le.mpr hus
  have hD : Nat.card (c'.Dl m') = 8 := c'.card_Dl hS hb'.1
  have h2 := c'.card_commSec hA
  rw [c'.bar_zpowers hus, hθu, card_commW_zc hD] at h2
  set K := commSec (Subgroup.zpowers u) (Zv β) (Vn β) with hK
  have hZK : Zv β ≤ K := Ch.Chart.Zv_le_commSec _
  have hcard := Subgroup.relIndex_mul_card (H := Zv β) (K := K)
  rw [inf_eq_left.mpr hZK, h2, hS.cardZ5 β hp.vδ] at hcard
  have hKK2 : K ≤ K2 := by
    refine sup_le (Subgroup.commutator_le.mpr fun w hw y hy => ?_) le_sup_right
    exact hkey y ((Subgroup.zpowers_le.mpr hu) hy) w hw
  have h3 := Subgroup.card_le_of_le hKK2
  have hC : ∀ z ∈ Zv β, ∀ y ∈ Subgroup.zpowers (v * u * v⁻¹ * u⁻¹), y * z = z * y :=
    fun z hz y hy =>
      central_comm hS hp.vδ hz (hVstab y ((Subgroup.zpowers_le.mpr hc0V) hy))
  have h4 : Nat.card K2 ≤ _ := card_sup_le_of_comm hC
  have h5 : Nat.card (Subgroup.zpowers (v * u * v⁻¹ * u⁻¹)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd two_pos
      (orderOf_dvd_of_pow_eq_one ((Std.Vn_isElemAbelian hS β).2 _ hc0V))
  rw [hS.cardZ5 β hp.vδ] at h4
  omega

end S35.Lp

end F53.Stellmacher

end CFSG.Quasithin
