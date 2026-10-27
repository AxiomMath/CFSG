module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Img

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp2

open S35.Ch2 S35.Fin S35.Lp
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  {β α' m γ' : Geo H M}

theorem Zv_le_comm (hS : Sit H M S) (hneg : ¬ ClaimLP H M) {β α' m γ' m' γ'' : Geo H M}
    (hp : S34.PD β α') (hb : Back H M β α' m γ') (hp' : S34.PD α' β)
    (hb' : Back H M α' β m' γ'') (c : Chart2 α') (c' : Chart2 β) (hU : UC α')
    (hU' : UC β) : Zv α' ≤ ⁅Vn β, Vn α'⁆ := by
  by_contra hZ
  have hs := Std.PD_Vn_le_stab hS hp
  obtain ⟨d, hdT, hd1, hdd, hbar⟩ := exists_d hS hneg hp hb c hU
  obtain ⟨d', hdT', hd1', hdd', hbar'⟩ := exists_d hS hneg hp' hb' c' hU'
  obtain ⟨v, hv, hvs, hθv⟩ := exists_pre c hbar
  obtain ⟨u, hu, hus', hθu⟩ := exists_pre c' hbar'
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
  have hVstab : ∀ y ∈ Vn β, y ∈ stab β := fun y hy =>
    Ch.Qv_le_stab' β (Std.Vn_le_Qv_self hS β hy)
  set K2 : Subgroup G := Subgroup.zpowers (v * u * v⁻¹ * u⁻¹) ⊔ Cb β with hK2
  have hvx : ∀ x ∈ Vn α', v * x * v⁻¹ * x⁻¹ ∈ K2 := by
    intro x hx
    have hZc : ∀ y ∈ Qv β, ∀ t ∈ Vn β, t * y * t⁻¹ * y⁻¹ ∈ Zv β := by
      intro y hy t ht
      have h := Ch.comm_mem_Zv_of_Qv hS hp.vδ hy ht
      have e : t * y * t⁻¹ * y⁻¹ = (y * t * y⁻¹ * t⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h
    rcases Vn_mem_or hS hp' c' hbar' hdd' hus' hθu hx with hxQ | hxQ
    · exact Subgroup.mem_sup_right (Zv_le_Cb' hS hp.vδ (hZc x hxQ v hv))
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
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _)
        (Zv_le_Cb' hS hp.vδ hz0)
  have hkey : ∀ x ∈ Vn α', ∀ w ∈ Vn β, w * x * w⁻¹ * x⁻¹ ∈ K2 := by
    intro x hx w hw
    rcases Vn_mem_or hS hp c hbar hdd hvs hθv hw with hwQ | hwQ
    · rw [h1 w hw hwQ x hx]
      exact K2.one_mem
    · have hv0 : v⁻¹ * w ∈ Vn β := mul_mem (inv_mem hv) hw
      have e := h1 _ hv0 hwQ x hx
      have hconj : v⁻¹ * w * x * (v⁻¹ * w)⁻¹ = x := mul_inv_eq_one.mp e
      have e2 : w * x * w⁻¹ * x⁻¹ = v * (v⁻¹ * w * x * (v⁻¹ * w)⁻¹) * v⁻¹ * x⁻¹ := by group
      rw [e2, hconj]
      exact hvx x hx
  have hA : Subgroup.zpowers u ≤ stab β := Subgroup.zpowers_le.mpr hus
  have h2 := c'.card_commSec hA
  rw [c'.bar_zpowers hus, hθu,
    card_commW_of_double (isDoubleSwap_of_mem_Tsub hdT' hd1' hdd')] at h2
  set K := commSec (Subgroup.zpowers u) (Cb β) (Vn β) with hK
  have hCK : Cb β ≤ K := le_sup_right
  have hcard := Subgroup.relIndex_mul_card (H := Cb β) (K := K)
  rw [inf_eq_left.mpr hCK, h2] at hcard
  have hKK2 : K ≤ K2 := by
    refine sup_le (Subgroup.commutator_le.mpr fun w hw y hy => ?_) le_sup_right
    exact hkey y ((Subgroup.zpowers_le.mpr hu) hy) w hw
  have h3 := Subgroup.card_le_of_le hKK2
  have hC : ∀ z ∈ Cb β, ∀ y ∈ Subgroup.zpowers (v * u * v⁻¹ * u⁻¹), y * z = z * y :=
    fun z hz y hy => Vn_comm hS β ((Subgroup.zpowers_le.mpr hc0V) hy) (c'.le hz)
  have h4 := card_sup_le_of_comm hC
  have h5 : Nat.card (Subgroup.zpowers (v * u * v⁻¹ * u⁻¹)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd two_pos
      (orderOf_dvd_of_pow_eq_one ((Std.Vn_isElemAbelian hS β).2 _ hc0V))
  have hpos : 0 < Nat.card (Cb β) := Nat.card_pos
  have h6 : Nat.card K2 ≤ 2 * Nat.card (Cb β) :=
    h4.trans (Nat.mul_le_mul_right _ h5)
  omega

end S35.Lp2

end F53.Stellmacher

end CFSG.Quasithin
