module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35At16B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtR

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.At

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

theorem relIndex_Vn_inf_Qv (hS : Sit H M S) (hp : S34.PD β α') (c : Ch.Chart α') :
    (Vn β ⊓ Qv α').relIndex (Vn β) = Nat.card (c.bar (Vn β)) := by
  rw [card_bar_eq hS c hp.vδ' (PD_Vn_le_stab hS hp).1, ← Subgroup.inf_relIndex_left (H := Vn β)
    (K := Qv α')]

theorem lemma161_aux (hS : Sit H M S)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ))
    (hA : ArcDict H M) (hp : S34.PD β α') (hb : Back H M β α' m γ')
    (hZβ : Zv β ⊓ Vn α' = ⊥)
    (hnt : ∀ v ∈ Vn β, v ∈ stab α' → secIdx (Subgroup.zpowers v) (Zv α') (Vn α') ≠ 2) :
    False := by
  obtain ⟨c⟩ := exists_chart hS hZ hp.vδ'
  obtain ⟨c'⟩ := exists_chart hS hZ hp.vδ
  have hle : Vn α' ≤ stab β := (PD_Vn_le_stab hS hp).2
  have hle2 : Vn β ≤ stab α' := (PD_Vn_le_stab hS hp).1
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hb.1
  obtain ⟨v, hv, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hp.not_le
  have hvs : v ∈ stab α' := hle2 hv
  have hT : ∀ w, ∀ hw : w ∈ Vn β, c.θ ⟨w, hle2 hw⟩ ∈ That (c.Dl m) := fun w hw =>
    (Back.comm_le hS hA c hp hb hw).1
  have hz : c.θ ⟨v, hvs⟩ = zc (c.Dl m) := by
    rcases That_cases hD (hT v hv) with h1 | h1 | h1
    · exact absurd ((c.ker_iff hS hp.vδ' _).mp h1) hvQ
    · exact h1
    · exfalso
      refine hnt v hv hvs ?_
      rw [c.secIdx_eq_idx hvs]
      exact (idx_orth_eq_two_iff _).mpr h1
  have hRle := PD_comm_le hS hp
  have h1' : ∀ u ∈ Vn α' ⊓ Qv β, ⁅v, u⁆ = 1 := by
    intro u hu
    have h2 : ⁅v, u⁆ ∈ ⁅Vn β, Qv β⁆ := Subgroup.commutator_mem_commutator hv hu.2
    rw [comm_Vn_Qv hS hp.vδ] at h2
    have h3 : ⁅v, u⁆ ∈ Vn α' := (hRle (Subgroup.commutator_mem_commutator hv hu.1)).2
    have : ⁅v, u⁆ ∈ Zv β ⊓ Vn α' := ⟨h2, h3⟩
    rw [hZβ] at this
    exact Subgroup.mem_bot.mp this
  have h4 := four_le_relIndex_Qv hS hp c hD hv hvs hz h1'
  obtain ⟨D', hD', hbar⟩ := exists_That_bar hS hp c' h4
  have hR4 := card_comm_eq_four hS hp hZβ c' hD' hbar
  have hRZ : Zv α' ⊓ ⁅Vn β, Vn α'⁆ = ⊥ := by
    have h5 := c.card_commSec hle2
    have h6 : (Zv α').relIndex (commSec (Vn β) (Zv α') (Vn α')) =
        (Zv α').relIndex ⁅Vn β, Vn α'⁆ := by
      have e : commSec (Vn β) (Zv α') (Vn α') = ⁅Vn β, Vn α'⁆ ⊔ Zv α' := by
        unfold commSec; rw [Subgroup.commutator_comm]
      rw [e]
      exact relIndex_sup_eq_of_comm (Vn_isElemAbelian hS α').1 (hRle.trans inf_le_right)
        (Zv_le_Vn_S5 hS hp.vδ')
    have hsub : Subgroup.zpowers (zc (c.Dl m)) ≤ c.bar (Vn β) := by
      rw [Subgroup.zpowers_le, ← hz]
      exact c.mem_bar_of_mem hv hvs
    have h7 : 4 ≤ Nat.card (commW orth (c.bar (Vn β)) ⊤) := by
      have h8 := Subgroup.card_le_of_le (commW_mono_left' hsub ⊤)
      have hD4 : Nat.card (commW orth (Subgroup.zpowers (zc (c.Dl m))) ⊤) = 4 := by
        rw [← commW_That_eq hD]; exact card_commW_That hD
      rwa [hD4] at h8
    have h9 : 4 ≤ (Zv α').relIndex ⁅Vn β, Vn α'⁆ := by rw [← h6, h5]; exact h7
    have h10 := relIndex_le_card' (Zv α') ⁅Vn β, Vn α'⁆
    exact inf_eq_bot_iff_relIndex.mpr (by omega)
  have hY : Vn β ⊓ Qv α' ≤ fixSecIn (Vn α') (Zv β) (Vn β) := by
    intro y hy
    rw [F53B3.N37.mem_fixSecIn_iff c'.le c'.Vn_le_normalizer_Zv]
    refine ⟨hy.1, fun u hu => ?_⟩
    have h2 : ⁅u, y⁆ ∈ ⁅Vn α', Qv α'⁆ := Subgroup.commutator_mem_commutator hu hy.2
    rw [comm_Vn_Qv hS hp.vδ'] at h2
    have h3 : ⁅u, y⁆ ∈ ⁅Vn β, Vn α'⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hu hy.1
    have : ⁅u, y⁆ ∈ Zv α' ⊓ ⁅Vn β, Vn α'⁆ := ⟨h2, h3⟩
    rw [hRZ, Subgroup.mem_bot] at this
    rw [commutatorElement_def] at this
    rw [this]
    exact (Zv β).one_mem
  have hF : (fixSecIn (Vn α') (Zv β) (Vn β)).relIndex (Vn β) = 4 := by
    rw [c'.relIndex_fixSecIn hle, hbar]
    exact index_fixW_That hD'
  have hFV : fixSecIn (Vn α') (Zv β) (Vn β) ≤ Vn β := Ch.Chart.fixSecIn_le_Vn _
  have hge : 4 ≤ (Vn β ⊓ Qv α').relIndex (Vn β) := by
    have := Subgroup.relIndex_mul_relIndex (Vn β ⊓ Qv α') _ (Vn β) hY hFV
    rw [hF] at this
    have hpos : 0 < ((Vn β ⊓ Qv α').relIndex (fixSecIn (Vn α') (Zv β) (Vn β))) := by
      apply Nat.pos_of_ne_zero
      exact Subgroup.index_ne_zero_of_finite
    omega
  rw [relIndex_Vn_inf_Qv hS hp c] at hge
  have hbarle : c.bar (Vn β) ≤ Subgroup.zpowers (zc (c.Dl m)) := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := (c.mem_bar_iff).mp hg
    have hwv : (w : G) ∈ Vn β := hw
    rcases That_cases hD (hT w hwv) with h1 | h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers _
    · exfalso
      refine hnt w hwv w.2 ?_
      rw [c.secIdx_eq_idx w.2]
      exact (idx_orth_eq_two_iff _).mpr h1
  have hzz : zc (c.Dl m) * zc (c.Dl m) = 1 := zc_mul_self hD
  have hcard : Nat.card (Subgroup.zpowers (zc (c.Dl m))) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hzz)
  have := Subgroup.card_le_of_le hbarle
  omega

theorem claim16a_of_dict (hS : Sit H M S)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ))
    (hA : ArcDict H M) : Claim16a H M := by
  intro β α' hL
  obtain ⟨hp, hnZ⟩ := hL
  have hZβ : Zv β ⊓ Vn α' = ⊥ := inf_eq_bot_of_card_two (hS.cardZ5 β hp.vδ) hnZ
  obtain ⟨m, γ', hm, hγ, d1, d2, -⟩ := PD_geodesic hS hp
  by_contra hno
  refine lemma161_aux hS hZ hA hp ⟨hm, hγ, d1, d2⟩ hZβ ?_
  intro v hv hvs h2
  exact hno ⟨v, hv, hvs, h2⟩

end S35.At

end F53.Stellmacher

end CFSG.Quasithin
