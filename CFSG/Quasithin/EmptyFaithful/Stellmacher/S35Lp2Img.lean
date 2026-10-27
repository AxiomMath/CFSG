module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Fin

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

theorem bar_Vn_isElemAb (hS : Sit H M S) (c : Chart2 α') :
    IsElemAb (c.bar (Vn β)) := by
  constructor
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := (c.mem_bar_iff).mp ha
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by simpa using Vn_sq hS β hx)
    rw [this, map_one]
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := (c.mem_bar_iff).mp ha
    obtain ⟨y, hy, rfl⟩ := (c.mem_bar_iff).mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Vn_comm hS β hx hy)

theorem bar_Vn_isQuad (hS : Sit H M S) (hp : S34.PD β α') (c : Chart2 α') :
    IsQuad (c.bar (Vn β)) := by
  have hA : Vn β ≤ stab α' := (Std.PD_Vn_le_stab hS hp).1
  have hRV := Std.PD_comm_le hS hp
  have hle : commSec (Vn β) (Cb α') (Vn α') ≤ fixSecIn (Vn β) (Cb α') (Vn α') := by
    refine sup_le ?_ (c.Cb_le_fixSecIn hA)
    rw [Subgroup.commutator_le]
    intro x hx a ha
    have h1 : ⁅x, a⁆ ∈ ⁅Vn α', Vn β⁆ := Subgroup.commutator_mem_commutator hx ha
    rw [Subgroup.commutator_comm] at h1
    have h2 := hRV h1
    refine (F53B3.N37.mem_fixSecIn_iff c.le c.Vn_le_normalizer_Cb).mpr ⟨h2.2, fun b hb => ?_⟩
    have e : b * ⁅x, a⁆ * b⁻¹ * ⁅x, a⁆⁻¹ = 1 := by
      rw [Vn_comm hS β hb h2.1]
      group
    rw [e]
    exact (Cb α').one_mem
  intro a ha w hw
  rw [← c.img_commSec hA] at hw
  have hw' := c.img_mono hle hw
  rw [c.img_fixSecIn hA] at hw'
  exact hw' a ha

theorem bar_Vn_cases (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (c : Chart2 α') (hU : UC α') :
    c.bar (Vn β) = ⊥ ∨ ∃ d, d ≠ 1 ∧ d * d = 1 ∧ c.bar (Vn β) = Subgroup.zpowers d := by
  refine quad_noswap_cases (bar_Vn_isElemAb hS c) (bar_Vn_isQuad hS hp c) ?_
  intro a ha
  obtain ⟨x, hx, rfl⟩ := (c.mem_bar_iff).mp ha
  exact not_swap_of_neg hS hneg hp c hU hx x.2

theorem exists_d (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Chart2 α') (hU : UC α') :
    ∃ d ∈ Tsub (c.Dl m), d ≠ 1 ∧ d * d = 1 ∧ c.bar (Vn β) = Subgroup.zpowers d := by
  have hbar : c.bar (Vn β) ≠ ⊥ := by
    intro h
    obtain ⟨v, hv, hvQ⟩ := Set.not_subset.mp hp.not_le
    have hvs : v ∈ stab α' := (Std.PD_Vn_le_stab hS hp).1 hv
    have h1 : c.θ ⟨v, hvs⟩ ∈ c.bar (Vn β) := c.mem_bar_of_mem hv hvs
    rw [h, Subgroup.mem_bot] at h1
    exact hvQ ((c.ker_iff hS hp.vδ' ⟨v, hvs⟩).mp h1)
  rcases bar_Vn_cases hS hneg hp c hU with h | ⟨d, hd1, hdd, hd⟩
  · exact absurd h hbar
  · refine ⟨d, ?_, hd1, hdd, hd⟩
    have hdA : d ∈ c.bar (Vn β) := hd ▸ Subgroup.mem_zpowers d
    have hdD : d ∈ c.Dl m := c.bar_mono (back_Vn_le_inf hS hp hb) hdA
    obtain ⟨x, hx, rfl⟩ := (c.mem_bar_iff).mp hdA
    exact mem_Tsub_of_not_swap hdD hdd (not_swap_of_neg hS hneg hp c hU hx x.2)

omit [Finite G] in
theorem exists_pre {d : Perm (Fin 5)} (c : Chart2 α') (hd : c.bar (Vn β) = Subgroup.zpowers d) :
    ∃ v ∈ Vn β, ∃ hvs : v ∈ stab α', c.θ ⟨v, hvs⟩ = d := by
  have : d ∈ c.bar (Vn β) := hd ▸ Subgroup.mem_zpowers d
  obtain ⟨x, hx, hxd⟩ := (c.mem_bar_iff).mp this
  exact ⟨x, hx, x.2, hxd⟩

theorem Vn_mem_or (hS : Sit H M S) (hp : S34.PD β α') (c : Chart2 α') {d : Perm (Fin 5)}
    (hd : c.bar (Vn β) = Subgroup.zpowers d) (hdd : d * d = 1) {v : G} (hvs : v ∈ stab α')
    (hθ : c.θ ⟨v, hvs⟩ = d) {w : G} (hw : w ∈ Vn β) : w ∈ Qv α' ∨ v⁻¹ * w ∈ Qv α' := by
  have hws : w ∈ stab α' := (Std.PD_Vn_le_stab hS hp).1 hw
  have hmem : c.θ ⟨w, hws⟩ ∈ Subgroup.zpowers d := hd ▸ c.mem_bar_of_mem hw hws
  rcases (mem_zpowers_iff_of_mul_self hdd).mp hmem with h | h
  · exact Or.inl ((c.ker_iff hS hp.vδ' ⟨w, hws⟩).mp h)
  · refine Or.inr ?_
    have h1 : c.θ (⟨v, hvs⟩⁻¹ * ⟨w, hws⟩) = 1 := by
      rw [map_mul, map_inv, hθ, h]
      exact inv_mul_cancel _
    exact (c.ker_iff hS hp.vδ' _).mp h1

theorem not_Vn_le_Qv (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Chart2 α') (hU : UC α') : ¬ Vn α' ≤ Qv β := by
  intro hle
  obtain ⟨d, hdT, hd1, hdd, hbar⟩ := exists_d hS hneg hp hb c hU
  obtain ⟨v, hv, hvs, hθ⟩ := exists_pre c hbar
  have hA : Subgroup.zpowers v ≤ stab α' := Subgroup.zpowers_le.mpr hvs
  have h1 := c.card_commSec hA
  rw [c.bar_zpowers hvs, hθ,
    card_commW_of_double (isDoubleSwap_of_mem_Tsub hdT hd1 hdd)] at h1
  set K := commSec (Subgroup.zpowers v) (Cb α') (Vn α') with hK
  have hCK : Cb α' ≤ K := le_sup_right
  have hcard := Subgroup.relIndex_mul_card (H := Cb α') (K := K)
  rw [inf_eq_left.mpr hCK, h1] at hcard
  have hKJ : K ≤ Zv β ⊔ Cb α' := by
    refine sup_le_sup_right ?_ _
    have h2 : ⁅Vn α', Subgroup.zpowers v⁆ ≤ ⁅Qv β, Vn β⁆ :=
      Subgroup.commutator_mono hle (Subgroup.zpowers_le.mpr hv)
    rw [Subgroup.commutator_comm (Qv β) (Vn β), Std.comm_Vn_Qv hS hp.vδ] at h2
    exact h2
  have hst : Vn α' ≤ stab β := (Std.PD_Vn_le_stab hS hp).2
  have hcomm : ∀ c' ∈ Cb α', ∀ y ∈ Zv β, y * c' = c' * y := fun c' hc' y hy =>
    (central_comm hS hp.vδ hy (hst (c.le hc'))).symm
  have h3 := card_sup_le_of_comm hcomm
  have h4 := Subgroup.card_le_of_le hKJ
  rw [hS.cardZ5 β hp.vδ] at h3
  have hpos : 0 < Nat.card (Cb α') := Nat.card_pos
  omega

end S35.Lp2

end F53.Stellmacher

end CFSG.Quasithin
