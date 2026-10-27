module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin10
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L16

open S35.Std S35.Fin S35.At S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' : Geo H M}

omit [Finite G] in
theorem isPGroup_bar2 {δ : Geo H M} (c : Chart2 δ) {A : Subgroup G} (hA : A ≤ stab δ)
    (h : IsPGroup 2 A) : IsPGroup 2 (c.bar A) := by
  have h1 : IsPGroup 2 (A.subgroupOf (stab δ)) :=
    h.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm
  exact h1.map c.θ

omit [Finite G] in
theorem isElemAb_bar2 {δ : Geo H M} (c : Chart2 δ) {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAb (c.bar A) := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := c.mem_bar_iff.mp ha
    rw [← map_mul]
    have : u * u = 1 := Subtype.ext (by simpa [pow_two] using hA.2 u hu)
    rw [this, map_one]
  · obtain ⟨u, hu, rfl⟩ := c.mem_bar_iff.mp ha
    obtain ⟨w, hw, rfl⟩ := c.mem_bar_iff.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (F7.isElemAbelian_comm hA hu hw)

omit [Finite G] in
theorem isQuad_bar2 {δ : Geo H M} (c : Chart2 δ) {A : Subgroup G} (hAs : A ≤ stab δ)
    (hq : ⁅⁅Vn δ, A⁆, A⁆ = ⊥) : IsQuad (c.bar A) := by
  intro a ha w hw
  obtain ⟨u, hu, rfl⟩ := (c.mem_bar_iff).mp ha
  rw [← c.img_commSec hAs] at hw
  obtain ⟨r, hr, rfl⟩ := (c.mem_img_iff').mp hw
  refine (c.comm_mem_iff u r).mp ?_
  have hun : (u : G) ∈ Subgroup.normalizer (Cb δ : Set G) :=
    S34.bl12_stab_le_normalizer_Cb δ u.2
  have hK : commSec A (Cb δ) (Vn δ) ≤ fixSecIn (Subgroup.zpowers (u : G)) (Cb δ) (Vn δ) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro x hx a ha
      have hxa : ⁅x, a⁆ ∈ ⁅Vn δ, A⁆ := Subgroup.commutator_mem_commutator hx ha
      have hV : ⁅x, a⁆ ∈ Vn δ := c.commSec_le_Vn hAs (le_sup_left (a := ⁅Vn δ, A⁆) (b := Cb δ) hxa)
      rw [mem_fixSecIn_zpowers_iff c.Vn_le_normalizer_Cb hun]
      refine ⟨hV, ?_⟩
      have h1 : ⁅⁅x, a⁆, (u : G)⁆ ∈ ⁅⁅Vn δ, A⁆, A⁆ :=
        Subgroup.commutator_mem_commutator hxa hu
      rw [hq, Subgroup.mem_bot] at h1
      have h2 : (u : G) * ⁅x, a⁆ * (u : G)⁻¹ * ⁅x, a⁆⁻¹ = 1 := by
        have := commutatorElement_eq_one_iff_mul_comm.mp h1
        calc (u : G) * ⁅x, a⁆ * (u : G)⁻¹ * ⁅x, a⁆⁻¹
            = (⁅x, a⁆ * (u : G)) * (u : G)⁻¹ * ⁅x, a⁆⁻¹ := by rw [this]
          _ = 1 := by group
      rw [h2]
      exact (Cb δ).one_mem
    · intro z hz
      rw [mem_fixSecIn_zpowers_iff c.Vn_le_normalizer_Cb hun]
      refine ⟨c.le hz, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp hun z).mp hz
      exact (Cb δ).mul_mem this ((Cb δ).inv_mem hz)
  have := hK hr
  rw [mem_fixSecIn_zpowers_iff c.Vn_le_normalizer_Cb hun] at this
  exact this.2

theorem card_bar_eq2 (hS : Sit H M S) {δ : Geo H M} (c : Chart2 δ) (hδ : vtype δ = false)
    {A : Subgroup G} (hA : A ≤ stab δ) : Nat.card (c.bar A) = (Qv δ).relIndex A := by
  have := Subgroup.relIndex_ker (K := A.subgroupOf (stab δ)) c.θ
  rw [c.ker_eq_Qv hS hδ, Subgroup.relIndex_subgroupOf hA] at this
  exact this.symm

end S35.L16

end F53.Stellmacher

end CFSG.Quasithin
