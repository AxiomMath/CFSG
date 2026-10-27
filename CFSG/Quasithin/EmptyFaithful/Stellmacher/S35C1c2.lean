module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1c1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.IrrSec

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.C1

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem card_map_mk_subgroupOf {G : Type} [Group G] {L U X : Subgroup G} (hUX : U ≤ X)
    [(L.subgroupOf X).Normal] :
    Nat.card ((U.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X))) = L.relIndex U := by
  set K := U.subgroupOf X
  set f := QuotientGroup.mk' (L.subgroupOf X)
  have h1 : K.map f = (f.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1, ← Subgroup.index_ker]
  have h2 : (f.comp K.subtype).ker = (L.subgroupOf X).subgroupOf K := by
    ext x; simp [f, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rw [h2]
  have := Subgroup.relIndex_subgroupOf (H := L) (K := U) (L := X) hUX
  rw [← this]; rfl

variable {G : Type} [Group G] [Finite G]

theorem map_eq_one_of_comm_sec {F L X S₀ U : Subgroup G} (hs : IsSec F L X)
    (θ : ↥F →* Perm (Fin 5)) (hθ : Function.Surjective θ)
    (hk : θ.ker ≤ (cSecIn F L X).subgroupOf F) (e : (secModule hs θ hθ hk).Iso orth)
    (hS₀F : S₀ ≤ F) (hPS : (S₀.subgroupOf F).map θ = S5Syl) (hLU : L ≤ U) (hUX : U ≤ X)
    (hUn : ∀ k ∈ S₀, ∀ u ∈ U, k * u * k⁻¹ ∈ U) (hidx : L.relIndex U = 8) {x : G} (hx : x ∈ S₀)
    (hxU : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ L) : θ ⟨x, hS₀F hx⟩ = 1 := by
  have := hs.normal_subgroupOf
  set M := secModule hs θ hθ hk with hM
  have hsd : SecData M F L X θ (MonoidHom.id hs.W) :=
    CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.secData_secModule hs θ hθ hk
  obtain ⟨Y, hY, hYm⟩ := (hsd.invariant_iff_sub hS₀F hLU hUX).mp hUn
  have hcard : Nat.card Y = 2 ^ 3 := by
    have h1 : Nat.card (Y.map (MonoidHom.id hs.W)) = Nat.card Y :=
      Subgroup.card_map_of_injective Function.injective_id
    have h2 := congrArg (fun K : Subgroup (↥X ⧸ L.subgroupOf X) => Nat.card K) hYm
    exact h1.symm.trans (h2.trans ((card_map_mk_subgroupOf hUX).trans hidx))
  set Y' : Subgroup orth.W := Y.map e.toMulEquiv.toMonoidHom with hY'
  have hinv : IsInvSub orth S5Syl Y' := by
    intro b hb u hu
    obtain ⟨y, hy, rfl⟩ := hu
    rw [← hPS] at hb
    have := hY b hb y hy
    refine ⟨M.act b y, this, ?_⟩
    exact e.map_act b y
  have hc' : Nat.card Y' = 2 ^ 3 := by
    rw [hY', Subgroup.card_map_of_injective e.toMulEquiv.injective]
    exact hcard
  have hσ : θ ⟨x, hS₀F hx⟩ ∈ S5Syl := by
    rw [← hPS]
    exact ⟨⟨x, hS₀F hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  refine eq_one_of_fixes_invSub_card_eight hinv hc' hσ ?_
  rintro _ ⟨y, hy, rfl⟩
  have h2 := (hsd.act_trivial_iff hUX hYm (hS₀F hx)).mp hxU y hy
  show orth.act _ (e.toMulEquiv y) = e.toMulEquiv y
  rw [← e.map_act, h2]

end CFSG.Quasithin.F53.Stellmacher.S35.C1
