module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddElevenB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem Wn_inf_stab_le_stab_nbr (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M)
    (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ)) {α' ν κ θ β : Geo H M}
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M)
    (_hκ : κ ∈ nbrs ν) (_hdκ : dist α κ + 2 = bMin H M) (_hθ : θ ∈ nbrs κ)
    (_hdθ : dist α θ + 3 = bMin H M) (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) :
    Wn α ⊓ stab ν ≤ stab α' := fun _ hw =>
  Eleven.mem_stab_of_mem_Mab hA h26 hs ho hb5 hc hν hdν hβ hdβ hw
    (Eleven.mem_Mab_of_caseL hA h26 hs ho hb5 hL hc hν hdν hβ hdβ hw)

theorem Wn_inf_stab_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M)
    (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ)) {α' ν κ θ β : Geo H M}
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M)
    (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M) (hθ : θ ∈ nbrs κ)
    (hdθ : dist α θ + 3 = bMin H M) (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) :
    Wn α ⊓ stab α' = Wn α ⊓ stab ν := by
  refine le_antisymm (fun w hw => ⟨hw.1, ?_⟩) (fun w hw => ⟨hw.1,
    Wn_inf_stab_le_stab_nbr hA h26 hs ho hb5 hL hc hν hdν hκ hdκ hθ hdθ hβ hdβ hw⟩)
  have hwα : w ∈ stab α := pCoreOf_le 2 _ (hs.Wn_le_Qv hA (by omega) hw.1)
  set g : ↥(H ⊔ M) := ⟨w, stab_le α hwα⟩
  have hgν : g • ν ∈ nbrs α' := smul_mem_nbrs_of_mem_stab g hw.2 hν
  have hd : dist α (g • ν) = dist α ν := by
    calc dist α (g • ν) = dist (g • α) (g • ν) := by
          rw [smul_eq_of_mem_stab (g := g) hwα]
      _ = dist α ν := CosetGeom.dist_smul g α ν
  exact mem_stab_of_smul_eq
    (Core.eq_of_mem_nbrs_crit hA h26 hs ho hc hν hdν hgν (by rw [hd]; exact hdν))

theorem relIndex_Wn_inf_stab_le_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M)
    (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ)) {α' ν κ θ β : Geo H M}
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M)
    (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M) (hθ : θ ∈ nbrs κ)
    (hdθ : dist α θ + 3 = bMin H M) (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) :
    (Wn α ⊓ stab α').relIndex (Wn α) ≤ 2 := by
  rw [Wn_inf_stab_eq hA h26 hs ho hb5 hL hc hν hdν hκ hdκ hθ hdθ hβ hdβ]
  have hθv : vtype θ = false := by
    obtain ⟨k, hk⟩ := ho
    exact Core.vtype_of_even hA hs ⟨k - 1, by omega⟩
  have hWE : Wn α ≤ stab θ ⊓ stab κ :=
    le_inf ((Wn_le_Qv_of_dist hA hs (by omega)).trans (pCoreOf_le 2 _))
      (Wn_le_stab_of_dist hA hs (by omega))
  have h2 : (Qv κ).relIndex (stab θ ⊓ stab κ) = 2 :=
    Sit43.relIndex_Qv_edge hA hθv (nbrs_symm hθ)
  have hle : Qv κ ⊓ Wn α ≤ Wn α ⊓ stab ν := fun x hx =>
    ⟨hx.2, Qv_le_stab_of_mem_nbrs hA (nbrs_symm hκ) hx.1⟩
  calc (Wn α ⊓ stab ν).relIndex (Wn α) ≤ (Qv κ ⊓ Wn α).relIndex (Wn α) :=
        Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
    _ = (Qv κ).relIndex (Wn α) := Subgroup.inf_relIndex_right _ _
    _ ≤ (Qv κ).relIndex (stab θ ⊓ stab κ) :=
        Subgroup.relIndex_le_of_le_right hWE (by rw [h2]; norm_num)
    _ = 2 := h2

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
