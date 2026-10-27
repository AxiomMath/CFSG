module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveGeo
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveFin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Twelve

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}
variable {α' ν β l : Geo H M}

theorem Data.Zv_inf_Qv_le_edge (hA : F53Amalgam H M S) (d : Data α α' ν β l) :
    Zv l ⊓ Qv β ≤ stab α ⊓ stab β := fun _ hu =>
  ⟨d.Qv_beta_le hA hu.2, pCoreOf_le 2 _ hu.2⟩

theorem Data.ψ_mem_S5That (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 4 ≤ bMin H M) (d : Data α α' ν β l)
    (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {u : G} (hu : u ∈ Zv l ⊓ Qv β) :
    D.ψ ⟨u, d.Qv_beta_le hA hu.2⟩ ∈ S5That := by
  have hY : u ∈ Subgroup.centralizer (Yv β : Set G) := d.Zv_le_centralizer_Yv hA hs ho hb hu.1
  rw [hs.Yv_eq_comm_comm hA h26 (Core.vtype_beta hs d.hβ) (nbrs_symm d.hβ)] at hY
  exact (D.mem_centralizer_Y_iff ⟨u, d.Qv_beta_le hA hu.2⟩).mp
    ⟨d.Zv_inf_Qv_le_edge hA hu, hY⟩

theorem Data.comm_mem_Qv_of_not_swap (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb : 4 ≤ bMin H M) (d : Data α α' ν β l)
    (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {u : G} (hu : u ∈ Zv l ⊓ Qv β)
    (huQ : u ∉ Qv α) (hsw : ¬ (D.ψ ⟨u, d.Qv_beta_le hA hu.2⟩).IsSwap) :
    ∀ g ∈ stab α ⊓ stab β, ⁅u, g⁆ ∈ Qv α := by
  intro g hg
  have hT := (mem_S5That_iff _).mp (d.ψ_mem_S5That hA h26 hs ho hb D hu)
  have h1 : D.ψ ⟨u, d.Qv_beta_le hA hu.2⟩ ≠ 1 := fun h => huQ ((D.ker_iff _).mp h)
  have hz := eq_z_of_mem_S5ThatF hT h1 hsw
  have hgS := (mem_S5Syl_iff _).mp (D.ψ_mem_S5Syl hg)
  have hcomm := z_commute _ hgS
  have hmem : ⁅u, g⁆ ∈ stab α :=
    (stab α).mul_mem ((stab α).mul_mem ((stab α).mul_mem (d.Qv_beta_le hA hu.2) hg.1)
      ((stab α).inv_mem (d.Qv_beta_le hA hu.2))) ((stab α).inv_mem hg.1)
  have e : (⟨⁅u, g⁆, hmem⟩ : ↥(stab α)) =
      ⁅(⟨u, d.Qv_beta_le hA hu.2⟩ : ↥(stab α)), (⟨g, D.S_le hg⟩ : ↥(stab α))⁆ :=
    Subtype.ext rfl
  refine (D.ker_iff ⟨⁅u, g⁆, hmem⟩).mp ?_
  rw [e, map_commutatorElement, hz, commutatorElement_eq_one_iff_mul_comm]
  exact hcomm.symm

end Twelve

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
