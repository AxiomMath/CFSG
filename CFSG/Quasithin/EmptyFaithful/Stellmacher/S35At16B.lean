module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35At16A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtArc
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.At

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' : Geo H M}

theorem isQuad_bar (hS : Sit H M S) (hp : S34.PD β α') (c : Ch.Chart β) :
    IsQuad (c.bar (Vn α')) := by
  have hle : Vn α' ≤ stab β := (PD_Vn_le_stab hS hp).2
  intro a ha w hw
  obtain ⟨u, hu, rfl⟩ := (c.mem_bar_iff).mp ha
  rw [← c.img_commSec hle] at hw
  obtain ⟨r, hr, rfl⟩ := (c.mem_img_iff').mp hw
  refine (c.comm_mem_iff u r).mp ?_
  have hcen : (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) := by
    have hsub : commSec (Vn α') (Zv β) (Vn β) ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have h1 : ⁅x, (u : G)⁆ ∈ ⁅⁅Vn β, Vn α'⁆, Vn α'⁆ :=
          Subgroup.commutator_mem_commutator hx hu
        rw [(PD_quadratic hS hp).2, Subgroup.mem_bot] at h1
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mp (hS.glob.central β hp.vδ hx).2 (u : G) (hle hu)
    exact hsub hr
  have := (Subgroup.mem_centralizer_iff.mp hcen) u rfl
  show (u : G) * (r : G) * (u : G)⁻¹ * (r : G)⁻¹ ∈ Zv β
  have e : (u : G) * (r : G) * (u : G)⁻¹ * (r : G)⁻¹ = 1 := by
    rw [this]; simp
  rw [e]
  exact (Zv β).one_mem

theorem exists_That_bar (hS : Sit H M S) (hp : S34.PD β α') (c : Ch.Chart β)
    (hd : 4 ≤ (Qv β).relIndex (Vn α')) :
    ∃ D' : Subgroup (Perm (Fin 5)), Nat.card D' = 8 ∧ c.bar (Vn α') = That D' := by
  have hle : Vn α' ≤ stab β := (PD_Vn_le_stab hS hp).2
  have h4 : 4 ≤ Nat.card (c.bar (Vn α')) := by
    rw [card_bar_eq hS c hp.vδ hle]; exact hd
  have hpg : IsPGroup 2 (Vn α') :=
    IsPGroup.to_le (pCoreOf_isPGroup 2 (stab α')) (Vn_le_Qv_self hS α')
  obtain ⟨D', hD', hle'⟩ := exists_sylow_ge (isPGroup_bar c hle hpg)
  exact ⟨D', hD', eq_That_of_quad hD' hle' (isQuad_bar hS hp c) h4⟩

theorem card_comm_eq_four (hS : Sit H M S) (hp : S34.PD β α') (hZβ : Zv β ⊓ Vn α' = ⊥)
    (c : Ch.Chart β) {D' : Subgroup (Perm (Fin 5))} (hD' : Nat.card D' = 8)
    (hbar : c.bar (Vn α') = That D') : Nat.card ↥⁅Vn β, Vn α'⁆ = 4 := by
  have hle : Vn α' ≤ stab β := (PD_Vn_le_stab hS hp).2
  have hRle := PD_comm_le hS hp
  have h1 := c.card_commSec hle
  rw [hbar, card_commW_That hD'] at h1
  have h2 : (Zv β).relIndex (commSec (Vn α') (Zv β) (Vn β)) =
      (Zv β).relIndex ⁅Vn β, Vn α'⁆ :=
    relIndex_sup_eq_of_comm (Vn_isElemAbelian hS β).1 (hRle.trans inf_le_left)
      (Zv_le_Vn_S5 hS hp.vδ)
  have hbot : Zv β ⊓ ⁅Vn β, Vn α'⁆ = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ (hRle.trans inf_le_right)).trans hZβ.le)
  have := (inf_eq_bot_iff_relIndex.mp hbot)
  rw [← this, ← h2, h1]

end S35.At

end F53.Stellmacher

end CFSG.Quasithin
