module

public import CFSG.Quasithin.EmptyFaithful.SBc17In
public import CFSG.Quasithin.EmptyFaithful.SBc13J1Aux
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pCoreOf_le_centralizer_of_quasisimple [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) : pCoreOf 2 L ≤ Subgroup.centralizer (L : Set G) := by
  have hcen : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (CFSG.pCore_normal) with h | h
    · exfalso
      have hP : IsPGroup 2 ↥L := by
        have := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
        rw [h] at this
        exact this.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup ↥L) ≃* ↥L).toMonoidHom
          (Subgroup.topEquiv).surjective
      have hn : Group.IsNilpotent ↥L := hP.isNilpotent
      have hsol : Group.IsSolvable ↥L := inferInstance
      have hnt : Nontrivial ↥L := by
        obtain ⟨-, hs, -⟩ := hq
        have := hs.toNontrivial
        exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L).ne hq.1.commutator_eq_top
    · exact h
  intro g hg
  have hgL : g ∈ L := pCoreOf_le 2 L hg
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : (⟨g, hgL⟩ : ↥L) ∈ (pCoreOf 2 L).subgroupOf L := hg
  rw [SBc13.pCoreOf_subgroupOf_eq_pCore_J1] at h1
  have := Subgroup.mem_center_iff.1 (hcen h1) ⟨l, hl⟩
  exact congrArg Subtype.val this

theorem comm_eq_bot_of_perfect {L Y : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hQc : pCoreOf 2 L ≤ Subgroup.centralizer (L : Set G)) (hYc : Y ≤ SBc17.cMod L) :
    ⁅L, Y⁆ = ⊥ := by
  have hLY : ⁅L, Y⁆ ≤ pCoreOf 2 L :=
    Subgroup.commutator_le.2 fun x hx y hy => (SBc17.mem_cMod.1 (hYc hy)).2 x hx
  have h1 : ⁅⁅L, Y⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hLY.trans hQc)
  have h2 : ⁅⁅Y, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Y L]
    exact h1
  have h3 : ⁅⁅L, L⁆, Y⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hperf] at h3

theorem comm_eq_bot_of_component [Finite G] {L Y : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hYc : Y ≤ SBc17.cMod L) : ⁅L, Y⁆ = ⊥ := by
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hq.1
  exact comm_eq_bot_of_perfect hperf (pCoreOf_le_centralizer_of_quasisimple hq) hYc

theorem false_of_comm_eq_bot {L V Y : Subgroup G} (hV : V ≤ Subgroup.normalizer (L : Set G))
    (hLV : ⁅L, V⁆ ≠ ⊥) (hVY : ⁅V, Y⁆ = V) (hLY : ⁅L, Y⁆ = ⊥) : False := by
  have hY : Y ≤ Subgroup.centralizer (L : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hLY
  have hconj : ∀ v ∈ V, ∀ y ∈ Y, v * y * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro v hv y hy
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : v⁻¹ * l * v ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hV hv)) l).1 hl
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 (hY hy) _ hl'
    calc l * (v * y * v⁻¹) = v * ((v⁻¹ * l * v) * y) * v⁻¹ := by group
      _ = v * (y * (v⁻¹ * l * v)) * v⁻¹ := by rw [hc]
      _ = v * y * v⁻¹ * l := by group
  have hVc : V ≤ Subgroup.centralizer (L : Set G) := by
    rw [← hVY]
    refine Subgroup.commutator_le.2 fun v hv y hy => ?_
    have : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := rfl
    rw [this]
    exact mul_mem (hconj v hv y hy) (inv_mem (hY hy))
  apply hLV
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hVc

end CFSG.Quasithin.H23P4
