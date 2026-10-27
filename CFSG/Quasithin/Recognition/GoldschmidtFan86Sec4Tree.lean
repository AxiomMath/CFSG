module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubLong
public import CFSG.Quasithin.Recognition.GoldschmidtFan86OrbitTreeMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubConn
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubPartner

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {T : Track Γ G}
  {a b : ℤ} {H : Subgroup G}

namespace SubgraphProp

theorem orbitLoc (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m) :
    OrbitLoc Γ H (MulAction.orbit ↥H (T.line.vert a)) :=
  fan46_loc T hS F hm

theorem orbitPartner (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m) :
    OrbitPartner Γ (MulAction.orbit ↥H (T.line.vert a)) :=
  orbitPartner_of_orbit fun _ hu _ hw => fan46_partner hS F hm hu hw

theorem orbitConn (hS : SubgraphProp T a b H) (F : FanTree Γ G) :
    OrbitConn Γ (MulAction.orbit ↥H (T.line.vert a)) :=
  fun _ hSA hne hcl => fan46_conn hS F hSA hne hcl

theorem fixSet_orbit_of_arc (hS : SubgraphProp T a b H) {k : ℕ}
    (hfix : ∀ P : Arc Γ (2 * k),
      (∀ i, i ≤ k → P.vert (2 * i) ∈ MulAction.orbit ↥H (T.line.vert a)) →
        ∀ g ∈ H, (∀ i, i ≤ k → g • P.vert (2 * i) = P.vert (2 * i)) →
          ∀ u ∈ MulAction.orbit ↥H (T.line.vert a), g • u = u)
    {c : ℤ} (hc : (c - a) % 2 = 0) {g : G} (hg : g ∈ H)
    (hgc : ∀ i : ℕ, i ≤ k → g • T.line.vert (c + 2 * i) = T.line.vert (c + 2 * i)) :
    g ∈ fixSet G (MulAction.orbit ↥H (T.line.vert a)) := by
  refine hfix (T.line.arc c (2 * k)) (fun i _ => ?_) g hg (fun i hi => ?_)
  · have e : c + ((2 * i : ℕ) : ℤ) = a + 2 * ((c - a) / 2 + i) := by push_cast; omega
    show T.line.vert (c + ((2 * i : ℕ) : ℤ)) ∈ _
    rw [e]
    exact hS.vert_mem_orbit _
  · exact hgc i hi

end SubgraphProp

theorem fan46_three (hS : SubgraphProp T a b H) (F : FanTree Γ G) (hPi : TrackInPi T)
    (h211 : Tutte.TutteTree) (h3 : valence Γ (T.line.vert a) = 3) :
    fixSet G (MulAction.orbit ↥H (T.line.vert a)) = T.fixer ∧ b - a ≤ 8 := by
  have hev := fan_4_3_2 T F hPi hS.tarc
  obtain ⟨m, hm⟩ : ∃ m : ℤ, b - a = 2 * m := ⟨(b - a) / 2, by omega⟩
  obtain ⟨k, hk1, hk5, hfix⟩ := orbitTree_fixes h211 F.isTree F.adj_smul F.loc_finite
    (H := H) (α := T.line.vert a) h3 (hS.orbitLoc F hm) (hS.orbitPartner F hm) (hS.orbitConn F)
  refine ⟨le_antisymm (hS.fixSet_orbit_le_fixer F) fun g hg => ?_, ?_⟩
  · exact hS.fixSet_orbit_of_arc hfix (c := a) (by omega) (hS.sub (T.fixer_le_subFixer a b hg))
      fun i _ => (T.mem_fixer).1 hg _
  · by_contra hcon
    have hkm : (k : ℤ) ≤ m := by omega
    refine hS.not_subFixer_le_fixSet F fun g hg => ?_
    refine hS.fixSet_orbit_of_arc hfix (c := b - 2 * k) (by omega) (hS.sub hg) fun i hi => ?_
    exact (T.mem_subFixer).1 hg _ (by omega) (by omega)

end CFSG.Quasithin.Fan86
