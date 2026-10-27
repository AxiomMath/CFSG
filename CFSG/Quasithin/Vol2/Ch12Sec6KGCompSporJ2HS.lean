module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSpor
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineSporadic

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem center_eq_bot_of_centralizer_eq_bot {G : Type*} [Group G] {P : Subgroup G}
    (h : Subgroup.centralizer (P : Set G) = ⊥) : Subgroup.center ↥P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : (z : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  rw [h, Subgroup.mem_bot] at hz'
  exact (Subgroup.mem_bot).mpr (Subtype.ext hz')

theorem noTwoCentralNine_j2 :
    NoTwoCentralNine ↥j2P := by
  obtain ⟨-, -, -, hrows, hcov, -, hmap, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  refine noTwoCentralNine_of_reps (R := j2R) le_sup_left card_j2P j2Rows (fun r => tp 315 r.rep)
    (fun r => r.centOrder) hcov (fun r hr => (hrows r hr).2.2.2.2.1) ?_
  intro r hr i hi _
  have hm := List.mem_map_of_mem (f := fun r => (r.outer, r.classSize, r.centOrder)) hr
  rw [hmap] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> omega

theorem exists_elemAbelian_nine_j2P :
    ∃ E : Subgroup ↥j2P, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have e : ↥j2P ≃* NativeSporadic.J2 := j2PermEquiv.symm
  have h : ∃ E : Subgroup NativeSporadic.J2, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨E, hE, hcard⟩ := Id2519.exists_elemAbelian_nine_J2
    exact ⟨E, hE, by rw [hcard]; norm_num⟩
  exact exists_elemAbelian_nine_of_mulEquiv (M := ↥j2P) (M' := NativeSporadic.J2) e h

theorem Conf12626.not_j2
    {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .J2) : False :=
  h.false_of_noTwoCentralNine hQ (e.trans j2PermEquiv)
    (center_eq_bot_of_centralizer_eq_bot j2_centralizer_eq_bot)
    (not_three_dvd_card_outer_of_le_two j2_outer_card_le)
    exists_elemAbelian_nine_j2P
    noTwoCentralNine_j2
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

theorem noTwoCentralNine_hs :
    NoTwoCentralNine ↥hsP := by
  obtain ⟨-, -, -, hrows, hcov, -, hmap, -⟩ := hs_involution_centralizers
  refine noTwoCentralNine_of_reps (R := hsR) le_sup_left card_hsP hsRows
    (fun r => tp 3850 r.rep) (fun r => r.centOrder) hcov (fun r hr => (hrows r hr).2.2.2.2.1) ?_
  intro r hr i hi h2
  have hm := List.mem_map_of_mem (f := fun r => (r.outer, r.classSize, r.centOrder)) hr
  rw [hmap] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] at hi ⊢ <;> omega

theorem exists_elemAbelian_nine_hsP :
    ∃ E : Subgroup ↥hsP, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have e : ↥hsP ≃* NativeSporadic.HS := hsPermEquiv.symm
  have h : ∃ E : Subgroup NativeSporadic.HS, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨E, hE, hcard⟩ := Id2519.exists_elemAbelian_nine_HS
    exact ⟨E, hE, by rw [hcard]; norm_num⟩
  exact exists_elemAbelian_nine_of_mulEquiv (M := ↥hsP) (M' := NativeSporadic.HS) e h

theorem Conf12626.not_hs
    {Q : Type} [Group Q]
    {K L P T : Subgroup Q} {v : Q} (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    (hS : Ch1.SporadicAutInner) (e : ↥K ≃* NativeSporadic.Carrier .HS) : False :=
  h.false_of_noTwoCentralNine hQ (e.trans hsPermEquiv)
    (center_eq_bot_of_centralizer_eq_bot hs_centralizer_eq_bot)
    (not_three_dvd_card_outer_of_le_two hs_outer_card_le)
    exists_elemAbelian_nine_hsP
    noTwoCentralNine_hs
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

end CFSG.Quasithin.H13.S126C
