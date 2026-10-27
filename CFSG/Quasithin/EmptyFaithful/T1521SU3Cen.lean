module

public import CFSG.Quasithin.EmptyFaithful.T1521SU3Base
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.U31521

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Goldschmidt
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

variable {G : Type} [Group G]

theorem exists_center_u3 [Finite G] {L R : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : IsPSU 3 2 n ↥L) (hR : IsSylowTwoOf R L) :
    ∃ Z : Subgroup G, Z ≤ R ∧ IsElemAbelian 2 Z ∧ Nat.card Z = 2 ^ n ∧
      ∀ z, z ∈ Z ↔ z ∈ R ∧ ∀ y ∈ R, z * y = y * z := by
  obtain ⟨e⟩ := nonempty_equiv_psu3_of_isPSU hn hL
  let T : Sylow 2 ↥L := A4.toSylow hR
  have hTmem : ∀ x : ↥L, x ∈ (T : Subgroup ↥L) ↔ (x : G) ∈ R := fun x => Iff.rfl
  obtain ⟨D, hD⟩ := G3a.exists_borelSetup (bender_of_isPSU hn hL) T
  obtain ⟨hZc, -, -⟩ := hD.orders_psu3 hn e
  have hiff : ∀ z : G, z ∈ (sylowCenter (T : Subgroup ↥L)).map L.subtype ↔
      z ∈ R ∧ ∀ y ∈ R, z * y = y * z := by
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxT, hxc⟩ := mem_sylowCenter.mp hx
      refine ⟨(hTmem x).1 hxT, fun y hy => ?_⟩
      have := hxc ⟨y, hR.1 hy⟩ ((hTmem _).2 hy)
      exact (congrArg (fun w : ↥L => (w : G)) this).symm
    · rintro ⟨hzR, hzc⟩
      refine ⟨⟨z, hR.1 hzR⟩, mem_sylowCenter.mpr ⟨(hTmem _).2 hzR, fun t ht => ?_⟩, rfl⟩
      exact Subtype.ext (hzc (t : G) ((hTmem t).1 ht)).symm
  refine ⟨(sylowCenter (T : Subgroup ↥L)).map L.subtype, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, hiff⟩
  · intro z hz
    exact ((hiff z).1 hz).1
  · exact Subtype.ext (((hiff _).1 a.2).2 _ ((hiff _).1 b.2).1)
  · rintro _ ⟨x, hx, rfl⟩
    have := hD.sq x hx
    exact congrArg (fun w : ↥L => (w : G)) this
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact hZc

theorem eq_one_of_central_u3 [Finite G] {L : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : IsPSU 3 2 n ↥L) {x : G} (hx : x ∈ L) (hc : ∀ y ∈ L, x * y = y * x) :
    x = 1 := by
  have h : (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rw [center_eq_bot_of_isPSU hn hL, Subgroup.mem_bot] at h
  exact congrArg (fun w : ↥L => (w : G)) h

end CFSG.Quasithin.U31521
