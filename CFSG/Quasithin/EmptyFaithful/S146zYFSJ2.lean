module

public import CFSG.Quasithin.EmptyFaithful.S146zYFSBase
public import CFSG.Quasithin.Background.E2TwoProofSporJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Sporadic.J2
public import Certificates.Certificate3139
public import Certificates.Certificate4142
public import Certificates.Certificate7125
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Quasithin.E2P.SporB CFSG.Sporadic.J2

theorem j2_S_sylow :
    IsSylowTwoOf j2Ctx.S ⊤ := by
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  have hN : j2Ctx.D.O.lbl.size = 4725 := j2_O_size
  refine K1.isSylowTwoOf_top_iff.mpr ⟨j2Ctx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index j2Ctx.S
  rw [j2Ctx.S_card, j2Ctx.hΓ, hN] at h1
  have h2 : j2Ctx.S.index = 4725 := by
    have : j2Ctx.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem j2_overgroups
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .J2)) {T Z : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hTZ : T ≤ Z) :
    Z = ⊤ ∨ Nat.card Z = 2 ^ 7 ∨ Nat.card Z = 3 * 2 ^ 7 ∨ Nat.card Z = 9 * 2 ^ 7 ∨
      Nat.card Z = 15 * 2 ^ 7 := by
  obtain ⟨e⟩ := hX
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  let mems : List Mem := (List.range 5).map fun j =>
    ⟨Nat.card (j2Ctx.Y j), Nat.card (CFSG.Open.pCoreOf 2 (j2Ctx.Y j)), Nat.card (j2Ctx.Y j)⟩
  have hall : ∀ Z : Subgroup ↥J, j2Ctx.S ≤ Z → ∃ j ≤ 5, Z = memberOrTop 5 j2Ctx.Y j :=
    lat_all j2Ctx hL
  have hmem : ∀ j < 5, ∃ m ∈ mems, MemStmt (j2Ctx.Y j) m := by
    intro j hj
    refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, rfl, rfl, ?_⟩
    intro N _ _
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card N)
  rcases overgroups_of_lattice j2Ctx.S j2_S_sylow 5 j2Ctx.Y mems hall hmem
      ⟨e.trans nativeEquiv⟩ hT hTZ with h | ⟨m, hm, hZ⟩
  · exact Or.inl h
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
    have hj5 : j < 5 := List.mem_range.mp hj
    have hc := lat_card j2Ctx hL j hj5
    have hk : j2Ctx.k = 7 := rfl
    rw [hk] at hc
    right
    rw [hZ.1, hc]
    interval_cases j <;> simp

theorem facts134Five_j2 :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2) := by
  rintro A _ _ L P T ⟨e⟩ hcfg
  have hL : Nat.card L = 2 ^ 7 * 4725 := by
    rw [Nat.card_congr e.toEquiv]
    exact (CFSG.Sporadic.J2.card_J2).trans (by norm_num)
  obtain ⟨S, Y, hS, hSY, -, hY⟩ := hcfg.exists_sylow_le_of_card (by norm_num) hL
  rcases j2_overgroups ⟨e⟩ hS hSY with htop | h | h | h | h
  · rw [htop, Subgroup.card_top, hL] at hY
    norm_num at hY
  all_goals
    rw [h] at hY
    norm_num at hY

end CFSG.Quasithin.S146zY
