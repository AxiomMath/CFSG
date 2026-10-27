module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22


theorem w183l312_ordered_inf {Y : Type} [Group Y] {L S S' : Subgroup Y}
    (hshape : IsL2 ↥L 2) (hS : IsSylowIn 2 S L) (hS' : IsSylowIn 2 S' L) (hne : S ≠ S') :
    S ⊓ Subgroup.normalizer (S' : Set Y) = ⊥ := by
  classical
  let X := ↥L
  let P : Subgroup X := S.subgroupOf L
  let P' : Subgroup X := S'.subgroupOf L
  obtain ⟨e⟩ := nonempty_psl_equiv_of_isL2 (r := 2) (by norm_num) hshape
  have hP : CFSG.CGT.Timmesfeld75.IsL2Pair X P (2 ^ 2) := by
    simpa [P] using CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow
      (f := 2) (by norm_num) ⟨e⟩ hS.toSylow
  have hP' : CFSG.CGT.Timmesfeld75.IsL2Pair X P' (2 ^ 2) := by
    simpa [P'] using CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow
      (f := 2) (by norm_num) ⟨e⟩ hS'.toSylow
  have hPP' : P ≠ P' := by
    intro h
    apply hne
    have hPsub : S.subgroupOf L = S'.subgroupOf L := by simpa only [P, P'] using h
    have hinf : S ⊓ L = S' ⊓ L := Subgroup.subgroupOf_inj.mp hPsub
    simpa [inf_eq_left.mpr hS.le, inf_eq_left.mpr hS'.le] using hinf
  obtain ⟨g, hgconj⟩ := hP'.exists_conj_eq_sylow hS.toSylow
  have hgconjP : CFSG.CGT.Timmesfeld75.conjSubgroup g P' = P := by
    simpa [P] using hgconj
  have hg : g ∉ Subgroup.normalizer (P' : Set X) := by
    intro hgn
    have hEq : CFSG.CGT.Timmesfeld75.conjSubgroup g P' = P' :=
      CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq.mp hgn
    exact hPP' (hgconjP.symm.trans hEq)
  have hbot : P ⊓ Subgroup.normalizer (P' : Set X) = ⊥ := by
    rw [inf_comm]
    simpa [hgconjP] using hP'.normalizer_inf_conj_eq_bot hg
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨hyS, hyN⟩ := Subgroup.mem_inf.mp hy
  have hyL : y ∈ L := hS.le hyS
  let x : X := ⟨y, hyL⟩
  have hxP : x ∈ P := by
    change y ∈ S
    exact hyS
  have hxN : x ∈ Subgroup.normalizer (P' : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hz := (Subgroup.mem_normalizer_iff.mp hyN) (z : Y)
    change z ∈ S'.subgroupOf L ↔
      ⟨y, hyL⟩ * z * ⟨y, hyL⟩⁻¹ ∈ S'.subgroupOf L
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hcoe : ((⟨y, hyL⟩ * z * ⟨y, hyL⟩⁻¹ : X) : Y) = y * (z : Y) * y⁻¹ := rfl
    rw [hcoe]
    exact hz
  have hxbot : x ∈ (⊥ : Subgroup X) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hxP, hxN⟩
  have hx1 : x = 1 := Subgroup.mem_bot.mp hxbot
  have hy1 : (⟨y, hyL⟩ : X) = 1 := hx1
  exact Subtype.ext_iff.mp hy1

theorem w183l312_sup_of_sylow {Y : Type} [Group Y] {L S S' : Subgroup Y}
    (hshape : IsL2 ↥L 2) (hS : IsSylowIn 2 S L) (hS' : IsSylowIn 2 S' L) (hne : S ≠ S') :
    S ⊔ S' = L := by
  classical
  let X := ↥L
  let P : Subgroup X := S.subgroupOf L
  let P' : Subgroup X := S'.subgroupOf L
  obtain ⟨e⟩ := nonempty_psl_equiv_of_isL2 (r := 2) (by norm_num) hshape
  have hP : CFSG.CGT.Timmesfeld75.IsL2Pair X P (2 ^ 2) := by
    simpa [P] using CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow
      (f := 2) (by norm_num) ⟨e⟩ hS.toSylow
  have hPP' : P ≠ P' := by
    intro h
    apply hne
    have hPsub : S.subgroupOf L = S'.subgroupOf L := by simpa only [P, P'] using h
    have hinf : S ⊓ L = S' ⊓ L := Subgroup.subgroupOf_inj.mp hPsub
    simpa [inf_eq_left.mpr hS.le, inf_eq_left.mpr hS'.le] using hinf
  have hPQ : hS.toSylow ≠ hS'.toSylow := by
    intro h
    apply hPP'
    have := congrArg (fun Q : Sylow 2 X => (Q : Subgroup X)) h
    simpa [P, P'] using this
  have htop : P ⊔ P' = ⊤ := by
    have := hP.sup_sylow_eq_top hPQ
    simpa [P, P'] using this
  calc S ⊔ S' = (P.map L.subtype) ⊔ (P'.map L.subtype) := by
        rw [Subgroup.map_subgroupOf_eq_of_le hS.le,
          Subgroup.map_subgroupOf_eq_of_le hS'.le]
    _ = (P ⊔ P').map L.subtype := (Subgroup.map_sup P P' L.subtype).symm
    _ = (⊤ : Subgroup X).map L.subtype := by rw [htop]
    _ = L := by rw [Subgroup.map_top, Subgroup.range_subtype]


end CFSG.LocalAnalysis.WeakClosure81

end
