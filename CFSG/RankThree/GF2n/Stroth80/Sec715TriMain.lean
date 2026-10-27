module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriCoord
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriPair
public import CFSG.RankThree.GF2n.Stroth80.Sec715Triality

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small CFSG.Open CFSG.StandardType.Triality
open scoped Matrix

theorem omega8Triality_of (hA : SmallNFStatement) (hB : NFIsoStatement) :
    Omega8TrialityStatement := by
  intro K _ _ _ hK H _ φ hφ X _ _ _ ρX Y _ _ _ ρY hkerX hkerY hirrX hirrY hdimX hdimY β hβ hβ0
  obtain ⟨σX, hdX⟩ := exists_descends hφ hkerX
  obtain ⟨σY, hdY⟩ := exists_descends hφ hkerY
  have hXirr : Om8Irr8 σX := hdX.irr8 hirrX hdimX
  have hYirr : Om8Irr8 σY := hdY.irr8 hirrY hdimY
  have hβ' : IsEquivBil σX σY β := by
    intro g x y
    obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
    rw [hdX.apply_eq, hdY.apply_eq, natRep_toOm8]
    exact hβ h x y
  obtain ⟨CX, CY, bX, bY, b₀, e, l, hXNF, hYNF, hb₀, he, hCX, hCY, hl, hβl⟩ :=
    tri_pair_data hA hK hXirr hYirr hβ' hβ0
  obtain ⟨hcX, hcY, hc⟩ := clauses_of_coord hK (om8Datum K) hXNF hYNF hb₀ he hCX hCY β hl hβl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨f, hf⟩
    refine tri_no_equiv_pair hA hK hXirr hβ' hβ0 ⟨f, fun g x => ?_⟩
    obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
    rw [hdX.apply_eq, hdY.apply_eq]
    exact hf h x
  · rintro ⟨f, hf⟩
    refine tri_no_equiv_nat_left hA hK hYirr hβ' hβ0 ⟨f, fun g x => ?_⟩
    obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
    rw [hdX.apply_eq, natRep_toOm8]
    exact hf h x
  · rintro ⟨f, hf⟩
    refine tri_no_equiv_nat_right hA hK hXirr hβ' hβ0 ⟨f, fun g y => ?_⟩
    obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
    rw [hdY.apply_eq, natRep_toOm8]
    exact hf h y
  · intro β'' hβ''
    refine tri_hom_scalar hA hK hXirr hYirr hβ' hβ0 β'' fun g x y => ?_
    obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
    rw [hdX.apply_eq, hdY.apply_eq, natRep_toOm8]
    exact hβ'' h x y
  · intro β'' hβ''
    refine tri_no_nonzero_sq hA hK hXirr β'' fun g x x' => ?_
    obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
    rw [hdX.apply_eq, hdX.apply_eq, natRep_toOm8]
    exact hβ'' h x x'
  · intro Z _ _ _ ρZ Z' _ _ _ ρZ' hkerZ hkerZ' hirrZ hirrZ' hdimZ hdimZ' γ hγ hγ0
    obtain ⟨σZ, hdZ⟩ := exists_descends hφ hkerZ
    obtain ⟨σZ', hdZ'⟩ := exists_descends hφ hkerZ'
    have hZirr : Om8Irr8 σZ := hdZ.irr8 hirrZ hdimZ
    have hZ'irr : Om8Irr8 σZ' := hdZ'.irr8 hirrZ' hdimZ'
    have hγ' : IsEquivBil σZ σZ' γ := by
      intro g z z'
      obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
      rw [hdZ.apply_eq, hdZ'.apply_eq, natRep_toOm8]
      exact hγ h z z'
    rcases tri_pair_unique hA hK hB hXNF hYNF hb₀ he hCX hCY hZirr hZ'irr hγ' hγ0 with
      ⟨⟨f, hf⟩, ⟨f', hf'⟩⟩ | ⟨⟨f, hf⟩, ⟨f', hf'⟩⟩
    · refine Or.inl ⟨⟨f, fun h z => ?_⟩, ⟨f', fun h z => ?_⟩⟩
      · have := hf (toOm8 hφ h) z
        rwa [hdZ.apply_eq, hdX.apply_eq] at this
      · have := hf' (toOm8 hφ h) z
        rwa [hdZ'.apply_eq, hdY.apply_eq] at this
    · refine Or.inr ⟨⟨f, fun h z => ?_⟩, ⟨f', fun h z => ?_⟩⟩
      · have := hf (toOm8 hφ h) z
        rwa [hdZ.apply_eq, hdY.apply_eq] at this
      · have := hf' (toOm8 hφ h) z
        rwa [hdZ'.apply_eq, hdX.apply_eq] at this
  · obtain ⟨qX, hqX, hnd⟩ := hcX
    refine ⟨qX, fun h x => ?_, hnd⟩
    have := hqX (toOm8 hφ h) x
    rwa [hdX.apply_eq] at this
  · obtain ⟨qY, hqY, hnd⟩ := hcY
    refine ⟨qY, fun h y => ?_, hnd⟩
    have := hqY (toOm8 hφ h) y
    rwa [hdY.apply_eq] at this
  · intro qX qY hqX hqY hqX0 hqY0
    refine hc qX qY (fun g x => ?_) (fun g y => ?_) hqX0 hqY0
    · obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
      rw [hdX.apply_eq]
      exact hqX h x
    · obtain ⟨h, rfl⟩ := toOm8_surjective hφ g
      rw [hdY.apply_eq]
      exact hqY h y

end CFSG.RankThree.GF2n.Stroth80.Tri

end
