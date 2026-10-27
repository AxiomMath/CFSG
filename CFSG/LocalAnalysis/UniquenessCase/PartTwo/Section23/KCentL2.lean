module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
public import CFSG.Walter.PSL2Facts.EvenAutFixedPoints

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GorensteinWalter

theorem kCentL2_holds : KCentL2 := by
  intro X _ _ a hX θ hθ S hS
  have ha : 1 ≤ a := hX.admissible.2.1
  have hm : CFSG.Open.StatedClassicalModel X .PSL 2 2 a :=
    hX.statedClassicalModel_of_ne_zero (by omega)
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hm
  let Φ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K
  let e : X ≃* PSL2 K := e₀.trans Φ.symm
  let θ' : MulAut (PSL2 K) := MulAut.congr e θ
  have hθ' : Odd (orderOf θ') := by
    rw [show θ' = MulAut.congr e θ from rfl, MulEquiv.orderOf_eq]
    exact hθ
  let S' : Sylow 2 (PSL2 K) :=
    Sylow.mapSurjective (f := (e : X →* PSL2 K)) (hf := e.surjective) S
  have hS'coe : (S' : Subgroup (PSL2 K)) = S.map (e : X →* PSL2 K) :=
    Sylow.coe_mapSurjective (f := (e : X →* PSL2 K)) (hf := e.surjective) S
  have hS' : ∀ x ∈ (S' : Subgroup (PSL2 K)), θ' x ∈ (S' : Subgroup (PSL2 K)) := by
    intro x hx
    rw [hS'coe] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    change θ' (e.toMonoidHom y) ∈ Subgroup.map e.toMonoidHom (S : Subgroup X)
    have hθ'ey : θ' (e.toMonoidHom y) = e.toMonoidHom (θ y) := by
      simp [θ', MulAut.congr_apply]
    rw [hθ'ey]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hS y hy)
  obtain ⟨s, hsdvd, hsodd, ⟨y, hyord, hyfix⟩, hy3⟩ :=
    CFSG.Walter.psl2_even_odd_aut_fixed_points hK θ' hθ' S' hS'
  have hθeq : θ = MulAut.congr e.symm θ' := by
    rw [show θ' = MulAut.congr e θ from rfl]
    ext x
    simp [MulAut.congr_apply]
  refine ⟨s, hsdvd, hsodd, ⟨e.symm y, ?_, ?_⟩, ?_⟩
  · rw [MulEquiv.orderOf_eq, hyord]
  · rw [hθeq]
    simpa [MulAut.congr_apply] using congrArg (fun z => e.symm z) hyfix
  · intro hs1
    obtain ⟨z, hzord, hzfix⟩ := hy3 hs1
    have hθz : θ (e.symm z) = e.symm z := by
      rw [hθeq]
      simpa [MulAut.congr_apply] using congrArg (fun w => e.symm w) hzfix
    exact ⟨e.symm z, by rw [MulEquiv.orderOf_eq, hzord], hθz⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
