module

public import CFSG.LocalAnalysis.StandardType.GGResSideDatumParabolic
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenWeylLift

public section

namespace CFSG.StandardType
open CFSG.Assembly
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResSideDatum_of_B3_gamma_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs X J : Subgroup G} (hJK : J ≤ X)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNT : GGNoTransvection p Bs) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hW : ∀ n : X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hN).range : Set (MulAut X)) → GGTorusWeylElt p (ggGamma X hN).range n)
    (b : Fin 3) (hb : b = 0 ∨ b = 2)
    (fΓ : (CoxeterMatrix.B 3).Group ≃*
      ↥(ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hN).range))
    (hreflΓ : ∀ i, GGIsReflection p (fΓ ((CoxeterMatrix.B 3).simple i) :
      MulAut (ggGamma X hN).range))
    (hJΓ : ggAutomizer ((J.subgroupOf X).map (MulAut.conj : X →* MulAut X)) (ggGamma X hN).range =
      Subgroup.closure (Set.range fun j : {j : Fin 3 // j ≠ b} =>
        (fΓ ((CoxeterMatrix.B 3).simple j) : MulAut (ggGamma X hN).range))) :
    GGResSideDatum p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  let Φ := ggAutomizerGammaHom hN
  have hΦinj : Function.Injective Φ := ggAutomizerGammaHom_injective hp hBs hNT hN hZ
  have hΦsurj : Function.Surjective Φ := ggAutomizerGammaHom_surjective_of_weyl_normalizers hN hSC hW
  let eΦ := MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  let f : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer X Bs) := fΓ.trans eΦ.symm
  have hfmap (w : (CoxeterMatrix.B 3).Group) : Φ (f w) = fΓ w := eΦ.apply_symm_apply _
  have hAJ : ggAutomizer J Bs ≤ ggAutomizer X Bs := ggAutomizer_mono Bs hJK
  let SJ := (ggAutomizer J Bs).subgroupOf (ggAutomizer X Bs)
  let SG : Subgroup (ggAutomizer X Bs) := Subgroup.closure
    (Set.range fun j : {j : Fin 3 // j ≠ b} => f ((CoxeterMatrix.B 3).simple j))
  let AΓ := ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hN).range
  have hSJmap : (SJ.map Φ).map AΓ.subtype =
      ggAutomizer ((J.subgroupOf X).map (MulAut.conj : X →* MulAut X)) (ggGamma X hN).range :=
    map_ggAutomizerGammaHom_subgroup_of_weyl_normalizers hJK hN hSC hW
  have hSGmap : (SG.map Φ).map AΓ.subtype =
      ggAutomizer ((J.subgroupOf X).map (MulAut.conj : X →* MulAut X)) (ggGamma X hN).range := by
    dsimp only [SG]
    rw [MonoidHom.map_closure, MonoidHom.map_closure, hJΓ]
    congr 1
    ext a
    constructor
    · rintro ⟨u, ⟨v, ⟨j, rfl⟩, rfl⟩, rfl⟩
      exact ⟨j, congrArg Subtype.val (hfmap _).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨Φ (f ((CoxeterMatrix.B 3).simple j)),
        ⟨f ((CoxeterMatrix.B 3).simple j), ⟨j, rfl⟩, rfl⟩, ?_⟩
      exact congrArg Subtype.val (hfmap _)
  have hS : SJ = SG :=
    Subgroup.map_injective (f := Φ) hΦinj
      (Subgroup.map_injective (f := AΓ.subtype) AΓ.subtype_injective (hSJmap.trans hSGmap.symm))
  have hSJval : SJ.map (ggAutomizer X Bs).subtype = ggAutomizer J Bs := by
    ext c
    constructor
    · rintro ⟨cX, hcX, rfl⟩
      exact hcX
    · intro hc
      exact ⟨⟨c, hAJ hc⟩, hc, rfl⟩
  have hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 3 // j ≠ b} => (f ((CoxeterMatrix.B 3).simple j) : MulAut Bs)) := by
    rw [← hSJval, hS]
    dsimp only [SG]
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hrefl : ∀ i, GGIsReflection p (f ((CoxeterMatrix.B 3).simple i) : MulAut Bs) := by
    intro i
    obtain ⟨u, ⟨n, rfl⟩, hn, hau⟩ := mem_ggAutomizer_iff.mp (fΓ ((CoxeterMatrix.B 3).simple i)).2
    have haeq : (fΓ ((CoxeterMatrix.B 3).simple i) : MulAut (ggGamma X hN).range) =
        ggConjAut (ggGamma X hN).range hn := MulEquiv.ext fun a => Subtype.ext (hau a)
    have hra : GGIsReflection p (ggConjAut (ggGamma X hN).range hn) := by
      rw [← haeq]
      exact hreflΓ i
    obtain ⟨g, hgX, hgN, hrg, hover⟩ :=
      exists_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hN (hW n hn) hn hra
    let c : ggAutomizer X Bs := ⟨ggConjAut Bs hgN, ggConjAut_mem_ggAutomizer hgX hgN⟩
    have heq : f ((CoxeterMatrix.B 3).simple i) = c := by
      apply hΦinj
      rw [hfmap]
      apply Subtype.ext
      exact haeq.trans ((ggAutomizerGammaHom_overGamma hN c).unique hover).symm
    rw [heq]
    exact hrg
  exact ggResSideDatum_of_B3_end hp2 hBs hNT b hb f hrefl hJ

end CFSG.StandardType
