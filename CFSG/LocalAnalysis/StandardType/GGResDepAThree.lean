module

public import CFSG.LocalAnalysis.StandardType.GGResDepAFive
public import CFSG.LocalAnalysis.StandardType.GGDepAOddLarge
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeBasic
public import CFSG.LocalAnalysis.StandardType.GGDepAThreePat
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeSmall
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeSurvivor
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeCells9
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeCells6

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggResDepAThreeInput_of_inputs
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) :
    GGResDepAThreeInput := by
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ⟩ := hP.2
  have hp3 : p = 3 := hP.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hdep : ¬ LinearIndependent (ZMod p) fun i : Λ => h (some i) := hsel
  have htypA : GGIsTypeA ML := htyp
  have hαL : ∀ c : Λ, α (some c) (h (some c)) = 2 := by
    intro c
    have h1 := hL c c
    rw [hCL.1 c] at h1
    simpa using h1
  obtain ⟨N, e, hN3, hpN, hend, hCartan, F⟩ :=
    ggDepA_frame_of_config hFix hp2 hH hxBs hCL htypA hdel hφ hL hdep hAL
  obtain ⟨y', hy'x, hy'α⟩ := ggDepA_y_fixed hp2 hH hxBs hφ hαL hJ
  have hy : ∃ y : V, y ∉ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hxBs⟩)} ∧
      ∀ c : Fin (N - 1), c ≠ e.symm b → α (some (e c)) y = 0 := by
    refine ⟨y', hy'x, ?_⟩
    intro c hc
    exact hy'α (e c) (fun h => hc ((Equiv.symm_apply_apply e c).symm.trans (congrArg e.symm h)))
  have hdim : Module.finrank (ZMod p) V = N := ggDepA_finrank_eq F (e.symm b) hend hy
  have hN6 : 6 ≤ N := ggDepAThree_six_le_N hp3 hH ι F hdim
  obtain ⟨hαa, hw, hjoin, hnt, hcard⟩ :=
    ggDepA_kside hFix hFixK hOrb hp2 hH hxBs hWL hCL hWK hCK hφ hL hK hAL hAK e (by omega) F
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (some (e i)))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φ none)
  have hr : ∀ i v, r i v = v - α (some (e i)) v • h (some (e i)) := fun i v => hφ (some (e i)) v
  have hra : ∀ v, ra v = v - α none v • h none := fun v => hφ none v
  by_cases hN11 : 11 ≤ N
  · exfalso
    exact ggDepAOdd_large_false hKG hp2 hN11 F r hr ra (h none) (α none) hra hαa hjoin hw hnt hcard
  · have hN : N = 6 ∨ N = 9 := by
      have h3 : 3 ∣ N := by rw [← hp3]; exact hpN
      omega
    have hKss : ∀ i j : {i : Λ // i ≠ b},
        (fun i : Fin (N - 1) => α (some (e i))) (e.symm i.1)
          ((fun i : Fin (N - 1) => h (some (e i))) (e.symm j.1)) =
          (CK (some i) (some j) : ZMod p) := by
      intro i j
      simpa using hK (some i) (some j)
    have hJ' : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod 3) =
        (CartanMatrix.A (N - 1) (e.symm i.1) (e.symm j.1) : ZMod 3) := by
      intro i j
      subst hp3
      rw [← hKss i j, F.pair]
    obtain ⟨c0, m, n, hpat, hclause⟩ := ggDepAThree_pattern hN e hend hWK hCK hJ'
    have hpair : ∀ c : Fin (N - 1), c ≠ e.symm b →
        α none (h (some (e c))) = (if c = c0 then (m : ZMod p) else 0) ∧
        α (some (e c)) (h none) = (if c = c0 then (n : ZMod p) else 0) := by
      intro c hc
      have hcb : e c ≠ b := fun h' =>
        hc ((Equiv.symm_apply_apply e c).symm.trans (congrArg e.symm h'))
      let i : {i : Λ // i ≠ b} := ⟨e c, hcb⟩
      have hii : e.symm i.1 = c := by simp [i]
      obtain ⟨h1, h2⟩ := hclause i
      rw [hii] at h1 h2
      have k1 : α none (h (some (e c))) = (CK none (some i) : ZMod p) := by
        simpa [i] using hK none (some i)
      have k2 : α (some (e c)) (h none) = (CK (some i) none : ZMod p) := by
        simpa [i] using hK (some i) none
      constructor
      · rw [k1, h1]
        by_cases hc0 : c = c0 <;> simp [hc0]
      · rw [k2, h2]
        by_cases hc0 : c = c0 <;> simp [hc0]
    have hy' : ∃ y : V, y ∉ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hxBs⟩)} ∧
        ∀ c : Fin (N - 1), c ≠ e.symm b → α (some (e c)) y = 0 := hy
    subst hp3
    rcases hN with rfl | rfl
    · obtain ⟨θ, αa', hθh, hθα, hθx, hαa', hdata⟩ :=
        ggDepAThree_small6 ggDepAThree_cells6 F r hr ra (h none) (α none) hra hαa hw (e.symm b) c0 m
          n hpat hpair hy' hnt
      have hperm := ggDepAThree_stab F r hr
      exact ggDepAThree_survivor_weyl ι F r hr ra (h none) (α none) hra
        (l05nDK3_range_le ι hAL hAK e).symm hperm θ hθh hθα hθx αa' hαa' hdata
    · exact (ggDepAThree_small_false ggDepAThree_cells9 F r hr ra (h none) (α none) hra hαa hw
        (e.symm b) c0 m n hpat hpair hy' hnt).elim

end CFSG.StandardType
