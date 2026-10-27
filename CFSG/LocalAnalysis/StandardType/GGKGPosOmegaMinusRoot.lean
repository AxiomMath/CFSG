module

public import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
import Mathlib.Tactic.Group
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusTorus
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusPosLift
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.SplitTorusSpinMinus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open CFSG.SeitzReduction.SymplecticPilot Multiplicative Matrix
open CFSG.Open
open scoped Matrix

private theorem eq_zero_of_commute_minusPrimeTorus
    {F : Type} [Field F] {p : ℕ} {ζ : Fˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hcomm : ∀ u : Fin 3 → Multiplicative (ZMod p),
      g * omMinusTorusGL hζ u = omMinusTorusGL hζ u * g)
    (l : Fin 3) {a a' : Fin 3 ⊕ Fin 3 ⊕ Fin 2} (haa : a ≠ a')
    (hside : (a = Sum.inl l ∨ a = Sum.inr (Sum.inl l)) ∨
      (a' = Sum.inl l ∨ a' = Sum.inr (Sum.inl l))) :
    (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) a a' = 0 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hκ : ζ * ζ ≠ 1 := by
    intro h
    have hdiv : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa only [pow_two] using h)
    rw [hζo] at hdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  have hχ1 : TableBSymp.zmodPowHom hζ (ofAdd (1 : ZMod p)) = ζ := by
    simpa only [Nat.cast_one, pow_one] using TableBSymp.zmodPowHom_natCast hζ 1
  let u : Fin 3 → Multiplicative (ZMod p) := Pi.mulSingle l (ofAdd (1 : ZMod p))
  have hparam : omMinusTorusParam 3 hζ u = Pi.mulSingle l ζ := by
    funext k
    rw [omMinusTorusParam_apply]
    dsimp only [u]
    by_cases hk : k = l
    · subst k
      rw [Pi.mulSingle_eq_same, hχ1, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hk, map_one, Pi.mulSingle_eq_of_ne hk]
  have hmat := congrArg (fun A : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F =>
    (A : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (hcomm u)
  simp only [Units.val_mul, omMinusTorusGL_apply, kOmMDiag_coe, hparam] at hmat
  have hweights : kOmMWeight F 3 (Pi.mulSingle l ζ) a ≠
      kOmMWeight F 3 (Pi.mulSingle l ζ) a' :=
    hside.elim (kOmMWeight_mulSingle_ne hκ l haa)
      (fun h => (kOmMWeight_mulSingle_ne hκ l haa.symm h).symm)
  exact TableBOrth.eq_zero_of_commute_diagonal hmat hweights

theorem centralizer_spinMinus_splitPrimeTorus
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    let e := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by decide : 4 ≤ 4) hirr
    let T := e.symm.toMonoidHom.comp (omMinusTorus b c hζ (m := 3))
    Subgroup.centralizer (T.range : Set (spinGroup (quadMinus 4 F b c))) =
      ggTorus (minusDatum 4 hirr) := by
  dsimp only
  let Q := quadMinus 4 F b c
  let e := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by decide : 4 ≤ 4) hirr
  let T := e.symm.toMonoidHom.comp (omMinusTorus b c hζ (m := 3))
  have hmatT (u : Fin 3 → Multiplicative (ZMod p)) :
      spinMatrix Q (T u) = omMinusTorusGL hζ u :=
    congrArg (fun A : StatedOmega (StatedQuadMinus 4 F b c) =>
      (A : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (e.apply_symm_apply (omMinusTorus b c hζ u))
  have hcomm (g : spinGroup Q)
      (hg : g ∈ Subgroup.centralizer (T.range : Set (spinGroup Q)))
      (u : Fin 3 → Multiplicative (ZMod p)) :
      spinMatrix Q g * omMinusTorusGL hζ u = omMinusTorusGL hζ u * spinMatrix Q g := by
    have h := Subgroup.mem_centralizer_iff.mp hg (T u) ⟨u, rfl⟩
    have h' := congrArg (spinMatrix Q) h.symm
    simpa only [map_mul, hmatT] using h'
  have hoff (g : spinGroup Q)
      (hg : g ∈ Subgroup.centralizer (T.range : Set (spinGroup Q))) (l : Fin 3)
      {a a' : Fin 3 ⊕ Fin 3 ⊕ Fin 2} (haa : a ≠ a')
      (hside : (a = Sum.inl l ∨ a = Sum.inr (Sum.inl l)) ∨
        (a' = Sum.inl l ∨ a' = Sum.inr (Sum.inl l))) :
      (spinMatrix Q g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) a a' = 0 :=
    eq_zero_of_commute_minusPrimeTorus hp hp2 hζ hζo _ (hcomm g hg) l haa hside
  have hvec (g : spinGroup Q)
      (hg : g ∈ Subgroup.centralizer (T.range : Set (spinGroup Q))) :
      ∀ i s, ∃ a : Fˣ, spinAction Q g (minusVec 4 i s) = (a : F) • minusVec 4 i s := by
    intro i s
    let j : Fin 3 ⊕ Fin 3 ⊕ Fin 2 := if s then Sum.inl i else Sum.inr (Sum.inl i)
    have hj : j = Sum.inl i ∨ j = Sum.inr (Sum.inl i) := by cases s <;> simp [j]
    have hcol : ∀ k, k ≠ j →
        (spinMatrix Q g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) k j = 0 :=
      fun k hk => hoff g hg i hk (Or.inr hj)
    have hnonzero :
        (spinMatrix Q g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) j j ≠ 0 := by
      obtain ⟨k, hk⟩ := ReflSp.exists_ne_zero_col (spinMatrix Q g) j
      by_cases hkj : k = j
      · simpa only [hkj] using hk
      · exact False.elim (hk (hcol k hkj))
    let a : Fˣ := Units.mk0
      ((spinMatrix Q g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) j j) hnonzero
    refine ⟨a, ?_⟩
    have hjvec : minusVec 4 i s = Pi.single j (1 : F) := by cases s <;> rfl
    rw [hjvec, ← spinMatrix_mulVec Q g (Pi.single j (1 : F))]
    funext k
    simp only [Matrix.mulVec_single, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hkj : k = j
    · subst k
      simp [a]
    · simpa [hkj] using hcol k hkj
  have hplane (g : spinGroup Q)
      (hg : g ∈ Subgroup.centralizer (T.range : Set (spinGroup Q))) :
      ∀ v : Fin 2 → F, ∃ w : Fin 2 → F, spinAction Q g (planeVec 4 v) = planeVec 4 w := by
    intro v
    let w := (spinMatrix Q g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).submatrix
      (kOmMPlaneEmb 3) (kOmMPlaneEmb 3) *ᵥ v
    have hplaneEq (p : Fin 2 → F) : planeVec 4 p = kOmMPlaneVec 3 p := by
      funext k
      rcases k with i | i | k <;> simp [planeVec, kOmMPlaneVec]
    refine ⟨w, ?_⟩
    rw [← spinMatrix_mulVec Q g (planeVec 4 v)]
    rw [hplaneEq v, hplaneEq w]
    refine kOmM_mulVec_planeVec (fun k j hk => ?_) v
    rcases k with i | i | k
    · exact hoff g hg i (by simp [kOmMPlaneEmb]) (Or.inl (Or.inl rfl))
    · exact hoff g hg i (by simp [kOmMPlaneEmb]) (Or.inl (Or.inr rfl))
    · exact False.elim (hk ⟨k, rfl⟩)
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · exact ClassicalPosition.mem_ggTorus_minusDatum_of_frame_lines hirr g
      (hvec g hg) (hplane g hg) (hplane g⁻¹ (inv_mem hg))
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have ht : T u ∈ ggTorus (minusDatum 4 hirr) :=
      ClassicalPosition.spinMinus_splitTorus_mem_ggTorus (by decide : 3 ≤ 3) hirr hζ u
    have hct := minusDatum_isCTGroupDatum 4 hirr (by decide : 4 ≤ 4)
    have hext := minusDatum_steinbergExtras 4 hirr
    have hBU := CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras
      (n := 4) hirr (by decide : 4 ≤ 4)
    rw [ggStdPos_ggTorus_eq hct hext hBU] at hg ht
    exact Subgroup.mem_centralizer_iff.mp
      (CFSG.LieType.TitsSimplicity.iSup_le_centralizer_iSup hext hg) _ ht

end CFSG.StandardType
