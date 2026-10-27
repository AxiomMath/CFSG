module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpWeylOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Rep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuClosure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic
open CFSG.StandardType CFSG.Open CFSG.Quasithin.SmithCurtis

theorem exists_spinRep_statedSp :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module (ZMod 2) V₀) (_ : Finite V₀)
      (ρ₀ : Representation (ZMod 2) (StatedSp 3 (ZMod 2)) V₀), IsSimpleRep ρ₀ ∧
        Module.finrank (ZMod 2) V₀ = 8 := by
  obtain ⟨V₀, instA, instM, instF, ρ₀, hs₀, hd₀⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_spinRep
  refine ⟨V₀, instA, instM, instF,
    ρ₀.comp (CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis.g6Equiv.symm).toMonoidHom,
    ?_, hd₀⟩
  exact (isSimpleRep_comp_iff ρ₀
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis.g6Equiv.symm).surjective).mpr hs₀

private theorem spToStd_weylAction_spWeight2 {S : Finset (Fin 3)}
    {w : (coxeterMatrix (isFiniteType_cartanC 3)).Group} {π : Equiv.Perm (Fin 3)}
    {s : Fin 3 → ℤ} (h : SpRealizes 3 w π s) :
    toStd 3 (weylAction (isFiniteType_cartanC 3) w (spWeight2 S)) =
      fun b => 2 * spAct π s (spTypeVec S) b := by
  rw [h (spWeight2 S)]
  have hstd : toStd 3 (spWeight2 S) = fun a => 2 * spTypeVec S a :=
    toStd_spFromStd2 3 (spTypeVec S)
  rw [hstd]
  funext b
  simp only [spAct]
  ring

private theorem exists_nine_orbit_of_spAct {S : Finset (Fin 3)}
    (h : ∃ (σ : Fin 9 → Equiv.Perm (Fin 3)) (t : Fin 9 → Fin 3 → ℤ),
      (∀ i, SpIsSign (t i)) ∧
        Function.Injective (fun i => spAct (σ i) (t i) (spTypeVec S))) :
    ∃ u : Fin 9 → Fin 3 → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanC 3) w (spWeight2 S)) ∧
        Function.Injective u := by
  obtain ⟨σ, t, ht, hinj⟩ := h
  choose w hw using fun i => exists_spRealizes_of_spIsSign (σ i) (ht i)
  refine ⟨fun i => weylAction (isFiniteType_cartanC 3) (w i) (spWeight2 S), ?_, ?_⟩
  · intro i
    exact ⟨w i, rfl⟩
  · intro i j hij
    apply hinj
    have key := congrArg (toStd 3) hij
    rw [spToStd_weylAction_spWeight2 (S := S) (h := hw i),
      spToStd_weylAction_spWeight2 (S := S) (h := hw j)] at key
    funext b
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key b)

private theorem spWitness_nine_singletonOne :
    ∃ (σ : Fin 9 → Equiv.Perm (Fin 3)) (t : Fin 9 → Fin 3 → ℤ),
      (∀ i, SpIsSign (t i)) ∧
        Function.Injective (fun i => spAct (σ i) (t i) (spTypeVec ({1} : Finset (Fin 3)))) := by
  have hc : spTypeVec ({1} : Finset (Fin 3)) = ![1, 1, 0] := by decide
  let σ : Fin 9 → Equiv.Perm (Fin 3) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _,
      Equiv.swap 0 2, Equiv.swap 0 2, Equiv.swap 0 2, Equiv.swap 0 2, Equiv.swap 1 2]
  let t : Fin 9 → Fin 3 → ℤ :=
    ![1, spSgn 0, spSgn 1, spSgnOn ({0, 1} : Finset (Fin 3)),
      1, spSgn 0, spSgn 1, spSgnOn ({0, 1} : Finset (Fin 3)), 1]
  refine ⟨σ, t, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [t, spIsSign_one, spIsSign_spSgn, spIsSign_spSgnOn]
  · rw [hc]
    simp only [σ, t]
    decide

private theorem spWitness_nine_pairZeroOne :
    ∃ (σ : Fin 9 → Equiv.Perm (Fin 3)) (t : Fin 9 → Fin 3 → ℤ),
      (∀ i, SpIsSign (t i)) ∧
        Function.Injective
          (fun i => spAct (σ i) (t i) (spTypeVec ({0, 1} : Finset (Fin 3)))) := by
  have hc : spTypeVec ({0, 1} : Finset (Fin 3)) = ![2, 1, 0] := by decide
  let σ : Fin 9 → Equiv.Perm (Fin 3) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _,
      Equiv.swap 0 1, Equiv.swap 0 1, Equiv.swap 0 1, Equiv.swap 0 1, Equiv.swap 0 2]
  let t : Fin 9 → Fin 3 → ℤ :=
    ![1, spSgn 0, spSgn 1, spSgnOn ({0, 1} : Finset (Fin 3)),
      1, spSgn 0, spSgn 1, spSgnOn ({0, 1} : Finset (Fin 3)), 1]
  refine ⟨σ, t, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [t, spIsSign_one, spIsSign_spSgn, spIsSign_spSgnOn]
  · rw [hc]
    simp only [σ, t]
    decide

private theorem spWitness_nine_pairZeroTwo :
    ∃ (σ : Fin 9 → Equiv.Perm (Fin 3)) (t : Fin 9 → Fin 3 → ℤ),
      (∀ i, SpIsSign (t i)) ∧
        Function.Injective
          (fun i => spAct (σ i) (t i) (spTypeVec ({0, 2} : Finset (Fin 3)))) := by
  have hc : spTypeVec ({0, 2} : Finset (Fin 3)) = ![2, 1, 1] := by decide
  let σ : Fin 9 → Equiv.Perm (Fin 3) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _,
      Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.swap 0 2]
  let t : Fin 9 → Fin 3 → ℤ :=
    ![1, spSgn 0, spSgn 1, spSgn 2, spSgnOn ({0, 1} : Finset (Fin 3)),
      spSgnOn ({0, 2} : Finset (Fin 3)), spSgnOn ({1, 2} : Finset (Fin 3)),
      spSgnOn ({0, 1, 2} : Finset (Fin 3)), 1]
  refine ⟨σ, t, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [t, spIsSign_one, spIsSign_spSgn, spIsSign_spSgnOn]
  · rw [hc]
    simp only [σ, t]
    decide

private theorem spWitness_nine_pairOneTwo :
    ∃ (σ : Fin 9 → Equiv.Perm (Fin 3)) (t : Fin 9 → Fin 3 → ℤ),
      (∀ i, SpIsSign (t i)) ∧
        Function.Injective
          (fun i => spAct (σ i) (t i) (spTypeVec ({1, 2} : Finset (Fin 3)))) := by
  have hc : spTypeVec ({1, 2} : Finset (Fin 3)) = ![2, 2, 1] := by decide
  let σ : Fin 9 → Equiv.Perm (Fin 3) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _,
      Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.swap 0 2]
  let t : Fin 9 → Fin 3 → ℤ :=
    ![1, spSgn 0, spSgn 1, spSgn 2, spSgnOn ({0, 1} : Finset (Fin 3)),
      spSgnOn ({0, 2} : Finset (Fin 3)), spSgnOn ({1, 2} : Finset (Fin 3)),
      spSgnOn ({0, 1, 2} : Finset (Fin 3)), 1]
  refine ⟨σ, t, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [t, spIsSign_one, spIsSign_spSgn, spIsSign_spSgnOn]
  · rw [hc]
    simp only [σ, t]
    decide

private theorem spWitness_nine_triple :
    ∃ (σ : Fin 9 → Equiv.Perm (Fin 3)) (t : Fin 9 → Fin 3 → ℤ),
      (∀ i, SpIsSign (t i)) ∧
        Function.Injective
          (fun i => spAct (σ i) (t i) (spTypeVec ({0, 1, 2} : Finset (Fin 3)))) := by
  have hc : spTypeVec ({0, 1, 2} : Finset (Fin 3)) = ![3, 2, 1] := by decide
  let σ : Fin 9 → Equiv.Perm (Fin 3) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _,
      Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.swap 0 2]
  let t : Fin 9 → Fin 3 → ℤ :=
    ![1, spSgn 0, spSgn 1, spSgn 2, spSgnOn ({0, 1} : Finset (Fin 3)),
      spSgnOn ({0, 2} : Finset (Fin 3)), spSgnOn ({1, 2} : Finset (Fin 3)),
      spSgnOn ({0, 1, 2} : Finset (Fin 3)), 1]
  refine ⟨σ, t, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [t, spIsSign_one, spIsSign_spSgn, spIsSign_spSgnOn]
  · rw [hc]
    simp only [σ, t]
    decide

theorem exists_nine_orbit_spWeight2 {S : Finset (Fin 3)} (hS : S.Nonempty) (hS0 : S ≠ {0})
    (hS2 : S ≠ {2}) :
    ∃ u : Fin 9 → Fin 3 → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanC 3) w (spWeight2 S)) ∧
        Function.Injective u := by
  have hcases : S = {1} ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} ∨ S = {0, 1, 2} := by
    revert S
    decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact exists_nine_orbit_of_spAct (S := {1}) spWitness_nine_singletonOne
  · exact exists_nine_orbit_of_spAct (S := {0, 1}) spWitness_nine_pairZeroOne
  · exact exists_nine_orbit_of_spAct (S := {0, 2}) spWitness_nine_pairZeroTwo
  · exact exists_nine_orbit_of_spAct (S := {1, 2}) spWitness_nine_pairOneTwo
  · exact exists_nine_orbit_of_spAct (S := {0, 1, 2}) spWitness_nine_triple

end CFSG.LocalAnalysis.WeakClosure81
