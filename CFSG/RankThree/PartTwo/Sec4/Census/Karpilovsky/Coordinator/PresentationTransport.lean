module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Sporadic.Bridge.Common
import all CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PresentationTransport

open CFSG.LieType.Multipliers CFSG.Sporadic.Bridge

theorem IsPresentation.castIdx {n m : ℕ} (h : n = m) {X : Type*} [Group X] {g : Fin n → X}
    {R : Set (FreeGroup (Fin n))} {R' : Set (FreeGroup (Fin m))}
    (hR : R' = FreeGroup.map (Fin.cast h) '' R) (H : IsPresentation g R) :
    IsPresentation (fun i : Fin m => g (Fin.cast h.symm i)) R' := by
  subst h
  have h1 : (FreeGroup.map (Fin.cast rfl) : FreeGroup (Fin n) → FreeGroup (Fin n)) = id := by
    funext x
    have : (Fin.cast rfl : Fin n → Fin n) = id := funext fun i => Fin.cast_eq_self i
    rw [this]
    exact FreeGroup.map.id x
  rw [hR, h1, Set.image_id]
  exact H

theorem natWord_inj : Function.Injective (List.map fun l : Fin 2 × Bool => (l.1.val, l.2)) :=
  List.map_injective_iff.mpr fun x y hxy => by
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (Fin.ext hxy.1) hxy.2

theorem relators_eq {P : TauCeti.GroupPresentation} (e : P.generatorCount = 2)
    {R : List (List (Fin 2 × Bool))}
    (hR : R.map (List.map fun l => (l.1.val, l.2)) = P.relatorLetters) :
    P.relators.map (List.map fun l => (Fin.cast e l.1, l.2)) = R := by
  refine List.map_injective_iff.mpr natWord_inj ?_
  have h1 : (P.relators.map (List.map fun l => (Fin.cast e l.1, l.2))).map
      (List.map fun l : Fin 2 × Bool => (l.1.val, l.2)) = P.relatorLetters := by
    rw [TauCeti.GroupPresentation.relatorLetters_def, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp [Function.comp_def, List.map_map]
  rw [h1, hR]

theorem image_relatorSet_eq {P : TauCeti.GroupPresentation} (e : P.generatorCount = 2)
    {R : List (List (Fin 2 × Bool))}
    (hR : R.map (List.map fun l => (l.1.val, l.2)) = P.relatorLetters) :
    FreeGroup.map (Fin.cast e) '' P.relatorSet = wordSet R := by
  have hrel := relators_eq e hR
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [TauCeti.GroupPresentation.mem_relatorSet_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [← TauCeti.Relator.toWord_toFreeGroup, FreeGroup.map.mk]
    refine List.mem_map.2 ⟨_, ?_, rfl⟩
    rw [← hrel, TauCeti.GroupPresentation.relators_def]
    simp only [List.map_map, List.mem_map]
    exact ⟨t, ht, rfl⟩
  · intro hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [← hrel, TauCeti.GroupPresentation.relators_def] at hw
    simp only [List.map_map, List.mem_map] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    refine ⟨t.toFreeGroup, ?_, ?_⟩
    · rw [TauCeti.GroupPresentation.mem_relatorSet_iff]
      exact ⟨t, ht, rfl⟩
    · rw [← TauCeti.Relator.toWord_toFreeGroup, FreeGroup.map.mk]
      rfl

theorem isPresentation_of_presHom_bijective {P : TauCeti.GroupPresentation}
    (e : P.generatorCount = 2) {R : List (List (Fin 2 × Bool))}
    (hR : R.map (List.map fun l => (l.1.val, l.2)) = P.relatorLetters) {G : Type*} [Group G]
    (img : ℕ → G) (hrel : ∀ v ∈ P.relatorLetters, wordProd img v = 1)
    (hb : Function.Bijective (presHom P img hrel)) :
    IsPresentation (fun i : Fin 2 => img i.val) (wordSet R) := by
  have h : IsPresentation (fun i : Fin P.generatorCount => img i.val) P.relatorSet :=
    IsPresentation.of_bijective (lift_relator P img hrel) hb
  have h' := IsPresentation.castIdx e (R' := wordSet R) (image_relatorSet_eq e hR).symm h
  have hg : (fun i : Fin 2 => img i.val) =
      fun i : Fin 2 => img (Fin.cast e.symm i).val := by
    funext i
    simp
  rw [hg]
  exact h'

theorem lift_g_eq_wordProd {G : Type*} [Group G] (img : ℕ → G) (w : List (Fin 2 × Bool)) :
    FreeGroup.lift (fun i : Fin 2 => img i.val) (FreeGroup.mk w) =
      wordProd img (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [show FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w from rfl, map_mul, ih]
    obtain ⟨i, b⟩ := x
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, ↓reduceIte]
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PresentationTransport
