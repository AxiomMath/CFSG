module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.RecognitionClosure
public import Certificates.Certificate272037
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.GoursatKernel

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.CosetTable CFSG.Sporadic.J3 CFSG.Sporadic.Th

theorem card_closure_le_gen {ws : List (List (Fin 7 × Bool))} {N : ℕ}
    (hc : Finite (PG 7 ws) ∧ Nat.card (PG 7 ws) ≤ N) {X : Type*} [Group X] (ρ : Fin 7 → X)
    (h : ∀ w ∈ ws, FreeGroup.lift ρ (FreeGroup.mk w) = 1) :
    Nat.card (Subgroup.closure (Set.range ρ)) ≤ N := by
  obtain ⟨hfin, hc⟩ := hc
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 7) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift ρ r = 1 := by
    rintro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact h w hw
  let φ : PG 7 ws →* X := PresentedGroup.toGroup hrel
  have hrange : φ.range = Subgroup.closure (Set.range ρ) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      {r : FreeGroup (Fin 7) | r ∈ ws.map FreeGroup.mk}, MonoidHom.map_closure]
    congr 1
    ext x
    simp [φ, PresentedGroup.toGroup.of]
  rw [← hrange]
  exact (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective).trans hc

section

theorem card_PG_le_W : Finite (PG 7 j3WordsW) ∧ Nat.card (PG 7 j3WordsW) ≤ 78489 * 1920 :=
  Certificates.certificate272037.1

theorem card_PG_le_J2 : Finite (PG 7 j2Words) ∧ Nat.card (PG 7 j2Words) ≤ 315 * 1920 :=
  Certificates.certificate272037.2.2.1

theorem card_closure_le_W {X : Type*} [Group X] (ρ : Fin 7 → X) (h : SatisfiesJ3WordsW ρ) :
    Nat.card (Subgroup.closure (Set.range ρ)) ≤ 78489 * 1920 :=
  card_closure_le_gen card_PG_le_W ρ h

theorem card_closure_le_J2 {X : Type*} [Group X] (ρ : Fin 7 → X)
    (h : ∀ r ∈ j2Words, FreeGroup.lift ρ (FreeGroup.mk r) = 1) :
    Nat.card (Subgroup.closure (Set.range ρ)) ≤ 315 * 1920 :=
  card_closure_le_gen card_PG_le_J2 ρ h

theorem e6_mem_closure_of_collapse {r : List (Fin 7 × Bool)} (hr : r ∈ collapseRels)
    {X : Type*} [Group X] (ρ : Fin 7 → X)
    (hrest : ∀ w ∈ j3WordsRest, FreeGroup.lift ρ (FreeGroup.mk w) = 1)
    (hr' : FreeGroup.lift ρ (FreeGroup.mk r) = 1) :
    ρ 6 ∈ Subgroup.closure (ρ '' {i : Fin 7 | i.val ≠ 6}) := by
  obtain ⟨-, hcol, -, -⟩ := Certificates.certificate272037
  set ws := j3WordsRest ++ [r] with hws
  have htop := hcol r hr
  have hS : {x : Fin 7 | x ∈ subsetOf 7 [0, 1, 2, 3, 4, 5]} = {i : Fin 7 | i.val ≠ 6} := by
    ext i
    fin_cases i <;> decide
  have hrel : ∀ s ∈ {s : FreeGroup (Fin 7) | s ∈ ws.map FreeGroup.mk}, FreeGroup.lift ρ s = 1 := by
    rintro s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
    rcases List.mem_append.mp hw with h | h
    · exact hrest w h
    · rw [List.mem_singleton.mp h]; exact hr'
  let φ : PG 7 ws →* X := PresentedGroup.toGroup hrel
  have h6 : (PresentedGroup.of (6 : Fin 7) : PG 7 ws) ∈
      genSub {s : FreeGroup (Fin 7) | s ∈ ws.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 3, 4, 5]) := by
    rw [htop]
    trivial
  have := Subgroup.mem_map_of_mem φ h6
  rw [genSub, MonoidHom.map_closure, ← Set.image_comp, hS] at this
  simpa [φ, Function.comp_def, PresentedGroup.toGroup.of] using this

end

section Model

theorem uJ_satisfies_wRel : FreeGroup.lift uJ (FreeGroup.mk (wRel 4 1)) = 1 :=
  Certificates.certificate272037.2.2.2

theorem uJ_satisfies_W : SatisfiesJ3WordsW uJ := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · have : r ∈ j3Words := List.mem_append.mpr (Or.inl h)
    exact uJ_satisfies r this
  · rw [List.mem_singleton.mp h]; exact uJ_satisfies_wRel

end Model

section Recognition

theorem exists_mulEquiv_J3Model_of_generated_W {K : Type*} [Group K] [Finite K] (g : Fin 7 → K)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hrel : SatisfiesJ3WordsW g)
    (hK3 : 3 < Nat.card K) (hZ : ∀ c ∈ Subgroup.center K, c = 1) :
    ∃ Θ : K ≃* J3Model, ∀ i, Θ (g i) = uJ i := by
  have : IsSimpleGroup J3Model := isSimple_J3Model'
  have hfin : Finite J3Model := Nat.finite_of_card_ne_zero (by rw [card_J3Model']; norm_num)
  set f : Fin 7 → K × J3Model := fun i => (g i, uJ i) with hf
  set D : Subgroup (K × J3Model) := Subgroup.closure (Set.range f) with hD
  have hrelD : SatisfiesJ3WordsW f := by
    intro r hr
    have h1 : (MonoidHom.fst K J3Model) (FreeGroup.lift f (FreeGroup.mk r)) =
        FreeGroup.lift g (FreeGroup.mk r) := by
      have : (MonoidHom.fst K J3Model).comp (FreeGroup.lift f) = FreeGroup.lift g := by
        ext i; simp [hf]
      exact congrArg (fun φ => φ (FreeGroup.mk r)) this
    have h2 : (MonoidHom.snd K J3Model) (FreeGroup.lift f (FreeGroup.mk r)) =
        FreeGroup.lift uJ (FreeGroup.mk r) := by
      have : (MonoidHom.snd K J3Model).comp (FreeGroup.lift f) = FreeGroup.lift uJ := by
        ext i; simp [hf]
      exact congrArg (fun φ => φ (FreeGroup.mk r)) this
    refine Prod.ext ?_ ?_
    · simpa [hrel r hr] using h1
    · simpa [uJ_satisfies_W r hr] using h2
  have hcard : Nat.card D ≤ 78489 * 1920 := card_closure_le_W f hrelD
  have hmap₁ : D.map (MonoidHom.fst K J3Model) = ⊤ := by
    rw [hD, MonoidHom.map_closure, ← Set.range_comp]
    simpa [hf, Function.comp_def] using hgen
  have hmap₂ : D.map (MonoidHom.snd K J3Model) = ⊤ := by
    rw [hD, MonoidHom.map_closure, ← Set.range_comp]
    simpa [hf, Function.comp_def] using closure_uJ
  have hs₁ : Function.Surjective (pr₁ D) := by
    intro x
    have : x ∈ D.map (MonoidHom.fst K J3Model) := by rw [hmap₁]; trivial
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨d, hd⟩, rfl⟩
  have hs₂ : Function.Surjective (pr₂ D) := by
    intro x
    have : x ∈ D.map (MonoidHom.snd K J3Model) := by rw [hmap₂]; trivial
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨d, hd⟩, rfl⟩
  have hM := card_J3Model'
  have hlt : Nat.card D < Nat.card K * Nat.card J3Model := by
    rw [hM]
    have : 78489 * 1920 = 3 * 50232960 := by norm_num
    omega
  have hker : Nat.card (pr₂ D).ker ≤ 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pr₂ D).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (pr₂ D) hs₂).toEquiv, hM] at h
    rw [h] at hcard
    have : 50232960 * Nat.card (pr₂ D).ker ≤ 50232960 * 3 := by
      calc 50232960 * Nat.card (pr₂ D).ker ≤ 78489 * 1920 := hcard
        _ = 50232960 * 3 := by norm_num
    exact Nat.le_of_mul_le_mul_left this (by norm_num)
  have hDe : D = Subgroup.closure (Set.range fun i => (g i, uJ i)) := rfl
  rw [hDe] at hs₁ hs₂ hlt hker
  refine exists_mulEquiv_of_closure_pairs (K := K) (M := J3Model) (ι := Fin 7)
    ?_ g uJ ?_ ?_ ?_ ?_ hZ
  · exact nonabelian_J3Model
  · exact hs₁
  · exact hs₂
  · exact hlt
  · exact hker

end Recognition

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
