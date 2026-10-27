module

public import CFSG.Sporadic.Recognition.CoverBootstrap
public import CFSG.Sporadic.Recognition.CoverChainSub
public import CFSG.Sporadic.Recognition.HNMultiplierInputs

public section

namespace CFSG.Sporadic.Recognition.HNMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.Sporadic.Recognition.CoverBootstrap Subgroup

abbrev hnSigma (j : Fin hnS1L.length) : Fin 7 := hnTL.get (hnS1L.get j)

theorem hnSigma_val (j : Fin hnS1L.length) : (hnSigma j).val = j.val := by
  revert j; decide

theorem hnSigma_exists (i : Fin 7) (hi : i.val < 5) : ∃ j, hnSigma j = i := by
  revert i; decide

structure HNGens {X : Type} [Group X] (g : Fin 7 → X) : Prop where
  rels : ∀ r ∈ hnRels, FreeGroup.lift g (FreeGroup.mk r) = 1
  comm : ∀ i, FreeGroup.lift g (FreeGroup.mk (hnCommWord i)) = g i
  gen : Subgroup.closure (Set.range g) = ⊤

theorem toGroup_mk {α G : Type*} [Group G] {f : α → G} {rels : Set (FreeGroup α)}
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (z : FreeGroup α) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels z) = FreeGroup.lift f z := by
  have : (PresentedGroup.toGroup h).comp (PresentedGroup.mk rels) = FreeGroup.lift f :=
    FreeGroup.ext_hom _ _ fun a => by
      simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact PresentedGroup.toGroup.of h
  exact congrArg (fun φ : FreeGroup α →* G => φ z) this

abbrev PC : Type := PG 7 hnCover

abbrev hx : Fin 7 → PC := coverGen hnRels hnCommWord

theorem lift_nested {G : Type*} [Group G] {f : Fin 7 → G} {ws : List (List (Fin 7 × Bool))}
    (hf : ∀ w ∈ ws, FreeGroup.lift f (FreeGroup.mk w) = 1) :
    ∀ r ∈ {r : FreeGroup (Fin hnS1L.length) |
      r ∈ (restrictWords hnS1L (restrictWords hnTL ws)).map FreeGroup.mk},
      FreeGroup.lift (fun j => f (hnSigma j)) r = 1 := by
  have h1 := lift_restrictWords ws hnTL f hf
  exact lift_restrictWords (restrictWords hnTL ws) hnS1L (fun j => f (hnTL.get j))
    (fun w hw => h1 _ (List.mem_map_of_mem hw))

abbrev PC1 : Type := PG hnS1L.length (restrictWords hnS1L (restrictWords hnTL hnCover))

noncomputable def hnIota : PC1 →* PC :=
  PresentedGroup.toGroup (f := fun j => hx (hnSigma j))
    (lift_nested (f := hx) (ws := hnCover) lift_coverGen_eq_one)

theorem range_hnIota :
    hnIota.range = Subgroup.closure (Set.range fun j => hx (hnSigma j)) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 2

section Maps

variable {X : Type} [Group X] {g : Fin 7 → X} (H : HNGens g)

include H

theorem hnCover_eval : ∀ w ∈ hnCover, FreeGroup.lift g (FreeGroup.mk w) = 1 :=
  lift_cover₂_eq_one H.rels H.comm

noncomputable def hnPi : PC →* X :=
  PresentedGroup.toGroup (f := g) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hnCover_eval H w hw

theorem hnPi_hx (i : Fin 7) : hnPi H (hx i) = g i := PresentedGroup.toGroup.of _

noncomputable def hnPsi : PC1 →* X :=
  PresentedGroup.toGroup (f := fun j => g (hnSigma j)) (lift_nested (hnCover_eval H))

theorem pi_iota : (hnPi H).comp hnIota = hnPsi H :=
  PresentedGroup.ext fun j => by
    rw [MonoidHom.comp_apply]
    unfold hnIota hnPsi
    rw [PresentedGroup.toGroup.of, PresentedGroup.toGroup.of]
    exact hnPi_hx H _

theorem range_hnPsi : (hnPsi H).range = Subgroup.closure (Set.range fun j => g (hnSigma j)) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 2
  funext j
  exact PresentedGroup.toGroup.of _

end Maps

theorem hnRelsMid_sub : ∀ r ∈ hnRelsMid, r ∈ hnRels := by
  intro r hr
  simp only [hnRelsMid, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · simp [hnRels, hr]
  · simp [hnRels, hnRels0]

theorem hnRels2_sub : ∀ r ∈ hnRels2, r ∈ hnRels := fun r hr => by simp [hnRels, hr]

theorem hnL2_mem : ∀ w ∈ hnL2, w ∈ restrictWords hnS1L (restrictWords hnTL hnCover) :=
  fun _ hw => mem_restrictWords_of_subset (fun _ hw' => mem_restrictWords_of_subset
    (fun _ hw'' => mem_cover₂Words_of_subset hnRelsMid_sub hw'') hw') hw

theorem hnL1_mem :
    ∀ w ∈ hnL1, w ∈ restrictWords hnS2L (restrictWords hnS1L (restrictWords hnTL hnCover)) :=
  fun _ hw => mem_restrictWords_of_subset (fun _ hw' => mem_restrictWords_of_subset
    (fun _ hw'' => mem_restrictWords_of_subset
      (fun _ hw3 => mem_cover₂Words_of_subset hnRels2_sub hw3) hw'') hw') hw

theorem hnCommWord_sigma (j : Fin hnS1L.length) :
    hnCommWord (hnSigma j) = hnEmbed (hnCommWord5 j) := by
  unfold hnCommWord
  have h : (hnSigma j).val < 5 := by
    rw [hnSigma_val]
    have := j.2
    have h5 := hnS1L_length
    omega
  simp only [h, dite_true]
  congr 2
  exact Fin.ext (hnSigma_val j)

theorem mk_hnCommWord_mem (i : Fin 7) :
    FreeGroup.mk (hnCommWord i) ∈ commutator (FreeGroup (Fin 7)) := by
  unfold hnCommWord
  split_ifs with h
  · have h5 := mk_commWords_mem_commutator
      (m := hnS1L.length) ((hnCommCodes ⟨↑(⟨i.val, by have h5 := hnS1L_length; omega⟩ :
        Fin hnS1L.length), by have h5 := hnS1L_length; omega⟩).map
          fun p => (ofCodes5 p.1, ofCodes5 p.2))
    have := map_mem_commutator (FreeGroup.map hnSigma) h5
    rwa [FreeGroup.map.mk] at this
  · exact mk_commWords_mem_commutator _

abbrev hnH : Subgroup PC := Subgroup.closure (Set.range fun j => hx (hnSigma j))

theorem hx_mem_hnH (i : Fin 7) (hi : i.val < 5) : hx i ∈ hnH := by
  obtain ⟨j, hj⟩ := hnSigma_exists i hi
  rw [← hj]
  exact Subgroup.subset_closure ⟨j, rfl⟩

theorem commutator_hnH : commutator hnH = ⊤ := by
  refine commutator_eq_top_of_commutator_words (fun j => hx (hnSigma j))
    (fun j => FreeGroup.mk (hnCommWord5 j)) (fun j => mk_commWords_mem_commutator _) fun j => ?_
  rw [lift_mk_map hx hnSigma (hnCommWord5 j)]
  change FreeGroup.lift hx (FreeGroup.mk (hnEmbed (hnCommWord5 j))) = _
  rw [← hnCommWord_sigma]
  exact lift_coverGen_commWord (hnSigma j)

section Exact

variable {X : Type} [Group X] {g : Fin 7 → X} (H : HNGens g)

include H

theorem ex_words (hinj : Function.Injective (hnPsi H)) (u : List (Fin hnS1L.length × Bool))
    (hu : FreeGroup.lift (fun j => g (hnSigma j)) (FreeGroup.mk u) = 1) :
    FreeGroup.lift (fun j => hx (hnSigma j)) (FreeGroup.mk u) = 1 := by
  have h1 : hnPsi H (PresentedGroup.mk _ (FreeGroup.mk u)) = 1 := by
    unfold hnPsi
    rw [toGroup_mk]
    exact hu
  have h2 : (PresentedGroup.mk _ (FreeGroup.mk u) : PC1) = 1 := hinj (h1.trans (map_one _).symm)
  have h3 : hnIota (PresentedGroup.mk _ (FreeGroup.mk u)) = 1 := by rw [h2, map_one]
  unfold hnIota at h3
  rw [toGroup_mk] at h3
  exact h3

theorem hnPlain1_eval (hinj : Function.Injective (hnPsi H)) :
    ∀ w ∈ hnPlain1, FreeGroup.lift hx (FreeGroup.mk w) = 1 := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
  have hX : FreeGroup.lift (fun j => g (hnSigma j)) (FreeGroup.mk u) = 1 :=
    lift_nested (ws := hnRels) H.rels _ (List.mem_map_of_mem hu)
  have hP := ex_words H hinj u hX
  rw [lift_mk_map hx hnSigma u] at hP
  exact hP

theorem hnH_inj (hinj : Function.Injective (hnPsi H)) :
    ∀ h ∈ hnH, ∀ h' ∈ hnH, hnPi H h = hnPi H h' → h = h' := by
  intro h hh h' hh' he
  have hh2 : h ∈ hnIota.range := by rw [range_hnIota]; exact hh
  have hh2' : h' ∈ hnIota.range := by rw [range_hnIota]; exact hh'
  obtain ⟨a, rfl⟩ := hh2
  obtain ⟨a', rfl⟩ := hh2'
  have : hnPsi H a = hnPsi H a' := by
    rw [← pi_iota H]
    exact he
  rw [hinj this]

end Exact

end CFSG.Sporadic.Recognition.HNMultiplier
