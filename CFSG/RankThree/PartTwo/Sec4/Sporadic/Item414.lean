module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Subgroup CFSG.Blueprint
open CFSG.RankThree.Asc83Table (Automizer)

@[expose] def SigB {G : Type} [Group G] [Finite G] (P B : Subgroup G) : Prop :=
  (Nonempty (autIn ⊤ B ≃* GL (Fin 2) (ZMod 3)) →
    invariantPiSubgroups ⊤ B (piOf 2) = {⊥}) ∧
  (Nonempty (autIn ⊤ B ≃* Equiv.Perm (Fin 3)) → gamma 1 B = ⊤ ∧
    ∀ a ∈ B, a ∉ P ⊓ Subgroup.centralizer (P : Set G) →
      (fun x : G => (conjugate (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer {a})) x).map
          (MulAut.conj : G →* MulAut G)) '' (P : Set G) =
        maxInvariantPiSubgroups ⊤ (B.map (MulAut.conj : G →* MulAut G)) (piOf 2))

theorem SigB.map {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G'] (φ : G ≃* G')
    {P B : Subgroup G} (h : SigB P B) : SigB (P.map φ.toMonoidHom) (B.map φ.toMonoidHom) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  · rw [← Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective,
      ← image_invariantPiSubgroups, h1 ⟨(autInTopCongr φ B).trans e⟩, Set.image_singleton,
      Subgroup.map_bot]
  · obtain ⟨hg, hmax⟩ := h2 ⟨(autInTopCongr φ B).trans e⟩
    refine ⟨?_, fun a' ha' hZ' => ?_⟩
    · rw [← map_gamma φ 1 B, hg]
      exact Subgroup.map_top_of_surjective _ φ.surjective
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      have hZ : a ∉ P ⊓ Subgroup.centralizer (P : Set G) := fun h =>
        hZ' (by rw [← map_inf_centralizer]; exact Subgroup.mem_map_of_mem _ h)
      have hm := hmax a ha hZ
      rw [map_map_conj φ B, ← Subgroup.map_top_of_surjective (MulAut.congr φ).toMonoidHom
        (MulAut.congr φ).surjective, ← image_maxInvariantPiSubgroups, ← hm, Set.image_image,
        Subgroup.coe_map, Set.image_image]
      congr 1
      funext x
      rw [MulEquiv.coe_toMonoidHom,
        ← CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore_centralizer 2 φ a,
        ← conjugate_map, map_map_conj]

@[expose] def SigAt {G : Type} [Group G] [Finite G] (P : Subgroup G) : Prop :=
  ∀ B : Subgroup G, B ≤ P → Nat.card B = 9 → SigB P B

theorem SigAt.map {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G'] (φ : G ≃* G')
    {P : Subgroup G} (h : SigAt P) : SigAt (P.map φ.toMonoidHom) := by
  intro B' hB' h9
  have hB : B'.map φ.symm.toMonoidHom ≤ P := by
    have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hB'
    rwa [map_symm_map] at this
  have h9' : Nat.card (B'.map φ.symm.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.symm.injective, h9]
  have := (h _ hB h9').map φ
  rwa [map_map_symm] at this

section Concrete

open CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
open CFSG.GH74.M12.Hyp (G12)

theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem not_gl_of_card {B : Subgroup G12} (h : Nat.card (Automizer B) = 6) :
    ¬ Nonempty (autIn ⊤ B ≃* GL (Fin 2) (ZMod 3)) := by
  rintro ⟨e⟩
  have := Nat.card_congr e.toEquiv
  rw [card_autIn_top, h, CFSG.RankThree.Asc83Table.card_GL23] at this
  omega

theorem not_perm_of_gl {B : Subgroup G12}
    (h : Nonempty (Automizer B ≃* GL (Fin 2) (ZMod 3))) :
    ¬ Nonempty (autIn ⊤ B ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨e⟩
  obtain ⟨f⟩ := h
  have h1 := Nat.card_congr e.toEquiv
  have h2 := Nat.card_congr f.toEquiv
  rw [card_autIn_top, card_perm_three] at h1
  rw [h1, CFSG.RankThree.Asc83Table.card_GL23] at h2
  omega

theorem sigB_E : SigB P0 E :=
  ⟨fun _ => invariant_E, fun h => absurd h (not_perm_of_gl automizer_E)⟩

theorem sigB_F : SigB P0 F :=
  ⟨fun _ => invariant_F, fun h => absurd h (not_perm_of_gl automizer_F)⟩

theorem sigB_A : SigB P0 A := by
  refine ⟨fun h => absurd h (not_gl_of_card card_automizer_A), fun _ => ⟨gamma_A, ?_⟩⟩
  intro a ha hZ
  rw [image_conjugate_pCore ha hZ, maxInvariant_A]

theorem sigB_A' : SigB P0 A' := by
  have h := sigB_A.map (MulAut.conj g0)
  rwa [eq_of_mem_normalizer g0_mem_NP, map_g0_A] at h

theorem sigAt_P0 : SigAt P0 := by
  intro B hB h9
  have hB' : B ∈ ({E, F, A, A'} : Set (Subgroup G12)) := nine_eq ▸ ⟨hB, h9⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB'
  rcases hB' with rfl | rfl | rfl | rfl
  · exact sigB_E
  · exact sigB_F
  · exact sigB_A
  · exact sigB_A'

end Concrete

theorem rank3II_4_14_signalizer : Item4_14_signalizer := by
  intro G _ _ h P B hBP hB9
  refine forall_sylow_of_P0 (fun G _ P => ∀ _ : Finite G, SigAt P) ?_ (fun _ => sigAt_P0) G h P
    inferInstance B hBP hB9
  intro G G' _ _ φ P hP _
  have : Finite G := Finite.of_equiv G' φ.symm.toEquiv
  exact (hP this).map φ

theorem rank3II_4_14 : Item4_14 :=
  ⟨rank3II_4_14_local, rank3II_4_14_signalizer⟩

end CFSG.RankThree.PartTwo.Sec4.Sporadic
