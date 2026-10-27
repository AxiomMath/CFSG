module

public import CFSG.Quasithin.Background.RonanE114Seven
public import CFSG.Quasithin.Background.RonanE114SevenL35Tr
public import CFSG.Quasithin.Background.RonanE114SevenL35Sol
public import CFSG.Quasithin.Background.RonanE114SevenL35Gen
public import CFSG.Quasithin.Background.RonanE114SevenL35Char

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11
open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Quasithin.RonanE114.Seven
  CFSG.Quasithin.RonanE114.Seven.L35
open scoped MatrixGroups

theorem l35OutSolvablePair : L35OutSolvablePair := by
  intro G _ _ T hSQ hFs hT hFT hP hTL
  set L := CFSG.generalizedFitting G with hL
  haveI : Fact (Nat.Prime 5) := fact_prime_five
  obtain ⟨e⟩ := E2P.Asc80.exists_equiv_psl3 (p := 5) hP
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := SecU1.L3I.exists_ne_comm_psl3 (p := 5)
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h1 := congrArg e h
    simpa using h1
  have hAS := SecE3.almostSimple_generalizedFitting hFs hnab hT.2.1 hFT
  have hLn : L.Normal := hAS.normal
  haveI := hLn
  have hSyl : IsSylowIn 2 (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hT le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  obtain ⟨E, hE⟩ := exists_equiv_conj35 hSyl hP
  let f : SL(3, ZMod 5) →* G := L.subtype.comp E.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp E.symm.injective
  have hfrange : f.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ E.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hfS : S35.map f = T ⊓ L := by
    have h1 : S35.map E.symm.toMonoidHom = (T ⊓ L).subgroupOf L := by
      rw [← hE, Subgroup.map_map]
      have : E.symm.toMonoidHom.comp E.toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [this, Subgroup.map_id]
    calc S35.map f = (S35.map E.symm.toMonoidHom).map L.subtype := by
          rw [Subgroup.map_map]
      _ = T ⊓ L := by
          rw [h1]
          exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
  let ι : Wreath (2 ^ 2) →* G := f.comp phi35
  have hιinj : Function.Injective ι := hf.comp phi35_injective
  have hιrange : ι.range = T ⊓ L := by
    rw [MonoidHom.range_comp, phi35_range, hfS]
  have hVmap : (modelV sylowS35 e35).map f = (Original.V (2 ^ 2)).map ι := by
    rw [modelV, wreathModelHom_e35, Subgroup.map_map]
  have hBmap : (modelBase sylowS35 e35).map f = (baseSubgroup (2 ^ 2)).map ι := by
    rw [modelBase, wreathModelHom_e35, Subgroup.map_map]
  have hTX : T ≤ Subgroup.normalizer (((modelV sylowS35 e35).map f : Subgroup G) : Set G) := by
    intro t ht
    rw [hVmap]
    exact mem_normalizer_map_of_characteristic ι hιinj original_V_characteristic_four
      (by rw [hιrange]; exact mem_normalizer_inf_of_mem hLn ht)
  have hTY : T ≤ Subgroup.normalizer (((modelBase sylowS35 e35).map f : Subgroup G) : Set G) := by
    intro t ht
    rw [hBmap]
    exact mem_normalizer_map_of_characteristic ι hιinj (base_characteristic (2 ^ 2) (by norm_num))
      (by rw [hιrange]; exact mem_normalizer_inf_of_mem hLn ht)
  have hq : IsPGroup 2 (G ⧸ L) := hAS.isPGroup_quotient
  have hXs : Group.IsSolvable ↥(Subgroup.normalizer
      (((modelV sylowS35 e35).map f : Subgroup G) : Set G)) :=
    isSolvable_normalizer_map_of_range_normal hq f hf hfrange isSolvable_normalizer_modelV35
  have hYs : Group.IsSolvable ↥(Subgroup.normalizer
      (((modelBase sylowS35 e35).map f : Subgroup G) : Set G)) :=
    isSolvable_normalizer_map_of_range_normal hq f hf hfrange
      (isSolvable_normalizer_modelBase 2 le_rfl sylowS35 e35)
  set X := Subgroup.normalizer (((modelV sylowS35 e35).map f : Subgroup G) : Set G) with hX
  set Y := Subgroup.normalizer (((modelBase sylowS35 e35).map f : Subgroup G) : Set G) with hY
  have hS35 : ∀ x ∈ S35, f x ∈ T := fun x hx => by
    have : f x ∈ S35.map f := Subgroup.mem_map_of_mem f hx
    rw [hfS] at this
    exact this.1
  have hK : (X ⊔ Y).comap f = ⊤ := by
    refine eq_top_of_mem_gens _ ?_ ?_ ?_ ?_ ?_
    · exact Subgroup.mem_comap.mpr
        (Subgroup.mem_sup_left (hTX (hS35 _ (Subgroup.subset_closure (by simp)))))
    · exact Subgroup.mem_comap.mpr
        (Subgroup.mem_sup_left (hTX (hS35 _ (Subgroup.subset_closure (by simp)))))
    · exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right
        (Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f p23_mem_normalizer35)))
    · exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right
        (Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f c3_mem_normalizer35)))
    · exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_left
        (Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f x1_mem_normalizer35)))
  refine ⟨X, Y, hTX, hTY, hXs, hYs, ?_⟩
  rw [eq_top_iff, ← hFT]
  refine sup_le ?_ (hTX.trans le_sup_left)
  intro l hl
  rw [← hfrange] at hl
  obtain ⟨γ, rfl⟩ := hl
  have : γ ∈ (X ⊔ Y).comap f := by rw [hK]; trivial
  exact this

section Main


theorem clause_seven (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∀ (s : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 s p 1 ↥(CFSG.generalizedFitting G) →
      E1.nParam (⊤ : Subgroup G) = 1 :=
  clause_seven_of l35OutSolvablePair G T hSQ hFs hT hFT

end Main

end CFSG.Quasithin.RonanE114
