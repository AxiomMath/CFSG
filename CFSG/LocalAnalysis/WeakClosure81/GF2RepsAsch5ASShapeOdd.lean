module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASShape
public import CFSG.LocalAnalysis.WeakClosure81.RankThreePrimePowerBounds
public import CFSG.Quasithin.Background.RonanE114U33
public import CFSG.Quasithin.Background.RonanE114SevenL35Char
public import CFSG.Quasithin.Background.RonanE114SevenL35Gen
public import CFSG.Quasithin.Background.RonanE114SevenL35Sol
public import CFSG.Quasithin.Background.RonanE114SevenL35Tr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11
open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Quasithin.RonanE114
  CFSG.Quasithin.RonanE114.Seven CFSG.Quasithin.RonanE114.Seven.L35
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem exists_solvable_pair_of_psl35 {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) (hP : IsPSL 3 5 1 ↥(CFSG.generalizedFitting G)) :
    ∃ X Y : Subgroup G, T ≤ X ∧ T ≤ Y ∧ Group.IsSolvable ↥X ∧ Group.IsSolvable ↥Y ∧
      X ⊔ Y = ⊤ := by
  set L := CFSG.generalizedFitting G with hL
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := E2P.Asc80.exists_equiv_psl3 (p := 5) hP
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := SecU1.L3I.exists_ne_comm_psl3 (p := 5)
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h1 := congrArg e h
    simpa using h1
  have hAS := SecE3.almostSimple_generalizedFitting hFs hnab hT.2.1 hFT
  have hLn : L.Normal := hAS.normal
  have := hLn
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

theorem nParam_le_one_of_psl3_five {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) (hP : IsPSL 3 5 1 ↥(CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  obtain ⟨X, Y, hX, hY, hXs, hYs, hXY⟩ := exists_solvable_pair_of_psl35 hFs hT hFT hP
  exact SecU1.nParam_le_one_of_solvable_pair hT hX hY hXs hYs hXY

theorem shapeInEAS_l35 : ShapeInEAS 1 (fun X _ => LieModel X .PSL 3 5 1) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ _ hs _ hT hFT hP =>
    (E1.nParam_le_iff Nat.one_pos).mp (by
      exact_mod_cast nParam_le_one_of_psl3_five hs hT hFT
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hP))

theorem shapeInEAS_u33 : ShapeInEAS 1 (fun X _ => LieModel X .PSU 3 3 1) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ _ _ _ hT hFT hP =>
    (E1.nParam_le_iff Nat.one_pos).mp (by
      exact_mod_cast (nParam_eq_one_of_isPSU33
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hP)
        (quasithinIsSylowTwo_of_isSylowInTop hT) hFT).le)

section Wreathed


theorem shapeInEAS_l3_wreathed {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 < p ^ f)
    (hq4 : p ^ f % 4 = 1) : ShapeInEAS 1 (fun X _ => LieModel X .PSL 3 p f) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ _ hs hnab hT hFT hP =>
    (E1.nParam_le_iff Nat.one_pos).mp (by
      exact_mod_cast nParam_le_one_of_lieModel_PSL_three_of_five_lt hp hp2 h5 hq4 hs hnab hP hT
        hFT)

theorem shapeInEAS_u3_wreathed {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 < p ^ f)
    (hq4 : p ^ f % 4 = 3) : ShapeInEAS 1 (fun X _ => LieModel X .PSU 3 p f) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ _ hs hnab hT hFT hP =>
    (E1.nParam_le_iff Nat.one_pos).mp (by
      exact_mod_cast nParam_le_one_of_lieModel_PSU_three_of_five_lt hp hp2 h5 hq4 hs hnab hP hT
        hFT)

end Wreathed

section U3All


theorem shapeInEAS_u3_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ShapeInEAS 1 (fun X _ => LieModel X .PSU 3 p f) := by
  intro L₀ _ _ hs hnab hP A S hAS
  by_cases hf : f = 1
  · subst hf
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (hp.odd_of_ne_two hp2)) with h1 | h3
    · exact shapeInEAS_u3_one hp h1 L₀ hs hnab hP A S hAS
    · by_cases hp3 : p = 3
      · subst hp3
        exact shapeInEAS_u33 L₀ hs hnab hP A S hAS
      · have h5 : 5 < p ^ 1 := by
          have := hp.two_le
          rw [pow_one]
          by_contra hle
          interval_cases p <;> omega
        exact shapeInEAS_u3_wreathed hp hp2 h5 (by rw [pow_one]; exact h3) L₀ hs hnab hP A S hAS
  · exact shapeInEAS_u3_pow asch4_11ASPow_holds hp hp2 (by have := hP.admissible.2.1; omega) L₀
      hs hnab hP A S hAS

end U3All

section L3All


theorem shapeInEAS_l3_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ShapeInEAS 1 (fun X _ => LieModel X .PSL 3 p f) := by
  intro L₀ _ _ hs hnab hP A S hAS
  by_cases hf : f = 1
  · subst hf
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (hp.odd_of_ne_two hp2)) with h1 | h3
    · by_cases hp5 : p = 5
      · subst hp5
        exact shapeInEAS_l35 L₀ hs hnab hP A S hAS
      · have h5 : 5 < p ^ 1 := by
          have := hp.two_le
          rw [pow_one]
          by_contra hle
          interval_cases p <;> omega
        exact shapeInEAS_l3_wreathed hp hp2 h5 (by rw [pow_one]; exact h1) L₀ hs hnab hP A S hAS
    · exact shapeInEAS_l3_one hp hp2 h3 L₀ hs hnab hP A S hAS
  · exact shapeInEAS_l3_pow asch4_11ASPow_holds hp hp2 (by have := hP.admissible.2.1; omega) L₀
      hs hnab hP A S hAS

theorem shapeInEAS_l3u3_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ShapeInEAS 1 (fun X _ => LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f) := by
  intro L₀ _ _ hs hnab hP A S hAS
  rcases hP with hL | hU
  · exact shapeInEAS_l3_odd hp hp2 L₀ hs hnab hL A S hAS
  · exact shapeInEAS_u3_odd hp hp2 L₀ hs hnab hU A S hAS

end L3All

end CFSG.LocalAnalysis.WeakClosure81
