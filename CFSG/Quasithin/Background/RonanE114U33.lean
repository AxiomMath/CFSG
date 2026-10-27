module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Main
public import CFSG.Quasithin.Background.RonanE114Pair
public import CFSG.Quasithin.Background.RonanE114A7

public section

namespace CFSG.Quasithin.RonanE114

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.ClassicalGroups.UnitaryFlag CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11 CFSG.Quasithin.B6

section Pair

variable {G : Type} [Group G] [Finite G]

theorem exists_solvable_pair_typeU33 (L R : Subgroup G)
    (hty : StatedClassicalModel ↥L .PSU 3 3 1) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowTwoOf (R ⊓ L) L) :
    ∃ K₁ K₂ : Subgroup G, K₁ ≤ L ∧ K₂ ≤ L ∧ K₁ ⊔ K₂ = L ∧
      R ≤ Subgroup.normalizer (K₁ : Set G) ∧ R ≤ Subgroup.normalizer (K₂ : Set G) ∧
      Nat.card K₁ = 96 ∧ Nat.card K₂ = 96 := by
  obtain ⟨-, F, hFf, hFfin, hFcard, ⟨e⟩⟩ := hty
  have hF : Nat.card F = 9 := by rw [hFcard]; norm_num
  obtain ⟨i, hi⟩ := exists_units_orderOf_eq_four hF
  let d : U33.Idata F := U33.Idata.ofUnit hF i hi
  have hscal := statedScalars_subgroupOf_statedSU_eq_bot hF
  let e' : ↥L ≃* (StatedSU 3 3 F ⧸ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 3 F)) := e
  let φ₀ : ↥L ≃* StatedSU 3 3 F :=
    e'.trans ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  obtain ⟨hcard0, P0, hP0⟩ := U33.S0_facts hF i hi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SL : Subgroup ↥L := (R ⊓ L).subgroupOf L with hSL
  have hSLp : IsPGroup 2 SL := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hSLi : ¬ 2 ∣ SL.index := hS.2.2
  let PL : Sylow 2 ↥L := hSLp.toSylow hSLi
  let PK : Sylow 2 (StatedSU 3 3 F) := PL.mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (StatedSU 3 3 F) PK P0
  let φ : ↥L ≃* StatedSU 3 3 F := φ₀.trans (MulAut.conj k)
  have hSφ : SL.map φ.toMonoidHom = U33.S0 hF d := by
    have h1 : SL.map φ₀.toMonoidHom = (PK : Subgroup (StatedSU 3 3 F)) :=
      (Sylow.coe_mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective PL).symm
    have h2 : ((k • PK : Sylow 2 (StatedSU 3 3 F)) : Subgroup (StatedSU 3 3 F)) =
        (PK : Subgroup (StatedSU 3 3 F)).map (MulAut.conj k).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hk] at h2
    calc SL.map φ.toMonoidHom = (SL.map φ₀.toMonoidHom).map (MulAut.conj k).toMonoidHom := by
          rw [Subgroup.map_map]
          rfl
      _ = (PK : Subgroup (StatedSU 3 3 F)).map (MulAut.conj k).toMonoidHom := by rw [h1]
      _ = (P0 : Subgroup (StatedSU 3 3 F)) := h2.symm
      _ = U33.S0 hF d := hP0
  have hK1 : (U33.canK1 SL).map φ.toMonoidHom = U33.K1 hF := by
    rw [← U33.canK1_map, hSφ, U33.canK1_eq_K1]
  have hK2 : (U33.canK2 SL).map φ.toMonoidHom = U33.stab0 hF := by
    rw [← U33.canK2_map, hSφ, U33.canK2_eq_stab0 hcard0]
  have hc1 : Nat.card ↥(U33.canK1 SL) = 96 := by
    have h := Subgroup.card_map_of_injective (show Function.Injective φ.toMonoidHom from φ.injective)
      (K := U33.canK1 SL)
    rw [hK1, U33.card_K1] at h
    exact h.symm
  have hc2 : Nat.card ↥(U33.canK2 SL) = 96 := by
    have h := Subgroup.card_map_of_injective (show Function.Injective φ.toMonoidHom from φ.injective)
      (K := U33.canK2 SL)
    rw [hK2, U33.card_stab0 d] at h
    exact h.symm
  refine ⟨(U33.canK1 SL).map L.subtype, (U33.canK2 SL).map L.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup]
    have h1 : U33.canK1 SL ⊔ U33.canK2 SL = ⊤ := by
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [Subgroup.map_sup, hK1, hK2, U33.K1_sup_stab0 hF d,
        Subgroup.map_top_of_surjective _ φ.surjective]
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  · exact U33.normalizes_of_stable hRN fun r hr x hx =>
      U33.mem_canK1_of_map_eq (U33.conjL L r (hRN hr)) (U33.conjL_map_S hRN hr) hx
  · exact U33.normalizes_of_stable hRN fun r hr x hx =>
      U33.mem_canK2_of_map_eq (U33.conjL L r (hRN hr)) (U33.conjL_map_S hRN hr) hx
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hc1]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hc2]

theorem nParam_eq_one_of_isPSU33 {T : Subgroup G} (hL : IsPSU 3 3 1 (ASInputs.FStar G))
    (hT : quasithinIsSylowTwo T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) = 1 := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  have hSK : IsSylowTwoOf (T ⊓ CFSG.generalizedFitting G) (CFSG.generalizedFitting G) :=
    isSylowTwoOf_inf_normal hTs le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
      trivial
  have hTN : T ≤ Subgroup.normalizer (CFSG.generalizedFitting G : Set G) := fun x _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    trivial
  obtain ⟨K₁, K₂, hK₁, hK₂, hgen, hn₁, hn₂, hc₁, hc₂⟩ :=
    exists_solvable_pair_typeU33 (CFSG.generalizedFitting G) T hL hTN hSK
  have hs₁ : Group.IsSolvable ↥K₁ :=
    CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_of_card_two_three (a := 5) (b := 1)
      (by rw [hc₁]; norm_num)
  have hs₂ : Group.IsSolvable ↥K₂ :=
    CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_of_card_two_three (a := 5) (b := 1)
      (by rw [hc₂]; norm_num)
  refine le_antisymm ?_ ?_
  · refine Vol2.Ch11.SecU1.nParam_le_one_of_solvable_pair (D₁ := K₁ ⊔ T) (D₂ := K₂ ⊔ T)
      ⟨le_top, hTs.2.1, hTs.2.2⟩ le_sup_right le_sup_right (isSolvable_sup_of_normalizes hT.1 hn₁ hs₁)
      (isSolvable_sup_of_normalizes hT.1 hn₂ hs₂) ?_
    have hKle : CFSG.generalizedFitting G ≤ K₁ ⊔ T ⊔ (K₂ ⊔ T) :=
      hgen.symm.le.trans (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left))
    rw [eq_top_iff, ← hFT]
    exact sup_le hKle (le_sup_of_le_left le_sup_right)
  · refine Vol2.Ch11.SecE3.one_le_nParam_of_not_odd
      (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G) ?_)
    have h96 : 96 ∣ Nat.card ↥(CFSG.generalizedFitting G) := by
      rw [← hc₁]
      exact Subgroup.card_dvd_of_le hK₁
    exact dvd_trans (by norm_num) h96

end Pair

end CFSG.Quasithin.RonanE114
