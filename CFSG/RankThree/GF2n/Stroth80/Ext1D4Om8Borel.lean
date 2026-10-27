module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Datum
public import CFSG.RankThree.GF2n.Stroth80.SmithEightHolds
public import CFSG.LieType.D4Small.Om8Datum
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotent
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Sylow
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open CFSG.LieType.D4Small CFSG.StandardType CFSG.StandardType.Triality Matrix QuadraticMap CFSG.Open
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

theorem halfVec_eq_lv : ∀ β ∈ posRoot, ∃ i j : Fin 4, i < j ∧ ∃ s : Bool,
    halfVec β = lv j i s true := by
  decide +kernel

theorem exists_posRoot_lv : ∀ i j : Fin 4, i < j → ∀ s : Bool, ∃ β ∈ posRoot,
    halfVec β = lv j i s true := by
  decide +kernel

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def om8Lin :
    Om8 K →* ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
  (orthElementaryGroup (quadPlus 4 K)).subtype.comp
    ((plusDerivedEquiv 4 K (by norm_num)).toMonoidHom.comp (reindexOm8 K).symm.toMonoidHom)

theorem om8Lin_injective : Function.Injective (om8Lin K) := by
  intro g h hgh
  apply (reindexOm8 K).symm.injective
  apply (plusDerivedEquiv 4 K (by norm_num)).injective
  exact Subtype.ext (by simpa [om8Lin] using hgh)

theorem om8Lin_apply (g : Om8 K) (v : Fin 4 ⊕ Fin 4 → K) :
    om8Lin K g v = (((reindexOm8 K).symm g : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v := by
  simp only [om8Lin, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, plusDerivedEquiv_val]
  rfl

theorem om8Lin_reindex (g : Om8 K) (v : Fin 4 ⊕ Fin 4 → K) :
    reindexVectorEquiv (plusIndexEquiv 4) (om8Lin K g v) =
      (g : GL (Fin (2 * 4)) K) *ᵥ reindexVectorEquiv (plusIndexEquiv 4) v := by
  have h := conjOm8_mulVec_conjPhi (1 : StatedOmega (StatedQuadPlus 4 K)) g
    (reindexVectorEquiv (plusIndexEquiv 4) v)
  have hc : ∀ x, conjPhi (1 : StatedOmega (StatedQuadPlus 4 K)) x =
      (reindexVectorEquiv (plusIndexEquiv 4)).symm x := fun x => by
    simp [conjPhi, toLinEquiv_apply]
  have hg : conjOm8 (1 : StatedOmega (StatedQuadPlus 4 K)) g = (reindexOm8 K).symm g := by
    simp [conjOm8]
  rw [hc, hc, LinearEquiv.symm_apply_apply, hg, ← om8Lin_apply] at h
  rw [h, LinearEquiv.apply_symm_apply]

theorem om8Lin_posX {β : Fin 4 → ℤ} {i j : Fin 4} (hij : i < j) {s : Bool}
    (hβ : halfVec β = lv j i s true) (c : K) :
    om8Lin K (posX (om8Datum K) β c) =
      eichler (quadPlus 4 K) (Pi.single (Sum.inl i) 1) (c • plusVec 4 K j s) := by
  have hu : quadPlus 4 K (Pi.single (Sum.inl i) 1) = 0 := by
    rw [← plusVec_true]
    exact quadPlus_plusVec 4 K i true
  have hw : polar (quadPlus 4 K) (Pi.single (Sum.inl i) 1) (c • plusVec 4 K j s) = 0 := by
    rw [← plusVec_true, polar_smul_right, polar_quadPlus_plusVec, if_neg (fun h => hij.ne h.1),
      smul_zero]
  have key : ∀ u w y : Fin 4 ⊕ Fin 4 → K,
      AutOm.eichlerC (coordinateQuadPlus 4 K) (reindexVectorEquiv (plusIndexEquiv 4) u)
        (reindexVectorEquiv (plusIndexEquiv 4) w) (reindexVectorEquiv (plusIndexEquiv 4) y) =
      reindexVectorEquiv (plusIndexEquiv 4)
        (y + polar (quadPlus 4 K) y u • w - polar (quadPlus 4 K) y w • u -
          (quadPlus 4 K w * polar (quadPlus 4 K) y u) • u) := by
    intro u w y
    rw [AutOm.eichlerC, AutOm.polar_reindex_plus, AutOm.polar_reindex_plus, coordinateQuadPlus,
      reindexQuadraticForm_map, map_sub, map_sub, map_add, LinearEquiv.map_smul,
      LinearEquiv.map_smul, LinearEquiv.map_smul]
  ext v : 1
  apply (reindexVectorEquiv (plusIndexEquiv 4)).injective
  rw [om8Lin_reindex, posX, hβ, om8Datum_x_mulVec K hij.ne' s true c, eichler_apply hu hw,
    show (AutOm.pvec i true : Fin (2 * 4) → K) =
      reindexVectorEquiv (plusIndexEquiv 4) (Pi.single (Sum.inl i) 1) by
        rw [AutOm.pvec, plusVec_true],
    show c • (AutOm.pvec j s : Fin (2 * 4) → K) =
      reindexVectorEquiv (plusIndexEquiv 4) (c • plusVec 4 K j s) by
        rw [AutOm.pvec, LinearEquiv.map_smul], key]
  congr 1
  rw [add_smul]
  abel

@[expose] noncomputable def posUnipOm8 : Subgroup (Om8 K) :=
  Subgroup.closure {g | ∃ β ∈ posRoot, ∃ c, posX (om8Datum K) β c = g}

theorem image_posX_eq_posUnipGens :
    om8Lin K '' {g | ∃ β ∈ posRoot, ∃ c, posX (om8Datum K) β c = g} = posUnipGens 4 K := by
  ext g
  constructor
  · rintro ⟨_, ⟨β, hβ, c, rfl⟩, rfl⟩
    obtain ⟨i, j, hij, s, hs⟩ := halfVec_eq_lv β hβ
    rw [om8Lin_posX K hij hs c]
    cases s
    · exact Or.inl ⟨i, j, -c, hij, by rw [neg_neg, plusVec_false]⟩
    · exact Or.inr ⟨i, j, -c, hij, by rw [neg_neg, plusVec_true]⟩
  · rintro (⟨i, j, t, hij, rfl⟩ | ⟨i, j, t, hij, rfl⟩)
    · obtain ⟨β, hβ, hs⟩ := exists_posRoot_lv i j hij false
      exact ⟨_, ⟨β, hβ, -t, rfl⟩, by rw [om8Lin_posX K hij hs, plusVec_false]⟩
    · obtain ⟨β, hβ, hs⟩ := exists_posRoot_lv i j hij true
      exact ⟨_, ⟨β, hβ, -t, rfl⟩, by rw [om8Lin_posX K hij hs, plusVec_true]⟩

theorem map_posUnipOm8 : (posUnipOm8 K).map (om8Lin K) = posUnip 4 K := by
  rw [posUnipOm8, MonoidHom.map_closure, image_posX_eq_posUnipGens, posUnip_eq_closure]

theorem card_posUnipOm8 : Nat.card (posUnipOm8 K) = Nat.card K ^ 12 := by
  rw [← Subgroup.card_map_of_injective (om8Lin_injective K), map_posUnipOm8, card_posUnip]

theorem odd_index_posUnipOm8 : Odd (posUnipOm8 K).index := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h := Subgroup.card_mul_index (posUnipOm8 K)
  rw [card_posUnipOm8, CFSG.StandardType.L613C3.card_om8_eq, mul_assoc, mul_assoc, mul_assoc]
    at h
  have hpos : 0 < Nat.card K ^ 12 := by positivity
  have hidx := Nat.eq_of_mul_eq_mul_left hpos h
  have hev : Even (Nat.card K) := by
    haveI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, even_iff_two_dvd]
    exact (CharP.cast_eq_zero_iff K 2 _).1 (FiniteField.cast_card_eq_zero K)
  have hq2 : 2 ≤ Nat.card K := by obtain ⟨k, hk⟩ := hev; omega
  rw [hidx]
  have h1 : Odd (Nat.card K - 1) := Nat.Even.sub_odd (by omega) hev odd_one
  have h2 : Odd (Nat.card K + 1) := hev.add_one
  have he2 : Even (Nat.card K ^ 2) := (Nat.even_pow' two_ne_zero).2 hev
  have he4 : Even (Nat.card K ^ 4) := (Nat.even_pow' (by norm_num)).2 hev
  have h3 : Odd (Nat.card K ^ 2 + 1) := he2.add_one
  have h4 : Odd (Nat.card K ^ 4 + Nat.card K ^ 2 + 1) := (he4.add he2).add_one
  exact (h1.pow).mul ((h2.pow).mul ((h3.pow).mul h4))

theorem borel_index_ne_zero : ((borel (om8Datum K)).index : K) ≠ 0 := by
  have hle : posUnipOm8 K ≤ borel (om8Datum K) :=
    Subgroup.closure_mono Set.subset_union_left
  obtain ⟨k, hk⟩ := Subgroup.index_dvd_of_le hle
  have hodd : Odd (borel (om8Datum K)).index := by
    have h := odd_index_posUnipOm8 K
    rw [hk] at h
    exact (Nat.odd_mul.1 h).1
  rw [Ne, CharP.cast_eq_zero_iff K 2]
  exact fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
