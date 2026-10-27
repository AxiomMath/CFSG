module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.KE.E7FourFinal
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIOut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalf
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVOut
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIII
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KGD.D4QA1

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem fs81Rf_maximal_centralizer_closed {G : Type} [Group G] {C E : Subgroup G}
    (h : IsMaxElemAb3 C E) {x : G} (hxC : x ∈ C)
    (hxc : x ∈ Subgroup.centralizer (E : Set G)) (hx3 : x ^ 3 = 1) : x ∈ E := by
  let E' := E ⊔ Subgroup.zpowers x
  have hE'C : E' ≤ C := sup_le h.1 (Subgroup.zpowers_le.mpr hxC)
  have hcomm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hxc a ha) k)
  have hE'abel : IsElemAbelian 3 E' :=
    IsElemAbelian.sup_of_commute h.2.1 (isElemAbelian_zpowers hx3) hcomm
  have hEq : E' = E := h.2.2 E' hE'C hE'abel le_sup_left
  exact hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem fs81_row_out_not_dvd_three
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : LargeEvenMarking K (fun lab _ _ _ _ _ => FSLab lab))
    (hZ : Subgroup.center K = ⊥) :
    ¬ 3 ∣ Nat.card (Outer K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨lab, hFS, hlab⟩ := exists_glaLabel hK
  obtain ⟨hn1, hcases⟩ := hFS
  have hmarked := CFSG.StandardType.Canonical.largeEvenMarking_markedModel hlab
  obtain ⟨-, lab', hlab2, hraw⟩ := hmarked
  obtain ⟨R, _, I, F, hs, hna, θ, hEq, hmod⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hmod' : MarkedModel lab R := hEq ▸ hmod
  let e0 : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eK : ↥K ≃* R := e0.symm.trans θ
  have hmodK : MarkedModel lab ↥K := MarkedModel.of_mulEquiv eK.symm hmod'
  rcases hcases with ⟨hD, hr6⟩ | ⟨htwD, hr7⟩ | ⟨hE7, hr0⟩
  · have h1 : markTag lab = .POmegaPlus := by simp [markTag, hD, hr6]
    have h2 : markRank lab = 6 := by simp [markRank, hD, hr6]
    have h3 : markChar lab = 2 := by simp [markChar, hD, hr6]
    have h4 : markDeg lab = 1 := by simp [markDeg, hD, hr6, hn1]
    have hmR : LieModel ↥K .POmegaPlus 6 2 1 := by
      have h := hmodK
      unfold MarkedModel at h
      rwa [h1, h2, h3, h4] at h
    have hst : StatedClassicalModel ↥K .POmegaPlus 6 2 1 :=
      hmR.statedClassicalModel (by decide)
    have hle := CFSG.AGLEmbedding.card_outer_le_two_of_omegaPlus_two_of_five_le hst
      (by norm_num : 5 ≤ 6)
    intro h3dvd
    have h3le : 3 ≤ Nat.card (Outer ↥K) := Nat.le_of_dvd hle.1 h3dvd
    omega
  · have h1 : markTag lab = .POmegaMinus := by simp [markTag, htwD, hr7]
    have h2 : markRank lab = 7 := by simp [markRank, htwD, hr7]
    have h3 : markChar lab = 2 := by simp [markChar, htwD, hr7]
    have h4 : markDeg lab = 1 := by simp [markDeg, htwD, hr7, hn1]
    have hmR : LieModel ↥K .POmegaMinus 7 2 1 := by
      have h := hmodK
      unfold MarkedModel at h
      rwa [h1, h2, h3, h4] at h
    have hst : StatedClassicalModel ↥K .POmegaMinus 7 2 1 :=
      hmR.statedClassicalModel (by decide)
    have hle := CFSG.AGLEmbedding.card_outer_le_two_of_omegaMinus_two hst
    intro h3dvd
    have h3le : 3 ≤ Nat.card (Outer ↥K) := Nat.le_of_dvd hle.1 h3dvd
    omega
  · obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := lab) hlab hE7 hZ
    have hGF : Nat.card (GaloisField 2 lab.n) = 2 := by
      rw [hn1]
      simpa using GaloisField.card 2 1 (by omega)
    have hdvd : Nat.card (Outer (↥(adjointGroup Tag.E7 (GaloisField 2 lab.n)))) ∣ 2 :=
      CFSG.RankThree.PartOne.KE.card_outer_E7_dvd_two (GaloisField 2 lab.n) Nat.prime_two hGF
    have hout : Nat.card (Outer ↥K) =
        Nat.card (Outer (↥(adjointGroup Tag.E7 (GaloisField 2 lab.n)))) :=
      Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv
    intro h3dvd
    rw [hout] at h3dvd
    exact absurd (h3dvd.trans hdvd) (by norm_num)

theorem fs81_E7_maxElemAb3_card
    {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (hK : IsEm 7 K) (hZ : Subgroup.center K = ⊥) (hA : IsMaxElemAb3 K A)
    (hcard : 3 ^ 6 ≤ Nat.card A) :
    Nat.card A = 3 ^ 7 ∧ K ⊓ Subgroup.centralizer (A : Set G) = A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨t, r, n⟩, hP, hlab⟩ := exists_glaLabel hK
  obtain ⟨hmt, -, hn⟩ := hP
  subst hn
  have ht : t = .E7 := by rcases hmt with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact h; omega]
  obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hZ
  let E₂ := (A.subgroupOf K).map φ.toMonoidHom
  have hE₂ : IsElemAbelian 3 E₂ := (hA.2.1.subgroupOf K).map φ.toMonoidHom
  have hcard₂ : Nat.card E₂ = Nat.card A := by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv]
  have hSC : ∀ x ∈ Subgroup.centralizer (E₂ : Set ↥(adjointGroup .E7 (GaloisField 2 1))),
      x ^ 3 = 1 → x ∈ E₂ := by
    intro x hx hx3
    have hxmem : ((φ.symm x : ↥K) : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haK : a ∈ K := hA.1 ha
      have hxa : φ ⟨a, haK⟩ ∈ E₂ :=
        ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have hcomm : φ ⟨a, haK⟩ * x = x * φ ⟨a, haK⟩ :=
        Subgroup.mem_centralizer_iff.mp hx _ hxa
      have h := congrArg (fun z : ↥K => (z : G)) (congrArg φ.symm hcomm)
      simpa using h
    have hx3' : ((φ.symm x : ↥K) : G) ^ 3 = 1 := by
      have h3 : (φ.symm x : ↥K) ^ 3 = 1 := by
        apply φ.injective
        rw [map_pow, φ.apply_symm_apply, hx3, map_one]
      simpa using congrArg (fun z : ↥K => (z : G)) h3
    have hxA : ((φ.symm x : ↥K) : G) ∈ A :=
      fs81Rf_maximal_centralizer_closed hA (φ.symm x).2 hxmem hx3'
    exact ⟨φ.symm x, Subgroup.mem_subgroupOf.mpr hxA, φ.apply_symm_apply x⟩
  have hfield : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  have hcard6 : 3 ^ 6 ≤ Nat.card E₂ := by rw [hcard₂]; exact hcard
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_half_E7
    (K := GaloisField 2 1) hfield hE₂ hcard6 hSC
  have hTcard : Nat.card (TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE7).range =
      3 ^ 7 := by
    have e : Multiplicative (Fin (6 + 1) → ZMod 3) ≃
        (TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE7).range :=
      (MonoidHom.ofInjective (TableBExcTwoTB.tE_injective (K := GaloisField 2 1)
        TableBExcTwo.frameE7)).toEquiv
    rw [show (7 : ℕ) = 6 + 1 by norm_num, ← Nat.card_congr e,
      Nat.card_congr (Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hE₂card : Nat.card E₂ = 3 ^ 7 := by
    rw [hc, Subgroup.card_map_of_injective (MulAut.conj c).injective, hTcard]
  have hAcard : Nat.card A = 3 ^ 7 := by rw [← hcard₂]; exact hE₂card
  exact ⟨hAcard, e7TwoSelfCentInput (G := G) (K := K) (E := A) hK hZ hA.1 hA.2.1 hAcard⟩

end CFSG.StandardType.FrameRoute
