module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem seven_le_twoLocalRank_of_e7Field
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hL : commutator L = ⊤)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup .E7 K) :
    7 ≤ LargeEvenTwoLocalRank 3 G := by
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hx : x ^ 3 = 1 := hS.1.1.2 x hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have h7 := succ_le_twoLocalRank_of_torusLift Nat.prime_three hLx hx hx1 hL θ
    (TableBExcTwo.ggTorusLift_E7Two (K := K))
  omega

theorem seven_le_twoLocalRank_of_e7Tag
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .E7)) :
    7 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨hL, lab, hlab, hraw⟩ := hmark
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨R, hR, I, F, hsimple, hna, θ₀, htag⟩ := largeEvenRawDatum_exists hraw
  have htag' : t = .E7 := htag
  subst htag'
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, i1, i2, hK, hQ⟩ := hraw
  obtain ⟨-, -, θ, -⟩ := hQ
  have hchar : CharP K 2 := charP_two_of_card hK
  exact seven_le_twoLocalRank_of_e7Field hcfg hL θ

theorem pow_five_le_card_range_gamma_J_of_e7Tag
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .E7))
    (hBN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    3 ^ 5 ≤ Nat.card (ggGamma J hBN).range := by
  have h7 := seven_le_twoLocalRank_of_e7Tag hcfg hmark
  exact (Nat.pow_le_pow_right Nat.prime_three.pos (by omega)).trans
    (hcfg.pow_le_card_gamma_J hBN)

theorem pow_five_le_card_range_gamma_J_of_e7Selected
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : LargeEvenMarking L (fun lab _ _ I _ θ =>
      lab.tag = .E7 ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ))
    (hBN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    3 ^ 5 ≤ Nat.card (ggGamma J hBN).range :=
  pow_five_le_card_range_gamma_J_of_e7Tag hcfg
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hmark) hBN

theorem pow_six_le_card_range_gamma_J_of_e7TagJ
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hBN : Bs ≤ Subgroup.normalizer (J : Set G))
    (labJ : LargeEvenLabel) (htagJ : labJ.tag = .E7)
    (hlabelJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    3 ^ 6 ≤ Nat.card (ggGamma J hBN).range := by
  classical
  have hJdata := hlabelJ
  unfold GGHasLabel at hJdata
  simp only [LargeEvenRawDatum, htagJ] at hJdata
  obtain ⟨K, hKfield, hKfin, hKcard, eJ⟩ := hJdata
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hchar : CharP K 2 := charP_two_of_card hKcard
  obtain ⟨eJ⟩ := eJ
  let θJ : ↥J ⧸ Subgroup.center ↥J ≃* TableBExc.RecipeGroup .E7 K := eJ
  exact hcfg.pow_le_card_range_gamma_J_of_torusLift hBN θJ
    (TableBExcTwo.ggTorusLift_E7Two (K := K))

end CFSG.StandardType
