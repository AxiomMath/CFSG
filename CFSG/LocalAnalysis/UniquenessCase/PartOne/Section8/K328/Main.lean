module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKGammaLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Unified
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open

theorem rankThreeGamma_eq_top_of_eq_normal {G : Type} [Group G] [Finite G] (K : Subgroup G)
    [K.Normal] {Z P : Subgroup G} (hZ : Nat.card Z = 3) (hZK : Z ≤ K)
    (hZC : ∀ x ∈ K, ∀ z ∈ Z, z * x = x * z) (hcen : Nat.card (Subgroup.center ↥K) = 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P K) : rankThreeGamma 1 3 P = ⊤ := by
  obtain ⟨Q, hQ⟩ := hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZP : Z ≤ P := by
    have hnorm : (Z.subgroupOf K).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hc := hZC g g.2 n hn
      have : ((g * n * g⁻¹ : K) : G) = n := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hc]; group
      rw [this]; exact hn⟩
    have hpg : IsPGroup 3 (Z.subgroupOf K) :=
      IsPGroup.of_card (n := 1) (by rw [card_subgroupOf_of_le hZK, hZ, pow_one])
    have hle := hpg.le_sylow_of_normal Q
    intro z hz
    rw [← hQ]
    exact ⟨⟨z, hZK hz⟩, hle (by simpa [Subgroup.mem_subgroupOf] using hz), rfl⟩
  set Zc : Subgroup G := (Subgroup.center ↥K).map K.subtype with hZc
  have hZZc : Z ≤ Zc := by
    intro z hz
    refine ⟨⟨z, hZK hz⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hZC g g.2 z hz).symm
  have hZcc : Nat.card Zc = 3 := by
    rw [hZc, Subgroup.card_map_of_injective K.subtype_injective, hcen]
  have hZeq : Z = Zc := Subgroup.eq_of_le_of_card_ge hZZc (by rw [hZ, hZcc])
  have hconj : ∀ (g : G) (z : G), z ∈ Z → g * z * g⁻¹ ∈ Z := by
    intro g z hz
    rw [hZeq] at hz ⊢
    obtain ⟨z', hz', rfl⟩ := hz
    have hzK : g * (z' : G) * g⁻¹ ∈ K := by
      have := Subgroup.Normal.conj_mem inferInstance (z' : G) z'.2 g
      simpa using this
    refine ⟨⟨_, hzK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hk' : g⁻¹ * (k : G) * g ∈ K := by
      have := Subgroup.Normal.conj_mem inferInstance (k : G) k.2 g⁻¹
      simpa using this
    have hcomm := Subgroup.mem_center_iff.1 hz' ⟨_, hk'⟩
    have hcomm' := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul] at hcomm' ⊢
    calc (k : G) * (g * (z' : G) * g⁻¹)
        = g * ((g⁻¹ * (k : G) * g) * (z' : G)) * g⁻¹ := by group
      _ = g * ((z' : G) * (g⁻¹ * (k : G) * g)) * g⁻¹ := by rw [hcomm']
      _ = g * (z' : G) * g⁻¹ * (k : G) := by group
  have hnorm : ∀ g : G, g ∈ Subgroup.normalizer (Z : Set G) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj g h hh, fun hh => ?_⟩
    have := hconj g⁻¹ _ hh
    simpa [mul_assoc] using this
  refine eq_top_iff.2 fun g _ => ?_
  exact normalizer_le_gamma hZP hZ (hnorm g)

theorem isSylowOf_subgroupOf_of_le {G : Type} [Group G] [Finite G] {K P X : Subgroup G}
    (hXK : X ≤ K) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf K) (X.subgroupOf K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPK : P ≤ K := hP.le.trans hXK
  refine CFSG.ABGLocalTools.isSylowOf_of_card
    (fun x hx => Subgroup.mem_subgroupOf.2 (hP.le (Subgroup.mem_subgroupOf.1 hx))) ?_
  rw [card_subgroupOf_of_le hPK, card_subgroupOf_of_le hXK]
  exact hP.card_eq

theorem k328_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328 := by
  intro G _ _ hq hKG hrank Z X P hZ hZX hXC hsub hXq hXZ hXt hP
  have hKn : (genFittingFStar G).Normal := CFSG.ClassicalInvolution.genFittingFStar_normal G
  set K : Subgroup G := genFittingFStar G with hK
  have hXK : X ≤ K := hXC.trans inf_le_right
  by_cases hXe : X = K
  · have hXZ' : Nat.card (Subgroup.center ↥K) = 3 := by rw [← hXe]; exact hXZ
    have hP' : CFSG.ABGLocalTools.IsSylowOf 3 P K := by rw [← hXe]; exact hP
    exact rankThreeGamma_eq_top_of_eq_normal K hZ (hZX.trans hXK)
      (fun x hx z hz => Subgroup.mem_centralizer_iff.1 (hXC (hXe ▸ hx)).1 z hz) hXZ' hP'
  · have hpos : Pos ↥K (Z.subgroupOf K) (X.subgroupOf K) :=
      pos_of_k328_hyps hZ hZX hXC hsub hXq hXZ hXt
    have hXne : X.subgroupOf K ≠ ⊤ := fun h =>
      hXe (le_antisymm hXK (Subgroup.subgroupOf_eq_top.1 h))
    have hrankK : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 :=
      (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) K.subtype
        K.subtype_injective).trans hrank
    have hdet := k328_detection hq hKG hrankK hpos hXne
      CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.k33_holds
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k34odd_holds
    rcases rowLeaves_or_ambLeaves_of_properComponent hGA hq hdet with hrow | hamb
    · exact assembly G K hKn hrow Z X P (hZX.trans hXK) hXK hpos hP
    · have := K328Exc.rankThreeGamma_eq_top_of_ambLeaves K hamb hrank hpos
        (isSylowOf_subgroupOf_of_le hXK hP)
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hP.le.trans hXK)] at this

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
