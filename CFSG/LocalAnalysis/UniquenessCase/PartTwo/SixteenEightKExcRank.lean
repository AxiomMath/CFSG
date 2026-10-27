module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827B
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16k_pRank_le_add_of_hom {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {A : Subgroup G} (φ : ↥A →* G') {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p A ≤ CFSG.Open.pRank p (φ.ker.map A.subtype) + CFSG.Open.pRank p φ.range := by
  have h := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map (p := p) hp φ
    (⊤ : Subgroup ↥A)
  rw [top_inf_eq, ← MonoidHom.range_eq_map] at h
  have h2 : CFSG.Open.pRank p φ.ker ≤ CFSG.Open.pRank p (φ.ker.map A.subtype) :=
    CFSG.SectionRank.pRank_le_map hp.one_lt A.subtype A.subtype_injective φ.ker
  have h3 : CFSG.Open.pRank p A = CFSG.Open.pRank p (⊤ : Subgroup ↥A) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup A
  omega

theorem s16k_pRank_mulAut_congr {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) (p : ℕ) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) = CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) := by
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p (MulAut X),
    ← CFSG.SectionRank.pRank_eq_open_pRank_top p (MulAut Y)]
  exact CFSG.pRank_congr_of_mulEquiv (MulAut.congr e) p

theorem s16k_pRank_le_of_normalizer {Q : Type} [CommGroup Q] [Finite Q]
    {L' N : Subgroup (MulAut Q)} (hN : ∀ n ∈ N, ∀ l ∈ L', n * l * n⁻¹ ∈ L') {p : ℕ}
    (hp : p.Prime) :
    CFSG.Open.pRank p N ≤
      CFSG.Open.pRank p (N ⊓ Subgroup.centralizer (L' : Set (MulAut Q)) : Subgroup (MulAut Q)) +
        CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥L')) := by
  exact CFSG.AGLEmbedding.pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp
    (Subgroup.le_normalizer_iff.mpr hN)

theorem s16k_pRank_le_two_of_aut_sixteen {Q : Type} [CommGroup Q] [Finite Q]
    (hQ : Nat.card Q = 16) (h2 : ∀ x : Q, x ^ 2 = 1) (A : Subgroup (MulAut Q)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p A ≤ 2 := by
  apply CFSG.SectionRank.pRank_le hp.one_lt
  intro E hEA hE
  haveI : Fact p.Prime := ⟨hp⟩
  have hEP : IsPGroup p E := hE.isPGroup
  obtain ⟨k, hk⟩ := hEP.exists_card_eq
  have hdiv : p ^ k ∣ 20160 := by
    rw [← hk, ← CFSG.Quasithin.H13.card_mulAut_827 (fun a b => mul_comm a b) h2 hQ]
    exact Subgroup.card_subgroup_dvd_card E
  have hk2 : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := by omega
    have hdvd3 : p ^ 3 ∣ 20160 := (pow_dvd_pow p h3).trans hdiv
    have hpdvd : p ∣ 20160 := (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans hdvd3
    rcases CFSG.Quasithin.H13.prime_dvd_20160_827 hp hpdvd with h2' | h3' | h5' | h7'
    · exact hp2 h2'
    · rw [h3'] at hdvd3; norm_num at hdvd3
    · rw [h5'] at hdvd3; norm_num at hdvd3
    · rw [h7'] at hdvd3; norm_num at hdvd3
  calc Nat.card E = p ^ k := hk
    _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos hk2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
