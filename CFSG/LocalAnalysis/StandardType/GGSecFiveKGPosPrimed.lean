module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosRankDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGStdPosTableBPos
import CFSG.LocalAnalysis.StandardType.GGStdPosRankBase
import CFSG.LocalAnalysis.StandardType.GGStdPosRankHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosLocalConj
import CFSG.LocalAnalysis.StandardType.GGStdPosA
import CFSG.LocalAnalysis.StandardType.GGStdPosD
import CFSG.LocalAnalysis.StandardType.GGStdPosE6
import CFSG.LocalAnalysis.StandardType.GGStdPosE6Three
import CFSG.LocalAnalysis.StandardType.GGStdPosE7
import CFSG.LocalAnalysis.StandardType.GGStdPosE8
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
import CFSG.LocalAnalysis.StandardType.GGStdPosRankLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section Inputs


@[expose] def GGSecFiveKGPosNbrInput'
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' → GGSplitLie p K' →
        ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n ∧
            ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = K' ∧
            (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ p ∣ 2 ^ f - 1 ∧
            GGTableBPos p Bs K' t n f ψ

end Inputs

theorem s2jn_ggKGPos_innerDiagOn
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦)
    {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) : GGInnerDiagOn Bs X := by
  have hInn : GGInnerDiagAll p B Bs x L D J := h.1.2.2.1
  rcases hX with rfl | ⟨y, hy⟩
  · exact hInn.1
  · exact hInn.2 y X hy

theorem s2jn_ggKGPos_prime_rank_ge_four
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) :
    p.Prime ∧ p ≠ 2 ∧ 4 ≤ LargeEvenTwoLocalRank p G := by
  obtain ⟨hp, hp2, -, h4⟩ := h.1.1.1.2.2.2.2.2.1
  exact ⟨hp, hp2, h4⟩

theorem s2jn_ggKGPos_exists_central_elt
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) :
    ∃ y : G, y ∈ B ∧ y ≠ 1 ∧ y ^ p = 1 ∧ X ≤ Subgroup.centralizer ({y} : Set G) ∧
      B ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers y := by
  obtain ⟨hp, -, -⟩ := s2jn_ggKGPos_prime_rank_ge_four h
  rcases hX with hXL | ⟨y, hnb⟩
  · have hS : LargeEvenSStar p B x L := h.1.1.1.2.2.2.2.2.2.1
    rw [hXL]
    exact ⟨x, hS.2.1, hS.2.2.1, hS.1.1.2 x hS.2.1, hS.2.2.2.1.1,
      inf_centralizer_eq_zpowers_of_sstar hp hS⟩
  · have hS : LargeEvenSHat p B y X := hnb.1
    exact ⟨y, hS.2.1, hS.2.2.1, hS.1.1.2 y hS.2.1, hS.2.2.2.1,
      inf_centralizer_eq_zpowers_of_sHat hS⟩

theorem s2jn_ggKGPos_pow_mul_card_le
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) :
    p ^ (LargeEvenTwoLocalRank p G - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤
      Nat.card ↥Bs := by
  obtain ⟨hp, -, h4⟩ := s2jn_ggKGPos_prime_rank_ge_four h
  obtain ⟨y, -, hy1, hyp, -, hBC⟩ := s2jn_ggKGPos_exists_central_elt h hX
  have := Fact.mk hp
  have hBBs : B ≤ Bs := h.1.1.2.1.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := h.1.1.1.2.2.2.2.2.2.1.1.2.1
  set C : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hC
  have hBC' : B ⊓ C = Subgroup.zpowers y := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr hBBs, hBC]
  have h1 : B.relIndex C * p = Nat.card C := by
    have := Subgroup.relIndex_mul_card B C
    rwa [hBC', Nat.card_zpowers, orderOf_eq_prime hyp hy1] at this
  have h2 : B.relIndex Bs * p ^ LargeEvenTwoLocalRank p G = Nat.card Bs := by
    have := Subgroup.relIndex_mul_card B Bs
    rwa [inf_eq_left.mpr hBBs, hBcard] at this
  have hne : B.relIndex Bs ≠ 0 := fun h0 =>
    (Nat.card_pos (α := Bs)).ne' (by rw [← h2, h0, zero_mul])
  have h3 : B.relIndex C ≤ B.relIndex Bs :=
    Subgroup.relIndex_le_of_le_right inf_le_left hne
  have hpm : p ^ (LargeEvenTwoLocalRank p G - 1) * p = p ^ LargeEvenTwoLocalRank p G := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  calc p ^ (LargeEvenTwoLocalRank p G - 1) * Nat.card C
      = B.relIndex C * (p ^ (LargeEvenTwoLocalRank p G - 1) * p) := by rw [← h1]; ring
    _ ≤ B.relIndex Bs * p ^ LargeEvenTwoLocalRank p G := by
        rw [hpm]; exact Nat.mul_le_mul_right _ h3
    _ = Nat.card Bs := h2

theorem s2jn_ggKGPosBaseStmt_holds
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦)
    (X : Subgroup G) (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) (hsplit : GGSplitLie p X) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
      GGKGPosBaseHyp p Bs X t n f ψ := by
  obtain ⟨t, n, f, ψ, hadm, hker, hrange, ht, hpf⟩ := hsplit
  obtain ⟨hp, hp2, h4⟩ := s2jn_ggKGPos_prime_rank_ge_four h
  have hInn := s2jn_ggKGPos_innerDiagOn h hX
  have hBsG : GGBstar p B Bs := h.1.1.2.1
  have hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))).trans
      (s2jn_ggKGPos_pow_mul_card_le h hX)
  have hrk : 3 ≤ bnRank t n :=
    ggKGPos_three_le_bnRank ggLabelRigidInput_holds hp hadm hker hrange ht hpf hBsG.2.1 hInn hcard
  have hrk2 : 2 ≤ (ggU t n f).D.rank := two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm hrk
  obtain ⟨-, lab, -, hraw⟩ := ggInnerDiagMpInput_holds G t n f ψ hadm hrk2 hker X hrange _ hInn
  obtain ⟨R, _, I, _, -, -, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  exact ⟨t, n, f, ψ, ⟨hp, hp2, hadm, hrk⟩, ⟨hker, hrange, ht, hpf⟩,
    ⟨hBsG.2.1, hBsN, hBsG.2.2.2⟩, fun b hb => himp b (hBsN hb) (hI b hb)⟩

theorem s2jn_ggKGPosBoundsStmt_holds
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦)
    (X : Subgroup G) (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (hbase : GGKGPosBaseHyp p Bs X t n f ψ) : GGKGPosBoundsHyp p Bs X t n := by
  obtain ⟨⟨hp, hp2, hadm, h3⟩, ⟨hker, hψX, ht, hpf⟩, -, -⟩ := hbase
  obtain ⟨y, -, hy1, hyp, hXy, -⟩ := s2jn_ggKGPos_exists_central_elt hcfg hX
  have hrk : 2 ≤ (ggU t n f).D.rank := by
    rw [show (ggU t n f).D.rank = bnRank t n from
      lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm h3]
    omega
  have : Group.IsPerfect (ggU t n f).K := ⟨(ggU_perfect_lieModel hadm hrk).1⟩
  have hmodel := lieModel_range_centerQuot hadm hrk ψ hker
  subst hψX
  have hcomm : commutator ψ.range = ⊤ := by
    have := Group.IsPerfect.range ψ
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨R, _, r, ⟨θ⟩, hlift, h1, h2⟩ := ggKGPos_lieLift ht hp hp2 hadm.2.1 h3 hpf hmodel
  exact ggKGPosBoundsHyp_of_rank hp (s2jn_ggKGPos_pow_mul_card_le hcfg hX)
    (succ_le_twoLocalRank_of_torusLift hp hXy hyp hy1 hcomm θ hlift) h1 h2

theorem s2jn_ggKGPosRankStmt_holds
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦)
    (X : Subgroup G) (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) (hsplit : GGSplitLie p X) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
      GGKGPosLocalHyp p Bs X t n f ψ := by
  obtain ⟨t, n, f, ψ, hbase⟩ := s2jn_ggKGPosBaseStmt_holds G p B Bs x L D J 𝒦 h X hX hsplit
  exact ⟨t, n, f, ψ, ggKGPosLocalHyp_iff.mpr
    ⟨hbase, s2jn_ggKGPosBoundsStmt_holds G p B Bs x L D J 𝒦 h X hX t n f ψ hbase⟩⟩

theorem s2jn_ggSecFiveKGPosNbrInput'_holds : GGSecFiveKGPosNbrInput' := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ y X hnb hsplit
  obtain ⟨t, n, f, ψ, hloc⟩ :=
    s2jn_ggKGPosRankStmt_holds G p B Bs x L D J 𝒦 hcfg X (Or.inr ⟨y, hnb⟩) hsplit
  obtain ⟨k, hstd⟩ := ggKGPos_exists_stdPos hloc
  have hloc' := ggKGPosLocalHyp_comp_conj hloc k
  exact ⟨t, n, f, ψ.comp (MulAut.conj k).toMonoidHom, hloc'.1.2.2.1, hloc'.1.2.2.2, hloc'.2.1.1,
    hloc'.2.1.2.1, hloc'.2.1.2.2.1, hloc'.2.1.2.2.2,
    ggKGPos_tableBPos_of_stdPos G p Bs X t n f _ hloc' hstd⟩


section Certs

theorem s2jn_exists_tableBFrame
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hL : GGSplitLie p L) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
      GGKGPosLocalHyp p Bs L t n f ψ ∧ GGKGPosStdPos (ggU t n f).D ψ Bs ∧
        GGTableBPos p Bs L t n f ψ := by
  obtain ⟨t, n, f, ψ, hloc⟩ :=
    s2jn_ggKGPosRankStmt_holds G p B Bs x L D J 𝒦 hcfg L (Or.inl rfl) hL
  obtain ⟨k, hstd⟩ := ggKGPos_exists_stdPos hloc
  have hloc' := ggKGPosLocalHyp_comp_conj hloc k
  exact ⟨t, n, f, ψ.comp (MulAut.conj k).toMonoidHom, hloc', hstd,
    ggKGPos_tableBPos_of_stdPos G p Bs L t n f _ hloc' hstd⟩

end Certs

end CFSG.StandardType
