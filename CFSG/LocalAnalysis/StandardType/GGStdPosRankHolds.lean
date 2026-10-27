module

public import CFSG.LocalAnalysis.StandardType.GGStdPosRankDefs
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
import CFSG.LocalAnalysis.StandardType.GGStdPosRankLift
import CFSG.LocalAnalysis.StandardType.GGStdPosRankCard
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPosBoundsHyp_of_rank {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    {t : StatedLieTag} {n m r : ℕ} (hp : p.Prime)
    (hcard : p ^ (m - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs)
    (hrm : r + 1 ≤ m) (h1 : bnRank t n - 1 ≤ r) (h2 : ¬ GGKGPosTorsion p t n → bnRank t n ≤ r) :
    GGKGPosBoundsHyp p Bs X t n :=
  ⟨fun ht => le_trans (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right hp.pos (by have := h2 ht; omega))) hcard,
    le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))) hcard⟩

theorem ggKGPosBoundsStmt_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
            GGKGPosBaseHyp p Bs X t n f ψ → GGKGPosBoundsHyp p Bs X t n := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg X hX _ t n f ψ hbase
  obtain ⟨⟨hp, hp2, hadm, h3⟩, ⟨hker, hψX, ht, hpf⟩, -, -⟩ := hbase
  obtain ⟨y, -, hy1, hyp, hXy, -⟩ := ggKGPos_exists_central_elt hcfg hX
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
  exact ggKGPosBoundsHyp_of_rank hp (ggKGPos_pow_mul_card_le hcfg hX)
    (succ_le_twoLocalRank_of_torusLift hp hXy hyp hy1 hcomm θ hlift) h1 h2

end CFSG.StandardType

end
