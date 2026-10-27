module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenCand
public import CFSG.Goldschmidt.Steps.LemmaXCore
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

theorem fstarSubOf_eq_top_of_isComponentOf {K Y : Subgroup (MulAut W)}
    (hK : IsComponentOf K Y) : fstarSubOf K = ⊤ := by
  have hF : CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar K = K :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.fstar_eq_self_of_isQuasisimple hK.2.2
  unfold fstarSubOf
  rw [hF, Subgroup.subgroupOf_self]

theorem nonempty_acandidate_aParam_self [Finite W] {K Y : Subgroup (MulAut W)} [Finite ↥K]
    (hW : ∀ w : W, w ^ 2 = 1) (hK : IsComponentOf K Y) :
    Nonempty (ACandidate ↥K (E3.aParam K)) := by
  have hKq : CFSG.IsQuasisimple ↥K := (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hK.2.2
  have hfsub : fstarSubOf K = ⊤ := fstarSubOf_eq_top_of_isComponentOf hK
  have hLn : (fstarSubOf K).Normal := hfsub ▸ inferInstance
  have hLq : CFSG.IsQuasisimple ↥(fstarSubOf K) := by
    rw [hfsub]
    exact (CFSG.Quasithin.A3.isQuasisimple_iff_open).2
      (CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hK.2.2)
  let e : ↥K ≃* ↥(fstarSubOf K) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hfsub).symm
  exact nonempty_aCandidate_of_surjective hKq hW K hLn hLq e.toMonoidHom e.surjective

theorem w4Lem7_7_two_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y K A : Subgroup (MulAut W)}
    {k : ℕ} [Finite ↥K] (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hlt : ∀ n, Nonempty (ACandidate ↥K n) → n < k) : 2 ≤ k := by
  have h2prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have h2 : 2 ∣ Nat.card ↥K :=
    CFSG.Goldschmidt.LemmaX.two_dvd_card_of_isQuasisimple hq
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2
  have hto : orderOf (x : MulAut W) = 2 := by
    rw [Subgroup.orderOf_coe, hx]
  have ht2 : (x : MulAut W) ^ 2 = 1 := by
    rw [← hto]
    exact pow_orderOf_eq_one _
  have htne : (x : MulAut W) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hto
    omega
  have hzp : Subgroup.zpowers (x : MulAut W) ≠ ⊥ := by
    intro h
    have hmem : (x : MulAut W) ∈ (⊥ : Subgroup (MulAut W)) :=
      h ▸ Subgroup.mem_zpowers (x : MulAut W)
    exact htne (Subgroup.mem_bot.mp hmem)
  have hmem : Subgroup.zpowers (x : MulAut W) ∈ E3.aSet 1 K := by
    rw [E3.aSet_one]
    exact ⟨Subgroup.zpowers_le.mpr x.2, hzp, E3.isElemAbelian2_zpowers ht2⟩
  have h1 : 1 ≤ E3.aParam K := E3.le_aParam_of_mem_aSet (by norm_num) hmem
  have hlt' : E3.aParam K < k := hlt (E3.aParam K) (nonempty_acandidate_aParam_self hW hK)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
