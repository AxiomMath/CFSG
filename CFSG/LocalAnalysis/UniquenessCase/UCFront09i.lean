module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_center_pCoreOf (M : Subgroup G) :
    M ≤ normalizer ((pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) : Subgroup G) : Set G) :=
  (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M).trans
      (Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _)))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem le_normalizer_zO2 {M X : Subgroup G} (hXM : X ≤ M) :
    X ≤ normalizer
      ((pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X : Subgroup G) : Set G) :=
  (le_inf (hXM.trans (le_normalizer_center_pCoreOf M)) Subgroup.le_normalizer).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem zO2_le_pCoreOf {M X : Subgroup G} (hXM : X ≤ M) :
    pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X ≤ pCoreOf 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (le_normalizer_zO2 hXM)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (inf_le_left.trans inf_le_left))

theorem zO2_ne_bot {M X : Subgroup G}
    (hZ : ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ ≠ ⊥) :
    pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X ≠ ⊥ :=
  fun h => hZ (by rw [h, Subgroup.commutator_bot_left])

theorem commutator_zO2_le {M X : Subgroup G} (hXM : X ≤ M) :
    ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ ≤
      pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 (le_normalizer_zO2 hXM)

theorem commutator_zO2_le_centralizer {M X : Subgroup G} (hXM : X ≤ M) :
    ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ ≤
      centralizer (⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ : Subgroup G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact Subgroup.mem_centralizer_iff.1 (commutator_zO2_le hXM ha).1.2 b
    (commutator_zO2_le hXM hb).1.1

theorem commutatorElement_eq_one_of_commute {z d : G} {m n : ℕ} (hc : Commute ⁅z, d⁆ d)
    (hd : d ^ n = 1) (hm : ⁅z, d⁆ ^ m = 1) (hmn : Nat.Coprime m n) : ⁅z, d⁆ = 1 := by
  have h1 : z * d * z⁻¹ = ⁅z, d⁆ * d := by rw [commutatorElement_def]; group
  have hn : ⁅z, d⁆ ^ n = 1 := by
    have h2 : (z * d * z⁻¹) ^ n = 1 := by rw [conj_pow, hd, mul_one, mul_inv_cancel]
    rwa [h1, hc.mul_pow, hd, mul_one] at h2
  have h := pow_gcd_eq_one.2 ⟨hm, hn⟩
  rwa [Nat.Coprime.gcd_eq_one hmn, pow_one] at h

theorem not_le_centralizer_commutator {M X : Subgroup G} (hXM : X ≤ M) (hX : Opp 3 X = X)
    (hZ : ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ ≠ ⊥) :
    ¬ X ≤ centralizer (⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hXC
  apply hZ
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine hX.symm.le.trans ?_
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  rw [Subgroup.closure_le]
  rintro d ⟨hdX, k, hk⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro z hz
  have hc := Subgroup.commutator_mem_commutator (SetLike.mem_coe.1 hz) hdX
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨_, (commutator_zO2_le hXM hc).1.1⟩
  have hj' : ⁅z, d⁆ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hd : d ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one d
  exact commutatorElement_eq_one_iff_mul_comm.1 (commutatorElement_eq_one_of_commute
    (Subgroup.mem_centralizer_iff.1 (hXC hdX) _ hc) hd hj' (Nat.Coprime.pow j k (by decide)))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
