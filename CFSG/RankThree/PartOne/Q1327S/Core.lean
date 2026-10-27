module

public import CFSG.RankThree.PartOne.KS.LyFiveGeneric
public import CFSG.RankThree.PartOne.S15K.SL2Model

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem simple_of_model {K : Type} [Group K] {g : ℕ} (hK : StatedClassicalModel K .PSL 2 2 g) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  have hq := S15K.isQuasisimple_of_model hK
  have hz := S15K.center_eq_bot_of_model hK
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem false_of_fiveCoreAt' {Q : Type} [Group Q] [Finite Q] {c : Q} (hF : FiveCoreAt' c)
    {Kb : Subgroup Q} (hKc : Kb ≤ Subgroup.centralizer ({c} : Set Q))
    (hKN : (Kb.subgroupOf (Subgroup.centralizer ({c} : Set Q))).Normal)
    (hsimple : IsSimpleGroup Kb) (hnab : ∃ a b : Kb, a * b ≠ b * a) : False := by
  obtain ⟨F, hFC, hFn, hFp, hFc⟩ := hF
  have hKn : ∀ g ∈ Subgroup.centralizer ({c} : Set Q), ∀ k ∈ Kb, g * k * g⁻¹ ∈ Kb := by
    intro g hg k hk
    have := hKN.conj_mem ⟨k, hKc hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hnot : ¬ Kb ≤ F := by
    intro hKF
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hp : IsPGroup 5 Kb := hFp.to_le hKF
    have : Group.IsNilpotent Kb := hp.isNilpotent
    have hsol : Group.IsSolvable Kb := inferInstance
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsol a b)
  have hnormN : ((Kb ⊓ F).subgroupOf Kb).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnK, hnF⟩ := hn
    have hkK : (k : Q) ∈ Kb := k.2
    refine ⟨?_, ?_⟩
    · exact Kb.mul_mem (Kb.mul_mem hkK hnK) (Kb.inv_mem hkK)
    · exact hFn (k : Q) (hKc hkK) (n : Q) hnF
  have := hnormN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Kb ⊓ F).subgroupOf Kb) with h | h
  · refine hnot fun k hk => ?_
    apply hFc k (hKc hk)
    intro f hf
    have h1 : k * f * k⁻¹ * f⁻¹ ∈ Kb ⊓ F := by
      refine ⟨?_, ?_⟩
      · have := hKn f (hFC hf) k⁻¹ (Kb.inv_mem hk)
        have h2 : k * f * k⁻¹ * f⁻¹ = k * (f * k⁻¹ * f⁻¹) := by group
        rw [h2]
        exact Kb.mul_mem hk this
      · exact F.mul_mem (hFn k (hKc hk) f hf) (F.inv_mem hf)
    have h3 : (⟨k * f * k⁻¹ * f⁻¹, h1.1⟩ : Kb) ∈ (Kb ⊓ F).subgroupOf Kb :=
      Subgroup.mem_subgroupOf.2 h1
    rw [h, Subgroup.mem_bot] at h3
    have h4 : k * f * k⁻¹ * f⁻¹ = 1 := congrArg Subtype.val h3
    calc k * f = k * f * k⁻¹ * f⁻¹ * (f * k) := by group
      _ = f * k := by rw [h4, one_mul]
  · refine absurd (fun k hk => ?_) hnot
    have h3 : (⟨k, hk⟩ : Kb) ∈ (Kb ⊓ F).subgroupOf Kb := by rw [h]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 h3).2

end CFSG.RankThree.PartOne.Q1327S
