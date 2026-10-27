module

public import CFSG.RankThree.PartTwo.Census.TransitiveLift
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.CoverRoots
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Open.QuasithinDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate8171
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

namespace DoubleCoverRanksTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.G2FieldFour CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.EvenSmallLie.GTwoFour

section G2

variable {K : Type} [Field K]

theorem isConj_rootX_c {s : K}
    (hs : s ≠ 0) : IsConj (rootX rootC s) (rootX rootC (1 : K)) := by
  refine (isConj_iff.mpr ⟨⟨torusElt .G2 K g2ia (Units.mk0 s hs), torusElt_mem_adjointGroup _ _⟩,
    Subtype.ext ?_⟩).symm
  change torusElt .G2 K g2ia (Units.mk0 s hs) * pinnedX .G2 K g2c 1 *
    (torusElt .G2 K g2ia (Units.mk0 s hs))⁻¹ = pinnedX .G2 K g2c s
  rw [torus_a_c, Units.val_mk0, mul_one]

theorem isConj_rootX_b [CharP K 2]
    {s : K} (hs : s ≠ 0) :
    IsConj (rootX rootB s) (rootX rootC (1 : K)) := by
  refine IsConj.trans ?_ (isConj_rootX_c hs)
  refine (isConj_iff.mpr ⟨⟨weylElt .G2 K g2ia 1, weylElt_mem_adjointGroup _ _⟩,
    Subtype.ext ?_⟩).symm
  change weylElt .G2 K g2ia 1 * pinnedX .G2 K g2c s * (weylElt .G2 K g2ia 1)⁻¹ =
    pinnedX .G2 K g2b s
  rw [weylElt_conj g2ia isRoot_g2c, reflect_a_c]

theorem eq_zero_of_rootX_mul_eq_one
    {s t : K}
    (h : rootX rootB s * rootX rootC t = 1) : s = 0 ∧ t = 0 := by
  have h' : g2N (0 : K) 0 0 0 s t = g2N 0 0 0 0 0 0 := by
    have hv := congrArg Subtype.val h
    simp only [g2N, pinnedX_zero, one_mul, mul_one]
    exact hv
  obtain ⟨-, -, -, -, h5, h6⟩ := g2N_injective h'
  exact ⟨h5, h6⟩

noncomputable def rootBC
    [CharP K 2] :
    Multiplicative (K × K) →* adjointGroup .G2 K where
  toFun v := rootX rootB (Multiplicative.toAdd v).1 * rootX rootC (Multiplicative.toAdd v).2
  map_one' := by simp [rootX_zero]
  map_mul' v w := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, rootX_add]
    have h := (commute_rootX_bc (K := K) (Multiplicative.toAdd w).1
      (Multiplicative.toAdd v).2).eq
    simp only [mul_assoc]
    rw [← mul_assoc (rootX rootC (Multiplicative.toAdd v).2), ← h]
    simp only [mul_assoc]

end G2

section Cover

variable {K : Type} [Field K] [CharP K 2] {M : Type} [Group M]

theorem lift_rootBC
    (hK : Nat.card K = 4)
    {π : M →* adjointGroup .G2 K} (hπ : Function.Surjective π)
    (hker : ∀ k, π k = 1 → k ∈ Subgroup.center M) {z : M} (hz1 : z ≠ 1)
    (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z) {y : M} (hy : π y ∈ (rootBC (K := K)).range) :
    ∃ β γ k : M, y = β * γ * k ∧ π k = 1 ∧ β * β = 1 ∧ γ * γ = 1 ∧
      (∃ s, π β = rootX rootB s) ∧ ∃ t, π γ = rootX rootC t := by
  obtain ⟨v, hv⟩ := hy
  obtain ⟨β, hβ⟩ := hπ (rootX rootB (Multiplicative.toAdd v).1)
  obtain ⟨γ, hγ⟩ := hπ (rootX rootC (Multiplicative.toAdd v).2)
  have hsq : ∀ (m : M) (d : Fin Tag.G2.rank → ℤ) (s : K), π m = rootX d s →
      (s ≠ 0 → IsConj (rootX d s) (rootX rootC (1 : K))) → m * m = 1 := by
    intro m d s hm hconj
    by_cases hs : s = 0
    · have h1 : π m = 1 := by rw [hm, hs, rootX_zero]
      rcases (hz m).1 h1 with h | h
      · rw [h, mul_one]
      · rw [h]; exact mul_self_z hz1 hz
    · exact mul_self_eq_one_of_isConj_rootX_c hz1 hz hK hπ hker (by rw [hm]; exact hconj hs)
  refine ⟨β, γ, (β * γ)⁻¹ * y, by rw [mul_inv_cancel_left], ?_,
    hsq β _ _ hβ (fun hs => isConj_rootX_b hs), hsq γ _ _ hγ (fun hs => isConj_rootX_c hs),
    ⟨_, hβ⟩, ⟨_, hγ⟩⟩
  rw [map_mul, map_inv, map_mul, hβ, hγ, ← hv]
  exact inv_mul_cancel _

theorem five_le_pRank_adjointGroup
    [Finite K] (hK : Nat.card K = 4)
    [Finite M] (π : M →* adjointGroup .G2 K) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center M) (hZ : Nat.card (Subgroup.center M) = 2) :
    5 ≤ CFSG.pRank 2 M := by
  have hker' : ∀ k, π k = 1 → k ∈ Subgroup.center M := fun k hk => by
    rw [← hker]; exact hk
  have : Nontrivial (Subgroup.center M) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center M)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hcen : ∀ k ∈ Subgroup.center M, k = 1 ∨ k = z := by
    intro k hk
    by_contra hne
    push Not at hne
    have h3 : 3 ≤ Nat.card (Subgroup.center M) := by
      classical
      have := Fintype.ofFinite (Subgroup.center M)
      rw [Nat.card_eq_fintype_card]
      have hs : ({1, ⟨z, hzc⟩, ⟨k, hk⟩} : Finset (Subgroup.center M)).card = 3 := by
        refine Finset.card_eq_three.mpr ⟨1, ⟨z, hzc⟩, ⟨k, hk⟩, ?_, ?_, ?_, rfl⟩
        · exact fun h => hz1' (congrArg Subtype.val h).symm
        · exact fun h => hne.1 (congrArg Subtype.val h).symm
        · exact fun h => hne.2 (congrArg Subtype.val h).symm
      rw [← hs]
      exact Finset.card_le_univ _
    omega
  have hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z := fun k => by
    refine ⟨fun hk => hcen k (hker' k hk), fun h => ?_⟩
    rcases h with h | h
    · rw [h, map_one]
    · rw [h]
      exact MonoidHom.mem_ker.mp (by rw [hker]; exact hzc)
  have hW : ∀ y y' : M, π y ∈ (rootBC (K := K)).range → π y' ∈ (rootBC (K := K)).range →
      y * y' = y' * y := by
    intro y y' hy hy'
    obtain ⟨β, γ, k, rfl, hk, -, -, ⟨s, hβ⟩, ⟨t, hγ⟩⟩ := lift_rootBC hK hπ hker' hz1' hz hy
    obtain ⟨β', γ', k', rfl, hk', -, -, ⟨s', hβ'⟩, ⟨t', hγ'⟩⟩ := lift_rootBC hK hπ hker' hz1' hz hy'
    have c₁ : Commute β β' := lift_commute_b hπ hker' hβ hβ'
    have c₂ : Commute β γ' := lift_commute_b_c hπ hker' hβ hγ'
    have c₃ : Commute γ β' := (lift_commute_b_c hπ hker' hβ' hγ).symm
    have c₄ : Commute γ γ' := lift_commute_c hπ hker' hγ hγ'
    have ck : ∀ x, Commute x k := fun x => Subgroup.mem_center_iff.mp (hker' k hk) x
    have ck' : ∀ x, Commute x k' := fun x => Subgroup.mem_center_iff.mp (hker' k' hk') x
    have ha : Commute (β * γ) (β' * γ') := (c₁.mul_right c₂).mul_left (c₃.mul_right c₄)
    exact (Commute.mul_left (ha.mul_right (ck' _)) (((ck _).symm).mul_right (ck' _))).eq
  have hsq : ∀ y : M, π y ∈ (rootBC (K := K)).range → ∃ c : M, π c = 1 ∧ y ^ 2 = c ^ 2 := by
    intro y hy
    obtain ⟨β, γ, k, rfl, hk, hβ2, hγ2, ⟨s, hβ⟩, ⟨t, hγ⟩⟩ := lift_rootBC hK hπ hker' hz1' hz hy
    have c₁ : Commute β γ := lift_commute_b_c hπ hker' hβ hγ
    have ck : Commute (β * γ) k := Subgroup.mem_center_iff.mp (hker' k hk) _
    refine ⟨k, hk, ?_⟩
    rw [ck.mul_pow, c₁.mul_pow, sq, sq, hβ2, hγ2, one_mul, one_mul]
  obtain ⟨A, hA, hcard⟩ := TransitiveLift.exists_isElementaryAbelian_card hπ (by
    rw [hker]) hW hsq
  have hinj : Function.Injective (rootBC (K := K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    obtain ⟨h1, h2⟩ := eq_zero_of_rootX_mul_eq_one (K := K) hv
    rw [Subgroup.mem_bot]
    apply Multiplicative.toAdd.injective
    exact Prod.ext h1 h2
  have hW16 : Nat.card (rootBC (K := K)).range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, hK]
  have hΩ : Nat.card {c : M // π c = 1 ∧ c ^ 2 = 1} = 2 := by
    have hΩ' : ∀ c ∈ Subgroup.center M, π c = 1 ∧ c ^ 2 = 1 := by
      intro c hc
      rcases hcen c hc with h | h
      · rw [h, map_one, one_pow]; exact ⟨rfl, rfl⟩
      · rw [h, sq]; exact ⟨(hz z).2 (Or.inr rfl), mul_self_z hz1' hz⟩
    refine (Nat.card_congr ?_).trans hZ
    exact
      { toFun := fun c => ⟨c.1, hker' _ c.2.1⟩
        invFun := fun c => ⟨c.1, hΩ' c.1 c.2⟩
        left_inv := fun c => rfl
        right_inv := fun c => rfl }
  exact TransitiveLift.le_pRank_of_card hA (k := 5) (by rw [hcard, hW16, hΩ]; norm_num)

end Cover

theorem noRankThreeDoubleCover_g24 :
    ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      q.exponent = 2 → NoRankThreeDoubleCover (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq hp he J _ _ _ hZ ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have hKq : Nat.card (GaloisField 2 2) = q.card := by
    rw [hK, TauCeti.PrimePower.card_def, hp, he]; norm_num
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hp (GaloisField 2 2) hKq
  let eA : AdjointQuotient .G2 (GaloisField 2 2) ≃* adjointGroup .G2 (GaloisField 2 2) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  let f : J ⧸ Subgroup.center J ≃* adjointGroup .G2 (GaloisField 2 2) := (e.trans b.symm).trans eA
  let π : J →* adjointGroup .G2 (GaloisField 2 2) :=
    f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hπ : Function.Surjective π := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center J := by
    ext x
    rw [MonoidHom.mem_ker]
    change f (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff f f.injective, QuotientGroup.eq_one_iff]
  have h5 := five_le_pRank_adjointGroup hK π hπ hker hZ
  omega

end DoubleCoverRanksTwo

end CFSG.RankThree.PartTwo.Sec4.Census
