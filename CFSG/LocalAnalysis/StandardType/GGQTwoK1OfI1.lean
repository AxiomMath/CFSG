module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsLK
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2k1_normal_eq_top_or_le_center {Q : Type*} [Group Q]
    (hQ : CFSG.Assembly.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

private theorem ggQ2k1_core_conj {G : Type} [Group G] {p : ℕ} {K : Subgroup G} {g z : G}
    (hg : g ∈ K) (hz : z ∈ LargeEvenPPrimeCoreOf p K) :
    g * z * g⁻¹ ∈ LargeEvenPPrimeCoreOf p K := by
  rw [LargeEvenPPrimeCoreOf] at hz ⊢
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (LargeEvenPPrimeCore.normal p ↥K).conj_mem z' hz' ⟨g, hg⟩

theorem ggQ2_K1_of_I1 {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) :
    GGQTwoK1 p B Bs x D J := by
  intro y K hnbr b hb hKb
  obtain ⟨hcfg, -, hIDAll, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBsabel : IsElemAbelian p Bs := hBstar.2.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hStdSub
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hStdSub.1.2.2.2.2.2.1.2.2
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJq
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hIDAll.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBstar.1 hStdSub.1 hBsL
  have hyB : y ∈ B := hnbr.1.2.1
  have hKc : K ≤ Subgroup.centralizer ({y} : Set G) := hnbr.1.2.2.2.1
  have hKpc : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hnbr.1.2.2.2.2.1
  have hJK : J ≤ K := le_of_ggNbr hLB hI hStdSub hpJ hnbr
  have hBsy : Bs ≤ Subgroup.centralizer ({y} : Set G) :=
    (GGBstar.le_centralizer hBstar).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyB))
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    GGDichotomy.le_normalizer_of_pComponent hBsy hKpc hJK hJJ hpJ hBsJ
  have hcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p K)) := by
    rw [LargeEvenPPrimeCoreOf, LargeEvenPPrimeCore,
      Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hbJ : b ∈ Subgroup.normalizer (J : Set G) := hBsJ hb
  have hZ0 : ⁅J, Subgroup.zpowers b⁆ ≤ J ⊓ LargeEvenPPrimeCoreOf p K := by
    rw [Subgroup.commutator_le]
    intro j hj g hg
    refine ⟨?_, hKb (Subgroup.commutator_mem_commutator (hJK hj) hg)⟩
    have hgN : g ∈ Subgroup.normalizer (J : Set G) := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact zpow_mem hbJ k
    have h1 : g * j⁻¹ * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hgN j⁻¹).mp (J.inv_mem hj)
    have h2 : j * (g * j⁻¹ * g⁻¹) ∈ J := J.mul_mem hj h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hcent : ∀ z ∈ J ⊓ LargeEvenPPrimeCoreOf p K, ∀ j ∈ J, z * j = j * z := by
    have hNnorm : ((J ⊓ LargeEvenPPrimeCoreOf p K).subgroupOf J).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨?_, ?_⟩
      · exact J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2)
      · exact ggQ2k1_core_conj (hJK g.2) hn.2
    rcases ggQ2k1_normal_eq_top_or_le_center hJq hNnorm with htop | hle
    · exfalso
      have hJO : J ≤ LargeEvenPPrimeCoreOf p K := fun j hj => by
        have hmem : (⟨j, hj⟩ : ↥J) ∈ (J ⊓ LargeEvenPPrimeCoreOf p K).subgroupOf J := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hmem).2
      have hdvd : p ∣ Nat.card (LargeEvenPPrimeCoreOf p K) :=
        hpJ.trans (Subgroup.card_dvd_of_le hJO)
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    · intro z hz j hj
      have hmem : (⟨z, hz.1⟩ : ↥J) ∈ (J ⊓ LargeEvenPPrimeCoreOf p K).subgroupOf J :=
        Subgroup.mem_subgroupOf.mpr hz
      have hzc := hle hmem
      have := Subgroup.mem_center_iff.mp hzc ⟨j, hj⟩
      exact congrArg Subtype.val this.symm
  have hJb1 : ⁅⁅J, Subgroup.zpowers b⁆, J⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun c hc => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
    exact (hcent c (hZ0 hc) j hj).symm
  have hJb2 : ⁅⁅Subgroup.zpowers b, J⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Subgroup.zpowers b) J]
    exact hJb1
  have hJb : ⁅J, Subgroup.zpowers b⁆ = ⊥ := by
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hJb1 hJb2
    rwa [hJJ] at h3
  have hbcJ : ∀ j ∈ J, b * j = j * b := by
    intro j hj
    have hh := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJb hj
    exact Subgroup.mem_centralizer_iff.mp hh b (Subgroup.mem_zpowers b)
  have hbD : b ∈ D := hI1 b hb hbcJ
  have hDB : D ≤ B := hStdSub.1.1
  exact (hnbr.1.2.2.2.2.2 b).mp ⟨hDB hbD, hBsK hb, hKb⟩

end CFSG.StandardType

end
