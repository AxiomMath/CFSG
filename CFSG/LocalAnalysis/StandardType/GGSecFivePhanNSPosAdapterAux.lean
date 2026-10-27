module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

lemma ggNSPosPD_routeCfg_rank {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    p ^ 4 ≤ Nat.card ↥B := by
  have hp : p.Prime := hcfg.tableB_facts.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hcard : Nat.card ↥B = p ^ LargeEvenTwoLocalRank p G := hS.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
    _ = Nat.card ↥B := hcard.symm

lemma ggNSPosPD_routeCfg_cent_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = p := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxS : x ∈ B := hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hBs : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hcfg.bstar_inf_centralizer_L
  have hBle : B ≤ Bs := hcfg.2.1.1
  have hEq : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hBle hz.1, hz.2⟩
      rwa [hBs] at hz'
    · exact Subgroup.zpowers_le.mpr ⟨hxS, hxCL⟩
  rw [hEq, Nat.card_zpowers, hcfg.orderOf_x]

lemma ggNSPosPD_routeCfg_cent_K {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {D J : Subgroup G} {y : G} {K : Subgroup G} (hp : p.Prime)
    (hnbr : GGNbr p B x D J y K) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G)) = p := by
  have hyB : y ∈ B := hnbr.1.2.1
  have hy_ne : y ≠ 1 := hnbr.1.2.2.1
  have hK_cy : K ≤ Subgroup.centralizer ({y} : Set G) := hnbr.1.2.2.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK_cy hk)
  have hiff := hnbr.1.2.2.2.2.2
  have hEq : B ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
    apply le_antisymm
    · intro z hz
      have hzB : z ∈ B := hz.1
      have hzK : z ∈ Subgroup.centralizer (K : Set G) := hz.2
      have hzN : z ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.centralizer_le_normalizer _ hzK
      have hcm : ⁅K, Subgroup.zpowers z⁆ ≤ LargeEvenPPrimeCoreOf p K := by
        have hz_le : Subgroup.zpowers z ≤ Subgroup.centralizer (K : Set G) :=
          Subgroup.zpowers_le.mpr hzK
        have hbot : ⁅K, Subgroup.zpowers z⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            (Subgroup.le_centralizer_iff.mp hz_le)
        rw [hbot]
        exact bot_le
      exact (hiff z).mp ⟨hzB, hzN, hcm⟩
    · exact Subgroup.zpowers_le.mpr ⟨hyB, hyK⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [hEq, Nat.card_zpowers]
  exact orderOf_eq_prime (hnbr.1.1.1.2 y hyB) hy_ne

end CFSG.StandardType

end
