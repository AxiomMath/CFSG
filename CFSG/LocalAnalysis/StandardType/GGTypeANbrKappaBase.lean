module

public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.bstar_inf_centralizer_L {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  exact inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1 hLx hS.2.2.2.2

theorem GGConfig.orderOf_x {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) : orderOf x = p := by
  obtain ⟨hp, hBs, hxB, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have := Fact.mk hp
  exact orderOf_eq_prime (hBs.2 x hxB) hS.2.2.1

theorem GGConfig.card_bstar_inf_centralizer_L {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
  rw [hcfg.bstar_inf_centralizer_L, Nat.card_zpowers, hcfg.orderOf_x]

theorem GGNbr.bstar_inf_centralizer_eq_zpowers {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K) (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    (hJK : J ≤ K) : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hxB : x ∈ B := hS.2.1
  have hyB : y ∈ B := hnbr.1.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hxy : x * y = y * x :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨y, hyB⟩)
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hx
    apply hnbr.2.2.2
    have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hx
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
    exact bot_le
  apply le_antisymm
  · rintro c ⟨hcBs, hcK⟩
    have hcD : c ∈ D := hCJ ⟨hcBs, Subgroup.centralizer_le hJK hcK⟩
    rw [hnbr.2.1] at hcD
    exact mem_zpowers_of_mem_closure_pair hp hxp hxy hyK hxK hcD hcK
  · exact Subgroup.zpowers_le.mpr ⟨hcfg.2.1.1 hyB, hyK⟩

theorem GGNbr.card_bstar_inf_centralizer {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K) (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    (hJK : J ≤ K) : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = p := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hy : orderOf y = p :=
    orderOf_eq_prime (hnbr.1.1.1.2 y hnbr.1.2.1) hnbr.1.2.2.1
  rw [hnbr.bstar_inf_centralizer_eq_zpowers hcfg hCJ hJK, Nat.card_zpowers, hy]

end CFSG.StandardType

end
