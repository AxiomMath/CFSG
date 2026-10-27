module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre3S
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentPQ

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.HallHigman

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem b_mem_ZZ (h : FF84Hyp b L) : b ∈ Cen b ⊓ CenS L :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
    Subgroup.mem_centralizer_iff.2 fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (h.hLC hl)⟩

theorem pSolv3_ZZ (h : FF84Hyp b L) : IsPSolvable 3 ↥(Cen b ⊓ CenS L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ZZ := Cen b ⊓ CenS L with hZZ
  have hb3 : b ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one b
  set bt : ↥ZZ := ⟨b, b_mem_ZZ h⟩ with hbt
  have hbt3 : bt ^ 3 = 1 := Subtype.ext hb3
  have hbtord : orderOf bt = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact h.ord
  have hbc : bt ∈ Subgroup.center ↥ZZ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).1)
  have hcyc : ∀ P : Sylow 3 ↥ZZ, IsCyclic ↥(P : Subgroup ↥ZZ) := by
    intro P
    set ι : ↥ZZ →* ↥(CenS L) := Subgroup.inclusion (inf_le_right : ZZ ≤ CenS L) with hι
    have hinj : Function.Injective ι := Subgroup.inclusion_injective _
    obtain ⟨Q, hQ⟩ := (P.isPGroup'.map ι).exists_le_sylow
    haveI := h.cyc Q
    haveI : IsCyclic ↥((P : Subgroup ↥ZZ).map ι) := Subgroup.isCyclic_of_le hQ
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective _ ι hinj).symm.toMonoidHom
      (Subgroup.equivMapOfInjective _ ι hinj).symm.surjective
  have hcen : ∀ x : ↥ZZ, orderOf x = 3 → x ∈ Subgroup.center ↥ZZ := by
    intro x hx
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    obtain ⟨P, hP⟩ := (isPGroup_zpowers (p := 3) (k := 1) (by simpa using hx3)).exists_le_sylow
    have hbn : (Subgroup.zpowers bt).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hbc hn) g, mul_inv_cancel_right]
      exact hn⟩
    have hbP : Subgroup.zpowers bt ≤ P :=
      (isPGroup_zpowers (p := 3) (k := 1) (by simpa using hbt3)).le_sylow_of_normal P
    haveI := hcyc P
    have hxP : x ∈ (P : Subgroup ↥ZZ) := hP (Subgroup.mem_zpowers x)
    have hbP' : bt ∈ (P : Subgroup ↥ZZ) := hbP (Subgroup.mem_zpowers bt)
    set x' : ↥(P : Subgroup ↥ZZ) := ⟨x, hxP⟩
    set b' : ↥(P : Subgroup ↥ZZ) := ⟨bt, hbP'⟩
    have hox : orderOf x' = 3 := by rw [← Subgroup.orderOf_coe]; exact hx
    have hob : orderOf b' = 3 := by rw [← Subgroup.orderOf_coe]; exact hbtord
    have hz : Subgroup.zpowers x' = Subgroup.zpowers b' :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hob])
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hz ▸ Subgroup.mem_zpowers x')
    have : x = bt ^ k := by
      have := congrArg Subtype.val hk
      simpa [x', b'] using this.symm
    rw [this]
    exact Subgroup.zpow_mem _ hbc k
  obtain ⟨N, hN, hcop, hq⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.hasNormalPComplement_of_cyclic_sylow_central
      (p := 3) hcyc hcen
  exact pSolv3_of_normal N (pSolv3_of_coprime hcop) (pSolv3_of_pGroup hq)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
