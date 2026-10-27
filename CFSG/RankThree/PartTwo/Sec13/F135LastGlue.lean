module

public import CFSG.RankThree.PartTwo.Sec13.F135LastGlueA
public import CFSG.RankThree.PartTwo.Sec13.F135LastGlueB
public import CFSG.RankThree.PartTwo.Sec13.F135LastCore
public import CFSG.RankThree.PartTwo.Sec13.F135LastKFacts
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofOneTwoSteps

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open CritProof
open scoped commutatorElement

section Glue

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {p : ℕ}
  {C : Subgroup (CFSG.pCore p L)}

theorem isPGroup_eOf (hcrit : Crit135 L p C) {z : G} (hz : z ∈ L) (Y : Subgroup G) :
    IsPGroup p (eOf (dPrime L p C z) Y) := by
  have h1 : IsPGroup p ↥(dPrime L p C z ⊓ cM Y : Subgroup G) :=
    (isPGroup_dPrime hcrit hz).to_le inf_le_left
  exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : dPrime L p C z ⊓ cM Y ≤ cM Y)).symm

theorem false_of_cfg5 (hK26 : KFactTwoSix) (hK437 : KFactFourCubeSeven) (hMult : KFactMultiplier)
    (hK3 : KFactK3) (c5 : Cfg5 G A c L p C) (hid : Identified p (↥c5.J ⧸ Subgroup.center ↥c5.J)) :
    False := by
  classical
  have hcrit : Crit135 L p C := c5.crit
  have hp : p.Prime := hcrit.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := c5.p_ge_seven
  have hD : Sec13Data G A c L := c5.data
  set Y := c5.Y with hY
  set Dp := dPrime L p C c5.z with hDp
  have hDpD : Dp ≤ dOf L p C := dPrime_le_dOf hcrit c5.z_mem
  have hYDp : Y ≤ Dp := (c5.Y_le).trans inf_le_left
  have hc_mem : c ∈ cM Y := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyL : y ∈ L := dOf_le_L (hDpD (hYDp hy))
    have h := L_le_centralizer hD hyL
    rw [Subgroup.mem_centralizer_iff] at h
    exact (h c rfl).symm
  let cM' : ↥(cM Y) := ⟨c, hc_mem⟩
  have hc3 : orderOf cM' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_c hD
  have hEp : IsPGroup p (eOf Dp Y) := isPGroup_eOf hcrit c5.z_mem Y
  set X : Subgroup G := Subgroup.centralizer ({c} : Set G) with hX
  set P₀ : Subgroup ↥(cM Y) := (CFSG.Open.pCoreOf p X).subgroupOf (cM Y) with hP₀
  have hP₀p : IsPGroup p P₀ := by
    intro s
    have hs : ((s : ↥(cM Y)) : G) ∈ CFSG.Open.pCoreOf p X := Subgroup.mem_subgroupOf.1 s.2
    obtain ⟨k, hk⟩ := isPGroup_pCoreOf p X ⟨((s : ↥(cM Y)) : G), hs⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hEP₀ : eOf Dp Y ≤ P₀ := by
    intro e he
    have he' : (e : G) ∈ Dp ⊓ cM Y := he
    exact dOf_le_pCoreOf hD hcrit (hDpD he'.1)
  have hP₀C : P₀ ≤ Subgroup.centralizer ({cM'} : Set ↥(cM Y)) := by
    intro x hx
    have hx' : (x : G) ∈ CFSG.Open.pCoreOf p X := hx
    have hxX : (x : G) ∈ X := (Subgroup.map_subtype_le _) hx'
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := Subgroup.mem_centralizer_iff.1 hxX c rfl
    exact Subtype.ext this
  have hP₀N : ∀ g ∈ Subgroup.centralizer ({cM'} : Set ↥(cM Y)),
      g ∈ Subgroup.normalizer (P₀ : Set ↥(cM Y)) := by
    intro g hg
    have hgX : (g : G) ∈ X := by
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact congrArg Subtype.val (hg cM' rfl)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact mem_pCoreOf_conj p X hgX (x : G)
  haveI := c5.R_normal
  have hR : Nat.Coprime (Nat.card c5.R) (2 * p) :=
    Nat.Coprime.mul_right (Nat.coprime_two_right.2 c5.R_odd) c5.R_coprime.symm
  have hJ : CFSG.IsQuasisimple c5.J := c5.J_comp.1
  have hJnt : ∃ e ∈ eOf Dp Y, ∃ j ∈ c5.J, ⁅(e : ↥(cM Y) ⧸ c5.R), j⁆ ≠ 1 := by
    have h2 : 2 ≤ p ^ 3 := by
      calc 2 ≤ 7 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp7 3
    obtain ⟨ē, hē, j, hj, hne⟩ :=
      exists_noncentral_of_relIndex c5.J ((eOf Dp Y).map (QuotientGroup.mk' c5.R)) p h2 c5.E_index
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hē
    exact ⟨e, he, j, hj, hne⟩
  have hrank3 := hrank3_of_evenRank hD.toPartTwoStanding.toTheoremFourHyp.evenRank_eq (cM Y)
  have hZ := coprime_center_of_identification hMult hp hp7 c5.J hJ hid
  have hEJ : ∀ ē ∈ (eOf Dp Y).map (QuotientGroup.mk' c5.R),
      ē ∈ Subgroup.normalizer (c5.J : Set (↥(cM Y) ⧸ c5.R)) := by
    rintro _ ⟨e, he, rfl⟩
    exact c5.J_normE e he
  have hK3' := hK3_of_kfact hK3 c5.J hJ ((eOf Dp Y).map (QuotientGroup.mk' c5.R)) p
    (hEp.map _) hEJ hid c5.E_index
  have hK3'' : ∀ g ∈ Subgroup.normalizer (c5.J : Set (↥(cM Y) ⧸ c5.R)), g ^ 3 = 1 →
      (∀ e ∈ eOf Dp Y, g * (e : ↥(cM Y) ⧸ c5.R) = (e : ↥(cM Y) ⧸ c5.R) * g) →
      ∀ j ∈ c5.J, ∀ k ∈ c5.J, ⁅⁅j, g⁆, k⁆ = 1 := fun g hg hg3 hcomm =>
    hK3' g hg hg3 (by rintro _ ⟨e, he, rfl⟩; exact hcomm e he)
  have hS := hasTwoSix_or_fourCubeSeven_of_identification hK26 hK437 hid
  exact last_step p hp7 cM' hc3 (eOf Dp Y) P₀ hEp hP₀p hEP₀ hP₀C hP₀N c5.R hR c5.J hJ
    c5.J_normE (c5.J_normc hc_mem) hJnt hrank3 hZ hK3'' hS

end Glue

theorem item135A7OneTwoCrit2_of_parts (h0 : R0) (h1 : R1) (h2 : R2) (h3 : R3) (h4 : R4) (h5 : R5)
    (hK26 : KFactTwoSix) (hK437 : KFactFourCubeSeven) (hMult : KFactMultiplier)
    (hK3 : KFactK3) : Item135A7OneTwoCrit2 := by
  intro G _ _ A c L hD hST hnq hO2 hm hO hA7 hprod hstar hcL h9 h12 p C hcrit hodd h2c
  have c0 : Cfg0 G A c L p C :=
    ⟨hD, hST, hnq, hO2, hm, hO, hA7, hprod, hstar, hcL, h9, h12, hcrit, hodd, h2c⟩
  obtain ⟨c1⟩ := h0 G A c L p C c0
  obtain ⟨c2⟩ := h1 G A c L p C c1
  obtain ⟨c3⟩ := h2 G A c L p C c2
  obtain ⟨c4⟩ := h3 G A c L p C c3
  obtain ⟨c5⟩ := h4 G A c L p C c4
  exact false_of_cfg5 hK26 hK437 hMult hK3 c5 (h5 G A c L p C c5)

end CFSG.RankThree.PartTwo.Sec13.F135Last
