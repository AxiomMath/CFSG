module

public import CFSG.RankThree.PartOne.Census3.OpenCases
public import CFSG.RankThree.PartTwo.Census.Spin.Exclude
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co2
public import CFSG.Monster.Existence.Co2Bridge
public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.B.Cbar.LocalStructure
public import CFSG.Monster.B.Cbar.FourGroupBar
public import CFSG.RankThree.PartOne.TCB.BabyRoute
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3138
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate8012
public import Certificates.Certificate8954
public import Certificates.Certificate9201
public import Certificates.Certificate10093
public import Certificates.Certificate10095
public import Certificates.Certificate10098
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10103
public import Certificates.Certificate10104
public import Certificates.Certificate16026
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.YGroups.DCE.B433Check

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.VisQuot CFSG.Blueprint CFSG.RankThree.PartTwo.Census.Spin

section Lift

variable {G K : Type*} [Group G] [Group K]

theorem exists_lift_elementary [Finite G] (π : G →* K) (hπ : Function.Surjective π)
    {E : Subgroup K} {p k : ℕ} (hE : IsMulCommutative E) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ k) (hcop : Nat.Coprime (Nat.card π.ker) (p ^ k)) :
    ∃ F : Subgroup G, IsMulCommutative F ∧ (∀ x ∈ F, x ^ p = 1) ∧ Nat.card F = p ^ k := by
  classical
  set H : Subgroup G := E.comap π with hH
  let ρ : H →* K := π.comp H.subtype
  have hker_le : π.ker ≤ H := fun x hx => by
    rw [hH, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact E.one_mem
  have hN : ρ.ker = π.ker.subgroupOf H := by
    ext x
    simp [ρ, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hrange : ρ.range = E := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨g, rfl⟩ := hπ y
      exact ⟨⟨g, hy⟩, rfl⟩
  have hNcard : Nat.card ρ.ker = Nat.card π.ker := by
    rw [hN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  have hidx : ρ.ker.index = p ^ k := by
    rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hrange]
    exact hcard
  obtain ⟨F', hF'⟩ := Subgroup.exists_right_complement'_of_coprime (N := ρ.ker)
    (by rw [hNcard, hidx]; exact hcop)
  have hdis : Disjoint ρ.ker F' := hF'.disjoint
  have hFcard : Nat.card F' = p ^ k := by
    rw [← hidx]
    exact hF'.symm.index_eq_card.symm
  have hmem : ∀ x : H, ρ x ∈ E := fun x => x.2
  have hcomm : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x := by
    intro x hx y hy
    have h1 : ρ (x * y * x⁻¹ * y⁻¹) = 1 := by
      have h2 : ρ x * ρ y = ρ y * ρ x :=
        congrArg Subtype.val (hE.is_comm.comm ⟨ρ x, hmem x⟩ ⟨ρ y, hmem y⟩)
      simp only [map_mul, map_inv]
      rw [h2]
      group
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ ρ.ker ⊓ F' :=
      ⟨MonoidHom.mem_ker.2 h1,
        F'.mul_mem (F'.mul_mem (F'.mul_mem hx hy) (F'.inv_mem hx)) (F'.inv_mem hy)⟩
    have h4 : x * y * x⁻¹ * y⁻¹ = 1 := Subgroup.disjoint_def.1 hdis h3.1 h3.2
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h4, one_mul]
  have hexp' : ∀ x ∈ F', x ^ p = 1 := by
    intro x hx
    have h1 : ρ (x ^ p) = 1 := by
      rw [map_pow]
      exact hexp _ (hmem x)
    exact Subgroup.disjoint_def.1 hdis (MonoidHom.mem_ker.2 h1) (F'.pow_mem hx p)
  refine ⟨F'.map H.subtype, ⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb]
    exact congrArg Subtype.val (hcomm a' ha' b' hb')
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    simp [hexp' x hx]
  · exact (Nat.card_congr
      (F'.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm.trans hFcard

end Lift

section Co2


noncomputable def kvEquivCo2' : Kstab (phi0 (coordOf rStar)) ≃* NativeSporadic.Co2 :=
  (MulEquiv.subgroupCongr (congrArg Kstab phi0_coordOf_rStar)).trans
    Existence.Co2Bridge.kvEquivCo2

noncomputable def jbarToCo2 : Jbar →* NativeSporadic.Co2 where
  toFun j := kvEquivCo2' (jbarToKv j)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]

theorem jbarToCo2_surjective : Function.Surjective jbarToCo2 := fun y => by
  obtain ⟨k, hk⟩ := kvEquivCo2'.surjective y
  obtain ⟨j, hj⟩ := jbarToKv_surjective k
  exact ⟨j, by change kvEquivCo2' (jbarToKv j) = y; rw [hj, hk]⟩

theorem ker_jbarToCo2 : jbarToCo2.ker = Ebar.subgroupOf Jbar := by
  rw [← ker_jbarToKv]
  ext j
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change kvEquivCo2' (jbarToKv j) = 1 ↔ jbarToKv j = 1
  exact map_eq_one_iff _ kvEquivCo2'.injective

end Co2

theorem hasWitness_Cbar :
    HasWitness Cbar 3 4 := by
  obtain ⟨E, hEab, hEcard⟩ := CFSG.SectionRank.Co2_elementary_three_rank_four
  have hEJ : Nat.card (Ebar.subgroupOf Jbar) = 2 ^ 23 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).toEquiv).trans
      Ebar_extraspecial.2
  have hcop : Nat.Coprime (Nat.card jbarToCo2.ker) (3 ^ 4) := by
    rw [ker_jbarToCo2, hEJ]
    norm_num
  obtain ⟨F, hFc, hFe, hFcard⟩ :=
    exists_lift_elementary jbarToCo2 jbarToCo2_surjective hEab.1 hEab.2 hEcard hcop
  refine ⟨F.map Jbar.subtype, Subgroup.zpowers xbar, ⟨⟨fun a b => ?_⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb]
    exact congrArg Subtype.val
      (congrArg Subtype.val (hFc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    simp [hFe x hx]
  · exact (Nat.card_congr
      (F.equivMapOfInjective Jbar.subtype Jbar.subtype_injective).toEquiv).symm.trans hFcard
  · exact (Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨xbar, Subgroup.mem_zpowers xbar⟩,
      fun h => xbar_ne_one (congrArg Subtype.val h)⟩)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_xbar]; norm_num)
  · rintro g ⟨x, hx, rfl⟩
    have hJ : (x : Cbar) ∈ Subgroup.centralizer {xbar} := Jbar_le_centralizer_xbar x.2
    have hc : Commute xbar (x : Cbar) := (Subgroup.mem_centralizer_singleton_iff.1 hJ).symm
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left hc n).eq

theorem rankFourBabyMonster :
    Census3.RankFourBabyMonster :=
  Census3.excludedIndex_of_equiv (i := .sporadic .B) (T := Cbar)
    (fun _ => ⟨(TCB.nonempty_mulEquiv_B.some.symm).trans Existence.phiB.symm⟩)
    (p := 3) Nat.prime_three (by norm_num)
    (fun [Finite Cbar] => by
      have := le_localRank_of_hasWitness (Q := Cbar) Nat.prime_three hasWitness_Cbar
      exact this)

end CFSG.RankThree.PartOne.CTP
