module

import CFSG.RankThree.PartOne.S11c.PSU3InPSL2
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement
public import CFSG.RankThree.PartOne.HNB.KComponent
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

theorem exists_elementaryAbelian_order_25 {K : Type} [Group K] [Finite K]
    (hK : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 5 1) :
    ∃ E : Subgroup K, IsElementaryAbelian 5 E ∧ Nat.card E = 5 ^ 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, y, hx5, hz5, hcx, hcy, hz1⟩ :=
    HNRed.exists_heisenberg_of_cover hK (MonoidHom.id K) Function.surjective_id
      (fun g hg => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hg
        rw [hg]
        exact one_mem _)
  set z : K := ⁅y, x⁆ with hz
  have hxz : x * z = z * x := hcx.eq.symm
  have hx1 : x ≠ 1 := by
    intro h1
    apply hz1
    rw [hz, h1]
    group
  have hx5' : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hz5' : orderOf z = 5 := orderOf_eq_prime hz5 hz1
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    by_contra hu1
    obtain ⟨hux, huz⟩ := Subgroup.mem_inf.mp hu
    have hxu : x ∈ Subgroup.zpowers u := mem_zpowers_of_mem_zpowers_prime hx5' hux hu1
    have hxz' : x ∈ Subgroup.zpowers z := (Subgroup.zpowers_le.mpr huz) hxu
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxz'
    have hzy : z * y = y * z := hcy.eq
    have hxy : x * y = y * x := by
      rw [← hn]
      exact (Commute.zpow_left (show Commute z y from hzy) n).eq
    apply hz1
    rw [hz, commutatorElement_def]
    calc y * x * y⁻¹ * x⁻¹ = (y * x) * y⁻¹ * x⁻¹ := by group
      _ = (x * y) * y⁻¹ * x⁻¹ := by rw [hxy]
      _ = 1 := by group
  have hcomm : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers z : Set K) :=
    zpowers_le_centralizer_zpowers hxz
  refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers z, ?_, ?_⟩
  · exact SteinbergBM.isElementaryAbelian_sup_of_le_centralizer
      (IsElementaryAbelian.zpowers_of_pow_eq_one hx5) (IsElementaryAbelian.zpowers_of_pow_eq_one hz5)
      hcomm
  · rw [SteinbergBM.card_sup_of_le_centralizer_of_inf_eq_bot hcomm hinf, Nat.card_zpowers,
      Nat.card_zpowers, hx5', hz5']
    norm_num

namespace Actor

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} (a : Actor G A L)

theorem R_commutator_B : ⁅a.R, a.B⁆ = a.R := by
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (a.B_le_A0.trans a.A0_le_normalizer_R)
  · calc a.R = ⁅a.R, Subgroup.zpowers a.c⁆ := a.R_commutator_self.symm
      _ ≤ ⁅a.R, a.B⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr a.c_mem_B)

theorem commutator_K_R_not_le_theta (h : SteinbergBM.SectionTenSetup G 5 A) :
    ¬ ⁅a.K, a.R⁆ ≤ inSubgroup (aschbacherSolvableCore 5) a.H := by
  intro hKR
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨E0, hE0, hE0card⟩ := exists_elementaryAbelian_order_25 a.N.hKmodel
  set E : Subgroup G := E0.map a.K.subtype with hE
  have hEK : E ≤ a.K := Subgroup.map_subtype_le E0
  have hEe : IsElementaryAbelian 5 E := CFSG.IsElementaryAbelian.map_subtype
  have hEcard : Nat.card E = 5 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective a.K.subtype_injective, hE0card]
  have hsupp := SteinbergBM.vanishing_centralizing_two_commutator_full_perfect_supplement hp
    (sectionTenSetup_three_lt h) (sectionTenSetup_vanishing h) a.isElementaryAbelian_A0 a.card_A0
    a.B_le_A0 (by rw [a.card_B]; norm_num) a.hbB a.b_ne_one a.K_le_centralizer_B a.N.hKsimple
    a.N.hKnonab a.R_le_centralizer_b a.R_isPGroup (a.B_le_A0.trans a.A0_le_normalizer_R)
    a.R_commutator_B hKR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ε, -, -, -, hEx⟩ := hsupp
  obtain ⟨P, -, -, -, -, -, -, -, hBPn, hBPe, hBPcard⟩ := hEx E hEK hEe 2 hEcard
  have hW : IsMulCommutative ↥(a.B ⊔ P) := hBPe.toIsMulCommutative
  have hexp : ∀ w ∈ (a.B ⊔ P : Subgroup G), w ^ 5 = 1 := fun w hw =>
    elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := a.B ⊔ P) w hw
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 5 G :=
    Theta.le_localRank_of_le_normalizer (by norm_num) a.R_ne_bot a.R_isPGroup hW hexp (k := 4)
      (by rw [hBPcard]) hBPn
  have h5G : 5 ∣ Nat.card G := by
    have := Subgroup.card_subgroup_dvd_card a.A0
    rw [a.card_A0] at this
    exact (dvd_pow_self 5 (by norm_num)).trans this
  have h3 := h4.trans (Theta.localRank_le_twoLocalOddRank hp (by norm_num) h5G)
  rw [h.2.2.2.2.1] at h3
  omega

end Actor

end CFSG.RankThree.PartOne.HNB
