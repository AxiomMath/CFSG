module

public import CFSG.RankThree.PartOne.HNB.ActorGroup
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree
open scoped Pointwise

namespace ActorGroup

variable {G : Type} [Group G] {A L : Subgroup G} (d : ActorGroup G A L)

abbrev Nt : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers d.t : Subgroup G) : Set G)

@[expose] def Q : Subgroup G := inSubgroup (pCore 2) d.Nt

theorem A0_le_Nt : d.A0 ≤ d.Nt := fun _ ha =>
  mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp
    (d.A0_le_centralizer_t ha))

theorem Y_le_Nt : d.Y ≤ d.Nt := fun _ ha =>
  mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp
    (d.Y_le_centralizer_t ha))

theorem Nt_le_normalizer_Q : d.Nt ≤ Subgroup.normalizer (d.Q : Set G) :=
  SteinbergBM.le_normalizer_inSubgroup_pCore 2 d.Nt

theorem A0_le_normalizer_Q : d.A0 ≤ Subgroup.normalizer (d.Q : Set G) :=
  d.A0_le_Nt.trans d.Nt_le_normalizer_Q

theorem B_le_normalizer_Q : d.B ≤ Subgroup.normalizer (d.Q : Set G) :=
  d.B_le_A0.trans d.A0_le_normalizer_Q

theorem Q_isPGroup : IsPGroup 2 d.Q :=
  (CFSG.pCore_isPGroup (p := 2) (G := d.Nt)).map d.Nt.subtype

theorem not_dvd_card_Q [Finite G] : ¬ 5 ∣ Nat.card d.Q := by
  have := coprime_five_card_of_isPGroup_two d.Q_isPGroup
  exact fun h => by
    have := Nat.Coprime.eq_one_of_dvd this h
    omega

theorem isPGroup_zpowers_t : IsPGroup 2 (Subgroup.zpowers d.t) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, d.N.ht2]; norm_num)

theorem zpowers_t_ne_bot : Subgroup.zpowers d.t ≠ ⊥ := by
  intro hbot
  have : d.t = 1 := by
    have := Subgroup.mem_zpowers d.t
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have h2 := d.N.ht2
  change orderOf d.t = 2 at h2
  rw [this, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem not_centralizes_Q (hCP : IsCharacteristicPType G 2) :
    ¬ ∀ s ∈ d.Q, s * d.c = d.c * s := by
  intro hcen
  have hc : d.c ∈ Subgroup.normalizer ((Subgroup.zpowers d.t : Subgroup G) : Set G) :=
    d.A0_le_Nt d.c_mem_A0
  have hcQ : d.c ∈ d.Q :=
    SteinbergBM.mem_inSubgroup_pCore_of_isCharacteristicPType hCP d.isPGroup_zpowers_t
      d.zpowers_t_ne_bot hc hcen
  exact false_of_mem_isPGroup_two d.Q_isPGroup hcQ d.hc5

theorem exists_b [Finite G] (hCP : IsCharacteristicPType G 2) :
    ∃ b ∈ d.B, b ∉ Subgroup.zpowers d.c ∧
      ⁅d.Q ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers d.c⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQc : d.Q ≤ Subgroup.centralizer ({d.c} : Set G) := by
    refine SteinbergBM.le_of_forall_inf_centralizer_le (p := 5) d.isElementaryAbelian_B
      (by rw [d.card_B]; norm_num) d.not_dvd_card_Q d.B_le_normalizer_Q ?_
    intro b hb hb1
    by_cases hbc : b ∈ Subgroup.zpowers d.c
    · have hcb : d.c ∈ Subgroup.zpowers b := mem_zpowers_of_mem_zpowers_prime d.hc5 hbc hb1
      intro u hu
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcb
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hub : u * b = b * u := Subgroup.mem_centralizer_singleton_iff.mp hu.2
      rw [← hn]
      exact (Commute.zpow_right (show Commute u b from hub) n).eq
    · intro u hu
      have := commutator_zpowers_eq_bot_iff.mp (hcon b hb hbc) u hu
      exact Subgroup.mem_centralizer_singleton_iff.mpr this
  exact d.not_centralizes_Q hCP fun s hs => Subgroup.mem_centralizer_singleton_iff.mp (hQc hs)

end ActorGroup

structure Actor (G : Type) [Group G] (A L : Subgroup G) extends ActorGroup G A L where
  b : G
  hbB : b ∈ toActorGroup.B
  hbc : b ∉ Subgroup.zpowers c
  hR : ⁅toActorGroup.Q ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≠ ⊥

namespace Actor

variable {G : Type} [Group G] {A L : Subgroup G} (a : Actor G A L)

@[expose] def U : Subgroup G := a.Q ⊓ Subgroup.centralizer ({a.b} : Set G)

@[expose] def R : Subgroup G := ⁅a.U, Subgroup.zpowers a.c⁆

theorem b_ne_one : a.b ≠ 1 := fun h => a.hbc (h ▸ Subgroup.one_mem _)

theorem b_mem_A0 : a.b ∈ a.A0 := a.B_le_A0 a.hbB

theorem commute_b_of_mem_A0 {g : G} (hg : g ∈ a.A0) : g * a.b = a.b * g :=
  congrArg Subtype.val (a.isElementaryAbelian_A0.is_comm.comm ⟨g, hg⟩ ⟨a.b, a.b_mem_A0⟩)

theorem commute_c_of_mem_A0 {g : G} (hg : g ∈ a.A0) : g * a.c = a.c * g :=
  congrArg Subtype.val (a.isElementaryAbelian_A0.is_comm.comm ⟨g, hg⟩ ⟨a.c, a.c_mem_A0⟩)

theorem commute_b_of_mem_K {g : G} (hg : g ∈ a.K) : g * a.b = a.b * g :=
  (Subgroup.mem_centralizer_iff.mp (a.K_le_centralizer_B hg) a.b a.hbB).symm

theorem commute_c_of_mem_K {g : G} (hg : g ∈ a.K) : g * a.c = a.c * g :=
  (Subgroup.mem_centralizer_iff.mp (a.K_le_centralizer_B hg) a.c a.c_mem_B).symm

theorem commute_b_of_mem_Y {g : G} (hg : g ∈ a.Y) : g * a.b = a.b * g :=
  a.commute_b_of_mem_K (a.N.hYK hg)

theorem commute_c_of_mem_Y {g : G} (hg : g ∈ a.Y) : g * a.c = a.c * g :=
  a.commute_c_of_mem_K (a.N.hYK hg)

theorem U_isPGroup : IsPGroup 2 a.U := a.Q_isPGroup.to_le inf_le_left

theorem le_normalizer_U {H : Subgroup G} (hHN : H ≤ a.Nt)
    (hHb : ∀ h ∈ H, h * a.b = a.b * h) : H ≤ Subgroup.normalizer (a.U : Set G) :=
  le_normalizer_inf_of_le_normalizer (hHN.trans a.Nt_le_normalizer_Q) fun h hh =>
    mem_normalizer_centralizer_of_commute (hHb h hh)

theorem le_normalizer_R {H : Subgroup G} (hHN : H ≤ a.Nt) (hHb : ∀ h ∈ H, h * a.b = a.b * h)
    (hHc : ∀ h ∈ H, h * a.c = a.c * h) : H ≤ Subgroup.normalizer (a.R : Set G) :=
  GorensteinWalter.le_normalizer_commutator_of_le_normalizer H a.U (Subgroup.zpowers a.c)
    (a.le_normalizer_U hHN hHb) fun h hh => mem_normalizer_zpowers_of_commute (hHc h hh)

theorem A0_le_normalizer_U : a.A0 ≤ Subgroup.normalizer (a.U : Set G) :=
  a.le_normalizer_U a.A0_le_Nt fun _ hg => a.commute_b_of_mem_A0 hg

theorem A0_le_normalizer_R : a.A0 ≤ Subgroup.normalizer (a.R : Set G) :=
  a.le_normalizer_R a.A0_le_Nt (fun _ hg => a.commute_b_of_mem_A0 hg)
    fun _ hg => a.commute_c_of_mem_A0 hg

theorem Y_le_normalizer_R : a.Y ≤ Subgroup.normalizer (a.R : Set G) :=
  a.le_normalizer_R a.Y_le_Nt (fun _ hg => a.commute_b_of_mem_Y hg)
    fun _ hg => a.commute_c_of_mem_Y hg

theorem c_mem_normalizer_U : a.c ∈ Subgroup.normalizer (a.U : Set G) :=
  a.A0_le_normalizer_U a.c_mem_A0

theorem R_le_U : a.R ≤ a.U :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr a.c_mem_normalizer_U)

theorem R_le_centralizer_b : a.R ≤ Subgroup.centralizer ({a.b} : Set G) :=
  a.R_le_U.trans inf_le_right

theorem R_isPGroup : IsPGroup 2 a.R := a.U_isPGroup.to_le a.R_le_U

theorem R_ne_bot : a.R ≠ ⊥ := a.hR

theorem R_commutator_self [Finite G] : ⁅a.R, Subgroup.zpowers a.c⁆ = a.R :=
  commutator_zpowers_self a.hc5 a.U_isPGroup a.c_mem_normalizer_U

theorem c_mem_normalizer_R : a.c ∈ Subgroup.normalizer (a.R : Set G) :=
  a.A0_le_normalizer_R a.c_mem_A0

end Actor

theorem exists_actor {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    (hCP : IsCharacteristicPType G 2) (d : ActorGroup G A L) : Nonempty (Actor G A L) := by
  obtain ⟨b, hbB, hbc, hR⟩ := d.exists_b hCP
  exact ⟨{ d with b := b, hbB := hbB, hbc := hbc, hR := hR }⟩

end CFSG.RankThree.PartOne.HNB
