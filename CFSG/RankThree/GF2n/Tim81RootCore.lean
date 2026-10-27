module

public import CFSG.RankThree.GF2n.Tim81Hyp3
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.RankThree.GF2n.Tim78Frattini
public import CFSG.RankThree.GF2n.Tim78S4Basic

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

structure RootCore (M B R : Subgroup G) : Prop where
  maxLocal : IsMaximalTwoLocal M
  B_le_M : B ≤ M
  M_le_normalizer_B : M ≤ Subgroup.normalizer (B : Set G)
  elemAb : Assembly.IsElemAbelian 2 B
  ti : IsTI B
  B_ne_bot : B ≠ ⊥
  isPGroup_R : IsPGroup 2 R
  M_le_normalizer_R : M ≤ Subgroup.normalizer (R : Set G)
  B_le_R : B ≤ R
  center_R : ∀ {b x : G}, b ∈ B → x ∈ R → b * x = x * b
  sq_mem : ∀ {a : G}, a ∈ R → a ^ 2 ∈ B

namespace RootCore

variable [Finite G] {M B R : Subgroup G} (H : RootCore M B R)
include H

omit [Finite G] in
theorem sq_eq_one : ∀ x ∈ B, x ^ 2 = 1 := H.elemAb.2

omit [Finite G] in
theorem isPGroup_B : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using H.sq_eq_one x x.2)⟩

omit [Finite G] in
theorem normalizer_B : Subgroup.normalizer (B : Set G) = M := by
  have hloc : IsPLocal 2 (Subgroup.normalizer (B : Set G)) :=
    ⟨B, H.B_ne_bot, H.isPGroup_B, rfl⟩
  by_contra hne
  exact H.maxLocal.2 _ (lt_of_le_of_ne H.M_le_normalizer_B (Ne.symm hne)) hloc

omit [Finite G] in
theorem normalizer_conj_eq (g : G) :
    Subgroup.normalizer (conjSubgroup g B : Set G) = conjSubgroup g M := by
  rw [normalizer_conjSubgroup, H.normalizer_B]

theorem centralizer_le_conj {g x : G} (hx : x ∈ conjSubgroup g B) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ conjSubgroup g M := by
  intro c hc
  rw [← H.normalizer_conj_eq, ← conjSubgroup_eq_self_iff]
  refine conjSubgroup_eq_of_isTI (isTI_conjSubgroup H.ti g) fun hbot => ?_
  have hxc : x ∈ conjSubgroup g B ⊓ conjSubgroup c (conjSubgroup g B) := by
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_conjSubgroup]
    have h1 : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [show c⁻¹ * x * c = x by rw [mul_assoc, ← h1]; group]
    exact hx
  rw [hbot, Subgroup.mem_bot] at hxc
  exact hx1 hxc

theorem normalizer_eq_and_centralizer_le :
    Subgroup.normalizer (B : Set G) = M ∧
      ∀ x ∈ B, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M := by
  refine ⟨H.normalizer_B, fun x hx hx1 => ?_⟩
  have := H.centralizer_le_conj (g := 1) (by rwa [conjSubgroup_one]) hx1
  rwa [conjSubgroup_one] at this

theorem commute_of_conj_le_M {g : G} (hg : conjSubgroup g B ≤ M) :
    ∀ a ∈ B, ∀ b ∈ conjSubgroup g B, a * b = b * a := fun _ ha _ hb =>
  comm_of_isElemAbelian (Tim77.tim77_2_3 H.elemAb H.ti (by rw [H.normalizer_B]; exact hg))
    (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem conj_le_M_symm {g : G} (hg : conjSubgroup g B ≤ M) : conjSubgroup g⁻¹ B ≤ M := by
  intro x hx
  rw [mem_conjSubgroup, inv_inv] at hx
  have hb : g * x * g⁻¹ ∈ Subgroup.normalizer (conjSubgroup g B : Set G) :=
    le_normalizer_of_comm (fun b hb a ha => H.commute_of_conj_le_M hg b hb a ha) hx
  rw [H.normalizer_conj_eq, mem_conjSubgroup] at hb
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hb

theorem conj_le_M_of_le_conj {g : G} (hg : B ≤ conjSubgroup g M) : conjSubgroup g B ≤ M := by
  have h1 : conjSubgroup g⁻¹ B ≤ M := by
    intro z hz
    rw [mem_conjSubgroup, inv_inv] at hz
    have := hg hz
    rwa [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
  have := H.conj_le_M_symm h1
  rwa [inv_inv] at this

theorem conj_inf_R_eq_bot_of_not_le_M {g : G} (hgM : ¬ conjSubgroup g B ≤ M) :
    conjSubgroup g B ⊓ R = ⊥ := by
  by_contra h
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  obtain ⟨hxB, hxR⟩ := Subgroup.mem_inf.mp hx
  apply hgM
  apply H.conj_le_M_of_le_conj
  intro b hb
  have hC : b ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (H.center_R hb hxR)
  exact H.centralizer_le_conj hxB hx1' hC

omit [Finite G] in
theorem M_le_normalizer_Q : M ≤ Subgroup.normalizer (R : Set G) := H.M_le_normalizer_R
omit [Finite G] in
theorem B_le_Q : B ≤ R := H.B_le_R
omit [Finite G] in
theorem isPGroup_Q : IsPGroup 2 R := H.isPGroup_R
omit [Finite G] in
theorem center_Q {b x : G} (hb : b ∈ B) (hx : x ∈ R) : b * x = x * b := H.center_R hb hx

end RootCore

end CFSG.RankThree.GF2n.Tim78

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78

variable {G : Type} [Group G]

namespace Hyp3

variable [Finite G] {M V Q P : Subgroup G} (H : Hyp3 M V Q P)
include H

theorem frattini_P_le_and_V_eq :
    inSubgroup frattini P ≤ V ∧ V = P ⊓ Subgroup.centralizer (P : Set G) :=
  tim78_2_9_beta_of_elementary H.fitting H.maxAb H.elemAb.2 (by rw [H.hP, H.hQ])

theorem sq_mem {a : G} (ha : a ∈ P) : a ^ 2 ∈ V := by
  have := sq_mem_inSubgroup_frattini H.isPGroup_P ha
  exact H.frattini_P_le_and_V_eq.1 this

theorem M_le_normalizer_P : M ≤ Subgroup.normalizer (P : Set G) := fun m hm => by
  rw [H.hP]
  exact mem_normalizer_inf (H.M_le_normalizer_Q hm)
    (mem_normalizer_centralizer (H.M_le_normalizer_V hm))

theorem toRootCore : RootCore M V P where
  maxLocal := H.maxLocal
  B_le_M := H.V_le_M
  M_le_normalizer_B := H.M_le_normalizer_V
  elemAb := H.elemAb
  ti := H.ti
  B_ne_bot := H.V_ne_bot
  isPGroup_R := H.isPGroup_P
  M_le_normalizer_R := H.M_le_normalizer_P
  B_le_R := H.V_le_P
  center_R := fun hb hx => H.center_P hb hx
  sq_mem := fun ha => H.sq_mem ha

end Hyp3

end CFSG.RankThree.GF2n.Tim81
