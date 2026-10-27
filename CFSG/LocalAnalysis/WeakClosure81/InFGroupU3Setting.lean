module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddAct
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase

structure Setting {Q : Type} [Group Q] (C : Subgroup Q) (n : ℕ) : Prop where
  normal : C.Normal
  quasisimple : CFSG.Open.IsQuasisimple ↥C
  isU3 : IsU3 (↥C ⧸ center ↥C) n
  centralizer_le : centralizer (C : Set Q) ≤ C
  odd_center : Odd (Nat.card (center ↥C))
  two_quot : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ C

variable {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q} {n : ℕ}

theorem Setting.pCoreOf_top_eq_bot (h : Setting C n) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : C.Normal := h.normal
  set P : Subgroup Q := CFSG.Open.pCoreOf 2 (⊤ : Subgroup Q) with hPdef
  have hP2 : IsPGroup 2 ↥P := by
    rw [hPdef]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hPnorm : P.Normal := by
    rw [hPdef, CFSG.openPCoreOf_eq_map_pCore]
    exact (CFSG.pCore_normal (p := 2) (G := ↥(⊤ : Subgroup Q))).map (⊤ : Subgroup Q).subtype
      fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  haveI : P.Normal := hPnorm
  have hPCnorm : (P ⊓ C).Normal := Subgroup.normal_inf_normal P C
  have hcent : ((P ⊓ C).subgroupOf C) ≤ Subgroup.center ↥C := by
    refine uc22p22a_qs_solvable_normal_le_center h.quasisimple (hPCnorm.subgroupOf C) ?_
    have hD2 : IsPGroup 2 ↥((P ⊓ C).subgroupOf C) :=
      (hP2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have := hD2.isNilpotent
    infer_instance
  have hPCbot : P ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
    have hz : (⟨x, hxC⟩ : ↥C) ∈ Subgroup.center ↥C :=
      hcent (Subgroup.mem_subgroupOf.2 hx)
    have hdiv : orderOf x ∣ Nat.card (Subgroup.center ↥C) := by
      rw [Subgroup.orderOf_coe (⟨x, hxC⟩ : ↥C)]
      exact Subgroup.orderOf_dvd_natCard (Subgroup.center ↥C) hz
    have hodd : Odd (orderOf x) := Odd.of_dvd_nat h.odd_center hdiv
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP2) ⟨x, hxP⟩
    have hk' : orderOf x = 2 ^ k := by
      rw [Subgroup.orderOf_coe (⟨x, hxP⟩ : ↥P)]
      exact hk
    have hodd' : Odd (2 ^ k) := hk' ▸ hodd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ 2 ^ k := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        exact ⟨2 ^ m, by rw [pow_succ]; ring⟩
      exact hodd'.not_two_dvd_nat h2
    have h1 : orderOf x = 1 := by simp [hk', hk0]
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h1)
  have hcomm : ⁅P, C⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_le_inf P C).trans hPCbot.le)
  have hPleC : P ≤ C :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans h.centralizer_le
  rw [← inf_eq_left.2 hPleC]
  exact hPCbot

theorem Setting.two_le (h : Setting C n) : 2 ≤ n := by
  have hadm := CFSG.Blueprint.LieModel.admissible h.isU3
  have h1 : 1 ≤ n := hadm.2.1
  by_contra hlt
  have hn1 : n = 1 := by omega
  subst hn1
  exact hadm.2.2.2 rfl

@[expose] def Setting.act (h : Setting C n) : Q →* MulAut (↥C ⧸ center ↥C) :=
  haveI := h.normal
  UCK.Odd.actHom C

theorem Setting.act_apply_mk (h : Setting C n) (g : Q) (y : ↥C) :
    h.act g (QuotientGroup.mk y : ↥C ⧸ center ↥C) =
      QuotientGroup.mk ⟨g * y * g⁻¹, h.normal.conj_mem _ y.2 g⟩ :=
  rfl

theorem Setting.act_coe (h : Setting C n) (c : ↥C) :
    h.act (c : Q) = MulAut.conj (QuotientGroup.mk c : ↥C ⧸ center ↥C) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [Setting.act_apply_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1

theorem Setting.mem_center_of_act_eq_one (h : Setting C n) {g : Q} (hg : h.act g = 1) :
    g ∈ (center ↥C).map C.subtype := by
  haveI : C.Normal := h.normal
  have hg' : UCK.Odd.actHom C g = 1 := hg
  have hcomm : ∀ y ∈ C, g * y = y * g := by
    refine UCK.Odd.centralizes_of_forall_comm_mem C h.quasisimple.1 ?_
    intro y hy
    refine (UCK.Odd.actHom_mk_eq_iff C g hy).1 ?_
    rw [hg']
    rfl
  have hmem : g ∈ Subgroup.centralizer (C : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => (hcomm y hy).symm
  have hgC : g ∈ C := h.centralizer_le hmem
  refine Subgroup.mem_map.2 ⟨⟨g, hgC⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro z
  exact Subtype.ext (hcomm (z : Q) z.2).symm

theorem Setting.act_not_mem_range (h : Setting C n) {s : Q} (hsC : s ∉ C) :
    h.act s ∉ (MulAut.conj : (↥C ⧸ center ↥C) →* MulAut (↥C ⧸ center ↥C)).range := by
  rintro ⟨x, hx⟩
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective x
  rw [← hc] at hx
  have h1 : h.act (s * (c : Q)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hx, Setting.act_coe, mul_inv_cancel]
  have h2 : s * (c : Q)⁻¹ ∈ C :=
    Subgroup.map_subtype_le (center ↥C) (h.mem_center_of_act_eq_one h1)
  refine hsC ?_
  have hs : s = (s * (c : Q)⁻¹) * c := by group
  rw [hs]
  exact C.mul_mem h2 c.2

theorem Setting.orderOf_act (h : Setting C n) {s : Q} (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    orderOf (h.act s) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, hs2, map_one]
  · intro h1
    exact h.act_not_mem_range hsC (h1 ▸ ⟨1, map_one MulAut.conj⟩)

theorem Setting.inf_center_map_eq_bot (h : Setting C n) {P : Subgroup Q} (hP : IsPGroup 2 P) :
    P ⊓ (center ↥C).map C.subtype = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ((center ↥C).map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact h.odd_center
  rcases (hP.to_le inf_le_left : IsPGroup 2 ↥(P ⊓ (center ↥C).map C.subtype)).card_eq_or_dvd
    with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (h2.trans (Subgroup.card_dvd_of_le inf_le_right)) hodd.not_two_dvd_nat

end CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
