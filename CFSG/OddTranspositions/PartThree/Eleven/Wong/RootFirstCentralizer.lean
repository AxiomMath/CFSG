module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootSpace
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDiagA5
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.SylowLift
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutOrder8Hom
public import CFSG.GH74.GLS.SP.GenOrder
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import Mathlib.GroupTheory.Commutator.Basic
import CFSG.Walter.ReeOrder.JT.PSL2
public import CFSG.GH74.GLS.Bg.TwoGroups.Statements
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.Walter.ReeOrder.JT.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup CFSG.ABGLocalTools CFSG.OddStandard.SmallF3.HarrisU33.Outside
open CFSG.Semidihedral.Principal.CoprimeFixedPoint
open scoped Pointwise

variable {G : Type} [Group G] (D : RootData G)

private theorem thetaM_centralizer_iff (x : SL5) :
    (∀ a : ZMod 5, x * thetaM a = thetaM a * x) ↔
      ∃ c : ZMod 5, x = thetaM c ∨ x = -thetaM c := by
  revert x
  decide +kernel

private theorem thetaM_normalizer_iff (x : SL5) :
    (∀ a : ZMod 5, ∃ b : ZMod 5, x⁻¹ * thetaM a * x = thetaM b) ↔
      ∃ u : ZMod 5, ∃ k : Fin 4, x = thetaM u * hM ^ k.val := by
  revert x
  decide +kernel

private theorem hM_conj_thetaM (a : ZMod 5) : hM * thetaM a * hM⁻¹ = thetaM (-a) := by
  revert a
  decide +kernel

private theorem conj_q1_by_prod (x y : SL5) (a : ZMod 5) :
    (D.i1 x * D.i2 y)⁻¹ * D.q1 (.ofAdd a) * (D.i1 x * D.i2 y) =
      D.i1 (x⁻¹ * thetaM a * x) := by
  rw [D.q1_ofAdd]
  have h1 : (D.i1 x)⁻¹ * D.i1 (thetaM a) * D.i1 x = D.i1 (x⁻¹ * thetaM a * x) := by
    simp [map_mul]
  calc
    (D.i1 x * D.i2 y)⁻¹ * D.i1 (thetaM a) * (D.i1 x * D.i2 y)
        = (D.i2 y)⁻¹ * ((D.i1 x)⁻¹ * D.i1 (thetaM a) * D.i1 x) * D.i2 y := by group
    _ = (D.i2 y)⁻¹ * D.i1 (x⁻¹ * thetaM a * x) * D.i2 y := by rw [h1]
    _ = D.i1 (x⁻¹ * thetaM a * x) := by
      rw [mul_assoc, (D.commute _ y).eq]
      group

private theorem conj_q1_by_prod_u (x y : SL5) (a : ZMod 5) :
    (D.i1 x * D.i2 y * D.u)⁻¹ * D.q1 (.ofAdd a) * (D.i1 x * D.i2 y * D.u) =
      D.i2 (x⁻¹ * thetaM a * x) := by
  rw [D.q1_ofAdd]
  have h1 := D.conj_q1_by_prod x y a
  rw [D.q1_ofAdd] at h1
  calc
    (D.i1 x * D.i2 y * D.u)⁻¹ * D.i1 (thetaM a) * (D.i1 x * D.i2 y * D.u)
        = D.u⁻¹ * ((D.i1 x * D.i2 y)⁻¹ * D.i1 (thetaM a) * (D.i1 x * D.i2 y)) * D.u := by
          group
    _ = D.u⁻¹ * D.i1 (x⁻¹ * thetaM a * x) * D.u := by rw [h1]
    _ = D.i2 (x⁻¹ * thetaM a * x) := by
      simpa [D.u_inv] using D.swap (x⁻¹ * thetaM a * x)

private theorem t_mem_centralizer_P1 : D.t ∈ centralizer (D.P1 : Set G) := by
  refine mem_centralizer_iff.mpr fun x hx => ?_
  obtain ⟨a, rfl⟩ := hx
  exact (D.t_commute_i1 (thetaHom a)).eq.symm

private abbrev firstCentralizer (D : RootData G) : Subgroup G := centralizer (D.P1 : Set G)

private abbrev firstOddCore (D : RootData G) : Subgroup (firstCentralizer D) :=
  CFSG.oddCore (firstCentralizer D)

private theorem P1_le_centralizer_P1 : D.P1 ≤ centralizer (D.P1 : Set G) := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  refine mem_centralizer_iff.mpr fun y hy => ?_
  obtain ⟨b, rfl⟩ := hy
  calc D.q1 b * D.q1 a = D.q1 (b * a) := (map_mul _ _ _).symm
    _ = D.q1 (a * b) := by rw [mul_comm]
    _ = D.q1 a * D.q1 b := map_mul _ _ _

private theorem i2_range_le_centralizer_P1 : D.i2.range ≤ centralizer (D.P1 : Set G) := by
  rintro _ ⟨y, rfl⟩
  refine mem_centralizer_iff.mpr fun q hq => ?_
  obtain ⟨a, rfl⟩ := hq
  change D.i1 (thetaHom a) * D.i2 y = D.i2 y * D.i1 (thetaHom a)
  exact (D.commute (thetaHom a) y).eq

private theorem P1_le_centralizer_t : D.P1 ≤ centralizer ({D.t} : Set G) := by
  rintro _ ⟨a, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (D.t_commute_i1 (thetaHom a)).eq.symm

private theorem i2_range_le_centralizer_t : D.i2.range ≤ centralizer ({D.t} : Set G) := by
  rintro _ ⟨y, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (D.t_commute_i2 y).eq.symm

private theorem P1_inf_i2_range : D.P1 ⊓ D.i2.range = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  obtain ⟨a, rfl⟩ := hx1
  have hmem : D.q1 a ∈ zpowers D.t := by
    rw [← D.range_inf]
    exact mem_inf.mpr ⟨⟨thetaHom a, rfl⟩, hx2⟩
  rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_t).mp hmem with h | h
  · exact h
  · have hdvd := D.P1.orderOf_dvd_natCard (D.q1.mem_range.mpr ⟨a, rfl⟩)
    rw [D.card_P1] at hdvd
    rw [h, D.orderOf_t] at hdvd
    exact absurd hdvd (by norm_num)

private theorem centralizer_P1_inf_centralizer_t [Finite G] :
    centralizer (D.P1 : Set G) ⊓ centralizer ({D.t} : Set G) = D.P1 ⊔ D.i2.range := by
  refine le_antisymm ?_ (sup_le
    (le_inf D.P1_le_centralizer_P1 D.P1_le_centralizer_t)
    (le_inf D.i2_range_le_centralizer_P1 D.i2_range_le_centralizer_t))
  intro g hg
  obtain ⟨hgP1, hgt⟩ := mem_inf.mp hg
  rcases D.mem_centralizer_t_iff.mp hgt with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · have hx : ∀ a : ZMod 5, x * thetaM a = thetaM a * x := by
      intro a
      have hcomm := (mem_centralizer_iff.mp hgP1) (D.q1 (.ofAdd a))
        (D.q1.mem_range.mpr ⟨.ofAdd a, rfl⟩)
      have hconj : (D.i1 x * D.i2 y)⁻¹ * D.q1 (.ofAdd a) * (D.i1 x * D.i2 y) =
          D.q1 (.ofAdd a) := by
        calc (D.i1 x * D.i2 y)⁻¹ * D.q1 (.ofAdd a) * (D.i1 x * D.i2 y)
            = (D.i1 x * D.i2 y)⁻¹ * (D.q1 (.ofAdd a) * (D.i1 x * D.i2 y)) := by group
          _ = (D.i1 x * D.i2 y)⁻¹ * ((D.i1 x * D.i2 y) * D.q1 (.ofAdd a)) := by rw [hcomm]
          _ = D.q1 (.ofAdd a) := by group
      rw [D.conj_q1_by_prod] at hconj
      have h : x⁻¹ * thetaM a * x = thetaM a := by
        simpa [thetaHom] using D.inj1 hconj
      calc x * thetaM a = x * (x⁻¹ * thetaM a * x) := by rw [h]
        _ = thetaM a * x := by group
    rcases (thetaM_centralizer_iff x).mp hx with ⟨c, rfl | rfl⟩
    · exact mul_mem_sup (D.q1.mem_range.mpr ⟨.ofAdd c, rfl⟩) (D.i2.mem_range.mpr ⟨y, rfl⟩)
    · have hxi : D.i1 (-thetaM c) = D.t * D.i1 (thetaM c) := D.i1_neg (thetaM c)
      have hmem : D.q1 (.ofAdd c) * D.i2 (-y) ∈ D.P1 ⊔ D.i2.range :=
        Subgroup.mul_mem_sup (D.q1.mem_range.mpr ⟨.ofAdd c, rfl⟩)
          (D.i2.mem_range.mpr ⟨-y, rfl⟩)
      convert hmem using 1
      rw [hxi, D.t_eq_i2]
      calc D.i2 (-1) * D.i1 (thetaM c) * D.i2 y
          = D.i1 (thetaM c) * D.i2 (-1) * D.i2 y := by
            rw [show D.i2 (-1) * D.i1 (thetaM c) = D.i1 (thetaM c) * D.i2 (-1) from
              (D.commute (thetaM c) (-1)).eq.symm]
        _ = D.i1 (thetaM c) * (D.i2 (-1) * D.i2 y) := by group
        _ = D.i1 (thetaM c) * D.i2 (-1 * y) := by rw [← map_mul]
        _ = D.i1 (thetaM c) * D.i2 (-y) := by rw [neg_one_mul]
  · have hcomm := (mem_centralizer_iff.mp hgP1) (D.q1 (.ofAdd 1))
      (D.q1.mem_range.mpr ⟨.ofAdd 1, rfl⟩)
    have hconj : (D.i1 x * D.i2 y * D.u)⁻¹ * D.q1 (.ofAdd 1) * (D.i1 x * D.i2 y * D.u) =
        D.q1 (.ofAdd 1) := by
      calc (D.i1 x * D.i2 y * D.u)⁻¹ * D.q1 (.ofAdd 1) * (D.i1 x * D.i2 y * D.u)
          = (D.i1 x * D.i2 y * D.u)⁻¹ * (D.q1 (.ofAdd 1) * (D.i1 x * D.i2 y * D.u)) := by group
        _ = (D.i1 x * D.i2 y * D.u)⁻¹ * ((D.i1 x * D.i2 y * D.u) * D.q1 (.ofAdd 1)) := by rw [hcomm]
        _ = D.q1 (.ofAdd 1) := by group
    rw [D.conj_q1_by_prod_u] at hconj
    have h := i1_eq_i2_iff D.inj1 D.inj2 D.orderOf_t D.range_inf |>.mp hconj.symm
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)

private theorem h1_mem_normalizer_P1 [Finite G] : D.h1 ∈ normalizer (D.P1 : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : D.P1.map (MulAut.conj D.h1) ≤ D.P1 := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, rfl⟩ := hg
    change D.h1 * D.q1 a * D.h1⁻¹ ∈ D.P1
    change D.i1 hM * D.q1 a * (D.i1 hM)⁻¹ ∈ D.P1
    rw [show D.q1 a = D.i1 (thetaM a.toAdd) from rfl]
    rw [← map_inv, ← map_mul, ← map_mul, hM_conj_thetaM]
    exact D.q1.mem_range.mpr ⟨.ofAdd (-a.toAdd), rfl⟩
  haveI : Finite ↥D.P1 := Finite.of_injective (fun x : ↥D.P1 => (x : G)) Subtype.val_injective
  exact eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj D.h1).injective])

private theorem normalizer_P1_inf_centralizer_t [Finite G] :
    normalizer (D.P1 : Set G) ⊓ centralizer ({D.t} : Set G) =
      D.P1 ⊔ D.i2.range ⊔ zpowers D.h1 := by
  have hP1N : D.P1 ≤ normalizer (D.P1 : Set G) :=
    D.P1_le_centralizer_P1.trans (centralizer_le_normalizer _)
  have hL2N : D.i2.range ≤ normalizer (D.P1 : Set G) :=
    D.i2_range_le_centralizer_P1.trans (centralizer_le_normalizer _)
  have hh1N : zpowers D.h1 ≤ normalizer (D.P1 : Set G) :=
    zpowers_le.mpr D.h1_mem_normalizer_P1
  refine le_antisymm ?_ (sup_le (sup_le (le_inf hP1N D.P1_le_centralizer_t)
    (le_inf hL2N D.i2_range_le_centralizer_t)) (le_inf hh1N ?_))
  · intro g hg
    obtain ⟨hgn, hgt⟩ := mem_inf.mp hg
    rcases D.mem_centralizer_t_iff.mp hgt with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
    · have hx : ∀ a : ZMod 5, ∃ b : ZMod 5,
          x⁻¹ * thetaM a * x = thetaM b := by
        intro a
        have hmem : (D.i1 x * D.i2 y)⁻¹ * D.q1 (.ofAdd a) * (D.i1 x * D.i2 y) ∈
            D.P1 :=
          ((mem_normalizer_iff''.mp hgn) (D.q1 (.ofAdd a))).mp
            (D.q1.mem_range.mpr ⟨.ofAdd a, rfl⟩)
        rw [D.conj_q1_by_prod] at hmem
        obtain ⟨b, hb⟩ := hmem
        exact ⟨b.toAdd, by simpa [thetaHom] using (D.inj1 hb).symm⟩
      obtain ⟨u, k, hk⟩ := (thetaM_normalizer_iff x).mp hx
      rw [hk]
      have hq : D.q1 (.ofAdd u) ∈ D.P1 := D.q1.mem_range.mpr ⟨.ofAdd u, rfl⟩
      have hpow : D.h1 ^ k.val ∈ zpowers D.h1 := pow_mem (mem_zpowers _) _
      have hi : D.i2 y ∈ D.i2.range := D.i2.mem_range.mpr ⟨y, rfl⟩
      have hmem : D.q1 (.ofAdd u) * D.h1 ^ k.val * D.i2 y ∈
          D.P1 ⊔ D.i2.range ⊔ zpowers D.h1 := by
        refine mul_mem ?_ (mem_sup_left (mem_sup_right hi))
        exact mul_mem (mem_sup_left (mem_sup_left hq)) (mem_sup_right hpow)
      simpa [RootData.q1, SwapData.h1, thetaHom] using hmem
    · have hmem : (D.i1 x * D.i2 y * D.u)⁻¹ * D.q1 (.ofAdd 1) *
          (D.i1 x * D.i2 y * D.u) ∈ D.P1 :=
        ((mem_normalizer_iff''.mp hgn) (D.q1 (.ofAdd 1))).mp
          (D.q1.mem_range.mpr ⟨.ofAdd 1, rfl⟩)
      rw [D.conj_q1_by_prod_u] at hmem
      have hle : D.i2 (x⁻¹ * thetaM 1 * x) ∈ D.i2.range :=
        D.i2.mem_range.mpr ⟨x⁻¹ * thetaM 1 * x, rfl⟩
      have hbot : D.i2 (x⁻¹ * thetaM 1 * x) ∈ (⊥ : Subgroup G) := by
        rw [← D.P1_inf_i2_range]
        exact mem_inf.mpr ⟨hmem, hle⟩
      rw [mem_bot] at hbot
      have h1 : x⁻¹ * thetaM 1 * x = 1 := D.inj2 (by simpa using hbot)
      have h2 : thetaM 1 = 1 := by
        calc thetaM 1 = x * (x⁻¹ * thetaM 1 * x) * x⁻¹ := by group
          _ = 1 := by rw [h1]; group
      exact absurd h2 (by decide)
  · exact zpowers_le.mpr
      (mem_centralizer_singleton_iff.mpr (D.t_commute_i1 hM).eq.symm)

private theorem card_SL5 : Nat.card SL5 = 120 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem hM_sq_test : hM ^ 2 = -1 := by decide

private theorem cM_sq_test : cM ^ 2 = -1 := by decide

private theorem hM_pow_four : hM ^ 4 = 1 := by decide

private theorem hM_sq_ne_one : hM ^ 2 ≠ 1 := by decide

private theorem cM_conj_hM : cM * hM * cM⁻¹ = hM⁻¹ := by decide

private theorem t_ne_one : D.t ≠ 1 := by
  intro h
  have h1 : orderOf D.t = 1 := by rw [h, orderOf_one]
  rw [D.orderOf_t] at h1
  norm_num at h1

private theorem q8_a_one_sq : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 =
    QuaternionGroup.a 2 := by
  decide +kernel

private theorem q8_unique_involution (q : QuaternionGroup 2) (hq : q ^ 2 = 1) :
    q = 1 ∨ q = QuaternionGroup.a 2 := by
  revert q
  decide +kernel

private theorem P1_le_centralizer_i2_range : D.P1 ≤ centralizer (D.i2.range : Set G) := by
  rintro _ ⟨a, rfl⟩
  refine mem_centralizer_iff.mpr fun q hq => ?_
  obtain ⟨y, rfl⟩ := hq
  change D.i2 y * D.i1 (thetaHom a) = D.i1 (thetaHom a) * D.i2 y
  exact (D.commute (thetaHom a) y).eq.symm

private theorem P1_le_normalizer_i2_range : D.P1 ≤ normalizer (D.i2.range : Set G) :=
  D.P1_le_centralizer_i2_range.trans (centralizer_le_normalizer _)

private theorem P1_le_V [Finite G] : D.P1 ≤ D.V := by
  let C : Subgroup G := centralizer (D.P1 : Set G)
  have hP1C : D.P1 ≤ C := D.P1_le_centralizer_P1
  have hnormal : (D.P1.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP1C).mpr (by
      intro x hx
      have hle := Subgroup.centralizer_le_normalizer (D.P1 : Set G)
      exact hle (show x ∈ centralizer (D.P1 : Set G) from hx))
  have hodd : Odd (Nat.card (D.P1.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP1C).toEquiv, D.card_P1]
    norm_num
  have hle : D.P1.subgroupOf C ≤ CFSG.oddCore C := le_oddCore_of_normal hnormal hodd
  intro x hx
  have hx' : (⟨x, hP1C hx⟩ : C) ∈ D.P1.subgroupOf C := hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hP1C hx⟩, hle hx', rfl⟩

private theorem V_normal_in_centralizer :
    centralizer (D.P1 : Set G) ≤ normalizer (D.V : Set G) := by
  let C : Subgroup G := centralizer (D.P1 : Set G)
  let X : Subgroup C := CFSG.oddCore C
  have hXV : X.map C.subtype = D.V := rfl
  intro c hc
  have hcN : c ∈ (normalizer (X : Set C)).map C.subtype := by
    rw [Subgroup.normalizer_eq_top]
    exact ⟨⟨c, hc⟩, Subgroup.mem_top _, rfl⟩
  rw [← hXV]
  exact Subgroup.le_normalizer_map (f := C.subtype) hcN

private theorem normal_odd_eq_bot_of_quotient_center {H : Type*} [Group H] [Finite H]
    {N : Subgroup H} [N.Normal] (hNodd : Odd (Nat.card N))
    (hcenter : Nat.card (Subgroup.center H) = 2)
    (hquot : Nat.card (H ⧸ Subgroup.center H) = 60)
    (hsimple : IsSimpleGroup (H ⧸ Subgroup.center H)) : N = ⊥ := by
  let Z : Subgroup H := Subgroup.center H
  let π : H →* H ⧸ Z := QuotientGroup.mk' Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hNbar_normal : (N.map π).Normal :=
    (inferInstance : N.Normal).map π (QuotientGroup.mk'_surjective Z)
  have hinf : N ⊓ Z = ⊥ := by
    have hdvd : Nat.card (N ⊓ Z : Subgroup H) ∣ 2 := by
      rw [← hcenter]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hodd : Odd (Nat.card (N ⊓ Z : Subgroup H)) :=
      hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hcard : Nat.card (N ⊓ Z : Subgroup H) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · rw [h2] at hodd
        norm_num at hodd
    exact Subgroup.eq_bot_of_card_eq _ hcard
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
  · rw [eq_bot_iff]
    intro n hn
    have hmem : π n ∈ N.map π := ⟨n, hn, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hnZ : n ∈ Z := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hmem
    have : n ∈ N ⊓ Z := ⟨hn, hnZ⟩
    rwa [hinf, Subgroup.mem_bot] at this
  · let f : N →* H ⧸ Z := π.comp N.subtype
    have hsurj : Function.Surjective f := by
      intro y
      have hy : y ∈ N.map π := by rw [htop]; exact Subgroup.mem_top y
      obtain ⟨n, hn, hnπ⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨n, hn⟩, hnπ⟩
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have hmem : (a : H) * (b : H)⁻¹ ∈ N ⊓ Z := by
        refine mem_inf.mpr ⟨N.mul_mem a.2 (N.inv_mem b.2), ?_⟩
        rw [← hker]
        have habπ : π (a : H) = π (b : H) := by simpa [f] using hab
        exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, habπ, mul_inv_cancel])
      rw [hinf, Subgroup.mem_bot] at hmem
      exact mul_inv_eq_one.mp hmem
    have hcardN : Nat.card N = 60 := by
      rw [← hquot]
      exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
    rw [hcardN] at hNodd
    norm_num at hNodd

private theorem center_SL5_eq : (Subgroup.center SL5 : Set SL5) = {1, -1} := by
  ext x
  change x ∈ Subgroup.center SL5 ↔ x ∈ ({1, -1} : Set SL5)
  rw [sl5_mem_center_iff]
  simp [or_comm]

private theorem card_center_SL5 : Nat.card (Subgroup.center SL5) = 2 := by
  rw [← SetLike.coe_sort_coe, center_SL5_eq, Nat.card_coe_set_eq, Set.ncard_pair]
  exact Ne.symm sl5_neg_one_ne_one

private theorem card_quotient_center_SL5 :
    Nat.card (SL5 ⧸ Subgroup.center SL5) = 60 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL5)
  rw [card_SL5, card_center_SL5] at h
  omega

private theorem isSimpleGroup_quotient_center_SL5 :
    IsSimpleGroup (SL5 ⧸ Subgroup.center SL5) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := ZMod 5) (by
    rw [Nat.card_eq_fintype_card]
    norm_num)
  simpa using h

private theorem exists_quaternion_subgroup_image [Finite G] :
    ∃ T : Subgroup G, Nat.card T = 8 ∧ D.t ∈ T ∧
      (∀ x ∈ T, x ^ 2 = 1 → x = 1 ∨ x = D.t) ∧
      T ≤ D.i2.range ∧ IsSylowOf 2 T D.i2.range ∧
      Nonempty (T ≃* QuaternionGroup 2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hinj, hφa1, -⟩ := exists_quaternion_hom hM cM hM_pow_four hM_sq_ne_one
    (by rw [cM_sq_test, hM_sq_test]) cM_conj_hM
  let ψ : QuaternionGroup 2 →* G := D.i2.comp φ
  have hψinj : Function.Injective ψ := D.inj2.comp hinj
  let T : Subgroup G := ψ.range
  have hcardT : Nat.card T = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hφa2 : φ (QuaternionGroup.a 2) = -1 := by
    rw [← q8_a_one_sq, map_pow, hφa1, hM_sq_test]
  have hψa2 : ψ (QuaternionGroup.a 2) = D.t := by
    rw [show ψ = D.i2.comp φ from rfl, MonoidHom.comp_apply, hφa2, D.t_eq_i2]
  have htT : D.t ∈ T := ⟨QuaternionGroup.a 2, hψa2⟩
  have huniq : ∀ x ∈ T, x ^ 2 = 1 → x = 1 ∨ x = D.t := by
    intro x hxT hx2
    obtain ⟨q, rfl⟩ := hxT
    have hq : q ^ 2 = 1 := hψinj (by rw [map_pow, hx2, map_one])
    rcases q8_unique_involution q hq with hq1 | hqa
    · left; rw [hq1, map_one]
    · right; rw [hqa, hψa2]
  have hTleL2 : T ≤ D.i2.range := by
    rintro _ ⟨q, rfl⟩
    exact ⟨φ q, rfl⟩
  have hcardL2 : Nat.card D.i2.range = 120 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective D.inj2).toEquiv, card_SL5]
  have hsylL2 : IsSylowOf 2 T D.i2.range := by
    refine isSylowOf_of_card hTleL2 ?_
    rw [hcardT, hcardL2]
    decide +kernel
  exact ⟨T, hcardT, htT, huniq, hTleL2, hsylL2,
    ⟨(MonoidHom.ofInjective hψinj).symm⟩⟩

private theorem isSylowOf_quaternion_P1_sup_i2 [Finite G] {T : Subgroup G}
    (hcardT : Nat.card T = 8) (hTleL2 : T ≤ D.i2.range) :
    IsSylowOf 2 T (D.P1 ⊔ D.i2.range) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardL2 : Nat.card D.i2.range = 120 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective D.inj2).toEquiv, card_SL5]
  have hcardSup : Nat.card (D.P1 ⊔ D.i2.range : Subgroup G) = 600 := by
    rw [show D.P1 ⊔ D.i2.range = D.i2.range ⊔ D.P1 from sup_comm _ _,
      CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot (K := D.i2.range) (A := D.P1)
        D.P1_le_normalizer_i2_range (by rw [inf_comm, D.P1_inf_i2_range]),
      hcardL2, D.card_P1]
  refine isSylowOf_of_card (hTleL2.trans le_sup_right) ?_
  rw [hcardT, hcardSup]
  decide +kernel

private theorem characteristic_zpowers_quaternion_sylow {T : Subgroup G}
    (htT : D.t ∈ T) (huniq : ∀ x ∈ T, x ^ 2 = 1 → x = 1 ∨ x = D.t) :
    ((zpowers D.t).subgroupOf T).Characteristic := by
  have htT_ne_one : (⟨D.t, htT⟩ : T) ≠ 1 := by
    intro h
    exact D.t_ne_one (Subtype.ext_iff.mp h)
  rw [Subgroup.characteristic_iff_map_eq]
  intro σ
  have hfix : σ ⟨D.t, htT⟩ = ⟨D.t, htT⟩ := by
    have hord : orderOf (σ ⟨D.t, htT⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, D.orderOf_t]
    have hsq : (σ ⟨D.t, htT⟩) ^ 2 = 1 := by
      rw [← hord, pow_orderOf_eq_one]
    have hsq' : (σ ⟨D.t, htT⟩ : G) ^ 2 = 1 := by
      simpa using congrArg Subtype.val hsq
    rcases huniq (σ ⟨D.t, htT⟩) (σ ⟨D.t, htT⟩).2 hsq' with h | h
    · exfalso
      have h1 : σ ⟨D.t, htT⟩ = σ 1 := Subtype.ext (by simpa using h)
      exact htT_ne_one (σ.injective h1)
    · exact Subtype.ext (by simpa using h)
  have hsub : (zpowers D.t).subgroupOf T = zpowers ⟨D.t, htT⟩ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  rw [hsub, MonoidHom.map_zpowers]
  simpa using congrArg Subgroup.zpowers hfix

private theorem isSylowOf_quaternion_centralizer_P1 [Finite G] {T : Subgroup G}
    (htT : D.t ∈ T) (hchar : ((zpowers D.t).subgroupOf T).Characteristic)
    (hsylSup : IsSylowOf 2 T (D.P1 ⊔ D.i2.range)) :
    IsSylowOf 2 T (centralizer (D.P1 : Set G)) := by
  have hsylInf : IsSylowOf 2 T
      (centralizer (D.P1 : Set G) ⊓ centralizer ({D.t} : Set G)) := by
    rw [D.centralizer_P1_inf_centralizer_t]
    exact hsylSup
  exact isSylowOf_of_isSylowOf_inf_centralizer D.orderOf_t htT hchar hsylInf

private theorem exists_sylow_centralizer_P1 [Finite G] :
    ∃ T : Subgroup G, Nat.card T = 8 ∧ D.t ∈ T ∧
      IsSylowOf 2 T (centralizer (D.P1 : Set G)) ∧
      ((zpowers D.t).subgroupOf T).Characteristic ∧
      (∀ x ∈ T, x ^ 2 = 1 → x = 1 ∨ x = D.t) ∧
      Nonempty (T ≃* QuaternionGroup 2) := by
  obtain ⟨T, hcardT, htT, huniq, hTleL2, _, heT⟩ := D.exists_quaternion_subgroup_image
  have hsylSup := D.isSylowOf_quaternion_P1_sup_i2 hcardT hTleL2
  have hchar := D.characteristic_zpowers_quaternion_sylow htT huniq
  exact ⟨T, hcardT, htT, D.isSylowOf_quaternion_centralizer_P1 htT hchar hsylSup,
    hchar, huniq, heT⟩

private theorem odd_card_firstOddCore [Finite G] : Odd (Nat.card (firstOddCore D)) := by
  let C := firstCentralizer D
  let X := firstOddCore D
  have hXV : Nat.card X = Nat.card D.V := by
    rw [show D.V = X.map C.subtype from rfl,
      Subgroup.card_map_of_injective C.subtype_injective]
  rw [hXV]
  exact D.odd_card_V

private theorem brauer_suzuki_centrality [Finite G] :
    ∃ tC : firstCentralizer D, (tC : G) = D.t ∧ orderOf tC = 2 ∧
      ∀ c : firstCentralizer D,
        c⁻¹ * tC * c * tC⁻¹ ∈ firstOddCore D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := firstCentralizer D
  let X := firstOddCore D
  obtain ⟨T, -, htT, hsylC, -, -, ⟨eT⟩⟩ := D.exists_sylow_centralizer_P1
  have hTC : T ≤ C := hsylC.le
  obtain ⟨Q, hQ⟩ := hsylC.exists_sylow_eq_subgroupOf
  have hquat : Nonempty ((Q : Subgroup C) ≃* QuaternionGroup 2) := by
    rw [hQ]
    exact ⟨(Subgroup.subgroupOfEquivOfLe hTC).trans eT⟩
  let tC : C := ⟨D.t, hTC htT⟩
  have htQC : tC ∈ (Q : Subgroup C) := by
    rw [hQ]
    exact htT
  have htCord : orderOf tC = 2 := (Subgroup.orderOf_mk D.t (hTC htT)).trans D.orderOf_t
  have hBS := CFSG.BrauerSuzuki.brauer_suzuki 3 (by norm_num) Q hquat tC htQC htCord
  have htC2 : tC * tC = 1 := by
    rw [← pow_two, ← htCord, pow_orderOf_eq_one]
  have htCinv : tC⁻¹ = tC := inv_eq_of_mul_eq_one_right htC2
  refine ⟨tC, rfl, htCord, ?_⟩
  intro c
  have hcomm := (Subgroup.mem_center_iff.mp hBS (QuotientGroup.mk c)).symm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
  simpa [X, htCinv, mul_assoc] using hcomm

private theorem conj_zpowers_mem_firstOddCore_sup [Finite G]
    {tC : firstCentralizer D} (htCord : orderOf tC = 2)
    (hcen : ∀ c : firstCentralizer D,
      c⁻¹ * tC * c * tC⁻¹ ∈ firstOddCore D) (c : firstCentralizer D) :
    c * tC * c⁻¹ ∈ firstOddCore D ⊔ zpowers tC := by
  let X := firstOddCore D
  let h : firstCentralizer D := c⁻¹ * tC * c * tC⁻¹
  have hhX : h ∈ X := hcen c
  have htC2 : tC * tC = 1 := by
    rw [← pow_two, ← htCord, pow_orderOf_eq_one]
  have htCinv : tC⁻¹ = tC := inv_eq_of_mul_eq_one_right htC2
  have h1 : c⁻¹ * tC * c = h * tC := by
    dsimp [h]
    rw [htCinv, mul_assoc (c⁻¹ * tC * c) tC tC, htC2, mul_one]
  have hconj : tC = (c * h * c⁻¹) * (c * tC * c⁻¹) := by
    calc tC = c * (c⁻¹ * tC * c) * c⁻¹ := by group
      _ = c * (h * tC) * c⁻¹ := by rw [h1]
      _ = (c * h * c⁻¹) * (c * tC * c⁻¹) := by
        rw [mul_assoc (c * h) c⁻¹ (c * tC * c⁻¹)]
        have hc : c⁻¹ * (c * tC * c⁻¹) = tC * c⁻¹ := by group
        rw [hc]
        group
  have h2 : c * tC * c⁻¹ = (c * h * c⁻¹)⁻¹ * tC := by
    calc c * tC * c⁻¹ = (c * h * c⁻¹)⁻¹ * ((c * h * c⁻¹) * (c * tC * c⁻¹)) := by
          group
      _ = (c * h * c⁻¹)⁻¹ * tC := by rw [← hconj]
  rw [h2]
  exact Subgroup.mul_mem_sup
    (X.inv_mem ((inferInstance : X.Normal).conj_mem h hhX c))
    (mem_zpowers tC)

private theorem firstOddCore_sup_zpowers_normal [Finite G]
    {tC : firstCentralizer D} (htCord : orderOf tC = 2)
    (hcen : ∀ c : firstCentralizer D,
      c⁻¹ * tC * c * tC⁻¹ ∈ firstOddCore D) :
    (firstOddCore D ⊔ zpowers tC).Normal := by
  let X := firstOddCore D
  let N : Subgroup (firstCentralizer D) := X ⊔ zpowers tC
  refine ⟨fun n hn c => ?_⟩
  rw [Subgroup.mem_sup_of_normal_left] at hn
  obtain ⟨x, hx, y, hy, rfl⟩ := hn
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hx' : c * x * c⁻¹ ∈ X := (inferInstance : X.Normal).conj_mem x hx c
  have hct' : c * tC * c⁻¹ ∈ N := D.conj_zpowers_mem_firstOddCore_sup htCord hcen c
  have hzpow : c * tC ^ k * c⁻¹ = (c * tC * c⁻¹) ^ k := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  have hmemEq : c * (x * tC ^ k) * c⁻¹ =
      (c * x * c⁻¹) * (c * tC * c⁻¹) ^ k := by
    rw [show c * (x * tC ^ k) * c⁻¹ = (c * x * c⁻¹) * (c * tC ^ k * c⁻¹) by group,
      hzpow]
  rw [hmemEq]
  exact mul_mem (Subgroup.mem_sup_left hx') (N.zpow_mem hct' k)

private theorem isSylow_zpowers_firstOddCore_sup [Finite G]
    {tC : firstCentralizer D} (htCord : orderOf tC = 2) :
    IsSylowOf 2 (zpowers tC) (firstOddCore D ⊔ zpowers tC) := by
  let X := firstOddCore D
  let N : Subgroup (firstCentralizer D) := X ⊔ zpowers tC
  have hXodd : Odd (Nat.card X) := D.odd_card_firstOddCore
  have hcardT : Nat.card (zpowers tC) = 2 := by
    rw [Nat.card_zpowers, htCord]
  have hTCp : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [hcardT]; norm_num)
  have hcardN : Nat.card N = Nat.card X * 2 := by
    have hnorm : zpowers tC ≤ normalizer (X : Set (firstCentralizer D)) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hinf : X ⊓ zpowers tC = ⊥ := by
      rw [inf_comm]
      exact CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hTCp hXodd
    rw [show N = X ⊔ zpowers tC from rfl,
      CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot (K := X) (A := zpowers tC) hnorm hinf,
      hcardT]
  have hindex : (zpowers tC).relIndex N = Nat.card X := by
    have hrel := Subgroup.relIndex_mul_card (H := zpowers tC) (K := N)
    rw [inf_eq_left.mpr (le_sup_right : zpowers tC ≤ N), hcardN, hcardT] at hrel
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) hrel
  rw [isSylowOf_iff]
  exact ⟨le_sup_right, hTCp, by rw [hindex]; exact hXodd.not_two_dvd_nat⟩

private theorem firstOddCore_sup_centralizer_top [Finite G]
    {tC : firstCentralizer D} (htCord : orderOf tC = 2)
    (hNnormal : (firstOddCore D ⊔ zpowers tC).Normal) :
    (⊤ : Subgroup (firstCentralizer D)) =
      firstOddCore D ⊔ centralizer ({tC} : Set (firstCentralizer D)) := by
  let X := firstOddCore D
  let N : Subgroup (firstCentralizer D) := X ⊔ zpowers tC
  have hsylN : IsSylowOf 2 (zpowers tC) N := D.isSylow_zpowers_firstOddCore_sup htCord
  obtain ⟨QN, hQN⟩ := hsylN.exists_sylow_eq_subgroupOf
  have hFr : normalizer (zpowers tC : Set (firstCentralizer D)) ⊔ N = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top QN
    rwa [hQN, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (le_sup_right : zpowers tC ≤ N)] at h
  refine le_antisymm ?_ le_top
  intro c hc
  haveI : N.Normal := hNnormal
  have hmem : c ∈ normalizer (zpowers tC : Set (firstCentralizer D)) ⊔ N := by
    rw [hFr]
    exact Subgroup.mem_top c
  rw [Subgroup.mem_sup_of_normal_right] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have haZ : a ∈ centralizer ({tC} : Set (firstCentralizer D)) := by
    rwa [CFSG.Walter.JT.normalizer_zpowers_of_orderOf_eq_two htCord] at ha
  have hTle : zpowers tC ≤ centralizer ({tC} : Set (firstCentralizer D)) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hbZ : b ∈ X ⊔ centralizer ({tC} : Set (firstCentralizer D)) :=
    (sup_le le_sup_left (hTle.trans le_sup_right)) hb
  rw [← hab]
  exact mul_mem (Subgroup.mem_sup_right haZ) hbZ

private theorem centralizer_le_V_sup_P1_sup_i2 [Finite G]
    {tC : firstCentralizer D} (htC_val : (tC : G) = D.t)
    (htop : (⊤ : Subgroup (firstCentralizer D)) =
      firstOddCore D ⊔ centralizer ({tC} : Set (firstCentralizer D))) :
    firstCentralizer D ≤ D.V ⊔ (D.P1 ⊔ D.i2.range) := by
  let C := firstCentralizer D
  let X := firstOddCore D
  intro g hg
  have hg' : (⟨g, hg⟩ : C) ∈ X ⊔ centralizer ({tC} : Set C) := by
    rw [← htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_left] at hg'
  obtain ⟨x, hxX, y, hyZ, hxy⟩ := hg'
  have hxV : (x : G) ∈ D.V := Subgroup.mem_map.mpr ⟨x, hxX, rfl⟩
  have hyc : (y : G) ∈ centralizer ({D.t} : Set G) := by
    have hy' := (mem_centralizer_singleton_iff.mp hyZ : y * tC = tC * y)
    exact mem_centralizer_singleton_iff.mpr (by
      simpa [htC_val] using congrArg Subtype.val hy')
  have hyPL : (y : G) ∈ D.P1 ⊔ D.i2.range := by
    rw [← D.centralizer_P1_inf_centralizer_t]
    exact mem_inf.mpr ⟨y.2, hyc⟩
  rw [show g = (x : G) * (y : G) from (congrArg Subtype.val hxy).symm]
  have hPL : D.P1 ⊔ D.i2.range ≤ D.V ⊔ (D.P1 ⊔ D.i2.range) :=
    sup_le (D.P1_le_V.trans le_sup_left) (le_sup_right.trans le_sup_right)
  exact mul_mem (Subgroup.mem_sup_left hxV) (hPL hyPL)

private theorem centralizer_P1_eq_i2_sup_V [Finite G] :
    centralizer (D.P1 : Set G) = D.i2.range ⊔ D.V := by
  let C := firstCentralizer D
  have hVle : D.V ≤ C := D.V_le_centralizer
  have hL2le : D.i2.range ≤ C := D.i2_range_le_centralizer_P1
  refine le_antisymm ?_ (sup_le hL2le hVle)
  obtain ⟨tC, htC_val, htCord, hcen⟩ := D.brauer_suzuki_centrality
  have hNnormal := D.firstOddCore_sup_zpowers_normal htCord hcen
  have htop := D.firstOddCore_sup_centralizer_top htCord hNnormal
  have hCdecomp := D.centralizer_le_V_sup_P1_sup_i2 htC_val htop
  intro g hg
  have hmem := hCdecomp hg
  have hle : D.V ⊔ (D.P1 ⊔ D.i2.range) ≤ D.i2.range ⊔ D.V :=
    sup_le le_sup_right (sup_le (D.P1_le_V.trans le_sup_right) le_sup_left)
  exact hle hmem

private theorem t_central_mod_V [Finite G] {c : G}
    (hc : c ∈ centralizer (D.P1 : Set G)) :
    c⁻¹ * D.t * c * D.t⁻¹ ∈ D.V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer (D.P1 : Set G)
  obtain ⟨T, -, htT, hsylC, -, -, ⟨eT⟩⟩ := D.exists_sylow_centralizer_P1
  have hTC : T ≤ C := hsylC.le
  obtain ⟨Q, hQ⟩ := hsylC.exists_sylow_eq_subgroupOf
  have hquat : Nonempty ((Q : Subgroup C) ≃* QuaternionGroup 2) := by
    rw [hQ]
    exact ⟨(Subgroup.subgroupOfEquivOfLe hTC).trans eT⟩
  let tC : C := ⟨D.t, hTC htT⟩
  have htQC : tC ∈ (Q : Subgroup C) := by
    rw [hQ]
    exact htT
  have htCord : orderOf tC = 2 := (Subgroup.orderOf_mk D.t (hTC htT)).trans D.orderOf_t
  have hBS := CFSG.BrauerSuzuki.brauer_suzuki 3 (by norm_num) Q hquat tC htQC htCord
  let cC : C := ⟨c, hc⟩
  have hcomm := (Subgroup.mem_center_iff.mp hBS (QuotientGroup.mk cC)).symm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
  have htCinv : tC⁻¹ = tC := by
    have h2 : tC * tC = 1 := by
      rw [← pow_two, ← htCord, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h2
  have hmem : cC⁻¹ * tC * cC * tC⁻¹ ∈ CFSG.oddCore C := by
    simpa [htCinv, mul_assoc] using hcomm
  exact Subgroup.mem_map.mpr ⟨cC⁻¹ * tC * cC * tC⁻¹, hmem, rfl⟩

private theorem P1_le_Q [Finite G] : D.P1 ≤ D.Q := by
  have hset := (D.odd_complement_of_diagonal_centralizer (G := G)).2.2.1
  intro x hx
  rw [← SetLike.mem_coe, hset]
  exact Set.mem_mul.mpr ⟨1, one_mem _,
    x, (le_sup_left : D.P1 ≤ D.R) hx, one_mul x⟩

private theorem P3_le_Q [Finite G] : D.P3 ≤ D.Q := by
  have hset := (D.odd_complement_of_diagonal_centralizer (G := G)).2.2.1
  rw [D.P3_eq_map_D2]
  intro x hx
  obtain ⟨d, hd, rfl⟩ := hx
  have hdR : d ∈ D.R := by
    obtain ⟨a, rfl⟩ := hd
    exact Subgroup.mul_mem_sup (D.q1.mem_range.mpr ⟨a, rfl⟩)
      (D.q2.mem_range.mpr ⟨a⁻¹, rfl⟩)
  rw [← SetLike.mem_coe, hset]
  exact Set.mem_mul.mpr ⟨(MulAut.conj D.y⁻¹).toMonoidHom d, ⟨d, hdR, rfl⟩,
    1, one_mem _, mul_one _⟩

private theorem P3_le_centralizer_P1 [Finite G] :
    D.P3 ≤ centralizer (D.P1 : Set G) := by
  intro p hp
  refine mem_centralizer_iff.mpr fun x hx => ?_
  have hQab : ∀ a ∈ D.Q, ∀ b ∈ D.Q, Commute a b :=
    (D.elementary_abelian_three_space (G := G)).2.1
  exact (hQab p (D.P3_le_Q hp) x (D.P1_le_Q hx)).eq.symm

private theorem P3_le_V [Finite G] : D.P3 ≤ D.V := by
  intro p hp
  obtain ⟨a, rfl⟩ := hp
  have hpC := D.P3_le_centralizer_P1 (D.q3.mem_range.mpr ⟨a, rfl⟩)
  have hmem := t_central_mod_V (D := D) hpC
  have htinv : D.t * D.q3 a * D.t⁻¹ = (D.q3 a)⁻¹ := by
    have h := D.t_conj_q3 a.toAdd
    rw [show (.ofAdd (-a.toAdd) : Multiplicative (ZMod 5)) = (.ofAdd a.toAdd)⁻¹ from rfl,
      map_inv] at h
    simpa [D.t_inv] using h
  have hsqV : (D.q3 a)⁻¹ * (D.q3 a)⁻¹ ∈ D.V := by
    simpa [htinv, mul_assoc] using hmem
  have hdvd : orderOf (D.q3 a) ∣ 5 := by
    have := D.P3.orderOf_dvd_natCard (D.q3.mem_range.mpr ⟨a, rfl⟩)
    rwa [D.card_P3] at this
  have hp5 : (D.q3 a) ^ 5 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hp2V : (D.q3 a) ^ 2 ∈ D.V := by
    simpa [pow_two, mul_inv_rev] using D.V.inv_mem hsqV
  have hp_eq : D.q3 a = ((D.q3 a) ^ 2) ^ 3 := by
    rw [show ((D.q3 a) ^ 2) ^ 3 = (D.q3 a) ^ 6 by group]
    rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_succ, hp5, one_mul]
  rw [hp_eq]
  exact D.V.pow_mem hp2V 3

private theorem i2_inf_V_eq_bot [Finite G] : D.i2.range ⊓ D.V = ⊥ := by
  let N0 : Subgroup SL5 := D.V.comap D.i2
  have hN0normal : N0.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    have hnorm := D.V_normal_in_centralizer
      (D.i2_range_le_centralizer_P1 (D.i2.mem_range.mpr ⟨g, rfl⟩))
    have hmem := (mem_normalizer_iff.mp hnorm (D.i2 n)).mp hn
    rwa [← map_mul, ← map_inv, ← map_mul] at hmem
  have hN0odd : Odd (Nat.card N0) := by
    have hmaple : N0.map D.i2 ≤ D.V := Subgroup.map_comap_le (f := D.i2) (H := D.V)
    have hcard : Nat.card (N0.map D.i2) = Nat.card N0 :=
      Subgroup.card_map_of_injective D.inj2
    rw [← hcard]
    exact D.odd_card_V.of_dvd_nat (Subgroup.card_dvd_of_le hmaple)
  have hN0bot : N0 = ⊥ :=
    normal_odd_eq_bot_of_quotient_center hN0odd card_center_SL5
      card_quotient_center_SL5 isSimpleGroup_quotient_center_SL5
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL2, hxV⟩ := mem_inf.mp hx
  obtain ⟨y, rfl⟩ := hxL2
  have hy : y ∈ N0 := hxV
  rw [hN0bot, Subgroup.mem_bot] at hy
  rw [hy, map_one]
  exact Subgroup.mem_bot.mpr rfl

private theorem exists_mul_of_mem_centralizer_P1_t [Finite G] {g : G}
    (hgP1 : g ∈ centralizer (D.P1 : Set G)) (hgt : g ∈ centralizer ({D.t} : Set G)) :
    ∃ p ∈ D.P1, ∃ l ∈ D.i2.range, p * l = g := by
  rcases D.mem_centralizer_t_iff.mp hgt with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · have hx : ∀ a : ZMod 5, x * thetaM a = thetaM a * x := by
      intro a
      have hcomm := (mem_centralizer_iff.mp hgP1) (D.q1 (.ofAdd a))
        (D.q1.mem_range.mpr ⟨.ofAdd a, rfl⟩)
      have hconj : (D.i1 x * D.i2 y)⁻¹ * D.q1 (.ofAdd a) * (D.i1 x * D.i2 y) =
          D.q1 (.ofAdd a) := by
        calc (D.i1 x * D.i2 y)⁻¹ * D.q1 (.ofAdd a) * (D.i1 x * D.i2 y)
            = (D.i1 x * D.i2 y)⁻¹ * (D.q1 (.ofAdd a) * (D.i1 x * D.i2 y)) := by group
          _ = (D.i1 x * D.i2 y)⁻¹ * ((D.i1 x * D.i2 y) * D.q1 (.ofAdd a)) := by rw [hcomm]
          _ = D.q1 (.ofAdd a) := by group
      rw [D.conj_q1_by_prod] at hconj
      have h : x⁻¹ * thetaM a * x = thetaM a := by
        simpa [thetaHom] using D.inj1 hconj
      calc x * thetaM a = x * (x⁻¹ * thetaM a * x) := by rw [h]
        _ = thetaM a * x := by group
    rcases (thetaM_centralizer_iff x).mp hx with ⟨c, rfl | rfl⟩
    · exact ⟨D.q1 (.ofAdd c), D.q1.mem_range.mpr ⟨.ofAdd c, rfl⟩,
        D.i2 y, D.i2.mem_range.mpr ⟨y, rfl⟩, rfl⟩
    · refine ⟨D.q1 (.ofAdd c), D.q1.mem_range.mpr ⟨.ofAdd c, rfl⟩,
        D.i2 (-y), D.i2.mem_range.mpr ⟨-y, rfl⟩, ?_⟩
      change D.i1 (thetaM c) * D.i2 (-y) = D.i1 (-thetaM c) * D.i2 y
      rw [D.i1_neg, D.t_eq_i2]
      have hneg : D.i2 (-y) = D.i2 (-1) * D.i2 y := by
        simpa only [neg_one_mul] using (map_mul D.i2 (-1 : SL5) y)
      rw [show D.i1 (thetaM c) * D.i2 (-y) =
        (D.i1 (thetaM c) * D.i2 (-1)) * D.i2 y by
          rw [hneg]
          group]
      rw [(D.commute (thetaM c) (-1)).eq]
  · have hcomm := (mem_centralizer_iff.mp hgP1) (D.q1 (.ofAdd 1))
      (D.q1.mem_range.mpr ⟨.ofAdd 1, rfl⟩)
    have hconj : (D.i1 x * D.i2 y * D.u)⁻¹ * D.q1 (.ofAdd 1) *
        (D.i1 x * D.i2 y * D.u) = D.q1 (.ofAdd 1) := by
      calc (D.i1 x * D.i2 y * D.u)⁻¹ * D.q1 (.ofAdd 1) * (D.i1 x * D.i2 y * D.u)
          = (D.i1 x * D.i2 y * D.u)⁻¹ *
              (D.q1 (.ofAdd 1) * (D.i1 x * D.i2 y * D.u)) := by group
        _ = (D.i1 x * D.i2 y * D.u)⁻¹ *
              ((D.i1 x * D.i2 y * D.u) * D.q1 (.ofAdd 1)) := by rw [hcomm]
        _ = D.q1 (.ofAdd 1) := by group
    rw [D.conj_q1_by_prod_u] at hconj
    have h := i1_eq_i2_iff D.inj1 D.inj2 D.orderOf_t D.range_inf |>.mp hconj.symm
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)

private theorem exists_mul_of_mem_P1_sup_i2_range [Finite G] {g : G}
    (hg : g ∈ D.P1 ⊔ D.i2.range) :
    ∃ p ∈ D.P1, ∃ l ∈ D.i2.range, p * l = g := by
  have hle : D.P1 ⊔ D.i2.range ≤
      centralizer (D.P1 : Set G) ⊓ centralizer ({D.t} : Set G) :=
    le_inf (sup_le D.P1_le_centralizer_P1 D.i2_range_le_centralizer_P1)
      (sup_le D.P1_le_centralizer_t D.i2_range_le_centralizer_t)
  exact D.exists_mul_of_mem_centralizer_P1_t (hle hg).1 (hle hg).2

private theorem V_inf_centralizer_t_eq_P1 [Finite G] :
    D.V ⊓ centralizer ({D.t} : Set G) = D.P1 := by
  refine le_antisymm ?_ (le_inf D.P1_le_V D.P1_le_centralizer_t)
  intro x hx
  obtain ⟨hxV, hxt⟩ := mem_inf.mp hx
  have hxPL : x ∈ D.P1 ⊔ D.i2.range := by
    rw [← D.centralizer_P1_inf_centralizer_t]
    exact mem_inf.mpr ⟨D.V_le_centralizer hxV, hxt⟩
  obtain ⟨p, hpP1, l, hlL2, hpl⟩ := D.exists_mul_of_mem_P1_sup_i2_range hxPL
  have hlV : l ∈ D.V := by
    have hl : l = p⁻¹ * x := by rw [← hpl]; group
    rw [hl]
    exact D.V.mul_mem (D.V.inv_mem (D.P1_le_V hpP1)) hxV
  have hlbot : l ∈ (⊥ : Subgroup G) := by
    rw [← D.i2_inf_V_eq_bot]
    exact mem_inf.mpr ⟨hlL2, hlV⟩
  rw [Subgroup.mem_bot] at hlbot
  rw [← hpl, hlbot, mul_one]
  exact hpP1

private theorem P1_subgroupOf_V_normal : (D.P1.subgroupOf D.V).Normal := by
  refine ⟨fun n hn v => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hcomm := mem_centralizer_iff.mp
    (D.V_le_centralizer (Subgroup.mem_subgroupOf.mp v.2)) n.val hn
  have hfix : (v : G) * n.val * (v : G)⁻¹ = n.val := by
    rw [← hcomm]
    group
  change (v : G) * n.val * (v : G)⁻¹ ∈ D.P1
  rw [hfix]
  exact hn

private instance instNormalP1SubgroupOfV {D : RootData G} :
    (D.P1.subgroupOf D.V).Normal :=
  P1_subgroupOf_V_normal D

private abbrev tZpowers (D : RootData G) : Subgroup G := zpowers D.t

private noncomputable def tConjAction (D : RootData G) : tZpowers D →* MulAut D.V :=
  (D.V.normalizerMonoidHom).comp
    (Subgroup.inclusion (zpowers_le.mpr
      (D.V_normal_in_centralizer D.t_mem_centralizer_P1)))

private theorem tConjAction_mem_P1 {a : tZpowers D} {n : D.V}
    (hn : n ∈ D.P1.subgroupOf D.V) : tConjAction D a n ∈ D.P1.subgroupOf D.V := by
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (n : G) ∈ D.P1 := hn
  obtain ⟨b, hb⟩ := hn
  have hcommA : Commute (a : G) (D.q1 b) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    rw [← hk]
    exact (D.t_commute_i1 (thetaHom b)).zpow_left k
  have hfix : tConjAction D a n = n := by
    apply Subtype.ext
    change (a : G) * (n : G) * (a : G)⁻¹ = (n : G)
    calc (a : G) * (n : G) * (a : G)⁻¹ = (a : G) * D.q1 b * (a : G)⁻¹ := by rw [hb]
      _ = D.q1 b := by rw [hcommA.eq]; group
      _ = (n : G) := hb
  rw [hfix]
  exact hn'

private noncomputable def tConjActionOnQuotient (D : RootData G) :
    tZpowers D →* MulAut (D.V ⧸ D.P1.subgroupOf D.V) := by
  letI : (D.P1.subgroupOf D.V).Normal := D.P1_subgroupOf_V_normal
  exact quotientAction (tConjAction D) (D.P1.subgroupOf D.V)
    (fun a n hn => D.tConjAction_mem_P1 hn)

private theorem fixed_points_tConjAction_eq_P1 [Finite G] :
    {c : D.V | ∀ a : tZpowers D, tConjAction D a c = c} =
      (D.P1.subgroupOf D.V : Set D.V) := by
  let V := D.V
  let P : Subgroup V := D.P1.subgroupOf D.V
  let tA : tZpowers D := ⟨D.t, mem_zpowers D.t⟩
  ext c
  constructor
  · intro hc
    have htfix : tConjAction D tA c = c := hc tA
    have htfixG : D.t * (c : G) * D.t⁻¹ = (c : G) := by
      have h := congrArg Subtype.val htfix
      simpa [tConjAction, tA, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    have hmem : (c : G) ∈ D.V ⊓ centralizer ({D.t} : Set G) := by
      refine mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (c : G) * D.t = (D.t * (c : G) * D.t⁻¹) * D.t := by rw [htfixG]
        _ = D.t * (c : G) := by group
    rw [D.V_inf_centralizer_t_eq_P1] at hmem
    exact hmem
  · intro hc a
    have hcP1 : (c : G) ∈ D.P1 := Subgroup.mem_subgroupOf.mp hc
    obtain ⟨b, hb⟩ := hcP1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hcommA : Commute (a : G) (c : G) := by
      rw [← hk, ← hb]
      exact (D.t_commute_i1 (thetaHom b)).zpow_left k
    apply Subtype.ext
    change (a : G) * (c : G) * (a : G)⁻¹ = (c : G)
    calc (a : G) * (c : G) * (a : G)⁻¹ = (c : G) * (a : G) * (a : G)⁻¹ := by
          rw [hcommA.eq]
      _ = (c : G) := by group

private theorem mk_image_P1_subgroupOf_V_eq_singleton :
    (QuotientGroup.mk' (D.P1.subgroupOf D.V)) '' (D.P1.subgroupOf D.V : Set D.V) =
      {(1 : D.V ⧸ D.P1.subgroupOf D.V)} := by
  let P : Subgroup D.V := D.P1.subgroupOf D.V
  ext q
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (QuotientGroup.eq_one_iff (N := P) c).mpr hc
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨1, P.one_mem, map_one (QuotientGroup.mk' P)⟩

private theorem fixed_points_quotient_tConjAction [Finite G]
    {q : D.V ⧸ D.P1.subgroupOf D.V}
    (hq : ∀ a : tZpowers D, tConjActionOnQuotient D a q = q) : q = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := D.V
  let P : Subgroup V := D.P1.subgroupOf D.V
  haveI : P.Normal := D.P1_subgroupOf_V_normal
  have hA2 : IsPGroup 2 (tZpowers D) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, D.orderOf_t]; norm_num)
  have hcop : ¬ 2 ∣ Nat.card P := by
    have hcard : Nat.card P = 5 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.P1_le_V).toEquiv, D.card_P1]
    rw [hcard]
    norm_num
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hA2
    (tConjAction D) P (fun a n hn => D.tConjAction_mem_P1 hn) hcop
  have hq' : ∀ a : tZpowers D,
      quotientAction (tConjAction D) P (fun a n hn => D.tConjAction_mem_P1 hn) a q = q := hq
  have hmem : q ∈ (QuotientGroup.mk' P) ''
      {c : V | ∀ a : tZpowers D, tConjAction D a c = c} := by
    rw [← hlift]
    exact hq'
  rw [D.fixed_points_tConjAction_eq_P1, D.mk_image_P1_subgroupOf_V_eq_singleton] at hmem
  exact hmem

private theorem isMulCommutative_V_quotient_P1 [Finite G] :
    IsMulCommutative (D.V ⧸ D.P1.subgroupOf D.V) := by
  classical
  let V := D.V
  let P : Subgroup V := D.P1.subgroupOf D.V
  haveI : P.Normal := D.P1_subgroupOf_V_normal
  let tA : tZpowers D := ⟨D.t, mem_zpowers D.t⟩
  let φ : MulAut (V ⧸ P) := tConjActionOnQuotient D tA
  have htA2 : tA * tA = 1 := by
    apply Subtype.ext
    exact D.t_mul_t
  have hφ2 : φ * φ = 1 := by
    change tConjActionOnQuotient D tA * tConjActionOnQuotient D tA = 1
    rw [← map_mul, htA2, map_one]
  have hφinv : Function.Involutive (φ : V ⧸ P → V ⧸ P) := by
    intro q
    change (φ * φ) q = q
    rw [hφ2, MulAut.one_apply]
  have hφ : MonoidHom.FixedPointFree (φ : V ⧸ P → V ⧸ P) := by
    intro q hq
    apply D.fixed_points_quotient_tConjAction
    intro a
    have hφpow : ∀ k : ℤ, (φ ^ k) q = q := by
      intro k
      induction k using Int.induction_on with
      | zero => rw [zpow_zero, MulAut.one_apply]
      | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hq, ih]
      | pred n ih =>
          have hinv : φ⁻¹ = φ := inv_eq_of_mul_eq_one_right hφ2
          rw [zpow_sub_one, MulAut.mul_apply, hinv, hq, ih]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hak : tConjActionOnQuotient D a = φ ^ k := by
      apply MulEquiv.ext
      intro x
      change tConjActionOnQuotient D a x = (φ ^ k) x
      have haeq : a = tA ^ k := by
        apply Subtype.ext
        change (a : G) = D.t ^ k
        exact hk.symm
      rw [haeq, map_zpow]
    rw [hak]
    exact hφpow k
  exact IsMulCommutative.of_comm
    (MonoidHom.FixedPointFree.commute_all_of_involutive hφ hφinv)

private theorem commutator_V_le_P1 [Finite G] : ⁅D.V, D.V⁆ ≤ D.P1 := by
  let V := D.V
  let P : Subgroup V := D.P1.subgroupOf D.V
  haveI : P.Normal := D.P1_subgroupOf_V_normal
  haveI : IsMulCommutative (V ⧸ P) := isMulCommutative_V_quotient_P1 (D := D)
  have hcomm : _root_.commutator V ≤ P :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (V ⧸ P))
  calc ⁅D.V, D.V⁆ = (_root_.commutator V).map V.subtype :=
        (Subgroup.map_subtype_commutator V).symm
    _ ≤ P.map V.subtype := Subgroup.map_mono hcomm
    _ = D.P1 := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr D.P1_le_V]

private theorem Q_inf_V_eq [Finite G] : D.Q ⊓ D.V = D.P1 ⊔ D.P3 := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    obtain ⟨hxQ, hxV⟩ := mem_inf.mp hx
    obtain ⟨a, ha, -⟩ :=
      (D.elementary_abelian_three_space (G := G)).2.2.2.2.1 x hxQ
    set q1 : G := D.q1 (.ofAdd (a 0)) with hq1def
    set q2 : G := D.q2 (.ofAdd (a 1)) with hq2def
    set q3 : G := D.q3 (.ofAdd (a 2)) with hq3def
    have hq1V : q1 ∈ D.V :=
      D.P1_le_V (D.q1.mem_range.mpr ⟨.ofAdd (a 0), rfl⟩)
    have hq3V : q3 ∈ D.V :=
      D.P3_le_V (D.q3.mem_range.mpr ⟨.ofAdd (a 2), rfl⟩)
    have hq1Q : q1 ∈ D.Q :=
      D.P1_le_Q (D.q1.mem_range.mpr ⟨.ofAdd (a 0), rfl⟩)
    have hq3Q : q3 ∈ D.Q :=
      D.P3_le_Q (D.q3.mem_range.mpr ⟨.ofAdd (a 2), rfl⟩)
    have hq2 : q2 = q1⁻¹ * x * q3⁻¹ := by
      rw [ha]
      group
    have hq2Q : q2 ∈ D.Q := by
      rw [hq2]
      exact D.Q.mul_mem (D.Q.mul_mem (D.Q.inv_mem hq1Q) hxQ) (D.Q.inv_mem hq3Q)
    have hq2V : q2 ∈ D.V := by
      rw [hq2]
      exact D.V.mul_mem (D.V.mul_mem (D.V.inv_mem hq1V) hxV) (D.V.inv_mem hq3V)
    have hq2L : q2 ∈ D.i2.range := by
      rw [hq2def]
      exact D.i2.mem_range.mpr ⟨thetaHom (.ofAdd (a 1)), rfl⟩
    have hq2bot : q2 ∈ (⊥ : Subgroup G) := by
      rw [← D.i2_inf_V_eq_bot]
      exact mem_inf.mpr ⟨hq2L, hq2V⟩
    rw [Subgroup.mem_bot] at hq2bot
    have hq2one : D.q2 (.ofAdd (a 1)) = 1 := by
      rw [← hq2def]
      exact hq2bot
    have ha1 : a 1 = 0 := by
      have h : D.q2 (.ofAdd (a 1)) = D.q2 1 := by rw [hq2one, map_one]
      simpa using congrArg Multiplicative.toAdd (D.q2_injective h)
    have hx13 : x = q1 * q3 := by
      rw [ha, hq2bot, mul_one]
    rw [hx13]
    exact Subgroup.mul_mem_sup (D.q1.mem_range.mpr ⟨.ofAdd (a 0), rfl⟩)
      (D.q3.mem_range.mpr ⟨.ofAdd (a 2), rfl⟩)
  · intro p hp
    exact mem_inf.mpr ⟨D.P1_le_Q hp, D.P1_le_V hp⟩
  · intro p hp
    exact mem_inf.mpr ⟨D.P3_le_Q hp, D.P3_le_V hp⟩

private theorem exists_sylow_normalizer_map {C M : Subgroup G} [Finite G]
    (hCM : C ≤ M) (Q : Sylow 2 C) :
    ∃ P : Sylow 2 (C.subgroupOf M),
      (((P : Subgroup (C.subgroupOf M)).map (C.subgroupOf M).subtype : Subgroup M).map
        M.subtype) = (Q : Subgroup C).map C.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : C ≃* C.subgroupOf M := (Subgroup.subgroupOfEquivOfLe hCM).symm
  let P : Sylow 2 (C.subgroupOf M) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  refine ⟨P, ?_⟩
  have hPcoe : (P : Subgroup (C.subgroupOf M)) =
      (Q : Subgroup C).map e.toMonoidHom := Sylow.coe_mapSurjective e.surjective Q
  have hcomp : (M.subtype.comp (C.subgroupOf M).subtype).comp e.toMonoidHom = C.subtype := by
    ext x
    rfl
  calc ((P : Subgroup (C.subgroupOf M)).map (C.subgroupOf M).subtype).map M.subtype
      = (P : Subgroup (C.subgroupOf M)).map (M.subtype.comp (C.subgroupOf M).subtype) := by
        rw [Subgroup.map_map]
    _ = ((Q : Subgroup C).map e.toMonoidHom).map
          (M.subtype.comp (C.subgroupOf M).subtype) := by rw [hPcoe]
    _ = (Q : Subgroup C).map
          ((M.subtype.comp (C.subgroupOf M).subtype).comp e.toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = (Q : Subgroup C).map C.subtype := by rw [hcomp]

private theorem P1_sup_i2_sup_h1_le [Finite G] :
    D.P1 ⊔ D.i2.range ⊔ zpowers D.h1 ≤ D.i2.range ⊔ D.V ⊔ zpowers D.h1 := by
  refine sup_le ?_ le_sup_right
  refine sup_le ?_ ?_
  · exact (D.P1_le_V.trans (le_sup_right : D.V ≤ D.i2.range ⊔ D.V)).trans le_sup_left
  · exact (le_sup_left : D.i2.range ≤ D.i2.range ⊔ D.V).trans le_sup_left

private theorem normalizer_P1_eq [Finite G] :
    normalizer (D.P1 : Set G) = D.i2.range ⊔ D.V ⊔ zpowers D.h1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer (D.P1 : Set G)
  let M : Subgroup G := normalizer (D.P1 : Set G)
  let R : Subgroup G := D.i2.range ⊔ D.V ⊔ zpowers D.h1
  have hCM : C ≤ M := Subgroup.centralizer_le_normalizer (D.P1 : Set G)
  have hRM : R ≤ M :=
    sup_le (sup_le (D.i2_range_le_centralizer_P1.trans hCM)
      (D.V_le_centralizer.trans hCM)) (zpowers_le.mpr D.h1_mem_normalizer_P1)
  refine le_antisymm ?_ hRM
  intro g hg
  obtain ⟨T, -, htT, hsylC, hchar, -, -⟩ := D.exists_sylow_centralizer_P1
  have hTC : T ≤ C := hsylC.le
  obtain ⟨Q, hQ⟩ := hsylC.exists_sylow_eq_subgroupOf
  let NM : Subgroup M := C.subgroupOf M
  have hNMnormal : NM.Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (D.P1 : Set G)
  haveI : NM.Normal := hNMnormal
  obtain ⟨P, hPmapQ⟩ := exists_sylow_normalizer_map hCM Q
  have hPmap : ((P : Subgroup NM).map NM.subtype : Subgroup M).map M.subtype = T := by
    rw [hPmapQ, hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTC]
  have hmem : (⟨g, hg⟩ : M) ∈ normalizer ((P : Subgroup NM).map NM.subtype : Set M) ⊔ NM := by
    rw [Sylow.normalizer_sup_eq_top P]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_right] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have haT : (a : G) ∈ normalizer (T : Set G) := by
    have hle : (normalizer ((P : Subgroup NM).map NM.subtype : Set M)).map M.subtype ≤
        normalizer (T : Set G) := by
      rw [← hPmap]
      exact Subgroup.le_normalizer_map (f := M.subtype)
    exact hle ⟨a, ha, rfl⟩
  have haCt : (a : G) ∈ centralizer ({D.t} : Set G) :=
    normalizer_le_centralizer_of_characteristic D.orderOf_t htT hchar haT
  have haPL : (a : G) ∈ D.P1 ⊔ D.i2.range ⊔ zpowers D.h1 := by
    have : (a : G) ∈ M ⊓ centralizer ({D.t} : Set G) := ⟨a.2, haCt⟩
    rwa [D.normalizer_P1_inf_centralizer_t] at this
  have hbC : (b : G) ∈ C := Subgroup.mem_subgroupOf.mp hb
  have hbVL : (b : G) ∈ D.i2.range ⊔ D.V := by
    rw [← D.centralizer_P1_eq_i2_sup_V]
    exact hbC
  have hAR := P1_sup_i2_sup_h1_le (D := D)
  have hBR : D.i2.range ⊔ D.V ≤ R := le_sup_left
  rw [show g = (a : G) * (b : G) from (congrArg Subtype.val hab).symm]
  exact mul_mem (hAR haPL) (hBR hbVL)

theorem first_root_centralizer_odd_core [Finite G] :
    centralizer (D.P1 : Set G) = D.i2.range ⊔ D.V ∧ D.i2.range ⊓ D.V = ⊥ ∧
    normalizer (D.P1 : Set G) = D.i2.range ⊔ D.V ⊔ zpowers D.h1 ∧
    D.P1 ≤ D.V ∧ (∀ x ∈ D.P1, ∀ x' ∈ D.V, Commute x x') ∧
    ⁅D.V, D.V⁆ ≤ D.P1 ∧ D.Q ⊓ D.V = D.P1 ⊔ D.P3 := by
  refine ⟨D.centralizer_P1_eq_i2_sup_V, D.i2_inf_V_eq_bot, D.normalizer_P1_eq,
    D.P1_le_V, ?_, D.commutator_V_le_P1, D.Q_inf_V_eq⟩
  intro x hx x' hx'
  exact mem_centralizer_iff.mp (D.V_le_centralizer hx') x hx

end CFSG.OddTranspositions.PartThree.Wong.RootData
