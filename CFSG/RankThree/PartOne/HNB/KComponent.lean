module

public import CFSG.RankThree.PartOne.HNB.TwoCore
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.KS.Lines
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped Pointwise

theorem mem_thetaComponents_of_simple {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {S : Subgroup H} (hs : IsSimpleGroup S) (hn : ∃ a b : S, a * b ≠ b * a)
    (hsn : S.IsSubnormal) : S ∈ thetaComponents p H := by
  have hq : IsQuasisimple S := isQuasisimple_of_isSimpleGroup hn
  refine ⟨hq.1, hsn, ?_⟩
  have hθ : aschbacherSolvableCore p S = ⊥ :=
    SteinbergBM.eq_bot_of_normal_of_isSolvable_of_isSimpleGroup hn _
      (solvable_prime_complement_core_characterization hp).1
  have e : (S ⧸ aschbacherSolvableCore p S) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot
  exact LocalCores.isQuasisimple_of_mulEquiv e.symm hq

namespace Actor

variable {G : Type} [Group G] {A L : Subgroup G} (a : Actor G A L)

abbrev H : Subgroup G := Subgroup.centralizer ({a.b} : Set G)

abbrev P : Subgroup G := a.H ⊓ Subgroup.centralizer ({a.c} : Set G)

theorem A0_le_H : a.A0 ≤ a.H := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr (a.commute_b_of_mem_A0 hg)

theorem K_le_H : a.K ≤ a.H := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr (a.commute_b_of_mem_K hg)

theorem Y_le_H : a.Y ≤ a.H := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr (a.commute_b_of_mem_Y hg)

theorem R_le_H : a.R ≤ a.H := a.R_le_centralizer_b

theorem U_le_H : a.U ≤ a.H := inf_le_right

theorem c_mem_H : a.c ∈ a.H := a.A0_le_H a.c_mem_A0

theorem commute_x_of_commute_b_c [Finite G] {g : G} (hb : g * a.b = a.b * g)
    (hc : g * a.c = a.c * g) : g * a.x = a.x * g := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers a.c)
    (Subgroup.zpowers a.x)
    ((a.zpowers_c_le_centralizer_zpowers_x).trans (Subgroup.centralizer_le_normalizer _))
  have hb' : a.b ∈ ((Subgroup.zpowers a.c : Subgroup G) : Set G) *
      (Subgroup.zpowers a.x : Set G) := by
    rw [← hset]
    exact a.hbB
  obtain ⟨c', hc', x', hx', hbx⟩ := hb'
  change c' * x' = a.b at hbx
  have hx'1 : x' ≠ 1 := by
    intro h1
    apply a.hbc
    rw [h1, mul_one] at hbx
    exact hbx ▸ hc'
  have hc'g : g * c' = c' * g := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    exact (Commute.zpow_right (show Commute g a.c from hc) n).eq
  have hx'g : g * x' = x' * g := by
    have : x' = c'⁻¹ * a.b := by rw [← hbx]; group
    rw [this]
    calc g * (c'⁻¹ * a.b) = (g * c'⁻¹) * a.b := by group
      _ = (c'⁻¹ * g) * a.b := by
        rw [show g * c'⁻¹ = c'⁻¹ * g from (Commute.inv_right (show Commute g c' from hc'g)).eq]
      _ = c'⁻¹ * (g * a.b) := by group
      _ = c'⁻¹ * (a.b * g) := by rw [hb]
      _ = (c'⁻¹ * a.b) * g := by group
  have hxx : a.x ∈ Subgroup.zpowers x' := mem_zpowers_of_mem_zpowers_prime a.N.hx5 hx' hx'1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxx
  rw [← hn]
  exact (Commute.zpow_right (show Commute g x' from hx'g) n).eq

theorem P_inf_L_le_normalizer_K [Finite G] : a.P ⊓ L ≤ Subgroup.normalizer (a.K : Set G) := fun _ hg =>
  a.N.hKnorm ⟨hg.2, Subgroup.mem_centralizer_singleton_iff.mpr
    (a.commute_x_of_commute_b_c (Subgroup.mem_centralizer_singleton_iff.mp hg.1.1)
      (Subgroup.mem_centralizer_singleton_iff.mp hg.1.2))⟩

theorem K_subnormal_P [Finite G] : (a.K.subgroupOf a.P).IsSubnormal := by
  have hLc : (L.subgroupOf (Subgroup.centralizer ({a.c} : Set G))).IsSubnormal :=
    isSubnormal_of_mem_thetaComponentsAt a.hLθ
  have hPC : a.P ≤ Subgroup.centralizer ({a.c} : Set G) := inf_le_right
  have hLP : (L.subgroupOf a.P).IsSubnormal := by
    have := hLc.comap (Subgroup.inclusion hPC)
    have e : L.subgroupOf a.P =
        Subgroup.comap (Subgroup.inclusion hPC)
          (L.subgroupOf (Subgroup.centralizer ({a.c} : Set G))) :=
      Subgroup.ext fun _ => Iff.rfl
    rw [e]
    exact this
  have hKL : a.K.subgroupOf a.P ≤ L.subgroupOf a.P := fun g hg => a.K_le_L hg
  have hnorm : (L.subgroupOf a.P) ≤ Subgroup.normalizer ((a.K.subgroupOf a.P : Subgroup a.P) : Set a.P) := by
    intro g hg
    have : (g : G) ∈ Subgroup.normalizer (a.K : Set G) := a.P_inf_L_le_normalizer_K ⟨g.2, hg⟩
    rw [Subgroup.mem_normalizer_iff] at this ⊢
    intro k
    have := this (k : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hKnormal : ((a.K.subgroupOf a.P).subgroupOf (L.subgroupOf a.P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr hnorm
  exact Subgroup.IsSubnormal.trans hKL hKnormal.isSubnormal hLP

@[expose] def cH : a.H := ⟨a.c, a.c_mem_H⟩

@[expose] def bH : a.H := ⟨a.b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem orderOf_cH : orderOf a.cH = 5 := by
  rw [cH, Subgroup.orderOf_mk]
  exact a.hc5

theorem KH_le_centralizer_cH :
    a.K.subgroupOf a.H ≤ Subgroup.centralizer ({a.cH} : Set a.H) := fun k hk => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (a.commute_c_of_mem_K hk)

theorem KH_mem_thetaComponentsAt [Finite G] : a.K.subgroupOf a.H ∈ thetaComponentsAt 5 a.cH := by
  have hp : Nat.Prime 5 := by norm_num
  have hsimple : IsSimpleGroup a.K := a.N.hKsimple
  set C : Subgroup a.H := Subgroup.centralizer ({a.cH} : Set a.H) with hC
  have e : (a.K.subgroupOf a.H).subgroupOf C ≃* a.K :=
    (Subgroup.subgroupOfEquivOfLe a.KH_le_centralizer_cH).trans
      (Subgroup.subgroupOfEquivOfLe a.K_le_H)
  refine mem_thetaComponentsAt_iff.mpr ⟨a.KH_le_centralizer_cH, ?_⟩
  have hs : IsSimpleGroup ((a.K.subgroupOf a.H).subgroupOf C) := e.isSimpleGroup_congr.mpr hsimple
  have hn : ∃ x y : (a.K.subgroupOf a.H).subgroupOf C, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := a.N.hKnonab
    exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  let φ : C →* a.P :=
    MonoidHom.codRestrict ((a.H.subtype).comp C.subtype) a.P fun g =>
      ⟨g.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2))⟩
  have hsn : ((a.K.subgroupOf a.H).subgroupOf C).IsSubnormal := by
    have := a.K_subnormal_P.comap φ
    have e2 : (a.K.subgroupOf a.H).subgroupOf C = Subgroup.comap φ (a.K.subgroupOf a.P) :=
      Subgroup.ext fun _ => Iff.rfl
    rw [e2]
    exact this
  exact mem_thetaComponents_of_simple hp hs hn hsn

end Actor

end CFSG.RankThree.PartOne.HNB
