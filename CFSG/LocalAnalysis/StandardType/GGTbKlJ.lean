module

import CFSG.LocalAnalysis.StandardType.GGTbKlLayer
import CFSG.LocalAnalysis.StandardType.GGTbKlLabel
import CFSG.LocalAnalysis.StandardType.GGTbKlTransport
public import CFSG.LocalAnalysis.StandardType.GGTbKlSetup
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTbKlWeight
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalType

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
open CFSG.RankThree.PartOne.KCOrthogonal


private theorem tbklj_hasLabel_of_mulEquiv {lab : LargeEvenLabel} {R S : Type} [Group R] [Group S]
    (e : R ≃* S) (h : GGHasLabel lab R) : GGHasLabel lab S := by
  unfold GGHasLabel at h ⊢
  refine largeEvenRawDatum_mono ?_ h
  rintro R' _ I F ⟨θ⟩
  exact ⟨e.symm.trans θ⟩

private theorem tbklj_map_zpowers {G H : Type} [Group G] [Group H] {L : Subgroup G} (ψ : ↥L ≃* H)
    {z : G} (hzL : z ∈ L) :
    ((Subgroup.zpowers z).subgroupOf L).map ψ.toMonoidHom = Subgroup.zpowers (ψ ⟨z, hzL⟩) := by
  ext h
  rw [Subgroup.mem_map, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨n, ?_⟩
    have : (⟨z, hzL⟩ : ↥L) ^ n = g := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn)
    rw [← this]
    exact (map_zpow ψ _ n).symm
  · rintro ⟨n, rfl⟩
    refine ⟨(⟨z, hzL⟩ : ↥L) ^ n, ?_, map_zpow ψ _ n⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers z n

private theorem tbklj_centralizer_zpowers {H : Type} [Group H] (t : H) :
    Subgroup.centralizer ((Subgroup.zpowers t : Subgroup H) : Set H) =
      Subgroup.centralizer ({t} : Set H) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · intro h
    exact h t (Subgroup.mem_zpowers t)
  · intro h s hs
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact ((Commute.zpow_left (show Commute t g from h) n).eq)

private theorem tbklj_inf_centralizer {G : Type} [Group G] {L D : Subgroup G} {x y z : G} {k : ℤ}
    (hD : D = Subgroup.closure {x, y}) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hyz : y = x ^ k * z) (hzD : z ∈ D) :
    L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  ext l
  simp only [Subgroup.mem_inf]
  refine and_congr_right fun hl => ?_
  constructor
  · intro h
    exact Subgroup.centralizer_le (fun a ha => Subgroup.zpowers_le.mpr hzD ha) h
  · intro h
    have hxl : Commute x l := Subgroup.mem_centralizer_iff.mp (hLx hl) x rfl
    have hzl : Commute z l := Subgroup.mem_centralizer_iff.mp h z (Subgroup.mem_zpowers z)
    have hyl : Commute y l := by
      rw [hyz]
      exact (hxl.zpow_left k).mul_left hzl
    have hDle : D ≤ Subgroup.centralizer ({l} : Set G) := by
      rw [hD, Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxl.eq
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using hyl.eq)
    exact Subgroup.mem_centralizer_iff.mpr fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.mp (hDle hd)


theorem ggF4QTwoOmegaEnd_label_J
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hIL : GGInnerDiagOn Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr 3 B x D J y K)
    (hL : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    GGHasLabel ⟨.A, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J) ∧ Subgroup.center J = ⊥ := by
  obtain ⟨ψ, z, hzL, k, u, hzD, hyz, hyx, hxL, hxD, hDcard, hψz, htor, hJL, hJD, hJJ, hJbot, hCJ,
    hLx, hJeq⟩ := ggF4QTwoOmegaEnd_setup hC hIL hNb hL
  have hw : Two.weight u = 1 :=
    two_weight_eq_one_of_end_setup ψ hzL hψz htor hyz hyx hxL hxD hzD hDcard hJL hJD hJJ hJbot hCJ
  have hJeq' : J =
      LargeEvenLayer (L ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)) := by
    rw [hJeq, tbklj_inf_centralizer hNb.2.1 hLx hyz hzD]
  obtain ⟨e4⟩ := nonempty_mulEquiv_largeEvenLayer_inf_centralizer ψ
    (Subgroup.zpowers_le.mpr hzL)
  rw [tbklj_map_zpowers ψ hzL, tbklj_centralizer_zpowers (ψ ⟨z, hzL⟩)] at e4
  have htor' : ((ψ ⟨z, hzL⟩ : ↥Two.omega) : Two.Aut) = Two.tor u := hψz
  have hQ : (QuadraticMap.polarBilin (modelForm (1 : ZMod 2) 1)).Nondegenerate :=
    nondegenerate_polarBilin_modelForm (by decide) (by decide)
  have hV : 8 ≤ Module.finrank (ZMod 2) (ModelSpace (ZMod 2)) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_prod]
    simp
  have ht2 : Module.finrank (ZMod 2)
      (CFSG.RankThree.PartOne.LIT.commSpace ((ψ ⟨z, hzL⟩ : ↥Two.omega) : Two.Aut)) = 2 := by
    rw [htor']
    exact finrank_commSpace_twoTor_of_weight_eq_one hw
  have ht1 : (ψ ⟨z, hzL⟩ : ↥Two.omega) ≠ 1 := by
    intro h
    have h0 : CFSG.RankThree.PartOne.LIT.commSpace
        (((ψ ⟨z, hzL⟩ : ↥Two.omega) : Two.Aut)) = ⊥ := by
      rw [h, Submodule.eq_bot_iff]
      intro w hw
      obtain ⟨y, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hw
      simp
    rw [h0, finrank_bot] at ht2
    exact absurd ht2 (by norm_num)
  have htp : (ψ ⟨z, hzL⟩ : ↥Two.omega) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, htor', Subgroup.coe_one]
    show (cm (ZMod 2) (Multiplicative.ofAdd u)) ^ 3 = 1
    rw [← map_pow]
    have h3 : (Multiplicative.ofAdd u) ^ 3 = 1 := by
      rw [← ofAdd_nsmul]
      have : (3 : ℕ) • u = 0 := by
        funext i
        exact (by decide : ∀ a : ZMod 3, 3 • a = 0) (u i)
      rw [this]
      rfl
    rw [h3, map_one]
  have hS1 := OrthRestOdd.largeEvenLayer_centralizer_eq_of_commSpace_two
    (Q := modelForm (1 : ZMod 2) 1) hQ hV Nat.prime_three (by norm_num)
    (by decide)
    (t := (ψ ⟨z, hzL⟩ :
      ↥(CFSG.RankThree.Classical2.orthDerived (modelForm (1 : ZMod 2) 1)))) ht1 htp ht2
  have hS1' : LargeEvenLayer
      (Subgroup.centralizer ({(ψ ⟨z, hzL⟩ : ↥Two.omega)} : Set ↥Two.omega)) =
        (supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u)).subgroupOf Two.omega := by
    rw [← htor']
    exact hS1
  have hx : OddOrderIsometry (modelForm (1 : ZMod 2) 1) 3 (Two.tor u) := by
    rw [← htor']
    exact ⟨orthDerived_le_orthogonalGroup (ψ ⟨z, hzL⟩).2, congrArg Subtype.val htp, by decide,
      fun v hv => hQ.1 v fun w => by rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hEΩ : supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u) ≤ Two.omega :=
    hx.supportedFixedDerived_le_orthDerived
  have hS3 := hasLabel_supportedFixedDerived_twoTor_of_weight_eq_one hw
  let e : ↥J ≃* ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u)) :=
    (MulEquiv.subgroupCongr hJeq').trans
      (e4.trans ((MulEquiv.subgroupCongr hS1').trans (Subgroup.subgroupOfEquivOfLe hEΩ)))
  have hZ : Subgroup.center ↥J = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hg' : e g ∈ Subgroup.center ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1)
        (Two.tor u)) := by
      rw [Subgroup.mem_center_iff] at hg ⊢
      intro w
      obtain ⟨a, rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, hg a]
    rw [hS3.2, Subgroup.mem_bot] at hg'
    exact e.injective (by simpa using hg')
  refine ⟨?_, hZ⟩
  have hq : (↥J ⧸ Subgroup.center ↥J) ≃*
      (↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u)) ⧸
        Subgroup.center ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u))) :=
    QuotientGroup.congr _ _ e (by rw [hZ, hS3.2, Subgroup.map_bot])
  exact tbklj_hasLabel_of_mulEquiv hq.symm hS3.1

end CFSG.StandardType

end
