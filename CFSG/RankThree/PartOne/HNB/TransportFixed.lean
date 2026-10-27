module

public import CFSG.RankThree.PartOne.HNB.TransportInner
import CFSG.RankThree.PartOne.KS.Lines
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement
public import CFSG.RankThree.PartOne.S11c.HNProps

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne.HNRed (fixedSubgroup FiveFixedPSU3)
open scoped Pointwise commutatorElement

namespace Actor

variable {G : Type} [Group G] {A L : Subgroup G} (a : Actor G A L)

theorem YH_le_KH : a.YH ≤ a.KH := fun _ hg =>
  Subgroup.mem_subgroupOf.mpr (a.N.hYK (Subgroup.mem_subgroupOf.mp hg))

end Actor

namespace Successor

variable {G : Type} [Group G] {A L : Subgroup G} {a : Actor G A L} (s : Successor a)

abbrev V : Type := ↥s.X ⧸ Subgroup.center ↥s.X

abbrev q : s.X →* s.V := QuotientGroup.mk' (Subgroup.center ↥s.X)

theorem mem_bar_iff {S : Subgroup a.H} {v : s.V} :
    v ∈ s.bar S ↔ ∃ x : s.X, (x : a.H) ∈ S ∧ s.q x = v := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem YH_le_X : a.YH ≤ s.X := fun _ hg => s.hKX (a.YH_le_KH hg)

theorem bar_YH_le_bar_KH : s.bar a.YH ≤ s.bar a.KH :=
  Subgroup.map_mono (fun _ hg => a.YH_le_KH hg)

theorem KH_inf_center {x : s.X} (hx : x ∈ a.KH.subgroupOf s.X)
    (hxc : x ∈ Subgroup.center ↥s.X) : x = 1 := by
  have : IsSimpleGroup a.K := a.N.hKsimple
  have hxK : ((x : a.H) : G) ∈ a.K := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
  have hcen : (⟨((x : a.H) : G), hxK⟩ : a.K) ∈ Subgroup.center a.K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hkX : (⟨⟨(k : G), a.K_le_H k.2⟩, s.hKX (Subgroup.mem_subgroupOf.mpr k.2)⟩ : s.X) * x =
        x * ⟨⟨(k : G), a.K_le_H k.2⟩, s.hKX (Subgroup.mem_subgroupOf.mpr k.2)⟩ :=
      Subgroup.mem_center_iff.mp hxc _
    exact congrArg (fun z : s.X => ((z : a.H) : G)) hkX
  rw [SteinbergBM.center_eq_bot_of_isSimpleGroup a.N.hKnonab, Subgroup.mem_bot] at hcen
  have h1 : ((x : a.H) : G) = 1 := congrArg (fun z : a.K => (z : G)) hcen
  exact Subtype.ext (Subtype.ext h1)

theorem subgroupMap_q_injective (T : Subgroup a.H)
    (hT : ∀ x ∈ T.subgroupOf s.X, x ∈ Subgroup.center ↥s.X → x = 1) :
    Function.Injective ((s.q).subgroupMap (T.subgroupOf s.X)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : s.q (x : s.X) = 1 := congrArg Subtype.val hx
  have hc : (x : s.X) ∈ Subgroup.center ↥s.X := by
    rw [← QuotientGroup.eq_one_iff]
    exact h1
  rw [Subgroup.mem_bot]
  exact Subtype.ext (hT x x.2 hc)

noncomputable def barEquiv (T : Subgroup a.H)
    (hT : ∀ x ∈ T.subgroupOf s.X, x ∈ Subgroup.center ↥s.X → x = 1) :
    T.subgroupOf s.X ≃* s.bar T :=
  MulEquiv.ofBijective ((s.q).subgroupMap (T.subgroupOf s.X))
    ⟨s.subgroupMap_q_injective T hT, (s.q).subgroupMap_surjective _⟩

theorem KH_inj : ∀ x ∈ a.KH.subgroupOf s.X, x ∈ Subgroup.center ↥s.X → x = 1 :=
  fun _ hx hxc => s.KH_inf_center hx hxc

theorem YH_inj : ∀ x ∈ a.YH.subgroupOf s.X, x ∈ Subgroup.center ↥s.X → x = 1 :=
  fun _ hx hxc => s.KH_inf_center
    (Subgroup.mem_subgroupOf.mpr (a.YH_le_KH (Subgroup.mem_subgroupOf.mp hx))) hxc

noncomputable def eK : s.bar a.KH ≃* a.K :=
  (s.barEquiv a.KH s.KH_inj).symm.trans
    ((Subgroup.subgroupOfEquivOfLe s.hKX).trans (Subgroup.subgroupOfEquivOfLe a.K_le_H))

noncomputable def eY : s.bar a.YH ≃* a.Y :=
  (s.barEquiv a.YH s.YH_inj).symm.trans
    ((Subgroup.subgroupOfEquivOfLe s.YH_le_X).trans (Subgroup.subgroupOfEquivOfLe a.Y_le_H))

@[expose] def CX : Subgroup s.X :=
  (Subgroup.centralizer ({a.cH} : Set a.H)).comap s.X.subtype

theorem mem_CX_iff {y : s.X} : y ∈ s.CX ↔ (y : a.H) * a.cH = a.cH * (y : a.H) :=
  Subgroup.mem_centralizer_singleton_iff

theorem psi_coe [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) (x : s.X) :
    ((s.X.normalizerMonoidHom (s.cN h) x : s.X) : a.H) = a.cH * (x : a.H) * a.cH⁻¹ :=
  coe_normalizerMonoidHom_apply (s.cN h) x

theorem psi_eq_self_iff [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) (x : s.X) :
    s.X.normalizerMonoidHom (s.cN h) x = x ↔ x ∈ s.CX := by
  rw [mem_CX_iff, Subtype.ext_iff, psi_coe, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem beta_q [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) (x : s.X) :
    s.beta h (s.q x) = s.q (s.X.normalizerMonoidHom (s.cN h) x) := rfl

theorem bar_KH_le_fixed [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    s.bar a.KH ≤ fixedSubgroup (s.beta h) := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := (s.mem_bar_iff).mp hv
  show s.beta h (s.q x) = s.q x
  rw [s.beta_q h, (s.psi_eq_self_iff h x).mpr (a.KH_le_centralizer_cH hx)]

@[expose] noncomputable def P [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) : Subgroup s.X :=
  (fixedSubgroup (s.beta h)).comap s.q

theorem CX_le_P [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) : s.CX ≤ s.P h := by
  intro y hy
  show s.beta h (s.q y) = s.q y
  rw [s.beta_q h, (s.psi_eq_self_iff h y).mpr hy]

theorem conj_mem_CX [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) {x y : s.X}
    (hx : x ∈ s.P h) (hy : y ∈ s.CX) : x * y * x⁻¹ ∈ s.CX := by
  have hy' : s.X.normalizerMonoidHom (s.cN h) y = y := (s.psi_eq_self_iff h y).mpr hy
  have hxq : s.q (s.X.normalizerMonoidHom (s.cN h) x) = s.q x := hx
  have hz : x⁻¹ * s.X.normalizerMonoidHom (s.cN h) x ∈ Subgroup.center ↥s.X :=
    QuotientGroup.eq.mp hxq.symm
  have hψx : s.X.normalizerMonoidHom (s.cN h) x =
      x * (x⁻¹ * s.X.normalizerMonoidHom (s.cN h) x) := by group
  have hzy : (x⁻¹ * s.X.normalizerMonoidHom (s.cN h) x) * y =
      y * (x⁻¹ * s.X.normalizerMonoidHom (s.cN h) x) := (Subgroup.mem_center_iff.mp hz y).symm
  rw [← s.psi_eq_self_iff h, map_mul, map_mul, map_inv, hy']
  generalize x⁻¹ * s.X.normalizerMonoidHom (s.cN h) x = z at hψx hzy
  rw [hψx]
  calc x * z * y * (x * z)⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ := by rw [hzy]
    _ = x * y * x⁻¹ := by group

theorem CX_subgroupOf_P_normal [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    (s.CX.subgroupOf (s.P h)).Normal :=
  ⟨fun _ hn g => s.conj_mem_CX h g.2 hn⟩

theorem KH_subnormal_CX [Finite G] :
    ((a.KH.subgroupOf s.X).subgroupOf s.CX).IsSubnormal := by
  have h1 := isSubnormal_of_mem_thetaComponentsAt a.KH_mem_thetaComponentsAt
  have h2 := h1.comap (s.X.subtype.subgroupComap (Subgroup.centralizer ({a.cH} : Set a.H)))
  have e : (a.KH.subgroupOf s.X).subgroupOf s.CX =
      Subgroup.comap (s.X.subtype.subgroupComap (Subgroup.centralizer ({a.cH} : Set a.H)))
        (a.KH.subgroupOf (Subgroup.centralizer ({a.cH} : Set a.H))) :=
    Subgroup.ext fun _ => Iff.rfl
  rw [e]
  exact h2

theorem KH_subnormal_P [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    ((a.KH.subgroupOf s.X).subgroupOf (s.P h)).IsSubnormal := by
  have hKC : (a.KH.subgroupOf s.X).subgroupOf (s.P h) ≤ s.CX.subgroupOf (s.P h) :=
    fun _ hx => a.KH_le_centralizer_cH hx
  have hsub : (((a.KH.subgroupOf s.X).subgroupOf (s.P h)).subgroupOf
      (s.CX.subgroupOf (s.P h))).IsSubnormal := by
    have h2 := s.KH_subnormal_CX.comap ((s.P h).subtype.subgroupComap s.CX)
    have e : ((a.KH.subgroupOf s.X).subgroupOf (s.P h)).subgroupOf (s.CX.subgroupOf (s.P h)) =
        Subgroup.comap ((s.P h).subtype.subgroupComap s.CX)
          ((a.KH.subgroupOf s.X).subgroupOf s.CX) := Subgroup.ext fun _ => Iff.rfl
    rw [e]
    exact h2
  exact Subgroup.IsSubnormal.trans hKC hsub (s.CX_subgroupOf_P_normal h).isSubnormal

noncomputable abbrev piP [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    ↥(s.P h) →* ↥(fixedSubgroup (s.beta h)) :=
  s.q.subgroupComap (fixedSubgroup (s.beta h))

theorem piP_surjective [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    Function.Surjective (s.piP h) :=
  MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective _)

theorem map_piP_eq [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    ((a.KH.subgroupOf s.X).subgroupOf (s.P h)).map (s.piP h) =
      (s.bar a.KH).subgroupOf (fixedSubgroup (s.beta h)) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (s.mem_bar_iff).mpr ⟨(x : s.X), hx, rfl⟩
  · intro hw
    obtain ⟨y, hy, hyq⟩ := (s.mem_bar_iff).mp hw
    have hyP : y ∈ s.P h := s.CX_le_P h (a.KH_le_centralizer_cH hy)
    exact ⟨⟨y, hyP⟩, hy, Subtype.ext hyq⟩

theorem bar_KH_subnormal [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    ((s.bar a.KH).subgroupOf (fixedSubgroup (s.beta h))).IsSubnormal := by
  rw [← s.map_piP_eq h]
  exact Subgroup.IsSubnormal.map (s.piP_surjective h) (s.KH_subnormal_P h)

theorem isComponent_bar_KH [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    CFSG.IsComponent ((s.bar a.KH).subgroupOf (fixedSubgroup (s.beta h))) := by
  refine ⟨?_, s.bar_KH_subnormal h⟩
  have : IsSimpleGroup a.K := a.N.hKsimple
  have hqK : CFSG.IsQuasisimple a.K := isQuasisimple_of_isSimpleGroup a.N.hKnonab
  exact LocalCores.isQuasisimple_of_mulEquiv
    (s.eK.symm.trans (Subgroup.subgroupOfEquivOfLe (s.bar_KH_le_fixed h)).symm) hqK

theorem fiveFixedPSU3 [Finite G] (hbridge : BridgeHyp) (hK : CatalogPrimeTwoAutomorphismsInner)
    (h : SteinbergBM.SectionTenSetup G 5 A) : FiveFixedPSU3 (s.beta h) (s.bar a.KH) :=
  ⟨s.orderOf_beta h (s.isQuasisimple_X hbridge hK h),
    ⟨s.bar_KH_le_fixed h, s.isComponent_bar_KH h⟩,
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv s.eK a.N.hKmodel⟩

theorem nonempty_bar_YH_equiv_sl2 :
    Nonempty (s.bar a.YH ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  obtain ⟨σ⟩ := a.N.hYsl
  exact ⟨s.eY.trans σ⟩

end Successor

end CFSG.RankThree.PartOne.HNB
