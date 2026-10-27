module

public import CFSG.LocalAnalysis.StandardType.N2PlaneFinite
public import CFSG.RepresentationTheory.GF2.FiveSquaredGroup
import CFSG.GroupTheory.PrimeOrderSubgroups
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Tactic.Group
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate10090
public import Certificates.Certificate10090Base
public import Certificates.Certificate1021
public import Certificates.Certificate16041
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2309
public import Certificates.Certificate2311
public import Certificates.Certificate2313
public import Certificates.Certificate2314
public import Certificates.Certificate2315
public import Certificates.Certificate2317
public import Certificates.Certificate2323
public import Certificates.Certificate2324
public import Certificates.Certificate2325
public import Certificates.Certificate3085
public import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType.N2Plane

open CFSG.RepresentationTheory.GF2 CFSG.GroupTheory
open CFSG.RankThree.PartOne.HNRed

theorem plane_bad_reflection_dichotomy {G : Type} [Group G] {y u γ : G}
    (hy : orderOf y = 5) (hu : orderOf u = 5) (hyu : Commute y u)
    (hyu' : y ∉ Subgroup.zpowers u)
    (hγ : ∀ d ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers u,
      γ * d * γ⁻¹ ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers u)
    (hγ2 : ∀ d ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers u,
      γ ^ 2 * d * (γ ^ 2)⁻¹ = d)
    (hγ1 : ∃ d ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers u, γ * d * γ⁻¹ ≠ d)
    (hbad : γ * (y * u ^ 2) * γ⁻¹ = y * u ^ 2 ∨
      γ * (y * u ^ 3) * γ⁻¹ = y * u ^ 3) :
    (∃ e ∈ ({y, u} : Set G), ∃ f ∈ ({y * u, y * u ^ 4} : Set G),
      Subgroup.zpowers (γ * e * γ⁻¹) = Subgroup.zpowers f) ∨
    (γ * y * γ⁻¹ = u ^ 2 ∧ γ * u * γ⁻¹ = y ^ 3) ∨
    (γ * y * γ⁻¹ = u ^ 3 ∧ γ * u * γ⁻¹ = y ^ 2) := by
  classical
  have hv1 : (1 : ZMod 5).val = 1 := by decide +kernel
  have hv2 : (2 : ZMod 5).val = 2 := by decide +kernel
  have hv3 : (3 : ZMod 5).val = 3 := by decide +kernel
  have hv4 : (4 : ZMod 5).val = 4 := by decide +kernel
  have hyp : y ^ 5 = 1 := by simpa [hy] using pow_orderOf_eq_one y
  have hup : u ^ 5 = 1 := by simpa [hu] using pow_orderOf_eq_one u
  have hy1 : y ≠ 1 := by intro h; simp [h] at hy
  have hu1 : u ≠ 1 := by intro h; simp [h] at hu
  have hne : Subgroup.zpowers y ≠ Subgroup.zpowers u := by
    intro h
    exact hyu' (h ▸ Subgroup.mem_zpowers y)
  have hdis : Disjoint (Subgroup.zpowers y) (Subgroup.zpowers u) :=
    disjoint_of_card_eq_prime_of_ne Nat.prime_five
      (by rw [Nat.card_zpowers, hy]) (by rw [Nat.card_zpowers, hu]) hne
  have hunot : u ∉ Subgroup.zpowers y := by
    intro h
    have hm : u ∈ Subgroup.zpowers y ⊓ Subgroup.zpowers u := ⟨h, Subgroup.mem_zpowers u⟩
    rw [disjoint_iff.mp hdis, Subgroup.mem_bot] at hm
    exact hu1 hm
  have hno : ∀ i : ℕ, u ≠ y ^ i := by
    intro i h
    exact hunot (h ▸ (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) i))
  let E := fiveSqSubgroup y u hyp hup hyu.eq
  have hE : E = Subgroup.zpowers y ⊔ Subgroup.zpowers u := by
    apply le_antisymm
    · intro d hd
      obtain ⟨a, rfl⟩ := mem_fiveSqSubgroup_iff.mp hd
      exact Subgroup.mul_mem _
        ((le_sup_left : Subgroup.zpowers y ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers u)
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) a.1.val))
        ((le_sup_right : Subgroup.zpowers u ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers u)
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) a.2.val))
    · exact sup_le (Subgroup.zpowers_le.mpr mem_fiveSqSubgroup_left)
        (Subgroup.zpowers_le.mpr mem_fiveSqSubgroup_right)
  let e : Multiplicative Vec ≃* E :=
    (AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow (ZMod 5) (ZMod 5)).toAddEquiv).trans
      (fiveSqEquiv hyp hy1 hup hyu.eq hno)
  let ev : Multiplicative Vec →* G := E.subtype.comp e.toMonoidHom
  have hevinj : Function.Injective ev := E.subtype_injective.comp e.injective
  have hev (v : Vec) : ev (Multiplicative.ofAdd v) = y ^ (v 0).val * u ^ (v 1).val := by
    rfl
  have hmem (v : Vec) : ev (Multiplicative.ofAdd v) ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers u :=
    hE.le (e (Multiplicative.ofAdd v)).2
  let a : ↥E →* ↥E := {
    toFun := fun d => ⟨γ * (d : G) * γ⁻¹, hE.ge (hγ d (hE.le d.2))⟩
    map_one' := by
      apply Subtype.ext
      change γ * 1 * γ⁻¹ = 1
      group
    map_mul' := by
      intro d q
      apply Subtype.ext
      change γ * ((d : G) * (q : G)) * γ⁻¹ =
        (γ * (d : G) * γ⁻¹) * (γ * (q : G) * γ⁻¹)
      group }
  let b : Multiplicative Vec →* Multiplicative Vec :=
    e.symm.toMonoidHom.comp (a.comp e.toMonoidHom)
  let f : Vec →+ Vec := {
    toFun := fun v => Multiplicative.toAdd (b (Multiplicative.ofAdd v))
    map_zero' := by
      change Multiplicative.toAdd (b 1) = 0
      rw [map_one]
      rfl
    map_add' := by
      intro v w
      exact congrArg Multiplicative.toAdd
        (b.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  let F : Vec →ₗ[ZMod 5] Vec := { f with
    map_smul' := by
      intro c v
      change f (c • v) = c • f v
      rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul (ZMod 5),
        Nat.cast_smul_eq_nsmul (ZMod 5)]
      exact f.map_nsmul c.val v }
  let M : Mat := LinearMap.toMatrix' F
  have hMv (v : Vec) : M.mulVec v = F v := LinearMap.toMatrix'_mulVec F v
  have hcomp (v : Vec) : ev (Multiplicative.ofAdd (F v)) =
      γ * ev (Multiplicative.ofAdd v) * γ⁻¹ := by
    change ((e (e.symm (a (e (Multiplicative.ofAdd v)))) : E) : G) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hF2 : F.comp F = 1 := by
    apply LinearMap.ext
    intro v
    apply Multiplicative.ofAdd.injective
    apply hevinj
    change ev (Multiplicative.ofAdd (F (F v))) = ev (Multiplicative.ofAdd v)
    rw [hcomp, hcomp]
    simpa only [pow_two, mul_inv_rev, mul_assoc] using hγ2 _ (hmem v)
  have hM2 : M * M = 1 := by
    change LinearMap.toMatrix' F * LinearMap.toMatrix' F = 1
    rw [← LinearMap.toMatrix'_comp, hF2]
    simp
  have hev_surj : ∀ d ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers u,
      ∃ v : Vec, ev (Multiplicative.ofAdd v) = d := by
    intro d hd
    obtain ⟨q, hq⟩ := e.surjective ⟨d, hE.ge hd⟩
    exact ⟨Multiplicative.toAdd q, congrArg Subtype.val hq⟩
  have hM1 : M ≠ 1 := by
    intro hm
    obtain ⟨d, hd, hmove⟩ := hγ1
    obtain ⟨v, hv⟩ := hev_surj d hd
    have hFv : F v = v := by rw [← hMv, hm, Matrix.one_mulVec]
    have h := hcomp v
    rw [hFv, hv] at h
    exact hmove h.symm
  have he0 : ev (Multiplicative.ofAdd e0) = y := by norm_num [hev, e0, hv1]
  have he1 : ev (Multiplicative.ofAdd e1) = u := by norm_num [hev, e1, hv1]
  have hop : ev (Multiplicative.ofAdd ![1, 1]) = y * u := by norm_num [hev, hv1]
  have hom : ev (Multiplicative.ofAdd ![1, 4]) = y * u ^ 4 := by norm_num [hev, hv1, hv4]
  have hfix : M.mulVec bad2 = bad2 ∨ M.mulVec bad3 = bad3 := by
    rcases hbad with h | h
    · left
      apply Multiplicative.ofAdd.injective
      apply hevinj
      rw [hMv, hcomp, hev]
      simpa [bad2, hv1, hv2] using h
    · right
      apply Multiplicative.ofAdd.injective
      apply hevinj
      rw [hMv, hcomp, hev]
      simpa [bad3, hv1, hv3] using h
  have hsmul (c : ZMod 5) (v : Vec) :
      ev (Multiplicative.ofAdd (c • v)) = ev (Multiplicative.ofAdd v) ^ c.val := by
    rw [← map_pow]
    congr 1
    apply Multiplicative.toAdd.injective
    change c • v = c.val • v
    rw [← Nat.cast_smul_eq_nsmul (ZMod 5), ZMod.natCast_zmod_val]
  have hpow (v : Vec) : ev (Multiplicative.ofAdd v) ^ 5 = 1 :=
    pow_five_eq_one_of_mem_fiveSqSubgroup (e (Multiplicative.ofAdd v)).2
  have hline {z w : G} (hz : orderOf z = 5) (hw : w ^ 5 = 1)
      (hzw : z ∈ Subgroup.zpowers w) : Subgroup.zpowers z = Subgroup.zpowers w := by
    have hwdvd : orderOf w ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hw
    have : Finite (Subgroup.zpowers w) := Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers]
      intro ho
      simp [ho] at hwdvd)
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzw)
    rw [Nat.card_zpowers, Nat.card_zpowers, hz]
    exact Nat.le_of_dvd (by norm_num : 0 < 5) hwdvd
  have haxis (i : Fin 2) : orderOf (γ * ev (Multiplicative.ofAdd (Pi.single i 1)) * γ⁻¹) = 5 := by
    fin_cases i
    · change orderOf (γ * ev (Multiplicative.ofAdd e0) * γ⁻¹) = 5
      rw [he0, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
    · change orderOf (γ * ev (Multiplicative.ofAdd e1) * γ⁻¹) = 5
      rw [he1, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
  rcases bad_reflection_dichotomy M hM2 hM1 hfix with hdiag | hM | hM
  · left
    obtain ⟨i, eps, heps, c, hc, hm⟩ := hdiag
    have hcon : γ * ev (Multiplicative.ofAdd (Pi.single i 1)) * γ⁻¹ =
        ev (Multiplicative.ofAdd (c • ![1, eps])) := by
      rw [← hcomp, ← hMv, hm]
    have hle : ev (Multiplicative.ofAdd (c • ![1, eps])) ∈
        Subgroup.zpowers (ev (Multiplicative.ofAdd ![1, eps])) := by
      rw [hsmul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) c.val
    have heq := hline (haxis i) (hpow ![1, eps]) (hcon.symm ▸ hle)
    fin_cases i
    · change Subgroup.zpowers (γ * ev (Multiplicative.ofAdd e0) * γ⁻¹) = _ at heq
      rcases heps with rfl | rfl
      · exact ⟨y, Or.inl rfl, y * u, Or.inl rfl, by simpa only [he0, hop] using heq⟩
      · exact ⟨y, Or.inl rfl, y * u ^ 4, Or.inr rfl, by simpa only [he0, hom] using heq⟩
    · change Subgroup.zpowers (γ * ev (Multiplicative.ofAdd e1) * γ⁻¹) = _ at heq
      rcases heps with rfl | rfl
      · exact ⟨u, Or.inr rfl, y * u, Or.inl rfl, by simpa only [he1, hop] using heq⟩
      · exact ⟨u, Or.inr rfl, y * u ^ 4, Or.inr rfl, by simpa only [he1, hom] using heq⟩
  · right; left
    have h0 := hcomp e0
    have h1 := hcomp e1
    have hm0 : (!![0, 3; 2, 0] : Mat).mulVec e0 = ![0, 2] := by decide +kernel
    have hm1 : (!![0, 3; 2, 0] : Mat).mulVec e1 = ![3, 0] := by decide +kernel
    rw [← hMv, hM, hm0, he0] at h0
    rw [← hMv, hM, hm1, he1] at h1
    exact ⟨by simpa [hev, hv2] using h0.symm, by simpa [hev, hv3] using h1.symm⟩
  · right; right
    have h0 := hcomp e0
    have h1 := hcomp e1
    have hm0 : (!![0, 2; 3, 0] : Mat).mulVec e0 = ![0, 3] := by decide +kernel
    have hm1 : (!![0, 2; 3, 0] : Mat).mulVec e1 = ![2, 0] := by decide +kernel
    rw [← hMv, hM, hm0, he0] at h0
    rw [← hMv, hM, hm1, he1] at h1
    exact ⟨by simpa [hev, hv3] using h0.symm, by simpa [hev, hv2] using h1.symm⟩

end CFSG.StandardType.N2Plane

end
