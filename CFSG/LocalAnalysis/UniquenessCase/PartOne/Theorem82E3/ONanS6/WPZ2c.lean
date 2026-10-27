module

public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofPoint
public import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.Sporadic.J2
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import Certificates.Data.Item434SporWords

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem exists_commutator_not_mem_theta {J : Subgroup G} {z : G}
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1) :
    ∃ x ∈ J, ⁅z, x⁆ ∉ inSubgroup (aschbacherSolvableCore 3) J := by
  classical
  set τ : MulAut (↥J ⧸ aschbacherSolvableCore 3 ↥J) :=
    thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) with hτ
  have hex : ∃ q : ↥J ⧸ aschbacherSolvableCore 3 ↥J, τ q ≠ q := by
    by_contra h
    push Not at h
    exact hπ (by ext q; exact h q)
  obtain ⟨q, hq⟩ := hex
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥J) q
  refine ⟨x, x.2, fun hmem => hq ?_⟩
  have hzxmem : z * (x : G) * z⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hzN x).mp x.2
  have hcxmem : ⁅z, (x : G)⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem hzxmem (J.inv_mem x.2)
  have hsub : (⟨z * (x : G) * z⁻¹, hzxmem⟩ : ↥J) = (⟨⁅z, (x : G)⁆, hcxmem⟩ : ↥J) * x := by
    ext
    show z * (x : G) * z⁻¹ = ⁅z, (x : G)⁆ * (x : G)
    rw [commutatorElement_def]
    group
  have hc1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J) (⟨⁅z, (x : G)⁆, hcxmem⟩ : ↥J) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [show (⟨⁅z, (x : G)⁆, hcxmem⟩ : ↥J) = y from Subtype.ext hyx.symm]
    exact hy
  have hmk : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J) (⟨z * (x : G) * z⁻¹, hzxmem⟩ : ↥J)
      = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J) x := by
    rw [hsub, map_mul, hc1, one_mul]
  rw [QuotientGroup.mk'_apply, hτ, CFSG.RankThree.PartTwo.Sec4.thetaQuotMulAut_mk,
    show J.normalizerMonoidHom ⟨z, hzN⟩ x = (⟨z * (x : G) * z⁻¹, hzxmem⟩ : ↥J) from
      Subtype.ext (CFSG.RankThree.PartTwo.Sec4.normalizerMonoidHom_apply_coe hzN x)]
  exact hmk

theorem thetaQuotMulAut_eq_one_of_conj_mem_theta {J : Subgroup G} {n : G}
    (hnN : n ∈ Subgroup.normalizer (J : Set G))
    (hn : ∀ x ∈ J, x⁻¹ * n * x * n⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) J) :
    thetaQuotMulAut J (J.normalizerMonoidHom ⟨n, hnN⟩) = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [CFSG.RankThree.PartTwo.Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
    have hσ : J.normalizerMonoidHom ⟨n, hnN⟩ x =
        (⟨n * (x : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnN x).mp x.2⟩ : ↥J) :=
      Subtype.ext (CFSG.RankThree.PartTwo.Sec4.normalizerMonoidHom_apply_coe hnN x)
    rw [hσ, QuotientGroup.eq]
    obtain ⟨y, hy, hyval⟩ := hn x x.2
    rw [show ((⟨n * (x : G) * n⁻¹,
      (Subgroup.mem_normalizer_iff.mp hnN x).mp x.2⟩ : ↥J))⁻¹ * x = y⁻¹ from Subtype.ext ?_]
    · exact (aschbacherSolvableCore 3 ↥J).inv_mem hy
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      have hyval' : (y : G) = (x : G)⁻¹ * n * (x : G) * n⁻¹ := hyval
      rw [hyval']
      group

theorem j0_iso_and_inner_aux {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a)
    (h3 : 3 ∣ Nat.card J) (hZJ : zSub P c.L ≤ Subgroup.normalizer (J : Set G))
    {z : G} (hzZ : z ∈ zSub P c.L) (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1)
    (hXsimple : IsSimpleGroup ↥(Xbar c P J)) :
    Nonempty (J0 J ≃* Xbar c P J) ∧
      thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ∈
        (MulAut.conj : (Jtilde J) →* MulAut (Jtilde J)).range := by
  classical
  have hG0normJ : (G0 c P J) ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer hZJ
  have hJG0 : (J.subgroupOf (G0 c P J)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hG0normJ
  have hJquasi : CFSG.IsQuasisimple (Jtilde J) :=
    CFSG.RankThree.PartTwo.Sec6.isQuasisimple_of_mem_thetaComponentsAt hJ
  have hJperf : Group.IsPerfect ↥J :=
    CFSG.RankThree.PartTwo.Sec6.isPerfect_of_mem_thetaComponentsAt hJ
  let ε : ↥(J.subgroupOf (G0 c P J)) ≃* ↥J :=
    Subgroup.subgroupOfEquivOfLe (le_sup_left : J ≤ J ⊔ zSub P c.L)
  have hJg_perf : Group.IsPerfect ↥(J.subgroupOf (G0 c P J)) :=
    Group.IsPerfect.ofSurjective (f := ε.symm.toMonoidHom) ε.symm.surjective
  have hJg_quasi : CFSG.IsQuasisimple
      (J.subgroupOf (G0 c P J) ⧸ aschbacherSolvableCore 3 ↥(J.subgroupOf (G0 c P J))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _
        ε.symm (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three ε.symm)) hJquasi
  have hJg_mem : J.subgroupOf (G0 c P J) ∈ thetaComponents 3 ↥(G0 c P J) :=
    ⟨hJg_perf, hJG0.isSubnormal, hJg_quasi⟩
  have hcardJg : Nat.card ↥(J.subgroupOf (G0 c P J)) = Nat.card ↥J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : J ≤ J ⊔ zSub P c.L)).toEquiv
  have h3g : 3 ∣ Nat.card ↥(J.subgroupOf (G0 c P J)) := by
    rw [hcardJg]; exact h3
  have hJN : J.subgroupOf (G0 c P J) ⊓ CFSG.pPrimeCore 3 ↥(G0 c P J) =
      inSubgroup (aschbacherSolvableCore 3) (J.subgroupOf (G0 c P J)) :=
    inf_pPrimeCore_eq_of_mem_thetaComponents hJg_mem h3g
  have htheta_map : (inSubgroup (aschbacherSolvableCore 3) (J.subgroupOf (G0 c P J))).map
      (G0 c P J).subtype = inSubgroup (aschbacherSolvableCore 3) J := by
    rw [inSubgroup, inSubgroup, Subgroup.map_map]
    have hcomp : ((G0 c P J).subtype).comp (J.subgroupOf (G0 c P J)).subtype =
        J.subtype.comp ε.toMonoidHom := by
      ext y
      exact (Subgroup.subgroupOfEquivOfLe_apply_coe (le_sup_left : J ≤ J ⊔ zSub P c.L) y).symm
    rw [hcomp, ← Subgroup.map_map,
      CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three ε]
  let N : Subgroup ↥(G0 c P J) := CFSG.pPrimeCore 3 ↥(G0 c P J)
  let π : ↥(G0 c P J) →* (↥(G0 c P J) ⧸ N) := QuotientGroup.mk' N
  let Jg : Subgroup ↥(G0 c P J) := J.subgroupOf (G0 c P J)
  let JN : Subgroup (↥(G0 c P J) ⧸ N) := Jg.map π
  haveI hXbarN : (Xbar c P J).Normal := Subgroup.normalClosure_normal
  have hJNnorm : JN.Normal := hJG0.map π (QuotientGroup.mk'_surjective N)
  haveI : JN.Normal := hJNnorm
  obtain ⟨η, -⟩ := exists_thetaQuot_equiv_map_starQuot hJg_mem h3g
  have hJNquasi : CFSG.IsQuasisimple ↥JN := CFSG.LocalCores.isQuasisimple_of_mulEquiv η hJg_quasi
  have hzG0 : z ∈ G0 c P J := Subgroup.mem_sup_right hzZ
  have hζ : π ⟨z, hzG0⟩ ∈ Xbar c P J := by
    refine Subgroup.subset_normalClosure ?_
    exact Subgroup.mem_map_of_mem π (show (⟨z, hzG0⟩ : ↥(G0 c P J)) ∈ Z0 c P J from hzZ)
  have hcomm_ne : ⁅Xbar c P J, JN⁆ ≠ ⊥ := by
    obtain ⟨x, hxJ, hxθ⟩ := exists_commutator_not_mem_theta hzN hπ
    intro hzero
    have hxG0 : x ∈ G0 c P J := Subgroup.mem_sup_left hxJ
    have hcxJ : ⁅z, x⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp hzN x).mp hxJ) (J.inv_mem hxJ)
    have hcxG0 : ⁅z, x⁆ ∈ G0 c P J := Subgroup.mem_sup_left hcxJ
    have hξ : π ⟨x, hxG0⟩ ∈ JN :=
      Subgroup.mem_map_of_mem π (show (⟨x, hxG0⟩ : ↥(G0 c P J)) ∈ Jg from hxJ)
    have hmem := Subgroup.commutator_mem_commutator hζ hξ
    rw [hzero, Subgroup.mem_bot] at hmem
    have hmap : π ⁅(⟨z, hzG0⟩ : ↥(G0 c P J)), ⟨x, hxG0⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmap
    have hval : ((⁅(⟨z, hzG0⟩ : ↥(G0 c P J)), ⟨x, hxG0⟩⁆ : ↥(G0 c P J)) : G) = ⁅z, x⁆ := by
      change (G0 c P J).subtype ⁅(⟨z, hzG0⟩ : ↥(G0 c P J)), ⟨x, hxG0⟩⁆ = ⁅z, x⁆
      rw [map_commutatorElement]
      rfl
    have hcxN : (⟨⁅z, x⁆, hcxG0⟩ : ↥(G0 c P J)) ∈ N := by
      rw [show (⟨⁅z, x⁆, hcxG0⟩ : ↥(G0 c P J)) =
        ⁅(⟨z, hzG0⟩ : ↥(G0 c P J)), ⟨x, hxG0⟩⁆ from Subtype.ext hval]
      exact hmap
    have hcxθg : (⟨⁅z, x⁆, hcxG0⟩ : ↥(G0 c P J)) ∈
        inSubgroup (aschbacherSolvableCore 3) Jg := by
      rw [← hJN]
      exact ⟨hcxJ, hcxN⟩
    apply hxθ
    rw [← htheta_map]
    exact ⟨⟨⁅z, x⁆, hcxG0⟩, hcxθg, rfl⟩
  have hXbar_le : Xbar c P J ≤ JN := by
    by_contra hnot
    have hinf : Xbar c P J ⊓ JN = ⊥ := by
      haveI : (Xbar c P J ⊓ JN).Normal := inferInstance
      have hnormal : ((Xbar c P J ⊓ JN).subgroupOf (Xbar c P J)).Normal := inferInstance
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Xbar c P J ⊓ JN).subgroupOf (Xbar c P J)) with h | h
      · rw [eq_bot_iff]
        intro y hy
        have hy' : (⟨y, hy.1⟩ : ↥(Xbar c P J)) ∈
            (Xbar c P J ⊓ JN).subgroupOf (Xbar c P J) := Subgroup.mem_subgroupOf.mpr hy
        rw [h, Subgroup.mem_bot] at hy'
        exact Subtype.ext_iff.mp hy'
      · exfalso
        apply hnot
        intro y hy
        have hy' : (⟨y, hy⟩ : ↥(Xbar c P J)) ∈
            (Xbar c P J ⊓ JN).subgroupOf (Xbar c P J) := by
          rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hy').2
    exact hcomm_ne (Subgroup.commutator_eq_bot_of_disjoint (by
      rw [disjoint_iff]; exact hinf))
  have hXbar_eq : Xbar c P J = JN := by
    refine le_antisymm hXbar_le ?_
    have hnormal : ((Xbar c P J).subgroupOf JN).Normal := Subgroup.normal_subgroupOf
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJNquasi hnormal with htop | hcen
    · rw [Subgroup.subgroupOf_eq_top] at htop
      exact htop
    · exfalso
      have hcent : Xbar c P J ≤
          Subgroup.centralizer (JN : Set (↥(G0 c P J) ⧸ N)) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have hmem : (⟨y, hXbar_le hy⟩ : ↥JN) ∈ Subgroup.center ↥JN :=
          hcen (Subgroup.mem_subgroupOf.mpr hy)
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨b, hb⟩)
      exact hcomm_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent)
  have hεθ : (aschbacherSolvableCore 3 ↥J).map ε.symm.toMonoidHom =
      aschbacherSolvableCore 3 ↥(J.subgroupOf (G0 c P J)) :=
    CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three ε.symm
  let e1 : Jtilde J ≃* (Jg ⧸ aschbacherSolvableCore 3 ↥Jg) :=
    QuotientGroup.congr _ _ ε.symm hεθ
  let eX : Jtilde J ≃* ↥(Xbar c P J) :=
    e1.trans (η.trans (MulEquiv.subgroupCongr hXbar_eq.symm))
  have hcenterX : Subgroup.center ↥(Xbar c P J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(Xbar c P J)) with h | h
    · exact h
    · exfalso
      have hcommX : ∀ a b : ↥(Xbar c P J), a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
      have hcommJ : ∀ a b : Jtilde J, a * b = b * a := by
        intro a b
        apply eX.injective
        rw [map_mul, map_mul, hcommX]
      obtain ⟨a0, b0, hab⟩ := hJquasi.2.2
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a0
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b0
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcommJ x y]
  have hcenterJ : Subgroup.center (Jtilde J) = ⊥ := by
    have h1 : (Subgroup.center (Jtilde J)).map eX.toMonoidHom =
        Subgroup.center ↥(Xbar c P J) := Subgroup.map_center_eq eX
    rw [hcenterX, Subgroup.map_eq_bot_iff] at h1
    have hker : eX.toMonoidHom.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]; exact eX.injective
    exact le_bot_iff.mp (h1.trans (le_of_eq hker))
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq hcenterJ).trans
    (QuotientGroup.quotientBot.trans eX)⟩, ?_⟩
  have hζJN : π ⟨z, hzG0⟩ ∈ JN := hXbar_eq ▸ hζ
  obtain ⟨j0, hj0Jg, hj0eq⟩ := Subgroup.mem_map.mp hζJN
  have hj0J : (j0 : G) ∈ J := hj0Jg
  have hj0N : (j0 : G) ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hj0J
  have hn0N : (j0⁻¹ * ⟨z, hzG0⟩ : ↥(G0 c P J)) ∈ N := by
    have h1 : π (j0⁻¹ * ⟨z, hzG0⟩) = 1 := by
      rw [map_mul, map_inv, hj0eq, inv_mul_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hnN : ((j0⁻¹ * ⟨z, hzG0⟩ : ↥(G0 c P J)) : G) ∈ Subgroup.normalizer (J : Set G) :=
    hG0normJ (j0⁻¹ * ⟨z, hzG0⟩ : ↥(G0 c P J)).2
  have hz_eq : (⟨z, hzN⟩ : Subgroup.normalizer (J : Set G)) =
      ⟨(j0 : G), hj0N⟩ *
        ⟨((j0⁻¹ * ⟨z, hzG0⟩ : ↥(G0 c P J)) : G), hnN⟩ := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    group
  have hn_triv : thetaQuotMulAut J (J.normalizerMonoidHom
      ⟨((j0⁻¹ * ⟨z, hzG0⟩ : ↥(G0 c P J)) : G), hnN⟩) = 1 := by
    refine thetaQuotMulAut_eq_one_of_conj_mem_theta hnN (fun x hxJ => ?_)
    have hxG0 : x ∈ G0 c P J := Subgroup.mem_sup_left hxJ
    have hxJg : (⟨x, hxG0⟩ : ↥(G0 c P J)) ∈ Jg := hxJ
    have hcxJg : (⟨x, hxG0⟩ : ↥(G0 c P J))⁻¹ * (j0⁻¹ * ⟨z, hzG0⟩) *
        ⟨x, hxG0⟩ * (j0⁻¹ * ⟨z, hzG0⟩)⁻¹ ∈ Jg := by
      have hconj : (j0⁻¹ * ⟨z, hzG0⟩) * ⟨x, hxG0⟩ * (j0⁻¹ * ⟨z, hzG0⟩)⁻¹ ∈ Jg :=
        hJG0.conj_mem ⟨x, hxG0⟩ hxJg (j0⁻¹ * ⟨z, hzG0⟩)
      have h1 : (⟨x, hxG0⟩ : ↥(G0 c P J))⁻¹ *
          ((j0⁻¹ * ⟨z, hzG0⟩) * ⟨x, hxG0⟩ * (j0⁻¹ * ⟨z, hzG0⟩)⁻¹) ∈ Jg :=
        Jg.mul_mem (Jg.inv_mem hxJg) hconj
      simpa only [mul_assoc] using h1
    have hcxN : (⟨x, hxG0⟩ : ↥(G0 c P J))⁻¹ * (j0⁻¹ * ⟨z, hzG0⟩) *
        ⟨x, hxG0⟩ * (j0⁻¹ * ⟨z, hzG0⟩)⁻¹ ∈ N := by
      haveI : N.Normal := CFSG.pPrimeCore_normal
      have h1 : (⟨x, hxG0⟩ : ↥(G0 c P J))⁻¹ * (j0⁻¹ * ⟨z, hzG0⟩) * ⟨x, hxG0⟩ ∈ N := by
        simpa using (inferInstance : N.Normal).conj_mem (j0⁻¹ * ⟨z, hzG0⟩) hn0N ⟨x, hxG0⟩⁻¹
      exact N.mul_mem h1 (N.inv_mem hn0N)
    have hc0θg : (⟨x, hxG0⟩ : ↥(G0 c P J))⁻¹ * (j0⁻¹ * ⟨z, hzG0⟩) *
        ⟨x, hxG0⟩ * (j0⁻¹ * ⟨z, hzG0⟩)⁻¹ ∈
        inSubgroup (aschbacherSolvableCore 3) Jg := by
      rw [← hJN]; exact ⟨hcxJg, hcxN⟩
    have hc0θ : (x : G)⁻¹ * ((j0⁻¹ * ⟨z, hzG0⟩ : ↥(G0 c P J)) : G) * (x : G) *
        ((j0⁻¹ * ⟨z, hzG0⟩ : ↥(G0 c P J)) : G)⁻¹ ∈
        inSubgroup (aschbacherSolvableCore 3) J := by
      rw [← htheta_map]
      refine ⟨(⟨x, hxG0⟩ : ↥(G0 c P J))⁻¹ * (j0⁻¹ * ⟨z, hzG0⟩) * ⟨x, hxG0⟩ *
        (j0⁻¹ * ⟨z, hzG0⟩)⁻¹, hc0θg, ?_⟩
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
        Subgroup.coe_subtype]
    exact hc0θ
  have hinner : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J) ⟨(j0 : G), hj0J⟩) := by
    have hz_decomp : J.normalizerMonoidHom ⟨z, hzN⟩ =
        J.normalizerMonoidHom ⟨(j0 : G), hj0N⟩ *
          J.normalizerMonoidHom ⟨((j0⁻¹ * ⟨z, hzG0⟩ : ↥(G0 c P J)) : G), hnN⟩ := by
      rw [hz_eq, map_mul]
    rw [hz_decomp, map_mul, hn_triv, mul_one,
      CFSG.RankThree.PartTwo.Sec15.Proof156.thetaQuotMulAut_eq_conj (L := J) (y := (j0 : G)) hj0J]
  exact ⟨_, hinner.symm⟩

theorem j0_iso_and_inner'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {z : G} (hzZ : z ∈ zSub P c.L) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1)
    (hroute : IsoGTwoPrime (Xbar c P J) ∨
      Nonempty (Xbar c P J ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Nonempty (J0 J ≃* Xbar c P J) ∧
      thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ∈
        (MulAut.conj : (Jtilde J) →* MulAut (Jtilde J)).range := by
  have hZJ : zSub P c.L ≤ Subgroup.normalizer (J : Set G) :=
    zSub_le_normalizer_of_threeComp c hON h7 hP hNZ haL ha3 haZ hJ h3
  have hXsimple : IsSimpleGroup ↥(Xbar c P J) := by
    rcases hroute with hG2 | hJ2
    · rcases hG2 with ⟨p, f, hmodel⟩ | hU3
      · exact (CFSG.LieType.Simplicity.fam_g2_simplicity (Xbar c P J) p f hmodel).2
      · obtain ⟨e⟩ := hU3
        exact @MulEquiv.isSimpleGroup _ _ _ _
          CFSG.RankThree.PartTwo.Sec19.Step1911EndProof.isSimpleGroup_projSU_three_three e
    · obtain ⟨e⟩ := hJ2
      exact @MulEquiv.isSimpleGroup _ _ _ _ (CFSG.Sporadic.J2.isSimpleGroup_J2) e
  exact j0_iso_and_inner_aux c hJ h3 hZJ hzZ hzN hπ hXsimple

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
