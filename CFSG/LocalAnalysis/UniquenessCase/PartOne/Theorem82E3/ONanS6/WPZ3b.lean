module

public import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
public import CFSG.RankThree.PartOne.S11d.HighRankExc
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ2e
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

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

theorem zSub_le_centralizer_sylow
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    zSub P c.L ≤ Subgroup.centralizer (P : Set G) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := P ⊓ c.L
  have hPL : P ≤ Subgroup.normalizer (c.L : Set G) := hP.le.trans c.le_normalizer_L
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := by
    intro p hp
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hp, hPL hp⟩
  have hQnormal : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : Q ≤ P)).mpr hPQ
  let H : Subgroup ↥P := Q.subgroupOf P
  let K : Subgroup ↥H := Subgroup.center ↥H
  have hKchar : K.Characteristic := Subgroup.centerCharacteristic
  have hKnormal : (K.map H.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hNp_eq : K.map H.subtype = (zSub P c.L).subgroupOf P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hyQ : ((y : ↥P) : G) ∈ Q :=
        (Subgroup.mem_subgroupOf (H := Q) (K := P)).mp y.2
      refine ⟨hyQ, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro t ht
      have htH : (⟨t, ht.1⟩ : ↥P) ∈ H :=
        (Subgroup.mem_subgroupOf (H := Q) (K := P)).mpr ht
      have hcomm := Subgroup.mem_center_iff.mp hy (⟨⟨t, ht.1⟩, htH⟩ : ↥H)
      exact congrArg (fun z : ↥H => (((z : ↥P) : G))) hcomm
    · intro hx
      have hxZ : ((x : ↥P) : G) ∈ zSub P c.L :=
        (Subgroup.mem_subgroupOf (H := zSub P c.L) (K := P)).mp hx
      have hxQ : ((x : ↥P) : G) ∈ Q := hxZ.1
      have hxH : (x : ↥P) ∈ H :=
        (Subgroup.mem_subgroupOf (H := Q) (K := P)).mpr hxQ
      have hxcent : (⟨x, hxH⟩ : ↥H) ∈ K := by
        refine Subgroup.mem_center_iff.mpr ?_
        intro y
        apply Subtype.ext
        apply Subtype.ext
        have hyQ : ((y : ↥P) : G) ∈ Q :=
          (Subgroup.mem_subgroupOf (H := Q) (K := P)).mp y.2
        exact Subgroup.mem_centralizer_iff.mp hxZ.2 ((y : ↥P) : G) hyQ
      exact ⟨⟨x, hxH⟩, hxcent, rfl⟩
  have hZleP : zSub P c.L ≤ P := (inf_le_left.trans inf_le_left)
  have hZcard : Nat.card ↥((zSub P c.L).subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleP).toEquiv]
    exact c.card_inf_centralizer_of_onan hON hP
  have hNpcard : Nat.card ↥(K.map H.subtype) = 3 := by
    rw [hNp_eq, hZcard]
  haveI : Fact (IsPGroup 3 ↥P) := ⟨hP.isPGroup⟩
  have hcent : K.map H.subtype ≤ Subgroup.center ↥P :=
    CFSG.normal_subgroup_card_eq_prime_le_center (K.map H.subtype) hNpcard
  have hcent' : (zSub P c.L).subgroupOf P ≤ Subgroup.center ↥P := hNp_eq ▸ hcent
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hzP : z ∈ P := hZleP hz
  have hmem : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P :=
    hcent' (Subgroup.mem_subgroupOf.mpr hz)
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨p, hp⟩)

theorem exists_w_central_sylow
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {z : G} (hzZ : z ∈ zSub P c.L) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ Subgroup.centralizer ({a} : Set G))
      (Subgroup.centralizer ({a} : Set G)))
    (wtilde : Jtilde J)
    (hwtilde : MulAut.conj wtilde =
      thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩))
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1) :
    ∃ (S : Sylow 3 (J0 J))
      (hwS : (QuotientGroup.mk' (Subgroup.center (Jtilde J))) wtilde ∈
        (S : Subgroup (J0 J))),
      (⟨(QuotientGroup.mk' (Subgroup.center (Jtilde J))) wtilde, hwS⟩ : ↥S) ∈
        Subgroup.center ↥S ∧
      orderOf ((QuotientGroup.mk' (Subgroup.center (Jtilde J))) wtilde) = 3 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q0 : Jtilde J →* J0 J := QuotientGroup.mk' (Subgroup.center (Jtilde J))
  let qθ : ↥J →* Jtilde J := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J)
  let q : ↥J →* J0 J := q0.comp qθ
  let w : J0 J := q0 wtilde
  let ζ : MulAut (Jtilde J) := thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩)
  have hζ3 : ζ ^ 3 = 1 := by
    have hz3pow : z ^ 3 = 1 := by
      rw [← hz3]
      exact pow_orderOf_eq_one z
    have hz3' : (⟨z, hzN⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hz3pow
    calc ζ ^ 3 = (thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩)) ^ 3 := rfl
      _ = thetaQuotMulAut J ((J.normalizerMonoidHom ⟨z, hzN⟩) ^ 3) :=
          (map_pow (thetaQuotMulAut J) (J.normalizerMonoidHom ⟨z, hzN⟩) 3).symm
      _ = 1 := by
          rw [show (J.normalizerMonoidHom ⟨z, hzN⟩) ^ 3 = 1 by
            rw [← map_pow, hz3', map_one]]
          exact map_one (thetaQuotMulAut J)
  have hwtilde3 : wtilde ^ 3 ∈ Subgroup.center (Jtilde J) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hconj : MulAut.conj (wtilde ^ 3) = 1 := by
      rw [map_pow, hwtilde, hζ3]
    have h := congrArg (fun f : MulAut (Jtilde J) => f y) hconj
    have h' : wtilde ^ 3 * y * (wtilde ^ 3)⁻¹ = y := by
      change (MulAut.conj (wtilde ^ 3)) y = y
      simpa using h
    have hcomm : wtilde ^ 3 * y = y * wtilde ^ 3 := by
      have hm := congrArg (fun z => z * wtilde ^ 3) h'
      simpa [mul_assoc] using hm
    exact hcomm.symm
  have hw3 : w ^ 3 = 1 := by
    change (q0 wtilde) ^ 3 = 1
    rw [← map_pow]
    change (QuotientGroup.mk' (Subgroup.center (Jtilde J))) (wtilde ^ 3) = 1
    exact (QuotientGroup.eq_one_iff (wtilde ^ 3)).mpr hwtilde3
  have hw1 : w ≠ 1 := by
    intro hw
    have hwtilde_cent : wtilde ∈ Subgroup.center (Jtilde J) := by
      rw [← QuotientGroup.eq_one_iff]
      exact hw
    have hconj : MulAut.conj wtilde = 1 := by
      ext y
      rw [MulAut.conj_apply, MulAut.one_apply]
      have hcomm := Subgroup.mem_center_iff.mp hwtilde_cent y
      calc wtilde * y * wtilde⁻¹ = (y * wtilde) * wtilde⁻¹ := by rw [hcomm]
        _ = y := by group
    exact hπ (hwtilde.symm.trans hconj)
  have hword : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  let T : Subgroup G := P ⊓ Subgroup.centralizer ({a} : Set G)
  have hJleC : J ≤ Subgroup.centralizer ({a} : Set G) :=
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ).1
  have hTJ : T ≤ Subgroup.normalizer (J : Set G) := by
    intro t ht
    exact normalizer_thetaComp_of_three_element' c hON h7 hP hNZ haL ha3 haZ hJ h3 ht.2
      (hT.isPGroup.to_le (Subgroup.zpowers_le.mpr ht))
  have hT_sylow_TJ : CFSG.ABGLocalTools.IsSylowOf 3 T (T ⊔ J) :=
    hT.of_le le_sup_left (sup_le hT.le hJleC)
  have hTJ_sup : T ⊔ J ≤ Subgroup.normalizer (J : Set G) :=
    sup_le hTJ Subgroup.le_normalizer
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (T ⊓ J) J :=
    hT_sylow_TJ.inf_of_le_normalizer le_sup_right hTJ_sup
  let S0 : Subgroup (J0 J) := ((T ⊓ J).subgroupOf J).map q
  have hSyl' : CFSG.ABGLocalTools.IsSylowOf 3 ((T ⊓ J).subgroupOf J) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) J]
    simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype] using hSyl
  have hqsurj : Function.Surjective q :=
    (QuotientGroup.mk'_surjective (Subgroup.center (Jtilde J))).comp
      (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥J))
  have hqtop : Subgroup.map q (⊤ : Subgroup ↥J) = ⊤ :=
    Subgroup.map_top_of_surjective q hqsurj
  have hS0syl : CFSG.ABGLocalTools.IsSylowOf 3 S0 ⊤ := by
    simpa [S0, hqtop] using
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c7_isSylowOf_map hSyl' q
  let S : Sylow 3 (J0 J) := hS0syl.isPGroup.toSylow (by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS0syl).2.2
    simpa using h)
  have hScoe : (S : Subgroup (J0 J)) = S0 :=
    IsPGroup.toSylow_coe hS0syl.isPGroup _
  have hzcentP : z ∈ Subgroup.centralizer (P : Set G) :=
    zSub_le_centralizer_sylow c hON hP hzZ
  have hcent_q : ∀ (t : ↥J), ((t : G) ∈ T ⊓ J) →
      q t ∈ Subgroup.centralizer ({w} : Set (J0 J)) := by
    intro t ht
    have hzconj_t : z * (t : G) * z⁻¹ = (t : G) := by
      have hcomm : z * (t : G) = (t : G) * z :=
        (Subgroup.mem_centralizer_iff.mp hzcentP (t : G) ht.1.1).symm
      calc z * (t : G) * z⁻¹ = ((t : G) * z) * z⁻¹ := by rw [hcomm]
        _ = (t : G) := by group
    have hfix : ζ (qθ t) = qθ t := by
      change thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) (t : Jtilde J) = (t : Jtilde J)
      rw [thetaQuotMulAut_mk]
      have hconj : J.normalizerMonoidHom ⟨z, hzN⟩ t = t := by
        apply Subtype.ext
        rw [normalizerMonoidHom_apply_coe]
        exact hzconj_t
      rw [hconj]
    have hconj_eq : wtilde * qθ t * wtilde⁻¹ = qθ t := by
      have h := congrArg (fun f : MulAut (Jtilde J) => f (qθ t)) (hwtilde.trans rfl)
      have h' : MulAut.conj wtilde (qθ t) = qθ t := by rw [hwtilde]; exact hfix
      simpa [MulAut.conj_apply] using h'
    have hq0eq := congrArg q0 hconj_eq
    have hcomm : w * q t * w⁻¹ = q t := by
      simpa [q, w, map_mul, map_inv] using hq0eq
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hwq : w * q t = q t * w := by
      calc w * q t = (w * q t * w⁻¹) * w := by group
        _ = q t * w := by rw [hcomm]
    exact hwq.symm
  have hS0_cent : S0 ≤ Subgroup.centralizer ({w} : Set (J0 J)) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨t, ht, rfl⟩
    exact hcent_q t (Subgroup.mem_subgroupOf.mp ht)
  have hw_cent_S0 : w ∈ Subgroup.centralizer (S0 : Set (J0 J)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS0_cent hs)
  have hZw_norm : Subgroup.zpowers w ≤ Subgroup.normalizer (S0 : Set (J0 J)) :=
    (Subgroup.zpowers_le.mpr hw_cent_S0).trans
      (Subgroup.centralizer_le_normalizer (S0 : Set (J0 J)))
  have hZwP : IsPGroup 3 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hword]; norm_num)
  have hsupP : IsPGroup 3 (S0 ⊔ Subgroup.zpowers w : Subgroup (J0 J)) :=
    IsPGroup.to_sup_of_normal_left' hS0syl.isPGroup hZwP hZw_norm
  have hsup_eq : (S0 ⊔ Subgroup.zpowers w : Subgroup (J0 J)) = S0 :=
    hS0syl.eq_of_le le_sup_left le_top hsupP
  have hwS0 : w ∈ S0 := by
    have h : w ∈ (S0 ⊔ Subgroup.zpowers w : Subgroup (J0 J)) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    simpa [hsup_eq] using h
  refine ⟨S, ?_, ?_, hword⟩
  · rw [hScoe]; exact hwS0
  · rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hyS0 : (y : J0 J) ∈ S0 := by rw [← hScoe]; exact y.2
    have hycomm : (y : J0 J) ∈ Subgroup.centralizer ({w} : Set (J0 J)) := hS0_cent hyS0
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hycomm
    simpa [w, q0] using hcomm

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
