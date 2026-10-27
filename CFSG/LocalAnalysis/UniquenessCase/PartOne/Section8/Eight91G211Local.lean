module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.GroupTheory.PCore.FixedSubgroupCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
import CFSG.GroupTheory.PCoreSurjective

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem k891gbasic_opp_le {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    Opp p X ≤ X := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem r891g211_basic {G : Type} [Group G] [Finite G] (D : Data G) {L S R A : Subgroup G}
    (hst : R891State D L S R A 1) :
    R ≤ R891H L S ∧ R891X L (R891Z L S) 1 ≤ R891H L S ∧ IsPGroup 3 ↥(R891Z L S) ∧
      IsPGroup 3 ↥R ∧ ZOf R = R891Z L S := by
  have hRleH : R ≤ R891H L S := by
    intro r hr
    change r ∈ centralizer (R891Z L S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzcent : z ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) :=
      (show z ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) from hz).2
    exact (Subgroup.mem_centralizer_iff.mp hzcent r
      (hst.ctx.xShape.rSylow hr)).symm
  have hXleH : R891X L (R891Z L S) 1 ≤ R891H L S := by
    have hXeq : R891X L (R891Z L S) 1 = Opp 2 (L ⊓ centralizer (R891Z L S : Set G)) := by
      unfold R891X
      rw [if_pos rfl]
    rw [hXeq]
    change Opp 2 (L ⊓ centralizer (R891Z L S : Set G)) ≤ centralizer (R891Z L S : Set G)
    exact (k891gbasic_opp_le 2 (L ⊓ centralizer (R891Z L S : Set G))).trans inf_le_right
  have hZp : IsPGroup 3 ↥(R891Z L S) :=
    IsPGroup.of_card (n := 1) (by rw [hst.basic.zOrder]; norm_num)
  have hExtra := hst.ctx.xShape.rExtra
  unfold IsExtraspecialExpP at hExtra
  have hRp : IsPGroup 3 ↥R := IsPGroup.of_card (n := 1 + 2 * 1) hExtra.1
  have hZle : R891Z L S ≤ ZOf R := by
    intro z hz
    change z ∈ R ∧ z ∈ centralizer (R : Set G)
    refine ⟨hst.ctx.xShape.zLe hz, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hzcent : z ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) :=
      (show z ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) from hz).2
    exact Subgroup.mem_centralizer_iff.mp hzcent r (hst.ctx.xShape.rSylow hr)
  have hcard : Nat.card (ZOf R) = 3 := by
    rw [ZOf, ← CFSG.center_map_subtype_eq_inf_centralizer R,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective R)]
    exact hExtra.2.2.2
  exact ⟨hRleH, hXleH, hZp, hRp,
    (Subgroup.eq_of_le_of_card_ge hZle (by rw [hcard, hst.basic.zOrder])).symm⟩

private theorem k891guniq_map_conj {G : Type} [Group G] {M A : Subgroup G} {m : G}
    (hA : A ∈ uniqueSet M) (hm : m ∈ M) :
    A.map (MulAut.conj m).toMonoidHom ∈ uniqueSet M := by
  have hMm : M.map (MulAut.conj m).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)
  refine ⟨?_, ?_⟩
  · rw [← hMm]
    exact Subgroup.map_mono hA.1
  · intro g hg
    have hcomp1 : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hcomp2 : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (m⁻¹ * g)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hcomp3 : (MulAut.conj m).toMonoidHom.comp (MulAut.conj (m⁻¹ * g)).toMonoidHom =
        (MulAut.conj g).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hle : A ≤ M.map (MulAut.conj (m⁻¹ * g)).toMonoidHom := by
      have h1 := Subgroup.map_mono (f := (MulAut.conj m⁻¹).toMonoidHom) hg
      rw [Subgroup.map_map, Subgroup.map_map, hcomp1, hcomp2, Subgroup.map_id] at h1
      exact h1
    have hmid : M.map (MulAut.conj (m⁻¹ * g)).toMonoidHom = M := hA.2 (m⁻¹ * g) hle
    have h2 := congrArg (Subgroup.map (MulAut.conj m).toMonoidHom) hmid
    rw [Subgroup.map_map, hcomp3, hMm] at h2
    exact h2

theorem r891g211_uniq {G : Type} [Group G] [Finite G] (D : Data G) {L S R A : Subgroup G}
    (hst : R891State D L S R A 1) :
    ∀ W : Subgroup G, R891Z L S < W → W ≤ R → W ∈ uniqueSet D.M := by
  intro W hZW hWR
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hst.set.mem.1
  have hRL : R ≤ L := hst.ctx.xShape.rSylow.trans inf_le_right
  have hWM : W ≤ D.M := hWR.trans (hRL.trans hLM)
  have hRexp : Monoid.exponent ↥R = 3 := hst.ctx.xShape.rExtra.2.1
  obtain ⟨w, hwW, hwZ⟩ := SetLike.exists_of_lt hZW
  have hwR : w ∈ R := hWR hwW
  have hw3 : w ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨w, hwR⟩ : ↥R)
    rw [hRexp] at h
    simpa using congrArg Subtype.val h
  have hw1 : w ≠ 1 := fun h => hwZ (h.symm ▸ (R891Z L S).one_mem)
  have hword : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hBcard : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hword]
  have hBW : Subgroup.zpowers w ≤ W := Subgroup.zpowers_le.mpr hwW
  have hBL : Subgroup.zpowers w ≤ L := hBW.trans (hWR.trans hRL)
  have hBne : Subgroup.zpowers w ≠ R891Z L S := by
    intro h
    exact hwZ (h ▸ Subgroup.mem_zpowers w)
  rcases hst.ctx.classes.classes (Subgroup.zpowers w) hBL hBcard with ⟨l, hlL, hBl⟩ | ⟨l, hlL, hBl⟩
  · have hZle : (R891Z L S).map (MulAut.conj l).toMonoidHom ≤ R891X L (R891Z L S) 1 := by
      rw [← hBl]
      exact hBW.trans (hWR.trans hst.ctx.xShape.rLe)
    have hfix := hst.ctx.xShape.zWeak l (hLM hlL) hZle
    exact absurd (hBl.trans hfix) hBne
  · have hAuniq : A.map (MulAut.conj l).toMonoidHom ∈ uniqueSet D.M :=
      k891guniq_map_conj hst.uniq (hLM hlL)
    exact CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le (hBl.symm ▸ hAuniq) hBW hWM

private theorem k891gsyllem_le_H {G : Type} [Group G] {L S R : Subgroup G}
    (hRSL : R ≤ S ⊓ L) : R ≤ R891H L S := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzC : z ∈ centralizer (S ⊓ L : Set G) :=
    (Subgroup.mem_inf.mp (show z ∈ (S ⊓ L) ⊓ centralizer (S ⊓ L : Set G) from hz)).2
  rw [Subgroup.mem_centralizer_iff] at hzC
  exact (hzC r (hRSL hr)).symm

theorem r891g211_sylow_le_M {G : Type} [Group G] [Finite G] (D : Data G) {L S R A : Subgroup G}
    (hst : R891State D L S R A 1)
    (huniq : ∀ W : Subgroup G, R891Z L S < W → W ≤ R → W ∈ uniqueSet D.M) :
    ∃ P0 : Subgroup G, IsSylowOf 3 P0 (R891H L S) ∧ R ≤ P0 ∧ P0 ≤ D.M := by
  have hcardR : Nat.card R = 3 ^ (1 + 2 * 1) := hst.ctx.xShape.rExtra.1
  have hcardZ : Nat.card (R891Z L S) = 3 := hst.basic.zOrder
  have hZr : R891Z L S ≤ R := hst.ctx.xShape.zLe
  have hZne : R891Z L S ≠ R := by
    intro h
    rw [h] at hcardZ
    rw [hcardR] at hcardZ
    norm_num at hcardZ
  have hRU : R ∈ uniqueSet D.M := huniq R (lt_of_le_of_ne hZr hZne) le_rfl
  have hRH : R ≤ R891H L S := k891gsyllem_le_H hst.ctx.xShape.rSylow
  have hRpg : IsPGroup 3 ↥R := IsPGroup.of_card (n := 1 + 2 * 1) hcardR
  have hRsub : IsPGroup 3 ↥(R.subgroupOf (R891H L S)) := hRpg.comap_subtype
  obtain ⟨Q, hQ⟩ := hRsub.exists_le_sylow
  have hle : R ≤ (Q : Subgroup ↥(R891H L S)).map (R891H L S).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRH]
    exact Subgroup.map_mono hQ
  have hP0 : IsSylowOf 3 ((Q : Subgroup ↥(R891H L S)).map (R891H L S).subtype) (R891H L S) :=
    ⟨Q, rfl⟩
  exact ⟨_, hP0, hle,
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      D.maxLocal hRU hle hP0.isPGroup⟩

private theorem k891gpprime_zcenter {G : Type} [Group G] {H Z : Subgroup G}
    (hHZ : H ≤ centralizer (Z : Set G)) :
    Z.subgroupOf H ≤ Subgroup.center ↥H := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx' : (x : G) ∈ Z := hx
  have hcomm : (x : G) * (y : G) = (y : G) * (x : G) :=
    Subgroup.mem_centralizer_iff.mp (hHZ y.2) (x : G) hx'
  simpa using hcomm.symm

private theorem k891gpprime_zpgroup {G : Type} [Group G] {Z : Subgroup G} (H : Subgroup G)
    (hZ : IsPGroup 3 ↥Z) : IsPGroup 3 (Z.subgroupOf H) :=
  hZ.comap_of_injective H.subtype Subtype.coe_injective

private theorem k891gpprime_ker_eq {G : Type} [Group G] [Finite G] {H Z : Subgroup G}
    (hHZ : H ≤ centralizer (Z : Set G)) :
    R891Ker H Z = CFSG.pPrimeCore 3 ↥H ⊔ Z.subgroupOf H := by
  have hZc : Z.subgroupOf H ≤ Subgroup.center ↥H := k891gpprime_zcenter hHZ
  have hZn : (Z.subgroupOf H).Normal := Subgroup.normal_of_le_center hZc
  show Subgroup.normalClosure ((CFSG.pPrimeCore 3 ↥H : Set ↥H) ∪ (Z.subgroupOf H : Set ↥H)) = _
  rw [Subgroup.normalClosure_union]
  simp

theorem r891g211_pPrimeCore_star {G : Type} [Group G] [Finite G] {H Z : Subgroup G}
    (hHZ : H ≤ centralizer (Z : Set G)) (hZ : IsPGroup 3 ↥Z) :
    CFSG.pPrimeCore 3 (R891Star H Z) = ⊥ := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K0 : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let Z' : Subgroup ↥H := Z.subgroupOf H
  have hZc : Z' ≤ Subgroup.center ↥H := k891gpprime_zcenter hHZ
  have hZ'n : Z'.Normal := Subgroup.normal_of_le_center hZc
  have hZp : IsPGroup 3 Z' := k891gpprime_zpgroup H hZ
  have hKer : R891Ker H Z = K0 ⊔ Z' := k891gpprime_ker_eq hHZ
  have hK0le : K0 ≤ R891Ker H Z := by rw [hKer]; exact le_sup_left
  let Q := ↥H ⧸ K0
  have hQcore : CFSG.pPrimeCore 3 Q = ⊥ := by
    show CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pPrimeCore 3 ↥H) = ⊥
    exact CFSG.pPrimeCore_quotient_eq_bot (G := ↥H) (p := 3) Nat.prime_three
  let Zb : Subgroup Q := (R891Ker H Z).map (QuotientGroup.mk' K0)
  have hZbEq : Zb = Z'.map (QuotientGroup.mk' K0) := by
    show (R891Ker H Z).map (QuotientGroup.mk' K0) = Z'.map (QuotientGroup.mk' K0)
    rw [hKer, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hZbn : Zb.Normal := by
    rw [hZbEq]
    exact (Subgroup.normal_of_le_center hZc).map (QuotientGroup.mk' K0)
      (QuotientGroup.mk'_surjective K0)
  have hZbc : Zb ≤ Subgroup.center Q := by
    rw [hZbEq]
    exact (Subgroup.map_mono (f := QuotientGroup.mk' K0) hZc).trans
      (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective K0))
  have hZbp : IsPGroup 3 Zb := by
    rw [hZbEq]
    exact IsPGroup.map hZp (QuotientGroup.mk' K0)
  have hZb : CFSG.pPrimeCore 3 (Q ⧸ Zb) = ⊥ := by
    rw [CFSG.central_p_subgroup_prime_core_quotient Zb hZbc hZbp, hQcore, Subgroup.map_bot]
  have hiso : (Q ⧸ Zb) ≃* (↥H ⧸ R891Ker H Z) :=
    QuotientGroup.quotientQuotientEquivQuotient K0 (R891Ker H Z) hK0le
  exact CFSG.pPrimeCore_eq_bot_of_mulEquiv 3 hiso hZb

private theorem k891ginfker_subgroupOf_normal {G : Type} [Group G] {H Z : Subgroup G}
    (hHZ : H ≤ centralizer (Z : Set G)) : (Z.subgroupOf H).Normal := by
  refine ⟨fun z hz k => ?_⟩
  have hcomm : (z : G) * (k : G) = (k : G) * (z : G) :=
    Subgroup.mem_centralizer_iff.mp (hHZ k.2) (z : G) hz
  change (k : G) * (z : G) * (k : G)⁻¹ ∈ Z
  rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact hz

private theorem k891ginfker_ker_eq {G : Type} [Group G] [Finite G] {H Z : Subgroup G}
    (hHZ : H ≤ centralizer (Z : Set G)) :
    R891Ker H Z = CFSG.pPrimeCore 3 ↥H ⊔ Z.subgroupOf H := by
  have hZn : (Z.subgroupOf H).Normal := k891ginfker_subgroupOf_normal hHZ
  rw [R891Ker, Subgroup.normalClosure_union, Subgroup.normalClosure_eq_self,
    Subgroup.normalClosure_eq_self]

private theorem k891ginfker_eq_one_of_mem_inf {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {K0 R' : Subgroup ↥H} (hK0 : Nat.Coprime 3 (Nat.card K0))
    (hR' : IsPGroup 3 R') {k : ↥H} (hk0 : k ∈ K0) (hkR : k ∈ R') : k = 1 := by
  obtain ⟨m, hm⟩ := (isPGroup_iff_orderOf_dvd_pow.mp hR') ⟨k, hkR⟩
  rw [Subgroup.orderOf_mk k hkR] at hm
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left m hK0) hm (K0.orderOf_dvd_natCard hk0))

theorem r891g211_inf_ker {G : Type} [Group G] [Finite G] {H Z R : Subgroup G}
    (hHZ : H ≤ centralizer (Z : Set G)) (hR : IsPGroup 3 ↥R) (hZR : Z ≤ R) :
    R.subgroupOf H ⊓ R891Ker H Z = Z.subgroupOf H := by
  rw [k891ginfker_ker_eq hHZ]
  refine le_antisymm ?_ (le_inf (Subgroup.subgroupOf_mono H hZR) le_sup_right)
  intro x hx
  have hxR : x ∈ R.subgroupOf H := hx.1
  obtain ⟨k, hk, z, hz, hkz⟩ := Subgroup.mem_sup_of_normal_left.mp hx.2
  have hzR : z ∈ R.subgroupOf H := Subgroup.subgroupOf_mono H hZR hz
  have hkR : k ∈ R.subgroupOf H := by
    have hkx : k = x * z⁻¹ := by
      rw [← hkz]
      group
    rw [hkx]
    exact mul_mem hxR (inv_mem hzR)
  have hk1 : k = 1 :=
    k891ginfker_eq_one_of_mem_inf
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
      (hR.comap_subtype (K := H)) hk hkR
  rw [← hkz, hk1, one_mul]
  exact hz

private theorem k891geinff_ker_eq {G : Type} [Group G] [Finite G] {H Z : Subgroup G}
    (hHZ : H ≤ centralizer (Z : Set G)) :
    R891Ker H Z = CFSG.pPrimeCore 3 ↥H ⊔ Z.subgroupOf H := by
  have hZc : Z.subgroupOf H ≤ Subgroup.center ↥H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx' : (x : G) ∈ Z := hx
    have hcomm : (x : G) * (y : G) = (y : G) * (x : G) :=
      Subgroup.mem_centralizer_iff.mp (hHZ y.2) (x : G) hx'
    simpa using hcomm.symm
  have hZn : (Z.subgroupOf H).Normal := Subgroup.normal_of_le_center hZc
  show Subgroup.normalClosure ((CFSG.pPrimeCore 3 ↥H : Set ↥H) ∪ (Z.subgroupOf H : Set ↥H)) = _
  rw [Subgroup.normalClosure_union]
  simp

private theorem k891geinff_W_le_M {G : Type} [Group G] [Finite G]
    {H Z R P0 M : Subgroup G} (hHZ : H ≤ centralizer (Z : Set G)) (hZH : Z ≤ H)
    (hZR : Z ≤ R) (hRP0 : R ≤ P0) (hP0 : IsSylowOf 3 P0 H) (hP0M : P0 ≤ M)
    (hK0M : (CFSG.pPrimeCore 3 ↥H).map H.subtype ≤ M) :
    ((CFSG.pCore 3 (R891Star H Z)).comap (QuotientGroup.mk' (R891Ker H Z))).map H.subtype ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Ker : Subgroup ↥H := R891Ker H Z
  let F : Subgroup (R891Star H Z) := CFSG.pCore 3 (R891Star H Z)
  let V : Subgroup ↥H := F.comap (QuotientGroup.mk' Ker)
  let W : Subgroup G := V.map H.subtype
  have hK : Ker = CFSG.pPrimeCore 3 ↥H ⊔ Z.subgroupOf H := k891geinff_ker_eq hHZ
  have hZ'leKer : Z.subgroupOf H ≤ Ker := by
    intro x hx
    exact Subgroup.subset_normalClosure (Set.mem_union_right _ hx)
  have hKerleV : Ker ≤ V := by
    intro k hk
    rw [Subgroup.mem_comap]
    have hk' : (QuotientGroup.mk' Ker) k = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hk
    rw [hk']
    exact F.one_mem
  have hZ'leV : Z.subgroupOf H ≤ V := hZ'leKer.trans hKerleV
  have hZmap : (Z.subgroupOf H).map H.subtype = Z := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZH]
  have hZW : Z ≤ W := by
    rw [← hZmap]
    exact Subgroup.map_mono hZ'leV
  have hWH : W ≤ H := Subgroup.map_subtype_le V
  have hVnormal : V.Normal := (CFSG.pCore_normal (p := 3) (G := R891Star H Z)).comap _
  have hWsub : W.subgroupOf H = V := by
    show Subgroup.comap H.subtype W = V
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective V]
  have hHnormW : H ≤ Subgroup.normalizer (W : Set G) := by
    have hWn : (W.subgroupOf H).Normal := by rw [hWsub]; exact hVnormal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mp hWn
  have hS0W : IsSylowOf 3 (P0 ⊓ W) W := IsSylowOf.inf_of_le_normalizer hP0 hWH hHnormW
  have hS0H : P0 ⊓ W ≤ H := inf_le_right.trans hWH
  have hS0'V : IsSylowOf 3 ((P0 ⊓ W).subgroupOf H) V := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := H)
      (A := (P0 ⊓ W).subgroupOf H) (B := V)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS0H] using hS0W
  obtain ⟨Q, hQ⟩ := hS0'V.exists_sylow_eq_subgroupOf
  have hQmap : ((Q : Subgroup ↥V).map V.subtype) = (P0 ⊓ W).subgroupOf H := by
    rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS0'V.le]
  let g : ↥V →* ↥F := MonoidHom.codRestrict ((QuotientGroup.mk' Ker).comp V.subtype) F
    (fun x => x.2)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective Ker (y : R891Star H Z)
    refine ⟨⟨z, ?_⟩, ?_⟩
    · show (QuotientGroup.mk' Ker) z ∈ F
      rw [hz]
      exact y.2
    · apply Subtype.ext
      show (QuotientGroup.mk' Ker) z = (y : R891Star H Z)
      exact hz
  have htopF : IsPGroup 3 ↥(⊤ : Subgroup ↥F) :=
    (CFSG.pCore_isPGroup (p := 3) (G := R891Star H Z)).of_equiv
      (Subgroup.topEquiv (G := ↥F)).symm
  have hQtop : ((Q.mapSurjective hg : Sylow 3 ↥F) : Subgroup ↥F) = ⊤ :=
    ((Q.mapSurjective hg).is_maximal' htopF le_top).symm
  have hVle : V ≤ Ker ⊔ (P0 ⊓ W).subgroupOf H := by
    intro v hv
    have hvtop : g ⟨v, hv⟩ ∈ ((Q.mapSurjective hg : Sylow 3 ↥F) : Subgroup ↥F) := by
      rw [hQtop]; trivial
    rw [Sylow.coe_mapSurjective] at hvtop
    obtain ⟨s, hsQ, hgs⟩ := Subgroup.mem_map.mp hvtop
    rw [hQ] at hsQ
    have hsS0 : ((s : ↥V) : ↥H) ∈ (P0 ⊓ W).subgroupOf H := hsQ
    have hpi : (QuotientGroup.mk' Ker) ((s : ↥V) : ↥H) =
        (QuotientGroup.mk' Ker) ((⟨v, hv⟩ : ↥V) : ↥H) := by
      have := congrArg (fun x : ↥F => (x : R891Star H Z)) hgs
      simpa [g, MonoidHom.codRestrict, MonoidHom.comp_apply] using this
    have hk : ((s : ↥V) : ↥H) * ((⟨v, hv⟩ : ↥V) : ↥H)⁻¹ ∈ Ker := by
      rw [← QuotientGroup.ker_mk' Ker]
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpi, mul_inv_cancel]
    have hv_eq : ((⟨v, hv⟩ : ↥V) : ↥H) =
        (((s : ↥V) : ↥H) * ((⟨v, hv⟩ : ↥V) : ↥H)⁻¹)⁻¹ * ((s : ↥V) : ↥H) := by
      group
    show ((⟨v, hv⟩ : ↥V) : ↥H) ∈ Ker ⊔ (P0 ⊓ W).subgroupOf H
    rw [hv_eq]
    exact Subgroup.mul_mem_sup (inv_mem hk) hsS0
  calc W = V.map H.subtype := rfl
    _ ≤ (Ker ⊔ (P0 ⊓ W).subgroupOf H).map H.subtype := Subgroup.map_mono hVle
    _ = Ker.map H.subtype ⊔ ((P0 ⊓ W).subgroupOf H).map H.subtype :=
        Subgroup.map_sup _ _ H.subtype
    _ ≤ M := by
      apply sup_le
      · rw [hK, Subgroup.map_sup]
        apply sup_le hK0M
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZH]
        exact (le_inf (hZR.trans hRP0) hZW).trans (inf_le_left.trans hP0M)
      · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS0H]
        exact inf_le_left.trans hP0M

private theorem k891geinff_H_le_M {G : Type} [Group G] [Finite G]
    {H Z P0 M : Subgroup G} (hP0 : IsSylowOf 3 P0 H)
    (hWM : ((CFSG.pCore 3 (R891Star H Z)).comap
      (QuotientGroup.mk' (R891Ker H Z))).map H.subtype ≤ M)
    (hNM : Subgroup.normalizer (P0 ⊓ ((CFSG.pCore 3 (R891Star H Z)).comap
      (QuotientGroup.mk' (R891Ker H Z))).map H.subtype : Set G) ≤ M) :
    H ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Ker : Subgroup ↥H := R891Ker H Z
  let F : Subgroup (R891Star H Z) := CFSG.pCore 3 (R891Star H Z)
  let V : Subgroup ↥H := F.comap (QuotientGroup.mk' Ker)
  let W : Subgroup G := V.map H.subtype
  let S0 : Subgroup G := P0 ⊓ W
  have hWM' : W ≤ M := hWM
  have hNM' : Subgroup.normalizer (S0 : Set G) ≤ M := hNM
  have hVnormal : V.Normal := (CFSG.pCore_normal (p := 3) (G := R891Star H Z)).comap _
  have hWH : W ≤ H := Subgroup.map_subtype_le V
  have hWsub : W.subgroupOf H = V := by
    show Subgroup.comap H.subtype W = V
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective V]
  have hHnormW : H ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mp (by rw [hWsub]; infer_instance)
  have hS0W : IsSylowOf 3 S0 W := IsSylowOf.inf_of_le_normalizer hP0 hWH hHnormW
  have hS0H : S0 ≤ H := inf_le_right.trans hWH
  have hS0'V : IsSylowOf 3 (S0.subgroupOf H) V := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := H)
      (A := S0.subgroupOf H) (B := V)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS0H] using hS0W
  obtain ⟨Q, hQ⟩ := hS0'V.exists_sylow_eq_subgroupOf
  have hQmap : ((Q : Subgroup ↥V).map V.subtype) = S0.subgroupOf H := by
    rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS0'V.le]
  have hFratt : Subgroup.normalizer (S0.subgroupOf H) ⊔ V = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top Q
    rwa [hQmap] at h
  intro h hh
  have hh_fratt : (⟨h, hh⟩ : ↥H) ∈ Subgroup.normalizer (S0.subgroupOf H) ⊔ V := by
    rw [hFratt]; trivial
  obtain ⟨n, hn, v, hv, hnv⟩ := Subgroup.mem_sup_of_normal_right.mp hh_fratt
  have hnG : (n : G) ∈ Subgroup.normalizer (S0 : Set G) := by
    have hn' : n ∈ Subgroup.normalizer (S0.subgroupOf H) := hn
    rwa [← Subgroup.subgroupOf_normalizer_eq hS0H] at hn'
  have hvG : (v : G) ∈ W := ⟨v, hv, rfl⟩
  have hnvG : (n : G) * (v : G) = h := by
    have := congrArg (fun x : ↥H => (x : G)) hnv
    simpa using this
  rw [← hnvG]
  exact M.mul_mem (hNM' hnG) (hWM' hvG)

theorem r891g211_e_inf_f {G : Type} [Group G] [Finite G] (D : Data G) {L S R A P0 : Subgroup G}
    (hst : R891State D L S R A 1) (hgam : R891Gamma895 D L S R)
    (huniq : ∀ W : Subgroup G, R891Z L S < W → W ≤ R → W ∈ uniqueSet D.M)
    (hP0 : IsSylowOf 3 P0 (R891H L S)) (hRP0 : R ≤ P0) (hP0M : P0 ≤ D.M) :
    R891Img (R891H L S) (R891Z L S) R ⊓ CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHZ : R891H L S ≤ centralizer (R891Z L S : Set G) := le_rfl
  have hZH : R891Z L S ≤ R891H L S := by
    intro z hz
    change z ∈ centralizer (R891Z L S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hzcent : z ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) :=
      (show z ∈ ZOf (S ⊓ L) from hz).2
    exact Subgroup.mem_centralizer_iff.mp hzcent w ((show w ∈ ZOf (S ⊓ L) from hw).1)
  let Ker : Subgroup ↥(R891H L S) := R891Ker (R891H L S) (R891Z L S)
  let F : Subgroup (R891Star (R891H L S) (R891Z L S)) :=
    CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S))
  let V : Subgroup ↥(R891H L S) := F.comap (QuotientGroup.mk' Ker)
  let W : Subgroup G := V.map (R891H L S).subtype
  have hZW : R891Z L S ≤ W := by
    have hZ'leKer : (R891Z L S).subgroupOf (R891H L S) ≤ Ker := by
      intro x hx
      exact Subgroup.subset_normalClosure (Set.mem_union_right _ hx)
    have hKerleV : Ker ≤ V := by
      intro k hk
      rw [Subgroup.mem_comap]
      have hk' : (QuotientGroup.mk' Ker) k = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hk
      rw [hk']
      exact F.one_mem
    have hZmap : ((R891Z L S).subgroupOf (R891H L S)).map (R891H L S).subtype = R891Z L S := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZH]
    rw [← hZmap]
    exact Subgroup.map_mono (hZ'leKer.trans hKerleV)
  by_contra hne
  rcases Subgroup.bot_or_exists_ne_one
    (R891Img (R891H L S) (R891Z L S) R ⊓
      CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S))) with hbot | ⟨e, he, he1⟩
  · exact hne hbot
  · have heE : e ∈ R891Img (R891H L S) (R891Z L S) R := he.1
    have heF : e ∈ F := he.2
    obtain ⟨r', hr', hpi⟩ := Subgroup.mem_map.mp heE
    have hrR : (r' : G) ∈ R := hr'
    have hr'V : r' ∈ V := by
      rw [Subgroup.mem_comap]
      rw [hpi]
      exact heF
    have hrW : (r' : G) ∈ W := ⟨r', hr'V, rfl⟩
    have hr_notZ : (r' : G) ∉ R891Z L S := by
      intro hrZ
      have hr'Z : r' ∈ (R891Z L S).subgroupOf (R891H L S) :=
        Subgroup.mem_subgroupOf.mpr hrZ
      have hmem : r' ∈ Ker :=
        Subgroup.subset_normalClosure (Set.mem_union_right _ hr'Z)
      have hroot : (QuotientGroup.mk' Ker) r' = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hmem
      exact he1 (hpi.symm.trans hroot)
    have hZleRW : R891Z L S ≤ R ⊓ W := le_inf hst.ctx.xShape.zLe hZW
    have hZlt : R891Z L S < R ⊓ W := by
      refine lt_of_le_of_ne hZleRW ?_
      intro heq
      exact hr_notZ (heq ▸ ⟨hrR, hrW⟩)
    have hUniqRW : R ⊓ W ∈ uniqueSet D.M := huniq (R ⊓ W) hZlt inf_le_left
    have hS0uniq : P0 ⊓ W ∈ uniqueSet D.M :=
      CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hUniqRW
        (le_inf (inf_le_left.trans hRP0) inf_le_right)
        (inf_le_left.trans hP0M)
    have hN : Subgroup.normalizer ((P0 ⊓ W : Subgroup G) : Set G) ≤ D.M :=
      CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hS0uniq
    have hWleM : W ≤ D.M :=
      k891geinff_W_le_M (H := R891H L S) (Z := R891Z L S) hHZ hZH
        hst.ctx.xShape.zLe hRP0 hP0 hP0M hgam.2.2
    have hHleM : R891H L S ≤ D.M :=
      k891geinff_H_le_M (H := R891H L S) (Z := R891Z L S) hP0 hWleM hN
    exact hst.f893.normZ.2.2 hHleM

private lemma k891gcentgam_zpowers_elemAbelian {J0 : Type} [Group J0] {a : J0}
    (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) : IsElemAbelian 3 (Subgroup.zpowers a) := by
  have horder : orderOf a = 3 := orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩) ha3 ha1
  refine ⟨inferInstance, ?_⟩
  intro x hx
  have hdvd : orderOf x ∣ 3 := by
    rw [← horder]
    exact orderOf_dvd_of_mem_zpowers hx
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

theorem centralizer_le_rankThreeGamma_of_pow_three {J0 : Type} [Group J0] [Finite J0]
    {E : Subgroup J0} {a : J0} (ha : a ∈ E) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) :
    centralizer ({a} : Set J0) ≤ rankThreeGamma 1 3 E := by
  have hQle : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.mpr ha
  have horder : orderOf a = 3 := orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩) ha3 ha1
  have hcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, horder]
  have h1 : (1 : ℕ) ≤ CFSG.Open.pRank (G := J0) 3 (Subgroup.zpowers a) :=
    CFSG.SectionRank.le_pRank (G := J0) (p := 3) (H := Subgroup.zpowers a)
      (E := Subgroup.zpowers a) (k := 1) (show 1 < 3 by norm_num) le_rfl
      (k891gcentgam_zpowers_elemAbelian ha1 ha3) (by rw [hcard]; norm_num)
  have hnorm : Subgroup.normalizer (Subgroup.zpowers a : Set J0) ≤ rankThreeGamma 1 3 E := by
    rw [rankThreeGamma]
    exact le_sSup ⟨Subgroup.zpowers a, hQle, h1, rfl⟩
  calc
    centralizer ({a} : Set J0) = Subgroup.normalizer ({a} : Set J0) :=
      (Subgroup.normalizer_singleton a).symm
    _ ≤ Subgroup.normalizer (Subgroup.zpowers a : Set J0) := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.normalizer_le_normalizer_closure {a}
    _ ≤ rankThreeGamma 1 3 E := hnorm

private theorem k891gkgroup_center_eq_bot {G : Type} [Group G] [Finite G] (D : Data G) :
    center G = ⊥ := by
  rcases D.standing.simple.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := D.standing.nonab
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

private theorem k891gkgroup_z_ne_bot {G : Type} [Group G] [Finite G] (D : Data G)
    {L S : Subgroup G} (hb : R891Basic D L S) : R891Z L S ≠ ⊥ := by
  intro hbot
  have h3 : Nat.card (⊥ : Subgroup G) = 3 := by
    rw [← hbot]
    exact hb.zOrder
  rw [Subgroup.card_bot] at h3
  omega

private theorem k891gkgroup_H_ne_top {G : Type} [Group G] [Finite G] (D : Data G)
    {L S : Subgroup G} (hb : R891Basic D L S) : R891H L S ≠ ⊤ := by
  intro hH
  have hZle : R891Z L S ≤ center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp hH
  have hZbot : R891Z L S = ⊥ :=
    le_bot_iff.mp (hZle.trans (le_of_eq (k891gkgroup_center_eq_bot D)))
  exact k891gkgroup_z_ne_bot D hb hZbot

theorem r891g211_kgroup_star {G : Type} [Group G] [Finite G] (D : Data G) {L S : Subgroup G}
    (hb : R891Basic D L S) : CFSG.Open.IsKGroup (R891Star (R891H L S) (R891Z L S)) := by
  have hKG : CFSG.Open.IsKGroup ↥(R891H L S) :=
    D.standing.kProper.isKGroup (R891H L S) (k891gkgroup_H_ne_top D hb)
  exact hKG.quotient (R891Ker (R891H L S) (R891Z L S))

private theorem k891gstarsyl_IsSylowOf_map {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Y : Type} [Group Y] {P B : Subgroup X} (h : IsSylowOf p P B) (φ : X →* Y) :
    IsSylowOf p (P.map φ) (B.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (φ.subgroupMap_surjective B), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem k891gstarsyl_image_mono {G : Type} [Group G] [Finite G] {H Z A B : Subgroup G}
    (h : A ≤ B) : R891Img H Z A ≤ R891Img H Z B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H h)

private theorem k891gstarsyl_sylow_top {G : Type} [Group G] [Finite G] {H Z P0 : Subgroup G}
    (hP0 : IsSylowOf 3 P0 H) : IsSylowOf 3 (R891Img H Z P0) ⊤ := by
  have hP0sub : IsSylowOf 3 (P0.subgroupOf H) (⊤ : Subgroup ↥H) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H]
    rw [Subgroup.map_subgroupOf_eq_of_le hP0.le, Subgroup.map_top, Subgroup.range_subtype]
    exact hP0
  have h := k891gstarsyl_IsSylowOf_map hP0sub (QuotientGroup.mk' (R891Ker H Z))
  rwa [Subgroup.map_top_of_surjective (QuotientGroup.mk' (R891Ker H Z))
    (QuotientGroup.mk'_surjective (R891Ker H Z))] at h

private theorem k891gstarsyl_sylow_rel {G : Type} [Group G] [Finite G] {H Z R X : Subgroup G}
    (hRX : IsSylowOf 3 R X) (hRH : R ≤ H) :
    IsSylowOf 3 (R891Img H Z R) (R891Img H Z X) := by
  have hRsub : IsSylowOf 3 (R.subgroupOf H) (X.subgroupOf H) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H]
    rw [Subgroup.map_subgroupOf_eq_of_le hRH, Subgroup.subgroupOf_map_subtype]
    exact hRX.of_le (le_inf hRX.le hRH) inf_le_left
  exact k891gstarsyl_IsSylowOf_map hRsub (QuotientGroup.mk' (R891Ker H Z))

theorem r891g211_star_sylow {G : Type} [Group G] [Finite G] {H Z R X P0 M : Subgroup G}
    (hXs : IsSolvable ↥X) (hRX : IsSylowOf 3 R X) (hP0 : IsSylowOf 3 P0 H) (hRP0 : R ≤ P0)
    (hP0M : P0 ≤ M) :
    IsSylowOf 3 (R891Img H Z P0) ⊤ ∧ R891Img H Z P0 ≤ R891Img H Z M ∧
      R891Img H Z R = R891Img H Z P0 ⊓ R891Img H Z X ∧ IsSolvable ↥(R891Img H Z X) := by
  have : Group.IsSolvable ↥X := hXs
  have hRH : R ≤ H := hRP0.trans hP0.le
  have : Group.IsSolvable ↥(X ⊓ H : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : X ⊓ H ≤ X))
      (Subgroup.inclusion_injective inf_le_left)
  have : Group.IsSolvable ↥(X.subgroupOf H) := by
    rw [← Subgroup.inf_subgroupOf_right X H]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ H ≤ H)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ H ≤ H)).injective
  refine ⟨k891gstarsyl_sylow_top hP0, k891gstarsyl_image_mono hP0M, ?_, ?_⟩
  · refine le_antisymm (le_inf (k891gstarsyl_image_mono hRP0) (k891gstarsyl_image_mono hRX.le)) ?_
    have hQ : IsPGroup 3 (R891Img H Z P0 ⊓ R891Img H Z X : Subgroup (R891Star H Z)) :=
      (k891gstarsyl_sylow_top hP0).isPGroup.to_le inf_le_left
    exact (IsSylowOf.eq_of_le (k891gstarsyl_sylow_rel hRX hRH)
      (le_inf (k891gstarsyl_image_mono hRP0) (k891gstarsyl_image_mono hRX.le))
      inf_le_right hQ).le
  · exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (R891Ker H Z)).subgroupMap (X.subgroupOf H))
      (MonoidHom.subgroupMap_surjective _ _)

private theorem k891gstare_ZOf_eq_map {G : Type} [Group G] (Q : Subgroup G) :
    ZOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext x
  rw [ZOf, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hxQ, hx⟩
    exact ⟨⟨x, hxQ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hx y y.2), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun h hh => congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)⟩

private theorem k891gstare_card_ZOf {G : Type} [Group G] {Q : Subgroup G}
    (hQ : IsExtraspecialExpP 3 1 ↥Q) : Nat.card (ZOf Q) = 3 := by
  rw [k891gstare_ZOf_eq_map, Subgroup.card_map_of_injective Q.subtype_injective]
  exact hQ.2.2.2

open scoped commutatorElement in
private theorem k891gstare_commutator_mem_ZOf {G : Type} [Group G] {R H : Subgroup G}
    (hR : commutator ↥R = Subgroup.center ↥R) {x y : ↥H}
    (hx : (x : G) ∈ R) (hy : (y : G) ∈ R) :
    ((⁅x, y⁆ : ↥H) : G) ∈ ZOf R := by
  let xR : ↥R := ⟨(x : G), hx⟩
  let yR : ↥R := ⟨(y : G), hy⟩
  have hcenter : ⁅xR, yR⁆ ∈ Subgroup.center ↥R := by
    rw [← hR, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top xR) (Subgroup.mem_top yR)
  have hZOf : ((⁅xR, yR⁆ : ↥R) : G) ∈ ZOf R := by
    rw [k891gstare_ZOf_eq_map]
    exact Subgroup.mem_map_of_mem R.subtype hcenter
  have hcoe : ((⁅x, y⁆ : ↥H) : G) = ((⁅xR, yR⁆ : ↥R) : G) := by
    simp [commutatorElement_def, xR, yR]
  rwa [hcoe]

private theorem k891gstare_im_ne_bot {G : Type} [Group G] [Finite G] {H Z R : Subgroup G}
    (hZ : ZOf R = Z) (hRH : R ≤ H) (hR : IsExtraspecialExpP 3 1 ↥R)
    (hRK : R.subgroupOf H ⊓ R891Ker H Z = Z.subgroupOf H) :
    R891Img H Z R ≠ ⊥ := by
  intro hbot
  have hle : R.subgroupOf H ≤ R891Ker H Z := by
    intro x hx
    have hmem : QuotientGroup.mk' (R891Ker H Z) x ∈ R891Img H Z R :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff (N := R891Ker H Z) x).mp hmem
  have hZR : Z ≤ R := by
    rw [← hZ]
    exact inf_le_left
  have hsub : R.subgroupOf H = Z.subgroupOf H :=
    (inf_eq_left.mpr hle).symm.trans hRK
  have hRZ : R = Z := by
    have h1 : R ⊓ H = Z ⊓ H := Subgroup.subgroupOf_inj.mp hsub
    rwa [inf_eq_left.mpr hRH, inf_eq_left.mpr (hZR.trans hRH)] at h1
  have hcardR : Nat.card R = 27 := by
    rw [hR.1]
    norm_num
  have hcardZ : Nat.card Z = 3 := by
    rw [← hZ]
    exact k891gstare_card_ZOf hR
  rw [hRZ, hcardZ] at hcardR
  exact absurd hcardR (by norm_num)

open scoped commutatorElement in
private theorem k891gstare_im_comm {G : Type} [Group G] [Finite G] {H Z R : Subgroup G}
    (hZ : ZOf R = Z) (hR : IsExtraspecialExpP 3 1 ↥R) :
    ∀ a ∈ R891Img H Z R, ∀ b ∈ R891Img H Z R, a * b = b * a := by
  intro a ha b hb
  rw [R891Img, Subgroup.mem_map] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine Subgroup.subset_normalClosure (Or.inr ?_)
  change ((⁅x, y⁆ : ↥H) : G) ∈ Z
  rw [← hZ]
  exact k891gstare_commutator_mem_ZOf hR.2.2.1 (Subgroup.mem_subgroupOf.mp hx)
    (Subgroup.mem_subgroupOf.mp hy)

private theorem k891gstare_pow_three {G : Type} [Group G] [Finite G] {H Z R : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) :
    ∀ a ∈ R891Img H Z R, a ^ 3 = 1 := by
  intro a ha
  rw [R891Img, Subgroup.mem_map] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  have hxR : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hx
  have hpow : (⟨(x : G), hxR⟩ : ↥R) ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨(x : G), hxR⟩ : ↥R)
    rwa [hR.2.1] at h
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simpa using congrArg (fun z : ↥R => (z : G)) hpow
  rw [← map_pow, hx3, map_one]

theorem r891g211_star_e {G : Type} [Group G] [Finite G] {H Z R : Subgroup G}
    (hZ : ZOf R = Z) (hRH : R ≤ H) (hR : IsExtraspecialExpP 3 1 ↥R)
    (hRK : R.subgroupOf H ⊓ R891Ker H Z = Z.subgroupOf H) :
    R891Img H Z R ≠ ⊥ ∧ (∀ a ∈ R891Img H Z R, ∀ b ∈ R891Img H Z R, a * b = b * a) ∧
      ∀ a ∈ R891Img H Z R, a ^ 3 = 1 := by
  exact ⟨k891gstare_im_ne_bot hZ hRH hR hRK, k891gstare_im_comm hZ hR,
    k891gstare_pow_three hR⟩

private theorem k891gstarshp_mk_eq_one_of_mem_Z {G : Type} [Group G] [Finite G] {H Z : Subgroup G}
    {z : ↥H} (hz : z ∈ Z.subgroupOf H) :
    QuotientGroup.mk' (R891Ker H Z) z = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure (Set.mem_union_right (CFSG.pPrimeCore 3 ↥H) hz)

private theorem k891gstarshp_conj_mem {G : Type} [Group G] [Finite G] {H Z R T0 : Subgroup G}
    (hTN : T0 ≤ normalizer (R : Set G)) :
    ∀ u ∈ R891Img H Z T0, ∀ e ∈ R891Img H Z R, u * e * u⁻¹ ∈ R891Img H Z R := by
  intro u hu e he
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
  have hu'G : (u' : G) ∈ T0 := Subgroup.mem_subgroupOf.mp hu'
  have he'G : (e' : G) ∈ R := Subgroup.mem_subgroupOf.mp he'
  have hmem : u' * e' * u'⁻¹ ∈ R.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_set_normalizer_iff.mp (hTN hu'G) (e' : G)).mp he'G
  have hEq : QuotientGroup.mk' (R891Ker H Z) u' * QuotientGroup.mk' (R891Ker H Z) e' *
        (QuotientGroup.mk' (R891Ker H Z) u')⁻¹ =
      QuotientGroup.mk' (R891Ker H Z) (u' * e' * u'⁻¹) := by
    simp only [map_mul, map_inv]
  rw [hEq]
  exact Subgroup.mem_map_of_mem _ hmem

private theorem k891gstarshp_normalizes {G : Type} [Group G] [Finite G] {H Z R T0 : Subgroup G}
    (hTN : T0 ≤ normalizer (R : Set G)) :
    R891Img H Z T0 ≤
      normalizer ((R891Img H Z R : Subgroup (R891Star H Z)) : Set (R891Star H Z)) := by
  intro t ht
  rw [Subgroup.mem_set_normalizer_iff]
  intro e
  constructor
  · exact k891gstarshp_conj_mem hTN t ht e
  · intro he
    have h2 := k891gstarshp_conj_mem hTN t⁻¹ (Subgroup.inv_mem _ ht) (t * e * t⁻¹) he
    rwa [show t⁻¹ * (t * e * t⁻¹) * (t⁻¹)⁻¹ = e by group] at h2

private theorem k891gstarshp_irreducible {G : Type} [Group G] [Finite G] {H Z R T0 : Subgroup G}
    (hZ : ZOf R = Z) (hRH : R ≤ H) (hT0H : T0 ≤ H)
    (hTN : T0 ≤ normalizer (R : Set G))
    (hirr : ∀ W : Subgroup G, ZOf R ≤ W → W ≤ R → T0 ≤ normalizer (W : Set G) →
      W = ZOf R ∨ W = R) :
    ∀ W : Subgroup (R891Star H Z), W ≤ R891Img H Z R →
      R891Img H Z T0 ≤ normalizer (W : Set (R891Star H Z)) → W = ⊥ ∨ W = R891Img H Z R := by
  intro W hWE hWT
  have hZR : Z ≤ R := by rw [← hZ]; exact inf_le_left
  have hZH : Z ≤ H := hZR.trans hRH
  set W1 : Subgroup G := R ⊓ (W.comap (QuotientGroup.mk' (R891Ker H Z))).map H.subtype
    with hW1def
  have hZleW1 : ZOf R ≤ W1 := by
    intro z hz
    rw [hW1def, Subgroup.mem_inf]
    refine ⟨hZR (hZ ▸ hz), ?_⟩
    refine Subgroup.mem_map.mpr ⟨⟨z, hZH (hZ ▸ hz)⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, k891gstarshp_mk_eq_one_of_mem_Z (Subgroup.mem_subgroupOf.mpr (hZ ▸ hz))]
    exact W.one_mem
  have hW1leR : W1 ≤ R := by rw [hW1def]; exact inf_le_left
  have hstep : ∀ u ∈ T0, ∀ n ∈ W1, u * n * u⁻¹ ∈ W1 := by
    intro u hu n hn
    have huH : u ∈ H := hT0H hu
    rw [hW1def, Subgroup.mem_inf] at hn
    obtain ⟨hnR, hnM⟩ := hn
    rw [hW1def, Subgroup.mem_inf]
    refine ⟨(Subgroup.mem_set_normalizer_iff.mp (hTN hu) n).mp hnR, ?_⟩
    obtain ⟨v, hv, hv_eq⟩ := Subgroup.mem_map.mp hnM
    refine Subgroup.mem_map.mpr ⟨⟨u, huH⟩ * v * ⟨u, huH⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_comap] at hv ⊢
      have hmemT : QuotientGroup.mk' (R891Ker H Z) ⟨u, huH⟩ ∈ R891Img H Z T0 :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
      have hnorm := (Subgroup.mem_set_normalizer_iff.mp (hWT hmemT))
        (QuotientGroup.mk' (R891Ker H Z) v)
      simpa only [map_mul, map_inv, SetLike.mem_coe] using hnorm.mp hv
    · have hv_eq' : (v : G) = n := hv_eq
      simp only [map_mul, map_inv, hv_eq', Subgroup.subtype_apply]
  have hT0W1 : T0 ≤ normalizer (W1 : Set G) := by
    intro u hu
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · exact hstep u hu n
    · intro hn
      have h2 := hstep u⁻¹ (T0.inv_mem hu) (u * n * u⁻¹) hn
      rwa [show u⁻¹ * (u * n * u⁻¹) * (u⁻¹)⁻¹ = n by group] at h2
  rcases hirr W1 hZleW1 hW1leR hT0W1 with hW1 | hW1
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp (hWE hw)
    have hr'W1 : (r' : G) ∈ W1 := by
      refine ⟨Subgroup.mem_subgroupOf.mp hr', ?_⟩
      exact Subgroup.mem_map.mpr ⟨r', by rwa [Subgroup.mem_comap], rfl⟩
    have hzZ : (r' : G) ∈ Z := by
      rw [← hZ, ← hW1]
      exact hr'W1
    exact k891gstarshp_mk_eq_one_of_mem_Z (Subgroup.mem_subgroupOf.mpr hzZ)
  · right
    refine le_antisymm hWE ?_
    change (R.subgroupOf H).map (QuotientGroup.mk' (R891Ker H Z)) ≤ W
    rw [Subgroup.map_le_iff_le_comap]
    intro r' hr'
    rw [Subgroup.mem_comap]
    have hr'W1 : (r' : G) ∈ W1 := by
      rw [hW1]
      exact Subgroup.mem_subgroupOf.mp hr'
    have hr'map : (r' : G) ∈ (W.comap (QuotientGroup.mk' (R891Ker H Z))).map H.subtype := by
      have h := hr'W1
      rw [hW1def, Subgroup.mem_inf] at h
      exact h.2
    obtain ⟨v, hv, hv_eq⟩ := Subgroup.mem_map.mp hr'map
    rw [← Subgroup.subtype_injective H hv_eq]
    rw [Subgroup.mem_comap] at hv
    exact hv

private theorem k891gstarshp_inverts {G : Type} [Group G] [Finite G] {H Z R T0 : Subgroup G}
    (hZ : ZOf R = Z) (hT0H : T0 ≤ H)
    (hinv : ∃ t ∈ ⁅T0, T0⁆, ∀ r ∈ R, t * r * t⁻¹ * r ∈ ZOf R) :
    ∃ t ∈ ⁅R891Img H Z T0, R891Img H Z T0⁆,
      ∀ e ∈ R891Img H Z R, t * e * t⁻¹ = e⁻¹ := by
  obtain ⟨t, ht, htr⟩ := hinv
  have htmap : t ∈ (⁅T0.subgroupOf H, T0.subgroupOf H⁆).map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hT0H]
    exact ht
  obtain ⟨t', ht'c, ht'eq⟩ := Subgroup.mem_map.mp htmap
  refine ⟨QuotientGroup.mk' (R891Ker H Z) t', ?_, ?_⟩
  · have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (R891Ker H Z)) ht'c
    rwa [Subgroup.map_commutator] at hmem
  · intro e he
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp he
    have hr'G : (r' : G) ∈ R := Subgroup.mem_subgroupOf.mp hr'
    have hker : t' * r' * t'⁻¹ * r' ∈ Z.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have hZmem : t * (r' : G) * t⁻¹ * (r' : G) ∈ Z := hZ ▸ htr (r' : G) hr'G
      have hcoe : ((t' * r' * t'⁻¹ * r' : ↥H) : G) = t * (r' : G) * t⁻¹ * (r' : G) := by
        have ht'eq' : (t' : G) = t := ht'eq
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht'eq']
      rwa [hcoe]
    have hmul : QuotientGroup.mk' (R891Ker H Z) t' * QuotientGroup.mk' (R891Ker H Z) r' *
          (QuotientGroup.mk' (R891Ker H Z) t')⁻¹ * QuotientGroup.mk' (R891Ker H Z) r' = 1 := by
      rw [show QuotientGroup.mk' (R891Ker H Z) t' * QuotientGroup.mk' (R891Ker H Z) r' *
            (QuotientGroup.mk' (R891Ker H Z) t')⁻¹ * QuotientGroup.mk' (R891Ker H Z) r' =
          QuotientGroup.mk' (R891Ker H Z) (t' * r' * t'⁻¹ * r') by
        simp only [map_mul, map_inv]]
      exact k891gstarshp_mk_eq_one_of_mem_Z hker
    exact mul_eq_one_iff_eq_inv.mp hmul

theorem r891g211_star_shape {G : Type} [Group G] [Finite G] {H Z R T0 X : Subgroup G}
    (hZ : ZOf R = Z) (hRH : R ≤ H) (hT0X : T0 ≤ X) (hXH : X ≤ H)
    (hTN : T0 ≤ normalizer (R : Set G))
    (hirr : ∀ W : Subgroup G, ZOf R ≤ W → W ≤ R → T0 ≤ normalizer (W : Set G) →
      W = ZOf R ∨ W = R)
    (hinv : ∃ t ∈ ⁅T0, T0⁆, ∀ r ∈ R, t * r * t⁻¹ * r ∈ ZOf R) :
    R891Img H Z T0 ≤ R891Img H Z X ∧
      R891Img H Z T0 ≤
        normalizer ((R891Img H Z R : Subgroup (R891Star H Z)) : Set (R891Star H Z)) ∧
      (∀ W : Subgroup (R891Star H Z), W ≤ R891Img H Z R →
        R891Img H Z T0 ≤ normalizer (W : Set (R891Star H Z)) → W = ⊥ ∨ W = R891Img H Z R) ∧
      ∃ t ∈ ⁅R891Img H Z T0, R891Img H Z T0⁆, ∀ e ∈ R891Img H Z R, t * e * t⁻¹ = e⁻¹ := by
  have hT0H : T0 ≤ H := hT0X.trans hXH
  exact ⟨Subgroup.map_mono (Subgroup.subgroupOf_mono H hT0X),
    k891gstarshp_normalizes hTN,
    k891gstarshp_irreducible hZ hRH hT0H hTN hirr,
    k891gstarshp_inverts hZ hT0H hinv⟩

private theorem k891glift_isMulCommutative_subgroupOf_center {X : Type*} [Group X]
    {Z' V : Subgroup X} (hZ : Z' ≤ Subgroup.center X) :
    IsMulCommutative (Z'.subgroupOf V) := by
  refine IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext ?_)
  exact (Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp a.2)) (b : X)).symm

private theorem k891glift_commutator_le {X : Type*} [Group X] {V N Z' : Subgroup X}
    (hNV : N ≤ V) (hVeq : V = N ⊔ Z') (hZ : Z' ≤ Subgroup.center X) :
    ⁅V, V⁆ ≤ N := by
  have hZ'V : Z' ≤ V := hVeq ▸ le_sup_right
  have hVnorm : V ≤ Subgroup.normalizer (N : Set X) := by
    rw [hVeq]
    exact sup_le N.le_normalizer (hZ.trans (Subgroup.center_le_normalizer (N : Set X)))
  have hNVnormal : (N.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNV).mpr hVnorm
  have hZVcomm : IsMulCommutative (Z'.subgroupOf V) :=
    k891glift_isMulCommutative_subgroupOf_center hZ
  have htop : N.subgroupOf V ⊔ Z'.subgroupOf V = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNV hZ'V, ← hVeq, Subgroup.subgroupOf_self]
  have hcomm : _root_.commutator ↥V ≤ N.subgroupOf V :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop hZVcomm
  have hmapNV : (N.subgroupOf V).map V.subtype = N := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNV]
  rw [← Subgroup.map_subtype_commutator V, ← hmapNV]
  exact Subgroup.map_mono hcomm

private theorem k891glift_map_perfectResidual_map_subtype {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (V : Subgroup ↥H) :
    ((CFSG.perfectResidual ↥V).map V.subtype).map H.subtype =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F08.DerInf8 (V.map H.subtype) := by
  have hVH : V.map H.subtype ≤ H := Subgroup.map_subtype_le V
  have h := CFSG.perfectResidual_subtype_subgroupOf (K := V.map H.subtype) (L := H) hVH
  have hsub : (V.map H.subtype).subgroupOf H = V := by
    change (V.map H.subtype).comap H.subtype = V
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [hsub] at h
  have h' : (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.DerInf8 (V.map H.subtype)).subgroupOf H =
      (CFSG.perfectResidual ↥V).map V.subtype := h
  have hDerH : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.DerInf8 (V.map H.subtype) ≤ H :=
    (Subgroup.map_subtype_le (CFSG.perfectResidual ↥(V.map H.subtype))).trans hVH
  rw [← h', Subgroup.map_subgroupOf_eq_of_le hDerH]

private theorem k891glift_map_perfectResidual_comap {X YT : Type*} [Group X] [Finite X] [Group YT]
    (φ : X →* YT) (hφ : Function.Surjective φ) {Ys : Subgroup YT}
    (hperf : Group.IsPerfect ↥Ys) :
    ((CFSG.perfectResidual ↥(Ys.comap φ)).map (Ys.comap φ).subtype).map φ = Ys := by
  have hmap : (Ys.comap φ).map φ = Ys := Subgroup.map_comap_eq_self_of_surjective hφ Ys
  have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map φ (Ys.comap φ)
  rw [hmap] at h
  rw [h]
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.perfectResidual_map_eq_of_isPerfect hperf

private theorem k891glift_V_eq_sup {X YT : Type*} [Group X] [Group YT]
    (φ : X →* YT) (Ker : Subgroup X) (hKer : φ.ker = Ker) {Ys : Subgroup YT}
    (Yh : Subgroup X) (hYh : Yh.map φ = Ys) :
    Ys.comap φ = Yh ⊔ Ker := by
  apply le_antisymm
  · intro v hv
    have hvY : φ v ∈ Yh.map φ := by rw [hYh]; exact hv
    obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp hvY
    have hk : y⁻¹ * v ∈ Ker := by
      rw [← hKer, MonoidHom.mem_ker, map_mul, map_inv, hyv, inv_mul_cancel]
    rw [show v = y * (y⁻¹ * v) by group]
    exact Subgroup.mul_mem_sup hy hk
  · rw [sup_le_iff]
    refine ⟨Subgroup.map_le_iff_le_comap.mp (le_of_eq hYh), ?_⟩
    intro k hk
    rw [Subgroup.mem_comap]
    rw [show φ k = 1 from MonoidHom.mem_ker.mp (hKer.symm ▸ hk)]
    exact Ys.one_mem

private theorem k891glift_Zprime_eq_commutator {G : Type} [Group G] {H Z R : Subgroup G}
    (hZ : ZOf R = Z) (hRH : R ≤ H) (hR : IsExtraspecialExpP 3 1 ↥R) :
    Z.subgroupOf H = ⁅R.subgroupOf H, R.subgroupOf H⁆ := by
  have hZeq : Z = ⁅R, R⁆ := by
    rw [← hZ, k891gstare_ZOf_eq_map, ← hR.2.2.1]
    exact Subgroup.map_subtype_commutator R
  rw [hZeq]
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_commutator,
    Subgroup.subgroupOf_map_subtype]
  rw [inf_eq_left.mpr hRH]
  exact inf_eq_left.mpr
    ((Subgroup.commutator_le_sup R R).trans (le_of_eq (sup_idem R)) |>.trans hRH)

private theorem k891glift_mem_map_perfectResidual {X : Type*} [Group X]
    {V : Subgroup X} {m : ℕ} {r k y : X}
    (hrV : r ∈ V) (hkV : k ∈ V) (hyV : y ∈ V)
    (hy : y ∈ (CFSG.perfectResidual ↥V).map V.subtype)
    (hyrk : r = y * k) (hr3 : r ^ 3 = 1) (hk : k ^ m = 1)
    (hcop : Nat.Coprime 3 m) :
    r ∈ (CFSG.perfectResidual ↥V).map V.subtype := by
  have hchar : (CFSG.perfectResidual ↥V).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
  have hyC : (⟨y, hyV⟩ : ↥V) ∈ CFSG.perfectResidual ↥V := by
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    have : c = ⟨y, hyV⟩ := Subtype.ext hcy
    rwa [this] at hc
  have hyq : QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨y, hyV⟩ : ↥V) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hyC
  have hrr : (⟨r, hrV⟩ : ↥V) = ⟨y, hyV⟩ * ⟨k, hkV⟩ := by
    apply Subtype.ext
    change r = y * k
    exact hyrk
  have hqr : QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨r, hrV⟩ : ↥V) =
      QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨k, hkV⟩ : ↥V) := by
    rw [hrr, map_mul, hyq, one_mul]
  have hr3V : (⟨r, hrV⟩ : ↥V) ^ 3 = 1 := by
    apply Subtype.ext
    change r ^ 3 = 1
    exact hr3
  have hkpowV : (⟨k, hkV⟩ : ↥V) ^ m = 1 := by
    apply Subtype.ext
    change k ^ m = 1
    exact hk
  have hr3q : (QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨r, hrV⟩ : ↥V)) ^ 3 = 1 := by
    rw [← map_pow, hr3V, map_one]
  have hk3q : (QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨k, hkV⟩ : ↥V)) ^ 3 = 1 := by
    rw [← hqr]
    exact hr3q
  have hkmq : (QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨k, hkV⟩ : ↥V)) ^ m = 1 := by
    rw [← map_pow, hkpowV, map_one]
  have hkgcd : (QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨k, hkV⟩ : ↥V)) ^
      Nat.gcd 3 m = 1 := pow_gcd_eq_one.mpr ⟨hk3q, hkmq⟩
  have hkq : QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨k, hkV⟩ : ↥V) = 1 := by
    rwa [show Nat.gcd 3 m = 1 from hcop, pow_one] at hkgcd
  have hrC : (⟨r, hrV⟩ : ↥V) ∈ CFSG.perfectResidual ↥V := by
    have hrq : QuotientGroup.mk' (CFSG.perfectResidual ↥V) (⟨r, hrV⟩ : ↥V) = 1 := by
      rw [hqr, hkq]
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hrq
  exact Subgroup.mem_map_of_mem V.subtype hrC

theorem r891g211_lift {G : Type} [Group G] [Finite G] {H Z R M : Subgroup G}
    (hR : IsExtraspecialExpP 3 1 ↥R) (hZ : ZOf R = Z) (hRH : R ≤ H)
    (hHZ : H ≤ centralizer (Z : Set G))
    {Ys : Subgroup (R891Star H Z)} (hYs : IsComponentOf Ys ⊤)
    (hRY : R891Img H Z R ≤ Ys) (hYM : ¬ Ys ≤ R891Img H Z M) :
    R ≤ R891Y H Z Ys ∧ Z ≤ R891Y H Z Ys ∧ ¬ R891Y H Z Ys ≤ M := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperfYs : Group.IsPerfect ↥Ys := Group.isPerfect_def.mpr hYs.2.2.1
  let Ker : Subgroup ↥H := R891Ker H Z
  let π : ↥H →* R891Star H Z := QuotientGroup.mk' Ker
  let V : Subgroup ↥H := Ys.comap π
  let Yh : Subgroup ↥H := (CFSG.perfectResidual ↥V).map V.subtype
  let K0 : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let Z' : Subgroup ↥H := Z.subgroupOf H
  let R' : Subgroup ↥H := R.subgroupOf H
  have hY_eq : R891Y H Z Ys =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F08.DerInf8 (V.map H.subtype) := rfl
  have hYhmap : Yh.map π = Ys :=
    k891glift_map_perfectResidual_comap π (QuotientGroup.mk'_surjective Ker) (Ys := Ys) hperfYs
  have hKer_eq : π.ker = Ker := QuotientGroup.ker_mk' Ker
  have hVeq : V = Yh ⊔ Ker := k891glift_V_eq_sup π Ker hKer_eq (Ys := Ys) Yh hYhmap
  have hKerK0Z : Ker = K0 ⊔ Z' := k891gpprime_ker_eq hHZ
  have hZ'center : Z' ≤ Subgroup.center ↥H := k891gpprime_zcenter hHZ
  have hK0normal : K0.Normal := CFSG.pPrimeCore_normal
  have hR'leV : R' ≤ V := by
    have h : R'.map π ≤ Ys := hRY
    exact Subgroup.map_le_iff_le_comap.mp h
  have hKer_le_V : Ker ≤ V := by
    intro k hk
    rw [Subgroup.mem_comap]
    rw [show π k = 1 from MonoidHom.mem_ker.mp (hKer_eq.symm ▸ hk)]
    exact Ys.one_mem
  have hYh_le_V : Yh ≤ V := Subgroup.map_subtype_le (CFSG.perfectResidual ↥V)
  have hK0_le_V : K0 ≤ V := by
    have h : K0 ≤ Ker := by rw [hKerK0Z]; exact le_sup_left
    exact h.trans hKer_le_V
  have hZ'_le_V : Z' ≤ V := by
    have h : Z' ≤ Ker := by rw [hKerK0Z]; exact le_sup_right
    exact h.trans hKer_le_V
  have hNV : Yh ⊔ K0 ≤ V := sup_le hYh_le_V hK0_le_V
  have hV_eq_NZ : V = (Yh ⊔ K0) ⊔ Z' := by rw [hVeq, hKerK0Z, sup_assoc]
  have hZ'_eq_comm : Z' = ⁅R', R'⁆ := k891glift_Zprime_eq_commutator hZ hRH hR
  have hR'comm_le : ⁅R', R'⁆ ≤ ⁅V, V⁆ := Subgroup.commutator_mono hR'leV hR'leV
  have hcomm_le_N : ⁅V, V⁆ ≤ Yh ⊔ K0 := k891glift_commutator_le hNV hV_eq_NZ hZ'center
  have hZ'_le_N : Z' ≤ Yh ⊔ K0 := hZ'_eq_comm.le.trans (hR'comm_le.trans hcomm_le_N)
  have hV_le_N : V ≤ Yh ⊔ K0 := by rw [hV_eq_NZ]; exact sup_le le_rfl hZ'_le_N
  have hV_eq_N : V = Yh ⊔ K0 := le_antisymm hV_le_N hNV
  have hR'_le_Yh : R' ≤ Yh := by
    intro r hr
    have hrV : r ∈ V := hR'leV hr
    have hrN : r ∈ Yh ⊔ K0 := hV_eq_N ▸ hrV
    obtain ⟨y, hy, k, hk, hyk⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := Yh) (t := K0)).mp hrN
    have hrG : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    have hyV : y ∈ V := hYh_le_V hy
    have hkV : k ∈ V := hK0_le_V hk
    have hr3 : r ^ 3 = 1 := by
      apply Subtype.ext
      change (r : G) ^ 3 = 1
      have h := Monoid.pow_exponent_eq_one (⟨(r : G), hrG⟩ : ↥R)
      rw [hR.2.1] at h
      simpa using congrArg Subtype.val h
    have hkpow : k ^ Nat.card K0 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (K0.orderOf_dvd_natCard hk)
    have hcop : Nat.Coprime 3 (Nat.card K0) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)
    exact k891glift_mem_map_perfectResidual hrV hkV hyV hy hyk.symm hr3 hkpow hcop
  have hR'_mapeq : R'.map H.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRH]
  have hYhmapH : Yh.map H.subtype =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F08.DerInf8 (V.map H.subtype) :=
    k891glift_map_perfectResidual_map_subtype V
  have hR_le_Y : R ≤ R891Y H Z Ys := by
    rw [hY_eq, ← hR'_mapeq, ← hYhmapH]
    exact Subgroup.map_mono hR'_le_Yh
  have hZ_le_R : Z ≤ R := by
    rw [← hZ]
    exact inf_le_left
  have hnotM : ¬ R891Y H Z Ys ≤ M := by
    intro hYM'
    apply hYM
    have hYh_le_M : Yh ≤ M.subgroupOf H := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxM : (x : G) ∈ Yh.map H.subtype := Subgroup.mem_map_of_mem H.subtype hx
      rw [hYhmapH] at hxM
      exact hYM' hxM
    have : Ys ≤ R891Img H Z M := by
      rw [← hYhmap]
      exact Subgroup.map_mono hYh_le_M
    exact this
  exact ⟨hR_le_Y, hZ_le_R.trans hR_le_Y, hnotM⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
