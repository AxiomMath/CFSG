module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_2_a
import Mathlib.GroupTheory.SchurZassenhaus

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki.PFchapter2

open PFchapter1section1

universe u v

private theorem not_twoRankAtLeastTwo_quotient_of_odd
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    (hG : ¬ TwoRankAtLeastTwo G) :
    ¬ TwoRankAtLeastTwo (G ⧸ N) := by
  classical
  intro hquot
  rcases hquot with ⟨E, hEcard, hEsq⟩
  let pi : G →* G ⧸ N := QuotientGroup.mk' N
  let M : Subgroup G := E.comap pi
  have hN_le_M : N ≤ M := by
    intro n hn
    change pi n ∈ E
    have hpi : pi n = 1 := by
      exact (QuotientGroup.eq_one_iff (N := N) n).2 hn
    simp [hpi]
  let NM : Subgroup M := N.subgroupOf M
  let phi : M →* E :=
    (pi.domRestrict M).codRestrict E (by
      intro m
      exact m.property)
  have hphi_surj : Function.Surjective phi := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (e : G ⧸ N)
    let m : M := ⟨g, by
      change pi g ∈ E
      rw [show pi g = e from hg]
      exact e.property⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    change pi (m : G) = e
    simpa [m, pi] using hg
  have hphi_ker : phi.ker = NM := by
    ext m
    constructor
    · intro hm
      change (m : G) ∈ N
      apply (QuotientGroup.eq_one_iff (N := N) (m : G)).1
      have hm' : phi m = 1 := by
        simpa [MonoidHom.mem_ker] using hm
      have hm'' := congrArg Subtype.val hm'
      change pi (m : G) = 1 at hm''
      exact hm''
    · intro hm
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change pi (m : G) = 1
      exact (QuotientGroup.eq_one_iff (N := N) (m : G)).2 hm
  haveI : NM.Normal := (inferInstance : N.Normal).subgroupOf M
  have hNMcard : Nat.card NM = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le_M).toEquiv
  have hNModd : Odd (Nat.card NM) := hNMcard ▸ hNodd
  have hNMindex : NM.index = 4 := by
    calc
      NM.index = phi.ker.index := congrArg Subgroup.index hphi_ker.symm
      _ = Nat.card phi.range := Subgroup.index_ker phi
      _ = Nat.card E := by
        rw [phi.range_eq_top_of_surjective hphi_surj]
        simp
      _ = 4 := hEcard
  have hcoprime : Nat.Coprime (Nat.card NM) NM.index := by
    rw [hNMindex, show 4 = 2 ^ 2 by decide]
    exact hNModd.coprime_two_right.pow_right 2
  obtain ⟨K, hK⟩ := NM.exists_right_complement'_of_coprime hcoprime
  have hKcard : Nat.card K = 4 := by
    calc
      Nat.card K = NM.index := hK.symm.index_eq_card.symm
      _ = 4 := hNMindex
  have hKsq : ∀ x : K, (x : K) ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    let xM : M := x
    let e : E := ⟨pi (xM : G), xM.property⟩
    have he2 : e ^ 2 = 1 := hEsq e
    have hpi2 : pi ((xM : G) ^ 2) = 1 := by
      simpa [e, map_pow] using congrArg Subtype.val he2
    have hx2_NM : xM ^ 2 ∈ NM := by
      change (xM : G) ^ 2 ∈ N
      exact (QuotientGroup.eq_one_iff (N := N) ((xM : G) ^ 2)).1 hpi2
    have hx2_K : xM ^ 2 ∈ K := K.pow_mem x.property 2
    have hx2_bot : xM ^ 2 ∈ (⊥ : Subgroup M) := by
      rw [← hK.disjoint.eq_bot]
      exact ⟨hx2_NM, hx2_K⟩
    simpa [xM] using hx2_bot
  let KG : Subgroup G := K.map M.subtype
  have hKGcard : Nat.card KG = 4 := by
    calc
      Nat.card KG = Nat.card K :=
        Subgroup.card_map_of_injective (K := K) (f := M.subtype) M.subtype_injective
      _ = 4 := hKcard
  apply hG
  refine ⟨KG, hKGcard, ?_⟩
  rintro ⟨g, hg⟩
  rcases hg with ⟨m, hmK, rfl⟩
  apply Subtype.ext
  simpa using congrArg (fun z : K => ((z : M) : G)) (hKsq ⟨m, hmK⟩)

private theorem faithfulSMul_quotient_pointStabilizerCore
    {G Omega : Type*} [Group G] [MulAction G Omega]
    [hN : (pointStabilizerCore G Omega).Normal]
    (quotientAction : MulAction (G ⧸ pointStabilizerCore G Omega) Omega)
    (hsmul : forall (g : G) (w : Omega),
      @SMul.smul (G ⧸ pointStabilizerCore G Omega) Omega
        quotientAction.toSMul (QuotientGroup.mk g) w = g • w) :
    @FaithfulSMul (G ⧸ pointStabilizerCore G Omega) Omega
      quotientAction.toSMul := by
  letI : MulAction (G ⧸ pointStabilizerCore G Omega) Omega := quotientAction
  refine { eq_of_smul_eq_smul := ?_ }
  intro a b hab
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pointStabilizerCore G Omega) a
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pointStabilizerCore G Omega) b
  apply QuotientGroup.eq_iff_div_mem.mpr
  simp only [pointStabilizerCore, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  intro w
  calc
    (g / h) • w = g • (h⁻¹ • w) := by simp [div_eq_mul_inv, mul_smul]
    _ = (QuotientGroup.mk g : G ⧸ pointStabilizerCore G Omega) • (h⁻¹ • w) := by
      exact (hsmul g (h⁻¹ • w)).symm
    _ = (QuotientGroup.mk h : G ⧸ pointStabilizerCore G Omega) • (h⁻¹ • w) :=
      hab (h⁻¹ • w)
    _ = h • (h⁻¹ • w) := hsmul h (h⁻¹ • w)
    _ = w := by simp

private theorem quotientMap_subgroup_equiv_of_disjoint
    {G : Type*} [Group G] (N Q : Subgroup G) [N.Normal]
    (hdis : Disjoint Q N) :
    Nonempty (Q ≃* Q.map (QuotientGroup.mk' N)) := by
  let pi : G →* G ⧸ N := QuotientGroup.mk' N
  let f : Q →* Q.map pi :=
    (pi.domRestrict Q).codRestrict (Q.map pi) (fun q => ⟨q, q.2, rfl⟩)
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hpi : pi (x : G) = pi (y : G) := by
      have hxy' := congrArg Subtype.val hxy
      change pi (x : G) = pi (y : G) at hxy'
      exact hxy'
    have hdivN : (x : G) / (y : G) ∈ N :=
      QuotientGroup.eq_iff_div_mem.mp hpi
    have hdivQ : (x : G) / (y : G) ∈ Q := Q.div_mem x.2 y.2
    have hdivBot : (x : G) / (y : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hdis) hdivQ hdivN
    exact div_eq_one.mp (Subgroup.mem_bot.mp hdivBot)
  have hf_surjective : Function.Surjective f := by
    intro z
    rcases z.2 with ⟨g, hgQ, hg⟩
    refine ⟨⟨g, hgQ⟩, ?_⟩
    apply Subtype.ext
    change pi g = (z : G ⧸ N)
    exact hg
  exact ⟨MulEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩⟩

/-!
# Peterfalvi, Part II, Chapter II, Claim (2)(b)
-/

public theorem claim_2_b
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : Nat)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Omega H D Q t ∧
  K ≤ D ∧
    (forall x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (forall x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (exists P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (forall s : G, s ∈ S → forall q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    exists r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let OmegaP : Type _ := {w : Omega // w ∈ fixedPointsOfSubgroup G Omega P}
    letI : MulAction C OmegaP := fixedPointCentralizerAction G Omega P
    let HP : Subgroup C := H.comap C.subtype
    let DP : Subgroup C := D.comap C.subtype
    let QP : Subgroup C := Q.comap C.subtype
    let tP : C :=
      ⟨t, t_mem_centralizer_of_le_peterfalviV D V P t hch.B1.P_le_V
        hch.section3.section2.V_eq⟩
    let N : Subgroup G :=
      D ⊓ Subgroup.centralizer ((Q ⊓ C : Subgroup G) : Set G) ⊓ C
    N.subgroupOf C = pointStabilizerCore C OmegaP ∧
      exists hnormal : (pointStabilizerCore C OmegaP).Normal,
      letI : (pointStabilizerCore C OmegaP).Normal := hnormal
      exists quotientAction : MulAction (C ⧸ pointStabilizerCore C OmegaP) OmegaP,
        letI : MulAction (C ⧸ pointStabilizerCore C OmegaP) OmegaP := quotientAction
        (forall (c : C) (w : OmegaP),
            (QuotientGroup.mk c : C ⧸ pointStabilizerCore C OmegaP) • w = c • w) ∧
          HypothesisA1 (C ⧸ pointStabilizerCore C OmegaP) OmegaP
            (HP.map (QuotientGroup.mk' (pointStabilizerCore C OmegaP)))
            (DP.map (QuotientGroup.mk' (pointStabilizerCore C OmegaP)))
            (QP.map (QuotientGroup.mk' (pointStabilizerCore C OmegaP)))
            (QuotientGroup.mk tP) ∧
          ∃ (F : Type v) (_ : PFAppendixII.RightNearField F) (_ : Finite F)
              (_ : Nontrivial F) (_ : nearFieldStar Q P ≃* Fˣ),
            PFAppendixII.PropositionOneConclusion
                (HP.map (QuotientGroup.mk' (pointStabilizerCore C OmegaP)))
                (DP.map (QuotientGroup.mk' (pointStabilizerCore C OmegaP)))
                (QP.map (QuotientGroup.mk' (pointStabilizerCore C OmegaP))) F ∧
              addOrderOf (1 : F) = orderOf (s * t) := by
  classical
  dsimp only
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let OmegaP : Type _ := {w : Omega // w ∈ fixedPointsOfSubgroup G Omega P}
  letI : MulAction C OmegaP := fixedPointCentralizerAction G Omega P
  let HP : Subgroup C := H.comap C.subtype
  let DP : Subgroup C := D.comap C.subtype
  let QP : Subgroup C := Q.comap C.subtype
  let tP : C :=
    ⟨t, t_mem_centralizer_of_le_peterfalviV D V P t hch.B1.P_le_V
      hch.section3.section2.V_eq⟩
  let N : Subgroup G :=
    D ⊓ Subgroup.centralizer ((Q ⊓ C : Subgroup G) : Set G) ⊓ C
  have h2a := claim_2_a H D Q K V W Q0 S Q1 P t s p hch
  have hA1P : HypothesisA1 C OmegaP HP DP QP tP := by
    simpa [C, OmegaP, HP, DP, QP, tP] using h2a.1
  rcases h2a.2 with ⟨N', hN', hNker⟩
  have hNcore : N.subgroupOf C = pointStabilizerCore C OmegaP := by
    calc
      N.subgroupOf C = N'.subgroupOf C := by rw [hN']; rfl
      _ = (MulAction.toPermHom C OmegaP).ker := by
        simpa [C, OmegaP] using hNker
      _ = pointStabilizerCore C OmegaP := by
        ext c
        simp [pointStabilizerCore, MulAction.mem_stabilizer_iff,
          MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  refine ⟨hNcore, ?_⟩
  have hnormal : (pointStabilizerCore C OmegaP).Normal := by
    have hker : pointStabilizerCore C OmegaP = (MulAction.toPermHom C OmegaP).ker := by
      ext c
      simp [pointStabilizerCore, MulAction.mem_stabilizer_iff,
        MonoidHom.mem_ker, Equiv.Perm.ext_iff]
    rw [hker]
    infer_instance
  refine ⟨hnormal, ?_⟩
  letI : (pointStabilizerCore C OmegaP).Normal := hnormal
  obtain ⟨pair, hpair, _hpair_unique⟩ := proposition_4_b HP DP QP tP hA1P
  have h4c := proposition_4_c HP DP QP tP pair.1 hA1P hpair.1 hpair.2.1
    ⟨pair.2, hpair.2.2.1, hpair.2.2.2⟩
  rcases h4c with ⟨hcore, _hcore_le, hquot, _hQiso, horder⟩
  rcases hquot with ⟨quotientAction, hsmul, hA1bar⟩
  refine ⟨quotientAction, hsmul, hA1bar, ?_⟩
  letI : MulAction (C ⧸ pointStabilizerCore C OmegaP) OmegaP := quotientAction
  letI : FaithfulSMul (C ⧸ pointStabilizerCore C OmegaP) OmegaP :=
    faithfulSMul_quotient_pointStabilizerCore quotientAction hsmul
  have hcore_le_DP : pointStabilizerCore C OmegaP ≤ DP := by
    rw [hcore]
    exact inf_le_left
  have hcore_odd : Odd (Nat.card (pointStabilizerCore C OmegaP)) :=
    hA1P.D_odd.of_dvd_nat (Subgroup.card_dvd_of_le hcore_le_DP)
  have hC_rank : ¬ TwoRankAtLeastTwo C := by
    simpa [C] using hch.B1.centralizer_has_two_rank_one
  have hquot_rank :
      ¬ TwoRankAtLeastTwo (C ⧸ pointStabilizerCore C OmegaP) :=
    not_twoRankAtLeastTwo_quotient_of_odd
      (pointStabilizerCore C OmegaP) hcore_odd hC_rank
  let core : Subgroup C := pointStabilizerCore C OmegaP
  let pi : C →* C ⧸ core := QuotientGroup.mk' core
  obtain ⟨F, hF, hFfinite, hFnontrivial, hPO⟩ :=
    PFAppendixII.proposition_1
      (Ω := OmegaP) (H := HP.map pi) (D := DP.map pi) (Q := QP.map pi)
      (t := QuotientGroup.mk tP) hA1bar hquot_rank
  letI : PFAppendixII.RightNearField F := hF
  letI : Finite F := hFfinite
  letI : Nontrivial F := hFnontrivial
  have hcore_le_DP : core ≤ DP := by
    change pointStabilizerCore C OmegaP ≤ DP
    exact hcore_le_DP
  have hQP_core_disjoint : Disjoint QP core := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxcore
    have hxD : (x : G) ∈ D := hcore_le_DP hxcore
    have hxQD : (x : G) ∈ Q ⊓ D := ⟨hxQ, hxD⟩
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) :=
      hch.section3.section2.hA.A1.Q_disjoint_D.le_bot hxQD
    simpa using hxBot
  obtain ⟨qpToQbar⟩ :=
    quotientMap_subgroup_equiv_of_disjoint core QP hQP_core_disjoint
  obtain ⟨unitToQbar⟩ :=
    PFAppendixII.propositionOneConclusion_unitsEquiv
      (HP.map pi) (DP.map pi) (QP.map pi) hPO
  let starToQP : nearFieldStar Q P ≃* QP :=
    { toFun := fun x => ⟨⟨x, x.2.2⟩, x.2.1⟩
      invFun := fun x => ⟨x, x.2, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let unitEquiv : nearFieldStar Q P ≃* Fˣ :=
    (starToQP.trans qpToQbar).trans unitToQbar.symm
  obtain ⟨globalPair, hglobalPair, hglobalUnique⟩ :=
    proposition_4_b H D Q t hch.section3.section2.hA.A1
  obtain ⟨r, hrQ, hrelation⟩ := hch.section3.2.2.2
  have horiginal : (s, r) = globalPair :=
    hglobalUnique (s, r)
      ⟨hch.section3.2.1, hch.section3.2.2.1, hrQ, hrelation⟩
  let pairG : G × G := ((pair.1 : C), (pair.2 : C))
  have hpairGData :
      pairG.1 ∈ H ∧ PFAppendixIII.IsInvolution pairG.1 ∧ pairG.2 ∈ Q ∧
        t * pairG.1 * t = pairG.2⁻¹ * t * pairG.2 := by
    refine ⟨hpair.1, ?_, hpair.2.2.1, ?_⟩
    · constructor
      · intro hone
        exact hpair.2.1.ne_one (Subtype.ext hone)
      · exact congrArg C.subtype hpair.2.1.sq_eq_one
    · simpa [pairG, tP] using congrArg C.subtype hpair.2.2.2
  have hpairGlobal : pairG = globalPair :=
    hglobalUnique pairG hpairGData
  have hpairFirst : (pair.1 : G) = s := by
    exact congrArg Prod.fst (hpairGlobal.trans horiginal.symm)
  have hpairBarI : PFAppendixIII.IsInvolution (pi pair.1) := by
    constructor
    · intro hone
      have hpairCore : pair.1 ∈ core :=
        (QuotientGroup.eq_one_iff (N := core) pair.1).mp hone
      exact
        (BenderSuzuki.PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
          DP hA1P.D_odd (hcore_le_DP hpairCore)) hpair.2.1
    · simpa using congrArg pi hpair.2.1.sq_eq_one
  have htBarI : PFAppendixIII.IsInvolution (pi tP) := by
    simpa [pi, core] using hA1bar.involution_t
  have hpairBarH : pi pair.1 ∈ HP.map pi :=
    ⟨pair.1, hpair.1, rfl⟩
  have hpairBar_ne_tBar : pi pair.1 ≠ pi tP := by
    intro heq
    apply hA1bar.t_not_mem_H
    have htBarH : pi tP ∈ HP.map pi := by
      rw [← heq]
      exact hpairBarH
    simpa [pi, core] using htBarH
  have hbarOrder :=
    BenderSuzuki.PFAppendixII.PropositionOneConclusion.involutionProductOrder
      (HP.map pi) (DP.map pi) (QP.map pi) hPO
        hpairBarI htBarI hpairBar_ne_tBar
  have hquotOrder :
      orderOf (pi (pair.1 * tP)) = orderOf (pair.1 * tP) := by
    simpa [pi, core] using horder
  have hambientOrder : orderOf (pair.1 * tP) = orderOf (s * t) := by
    calc
      orderOf (pair.1 * tP) = orderOf (((pair.1 * tP : C) : G)) :=
        (Subgroup.orderOf_coe (pair.1 * tP)).symm
      _ = orderOf (s * t) := by
        congr 1
        change (pair.1 : G) * t = s * t
        rw [hpairFirst]
  have hcharacteristic : addOrderOf (1 : F) = orderOf (s * t) := by
    calc
      addOrderOf (1 : F) = orderOf (pi pair.1 * pi tP) := hbarOrder.symm
      _ = orderOf (pi (pair.1 * tP)) := by rw [map_mul]
      _ = orderOf (pair.1 * tP) := hquotOrder
      _ = orderOf (s * t) := hambientOrder
  exact ⟨F, hF, hFfinite, hFnontrivial, unitEquiv, hPO, hcharacteristic⟩

end CFSG.BenderSuzuki.PFchapter2
