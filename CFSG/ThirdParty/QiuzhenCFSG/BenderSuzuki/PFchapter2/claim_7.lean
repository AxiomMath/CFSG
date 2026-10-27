module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_2_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_6

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

universe u v

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

/-!
# Peterfalvi, Part II, Chapter II, Claim (7)
-/

private theorem claim_7_sup_decomposition_of_direct_product
    {G : Type*} [Group G] {H A B N : Subgroup G}
    (hA_le_H : A ≤ H) (hB_le_H : B ≤ H)
    (hA_norm_H : ∀ h a : G, h ∈ H → a ∈ A → h * a * h⁻¹ ∈ A)
    (hsup : A ⊔ B = H)
    (hN_le_H : N ≤ H) (hB_le_N : B ≤ N) :
    N ≤ (N ⊓ A) ⊔ B := by
  classical
  have hA_normal_H : (A.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_H]
    intro h hhH
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hA_norm_H h a hhH ha
    · intro hconj
      have hinvH : h⁻¹ ∈ H := H.inv_mem hhH
      have hback : h⁻¹ * (h * a * h⁻¹) * (h⁻¹)⁻¹ ∈ A :=
        hA_norm_H h⁻¹ (h * a * h⁻¹) hinvH hconj
      simpa [mul_assoc] using hback
  intro x hxN
  let xH : H := ⟨x, hN_le_H hxN⟩
  haveI : (A.subgroupOf H).Normal := hA_normal_H
  have hsup_top : A.subgroupOf H ⊔ B.subgroupOf H = ⊤ := by
    have hsub :
        (A ⊔ B).subgroupOf H = A.subgroupOf H ⊔ B.subgroupOf H :=
      Subgroup.subgroupOf_sup hA_le_H hB_le_H
    rw [← hsub, hsup]
    simp
  have hx_sup : xH ∈ A.subgroupOf H ⊔ B.subgroupOf H := by
    rw [hsup_top]
    exact (show xH ∈ (⊤ : Subgroup H) from by simp)
  rcases (Subgroup.mem_sup_of_normal_left.mp hx_sup) with
    ⟨aH, haA, bH, hbB, hab⟩
  have hab_G : (aH : G) * (bH : G) = x := by
    simpa [xH] using congrArg Subtype.val hab
  have hbN : (bH : G) ∈ N := hB_le_N hbB
  have haN : (aH : G) ∈ N := by
    have ha_eq : (aH : G) = x * (bH : G)⁻¹ := by
      calc
        (aH : G) = ((aH : G) * (bH : G)) * (bH : G)⁻¹ := by
          simp [mul_assoc]
        _ = x * (bH : G)⁻¹ := by rw [hab_G]
    simpa [ha_eq] using N.mul_mem hxN (N.inv_mem hbN)
  have ha_sup : (aH : G) ∈ (N ⊓ A) ⊔ B :=
    Subgroup.mem_sup_left ⟨haN, haA⟩
  have hb_sup : (bH : G) ∈ (N ⊓ A) ⊔ B :=
    Subgroup.mem_sup_right hbB
  have hprod : (aH : G) * (bH : G) ∈ (N ⊓ A) ⊔ B :=
    ((N ⊓ A) ⊔ B).mul_mem ha_sup hb_sup
  simpa [hab_G] using hprod

private theorem claim_7_sigmaBar_mulEquiv_CW
    {G : Type*} [Group G]
    (D W P N C : Subgroup G) (core : Subgroup C) [core.Normal]
    (hNcore : N.subgroupOf C = core) (hNP : N = P)
    (hWC_le_DCP : W ⊓ C ≤ D ⊓ C) (hP_le_DCP : P ≤ D ⊓ C)
    (hWC_norm_DCP :
      ∀ h a : G, h ∈ D ⊓ C → a ∈ W ⊓ C →
        h * a * h⁻¹ ∈ W ⊓ C)
    (hdisj : Disjoint (W ⊓ C) P)
    (hsup : (W ⊓ C) ⊔ P = D ⊓ C) :
    ∃ e :
      ↥((D.comap C.subtype).map (QuotientGroup.mk' core)) ≃* ↥(W ⊓ C),
      ∀ a : ↥((D.comap C.subtype).map (QuotientGroup.mk' core)),
        QuotientGroup.mk' core
          ⟨(e a : G), (e a).property.2⟩ = (a : C ⧸ core) := by
  classical
  let Wc : Subgroup G := W ⊓ C
  let DCP : Subgroup G := D ⊓ C
  let DP : Subgroup C := D.comap C.subtype
  let pi : C →* C ⧸ core := QuotientGroup.mk' core
  let SigmaBar : Subgroup (C ⧸ core) := DP.map pi
  let fromW : Wc →* SigmaBar :=
    { toFun := fun w =>
        ⟨pi ⟨(w : G), w.2.2⟩, by
          rw [Subgroup.mem_map]
          refine ⟨⟨(w : G), w.2.2⟩, ?_, rfl⟩
          change (w : G) ∈ D
          exact (hWC_le_DCP w.2).1⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        rfl }
  have hfromW_injective : Function.Injective fromW := by
    intro x y hxy
    apply Subtype.ext
    have hpi :
        pi ⟨(x : G), x.2.2⟩ = pi ⟨(y : G), y.2.2⟩ :=
      congrArg Subtype.val hxy
    have hdivCore :
        (⟨(x : G), x.2.2⟩ : C) / ⟨(y : G), y.2.2⟩ ∈ core :=
      QuotientGroup.eq_iff_div_mem.mp hpi
    rw [← hNcore, hNP] at hdivCore
    have hdivP : (x : G) / (y : G) ∈ P := by
      exact Subgroup.mem_subgroupOf.mp hdivCore
    have hdivWc : (x : G) / (y : G) ∈ Wc :=
      Wc.div_mem x.2 y.2
    have hdivBot : (x : G) / (y : G) ∈ (⊥ : Subgroup G) :=
      (disjoint_iff_inf_le.mp hdisj) ⟨hdivWc, hdivP⟩
    have hdivOne : (x : G) / (y : G) = 1 := by
      simpa using hdivBot
    exact div_eq_one.mp hdivOne
  have hfromW_surjective : Function.Surjective fromW := by
    intro z
    rcases Subgroup.mem_map.mp z.2 with ⟨d, hdDP, hdpi⟩
    have hdD : (d : G) ∈ D := by
      change (d : G) ∈ D at hdDP
      exact hdDP
    let dDCP : DCP := ⟨(d : G), hdD, d.2⟩
    have hWc_normal_DCP : (Wc.subgroupOf DCP).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hWC_le_DCP]
      intro h hhDCP
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        exact hWC_norm_DCP h a hhDCP ha
      · intro hconj
        have hinvDCP : h⁻¹ ∈ DCP := DCP.inv_mem hhDCP
        have hback :
            h⁻¹ * (h * a * h⁻¹) * (h⁻¹)⁻¹ ∈ Wc :=
          hWC_norm_DCP h⁻¹ (h * a * h⁻¹) hinvDCP hconj
        have hback_eq : h⁻¹ * (h * a * h⁻¹) * (h⁻¹)⁻¹ = a := by
          group
        rw [hback_eq] at hback
        exact hback
    letI : (Wc.subgroupOf DCP).Normal := hWc_normal_DCP
    have hsup_top :
        Wc.subgroupOf DCP ⊔ P.subgroupOf DCP = ⊤ := by
      have hsub :
          (Wc ⊔ P).subgroupOf DCP =
            Wc.subgroupOf DCP ⊔ P.subgroupOf DCP :=
        Subgroup.subgroupOf_sup hWC_le_DCP hP_le_DCP
      rw [← hsub, hsup]
      simp [DCP]
    have hd_sup :
        dDCP ∈ Wc.subgroupOf DCP ⊔ P.subgroupOf DCP := by
      rw [hsup_top]
      simp
    rcases Subgroup.mem_sup_of_normal_left.mp hd_sup with
      ⟨wDCP, hwWc, pDCP, hpP, hwp⟩
    let w : Wc := ⟨(wDCP : G), hwWc⟩
    let wC : C := ⟨(wDCP : G), wDCP.2.2⟩
    let pC : C := ⟨(pDCP : G), pDCP.2.2⟩
    have hpCore : pC ∈ core := by
      rw [← hNcore, hNP]
      exact hpP
    have hpiP : pi pC = 1 :=
      (QuotientGroup.eq_one_iff pC).2 hpCore
    have hwpG : (wDCP : G) * (pDCP : G) = (d : G) := by
      simpa [dDCP] using congrArg Subtype.val hwp
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change pi wC = (z : C ⧸ core)
    calc
      pi wC = pi wC * 1 := (mul_one _).symm
      _ = pi wC * pi pC := by rw [hpiP]
      _ = pi (wC * pC) := (map_mul pi wC pC).symm
      _ = pi d := by
        congr 1
        apply Subtype.ext
        exact hwpG
      _ = z := hdpi
  let fromWEquiv : Wc ≃* SigmaBar :=
    MulEquiv.ofBijective fromW ⟨hfromW_injective, hfromW_surjective⟩
  let e : SigmaBar ≃* Wc := fromWEquiv.symm
  refine ⟨e, ?_⟩
  intro a
  change pi ⟨(e a : G), (e a).property.2⟩ = (a : C ⧸ core)
  change (fromW (e a) : C ⧸ core) = (a : C ⧸ core)
  change (fromWEquiv (fromWEquiv.symm a) : C ⧸ core) = (a : C ⧸ core)
  exact congrArg Subtype.val (fromWEquiv.apply_symm_apply a)
private theorem claim_7_N_decomposition_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P N : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hN : N =
      D ⊓ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
        Subgroup.centralizer (P : Set G))
    :
    N = (N ⊓ W) ⊔ P := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let CQ : Subgroup G := Q ⊓ C
  rcases claim_1 H D Q K V W Q0 S Q1 P t s p hch with
    ⟨_hV, _hQ0, _hNormP, hDirect⟩
  rcases hDirect with
    ⟨hWC_le_DCP, hP_le_DCP, hWC_norm_DCP, _hP_norm_DCP, _hdisj, hsup, _hcomm⟩
  have hP_le_N : P ≤ N := by
    intro x hxP
    have hxDCP : x ∈ D ⊓ C := by
      simpa [C] using hP_le_DCP hxP
    have hxCQ : x ∈ Subgroup.centralizer (CQ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyCQ
      have hyC : y ∈ C := hyCQ.2
      exact ((Subgroup.mem_centralizer_iff.mp hyC) x hxP).symm
    have hxN : x ∈ D ⊓ Subgroup.centralizer (CQ : Set G) ⊓ C := by
      exact ⟨⟨hxDCP.1, hxCQ⟩, hxDCP.2⟩
    simpa [hN, C, CQ] using hxN
  apply le_antisymm
  · have hN_le_DCP : N ≤ D ⊓ C := by
      intro x hxN
      have hxN' :
          x ∈ D ⊓ Subgroup.centralizer (CQ : Set G) ⊓ C := by
        simpa [hN, C, CQ] using hxN
      exact ⟨hxN'.1.1, hxN'.2⟩
    have hN_le_NWC_sup :
        N ≤ (N ⊓ (W ⊓ C)) ⊔ P :=
      claim_7_sup_decomposition_of_direct_product
        (H := D ⊓ C) (A := W ⊓ C) (B := P) (N := N)
        hWC_le_DCP hP_le_DCP hWC_norm_DCP hsup hN_le_DCP hP_le_N
    have hsmall_le : N ⊓ (W ⊓ C) ≤ N ⊓ W := by
      intro x hx
      exact ⟨hx.1, hx.2.1⟩
    have hsup_le : (N ⊓ (W ⊓ C)) ⊔ P ≤ (N ⊓ W) ⊔ P := by
      exact
        sup_le
          (fun x hx => Subgroup.mem_sup_left (hsmall_le hx))
          (fun x hx => Subgroup.mem_sup_right hx)
    exact hN_le_NWC_sup.trans hsup_le
  · exact sup_le inf_le_left hP_le_N

private theorem claim_7_addOrderOf_one_eq_three_of_dickson_model
    {F : Type*} [PFAppendixII.RightNearField F] [Finite F]
    (hmodel : PFAppendixII.IsDicksonIndexTwoModel F 3 1) :
    addOrderOf (1 : F) = 3 := by
  rw [PFAppendixII.IsDicksonIndexTwoModel] at hmodel
  rcases hmodel with
    ⟨_hprime, _hne_two, _hn_pos, hfact, e, he1, _hmul, _hfrob, _hcenter⟩
  letI : Fact (Nat.Prime 3) := hfact
  apply addOrderOf_eq_prime
  · apply e.injective
    have hchar : (3 : GaloisField 3 (2 * 1)) = 0 :=
      CharP.cast_eq_zero (GaloisField 3 (2 * 1)) 3
    simp [map_nsmul, he1, nsmul_eq_mul, hchar]
  · exact one_ne_zero

private theorem claim_7_D_inf_centralizer_Q_eq_bot
    {G : Type*} {Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA : PFchapter1section1.HypothesisA G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) :
    D ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
  have hcore :=
    (PFchapter1section1.proposition_4_c H D Q t s
      hA.A1 hsH hsI hsStructure).1
  rw [← hcore, eq_bot_iff]
  intro x hxCore
  have hfix : ∀ omega : Ω, x • omega = omega := by
    have hxAll : ∀ point : Ω, x ∈ MulAction.stabilizer G point := by
      simpa [pointStabilizerCore] using hxCore
    intro omega
    exact MulAction.mem_stabilizer_iff.mp (hxAll omega)
  have hxOne : x = 1 :=
    (faithfulSMul_iff.mp hA.A2) x hfix
  simp [hxOne]

private theorem claim_7_eq_bot_of_isPGroup_two_of_odd_card
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (hA_two : IsPGroup 2 A) (hA_odd : Odd (Nat.card A)) :
    A = ⊥ := by
  obtain ⟨n, hn⟩ := hA_two.exists_card_eq
  have hn_zero : n = 0 := by
    by_contra hn_ne
    have hEven : Even (Nat.card A) := by
      rw [hn]
      exact even_two.pow_of_ne_zero hn_ne
    exact (Nat.not_even_iff_odd.mpr hA_odd) hEven
  apply Subgroup.card_eq_one.mp
  simpa [hn_zero] using hn

/- Claim (7): the nontrivial `N ∩ W` case is impossible. -/
private theorem chapter2_claim7_N_inf_W_nontrivial_case_elimination
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P N : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hN : N =
      D ⊓ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
        Subgroup.centralizer (P : Set G))
    (hNW_ne_bot : N ⊓ W ≠ ⊥) :
    False := by
  classical
  let X : Subgroup G := N ⊓ W
  let CX : Subgroup G := Subgroup.centralizer (X : Set G)
  let R : Subgroup G := CX ⊓ Q
  have hX_ne : X ≠ ⊥ := by
    simpa [X] using hNW_ne_bot
  have hX_le_V : X ≤ V := by
    exact inf_le_right.trans hch.section3.section2.W_le_V
  have hWcentralizer :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
    _root_.CFSG.BenderSuzuki.PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hch.section3.section2.hA.A1
          hch.section3.section2.K_def hch.section3.section2.V_eq
          hch.section3.section2.W_eq
  have hQ0_le_CX : Q0 ≤ CX := by
    intro q hqQ0
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    have hxW : x ∈ W := by
      exact hxX.2
    have hxCentralizer :
        x ∈ Subgroup.centralizer ({y : G | y ∈ H ∧ IsInvolution y}) := by
      rw [hWcentralizer] at hxW
      exact hxW.2
    rcases (hch.section3.section2.Q0_def q).mp hqQ0 with hq_one | hq_inv
    · subst q
      simp
    · exact ((Subgroup.mem_centralizer_iff.mp hxCentralizer) q hq_inv).symm
  have h2rank : TwoRankAtLeastTwo CX := by
    exact
      claim_1_rank_two_subgroup_of_large_exp_two_subgroup
        hQ0_le_CX
        (claim_1_Q0_card_gt_two H D Q K V W Q0 S Q1 P t s p hch)
        (claim_1_Q0_sq H D Q K V W Q0 S Q1 P t s p hch)
  have hprop :=
    PFchapter1section3.proposition_1_c
      H D Q K V W Q0 S Q1 X t s hch.section3 hind
        hX_ne hX_le_V h2rank
  dsimp only at hprop
  rcases hprop with
    ⟨hCXQ1_bot, hNLF, ell, hellpow, hellgt, hellcard, hcases⟩
  have hCX_inf_Q0 : CX ⊓ Q0 = Q0 := inf_eq_right.mpr hQ0_le_CX
  have hellQ0 : ell = Nat.card Q0 := by
    simpa [CX, hCX_inf_Q0] using hellcard
  have hR_pgroup : IsPGroup 2 R := by
    rcases hellpow with ⟨n, hn⟩
    rcases hcases with hlinear | hquadratic | hcubic
    · rcases hlinear with ⟨_, _, _, _, _, _, hcard⟩
      apply IsPGroup.of_card (n := n)
      simpa [R, CX, hn] using hcard
    · rcases hquadratic with ⟨_, _, _, _, _, _, hcard⟩
      apply IsPGroup.of_card (n := n * 2)
      simpa [R, CX, hn, pow_mul] using hcard
    · rcases hcubic with ⟨_, _, _, _, _, _, _, _, _, _, hcard⟩
      apply IsPGroup.of_card (n := n * 3)
      simpa [R, CX, hn, pow_mul] using hcard.1
  have hStar_le_R : nearFieldStar Q P ≤ R := by
    intro z hzStar
    refine ⟨?_, hzStar.1⟩
    change z ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    have hxN : x ∈ N := hxX.1
    rw [hN] at hxN
    exact
      ((Subgroup.mem_centralizer_iff.mp hxN.1.2) z hzStar).symm
  have hStar_pgroup : IsPGroup 2 (nearFieldStar Q P) :=
    IsPGroup.to_le hR_pgroup hStar_le_R
  have hQcard :
      Nat.card Q = Nat.card (nearFieldStar Q P) ^ p := by
    simpa [nearFieldStar] using
      claim_4 H D Q K V W Q0 S Q1 P t s p hch
  have hQ_pgroup : IsPGroup 2 Q := by
    obtain ⟨n, hn⟩ := hStar_pgroup.exists_card_eq
    apply IsPGroup.of_card (n := n * p)
    rw [hQcard, hn, pow_mul]
  have hQ1_pgroup : IsPGroup 2 Q1 :=
    IsPGroup.to_le hQ_pgroup hch.section3.section2.Q1_le_Q
  have hQ1_bot : Q1 = ⊥ :=
    claim_7_eq_bot_of_isPGroup_two_of_odd_card
      Q1 hQ1_pgroup hch.section3.section2.Q1_odd_order
  have horder_cases : orderOf (s * t) = 3 ∨ orderOf (s * t) = 5 := by
    rcases hcases with hlinear | hquadratic | hcubic
    · rcases hlinear with ⟨_, _, _, _, horder, _, _⟩
      exact Or.inl horder
    · rcases hquadratic with ⟨_, _, _, _, horder, _, _⟩
      exact Or.inr horder
    · rcases hcubic with ⟨_, _, _, _, _, _, _, _, horder, _, _⟩
      exact Or.inl horder
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with
    ⟨_hNcore, hnormal, _quotientAction, _hsmul, _hAbar,
      F, hF, hFfinite, hFnontrivial, unitEquiv, _hPO, hcharacteristic⟩
  letI : PFAppendixII.RightNearField F := hF
  letI : Finite F := hFfinite
  letI : Nontrivial F := hFnontrivial
  have hQnil : Group.IsNilpotent Q :=
    _root_.CFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
      H D Q K V W Q0 S Q1 t hch.section3.section2
  have hSclass : IsMulCommutative S ∨ PFAppendixIII.IsSuzukiTwoGroup S :=
    _root_.CFSG.BenderSuzuki.PFchapter1section2.corollary
      H D Q K V W Q0 S Q1 t hch.section3.section2
  have hStarCardUnits :
      Nat.card (nearFieldStar Q P) = Nat.card Fˣ :=
    Nat.card_congr unitEquiv.toEquiv
  have hpaired :
      (Nat.card (nearFieldStar Q P) = 2 ∧ orderOf (s * t) = 3) ∨
        (Nat.card (nearFieldStar Q P) = 4 ∧ orderOf (s * t) = 5) ∨
          (Nat.card (nearFieldStar Q P) = 8 ∧ orderOf (s * t) = 3) := by
    by_cases hcomm : IsMulCommutative (nearFieldStar Q P)
    · have h6 :=
        claim_6 H D Q K V W Q0 S Q1 P t s p (orderOf (s * t))
          hch hQ1_bot rfl
      dsimp only at h6
      rcases h6 with ⟨_hnormal6, _hnoncomm6, hcomm6⟩
      rcases (hcomm6 hcomm).1 with hstarSucc | hstarNine
      · rcases horder_cases with horder3 | horder5
        · left
          exact ⟨by omega, horder3⟩
        · right
          left
          exact ⟨by omega, horder5⟩
      · have hFcard : Nat.card F = 9 := by
          rw [Nat.card_eq_card_units_add_one, ← hStarCardUnits]
          exact hstarNine
        have horder_dvd : orderOf (s * t) ∣ 9 := by
          simpa [hcharacteristic, hFcard] using
            addOrderOf_dvd_natCard (1 : F)
        have horder_ne_five : orderOf (s * t) ≠ 5 := by
          intro horder5
          rw [horder5] at horder_dvd
          norm_num at horder_dvd
        right
        right
        exact ⟨by omega, horder_cases.resolve_right horder_ne_five⟩
    · obtain ⟨_hFnoncomm, hUnitsCard, hmodel⟩ :=
        claim_5_classify_nearFieldWitness Q S P hQnil
          hch.section3.section2.S_sylow_in_Q hSclass unitEquiv hcomm
      right
      right
      refine ⟨hStarCardUnits.trans hUnitsCard, ?_⟩
      exact hcharacteristic.symm.trans
        (claim_7_addOrderOf_one_eq_three_of_dickson_model hmodel)
  have hR_ne_Q : R ≠ Q := by
    intro hR_eq_Q
    have hX_le_CQ : X ≤ Subgroup.centralizer (Q : Set G) := by
      intro x hxX
      rw [Subgroup.mem_centralizer_iff]
      intro q hqQ
      have hqR : q ∈ R := by
        rw [hR_eq_Q]
        exact hqQ
      have hqCX : q ∈ CX := hqR.1
      exact ((Subgroup.mem_centralizer_iff.mp hqCX) x hxX).symm
    have hX_le_D : X ≤ D := by
      intro x hxX
      have hxW : x ∈ W := hxX.2
      rw [hWcentralizer] at hxW
      exact hxW.1
    have hDQbot : D ⊓ Subgroup.centralizer (Q : Set G) = ⊥ :=
      claim_7_D_inf_centralizer_Q_eq_bot
        H D Q t s hch.section3.section2.hA
          hch.section3.s_mem_H hch.section3.s_involution
          hch.section3.s_conjugate
    apply hX_ne
    rw [eq_bot_iff]
    intro x hxX
    rw [← hDQbot]
    exact ⟨hX_le_D hxX, hX_le_CQ hxX⟩
  have hQ0card : Nat.card Q0 = 2 ^ p :=
    (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.1
  have hQ0_le_Q : Q0 ≤ Q := hch.section3.section2.Q0_le_Q
  have hQ0_le_R : Q0 ≤ R := by
    intro q hqQ0
    exact ⟨hQ0_le_CX hqQ0, hQ0_le_Q hqQ0⟩
  rcases hpaired with hcaseTwo | hcaseFour | hcaseEight
  · have hQcardQ0 : Nat.card Q = Nat.card Q0 := by
      rw [hQcard, hcaseTwo.1, hQ0card]
    have hQ0_eq_Q : Q0 = Q :=
      Subgroup.eq_of_le_of_card_ge hQ0_le_Q (le_of_eq hQcardQ0)
    have hQ_le_CX : Q ≤ CX := by
      simpa [hQ0_eq_Q] using hQ0_le_CX
    apply hR_ne_Q
    change CX ⊓ Q = Q
    exact inf_eq_right.mpr hQ_le_CX
  · have hQcardSq : Nat.card Q = Nat.card Q0 ^ 2 := by
      calc
        Nat.card Q = 4 ^ p := by rw [hQcard, hcaseFour.1]
        _ = (2 ^ 2) ^ p := by norm_num
        _ = (2 ^ p) ^ 2 := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
        _ = Nat.card Q0 ^ 2 := by rw [hQ0card]
    have hRcardSq : Nat.card R = Nat.card Q0 ^ 2 := by
      rcases hcases with hlinear | hquadratic | hcubic
      · rcases hlinear with ⟨_, _, _, _, horder, _, _⟩
        omega
      · rcases hquadratic with ⟨_, _, _, _, _, _, hcard⟩
        simpa [R, CX, hellQ0] using hcard
      · rcases hcubic with ⟨_, _, _, _, _, _, _, _, horder, _, _⟩
        omega
    have hR_eq_Q : R = Q :=
      Subgroup.eq_of_le_of_card_ge inf_le_right
        (le_of_eq (hQcardSq.trans hRcardSq.symm))
    exact hR_ne_Q hR_eq_Q
  · have hQcardCube : Nat.card Q = Nat.card Q0 ^ 3 := by
      calc
        Nat.card Q = 8 ^ p := by rw [hQcard, hcaseEight.1]
        _ = (2 ^ 3) ^ p := by norm_num
        _ = (2 ^ p) ^ 3 := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
        _ = Nat.card Q0 ^ 3 := by rw [hQ0card]
    have hRcards :
        Nat.card R = Nat.card Q0 ∨ Nat.card R = Nat.card Q0 ^ 3 := by
      rcases hcases with hlinear | hquadratic | hcubic
      · rcases hlinear with ⟨_, _, _, _, _, _, hcard⟩
        left
        simpa [R, CX, hellQ0] using hcard
      · rcases hquadratic with ⟨_, _, _, _, horder, _, _⟩
        omega
      · rcases hcubic with ⟨_, _, _, _, _, _, _, _, _, _, hcard⟩
        right
        simpa [R, CX, hellQ0] using hcard.1
    rcases hRcards with hRcardLinear | hRcardCube
    · have hQ0_eq_R : Q0 = R :=
        Subgroup.eq_of_le_of_card_ge hQ0_le_R
          (le_of_eq hRcardLinear)
      have hStar_le_Q0 : nearFieldStar Q P ≤ Q0 := by
        simpa [hQ0_eq_R] using hStar_le_R
      have hStar_sq : ∀ z : nearFieldStar Q P, z ^ 2 = 1 := by
        intro z
        apply Subtype.ext
        have hzQ0 :=
          claim_1_Q0_sq H D Q K V W Q0 S Q1 P t s p hch
            ⟨(z : G), hStar_le_Q0 z.property⟩
        simpa using congrArg Subtype.val hzQ0
      have htwo :
          TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G)) :=
        claim_1_rank_two_subgroup_of_large_exp_two_subgroup
          (Q0 := nearFieldStar Q P)
          (C := Subgroup.centralizer (P : Set G)) inf_le_right
          (by omega) hStar_sq
      exact hch.B1.centralizer_has_two_rank_one htwo
    · have hR_eq_Q : R = Q :=
        Subgroup.eq_of_le_of_card_ge inf_le_right
          (le_of_eq (hQcardCube.trans hRcardCube.symm))
      exact hR_ne_Q hR_eq_Q

private theorem claim_7_N_inf_W_bot_of_case_elimination
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P N : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hN : N =
      D ⊓ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
        Subgroup.centralizer (P : Set G))
    :
    N ⊓ W = ⊥ := by
  by_contra hNW_ne_bot
  exact
    chapter2_claim7_N_inf_W_nontrivial_case_elimination
      H D Q K V W Q0 S Q1 P N t s p hch hind hN hNW_ne_bot

public theorem claim_7
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P N : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hN : N =
      D ⊓ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
        Subgroup.centralizer (P : Set G)) :
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let OmegaP : Type _ := {w : Ω // w ∈ fixedPointsOfSubgroup G Ω P}
    letI : MulAction C OmegaP := fixedPointCentralizerAction G Ω P
    let DP : Subgroup C := D.comap C.subtype
    let core : Subgroup C := pointStabilizerCore C OmegaP
    ∃ hnormal : core.Normal,
      letI : core.Normal := hnormal
      N = P ∧
        ∃ e : ↥(DP.map (QuotientGroup.mk' core)) ≃* ↥(W ⊓ C),
          ∀ a : ↥(DP.map (QuotientGroup.mk' core)),
            QuotientGroup.mk' core
              ⟨(e a : G), (e a).property.2⟩ = (a : C ⧸ core) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let OmegaP : Type _ := {w : Ω // w ∈ fixedPointsOfSubgroup G Ω P}
  letI : MulAction C OmegaP := fixedPointCentralizerAction G Ω P
  let DP : Subgroup C := D.comap C.subtype
  let core : Subgroup C := pointStabilizerCore C OmegaP
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with ⟨hNcoreDef, hnormal, _⟩
  have hNcore : N.subgroupOf C = core := by
    rw [hN]
    exact hNcoreDef
  refine ⟨hnormal, ?_⟩
  letI : core.Normal := hnormal
  have hdecomp : N = (N ⊓ W) ⊔ P :=
    claim_7_N_decomposition_obligation
      H D Q K V W Q0 S Q1 P N t s p hch hN
  have hNW : N ⊓ W = ⊥ :=
    claim_7_N_inf_W_bot_of_case_elimination
      H D Q K V W Q0 S Q1 P N t s p hch hind hN
  have hNP : N = P := by
    calc
      N = (N ⊓ W) ⊔ P := hdecomp
      _ = P := by simp [hNW]
  rcases claim_1 H D Q K V W Q0 S Q1 P t s p hch with
    ⟨_hV, _hQ0, _hNormP, hDirect⟩
  rcases hDirect with
    ⟨hWC_le_DCP, hP_le_DCP, hWC_norm_DCP, _hP_norm_DCP,
      hdisj, hsup, _hcomm⟩
  exact ⟨hNP, claim_7_sigmaBar_mulEquiv_CW
    D W P N C core hNcore hNP hWC_le_DCP hP_le_DCP
      hWC_norm_DCP hdisj hsup⟩
end PFchapter2
end CFSG.BenderSuzuki
