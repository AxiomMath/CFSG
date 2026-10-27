module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.GroupTheory.TwoResidualModPCore
public import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1A5
public import CFSG.Quasithin.Vol2.Ch7Bridge326

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.RankThree.PartTwo.Sec19.Step1911EndProof (phiL phiL_surjective phiL_eq_one_iff)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_26a_First_holds
    {D : Data G} {V₀ V : Subgroup G}
    (hW3 : W3Lem71 G) (hK2 : K_J2_centralizer_shape) :
    Gap17_26a_First D V₀ V := by
  intro L c hm hJ2 hN h242 A hA _ h hh hO hres
  classical
  have hV := c.hyp125.isElemAbelian
  have hpair := c.hyp125.pairFacts
  set H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian with hH₁
  set K : Subgroup G := CFSG.Quasithin.twoResidual H₁ with hK
  set X : Subgroup G := A ⊔ conjSubgroup A h with hX
  set U : Subgroup G := A ⊓ normalizer (conjSubgroup A h) with hU
  set B : Subgroup G := conjSubgroup A h ⊓ normalizer (A : Set G) with hB
  have hAH : A ≤ H₁ := hA.1.trans (T_le_H17_25_one c.hyp125)
  have hAhH : conjSubgroup A h ≤ H₁ := by
    intro x hx
    change x ∈ A.map (MulAut.conj h⁻¹).toMonoidHom at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact H₁.mul_mem (H₁.mul_mem (H₁.inv_mem hh) (hAH ha)) (by simpa using hh)
  have hXH : X ≤ H₁ := by
    rw [hX]
    exact sup_le hAH hAhH
  have hsup : K = X ⊔ pCoreOf 2 K := by
    rw [hK, hX, hH₁]
    exact hres
  have hXK : X ≤ K := by
    rw [hsup]
    exact le_sup_left
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, mSub, CFSG.Quasithin.rk_bot] at hm
    omega
  have hV0ti : IsTI V₀ := by
    rcases c.hyp125.1 with ⟨-, hbot⟩ | ⟨hV0, -, -⟩
    · exact absurd hbot hV0ne
    · exact hV0.2.2.2.1
  have hV0p : IsPGroup 2 V₀ := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian
    hpair.elemAbelian₀
  obtain ⟨-, gA, hAgA, hquot⟩ := hA
  have hAeq : A = conjSubgroup V₀ gA :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV0p gA) hAgA).mp hquot
  have hAelem : IsElemAbelian 2 A := by
    rw [hAeq]
    exact E3.isElemAbelian_conjSubgroup hpair.elemAbelian₀ gA
  have hATI : IsTI A := by
    have h := CFSG.RankThree.GF2n.isTI_conjSubgroup hV0ti gA⁻¹
    have heq : A = CFSG.CGT.Timmesfeld75.conjSubgroup gA⁻¹ V₀ := by
      rw [hAeq]
      rfl
    rwa [heq]
  have hAcard_big : 32 ≤ Nat.card A := by
    rw [hAeq, E3.card_conjSubgroup, card_eq_two_pow_mSub hV0p]
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAcard_two : 2 < Nat.card A := by omega
  have hHyp7 : Hyp7 A := ⟨hAelem, hAcard_two, hATI⟩
  have hNconj : conjSubgroup (Subgroup.normalizer (A : Set G)) h =
      Subgroup.normalizer (conjSubgroup A h : Set G) :=
    E3.conjSubgroup_normalizer A h
  have hnotMem : h ∉ Subgroup.normalizer (A : Set G) := by
    intro hhN
    apply hO.1.1
    rw [CFSG.QuasithinUnique.C5.conjSubgroup_eq_self hhN]
    exact Subgroup.le_normalizer
  have hmq : E3.mQuot A U ≤ 2 := by
    have hEq : E3.mQuot A U = E3.mQuot A
        (conjSubgroup (Subgroup.normalizer (A : Set G)) h) := by
      unfold E3.mQuot
      rw [hU, ← hNconj, inf_comm, Subgroup.inf_relIndex_right]
    rw [hEq]
    exact hO.1.2.1
  have hAp : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAelem
  have hUleA : U ≤ A := by
    rw [hU]
    exact inf_le_left
  have hpowmq : 2 ^ E3.mQuot A U ≤ 4 := by
    calc 2 ^ E3.mQuot A U ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hmq
      _ = 4 := by norm_num
  have hUbot : U ≠ ⊥ := by
    have hcard := E3.card_eq_two_pow_mul hAp hUleA
    have hcard_le : 32 ≤ 2 ^ E3.mQuot A U * Nat.card U := by
      rw [← hcard]
      exact hAcard_big
    have hUge : 8 ≤ Nat.card U := by
      by_contra hlt
      have hUle : Nat.card U ≤ 7 := by omega
      have hmul : 2 ^ E3.mQuot A U * Nat.card U ≤ 4 * 7 :=
        Nat.mul_le_mul hpowmq hUle
      omega
    intro hUbot
    rw [hUbot, Subgroup.card_bot] at hUge
    omega
  have hUneA : U ≠ A := by
    intro hUA
    apply hO.2.1
    rw [hNconj]
    have hle : U ≤ Subgroup.normalizer (conjSubgroup A h : Set G) := inf_le_right
    rw [hUA] at hle
    exact hle
  have hcomm : ⁅A, conjSubgroup A h⁆ ≠ ⊥ := by
    intro hbot
    apply hO.2.1
    rw [hNconj]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨hO2X, -, hcommUB, hshapeX, -, -⟩ :=
    hW3 A h hHyp7 hnotMem hUbot hUneA hcomm
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN
  have hL1 : barSub V₀ V hV L ≠ ⊥ := by
    have hsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
    have hcardW : Nat.card (Vtil V₀ V hV) = 2 ^ 12 := by
      rw [← Subgroup.card_top (G := Vtil V₀ V hV),
        CFSG.Quasithin.card_eq_two_pow hsq ⊤, CFSG.Quasithin.rk_top, h242.2.1]
    exact ne_bot_of_isIrrOn_of_two_lt_card hsq h242.1 (by rw [hcardW]; norm_num)
  obtain ⟨eK₁⟩ := CFSG.GroupTheory.nonempty_twoResidual_quot_pCore_mulEquiv H₁
  obtain ⟨eK₂⟩ := CFSG.GroupTheory.nonempty_twoResidual_top_mulEquiv_alt5
    (gap17_25_H1_shape_core D V₀ V hK2 L c hJ2 hMnorm hL1)
  have hO2eq : pCoreOf 2 X = X ⊓ pCoreOf 2 K := PartTwo.pCoreOf_eq_inf hXK hsup
  let q : ↥X →* alternatingGroup (Fin 5) := (eK₁.trans eK₂).toMonoidHom.comp (phiL hXK)
  have hqsurj : Function.Surjective q :=
    (eK₁.trans eK₂).surjective.comp (phiL_surjective hXK hsup)
  have hqkerO2 : q.ker = (pCoreOf 2 X).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, phiL_eq_one_iff, Subgroup.mem_subgroupOf, hO2eq]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  let eX : Bar2 X ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq
      (hqkerO2.trans (CFSG.openPCoreOf_subgroupOf 2 X))).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective q hqsurj)
  obtain ⟨Z, instZ, φ, hφsurj, hφker, hP⟩ := hshapeX
  have hφker' : φ.ker = (pCoreOf 2 X).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker]
    exact hφker x
  have hkerEq : φ.ker = CFSG.pCore 2 ↥X := by
    rw [hφker', ← CFSG.openPCoreOf_subgroupOf 2 X]
  let eZX : Z ≃* Bar2 X :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerEq)
  let eZA : Z ≃* alternatingGroup (Fin 5) := eZX.trans eX
  have hA60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  have hmq_eq : E3.mQuot A U = 2 := by
    rcases hP with ⟨n, hL2, hn⟩ | ⟨n, hSz, hn⟩ | ⟨m, hm_odd, ⟨eD⟩, hn⟩
    · have h2n : 2 ≤ n := CFSG.Quasithin.H13.two_le_of_lieModel_psl_two hL2
      rw [hn] at hmq ⊢
      omega
    · have h3n : 3 ≤ n := (s13_odd_three_le_of_isSz hSz).2
      rw [hn] at hmq
      omega
    · exfalso
      have hAD : ↥(alternatingGroup (Fin 5)) ≃* DihedralGroup m := eZA.symm.trans eD
      have : Group.IsSolvable (DihedralGroup m) :=
        CFSG.Quasithin.Dickson.isSolvable_dihedral m
      have hsolv : Group.IsSolvable ↥(alternatingGroup (Fin 5)) :=
        Group.isSolvable_of_isSolvable_injective (f := hAD.toMonoidHom) hAD.injective
      have : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
        Group.isPerfect_def.mpr (by
          rw [_root_.commutator_def]
          exact commutator_alternatingGroup_eq_top (α := Fin 5) (by simp))
      exact Group.IsPerfect.not_isSolvable _ hsolv
  have hdisj : A ⊓ conjSubgroup A h = ⊥ := by
    have hTIy : A ⊓ conjSubgroup A h = ⊥ ∨ A ⊓ conjSubgroup A h = A := by
      have heq : CFSG.CGT.Timmesfeld75.conjSubgroup h⁻¹ A = conjSubgroup A h := by
        rfl
      have h := hATI h⁻¹
      rwa [heq] at h
    rcases hTIy with hbot | htop
    · exact hbot
    · exfalso
      have hAle : A ≤ conjSubgroup A h := by
        have hle : A ⊓ conjSubgroup A h ≤ conjSubgroup A h := inf_le_right
        rwa [htop] at hle
      have hAeq' : A = conjSubgroup A h :=
        Subgroup.eq_of_le_of_card_ge hAle (by rw [E3.card_conjSubgroup])
      exact hnotMem (conjSubgroup_eq_iff_mem_normalizer.mp hAeq'.symm)
  have hUA : U ≤ A := by
    rw [hU]
    exact inf_le_left
  have hUBle : B ≤ conjSubgroup A h := by
    rw [hB]
    exact inf_le_left
  have hBleN : B ≤ Subgroup.normalizer (A : Set G) := by
    rw [hB]
    exact inf_le_right
  have hcomm_el : ∀ u ∈ U, ∀ b ∈ B, u * b = b * u := by
    intro u hu b hb
    have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommUB) hu
    exact ((Subgroup.mem_centralizer_iff.mp hc) b hb).symm
  have hAinter : A ⊓ pCoreOf 2 X = U := by
    rw [hO2X]
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxA, hxUB⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨u, huU, b, hbB, rfl⟩ :=
        CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm_el hxUB
      have hbA : b ∈ A := by
        have hb_eq : b = u⁻¹ * (u * b) := by group
        rw [hb_eq]
        exact A.mul_mem (A.inv_mem (hUA huU)) hxA
      have hbBot : b ∈ A ⊓ conjSubgroup A h := ⟨hbA, hUBle hbB⟩
      rw [hdisj, Subgroup.mem_bot] at hbBot
      subst hbBot
      simpa using huU
    · exact le_inf hUA le_sup_left
  have hABbot : A ⊓ B = ⊥ := by
    refine le_bot_iff.mp ?_
    calc A ⊓ B ≤ A ⊓ conjSubgroup A h := inf_le_inf_left A hUBle
      _ = ⊥ := hdisj
  have hcardAB : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
    have h := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (A := B) (B := A) hBleN
    rw [sup_comm, inf_comm, mul_comm (Nat.card B) (Nat.card A),
      hABbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hAO2card : Nat.card ↥(A ⊔ pCoreOf 2 X) = Nat.card ↥A * Nat.card ↥B := by
    rw [hO2X, ← sup_assoc, sup_eq_left.mpr hUA]
    exact hcardAB
  have hBne : B ≠ conjSubgroup A h := by
    intro hBeq
    have hAleN : conjSubgroup A h ≤ Subgroup.normalizer (A : Set G) := hBeq ▸ hBleN
    have hAhp : IsPGroup 2 (conjSubgroup A h) := E3.isPGroup_conjSubgroup hAp h
    have hX2 : IsPGroup 2 X := by
      rw [hX]
      exact IsPGroup.to_sup_of_normal_left' hAp hAhp hAleN
    have hbar1 : Nat.card (Bar2 X) = 1 := by
      change Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 1
      rw [← CFSG.openPCoreOf_subgroupOf 2 X, CFSG.Quasithin.F6.pCoreOf_eq_self_of_isPGroup hX2,
        Subgroup.subgroupOf_self]
      exact Subgroup.index_top
    have hbar60 : Nat.card (Bar2 X) = 60 := by
      rw [Nat.card_congr eX.toEquiv, hA60]
    omega
  have hBlt : B < conjSubgroup A h := lt_of_le_of_ne hUBle hBne
  have hBltcard : Nat.card B < Nat.card A := by
    have h := Subgroup.card_lt_of_lt hBlt
    rwa [E3.card_conjSubgroup] at h
  have hAX : A ≤ X := by
    rw [hX]
    exact le_sup_left
  let fA : ↥A →* ↥(alternatingGroup (Fin 5)) := q.comp (Subgroup.inclusion hAX)
  have hfAker : fA.ker = U.subgroupOf A := by
    ext a
    change q (Subgroup.inclusion hAX a) = 1 ↔ (a : G) ∈ U
    constructor
    · intro h
      have hq : (a : G) ∈ pCoreOf 2 X := by
        have hmem : Subgroup.inclusion hAX a ∈ q.ker := h
        rw [hqkerO2, Subgroup.mem_subgroupOf] at hmem
        exact hmem
      rw [← hAinter]
      exact ⟨a.2, hq⟩
    · intro h
      have hq : (a : G) ∈ pCoreOf 2 X := by
        have hUleO2 : U ≤ pCoreOf 2 X := by
          rw [← hAinter]
          exact inf_le_right
        exact hUleO2 h
      have hmem : Subgroup.inclusion hAX a ∈ q.ker := by
        rw [hqkerO2, Subgroup.mem_subgroupOf]
        exact hq
      exact hmem
  let P : Subgroup ↥(alternatingGroup (Fin 5)) := (A.subgroupOf X).map q
  have hfArange : fA.range = P := by
    show (q.comp (Subgroup.inclusion hAX)).range = P
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by apply Subtype.ext; rfl⟩
  have hcardker : Nat.card ↥(fA.ker) = Nat.card ↥U := by
    rw [hfAker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv
  have hcardrange : Nat.card ↥(fA.range) = Nat.card P := by
    rw [hfArange]
  have hcardA1 : Nat.card ↥A = 4 * Nat.card ↥U := by
    have h := E3.card_eq_two_pow_mul hAp hUleA
    rw [hmq_eq] at h
    norm_num at h
    exact h
  have hcardA2 : Nat.card ↥A = Nat.card ↥U * Nat.card P := by
    have h := CFSG.ABGLocalTools.card_eq_card_ker_mul_of_surjective
      (f := fA.rangeRestrict) fA.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict, hcardker, hcardrange] at h
    exact h
  have hPcard : Nat.card P = 4 := by
    have h1 : 4 * Nat.card ↥U = Nat.card P * Nat.card ↥U := by
      rw [mul_comm (Nat.card P) (Nat.card ↥U), ← hcardA2, hcardA1]
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  obtain ⟨z, hzN, hzord⟩ := CFSG.Quasithin.H13.A5Syl.exists_orderOf_three P hPcard
  obtain ⟨y, hyq⟩ := hqsurj z
  have hzN_inv : z⁻¹ ∈ Subgroup.normalizer (P : Set ↥(alternatingGroup (Fin 5))) :=
    Subgroup.inv_mem _ hzN
  have hAy_le : conjSubgroup A y ≤ A ⊔ pCoreOf 2 X := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hw
    have haX : a ∈ X := hAX ha
    let ax : ↥X := ⟨a, haX⟩
    have hax : ax ∈ A.subgroupOf X := Subgroup.mem_subgroupOf.mpr ha
    have hqa : q ax ∈ P := Subgroup.mem_map_of_mem q hax
    have hzn : z⁻¹ * q ax * z ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hzN_inv (q ax)).mp hqa
    obtain ⟨a', haX', ha'q⟩ := Subgroup.mem_map.mp hzn
    have ha'A : (a' : G) ∈ A := Subgroup.mem_subgroupOf.mp haX'
    have hyconj_mem : (y : G)⁻¹ * a * (y : G) ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem y.2) haX) y.2
    let yconj : ↥X := ⟨(y : G)⁻¹ * a * (y : G), hyconj_mem⟩
    have hyconj : q yconj = z⁻¹ * q ax * z := by
      have hyx : yconj = (y : ↥X)⁻¹ * ax * (y : ↥X) := Subtype.ext rfl
      rw [hyx, map_mul, map_mul, map_inv, hyq]
    have hprod1 : q (yconj * (Subgroup.inclusion hAX ⟨(a' : G), ha'A⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      change q yconj * (q ⟨(a' : G), hAX ha'A⟩)⁻¹ = 1
      have ha'q' : q ⟨(a' : G), hAX ha'A⟩ = z⁻¹ * q ax * z := ha'q
      rw [hyconj, ha'q', mul_inv_cancel]
    have hk : ((y : G)⁻¹ * a * (y : G)) * (a' : G)⁻¹ ∈ pCoreOf 2 X := by
      have hmem : yconj * (Subgroup.inclusion hAX ⟨(a' : G), ha'A⟩)⁻¹ ∈ q.ker := hprod1
      rw [hqkerO2, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    change (MulAut.conj (y : G)⁻¹) a ∈ A ⊔ pCoreOf 2 X
    have heq : (MulAut.conj (y : G)⁻¹) a =
        (((MulAut.conj (y : G)⁻¹) a) * (a' : G)⁻¹) * (a' : G) := by
      simp only [MulAut.conj_apply, inv_inv]
      group
    rw [heq]
    have hk' : (MulAut.conj (y : G)⁻¹) a * (a' : G)⁻¹ ∈ pCoreOf 2 X := by
      simpa only [MulAut.conj_apply, inv_inv] using hk
    exact (A ⊔ pCoreOf 2 X).mul_mem
      ((le_sup_right : pCoreOf 2 X ≤ A ⊔ pCoreOf 2 X) hk')
      ((le_sup_left : A ≤ A ⊔ pCoreOf 2 X) ha'A)
  have hprod_sub : ((A : Set G) * (conjSubgroup A y : Set G)) ⊆
      ((A ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    rintro x ⟨a, ha, c, hc, rfl⟩
    exact (A ⊔ pCoreOf 2 X).mul_mem
      ((le_sup_left : A ≤ A ⊔ pCoreOf 2 X) ha) (hAy_le hc)
  have hprod_card_le : Nat.card ↥((A : Set G) * (conjSubgroup A y : Set G)) ≤
      Nat.card ↥(A ⊔ pCoreOf 2 X) := by
    simpa only [SetLike.coe_sort_coe] using
      Nat.card_mono (Set.toFinite ((A ⊔ pCoreOf 2 X : Subgroup G) : Set G)) hprod_sub
  have hprod_formula :=
    CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf A (conjSubgroup A y)
  have hAyeq : Nat.card (conjSubgroup A y) = Nat.card A := E3.card_conjSubgroup A y
  rw [hAyeq] at hprod_formula
  have hAle : Nat.card A ≤ Nat.card B * Nat.card ↥(A ⊓ conjSubgroup A y) := by
    have h1 : Nat.card A * Nat.card A ≤
        Nat.card ↥(A ⊔ pCoreOf 2 X) * Nat.card ↥(A ⊓ conjSubgroup A y) := by
      rw [← hprod_formula]
      exact Nat.mul_le_mul_right _ hprod_card_le
    rw [hAO2card] at h1
    have h2 : Nat.card A * Nat.card A ≤
        Nat.card A * (Nat.card B * Nat.card ↥(A ⊓ conjSubgroup A y)) := by
      calc Nat.card A * Nat.card A
          ≤ (Nat.card A * Nat.card B) * Nat.card ↥(A ⊓ conjSubgroup A y) := h1
        _ = Nat.card A * (Nat.card B * Nat.card ↥(A ⊓ conjSubgroup A y)) := by
              rw [mul_assoc]
    exact Nat.le_of_mul_le_mul_left h2 Nat.card_pos
  have hInter_gt_one : 1 < Nat.card ↥(A ⊓ conjSubgroup A y) := by
    by_contra h
    have hle1 : Nat.card ↥(A ⊓ conjSubgroup A y) ≤ 1 := by omega
    have hmulB : Nat.card B * Nat.card ↥(A ⊓ conjSubgroup A y) ≤ Nat.card B * 1 :=
      Nat.mul_le_mul_left _ hle1
    have hBlt : Nat.card B < Nat.card A := hBltcard
    omega
  have hInter_ne_bot : A ⊓ conjSubgroup A y ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hInter_gt_one
    omega
  have hTIy : A ⊓ conjSubgroup A y = ⊥ ∨ A ⊓ conjSubgroup A y = A := by
    have heq : CFSG.CGT.Timmesfeld75.conjSubgroup (y : G)⁻¹ A = conjSubgroup A y := by
      rfl
    have h := hATI (y : G)⁻¹
    rwa [heq] at h
  have hAyeqA : conjSubgroup A y = A := by
    rcases hTIy with hbot | htop
    · exact absurd hbot hInter_ne_bot
    · have hAle : A ≤ conjSubgroup A y := by
        have hle : A ⊓ conjSubgroup A y ≤ conjSubgroup A y := inf_le_right
        rwa [htop] at hle
      exact (Subgroup.eq_of_le_of_card_ge hAle (by rw [E3.card_conjSubgroup])).symm
  have hyN : (y : G) ∈ Subgroup.normalizer (A : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hAyeqA
  have h3ord : 3 ∣ orderOf y := by
    have hz3 : orderOf (q y) = 3 := by rw [hyq]; exact hzord
    have hdvd : orderOf (q y) ∣ orderOf y :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    rwa [hz3] at hdvd
  have h3dvd_final : 3 ∣ Nat.card ↥(X ⊓ Subgroup.normalizer (A : Set G)) := by
    have hyX : (y : G) ∈ X := y.2
    let yy : ↥(X ⊓ Subgroup.normalizer (A : Set G)) := ⟨(y : G), ⟨hyX, hyN⟩⟩
    have hdvd : orderOf yy ∣ Nat.card ↥(X ⊓ Subgroup.normalizer (A : Set G)) :=
      orderOf_dvd_natCard yy
    have hyy : orderOf yy = orderOf y := by
      rw [← Subgroup.orderOf_coe yy, ← Subgroup.orderOf_coe y]
    rw [hyy] at hdvd
    exact h3ord.trans hdvd
  rw [hX] at h3dvd_final
  exact h3dvd_final

