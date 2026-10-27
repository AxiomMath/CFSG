module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKMod
public import CFSG.LocalAnalysis.WeakClosure81.SevenSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp78 (V H E J L : Subgroup G) : Prop extends Hyp73 V H E J where
  oddCore : fusionOddCoreOf (kSub V H E) = ⊥
  transitive : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k
  le_kSub : L ≤ kSub V H E
  generated : IsGeneratedByOmega V H E L
  left_le : V ≤ L
  quot : HasQuotShape L (pCoreOf 2 L : Set G) (fun X _ => IsSymGp X 3)
  four_le : 4 ≤ Set.ncard {W : Subgroup G | ∃ g ∈ pCoreOf 2 L, W = conjSubgroup V g ⊔ J}

section General

private theorem relIndex_conjSubgroup_eq (A B : Subgroup G) (k : G) :
    (conjSubgroup A k).relIndex (conjSubgroup B k) = A.relIndex B := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj k⁻¹).injective

theorem commutator_le_of_two_lt_relIndex {V H E J L N : Subgroup G} (h : Hyp73 V H E J)
    (htr : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k)
    (hbig : 2 < J.relIndex V) (hLK : L ≤ kSub V H E) (hL : IsGeneratedByOmega V H E L)
    (hNK : N ≤ kSub V H E) (hNnorm : kSub V H E ≤ Subgroup.normalizer (N : Set G))
    (hJN : kSub V H E ⊓ J ≤ N) (hNodd : Odd ((kSub V H E ⊓ J).relIndex N)) :
    ⁅L, N⁆ ≤ J := by
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hJleH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.jnormal
  have hrel : ∀ U ∈ omegaSet V H E, J.relIndex U = J.relIndex V := by
    intro U hU
    obtain ⟨k, hkK, rfl⟩ := htr U hU
    have hkH : k ∈ H := hKleH hkK
    have hJk : conjSubgroup J k = J :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormH hkH)
    have hstep : (conjSubgroup J k).relIndex (conjSubgroup V k) = J.relIndex V :=
      relIndex_conjSubgroup_eq J V k
    rwa [hJk] at hstep
  have hNleH : N ≤ H := hNK.trans hKleH
  have hRodd : Odd (J.relIndex (N ⊔ J)) := by
    haveI : (J.subgroupOf H).Normal := h.jnormal
    have hsup_le : N ⊔ J ≤ H := sup_le hNleH hJleH
    have h1 : (J.subgroupOf H).relIndex (N.subgroupOf H ⊔ J.subgroupOf H) =
        (J.subgroupOf H).relIndex (N.subgroupOf H) :=
      Subgroup.relIndex_sup_right (N.subgroupOf H) (J.subgroupOf H)
    have h2 : (J.subgroupOf H).relIndex ((N ⊔ J).subgroupOf H) = J.relIndex (N ⊔ J) :=
      Subgroup.relIndex_subgroupOf hsup_le
    have h3 : (J.subgroupOf H).relIndex (N.subgroupOf H) = J.relIndex N :=
      Subgroup.relIndex_subgroupOf hNleH
    have h4 : J.relIndex (N ⊔ J) = J.relIndex N := by
      rw [← h2, Subgroup.subgroupOf_sup hNleH hJleH, h1, h3]
    have h5 : J.relIndex N = (kSub V H E ⊓ J).relIndex N := by
      have hEq : J ⊓ N = (kSub V H E ⊓ J) ⊓ N := by
        rw [inf_assoc]
        exact (inf_eq_right.mpr (inf_le_right.trans hNK)).symm
      rw [← Subgroup.inf_relIndex_right J N,
        ← Subgroup.inf_relIndex_right (kSub V H E ⊓ J) N, hEq]
    rw [h4, h5]
    exact hNodd
  have hUN : ∀ U ∈ omegaWithin V H E L, ⁅U, N⁆ ≤ J := by
    intro U hU
    have hUΩ : U ∈ omegaSet V H E := hU.1
    have hUnormR : U ≤ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G) :=
      (le_inf ((le_kSub hUΩ).trans hNnorm)
        ((h.omega_le U hUΩ).trans hJnormH)).trans (inf_normalizer_le_normalizer_sup N J)
    have hUR : ⁅U, N ⊔ J⁆ ≤ J :=
      seven_three_five (V := U) (H := H) (E := E) (J := J) (R := N ⊔ J)
        (isElemAbelian_of_mem_omegaSet h.elemAbelian hUΩ)
        (isTI_of_mem_omegaSet hUΩ h.ti) h.abelian h.le h.normal
        (by rw [omegaSet_eq_of_mem hUΩ]; exact hUΩ)
        (by rw [omegaSet_eq_of_mem hUΩ]; exact h.omega_le)
        h.pcore_le h.jnormal (by rw [iSub_eq_of_mem hUΩ]; exact h.iSub_le)
        (by rw [hrel U hUΩ]; exact hbig)
        le_sup_right (sup_le hNleH hJleH) hUnormR hRodd
    exact (Subgroup.commutator_mono_right le_sup_left).trans hUR
  refine Subgroup.commutator_le.mpr fun l hl n hn => ?_
  have hgen : (⨆ U : {U : Subgroup G // U ∈ omegaWithin V H E L}, (U : Subgroup G)) = L := by
    rw [show (⨆ U : {U : Subgroup G // U ∈ omegaWithin V H E L}, (U : Subgroup G))
        = (⨆ (U : Subgroup G) (_ : U ∈ omegaWithin V H E L), U) from
      iSup_subtype'' (omegaWithin V H E L) (fun U : Subgroup G => U)]
    exact hL
  have hmem : ∀ (i : {U : Subgroup G // U ∈ omegaWithin V H E L}), ∀ x ∈ (i : Subgroup G),
      x ∈ L ∧ ∀ n ∈ N, ⁅x, n⁆ ∈ J := by
    intro i x hx
    exact ⟨i.2.2 hx, fun n hn => hUN i.1 i.2 (Subgroup.commutator_mem_commutator hx hn)⟩
  have hone : (1 : G) ∈ L ∧ ∀ n ∈ N, ⁅(1 : G), n⁆ ∈ J :=
    ⟨L.one_mem, fun n _ => by simp⟩
  have hmul : ∀ x y : G, (x ∈ L ∧ ∀ n ∈ N, ⁅x, n⁆ ∈ J) →
      (y ∈ L ∧ ∀ n ∈ N, ⁅y, n⁆ ∈ J) →
      (x * y ∈ L ∧ ∀ n ∈ N, ⁅x * y, n⁆ ∈ J) := by
    rintro x y ⟨hxL, hxC⟩ ⟨hyL, hyC⟩
    refine ⟨L.mul_mem hxL hyL, fun n hn => ?_⟩
    have hxH : x ∈ H := hKleH (hLK hxL)
    have hxn : x * ⁅y, n⁆ * x⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hJnormH hxH) ⁅y, n⁆).mp (hyC n hn)
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact J.mul_mem hxn (hxC n hn)
  have hCl : l ∈ L ∧ ∀ n ∈ N, ⁅l, n⁆ ∈ J :=
    Subgroup.iSup_induction
      (fun i : {U : Subgroup G // U ∈ omegaWithin V H E L} => (i : Subgroup G))
      (C := fun x => x ∈ L ∧ ∀ n ∈ N, ⁅x, n⁆ ∈ J)
      (by rw [hgen]; exact hl) hmem hone hmul
  exact hCl.2 n hn

theorem seven_eight_relIndex_conjSubgroup_eq_two {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) {x : G} (hx : x ∈ pCoreOf 2 L) :
    J.relIndex (conjSubgroup V x) = 2 := by
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLleH : L ≤ H := h.le_kSub.trans hKleH
  have hxL : x ∈ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hx
  have hJleH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.jnormal
  have hJx : conjSubgroup J x = J :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormH (hLleH hxL))
  have hstep : (conjSubgroup J x).relIndex (conjSubgroup V x) = J.relIndex V :=
    relIndex_conjSubgroup_eq J V x
  rw [hJx, hV2] at hstep
  exact hstep

theorem seven_eight_inf_J_le_pCoreOf {V H E J L : Subgroup G} (h : Hyp78 V H E J L) :
    L ⊓ J ≤ pCoreOf 2 L := by
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLleH : L ≤ H := h.le_kSub.trans hKleH
  have hJleH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.jnormal
  have hJ2 : IsPGroup 2 J :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le h.pcore_le
  have h2 : IsPGroup 2 (L ⊓ J : Subgroup G) := hJ2.to_le inf_le_right
  have hnorm : ((L ⊓ J).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact (le_inf le_normalizer (hLleH.trans hJnormH)).trans
      (inf_normalizer_le_normalizer_inf (H := L) (K := J))
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hnorm h2

theorem seven_eight_commutator_conj_eq_bot {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    {x y : G} (hx : x ∈ pCoreOf 2 L) (hy : y ∈ pCoreOf 2 L) :
    ⁅conjSubgroup V x, conjSubgroup V y⁆ = ⊥ := by
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLleH : L ≤ H := h.le_kSub.trans hKleH
  have hxL : x ∈ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hx
  have hyL : y ∈ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hy
  let Q : Subgroup G := pCoreOf 2 L
  have hLnormQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hVp : IsPGroup 2 V :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian h.elemAbelian
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hVQp : IsPGroup 2 (V ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hVp hQp (h.left_le.trans hLnormQ)
  have hmemVQ : ∀ {q : G}, q ∈ Q → conjSubgroup V q ≤ V ⊔ Q := by
    intro q hq u hu
    rw [mem_conjSubgroup_iff] at hu
    have hqQ : q⁻¹ ∈ Q := Q.inv_mem hq
    have hwV : q * u * q⁻¹ ∈ V := hu
    have h1 : (q * u * q⁻¹)⁻¹ * q⁻¹ * (q * u * q⁻¹) ∈ Q := by
      have hg : (q * u * q⁻¹)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        hLnormQ (h.left_le (V.inv_mem hwV))
      rw [Subgroup.mem_normalizer_iff] at hg
      simpa using (hg q⁻¹).mp hqQ
    have hmemQ : (q * u * q⁻¹)⁻¹ * q⁻¹ * (q * u * q⁻¹) * q ∈ Q :=
      Q.mul_mem h1 hq
    have hmem : (q * u * q⁻¹) * ((q * u * q⁻¹)⁻¹ * q⁻¹ * (q * u * q⁻¹) * q) ∈ V ⊔ Q :=
      Subgroup.mul_mem_sup hwV hmemQ
    rwa [show (q * u * q⁻¹) * ((q * u * q⁻¹)⁻¹ * q⁻¹ * (q * u * q⁻¹) * q) = u by group]
      at hmem
  have hxΩ : conjSubgroup V x ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem (hLleH hxL)
  have hyΩ : conjSubgroup V y ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem (hLleH hyL)
  obtain ⟨a, b, ha, hb, hNab⟩ :=
    nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian hxΩ hyΩ
  have hN : conjSubgroup V x ⊓ Subgroup.normalizer (conjSubgroup V y : Set G) ≠ ⊥ := by
    rw [ha, hb]
    exact hNab
  have hP : IsPGroup 2 ↥(conjSubgroup V x ⊔ conjSubgroup V y) :=
    hVQp.to_le (sup_le (hmemVQ hx) (hmemVQ hy))
  have hcomm := commute_of_isPGroup_sup h.elemAbelian h.ti ⟨x, rfl⟩ ⟨y, rfl⟩ hN hP
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (hcomm u hu v hv).symm

end General

end CFSG.LocalAnalysis.WeakClosure81
