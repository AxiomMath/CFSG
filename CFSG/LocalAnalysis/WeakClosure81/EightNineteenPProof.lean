module

public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenP
public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenPQ
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPSit
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPSetupB
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPPull
public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenPSylowA
public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenPSylowB
public import CFSG.LocalAnalysis.WeakClosure81.FiveSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

private theorem wc819pp_cGrp_normal {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : ((cGrp H T).subgroupOf K).Normal := by
  have hCH : cGrp H T ≤ H := h.concl813.comp.2.1.trans h.concl813.comp.2.2.1
  have hKH : K ≤ H := h.concl813.sub_L.trans h.concl813.comp.2.2.1
  have hHnorm : H ≤ Subgroup.normalizer (cGrp H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mp h.concl813.comp.1
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.concl813.ge_C).mpr (hKH.trans hHnorm)

private theorem wc819pp_le_oTwoMod_self {N K : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) : N ≤ oTwoMod N K :=
  le_iSup₂ (f := fun W (_ : W ∈ {W : Subgroup G | N ≤ W ∧ W ≤ K ∧
    (W.subgroupOf K).Normal ∧ ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ N}) => W) N
    ⟨le_rfl, hNK, hN, fun w hw => ⟨0, by simpa using hw⟩⟩

private theorem wc819pp_oTwoMod_le_self {N K : Subgroup G} : oTwoMod N K ≤ K :=
  iSup₂_le fun _ hW => hW.2.1

private theorem wc819pp_conjClosure_le_self {L H : Subgroup G} (hLH : L ≤ H) :
    conjClosure L H ≤ H :=
  conjClosure_le fun a ha z hz => H.mul_mem (H.mul_mem ha (hLH hz)) (H.inv_mem ha)

private theorem wc819pp_sylow_two_sup {J T : Subgroup G} (hTJ : T ≤ normalizer (J : Set G))
    (hT : IsPGroup 2 ↥T) (hS : IsSylowIn 2 (T ⊓ J) J) : IsSylowIn 2 T (J ⊔ T) :=
  CFSG.Quasithin.E1.isSylowIn_two_of_sup_inf hTJ hT hS

private theorem wc819pp_frattini {J D Y : Subgroup G} (hJD : J ≤ D)
    (hDJ : D ≤ normalizer (J : Set G)) (hY : IsSylowIn 3 Y J) :
    D = J ⊔ (D ⊓ normalizer (Y : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJN : (J.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJD).mpr hDJ
  refine le_antisymm (fun x hx => ?_) (sup_le hJD inf_le_left)
  obtain ⟨y, hy, n, hn, hnorm, hxy⟩ := frattini_isSylowIn hJD hJN hY x hx
  rw [← hxy]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
    (Subgroup.mem_sup_right ⟨hn, hnorm⟩)

theorem exists_isSylowIn_three_trans {J T : Subgroup G} (hTJ : T ≤ normalizer (J : Set G))
    (hT : IsPGroup 2 ↥T) (hS : IsSylowIn 2 (T ⊓ J) J) :
    ∃ Y : Subgroup G, IsSylowIn 3 Y J ∧
      ∀ t ∈ T, ∃ n ∈ T ⊓ normalizer (Y : Set G), ∃ j ∈ T ⊓ J, t = n * j := by
  obtain ⟨Y, hY, hTY⟩ := exists_isSylowIn_three_good hTJ hT hS
  have hJD : J ≤ J ⊔ T := le_sup_left
  have hDJ : J ⊔ T ≤ normalizer (J : Set G) := sup_le Subgroup.le_normalizer hTJ
  have hN : (J ⊔ T) ⊓ normalizer (Y : Set G) ≤ J ⊔ T := inf_le_left
  have hTN : T ⊓ ((J ⊔ T) ⊓ normalizer (Y : Set G)) = T ⊓ normalizer (Y : Set G) := by
    rw [← inf_assoc, inf_of_le_left (le_sup_right : T ≤ J ⊔ T)]
  refine ⟨Y, hY, fun t ht => ?_⟩
  obtain ⟨n, hn, j, hj, rfl⟩ := eq_inf_mul_inf_of_isSylowIn hJD hDJ hN
    (wc819pp_frattini hJD hDJ hY) (wc819pp_sylow_two_sup hTJ hT hS) (by rw [hTN]; exact hTY) t ht
  exact ⟨n, ⟨hn.1, (Subgroup.mem_inf.mp hn.2).2⟩, j, hj, rfl⟩

theorem isSylowIn_three_inf_normalizer {J K V Y : Subgroup G} (hY : IsSylowIn 3 Y J)
    (hKJ : K ⊓ normalizer (V : Set G) ≤ J) (hYK : Y ≤ normalizer (K : Set G))
    (hYV : Y ≤ normalizer (V : Set G)) :
    IsSylowIn 3 (Y ⊓ K) (K ⊓ normalizer (V : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYK₀ : Y ≤ normalizer ((K ⊓ normalizer (V : Set G) : Subgroup G) : Set G) :=
    (le_inf hYK (hYV.trans (Subgroup.le_normalizer (H := normalizer (V : Set G))))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hK₀N : (K ⊓ normalizer (V : Set G) : Subgroup G) ≤
      normalizer ((K ⊓ normalizer (V : Set G) : Subgroup G) : Set G) := Subgroup.le_normalizer
  have hN : ((K ⊓ normalizer (V : Set G)).subgroupOf
      (Y ⊔ (K ⊓ normalizer (V : Set G)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sup_le hYK₀ hK₀N)
  have hYsyl : IsSylowIn 3 Y (Y ⊔ (K ⊓ normalizer (V : Set G))) :=
    isSylowIn_of_le_of_le hY le_sup_left (sup_le hY.1 hKJ)
  have hinf := IsSylowIn.inf_normal hYsyl le_sup_right hN
  have hEq : Y ⊓ (K ⊓ normalizer (V : Set G)) = Y ⊓ K := by
    rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hYV)]
  rwa [hEq] at hinf

theorem conjClosure_le_genFittingLayer {Q : Type} [Group Q] {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) : conjClosure J ⊤ ≤ genFittingLayer Q := by
  refine conjClosure_le fun h _ z hz => ?_
  have hcomp : IsComponentOf (J.map (MulAut.conj h).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj h) J).mpr hJ
  have hmem : h * z * h⁻¹ ∈ J.map (MulAut.conj h).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩
  rw [genFittingLayer.eq_sSup]
  exact Subgroup.mem_sSup_of_mem
    (show J.map (MulAut.conj h).toMonoidHom ∈ {L : Subgroup Q | IsComponentOf L ⊤} from hcomp)
    hmem

variable {V H T A L K : Subgroup G} {i : ℕ}

theorem Sit813.le_normalizer_conjClosure_inf (h : Sit813 V H T i A L K) :
    T ≤ normalizer ((conjClosure L H ⊓ normalizer (V : Set G) : Subgroup G) : Set G) := by
  have hTH : T ≤ H := h.minCex.hyp.sylow.le.trans inf_le_left
  have hT1 : T ≤ normalizer (conjClosure L H : Set G) :=
    hTH.trans (le_normalizer_conjClosure L H)
  have hTM : T ≤ normalizer (V : Set G) := h.minCex.hyp.sylow.le.trans inf_le_right
  have hT2 : T ≤ normalizer (normalizer (V : Set G) : Set G) :=
    hTM.trans (Subgroup.le_normalizer (H := normalizer (V : Set G)))
  exact (le_inf hT1 hT2).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem Sit813.isSylowIn_two_inf_conjClosure (h : Sit813 V H T i A L K) :
    IsSylowIn 2 (T ⊓ (conjClosure L H ⊓ normalizer (V : Set G)))
      (conjClosure L H ⊓ normalizer (V : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJH : conjClosure L H ≤ H := wc819pp_conjClosure_le_self h.concl813.comp.2.2.1
  have hJnorm : ((conjClosure L H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mpr (le_normalizer_conjClosure L H)
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.calH0.1 h.minCex.hyp.sylow
  have hSylJ : IsSylowIn 2 (T ⊓ conjClosure L H) (conjClosure L H) :=
    IsSylowIn.inf_normal hTH hJH hJnorm
  have hTM : T ≤ normalizer (V : Set G) := h.minCex.hyp.sylow.le.trans inf_le_right
  have hTJM : T ⊓ conjClosure L H ≤ normalizer (V : Set G) := inf_le_left.trans hTM
  have hres := isSylowIn_of_le_of_le hSylJ (le_inf inf_le_right hTJM) inf_le_left
  have hEq : T ⊓ (conjClosure L H ⊓ normalizer (V : Set G)) = T ⊓ conjClosure L H := by
    rw [← inf_assoc, inf_eq_left.mpr hTJM]
  rwa [hEq]

theorem Sit813.cShape_barSub (h : Sit813 V H T i A L K) {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H (cGrp H T) φ) :
    HasQuotShape (barSub H φ K)
      ((oTwoMod (⊥ : Subgroup Q) (barSub H φ K) : Subgroup Q) : Set Q)
      (fun X _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 X 2) := by
  have hCH : cGrp H T ≤ H := inf_le_left
  have hKH : K ≤ H := h.concl813.sub_L.trans h.concl813.comp.2.2.1
  have hCnorm : ((cGrp H T).subgroupOf K).Normal := wc819pp_cGrp_normal h
  have hCN : cGrp H T ≤ oTwoMod (cGrp H T) K := wc819pp_le_oTwoMod_self h.concl813.ge_C hCnorm
  have hNK : oTwoMod (cGrp H T) K ≤ K := wc819pp_oTwoMod_le_self
  have hshape := hasQuotShape_barSub hφ hCN hNK hKH h.concl813.c_shape
  have hpre : barPre H φ (barSub H φ K) = K := barPre_barSub hφ h.concl813.ge_C hKH
  have h2 : oTwoMod (cGrp H T) K =
      barPre H φ (oTwoMod (⊥ : Subgroup Q) (barSub H φ K)) := by
    calc oTwoMod (cGrp H T) K
        = oTwoMod (cGrp H T) (barPre H φ (barSub H φ K)) := by rw [hpre]
      _ = barPre H φ (oTwoMod (⊥ : Subgroup Q) (barSub H φ K)) :=
          oTwoMod_barPre hφ hCH (barSub H φ K)
  have hEq : barSub H φ (oTwoMod (cGrp H T) K) =
      oTwoMod (⊥ : Subgroup Q) (barSub H φ K) := by
    rw [h2]
    exact barSub_barPre hφ (oTwoMod (⊥ : Subgroup Q) (barSub H φ K))
  rw [hEq] at hshape
  exact hshape

theorem Sit813.conjClosure_inf_le_normalizer (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact) (h : Sit813 V H T i A L K)
    (hAB : Case813AB (cGrp H T) L K) :
    conjClosure L H ⊓ normalizer (V : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨hK, L₀, hL₀⟩ := h.toPre.exists_data810 h5_11 h5_13
  obtain ⟨Q, hQgrp, hQfin, φ, hφ⟩ := exists_isBarMap h.concl813.comp.1
  letI : Group Q := hQgrp
  letI : Finite Q := hQfin
  have hcfg := h.toPre.cfg h5_11 h5_13 hK hL₀ hφ
  have hLB : IsComponentOf (barSub H φ L) ⊤ := Sit813.isComponentOf_barSub h hφ
  have hKL : barSub H φ K ≤ barSub H φ L :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H h.concl813.sub_L)
  have hnorm : genFittingLayer Q ⊓ barSub H φ (H ⊓ normalizer (V : Set G)) ≤
      normalizer (barSub H φ K : Set Q) :=
    Cfg813.inf_layer_inf_B_le_normalizer hF0 hF1 hF2 hF3 hcfg hLB hKL
      (Sit813.cShape_barSub h hφ) (Sit813.isSylowIn_barSub h hφ)
      (Sit813.caseAB_barSub h hφ hAB)
  have hJH : conjClosure L H ≤ H := wc819pp_conjClosure_le_self h.concl813.comp.2.2.1
  have hKpre : barPre H φ (barSub H φ K) = K :=
    barPre_barSub hφ h.concl813.ge_C (h.concl813.sub_L.trans h.concl813.comp.2.2.1)
  intro y hy
  obtain ⟨hyJ, hyM⟩ := Subgroup.mem_inf.mp hy
  have hyH : y ∈ H := hJH hyJ
  have hyE : φ ⟨y, hyH⟩ ∈ genFittingLayer Q :=
    (conjClosure_le_genFittingLayer hLB)
      ((barSub_conjClosure_le h.concl813.comp.2.2.1)
        (mem_barSub.mpr ⟨⟨y, hyH⟩, hyJ, rfl⟩))
  have hyB : φ ⟨y, hyH⟩ ∈ barSub H φ (H ⊓ normalizer (V : Set G)) :=
    mem_barSub.mpr ⟨⟨y, hyH⟩, Subgroup.mem_inf.mpr ⟨hyH, hyM⟩, rfl⟩
  have hnormK : φ ⟨y, hyH⟩ ∈ normalizer (barSub H φ K : Set Q) := hnorm ⟨hyE, hyB⟩
  rw [← hKpre, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxH, hxK⟩ := mem_barPre.mp hx
    refine mem_barPre.mpr ⟨H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH), ?_⟩
    have hphi : φ ⟨y * x * y⁻¹, H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH)⟩ =
        φ ⟨y, hyH⟩ * φ ⟨x, hxH⟩ * (φ ⟨y, hyH⟩)⁻¹ := by
      rw [show (⟨y * x * y⁻¹, H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH)⟩ : ↥H) =
          ⟨y, hyH⟩ * ⟨x, hxH⟩ * ⟨y, hyH⟩⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
    rw [hphi]
    exact (Subgroup.mem_normalizer_iff.mp hnormK (φ ⟨x, hxH⟩)).mp hxK
  · intro hx
    obtain ⟨hxy, hxk⟩ := mem_barPre.mp hx
    have hxH : x ∈ H := by
      rw [show x = y⁻¹ * (y * x * y⁻¹) * y by group]
      exact H.mul_mem (H.mul_mem (H.inv_mem hyH) hxy) hyH
    refine mem_barPre.mpr ⟨hxH, ?_⟩
    have hphi : φ ⟨y * x * y⁻¹, hxy⟩ =
        φ ⟨y, hyH⟩ * φ ⟨x, hxH⟩ * (φ ⟨y, hyH⟩)⁻¹ := by
      rw [show (⟨y * x * y⁻¹, hxy⟩ : ↥H) =
          ⟨y, hyH⟩ * ⟨x, hxH⟩ * ⟨y, hyH⟩⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
    have hmem : φ ⟨y, hyH⟩ * φ ⟨x, hxH⟩ * (φ ⟨y, hyH⟩)⁻¹ ∈ barSub H φ K := by
      rw [← hphi]
      exact hxk
    exact (Subgroup.mem_normalizer_iff.mp hnormK (φ ⟨x, hxH⟩)).mpr hmem

theorem w3Claim819'_holds (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact) : W3Claim819' G := by
  intro V H T A L K i h hAB
  have hJK := h.conjClosure_inf_le_normalizer h5_11 h5_13 hF0 hF1 hF2 hF3 hAB
  obtain ⟨Y, hY, hYT⟩ := exists_isSylowIn_three_trans h.le_normalizer_conjClosure_inf
    h.minCex.hyp.sylow.isPGroup h.isSylowIn_two_inf_conjClosure
  have hYJ : Y ≤ conjClosure L H ⊓ normalizer (V : Set G) := hY.1
  refine ⟨Y ⊓ K, Y, isSylowIn_three_inf_normalizer hY ?_ (hYJ.trans hJK)
    (hYJ.trans inf_le_right), hY, inf_le_left, hYJ.trans hJK, fun t ht => ?_⟩
  · exact inf_le_inf_right _ (h.concl813.sub_L.trans (le_conjClosure L H))
  · obtain ⟨n, hn, j, hj, rfl⟩ := hYT t ht
    exact ⟨n, hn, j, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hj).1,
      hJK (Subgroup.mem_inf.mp hj).2⟩, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81

end
