module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeRel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_subgroupOf_mem_omegaSet_top {U H E W : Subgroup G} {k : G}
    (hUH : U ≤ H) (hWH : W ≤ H) (hW : W = conjSubgroup U k) (hk : k ∈ H)
    (hEH : E ≤ H) (hEW : E ⊓ W ≠ ⊥) (hWO : ¬ W ≤ pCoreOf 2 H) :
    W.subgroupOf H ∈ omegaSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) := by
  refine mem_omegaSet.mpr ⟨⟨k, hk⟩, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective H.subtype_injective
    rw [map_conjSubgroup_subgroupOf' hUH hk, Subgroup.map_subgroupOf_eq_of_le hWH, hW]
  · have hE'W' : E.subgroupOf H ⊓ W.subgroupOf H = (E ⊓ W).subgroupOf H :=
      (Subgroup.comap_inf E W H.subtype).symm
    rw [hE'W']
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    apply hEW
    have hEWh : E ⊓ W ≤ H := inf_le_left.trans hEH
    have hinf : (E ⊓ W) ⊓ H = E ⊓ W := inf_eq_left.mpr hEWh
    rw [disjoint_iff] at hbot
    rwa [hinf] at hbot
  · rw [pCoreOf_top_subgroupOf]
    intro hle
    apply hWO
    intro y hy
    have hyH : y ∈ H := hWH hy
    have hmem : (⟨y, hyH⟩ : ↥H) ∈ W.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
    have h2 := hle hmem
    rwa [Subgroup.mem_subgroupOf] at h2

private theorem nineThree_map_subtype_mem_omegaIn {V H E U : Subgroup G} {W' : Subgroup ↥H}
    (hU : U ∈ omegaIn V H E)
    (hW' : W' ∈ omegaSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H)) :
    W'.map H.subtype ∈ omegaIn V H E := by
  obtain ⟨a, hUa, -, -⟩ := mem_omegaSet.mp hU.1
  obtain ⟨γ, hW'γ, hEW', hW'O'⟩ := mem_omegaSet.mp hW'
  have hmapW : W'.map H.subtype = conjSubgroup U (γ : G) := by
    rw [hW'γ, ← map_conjSubgroup_hom H.subtype (U.subgroupOf H) γ,
      Subgroup.map_subgroupOf_eq_of_le hU.2]
    rfl
  refine ⟨?_, Subgroup.map_subtype_le W'⟩
  refine mem_omegaSet.mpr ⟨a * (γ : G), ?_, ?_, ?_⟩
  · rw [hmapW, hUa, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  · obtain ⟨x, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEW'
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨(x : G), ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · have h := (Subgroup.mem_inf.mp x.2).1
        rwa [Subgroup.mem_subgroupOf] at h
      · exact Subgroup.mem_map.mpr ⟨x.1, (Subgroup.mem_inf.mp x.2).2, rfl⟩
    · intro hh
      apply hx1'
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : ↥(E ⊓ W'.map H.subtype) => (t : G)) hh
  · intro hle
    apply hW'O'
    rw [pCoreOf_top_subgroupOf]
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩))

namespace Nine3Core

theorem nineI_eq_map (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) :
    nineI V K = (iSub (B.subgroupOf K) (⊤ : Subgroup ↥K)
      ((nineE V K).subgroupOf K)).map K.subtype := by
  have hBK : B ≤ K := hB.2.trans h.S_le_K
  have hBΩ : B ∈ omegaIn V K (nineE V K) := ⟨hB.1, hBK⟩
  have hEK : nineE V K ≤ K :=
    (nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  apply le_antisymm
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨k, hk, hUk⟩ :=
      nine_two_transitive h.hyp7 h.rk_gt h.hyp.base.toTwoPTwoIrred B hBΩ U hU
    obtain ⟨-, -, hEU, hUO⟩ := mem_omegaSet.mp hU.1
    have hmem := nineThree_subgroupOf_mem_omegaSet_top hBK hU.2 hUk hk hEK hEU hUO
    have hle : U.subgroupOf K ⊓ pCoreOf 2 (⊤ : Subgroup ↥K) ≤
        iSub (B.subgroupOf K) (⊤ : Subgroup ↥K) ((nineE V K).subgroupOf K) :=
      inf_pCoreOf_le_iSub hmem
    intro y hy
    obtain ⟨hyU, hyR⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_map.mpr ⟨⟨y, hU.2 hyU⟩, hle ?_, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hyU, ?_⟩
    rw [pCoreOf_top_subgroupOf]
    exact Subgroup.mem_subgroupOf.mpr hyR
  · unfold iSub
    rw [Subgroup.map_iSup]
    refine iSup_le fun W' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hW' => ?_
    have hW := nineThree_map_subtype_mem_omegaIn hBΩ hW'
    refine le_trans ?_ (le_iSup₂_of_le (W'.map K.subtype) hW le_rfl)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyW, hyR⟩ := Subgroup.mem_inf.mp hy
    rw [pCoreOf_top_subgroupOf] at hyR
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_map.mpr ⟨y, hyW, rfl⟩, Subgroup.mem_subgroupOf.mp hyR⟩


end Nine3Core


theorem nineThree_iSub_top {Γ : Type} [Group Γ] [Finite Γ] {V E : Subgroup Γ}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEnorm : (E.subgroupOf (⊤ : Subgroup Γ)).Normal) (hVΩ : V ∈ omegaSet V ⊤ E)
    (hindex : (V ⊓ iSub V ⊤ E).relIndex V = 2) :
    IsElemAbelian 2 (iSub V ⊤ E) ∧ ⁅iSub V ⊤ E, V⁆ = V ⊓ iSub V ⊤ E := by
  have hOmH : ∀ W ∈ omegaSet V ⊤ E, W ≤ ⊤ := fun _ _ => le_top
  have hI := seven_two_iSub_isElemAbelian_uncond hV hTI hE hOmH
  have hN := nVSub_eq_inf_iSub_of_relIndex_eq_two hV hTI hE le_top hEnorm hOmH hindex
  refine ⟨hI, le_antisymm ?_ ?_⟩
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    by_cases hbI : b ∈ iSub V ⊤ E
    · have hab : a * b = b * a := congrArg Subtype.val (hI.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbI⟩)
      have h1 : ⁅a, b⁆ = 1 := by
        rw [commutatorElement_def, hab]
        group
      rw [h1]
      exact Subgroup.one_mem _
    · have h2 := commutator_iSub_eq_inf_iSub hV hTI hE le_top hEnorm hOmH hVΩ hN hb hbI
      rw [← h2]
      exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers b)
  · obtain ⟨b, hbV, hbI⟩ : ∃ b ∈ V, b ∉ iSub V ⊤ E := by
      by_contra hcon
      push Not at hcon
      have h1 : (V ⊓ iSub V ⊤ E).relIndex V = 1 :=
        Subgroup.relIndex_eq_one.2 (fun x hx => ⟨hx, hcon x hx⟩)
      rw [hindex] at h1
      omega
    intro w hw
    have h2 := commutator_iSub_eq_inf_iSub hV hTI hE le_top hEnorm hOmH hVΩ hN hbV hbI
    rw [← h2] at hw
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hbV) hw


namespace Nine3Core

theorem nineI_facts (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) :
    IsElemAbelian 2 (nineI V K) ∧ ⁅nineI V K, B⁆ = B ⊓ pCoreOf 2 K := by
  have hBK : B ≤ K := hB.2.trans h.S_le_K
  have hEK : nineE V K ≤ K :=
    (nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  obtain ⟨-, -, hEB, hBO⟩ := mem_omegaSet.mp hB.1
  have hmap := h.nineI_eq_map hB
  set I' := iSub (B.subgroupOf K) (⊤ : Subgroup ↥K) ((nineE V K).subgroupOf K) with hI'
  have hI'eq : I' = (nineI V K).subgroupOf K := by
    rw [hmap]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective I').symm
  have hV' : IsElemAbelian 2 (B.subgroupOf K) :=
    isElemAbelian_subgroupOf (isElemAbelian_of_mem_omegaSet h.hyp7.1 hB.1)
  have hTI' : IsTI (B.subgroupOf K) :=
    isTI_subgroupOf hBK (isTI_of_mem_omegaSet hB.1 h.hyp7.2.2)
  have hE' : IsMulCommutative ((nineE V K).subgroupOf K) :=
    isMulCommutative_subgroupOf (isElemAbelian_nineE V K).1
  have hEnorm' : (((nineE V K).subgroupOf K).subgroupOf (⊤ : Subgroup ↥K)).Normal :=
    (nineE_subgroupOf_normal V K).subgroupOf ⊤
  have hΩ' : B.subgroupOf K ∈ omegaSet (B.subgroupOf K) (⊤ : Subgroup ↥K)
      ((nineE V K).subgroupOf K) :=
    nineThree_subgroupOf_mem_omegaSet_top hBK hBK (CFSG.Quasithin.conjSubgroup_one B).symm
      K.one_mem hEK hEB hBO
  have hindex : (B.subgroupOf K ⊓ I').relIndex (B.subgroupOf K) = 2 := by
    have hinf : B.subgroupOf K ⊓ (nineI V K).subgroupOf K = (B ⊓ nineI V K).subgroupOf K :=
      (Subgroup.comap_inf _ _ _).symm
    rw [hI'eq, hinf, Subgroup.relIndex_subgroupOf hBK, h.nineI_inf_eq hB,
      Subgroup.inf_relIndex_left]
    exact nine_two_relIndex h.hyp7 h.rk_gt h.hyp hB
  obtain ⟨hab, hcomm⟩ := nineThree_iSub_top hV' hTI' hE' hEnorm' hΩ' hindex
  refine ⟨?_, ?_⟩
  · rw [hmap]
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← ha'e, ← hb'e]
      exact congrArg Subtype.val
        (congrArg Subtype.val (hab.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      have := hab.2 y' hy'
      simpa using congrArg Subtype.val this
  · have h1 := congrArg (Subgroup.map K.subtype) hcomm
    rw [Subgroup.map_commutator, ← hmap, Subgroup.map_subgroupOf_eq_of_le hBK,
      Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, ← hmap,
      Subgroup.map_subgroupOf_eq_of_le hBK] at h1
    rw [h1, h.nineI_inf_eq hB]

end Nine3Core

theorem Nine3Core.nine3_IFacts (h : Nine3Core V T A K S X p) : Nine3IFacts V K S :=
  ⟨(h.nineI_facts h.A_mem_nineOmegaIn).1, fun _ hB => (h.nineI_facts hB).2⟩

end CFSG.LocalAnalysis.WeakClosure81
