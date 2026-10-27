module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeDefs
public import CFSG.LocalAnalysis.WeakClosure81.NineTwoC
public import CFSG.LocalAnalysis.WeakClosure81.EightFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ}

namespace Nine3Core

theorem V_le (h : Nine3Core V T A K S X p) : V ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVnorm : (V.subgroupOf (normalizer (V : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hVp : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.h9.hyp7.1
  exact h.h9.sylow.le_of_normal Subgroup.le_normalizer hVnorm hVp

theorem A_le_S (h : Nine3Core V T A K S X p) : A ≤ S := by
  have hAab : IsMulCommutative ↥A := by
    obtain ⟨g, hg⟩ := h.conj
    rw [hg]
    exact (E3.isElemAbelian_conjSubgroup h.h9.hyp7.1 g).1
  intro a ha
  refine h.tau (E1.mem_tauOf.mpr ⟨h.leT ha, ?_, ?_⟩)
  · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (normalizer (V : Set G))
      (h.h9.sylow.le (h.leT ha))
  · intro a' ha'
    have h1 : ⁅a, a'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hAab.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
    rw [h1]
    exact Subgroup.one_mem _

theorem S_le_normalizer (h : Nine3Core V T A K S X p) : S ≤ normalizer (V : Set G) :=
  h.hyp.base.sylowTwo.le.trans h.hyp.base.le

theorem V_le_centralizer (h : Nine3Core V T A K S X p) : V ≤ centralizer (A : Set G) := by
  have hAT := h.leT
  have hVT := h.V_le
  have hTM : T ≤ normalizer (V : Set G) := h.h9.sylow.le
  have hTp : IsPGroup 2 T := h.h9.sylow.isPGroup
  have hA1 : A ≠ ⊥ := by
    obtain ⟨g, hg⟩ := h.conj
    intro hbot
    have hcard : Nat.card A = Nat.card V := by rw [hg]; exact E3.card_conjSubgroup V g
    rw [hbot, Subgroup.card_bot] at hcard
    have := h.h9.hyp7.2.1
    omega
  have hAN : A ⊓ normalizer (V : Set G) ≠ ⊥ := by
    rwa [inf_eq_left.2 (hAT.trans hTM)]
  have hP : IsPGroup 2 ↥(A ⊔ V) := hTp.to_le (sup_le hAT hVT)
  have hcomm := commute_of_isPGroup_sup h.h9.hyp7.1 h.h9.hyp7.2.2 h.conj
    ⟨1, (CFSG.Quasithin.conjSubgroup_one V).symm⟩ hAN hP
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact hcomm u hu v hv

end Nine3Core

theorem nine_three_four_centralizer (h : Nine3Core V T A K S X p) :
    T ⊓ centralizer (A : Set G) ≤ S := by
  intro t ht
  refine h.tau (E1.mem_tauOf.mpr ⟨ht.1, ?_, ?_⟩)
  · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (normalizer (V : Set G))
      (h.h9.sylow.le ht.1)
  · intro a ha
    have h1 : ⁅t, a⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_centralizer_iff.mp ht.2) a ha).symm
    rw [h1]
    exact Subgroup.one_mem _

theorem nine_three_four_wClos (h : Nine3Core V T A K S X p) :
    E3.wClos V 0 (T ⊓ normalizer (A : Set G)) ≤ T ⊓ centralizer (A : Set G) := by
  rw [wClos_zero_eq_iSup h.h9.hyp7.1]
  refine iSup₂_le fun g hg => ?_
  have hBT : conjSubgroup V g ≤ T := hg.trans inf_le_left
  have hBN : conjSubgroup V g ≤ normalizer (A : Set G) := hg.trans inf_le_right
  refine le_inf hBT ?_
  have hB1 : conjSubgroup V g ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (conjSubgroup V g) = Nat.card V := E3.card_conjSubgroup V g
    rw [hbot, Subgroup.card_bot] at hcard
    have := h.h9.hyp7.2.1
    omega
  have hBNA : conjSubgroup V g ⊓ normalizer (A : Set G) ≠ ⊥ := by
    rwa [inf_eq_left.2 hBN]
  have hP : IsPGroup 2 ↥(conjSubgroup V g ⊔ A) :=
    h.h9.sylow.isPGroup.to_le (sup_le hBT h.leT)
  have hcomm := commute_of_isPGroup_sup h.h9.hyp7.1 h.h9.hyp7.2.2 ⟨g, rfl⟩ h.conj hBNA hP
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (hcomm v hv u hu).symm

namespace Nine3Core

theorem V_le_S (h : Nine3Core V T A K S X p) : V ≤ S :=
  fun x hx => nine_three_four_centralizer h ⟨h.V_le hx, h.V_le_centralizer hx⟩

theorem V_mem_nineDelta (h : Nine3Core V T A K S X p) : V ∈ nineDelta V S :=
  ⟨⟨1, (CFSG.Quasithin.conjSubgroup_one V).symm⟩, h.V_le_S⟩

theorem A_mem_nineDelta (h : Nine3Core V T A K S X p) : A ∈ nineDelta V S :=
  ⟨h.conj, h.A_le_S⟩

theorem A_mem_nineOmegaIn (h : Nine3Core V T A K S X p) : A ∈ nineOmegaIn V K S :=
  ((nine_two_one h.hyp7 h.rk_gt h.hyp).2 A h.conj h.A_le_S).resolve_right h.ne

theorem mem_nineDelta_iff (h : Nine3Core V T A K S X p) {B : Subgroup G} :
    B ∈ nineDelta V S ↔ B = V ∨ B ∈ nineOmegaIn V K S := by
  constructor
  · intro hB
    rcases (nine_two_one h.hyp7 h.rk_gt h.hyp).2 B hB.1 hB.2 with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  · rintro (rfl | hB)
    · exact h.V_mem_nineDelta
    · obtain ⟨g, hg, -, -⟩ := mem_omegaSet.mp hB.1
      exact ⟨⟨g, hg⟩, hB.2⟩

theorem V_not_mem_nineOmegaIn (h : Nine3Core V T A K S X p) : V ∉ nineOmegaIn V K S := by
  intro hV
  obtain ⟨g, hg, -, hnot⟩ := mem_omegaSet.mp hV.1
  exact hnot (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (h.V_le_S.trans h.hyp.base.sylowTwo.le) h.hyp.base.le
    (B2F.isPGroup_of_isElemAbelian h.h9.hyp7.1))

end Nine3Core

theorem nine_three_six (h : Nine3Core V T A K S X p) : IsMulCommutative ↥(nineW V S) := by
  have hΩ := nine_two_three h.hyp7 h.rk_gt h.hyp
  have hΩc : (⨆ B ∈ nineOmegaIn V K S, B) ≤
      centralizer ((⨆ B ∈ nineOmegaIn V K S, B : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hΩ
  have hVB : ∀ B ∈ nineDelta V S, B ≤ centralizer (V : Set G) := by
    intro B hB
    have hBM : B ≤ normalizer (V : Set G) := hB.2.trans h.S_le_normalizer
    have hB1 : B ≠ ⊥ := by
      obtain ⟨g, hg⟩ := hB.1
      intro hbot
      have hcard : Nat.card B = Nat.card V := by rw [hg]; exact E3.card_conjSubgroup V g
      rw [hbot, Subgroup.card_bot] at hcard
      have := h.h9.hyp7.2.1
      omega
    have hBN : B ⊓ normalizer (V : Set G) ≠ ⊥ := by rwa [inf_eq_left.2 hBM]
    have hP : IsPGroup 2 ↥(B ⊔ V) :=
      (h.h9.sylow.isPGroup.to_le h.leS).to_le (sup_le hB.2 h.V_le_S)
    have hcomm := commute_of_isPGroup_sup h.h9.hyp7.1 h.h9.hyp7.2.2 hB.1
      ⟨1, (CFSG.Quasithin.conjSubgroup_one V).symm⟩ hBN hP
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcomm u hu v hv).symm
  refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
  refine iSup₂_le fun B hB => ?_
  refine Subgroup.le_centralizer_iff.mpr ?_
  refine iSup₂_le fun B' hB' => ?_
  rcases h.mem_nineDelta_iff.mp hB with rfl | hBΩ
  · rcases h.mem_nineDelta_iff.mp hB' with rfl | hB'Ω
    · exact Subgroup.le_centralizer_iff_isMulCommutative.mpr h.h9.hyp7.1.1
    · exact hVB B' hB'
  · rcases h.mem_nineDelta_iff.mp hB' with rfl | hB'Ω
    · exact Subgroup.le_centralizer_iff.mpr (hVB B hB)
    · have hBle : B ≤ ⨆ B ∈ nineOmegaIn V K S, B := le_iSup₂_of_le B hBΩ le_rfl
      have hB'le : B' ≤ ⨆ B ∈ nineOmegaIn V K S, B := le_iSup₂_of_le B' hB'Ω le_rfl
      exact hB'le.trans (hΩc.trans (Subgroup.centralizer_le hBle))

end CFSG.LocalAnalysis.WeakClosure81
