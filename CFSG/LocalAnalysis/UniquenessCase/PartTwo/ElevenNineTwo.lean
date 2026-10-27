module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineTwoA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineTwoB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineTwoC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem exists_calC_conjClosure_eq (D : Data G) {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V)
    [hN : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hMY : D.M ≤ normalizer (Y : Set G)) (hYperf : ⁅Y, Y⁆ = Y) (hO2E : F11.O2E Y = Y)
    (hYC : Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y) {Lbar : Subgroup (F11.MBar11 D.M V₀ V)}
    (hL : IsComponentOf Lbar ⊤)
    (hX : F11.barImage11 D.M V₀ V Y =
      ⨆ g : F11.MBar11 D.M V₀ V, Lbar.map (MulAut.conj g).toMonoidHom) :
    ∃ K ∈ calC D.M, Y = conjClosure D.M K := by
  obtain ⟨-, hO, -⟩ := hyp11_ctilde D hV
  have hLperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hL.2.2.1)
  have hLY : Lbar ≤ F11.barImage11 D.M V₀ V Y := by
    rw [hX]
    have h1 : Lbar.map (MulAut.conj (1 : F11.MBar11 D.M V₀ V)).toMonoidHom = Lbar := by
      ext x
      simp
    calc Lbar = Lbar.map (MulAut.conj (1 : F11.MBar11 D.M V₀ V)).toMonoidHom := h1.symm
      _ ≤ _ := le_iSup (fun g : F11.MBar11 D.M V₀ V => Lbar.map (MulAut.conj g).toMonoidHom) 1
  set K : Subgroup G := Hinf (Y ⊓ F11.barPreimage11 D.M V₀ V Lbar) with hKdef
  have hKbar : F11.barImage11 D.M V₀ V K = Lbar :=
    barImage11_hinf_inf_barPreimage11 hLY hYM hLperf
  have hKsub : IsSubnormal K D.M := isSubnormal_hinf_inf_barPreimage11 hYM hMY hL.2.1
  have hKperf : ⁅K, K⁆ = K := uc22p21c_Hinf_perfect _
  have hKY : K ≤ Y := (uc22p21c_Hinf_le _).trans inf_le_left
  have hKM : K ≤ D.M := hKY.trans hYM
  let g : ↥K →* ↥Lbar :=
    ((QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)).comp
      (Subgroup.inclusion hKM)).codRestrict Lbar fun k =>
      hKbar ▸ uc22p22u_mem_barImage11.2 ⟨Subgroup.inclusion hKM k, k.2, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨q, hq⟩
    obtain ⟨m, hm, hmq⟩ := uc22p22u_mem_barImage11.1 (hKbar.symm ▸ hq)
    exact ⟨⟨(m : G), hm⟩, Subtype.ext hmq⟩
  have hgker : ∀ k : ↥K, k ∈ g.ker ↔ ((k : ↥K) : G) ∈ F11.CTilde D.M V₀ V := by
    intro k
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M))
          (Subgroup.inclusion hKM k) = 1 := congrArg Subtype.val h
      exact Subgroup.mem_subgroupOf.1
        ((QuotientGroup.eq_one_iff (N := (F11.CTilde D.M V₀ V).subgroupOf D.M)
          (Subgroup.inclusion hKM k)).1 h1)
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := (F11.CTilde D.M V₀ V).subgroupOf D.M)
        (Subgroup.inclusion hKM k)).2 (Subgroup.mem_subgroupOf.2 h)
  have hcore : CFSG.pCore 2 ↥K ≤ g.ker := by
    intro x hx
    rw [hgker]
    have h1 : ((x : ↥K) : G) ∈ pCoreOf 2 K := ⟨x, hx, rfl⟩
    exact hO (uc22p21c_pCoreOf_le_of_subnormal hKsub h1)
  have hcomm : ∀ k ∈ g.ker, ∀ k' : ↥K, ⁅k, k'⁆ ∈ CFSG.pCore 2 ↥K := by
    intro k hk k'
    have hkC : ((k : ↥K) : G) ∈ F11.CTilde D.M V₀ V := (hgker k).1 hk
    have h1 : ((k : ↥K) : G) * (k' : G) * ((k : ↥K) : G)⁻¹ * (k' : G)⁻¹ ∈ pCoreOf 2 Y :=
      commutator_mem_pCoreOf_of_mem_OInf hO2E (hYC ⟨hKY k.2, hkC⟩) (hKY k'.2)
    have h2 : ((k : ↥K) : G) * (k' : G) * ((k : ↥K) : G)⁻¹ * (k' : G)⁻¹ ∈ pCoreOf 2 K := by
      refine uc22p21c_le_pCoreOf (K := K) (P := K ⊓ pCoreOf 2 Y) inf_le_left
        ((uc22p21c_isPGroup_pCoreOf Y).to_inf_right) ?_
        ⟨K.mul_mem (K.mul_mem (K.mul_mem k.2 k'.2) (K.inv_mem k.2)) (K.inv_mem k'.2), h1⟩
      intro a ha x hx
      exact ⟨K.mul_mem (K.mul_mem ha hx.1) (K.inv_mem ha),
        uc22p21c_conj_mem_pCoreOf_self (hKY ha) hx.2⟩
    obtain ⟨y, hy, hyx⟩ := h2
    have hy' : y = ⁅k, k'⁆ := Subtype.ext (by simpa [commutatorElement_def] using hyx)
    exact hy' ▸ hy
  have hKq : CFSG.Open.IsQuasisimple (Bar2 K) :=
    isQuasisimple_bar2_of_ker_commutes (Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hKperf)) g
      hg hL.2.2 hcore hcomm
  have hK : K ∈ calC D.M := ⟨hKsub, hKperf, hKq⟩
  refine ⟨K, hK, ?_⟩
  refine eq_conjClosure_of_barImage11_eq hK hKY hYM hMY hYperf hYC ?_
  rw [barImage11_conjClosure hKM, hKbar, hX]

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
