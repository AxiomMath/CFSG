module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Red
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148FacDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22K148FacData
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Core
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Out
import TauCeti.Algebra.Group.Subgroup.Normalizer

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem commOn_top_le_iSup {m : ℕ} {Hs : Fin m → Subgroup G} (hHs : (⨆ i, Hs i) = ⊤) :
    commOn ρ ⊤ ⊤ ≤ ⨆ i, commOn ρ (Hs i) ⊤ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, -, v, -, rfl⟩
  have hg : g ∈ ⨆ i, Hs i := by
    rw [hHs]
    exact Subgroup.mem_top g
  rw [SetLike.mem_coe]
  refine Subgroup.iSup_induction Hs (C := fun g => ∀ w : V, ρ g w - w ∈ ⨆ i, commOn ρ (Hs i) ⊤)
    hg (fun i x hx w => Submodule.mem_iSup_of_mem i (sub_mem_commOn hx Submodule.mem_top))
    (fun w => by
      rw [map_one, Module.End.one_apply, sub_self]
      exact zero_mem _)
    (fun x y hx hy w => ?_) v
  have h1 : ρ (x * y) w - w = (ρ x (ρ y w) - ρ y w) + (ρ y w - w) := by
    rw [map_mul, Module.End.mul_apply]
    abel
  rw [h1]
  exact add_mem (hx _) (hy w)

theorem commOn_le_sup_of_isCompl {H O : Subgroup G}
    (hc : IsCompl (commOn ρ O ⊤) (fixSub ρ O)) (hN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H (commOn ρ O ⊤))
    (hT : ∀ u ∈ H, commOn ρ (Subgroup.zpowers u) (fixSub ρ O) ≤ fixSub ρ ⊤) :
    commOn ρ H ⊤ ≤ commOn ρ O ⊤ ⊔ (commOn ρ ⊤ ⊤ ⊓ fixSub ρ ⊤) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, hh, v, -, rfl⟩
  have hv : v ∈ commOn ρ O ⊤ ⊔ fixSub ρ O := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn, c, hc', rfl⟩ := Submodule.mem_sup.1 hv
  have h1 : ρ h (n + c) - (n + c) = (ρ h n - n) + (ρ h c - c) := by
    rw [map_add]
    abel
  rw [SetLike.mem_coe, h1]
  exact Submodule.add_mem_sup (sub_mem (hN h hh n hn) hn) (Submodule.mem_inf.2
    ⟨sub_mem_commOn (Subgroup.mem_top h) Submodule.mem_top,
      hT h hh (sub_mem_commOn (Subgroup.mem_zpowers h) hc')⟩)


theorem k148Concl_of_hasFactors148 [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (hF : HasFactors148 G) : K148Concl ρ := by
  obtain ⟨m, Hs, hD, hF⟩ := hF
  obtain ⟨O, J, -, hOH, hperf, hON, hF0, hfaith, hcompl, hNE, hO⟩ :=
    exists_coreData_of_isFactor148 hρ hshape hH hD hF
  have hHC := sup_centralizer_eq_top_of_isInternalDirect hD
  have hdata := fun i => factorData_of_isFactor148 hρ hshape hH (hF i) (hHC i)
  have hU : uP ρ = commOn ρ ⊤ ⊤ := by rw [uP, hH]
  have hC : cUP ρ = commOn ρ ⊤ ⊤ ⊓ fixSub ρ ⊤ := by rw [cUP, uP, hH]
  have hOHi : ∀ i, O i ≤ Hs i := fun i => by
    rw [hO i]
    exact Subgroup.commutator_le_self _
  have hNinv : ∀ i, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ ⊤ (commOn ρ (O i) ⊤) := fun i => by
    haveI : (Hs i).Normal := TauCeti.normal_of_commute_of_sup_eq_top
      (fun c hc x hx => Subgroup.mem_centralizer_iff.1 hx c hc) (hHC i)
    have hON' : (O i).Normal := by
      rw [hO i]
      infer_instance
    exact (invariant_commOn_top (A := ⊤) (L := O i) fun g _ => by
      rw [Subgroup.normalizer_eq_top_iff.2 hON']
      exact Subgroup.mem_top g).2
  have hVH : ∀ i, commOn ρ (Hs i) ⊤ ≤ commOn ρ (O i) ⊤ ⊔ cUP ρ := fun i => by
    by_cases hi : i ∈ J
    · rw [hC]
      exact commOn_le_sup_of_isCompl (hcompl i hi) (fun h _ => hNinv i h (Subgroup.mem_top h))
        fun u hu => commOn_zpowers_le_fixSub_top hH hD hOH hperf hON hF0 hfaith hcompl hNE hi hu
    · rw [hperf i hi]
      exact le_sup_left
  have hUle : uP ρ ≤ (⨆ i, commOn ρ (O i) ⊤) ⊔ cUP ρ := by
    rw [hU]
    exact (commOn_top_le_iSup hD.1).trans (iSup_le fun i =>
      (hVH i).trans (sup_le_sup_right (le_iSup (fun j => commOn ρ (O j) ⊤) i) _))
  have hUi : ∀ i, commOn ρ (Hs i) (uP ρ) = commOn ρ (O i) ⊤ := fun i => by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨x, hx, w, hw, rfl⟩
      have hle : (⨆ j, commOn ρ (O j) ⊤) ⊔ cUP ρ ≤ (commOn ρ (O i) ⊤).comap (ρ x - 1) := by
        refine sup_le (iSup_le fun j n hn => ?_) fun c hc => ?_
        · rw [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply]
          by_cases hji : j = i
          · subst hji
            exact sub_mem (hNinv j x (Subgroup.mem_top x) n hn) hn
          · rw [hF0 j i hji x hx n hn, sub_self]
            exact zero_mem _
        · rw [hC] at hc
          rw [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply,
            mem_fixSub.1 (Submodule.mem_inf.1 hc).2 x (Subgroup.mem_top x), sub_self]
          exact zero_mem _
      have h := Submodule.mem_comap.1 (hle (hUle hw))
      rwa [LinearMap.sub_apply, Module.End.one_apply] at h
    · have h1 : commOn ρ (O i) (commOn ρ (O i) ⊤) = commOn ρ (O i) ⊤ := by
        have h := (hdata i).2.1
        rwa [← hO i] at h
      calc commOn ρ (O i) ⊤ = commOn ρ (O i) (commOn ρ (O i) ⊤) := h1.symm
        _ ≤ commOn ρ (Hs i) (uP ρ) := (commOn_mono_left (hOHi i)).trans
          (commOn_mono_right ((commOn_mono_left le_top).trans hU.ge))
  have hD' : IsInternalDirect (hP ρ) Hs := by
    rw [hH]
    exact hD
  refine k148Concl_of_factors hD' (fun i j hij => ?_)
    (hUle.trans (sup_le_sup_right (iSup_mono fun i => (hUi i).ge) _)) fun i => ?_
  · rw [hUi i]
    exact fun n hn => mem_fixSub.2 fun h hh => hF0 i j hij h hh n hn
  · rw [hUi i]
    have h := (hdata i).2.2.1
    rwa [← hO i] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
