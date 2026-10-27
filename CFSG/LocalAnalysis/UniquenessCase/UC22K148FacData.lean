module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Strip
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148FacDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22K148FacS3
import CFSG.LocalAnalysis.UniquenessCase.UC22K148FacComp
import TauCeti.Algebra.Group.Subgroup.Normalizer

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem sup_centralizer_eq_top_of_isInternalDirect {m : ℕ} {Hs : Fin m → Subgroup G}
    (hD : IsInternalDirect ⊤ Hs) (i : Fin m) :
    Hs i ⊔ Subgroup.centralizer (Hs i : Set G) = ⊤ := by
  rw [eq_top_iff, ← hD.1]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    exact le_sup_left
  · exact le_sup_of_le_right fun x hx =>
      Subgroup.mem_centralizer_iff.2 fun y hy => (hD.2.1 j i hji x hx y hy).symm


theorem factorData_of_isFactor148 [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) {H : Subgroup G} (hF : IsFactor148 H)
    (hHC : H ⊔ Subgroup.centralizer (H : Set G) = ⊤) :
    (∀ c : G, (∀ x ∈ H, c * x = x * c) → ∀ n ∈ commOn ρ ⁅H, H⁆ ⊤, ρ c n = n) ∧
      commOn ρ ⁅H, H⁆ (commOn ρ ⁅H, H⁆ ⊤) = commOn ρ ⁅H, H⁆ ⊤ ∧
      Shape148 ρ H (commOn ρ ⁅H, H⁆ ⊤) (fixSub ρ H) ∧ (IsComponentOf H ⊤ → ⁅H, H⁆ = H) ∧
      (¬ IsComponentOf H ⊤ →
        (∀ h ∈ H, (∀ n ∈ commOn ρ ⁅H, H⁆ ⊤, ρ h n = n) → h = 1) ∧
        IsCompl (commOn ρ ⁅H, H⁆ ⊤) (fixSub ρ ⁅H, H⁆) ∧
        ∀ X : Subgroup G, IsElemAbelian 2 X → NoExcess ρ X (commOn ρ ⁅H, H⁆ ⊤)) := by
  have hHN : H.Normal := TauCeti.normal_of_commute_of_sup_eq_top
    (fun c hc x hx => Subgroup.mem_centralizer_iff.1 hx c hc) hHC
  have hperf : IsComponentOf H ⊤ → ⁅H, H⁆ = H := fun hc =>
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hc.2.2.1)
  rcases hF with hc | he | he
  · obtain ⟨hF0, hUU, hsh⟩ := factorData_of_isComponentOf hρ hH hc (hshape H hc) hHC
    rw [hperf hc]
    exact ⟨hF0, hUU, hsh, fun _ => rfl, fun h => absurd hc h⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hF0, hfaith, hcompl, hNE, hsh⟩ := factorData_of_mulEquiv_perm_three hρ hH hHN e
    exact ⟨hF0, commOn_commOn_eq_of_isCompl hcompl, hsh, hperf, fun _ => ⟨hfaith, hcompl, hNE⟩⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hF0, hfaith, hcompl, hNE, hsh⟩ :=
      factorData_of_mulEquiv_perm_five hρ hshape hH hHN e
    exact ⟨hF0, commOn_commOn_eq_of_isCompl hcompl, hsh, hperf, fun _ => ⟨hfaith, hcompl, hNE⟩⟩

theorem exists_coreData_of_isFactor148 [Finite G] [Finite V]
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) {m : ℕ}
    {Hs : Fin m → Subgroup G} (hD : IsInternalDirect ⊤ Hs) (hF : ∀ i, IsFactor148 (Hs i)) :
    ∃ (O : Fin m → Subgroup G) (J : Finset (Fin m)),
      (∀ i, i ∉ J ↔ IsComponentOf (Hs i) ⊤) ∧
      (∀ k ∈ J, O k ≤ Hs k) ∧ (∀ i ∉ J, O i = Hs i) ∧ (∀ k ∈ J, (O k).Normal) ∧
      (∀ i j, i ≠ j → ∀ h ∈ Hs j, ∀ n ∈ commOn ρ (O i) ⊤, ρ h n = n) ∧
      (∀ k ∈ J, ∀ h ∈ Hs k, (∀ n ∈ commOn ρ (O k) ⊤, ρ h n = n) → h = 1) ∧
      (∀ k ∈ J, IsCompl (commOn ρ (O k) ⊤) (fixSub ρ (O k))) ∧
      (∀ k ∈ J, ∀ X : Subgroup G, CFSG.Open.IsElemAbelian 2 X →
        NoExcess ρ X (commOn ρ (O k) ⊤)) ∧
      ∀ i, O i = ⁅Hs i, Hs i⁆ := by
  classical
  have hHC := sup_centralizer_eq_top_of_isInternalDirect hD
  have hdata := fun i => factorData_of_isFactor148 hρ hshape hH (hF i) (hHC i)
  set J : Finset (Fin m) := Finset.univ.filter fun i => ¬ IsComponentOf (Hs i) ⊤ with hJdef
  have hJ : ∀ i, i ∉ J ↔ IsComponentOf (Hs i) ⊤ := fun i => by simp [hJdef]
  have hnc : ∀ k ∈ J, ¬ IsComponentOf (Hs k) ⊤ := fun k hk hc => (hJ k).2 hc hk
  refine ⟨fun i => ⁅Hs i, Hs i⁆, J, hJ, fun k _ => Subgroup.commutator_le_self _,
    fun i hi => (hdata i).2.2.2.1 ((hJ i).1 hi), fun k _ => ?_,
    fun i j hij h hh => (hdata i).1 h fun x hx => hD.2.1 j i (Ne.symm hij) h hh x hx,
    fun k hk => ((hdata k).2.2.2.2 (hnc k hk)).1, fun k hk => ((hdata k).2.2.2.2 (hnc k hk)).2.1,
    fun k hk => ((hdata k).2.2.2.2 (hnc k hk)).2.2, fun i => rfl⟩
  haveI : (Hs k).Normal := TauCeti.normal_of_commute_of_sup_eq_top
    (fun c hc x hx => Subgroup.mem_centralizer_iff.1 hx c hc) (hHC k)
  infer_instance

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
