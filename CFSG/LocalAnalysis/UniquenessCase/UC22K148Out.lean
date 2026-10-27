module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

namespace OutAux

theorem mem_fixSub_iSup {ι : Sort*} {Hs : ι → Subgroup G} {x : V}
    (h : ∀ j, x ∈ fixSub ρ (Hs j)) : x ∈ fixSub ρ (⨆ j, Hs j) :=
  mem_fixSub.2 fun _ ha => Subgroup.iSup_induction Hs (C := fun g => ρ g x = x) ha
    (fun j g hg => h j g hg) (by rw [map_one, Module.End.one_apply])
    fun g g' hg hg' => by rw [map_mul, Module.End.mul_apply, hg', hg]

end OutAux

theorem commOn_uP_le_uP {X : Subgroup G} (hX : X ≤ hP ρ) : commOn ρ X (uP ρ) ≤ uP ρ :=
  Replacement.commOn_le_iff.2 fun _ ha _ _ => sub_mem_commOn (hX ha) Submodule.mem_top

theorem inf_cUP_eq_inf_fixSub {m : ℕ} {Hs : Fin m → Subgroup G}
    (hH : IsInternalDirect (hP ρ) Hs)
    (hD1 : ∀ i j, i ≠ j → commOn ρ (Hs i) (uP ρ) ≤ fixSub ρ (Hs j)) (i : Fin m) :
    commOn ρ (Hs i) (uP ρ) ⊓ cUP ρ = commOn ρ (Hs i) (uP ρ) ⊓ fixSub ρ (Hs i) := by
  have hle : Hs i ≤ hP ρ := (le_iSup Hs i).trans hH.1.le
  refine le_antisymm (inf_le_inf_left _ (inf_le_right.trans (fixSub_antitone hle))) ?_
  rintro x ⟨hx, hxi⟩
  have hxH : x ∈ fixSub ρ (hP ρ) := by
    rw [← hH.1]
    refine OutAux.mem_fixSub_iSup fun j => ?_
    rcases eq_or_ne i j with rfl | hij
    · exact hxi
    · exact hD1 i j hij hx
  exact ⟨hx, commOn_uP_le_uP hle hx, hxH⟩

theorem isDirectSumMod_of_factors {m : ℕ} {Hs : Fin m → Subgroup G}
    (hH : IsInternalDirect (hP ρ) Hs)
    (hD1 : ∀ i j, i ≠ j → commOn ρ (Hs i) (uP ρ) ≤ fixSub ρ (Hs j))
    (hD2 : uP ρ ≤ (⨆ i, commOn ρ (Hs i) (uP ρ)) ⊔ cUP ρ) :
    IsDirectSumMod (uP ρ) (cUP ρ) (fun i => commOn ρ (Hs i) (uP ρ)) := by
  have hle : ∀ i, Hs i ≤ hP ρ := fun i => (le_iSup Hs i).trans hH.1.le
  refine ⟨le_antisymm (sup_le (iSup_le fun i => commOn_uP_le_uP (hle i)) inf_le_left) hD2,
    fun i => ?_⟩
  have hC : cUP ρ ≤ fixSub ρ (Hs i) := inf_le_right.trans (fixSub_antitone (hle i))
  have hS : (⨆ j ∈ {j | j ≠ i}, commOn ρ (Hs j) (uP ρ)) ≤ fixSub ρ (Hs i) :=
    iSup₂_le fun j hj => hD1 j i hj
  calc (commOn ρ (Hs i) (uP ρ) ⊔ cUP ρ) ⊓
        ((⨆ j ∈ {j | j ≠ i}, commOn ρ (Hs j) (uP ρ)) ⊔ cUP ρ)
      ≤ (commOn ρ (Hs i) (uP ρ) ⊔ cUP ρ) ⊓ fixSub ρ (Hs i) :=
        inf_le_inf_left _ (sup_le hS hC)
    _ = (cUP ρ ⊔ commOn ρ (Hs i) (uP ρ)) ⊓ fixSub ρ (Hs i) := by rw [sup_comm]
    _ = cUP ρ ⊔ commOn ρ (Hs i) (uP ρ) ⊓ fixSub ρ (Hs i) := sup_inf_assoc_of_le _ hC
    _ = cUP ρ ⊔ commOn ρ (Hs i) (uP ρ) ⊓ cUP ρ := by rw [inf_cUP_eq_inf_fixSub hH hD1 i]
    _ ≤ cUP ρ := sup_le le_rfl inf_le_right

theorem k148Concl_of_factors {m : ℕ} {Hs : Fin m → Subgroup G}
    (hH : IsInternalDirect (hP ρ) Hs)
    (hD1 : ∀ i j, i ≠ j → commOn ρ (Hs i) (uP ρ) ≤ fixSub ρ (Hs j))
    (hD2 : uP ρ ≤ (⨆ i, commOn ρ (Hs i) (uP ρ)) ⊔ cUP ρ)
    (hD3 : ∀ i, Shape148 ρ (Hs i) (commOn ρ (Hs i) (uP ρ)) (fixSub ρ (Hs i))) :
    K148Concl ρ := by
  refine ⟨m, Hs, hH, isDirectSumMod_of_factors hH hD1 hD2, fun i => ?_⟩
  have h := hD3 i
  unfold Shape148 at h ⊢
  rwa [inf_cUP_eq_inf_fixSub hH hD1 i]

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
