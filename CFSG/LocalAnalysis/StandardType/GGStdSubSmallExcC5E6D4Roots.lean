module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Lift

public section

namespace CFSG.StandardType.SmallExc.E6Node

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.StandardType.TableBExc.E6Three CFSG.SeitzReduction
open CFSG.LieType.Chevalley.C2E6Std (setD)


local instance : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def chiD4 {L : Type} [Field L] (l : Lˣ) : Fin Tag.E6.rank → Lˣ :=
  hChar (bE6 0) l * hChar (bE6 1) l

theorem mem_rootCharKernel_chiD4 {L : Type} [Field L] {l : Lˣ} (hl : orderOf l = 3)
    {γ : Fin Tag.E6.rank → ℤ} : γ ∈ rootCharKernel (chiD4 l) ↔
      IsRoot .E6 γ ∧ (iform (bE6 0) γ + iform (bE6 1) γ) % 3 = 0 := by
  simp only [rootCharKernel, Set.mem_setOf_eq, chiD4, rootChar_mul_left, rootChar_hChar,
    ← zpow_add]
  rw [← orderOf_dvd_iff_zpow_eq_one, hl, Nat.cast_ofNat, Int.dvd_iff_emod_eq_zero]

@[expose] def l2D4 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 0, 0]

@[expose] def l3D4 : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 1, 0, 0]

@[expose] def d4Roots : List (Fin Tag.E6.rank → ℤ) :=
  [bE6 2, -bE6 2, bE6 3, -bE6 3, l2D4, -l2D4, l3D4, -l3D4]

theorem d4Roots_spec : ∀ γ ∈ d4Roots,
    RootOps.isRootB .E6 γ = true ∧ (iform (bE6 0) γ + iform (bE6 1) γ) % 3 = 0 := by
  decide +kernel

theorem iform_sub_d4 : ∀ j : Fin Tag.E6.rank, iform (bE6 0) (Pi.single j 1) -
    iform (bE6 1) (Pi.single j 1) = iform l3D4 (Pi.single j 1) - iform l2D4 (Pi.single j 1) := by
  decide +kernel

@[expose] def d4Word : List (Fin Tag.E6.rank) := [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0]

@[expose] def d4Test (γ : Fin Tag.E6.rank → ℤ) : Bool :=
  decide ((iform (bE6 0) γ + iform (bE6 1) γ) % 3 = 0 →
    TableBExc.wordAct .E6 d4Word γ 0 = 0 ∧ TableBExc.wordAct .E6 d4Word γ 5 = 0 ∧
      permLattice (τ := Tag.E6) TwistTag.E6.perm (TableBExc.wordAct .E6 d4Word γ) =
        TableBExc.wordAct .E6 (d4Word ++ [1, 2]) γ)

theorem d4Test_roots : (List.range Tag.E6.rootCertificate.roots.length).all
    (fun k => d4Test (Tag.E6.rootCertificate.root k)) = true := by
  decide +kernel

@[expose] def d4TestInv (δ : Fin Tag.E6.rank → ℤ) : Bool :=
  decide (δ 0 = 0 ∧ δ 5 = 0 →
    (iform (bE6 0) (TableBExc.wordAct .E6 d4Word.reverse δ) +
        iform (bE6 1) (TableBExc.wordAct .E6 d4Word.reverse δ)) % 3 = 0 ∧
      TableBExc.wordAct .E6 d4Word (TableBExc.wordAct .E6 d4Word.reverse δ) = δ)

theorem d4TestInv_roots : (List.range Tag.E6.rootCertificate.roots.length).all
    (fun k => d4TestInv (Tag.E6.rootCertificate.root k)) = true := by
  decide +kernel

section Certs


theorem smul_d4Word_of_mem {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (h : (iform (bE6 0) γ + iform (bE6 1) γ) % 3 = 0) :
    (coxeterSystem .E6).wordProd d4Word • γ ∈ parabolicRoots .E6 setD ∧
      permLattice (τ := Tag.E6) TwistTag.E6.perm ((coxeterSystem .E6).wordProd d4Word • γ) =
        (coxeterSystem .E6).wordProd (d4Word ++ [1, 2]) • γ := by
  have hr : IsRoot .E6 (TableBExc.wordAct .E6 d4Word γ) := by
    rw [← TableBExc.wordProd_smul]
    exact IsRoot.smul hγ _
  rw [TableBExc.wordProd_smul, TableBExc.wordProd_smul]
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  have hc := d4Test_roots
  simp only [List.all_eq_true, List.mem_range, d4Test, decide_eq_true_eq] at hc
  obtain ⟨h0, h5, hρ⟩ := hc k hk h
  exact ⟨TwistedE6Pilot.mem_parabolicRoots_setD_iff.2 ⟨hr, h0, h5⟩, hρ⟩

theorem exists_smul_d4Word_eq {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ parabolicRoots .E6 setD) :
    ∃ γ, IsRoot .E6 γ ∧ (iform (bE6 0) γ + iform (bE6 1) γ) % 3 = 0 ∧
      (coxeterSystem .E6).wordProd d4Word • γ = δ := by
  obtain ⟨hr, h0, h5⟩ := TwistedE6Pilot.mem_parabolicRoots_setD_iff.1 hδ
  refine ⟨(coxeterSystem .E6).wordProd d4Word.reverse • δ, IsRoot.smul hr _, ?_⟩
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hr
  have hc := d4TestInv_roots
  simp only [List.all_eq_true, List.mem_range, d4TestInv, decide_eq_true_eq] at hc
  rw [TableBExc.wordProd_smul, TableBExc.wordProd_smul]
  exact hc k hk ⟨h0, h5⟩

end Certs

section R

variable {L : Type} [Field L]

theorem mem_rootCharKernel_of_mem_d4Roots {l : Lˣ} (hl : orderOf l = 3)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ d4Roots) :
    IsRoot .E6 γ ∧ γ ∈ rootCharKernel (chiD4 l) := by
  obtain ⟨h1, h2⟩ := d4Roots_spec γ hγ
  have hr := RootOps.isRootB_iff.mp h1
  exact ⟨hr, (mem_rootCharKernel_chiD4 hl).2 ⟨hr, h2⟩⟩


theorem rootSL2_mem_rootSpan_d4 {l : Lˣ} (hl : orderOf l = 3) {β : Fin Tag.E6.rank → ℤ}
    (h1 : β ∈ d4Roots) (h2 : -β ∈ d4Roots) (A : SL2 L) :
    rootSL2 .E6 L β A ∈ rootSpan .E6 L (rootCharKernel (chiD4 l)) :=
  rootSL2_mem_rootSpan (mem_rootCharKernel_of_mem_d4Roots hl h1).1
    (mem_rootCharKernel_of_mem_d4Roots hl h1).2 (mem_rootCharKernel_of_mem_d4Roots hl h2).2 A

theorem rootDiagUnit_hChar_mem_rootSpan_d4 {l : Lˣ} (hl : orderOf l = 3) :
    rootDiagUnit .E6 (hChar (bE6 0) l) * (rootDiagUnit .E6 (hChar (bE6 1) l))⁻¹ ∈
      rootSpan .E6 L (rootCharKernel (chiD4 l)) := by
  have e : hChar (bE6 0) l * (hChar (bE6 1) l)⁻¹ = hChar l3D4 l * (hChar l2D4 l)⁻¹ := by
    funext j
    simp only [hChar, Pi.mul_apply, Pi.inv_apply, ← zpow_neg, ← zpow_add, ← sub_eq_add_neg,
      iform_sub_d4 j]
  rw [rootDiagUnit_inv, ← rootDiagUnit_mul, e, rootDiagUnit_mul, ← rootDiagUnit_inv,
    ← rootSL2_HSL_eq (mem_rootCharKernel_of_mem_d4Roots hl (γ := l3D4) (by simp [d4Roots])).1,
    ← rootSL2_HSL_eq (mem_rootCharKernel_of_mem_d4Roots hl (γ := l2D4) (by simp [d4Roots])).1]
  exact mul_mem (rootSL2_mem_rootSpan_d4 hl (by simp [d4Roots]) (by simp [d4Roots]) _)
    (inv_mem (rootSL2_mem_rootSpan_d4 hl (by simp [d4Roots]) (by simp [d4Roots]) _))

end R

end CFSG.StandardType.SmallExc.E6Node

end
