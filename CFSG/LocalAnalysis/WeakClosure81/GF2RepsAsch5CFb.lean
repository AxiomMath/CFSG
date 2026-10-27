module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (OInf)

theorem exists_cComp_le_of_isSubnormal_not_isSolvable {Q : Type} [Group Q] [Finite Q]
    {H L : Subgroup Q} (hsub : IsSubnormal L H) (hsolv : ¬ Group.IsSolvable ↥L) :
    ∃ C : Subgroup Q, C ∈ cComp H ∧ C ≤ L := by
  have hne : perfectCore L ≠ ⊥ := fun h => hsolv ((isSolvable_iff_perfectCore_eq_bot L).mpr h)
  have hperf : perfectCore (perfectCore L) = perfectCore L :=
    perfectCore_eq_self_of_perfect (perfectCore_perfect L)
  have hsubP : IsSubnormal (perfectCore L) H := A3.subnormal_perfectCore hsub
  obtain ⟨C, hC⟩ := (Set.toFinite
    {K : Subgroup Q | K ≤ perfectCore L ∧ K ≠ ⊥ ∧ perfectCore K = K ∧
      IsSubnormal K H}).exists_minimal ⟨perfectCore L, le_rfl, hne, hperf, hsubP⟩
  obtain ⟨hCle, hCne, hCperf, hCsub⟩ := hC.1
  refine ⟨C, mem_cComp_iff_minimal.mpr ⟨⟨hCne, hCperf, hCsub⟩, ?_⟩, hCle.trans (perfectCore_le L)⟩
  rintro K ⟨hKne, hKperf, hKsub⟩ hKC
  exact hC.2 ⟨hKC.trans hCle, hKne, hKperf, hKsub⟩ hKC

theorem not_isSolvable_of_isComponentModN {Q : Type} [Group Q] {H L : Subgroup Q}
    (hL : IsComponentModN (OInf H) H L) : ¬ Group.IsSolvable ↥L := by
  obtain ⟨-, -, -, -, X, hXg, φ, hφ, -, hX⟩ := hL
  intro hs
  have hsX : Group.IsSolvable X := Group.isSolvable_of_surjective hφ
  obtain ⟨hperf, hsimp, -⟩ := hX
  haveI := hperf
  haveI := hsimp
  haveI : Nontrivial X := (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  exact Group.IsPerfect.not_isSolvable X hsX

theorem sup_eq_of_mem_cComp_of_isComponentModN {Q : Type} [Group Q] [Finite Q]
    {H L C : Subgroup Q} (hL : IsComponentModN (OInf H) H L) (hC : C ∈ cComp H) (hCL : C ≤ L) :
    C ⊔ OInf H = L := by
  obtain ⟨hNn, hNL, hLH, hLsub, X, hXg, φ, hφ, hker, hX⟩ := hL
  obtain ⟨hperfX, hsimpX, -⟩ := hX
  have hXopen : CFSG.Open.IsQuasisimple X := ⟨hperfX.commutator_eq_top, hsimpX⟩
  have hNsolv : Group.IsSolvable ↥(OInf H) := by
    have h := solvRad_isSolvable H
    rwa [solvRad_eq_map_solvableRadical] at h
  have hCsubL : CFSG.Open.IsSubnormal C L :=
    A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hC) hCL hLH
  let C' : Subgroup ↥L := C.subgroupOf L
  have hC'sub : C'.IsSubnormal := CFSG.Open.IsSubnormal.subgroupOf hCsubL
  have hC'perf : ⁅C', C'⁆ = C' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator]
    have h1 : C'.map L.subtype = C := Subgroup.map_subgroupOf_eq_of_le hCL
    rw [h1]
    exact perfect_of_mem_cComp hC
  let R : Subgroup X := C'.map φ
  have hRperf : ⁅R, R⁆ = R := by
    change ⁅C'.map φ, C'.map φ⁆ = C'.map φ
    rw [← Subgroup.map_commutator, hC'perf]
  have hRsub : R.IsSubnormal := Subgroup.IsSubnormal.map hφ hC'sub
  have hRopen : CFSG.Open.IsSubnormal R ⊤ := CFSG.Open.IsSubnormal.of_mathlib hRsub
  haveI : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hRperf
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
    hXopen R hRopen with hR | hR
  · exfalso
    have hCN : C ≤ OInf H := by
      intro c hc
      have hx : (⟨c, hCL hc⟩ : ↥L) ∈ C' := hc
      have h1 : φ ⟨c, hCL hc⟩ ∈ R := Subgroup.mem_map_of_mem φ hx
      rw [hR, Subgroup.mem_bot] at h1
      exact (hker _).mp h1
    haveI := hNsolv
    have hCs : Group.IsSolvable ↥C :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hCN)
        (Subgroup.inclusion_injective hCN)
    exact not_isSolvable_of_mem_cComp hC hCs
  · refine le_antisymm (sup_le hCL hNL) ?_
    intro l hl
    let x : ↥L := ⟨l, hl⟩
    have hx : φ x ∈ R := by rw [hR]; exact Subgroup.mem_top _
    obtain ⟨c', hc', hφc'⟩ := Subgroup.mem_map.mp hx
    have hn : ((c'⁻¹ * x : ↥L) : Q) ∈ (OInf H : Set Q) := by
      apply (hker _).mp
      rw [map_mul, map_inv, hφc', inv_mul_cancel]
    have hcC : (c' : Q) ∈ C := hc'
    have hmem : (c' : Q) * ((c'⁻¹ * x : ↥L) : Q) ∈ C ⊔ OInf H := Subgroup.mul_mem_sup hcC hn
    have heq : (c' : Q) * ((c'⁻¹ * x : ↥L) : Q) = l := by
      simp [x]
    rwa [heq] at hmem

theorem exists_cComp_of_isComponentModN {Q : Type} [Group Q] [Finite Q] {H L : Subgroup Q}
    (hL : IsComponentModN (OInf H) H L) :
    ∃ C : Subgroup Q, C ∈ cComp H ∧ C ≤ L ∧ C ⊔ OInf H = L := by
  obtain ⟨C, hC, hCL⟩ := exists_cComp_le_of_isSubnormal_not_isSolvable hL.2.2.2.1
    (not_isSolvable_of_isComponentModN hL)
  exact ⟨C, hC, hCL, sup_eq_of_mem_cComp_of_isComponentModN hL hC hCL⟩

end CFSG.LocalAnalysis.WeakClosure81
