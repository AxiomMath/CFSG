module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenC
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenD
public import CFSG.LocalAnalysis.WeakClosure81.W15Bundle

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.kerMOf_le_centralizer_of_inf_eq_bot (hI : NamedInputs15 G) (hS : Std15 G)
    (h152 : Thm152 G) (h1 : W16One G) (hV₀ : V₀ ≤ pCoreOf 2 H)
    (hX : Hyp167 M V₀ V U S H g X T) (hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥) :
    kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) := by
  have hA : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hpair : IsPairAt M X (conjSubgroup V g) := hX.mem.2.2
  have hXU : X ≤ centralizer (U : Set G) := hX.mem.1.trans hX.min.1.2.1
  have hK : CFSG.Open.IsKGroup ↥X :=
    (hS.localsK _ ⟨U, hX.cex.ne_bot, hX.cex.hyp.isPGroup.to_le hX.cex.le, rfl⟩).of_le
      (hXU.trans (Subgroup.centralizer_le_normalizer (U : Set G)))
  have hbig := Hyp167.two_lt_relIndex_of_inf_eq_bot h1 hS h152 hV₀ hX hBE
  obtain ⟨⟨n, hn⟩, -⟩ := five_nine_borel hI.thmB hpair hA hK hbig
  have hC : X ⊓ centralizer (eSub V₀ X T : Set G) ≤ kerMOf M X :=
    Hyp167.inf_centralizer_eSub_le_kerMOf hX
  have hXn : X ≤ normalizer (eSub V₀ X T : Set G) := le_normalizer_conjClosure _ _
  have hCn : ((X ⊓ centralizer (eSub V₀ X T : Set G)).subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro n x hn hx
    refine ⟨X.mul_mem (X.mul_mem hx hn.1) (X.inv_mem hx),
      Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have he' : x⁻¹ * e * x ∈ eSub V₀ X T := by
      have := (Subgroup.mem_normalizer_iff.1 (hXn (X.inv_mem hx)) e).1 he
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hn.2 _ he'
    calc e * (x * n * x⁻¹) = x * ((x⁻¹ * e * x) * n) * x⁻¹ := by group
      _ = x * (n * (x⁻¹ * e * x)) * x⁻¹ := by rw [hc]
      _ = x * n * x⁻¹ * e := by group
  have hTK : T ⊓ kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) :=
    Hyp167.inf_kerMOf_le_centralizer_eSub hX
  have hTK' : T ⊓ kerMOf M X ≤ X ⊓ centralizer (eSub V₀ X T : Set G) :=
    le_inf ((inf_le_right).trans (kerMOf_le_group M X)) hTK
  have hAT : conjSubgroup V g ≤ T := hX.A_le_T
  have hAK : conjSubgroup V g ⊓ kerMOf M X ≤ X ⊓ centralizer (eSub V₀ X T : Set G) :=
    (inf_le_inf_right (kerMOf M X) hAT).trans hTK'
  have hgen : conjClosure (conjSubgroup V g) X ⊔ (X ⊓ centralizer (eSub V₀ X T : Set G)) = X := by
    refine le_antisymm (sup_le (conjClosure_le fun k hk z hz => ?_) inf_le_left) ?_
    · exact X.mul_mem (X.mul_mem hk (hX.mem.2.2.A_le hz)) (X.inv_mem hk)
    · calc X = conjClosure (conjSubgroup V g) X ⊔ pCoreOf 2 (kerMOf M X) :=
            Hyp167.eq_conjClosure_sup_pCoreOf hX
        _ ≤ conjClosure (conjSubgroup V g) X ⊔ (X ⊓ centralizer (eSub V₀ X T : Set G)) :=
            sup_le_sup_left (by rw [← Hyp167.inf_kerMOf_eq_pCoreOf hX]; exact hTK') _
  have hcomm : ⁅conjSubgroup V g, kerMOf M X⁆ ≤ X ⊓ centralizer (eSub V₀ X T : Set G) := by
    refine le_inf ?_ (Hyp167.commutator_kerMOf_le_centralizer_eSub h1 hS h152 hV₀ hX hBE)
    rw [Subgroup.commutator_le]
    intro a ha k hk
    have hkX : k ∈ X := kerMOf_le_group M X hk
    have haX : a ∈ X := hpair.A_le ha
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem haX hkX) (X.inv_mem haX)) (X.inv_mem hkX)
  exact (IsPairAt.kerMOf_le_of_commutator_le hI.mult hpair hA.isPGroup hCn hC
    (Hyp167.odd_relIndex_inf_centralizer_eSub hX) hcomm hAK hgen
    ⟨n, one_lt_of_isPSL_or_isSz hn, hn⟩).trans inf_le_right

end CFSG.LocalAnalysis.WeakClosure81

end
