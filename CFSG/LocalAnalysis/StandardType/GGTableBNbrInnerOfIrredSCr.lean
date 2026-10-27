module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSCr
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusNbrSCr_of_ggTorusIrredSCr {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : TwE6TB.GGTorusIrredSCr p r R I) : GGTorusNbrSCr p r R I := by
  have := Fact.mk hp
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  obtain ⟨W, hW1, hW2, -, -⟩ := h L' ψ hψ hker hperf A hA hAI hr h3 hsc
  refine ⟨W, hW1, fun Y hWA hWY hYA hYp => ?_⟩
  set A' : Subgroup (MulAut L') := A ⊓ Subgroup.centralizer (Y : Set (MulAut L')) with hA'
  have hA'inv : ∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
    intro n hn a ha
    refine ⟨hWA n hn a ha.1, Subgroup.mem_centralizer_iff.mpr fun φ hφ => ?_⟩
    have hχ := inv_conj_mem_of_conj_mem (hWY n hn) hφ
    have hc := Subgroup.mem_centralizer_iff.mp ha.2 _ hχ
    set c := MulAut.conj n
    calc φ * (c * a * c⁻¹) = c * ((c⁻¹ * φ * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * φ * c)) * c⁻¹ := by rw [hc]
      _ = c * a * c⁻¹ * φ := by group
  rcases hW2 A' inf_le_left hA'inv with hbot | htop
  · exfalso
    have hA1 : Nat.card A ≠ 1 := by
      intro h1
      rw [h1] at h3
      have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    obtain ⟨a, ha, ha1, hac⟩ :=
      exists_ne_one_forall_comm_of_pGroup (isPGroup_of_isElemAbelian hA) hA1 hYA hYp
    have haA' : a ∈ A' := ⟨ha, Subgroup.mem_centralizer_iff.mpr hac⟩
    rw [hbot] at haA'
    exact ha1 (Subgroup.mem_bot.mp haA')
  · intro φ hφ a ha
    have haA' : a ∈ A' := htop ▸ ha
    exact Subgroup.mem_centralizer_iff.mp haA'.2 φ hφ

end CFSG.StandardType

end
