module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowPElement
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowFunSet
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddExcFrameCommute
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35FrameExc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22


theorem normSylowAt_exceptional {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {t : StatedLieTag} {n r f : ℕ}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hr2 : r ≠ 2) (hadm : StatedLieAdmissible t n r f)
    (hX : CFSG.Blueprint.LieModel X t n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormSylowAt X p := by
  classical
  have hpr : r.Prime := hadm.1
  have : Fact r.Prime := ⟨hpr⟩
  have : IsSimpleGroup X := hXs
  have hn : n = 0 := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact hadm.2.2
  subst hn
  have hA1 : ¬ (t = .PSL ∧ 0 = 2) := by simp
  have hRee : t ≠ .twistedG2 := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide
  have hp2 : p ≠ 2 := by omega
  refine normSylowAt_of_pPow hp ?_
  intro S hS y hyN ⟨j, hyj⟩ hyp
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  let P : Sylow 2 X :=
    hSiff.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hSiff.2.2)
  have hPcoe : (P : Subgroup X) = S := IsPGroup.toSylow_coe _ _
  have hyNP : y ∈ normalizer ((P : Subgroup X) : Set X) := hPcoe.symm ▸ hyN
  have hypP : y ^ p ∈ centralizer ((P : Subgroup X) : Set X) := hPcoe.symm ▸ hyp
  rw [← hPcoe]
  have hyK := mem_centralizer_funSet_of_mem_normalizer hpr hr2 hadm hX hA1 hRee P hyNP hp hp5
    hyj hypP
  have hconj : ∀ (g : X) {K : Subgroup X}, fundPred (r ^ f) (⊤ : Subgroup X) K →
      fundPred (r ^ f) (⊤ : Subgroup X) (K.map (MulAut.conj g).toMonoidHom) :=
    fun g _ h => CFSG.LocalAnalysis.UniquenessCase.isFundamentalOver_map_mulEquiv
      (MulAut.conj g) h
  refine mem_centralizer_of_commute_funSet hconj P hp hp2 ?_ hyNP hyj hyK
  intro z₁ z₂ hz₁ hz₂ h₁ h₂
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    have hz : ∀ z : X, (∃ i : ℕ, z ^ p ^ i = 1) →
        (∀ K ∈ F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X), z ∈ centralizer (K : Set X)) →
        z = 1 := by
      intro z ⟨i, hi⟩ hzK
      have hB : IsPGroup p (zpowers z) := by
        rintro ⟨g, hg⟩
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hg
        refine ⟨i, Subtype.ext ?_⟩
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hi, one_zpow]
      have hbot := eq_bot_of_forall_funSet_f4 hr2 hadm hX P hp hp2 hB
        (fun K hK => (Subgroup.zpowers_le).mpr (hzK K hK))
      have hmem := mem_zpowers z
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [hz z₁ hz₁ h₁, hz z₂ hz₂ h₂]
  · exact commute_of_mem_centralizer_funSet_e6 hr2 hadm hX P h₁ h₂
  · exact commute_of_mem_centralizer_funSet_e7 hr2 hadm hX P h₁ h₂
  · exact commute_of_mem_centralizer_funSet_e8 hr2 hadm hX P h₁ h₂
  · exact commute_of_mem_centralizer_funSet_twistedE6 hr2 hadm hX P h₁ h₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

end
