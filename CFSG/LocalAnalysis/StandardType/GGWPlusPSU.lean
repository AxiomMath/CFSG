module

public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitQuot
public import CFSG.LocalAnalysis.StandardType.GGWPlusPositionRk
public import CFSG.LocalAnalysis.StandardType.GGWPlusAutomizer
public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBMeta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem finite_largeEvenProj_PSU {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] (H : Subgroup (GL ι K)) : Finite (LargeEvenProj H) := by
  have : Finite H := Subtype.finite
  exact Finite.of_surjective _ (QuotientGroup.mk'_surjective _)

theorem ggWPlusTableBRk_PSU
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) :
    GGWPlusTableBRk p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n))) (d - 1) := by
  intro M _ _ L' E θ hE hP hr6 hZ A M₁ E₁ h hXA hAN hAp hME hEA hCM hAM hAE hpow hh hhp hAh
  haveI : Finite (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
    finite_largeEvenProj_PSU _
  haveI : Finite (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    Finite.of_injective
      (fun f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) =>
        (f : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →
          LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
      DFunLike.coe_injective
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hr : p ^ (d - 2) ≤ Nat.card (ggLAutImage L' θ E) := by
    simpa only [show d - 1 - 1 = d - 2 by omega] using
      pow_pred_le_card_ggLAutImage hP hp hr6
  have hsc : GGTorusSelfCent p (ggLAutImage L' θ E) :=
    ggTorusSelfCent_ggLAutImage hP hp hZ
  have hA : IsElemAbelian p (ggLAutImage L' θ E) :=
    ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hP.2.1 _) (ggLAut L' θ)
  have hI : (ggLAutImage L' θ E : Set
        (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    intro a ha
    simp only [ggLAutImage, Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hxe : (⟨(x : M), hE hx⟩ : Subgroup.normalizer (L' : Set M)) = x :=
      Subtype.ext rfl
    rw [← hxe]
    exact hP.2.2.2.1 ⟨(x : M), hx⟩
  have hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ y
    have hl : l ∈ commutator L' := by rw [hP.1]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem (ggQuotHom θ) hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (ggQuotHom_surjective θ), ← commutator_def] at h1
  have hX := ggSolvQuotLeTwo_PSU hK hn hd hp hpq hpd hperf hA hI hr hsc
  haveI : ((MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).range).Normal :=
    ggInnNormal _
  exact wplus_of_automizer hp hp2 _
    (ggLAutImage L' θ E) hX A M₁ E₁ hXA hAN hAp hME hEA hCM hAM hAE hpow h hh hAh

end CFSG.StandardType
