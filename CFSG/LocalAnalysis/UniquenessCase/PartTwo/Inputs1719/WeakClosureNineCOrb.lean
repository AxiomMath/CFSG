module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbCopy
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCStmt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

namespace TC914

variable {X : Type} [Group X] [Finite X] {Lb Tb : Subgroup X} {B : Type} [Group B] [Finite B]
  {π : ↥(tcN1 Lb Tb) →* B} {Es : Subgroup B}

omit [Finite B] in
theorem orbData_of (c : TCBar Lb Tb π Es) {A : Subgroup X} (hAT : A ≤ Tb)
    (hAe : IsElemAbelian 2 A) (hAL : ¬ A ≤ normalizer (Lb : Set X)) {H Xh : Subgroup B} {p : ℕ}
    (hmov : MovWit914 (barSub π Lb) (barSub π Tb) (barSub π (A ⊓ normalizer (Lb : Set X)))
      H Xh p)
    {F : Subgroup X} (hFT : F ≤ tcT1 Lb Tb) (hTF : Tb ≤ normalizer (F : Set X))
    (hFH : barSub π F ≤ normalizer (H : Set B))
    (hFX : ∀ f ∈ barSub π F, ∀ x ∈ Xh, f * x * f⁻¹ * x⁻¹ ∈ pCoreOf 2 H) :
    ∃ C : Subgroup X, OrbData Lb Tb A C F (lbCopy π H) (lbCopy π Xh) p := by
  obtain ⟨C, hCA, hCinf, hCsup⟩ :=
    exists_compl_of_isElemAbelian hAe (inf_le_left : A ⊓ normalizer (Lb : Set X) ≤ A)
  have hcomm := hAe.1
  have hT1 : tcT1 Lb Tb ≤ tcN1 Lb Tb := le_sup_right
  refine ⟨C, ⟨c.sylow.isPGroup, hAT, fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩), hCA, ?_, hCsup, ?_, lcomm_of c,
    lbCopy_le H, twoPTwoIrred_lbCopy_inf c hmov.irr hmov.le,
    (isElemAbelian_comap (lbHom_injective c) hmov.elem).map _,
    nontriv_lbCopy c hmov.le hmov.irr.sylowP.le hmov.nontriv,
    lbCopy_inf_centralizer c hmov.inf_centralizer,
    le_normalizer_lbCopy ((le_inf (inf_le_left.trans hAT) inf_le_right).trans hT1)
      hmov.normalizes, hFT.trans inf_le_left, hTF, le_normalizer_lbCopy (hFT.trans hT1) hFH,
    commutator_mem_lbCopy c hmov.le hFT hFX⟩⟩
  · rw [← hCinf, ← inf_assoc, inf_eq_left.2 hCA]
  · intro h
    apply hAL
    rw [← hCsup, h, bot_sup_eq]
    exact inf_le_right

end TC914

theorem orbitStmt_holds : OrbitStmt := by
  intro X _ _ Lb Tb B _ _ π Es c A hAT hAe hAL H Xh p hmov F hFT hTF hFH hFX
  obtain ⟨C, d⟩ := TC914.orbData_of c hAT hAe hAL hmov hFT hTF hFH hFX
  obtain ⟨K, Y, hK, hAK, hnot, hF, hXY⟩ := d.exists_K
  refine ⟨K, Y, hK, hAK, hnot, hF, hmov.three.imp id fun ⟨y, hy, hy3⟩ J hTJ hYJ => ?_⟩
  have hle : closure {z | ∃ d ∈ barSub π Tb, ∃ x ∈ Xh, z = d * x * d⁻¹} ≤ barSub π J := by
    rw [closure_le]
    rintro _ ⟨_, ⟨t, ht, rfl⟩, x, hx, rfl⟩
    obtain ⟨x₀, rfl⟩ : x ∈ (TC914.lbHom π).range := by
      rw [TC914.lbHom_range]
      exact hmov.le (hmov.irr.sylowP.le hx)
    have hJ : (t : X) * x₀ * (t : X)⁻¹ ∈ J :=
      (mem_normalizer_iff.1 (hTJ (mem_subgroupOf.1 ht)) _).1
        (hYJ (hXY (TC914.coe_mem_lbCopy.2 hx)))
    exact ⟨t * inclusion le_sup_left x₀ * t⁻¹, hJ, by rw [map_mul, map_mul, map_inv]; rfl⟩
  exact NFW.exists_orderOf_eq_of_barSub (hle hy) hy3

end CFSG.LocalAnalysis.WeakClosure81
