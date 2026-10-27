module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeam
public import CFSG.LocalAnalysis.StandardType.PhanEResPsiAct
public import CFSG.LocalAnalysis.StandardType.PhanEResOrbitBlock
public import CFSG.LocalAnalysis.StandardType.PhanEResOrbitPanel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix Module CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Universal.SpecialLinear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {d : List ℕ}

private theorem plo_orbit_step (hd : IsCut (m + 1) d) {a b : FlagK K (m + 1)} {i : Fin m}
    (hi : i ∈ cutTypes m d)
    (ha : ∃ A ∈ blockSL K m d, a = flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)))
    (hab : (flagSys K m).adj i a b) :
    ∃ A ∈ blockSL K m d, b = flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)) := by
  obtain ⟨A, hA, rfl⟩ := ha
  have h1 : flagAct (SpecialLinearGroup.toGL A)
      (flagAct (SpecialLinearGroup.toGL A)⁻¹ b) = b := by
    rw [← flagAct_mul, mul_inv_cancel, flagAct_one]
  have hb : (flagSys K m).adj i (stdFlag K (m + 1))
      (flagAct (SpecialLinearGroup.toGL A)⁻¹ b) := by
    rw [← h1] at hab
    exact (flagMap_adj (e := glLin (SpecialLinearGroup.toGL A))).mp hab
  obtain ⟨B, hB, hBy⟩ := exists_sl2_of_adj (K := K) i hb
  have hsub : {A : SpecialLinearGroup (Fin (m + 1)) K |
      ∃ c : K, A = tv K i.castSucc i.succ c ∨ A = tv K i.succ i.castSucc c} ⊆
      {A | ∃ k : Fin m, k ∈ cutTypes m d ∧ ∃ c : K,
        A = tv K k.castSucc k.succ c ∨ A = tv K k.succ k.castSucc c} := by
    rintro A ⟨c, hc | hc⟩
    · exact ⟨i, hi, c, Or.inl hc⟩
    · exact ⟨i, hi, c, Or.inr hc⟩
  refine ⟨A * B, (blockSL K m d).mul_mem hA (Subgroup.closure_mono hsub hB), ?_⟩
  rw [← h1, hBy, ← flagAct_mul, ← map_mul]

private theorem plo_gallery_orbit_aux (hd : IsCut (m + 1) d) :
    ∀ (γ : List (Fin m × FlagK K (m + 1))) (a : FlagK K (m + 1)),
      (∃ A ∈ blockSL K m d, a = flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1))) →
      (flagSys K m).IsGallery a γ →
      (∀ i ∈ galleryType γ, i ∈ cutTypes m d) →
      ∃ A ∈ blockSL K m d, galleryEnd a γ =
        flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)) := by
  intro γ
  induction γ with
  | nil =>
    intro a ha _ _
    exact ha
  | cons p γ ih =>
    intro a ha hγ hJ
    obtain ⟨h1, h2⟩ := hγ
    have hstep := plo_orbit_step hd (hJ p.1 (by simp)) ha h1
    exact ih p.2 hstep h2 (fun i hi => hJ i (List.mem_cons_of_mem p.1 hi))

theorem exists_blockSL_of_mem_refSet (hd : IsCut (m + 1) d) {x : FlagK K (m + 1)}
    (hx : x ∈ refSet K (m + 1) d) :
    ∃ A ∈ blockSL K m d, x = flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)) := by
  have hstd : stdFlag K (m + 1) ∈ refSet K (m + 1) d := stdFlag_mem_refSet hd
  have hxres : x ∈ (flagSys K m).residue (cutTypes m d) (stdFlag K (m + 1)) := by
    rw [← residue_flagδ_eq (K := K) (cutTypes m d) (stdFlag K (m + 1))]
    rw [residue_cutTypes_eq hd hstd]
    exact hx
  obtain ⟨γ, hγ, hJ, hxend⟩ := hxres
  obtain ⟨A, hA, hAx⟩ := plo_gallery_orbit_aux hd γ (stdFlag K (m + 1))
    ⟨1, Subgroup.one_mem _, by rw [map_one, flagAct_one]⟩ hγ hJ
  exact ⟨A, hA, by rw [← hxend]; exact hAx⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
