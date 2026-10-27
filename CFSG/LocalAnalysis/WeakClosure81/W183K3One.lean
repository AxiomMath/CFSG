module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3NC
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fin
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W183K3InnerFour
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

theorem br3_false_of_one (rows : Br3Rows) (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br3OneComp Y T L)
    (hshape : IsL3 (↥L ⧸ Subgroup.center ↥L) 2 ∨ IsAlt (↥L ⧸ Subgroup.center ↥L) 6)
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty) : False := by
  classical
  rcases hshape with h | h
  · obtain ⟨hnc, hdyn⟩ := rows.g4l34 (↥L ⧸ Subgroup.center ↥L) h
    have hX₀ : innAutOf (↥L ⧸ Subgroup.center ↥L) ≤
        (psiQuot Y L hL.core.normal).range := by
      rw [← QuasiCore.imgOf_psiQuot_L hL.core]
      exact imgOf_le_range _ _
    have hX₀n : ∀ r : ↥Y, ∀ x ∈ innAutOf (↥L ⧸ Subgroup.center ↥L),
        psiQuot Y L hL.core.normal r * x * (psiQuot Y L hL.core.normal r)⁻¹ ∈
          innAutOf (↥L ⧸ Subgroup.center ↥L) :=
      fun r x hx => psiQuot_conj_mem_innAutOf hL.core r hx
    have hmem : ∀ D ∈ Γ, imgOf (psiQuot Y L hL.core.normal) D ≤
        innAutOf (↥L ⧸ Subgroup.center ↥L) :=
      fun D hD => w183k3_inner_of_quadratic rows.h65f hL.core h
        (hc.h131.le_G D hD) (hc.h131.isElemAb D hD) (hc.h131.quadratic D hD) (hrk D hD)
    exact w183k3_false_of_dynkin hc.toBr1Base hL hX₀ hX₀n hmem hnc hdyn hrk hne
  · obtain ⟨hX₀normal, hle, hsup, hnc1, hnc2⟩ :=
      rows.g4a6 (↥L ⧸ Subgroup.center ↥L) h
    let ψ := psiQuot Y L hL.core.normal
    have hcard_ne : ∀ D ∈ Γ, Nat.card D ≠ 0 := by
      intro D _
      exact Nat.pos_iff_ne_zero.mp (Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩)
    have hcard8 : ∀ D ∈ Γ, 8 ≤ Nat.card (imgOf ψ D) := by
      intro D hD
      rw [QuasiCore.card_imgOf_psiQuot hL.core (hc.h131.le_G D hD)
        (hc.h131.isElemAb D hD).isPGroup]
      have hlog : 3 ≤ Nat.log 2 (Nat.card D) := hrk D hD
      have hpow : 2 ^ 3 ≤ Nat.card D := Nat.pow_le_of_le_log (hcard_ne D hD) hlog
      norm_num at hpow
      exact hpow
    have hEA : ∀ D ∈ Γ, IsElemAbelian 2 (imgOf ψ D) := by
      intro D hD
      rw [imgOf]
      exact CFSG.Open.IsElemAbelian.map
        (CFSG.Open.IsElemAbelian.subgroupOf (hc.h131.isElemAb D hD) Y) ψ
    have hmem : ∀ D ∈ Γ, imgOf ψ D ≤ autNoDynkin (↥L ⧸ Subgroup.center ↥L) :=
      fun D hD => hle (imgOf ψ D) (hEA D hD) (hcard8 D hD)
    have hX₀ : autNoDynkin (↥L ⧸ Subgroup.center ↥L) ≤ ψ.range := by
      obtain ⟨D₀, hD₀⟩ := hne
      have hsup₀ : innAutOf (↥L ⧸ Subgroup.center ↥L) ⊔ imgOf ψ D₀ =
          autNoDynkin (↥L ⧸ Subgroup.center ↥L) :=
        hsup (imgOf ψ D₀) (hEA D₀ hD₀) (hcard8 D₀ hD₀)
      rw [← hsup₀]
      refine sup_le ?_ (imgOf_le_range ψ D₀)
      rw [show innAutOf (↥L ⧸ Subgroup.center ↥L) = imgOf ψ L from
        (QuasiCore.imgOf_psiQuot_L hL.core).symm]
      exact imgOf_le_range ψ L
    have hX₀n : ∀ r : ↥Y, ∀ x ∈ autNoDynkin (↥L ⧸ Subgroup.center ↥L),
        ψ r * x * (ψ r)⁻¹ ∈ autNoDynkin (↥L ⧸ Subgroup.center ↥L) :=
      fun r x hx => hX₀normal.conj_mem x hx (ψ r)
    exact w183k3_false_of_dynkin hc.toBr1Base hL hX₀ hX₀n hmem hnc1 hnc2 hrk hne

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
