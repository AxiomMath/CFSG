module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3SideB
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fin
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W183K3InnerFour
public import CFSG.LocalAnalysis.WeakClosure81.W183K3InnerMem
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

private theorem w183k3_eight_le_card_of_three_le_mRank {A : Subgroup (LGL 2 V)}
    (h : 3 ≤ mRank A) : 8 ≤ Nat.card A := by
  haveI : Nonempty ↥A := (OneMemClass.coe_nonempty A).to_subtype
  have hlog : 3 ≤ Nat.log 2 (Nat.card A) := by simpa only [mRank] using h
  have hpow : 2 ^ 3 ≤ Nat.card A := Nat.pow_le_of_le_log Nat.card_pos.ne' hlog
  simpa using hpow

theorem w183k3_false_of_swap (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br3TwoComp Y T L₁ L₂)
    {X₀ : Subgroup (MulAut (↥L₁ ⧸ Subgroup.center ↥L₁))}
    (hX₀ : X₀ ≤ (psiQuot (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁
      hL.core₁.normal).range)
    (hX₀n : ∀ r : ↥(Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))), ∀ x ∈ X₀,
      psiQuot (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁ hL.core₁.normal r * x *
        (psiQuot (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁ hL.core₁.normal r)⁻¹ ∈ X₀)
    (hmem : ∀ D ∈ Γ, D ≤ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) →
      imgOf (psiQuot (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁ hL.core₁.normal) D ≤ X₀)
    (hnc : Br2NormalConj (↥L₁ ⧸ Subgroup.center ↥L₁) X₀)
    (hone : ∀ D ∈ Γ, D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
      D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty) : False := by
  classical
  let X₁ : Subgroup (LGL 2 V) := Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))
  let X₂ : Subgroup (LGL 2 V) := Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))
  let ψ : ↥X₁ →* MulAut (↥L₁ ⧸ Subgroup.center ↥L₁) := psiQuot X₁ L₁ hL.core₁.normal
  have hTY : T ≤ Y := hc.sylow.le
  have hSyl : IsSylowIn 2 (T ⊓ X₁) X₁ := w183two_isSylowIn_inf_X₁ hc.sylow hL.toBase
  obtain ⟨D₀, hD₀mem, hD₀X₁⟩ := w183two_exists_type_one hc.h131 hTY hL.toBase hone hne
  have hD₀card : 8 ≤ Nat.card D₀ :=
    w183k3_eight_le_card_of_three_le_mRank (hrk D₀ hD₀mem)
  obtain ⟨D, hDmem, hDT, -, -, -, hgen⟩ :=
    w183k3_exists_normal_member (R := X₁) (L := L₁) (T := T)
      hc.h131 inf_le_left hL.core₁ hSyl hX₀ hX₀n hnc hD₀mem hD₀X₁
      (hmem D₀ hD₀mem hD₀X₁) hD₀card
  have hDX₁ : D ≤ X₁ := hDT.trans inf_le_right
  have hDT' : D ≤ T := hDT.trans inf_le_left
  have hgenN : ∀ B ∈ 𝒢, B ≤ Subgroup.normalizer (D : Set (LGL 2 V)) := by
    intro B hB
    obtain ⟨hBT, D', hD'mem, hBD', -⟩ := hc.gens B hB
    have hD'le : D' ≤ Y := hc.h131.le_G D' hD'mem
    rcases hone D' hD'mem with hD'C₁ | hD'C₂
    · have hBX₂ : B ≤ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
        le_inf (hBT.trans hTY) (hBD'.trans hD'C₁)
      refine w183two_le_normalizer_of_comm ?_
      intro b hb d hd
      have hb2 : b * b = 1 := (hc.h131.isElemAb D' hD'mem).mul_self_eq_one (hBD' hb)
      have hd2 : d * d = 1 := (hc.h131.isElemAb D hDmem).mul_self_eq_one hd
      exact (hL.comm_X_of_sq_eq_one (hDX₁ hd) (hBX₂ hb) hd2 hb2).symm
    · have hD'X₁ : D' ≤ X₁ := le_inf hD'le hD'C₂
      have hBinf : B ≤ T ⊓ X₁ := le_inf hBT (hBD'.trans hD'X₁)
      have himg : imgOf ψ B ≤ X₀ := (imgOf_mono ψ hBD').trans (hmem D' hD'mem hD'X₁)
      exact hgen B hBinf himg
  have hTne : T ≠ Y := by
    intro hTYeq
    have hP := hSyl.isPGroup
    rw [hTYeq, inf_eq_right.2 inf_le_left] at hP
    exact hL.core₁.not_isPGroup hP
  have hTN : T ≤ Subgroup.normalizer (D : Set (LGL 2 V)) :=
    hc.weakClosure D hDmem hDT' hgenN T hTY le_rfl hTne
  obtain ⟨x, hxT, hxL⟩ := hL.swap
  have hxD : cj x D = D := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN hxT)
  have hxX₂ : cj x D ≤ X₂ := by
    have h : cj x D ≤ cj x X₁ := Subgroup.map_mono hDX₁
    rwa [hL.cj_X hTY hxT hxL] at h
  have hDX₂ : D ≤ X₂ := hxD ▸ hxX₂
  have hleK : D ≤ quasiCentre L₁ ⊔ quasiCentre L₂ :=
    (le_inf hDX₁ hDX₂).trans hL.inf_X_le
  have hD2 : IsPGroup 2 D := (hc.h131.isElemAb D hDmem).isPGroup
  have hDle : D ≤ (⊥ : Subgroup (LGL 2 V)) := by
    have h1 : D ≤ D ⊓ (quasiCentre L₁ ⊔ quasiCentre L₂) := le_inf le_rfl hleK
    rwa [isPGroup_inf_odd_eq_bot hD2 hL.odd_kStar] at h1
  exact hc.h131.ne_bot D hDmem (le_bot_iff.mp hDle)

theorem br3_false_of_one_sided (rows : Br3Rows) (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br3TwoComp Y T L₁ L₂)
    (_hmem : ∀ D ∈ Γ, D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hone : ∀ D ∈ Γ, D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
      D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty)
    (hshape : IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 ∨ IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6) :
    False := by
  classical
  rcases hshape with h | h
  · refine w183k3_false_of_swap hc.toBr1Base hL
      (X₀ := innAutOf (↥L₁ ⧸ Subgroup.center ↥L₁)) ?_ ?_ ?_ ?_ hone hrk hne
    · rw [← hL.core₁.imgOf_psiQuot_L]
      exact imgOf_le_range _ L₁
    · intro r x hx
      exact psiQuot_conj_mem_innAutOf hL.core₁ r hx
    · intro D hD hDX
      exact w183k3_inner_of_quadratic rows.h65f hL.core₁ h hDX
        (hc.h131.isElemAb D hD) (hc.h131.quadratic D hD) (hrk D hD)
    · exact (rows.g4l34 (↥L₁ ⧸ Subgroup.center ↥L₁) h).1
  · let X₁ : Subgroup (LGL 2 V) := Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))
    obtain ⟨hnorm, hall, hgen, hnc, -⟩ :=
      rows.g4a6 (↥L₁ ⧸ Subgroup.center ↥L₁) h
    obtain ⟨D₀, hD₀mem, hD₀X₁⟩ :=
      w183two_exists_type_one hc.h131 hc.sylow.le hL.toBase hone hne
    let ψ : ↥X₁ →* MulAut (↥L₁ ⧸ Subgroup.center ↥L₁) := psiQuot X₁ L₁ hL.core₁.normal
    have hD₀Ae : IsElemAbelian 2 (imgOf ψ D₀) := by
      rw [imgOf]
      exact IsElemAbelian.map (IsElemAbelian.subgroupOf (hc.h131.isElemAb D₀ hD₀mem) X₁) ψ
    have hD₀card : 8 ≤ Nat.card (imgOf ψ D₀) := by
      rw [hL.core₁.card_imgOf_psiQuot hD₀X₁ (hc.h131.isElemAb D₀ hD₀mem).isPGroup]
      exact w183k3_eight_le_card_of_three_le_mRank (hrk D₀ hD₀mem)
    have hX₀ : autNoDynkin (↥L₁ ⧸ Subgroup.center ↥L₁) ≤ ψ.range := by
      rw [← hgen (imgOf ψ D₀) hD₀Ae hD₀card]
      refine sup_le ?_ (imgOf_le_range ψ D₀)
      rw [← hL.core₁.imgOf_psiQuot_L]
      exact imgOf_le_range ψ L₁
    have hX₀n : ∀ r : ↥X₁, ∀ x ∈ autNoDynkin (↥L₁ ⧸ Subgroup.center ↥L₁),
        ψ r * x * (ψ r)⁻¹ ∈ autNoDynkin (↥L₁ ⧸ Subgroup.center ↥L₁) :=
      fun r x hx => hnorm.conj_mem x hx (ψ r)
    have hmem : ∀ D ∈ Γ, D ≤ X₁ →
        imgOf ψ D ≤ autNoDynkin (↥L₁ ⧸ Subgroup.center ↥L₁) := by
      intro D hD hDX
      refine hall (imgOf ψ D) ?_ ?_
      · rw [imgOf]
        exact IsElemAbelian.map (IsElemAbelian.subgroupOf (hc.h131.isElemAb D hD) X₁) ψ
      · rw [hL.core₁.card_imgOf_psiQuot hDX (hc.h131.isElemAb D hD).isPGroup]
        exact w183k3_eight_le_card_of_three_le_mRank (hrk D hD)
    exact w183k3_false_of_swap hc.toBr1Base hL hX₀ hX₀n hmem hnc hone hrk hne

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
