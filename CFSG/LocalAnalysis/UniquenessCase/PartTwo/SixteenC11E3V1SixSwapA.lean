module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3BCPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H CFSG.Quasithin.H.Pair CFSG.Quasithin.H.PairG CFSG.Quasithin.H.Sp4A6

private theorem s1611e3_isInv_map_congrHom {V W : Type*} [CommGroup V] [CommGroup W]
    (e : V ≃* W) {L : Subgroup (MulAut V)} {I : Subgroup V} (hI : Pair.IsInv L I) :
    Pair.IsInv (L.map (congrHom e)) (I.map e.toMonoidHom) := by
  rintro l hl w ⟨u₀, hu₀, rfl⟩
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  refine ⟨l₀ u₀, hI l₀ hl₀ u₀ hu₀, ?_⟩
  simp [congrHom_apply]

private theorem s1611e3_isIrr_map_congrHom {V W : Type*} [CommGroup V] [CommGroup W]
    (e : V ≃* W) {L : Subgroup (MulAut V)} {I : Subgroup V} (hI : Pair.IsIrr L I) :
    Pair.IsIrr (L.map (congrHom e)) (I.map e.toMonoidHom) := by
  constructor
  · intro h
    exact hI.1 ((Subgroup.map_eq_bot_iff_of_injective I e.injective).1 h)
  · intro U hU hUi
    have hUeq : (U.map e.symm.toMonoidHom).map e.toMonoidHom = U := by
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id W := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    have hU₀I : U.map e.symm.toMonoidHom ≤ I := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 (hU hu)
      simpa using hy
    have hInv₀ : Pair.IsInv L (U.map e.symm.toMonoidHom) := by
      rintro l hl u₀ hu₀
      have heu₀ : e u₀ ∈ U := (Subgroup.mem_map_equiv (f := e.symm)).1 hu₀
      refine (Subgroup.mem_map_equiv (f := e.symm)).2 ?_
      have h1 : congrHom e l (e u₀) ∈ U :=
        hUi (congrHom e l) ⟨l, hl, rfl⟩ (e u₀) heu₀
      rwa [congrHom_apply, MulEquiv.symm_apply_apply] at h1
    rcases hI.2 (U.map e.symm.toMonoidHom) hU₀I hInv₀ with h | h
    · left
      rw [← hUeq, h, Subgroup.map_bot]
    · right
      rw [← hUeq, h]

private theorem s1611e3_map_V₂_swapAut :
    (V₂ (Fin 2 ⊕ Fin 2) (ZMod 2)).map (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2)).toMonoidHom =
      V₁ (Fin 2 ⊕ Fin 2) (ZMod 2) := by
  rw [← map_V₁_swapAut (ι := Fin 2 ⊕ Fin 2) (K := ZMod 2), Subgroup.map_map]
  have hcomp : (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2)).toMonoidHom.comp
      (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2)).toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun _ => rfl
  rw [hcomp, Subgroup.map_id]

theorem s1611e3_six_swap_aut {W' : Type} [CommGroup W']
    {L' : Subgroup (MulAut W')} {I₁ I₂ : Subgroup W'} (hinf : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = ⊤)
    (h₁ : AlternatingNatural L' I₁ ⊥ 6) (h₂ : AlternatingNatural L' I₂ ⊥ 6)
    (hne : ∀ ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')), I₁.map ψ.toMonoidHom ≠ I₂) :
    ∃ ψ : MulAut W', (∀ ℓ ∈ L', ψ * ℓ * ψ⁻¹ ∈ L') ∧ I₁.map ψ.toMonoidHom = I₂ := by
  classical
  obtain ⟨e, he⟩ := s16t_exists_pair_model hinf hsup h₁ h₂ hne
  haveI : Finite W' := Finite.of_equiv (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2)) e.toEquiv.symm
  have hIrr₁ : I₁ ∈ irrSet L' := s16c167_mem_irrSet_alt (n := 6) (by norm_num) h₁
  have hIrr₂ : I₂ ∈ irrSet L' := s16c167_mem_irrSet_alt (n := 6) (by norm_num) h₂
  have hfix₁ : I₁ ⊓ fixV L' = ⊥ := s16c167_cfg2_fix_alt (n := 6) (by norm_num) h₁
  have hfix₂ : I₂ ⊓ fixV L' = ⊥ := s16c167_cfg2_fix_alt (n := 6) (by norm_num) h₂
  have hIrrOn₁ : IsIrrOn L' I₁ ⊥ := hfix₁ ▸ hIrr₁.2
  have hIrrOn₂ : IsIrrOn L' I₂ ⊥ := hfix₂ ▸ hIrr₂.2
  have hInv₁ : Pair.IsInv L' I₁ := hIrrOn₁.2.1
  have hInv₂ : Pair.IsInv L' I₂ := hIrrOn₂.2.1
  have hIrrL₁ : Pair.IsIrr L' I₁ :=
    ⟨hIrrOn₁.1.ne', fun U hU hUi => hIrrOn₁.2.2.2 U hUi bot_le hU⟩
  have hIrrL₂ : Pair.IsIrr L' I₂ :=
    ⟨hIrrOn₂.1.ne', fun U hU hUi => hIrrOn₂.2.2.2 U hUi bot_le hU⟩
  have hIrrJ₁ : Pair.IsIrr (pairImg Γ₆ tau₆) (I₁.map e.toMonoidHom) :=
    he ▸ s1611e3_isIrr_map_congrHom e hIrrL₁
  have hIrrJ₂ : Pair.IsIrr (pairImg Γ₆ tau₆) (I₂.map e.toMonoidHom) :=
    he ▸ s1611e3_isIrr_map_congrHom e hIrrL₂
  have hInvJ₁ : Pair.IsInv (pairImg Γ₆ tau₆) (I₁.map e.toMonoidHom) :=
    he ▸ s1611e3_isInv_map_congrHom e hInv₁
  have hInvJ₂ : Pair.IsInv (pairImg Γ₆ tau₆) (I₂.map e.toMonoidHom) :=
    he ▸ s1611e3_isInv_map_congrHom e hInv₂
  have hJ₁ : I₁.map e.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) (ZMod 2) ∨
      I₁.map e.toMonoidHom = V₂ (Fin 2 ⊕ Fin 2) (ZMod 2) :=
    Pair.eq_or_eq_of_isIrr (V₁_inf_V₂ (ι := Fin 2 ⊕ Fin 2) (K := ZMod 2))
      (V₁_sup_V₂ (ι := Fin 2 ⊕ Fin 2) (K := ZMod 2))
      (isInv_V₁ (Γ := Γ₆) (θ := tau₆)) (isInv_V₂ (Γ := Γ₆) (θ := tau₆))
      (isIrr_V₁ (Γ := Γ₆) (θ := tau₆) isNatIrr)
      (isIrr_V₂ (Γ := Γ₆) (θ := tau₆) isNatIrr tau₆_surjective)
      not_isoMod hInvJ₁ hIrrJ₁
  have hJ₂ : I₂.map e.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) (ZMod 2) ∨
      I₂.map e.toMonoidHom = V₂ (Fin 2 ⊕ Fin 2) (ZMod 2) :=
    Pair.eq_or_eq_of_isIrr (V₁_inf_V₂ (ι := Fin 2 ⊕ Fin 2) (K := ZMod 2))
      (V₁_sup_V₂ (ι := Fin 2 ⊕ Fin 2) (K := ZMod 2))
      (isInv_V₁ (Γ := Γ₆) (θ := tau₆)) (isInv_V₂ (Γ := Γ₆) (θ := tau₆))
      (isIrr_V₁ (Γ := Γ₆) (θ := tau₆) isNatIrr)
      (isIrr_V₂ (Γ := Γ₆) (θ := tau₆) isNatIrr tau₆_surjective)
      not_isoMod hInvJ₂ hIrrJ₂
  let s : MulAut (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2)) := swapAut (Fin 2 ⊕ Fin 2) (ZMod 2)
  let ψ : MulAut W' := (MulAut.congr e).symm s
  have hψc : congrHom e ψ = s := (MulAut.congr e).apply_symm_apply s
  refine ⟨ψ, ?_, ?_⟩
  · intro ℓ hℓ
    have hs : s ∈ pairNorm Γ₆ tau₆ := swapAut_mem_pairNorm tau₆ tau₆_tau₆
    have hℓmem : congrHom e ℓ ∈ pairImg Γ₆ tau₆ := by
      rw [← he]
      exact ⟨ℓ, hℓ, rfl⟩
    have hmem : congrHom e (ψ * ℓ * ψ⁻¹) ∈ pairImg Γ₆ tau₆ := by
      rw [map_mul, map_mul, map_inv, hψc]
      exact (Subgroup.mem_normalizer_iff.mp hs (congrHom e ℓ)).mp hℓmem
    rw [← Subgroup.comap_map_eq_self_of_injective (congrHom_injective e) L', he]
    exact Subgroup.mem_comap.2 hmem
  · have hJne : I₁.map e.toMonoidHom ≠ I₂.map e.toMonoidHom := by
      intro h
      have hI : I₁ = I₂ := Subgroup.map_injective e.injective h
      have hbot : I₁ = ⊥ := by rw [← hinf, hI, inf_idem]
      exact hIrrL₁.1 hbot
    have hsmap : (I₁.map e.toMonoidHom).map s.toMonoidHom = I₂.map e.toMonoidHom := by
      rcases hJ₁ with h | h <;> rcases hJ₂ with h' | h'
      · exact absurd (h.trans h'.symm) hJne
      · rw [h, h']
        exact map_V₁_swapAut
      · rw [h, h']
        exact s1611e3_map_V₂_swapAut
      · exact absurd (h.trans h'.symm) hJne
    have hcomp : s.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp ψ.toMonoidHom := by
      refine MonoidHom.ext fun v => ?_
      change s (e v) = e (ψ v)
      have hψapp : ψ v = e.symm (s (e v)) := rfl
      rw [hψapp, MulEquiv.apply_symm_apply]
    have hgoal : (I₁.map ψ.toMonoidHom).map e.toMonoidHom = I₂.map e.toMonoidHom := by
      rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, hsmap]
    exact Subgroup.map_injective e.injective hgoal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
