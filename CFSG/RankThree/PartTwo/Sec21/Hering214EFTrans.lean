module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EThmA

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG.Assembly (IsElemAbelian)

section Transport

variable {X Y : Type} [Group X] [Group Y]

private theorem evenTheta_congr_conj (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem evenTheta_congr_mem_range (e : X ≃* Y) (σ : MulAut X) :
    σ ∈ (MulAut.conj : X →* MulAut X).range ↔
      MulAut.congr e σ ∈ (MulAut.conj : Y →* MulAut Y).range := by
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, (evenTheta_congr_conj e x).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply (MulAut.congr e).injective
    rw [← hy, evenTheta_congr_conj, MulEquiv.apply_symm_apply]

private theorem evenTheta_map_range_le (e : X ≃* Y) {K : Subgroup (MulAut X)}
    (hK : K ≤ (MulAut.conj : X →* MulAut X).range) :
    K.map (MulAut.congr e).toMonoidHom ≤ (MulAut.conj : Y →* MulAut Y).range := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact (evenTheta_congr_mem_range e σ).mp (hK hσ)

private theorem evenTheta_map_range_eq (e : X ≃* Y) :
    ((MulAut.conj : X →* MulAut X).range).map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : Y →* MulAut Y).range := by
  refine le_antisymm (evenTheta_map_range_le e le_rfl) ?_
  rintro τ ⟨y, rfl⟩
  refine Subgroup.mem_map.mpr ⟨MulAut.conj (e.symm y),
    MonoidHom.mem_range.mpr ⟨e.symm y, rfl⟩, ?_⟩
  show MulAut.congr e (MulAut.conj (e.symm y)) = MulAut.conj y
  rw [evenTheta_congr_conj, MulEquiv.apply_symm_apply]

private theorem evenTheta_map_centralizer (e : X ≃* Y) (S : Subgroup (MulAut X)) :
    (Subgroup.centralizer (S : Set (MulAut X))).map (MulAut.congr e).toMonoidHom =
      Subgroup.centralizer
        ((S.map (MulAut.congr e).toMonoidHom : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
  ext τ
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨σ, hσ, rfl⟩ s' hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hσ s hs]
  · intro hτ
    refine ⟨(MulAut.congr e).symm τ, ?_, (MulAut.congr e).apply_symm_apply τ⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hτ _ (Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hs)

private theorem evenTheta_map_D (e : X ≃* Y) (U : Subgroup (MulAut X)) :
    ((MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (U : Set (MulAut X))).map
        (MulAut.congr e).toMonoidHom =
      (MulAut.conj : Y →* MulAut Y).range ⊓
        Subgroup.centralizer ((U.map (MulAut.congr e).toMonoidHom : Subgroup (MulAut Y)) :
          Set (MulAut Y)) := by
  rw [Subgroup.map_inf_eq _ _ (MulAut.congr e).toMonoidHom (MulAut.congr e).injective,
    evenTheta_map_range_eq, evenTheta_map_centralizer]

private theorem evenTheta_isElemAbelian_map {A B : Type} [Group A] [Group B] {p : ℕ}
    {K : Subgroup A} (hK : IsElemAbelian p K) (f : A →* B) :
    IsElemAbelian p (K.map f) := by
  obtain ⟨hc, hp⟩ := hK
  refine ⟨?_, ?_⟩
  · haveI := hc
    infer_instance
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hp x hx, map_one]

end Transport

theorem evenThetaFacts_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : EvenThetaFacts Y) : EvenThetaFacts X := by
  unfold EvenThetaFacts at h ⊢
  obtain ⟨hZ, hInv, ⟨Q', hQ', hQ'9⟩, hY⟩ := h
  have hψ : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have eInj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    have hxe : e x ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hx g']
    rw [hZ, Subgroup.mem_bot] at hxe
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hxe, map_one])
  ·
    intro σ hσ
    have hσ' : MulAut.congr e σ ^ 3 = 1 := by
      rw [← map_pow, hσ, map_one]
    exact (evenTheta_congr_mem_range e σ).mpr (hInv _ hσ')
  ·
    refine ⟨Q'.map e.symm.toMonoidHom, evenTheta_isElemAbelian_map hQ' _, ?_⟩
    rw [Subgroup.card_map_of_injective eInj, hQ'9]
  ·
    intro Ē Ū hĒI hĒab hĒ9 hŪab hŪne hŪ4 hcomm
    have hĒI' := evenTheta_map_range_le e hĒI
    have hĒab' := evenTheta_isElemAbelian_map hĒab (MulAut.congr e).toMonoidHom
    have hĒ9' : Nat.card (Ē.map (MulAut.congr e).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective hψ, hĒ9]
    have hŪab' := evenTheta_isElemAbelian_map hŪab (MulAut.congr e).toMonoidHom
    have hŪne' : Ū.map (MulAut.congr e).toMonoidHom ≠ ⊥ := by
      intro h0
      apply hŪne
      apply Subgroup.map_injective hψ
      rw [h0, Subgroup.map_bot]
    have hŪ4' : Nat.card (Ū.map (MulAut.congr e).toMonoidHom) ≤ 4 := by
      rw [Subgroup.card_map_of_injective hψ]
      exact hŪ4
    have hcomm' : ∀ u ∈ Ū.map (MulAut.congr e).toMonoidHom,
        ∀ k ∈ Ē.map (MulAut.congr e).toMonoidHom, u * k = k * u := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, hcomm u hu k hk]
    obtain ⟨hED, hO2⟩ := hY _ _ hĒI' hĒab' hĒ9' hŪab' hŪne' hŪ4' hcomm'
    refine ⟨?_, ?_⟩
    · rw [← evenTheta_map_D e Ū, ← Subgroup.map_commutator] at hED
      exact (Subgroup.map_le_map_iff_of_injective hψ).mp hED
    · intro P hP hPD hN
      apply Subgroup.map_injective hψ
      rw [Subgroup.map_bot]
      refine hO2 (P.map (MulAut.congr e).toMonoidHom) (hP.map _) ?_ ?_
      · rw [← evenTheta_map_D e Ū, ← Subgroup.map_commutator]
        exact Subgroup.map_mono hPD
      · rw [← evenTheta_map_D e Ū, ← Subgroup.map_commutator]
        exact (Subgroup.map_mono (f := (MulAut.congr e).toMonoidHom) hN).trans
          (Subgroup.map_equiv_normalizer_eq P (MulAut.congr e)).le

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
