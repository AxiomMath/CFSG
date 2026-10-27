module

public import CFSG.LocalAnalysis.WeakClosure81.W16LBDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem w16l_comap_fusionOddCore_eq {X Y : Type} [Group X] [Finite X]
    [Group Y] [Finite Y] (ψ : X →* Y) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) :
    (fusionOddCore Y).comap ψ = fusionOddCore X := by
  let H : Subgroup X := (fusionOddCore Y).comap ψ
  haveI hHnormal : H.Normal := by
    dsimp [H]; infer_instance
  have hHodd : Odd (Nat.card H) := by
    let f : ↥H →* Y := ψ.comp H.subtype
    have hrange : f.range = fusionOddCore Y := by
      dsimp [f, H]
      rw [MonoidHom.range_comp, Subgroup.range_subtype,
        Subgroup.map_comap_eq_self_of_surjective hψ]
    have hkerleH : ψ.ker ≤ H := by
      intro x hx
      exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hx]; exact one_mem _)
    have hker : Nat.card f.ker = Nat.card ψ.ker := by
      have h1 : f.ker = (ψ.ker).subgroupOf H := by
        ext x
        rfl
      rw [h1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerleH).toEquiv
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hrange, hker] at hcard
    rw [← hcard]
    exact hodd.mul (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y)
  have hHle : H ≤ fusionOddCore X :=
    CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hHodd
  have hOle : fusionOddCore X ≤ H := by
    haveI : ((fusionOddCore X).map ψ).Normal :=
      Subgroup.Normal.map inferInstance ψ hψ
    have hodd' : Odd (Nat.card ((fusionOddCore X).map ψ)) :=
      Odd.of_dvd_nat (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore X)
        (Subgroup.card_map_dvd (fusionOddCore X) ψ)
    have hle := CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore
      (N := (fusionOddCore X).map ψ) hodd'
    intro x hx
    exact Subgroup.mem_comap.mpr (hle (Subgroup.mem_map_of_mem ψ hx))
  exact le_antisymm hHle hOle

theorem w16l_isSymGp_quot_fusionOddCore_of_odd_ker {X Y : Type} [Group X] [Finite X]
    [Group Y] [Finite Y] (ψ : X →* Y) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) {m : ℕ} (h : IsSymGp (X ⧸ fusionOddCore X) m) :
    IsSymGp (Y ⧸ fusionOddCore Y) m := by
  have hHeq := w16l_comap_fusionOddCore_eq ψ hψ hodd
  let π : X →* Y ⧸ fusionOddCore Y := (QuotientGroup.mk' (fusionOddCore Y)).comp ψ
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective (fusionOddCore Y)).comp hψ
  have hπker : π.ker = fusionOddCore X := by
    change (QuotientGroup.mk' (fusionOddCore Y)).ker.comap ψ = fusionOddCore X
    rw [QuotientGroup.ker_mk']
    exact hHeq
  obtain ⟨e'⟩ := h
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hπker).trans e')⟩

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G} {X : Type} [Group X]
  {φ : ↥(kGenIn V H) →* X}

theorem ShapeData.kBarOddQuotShape (d : ShapeData V H T φ) {m : ℕ}
    (h : IsSymGp (X ⧸ fusionOddCore X) m) :
    KBarOddQuotShape V H T (fun Y _ => IsSymGp Y m) := by
  haveI : Finite X := d.finite
  obtain ⟨Y, hYgrp, φ₀, ψ, hbar, hψsurj, _hcomp, hψker⟩ :=
    exists_central_quotient d.hyp83 d.eq_sup d.bar
  letI := hYgrp
  haveI : Finite Y := Finite.of_surjective φ₀ hbar.surjective
  have hoddψ : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat d.odd_card_center (Subgroup.card_dvd_of_le hψker)
  exact ⟨Y, hYgrp, φ₀, hbar,
    w16l_isSymGp_quot_fusionOddCore_of_odd_ker ψ hψsurj hoddψ h⟩

theorem ShapeData.noHyp85 (d : ShapeData V H T φ) (h : ¬ Hyp85Three' V H T) :
    NoHyp85 X (barSub (kGenIn V H) φ V) := by
  haveI : Finite X := d.finite
  have hc := Hyp83.card_barSub_eq_two_pow_rankBarV d.hyp83 d.eq_sup d.bar
  unfold NoHyp85
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨m, n, hm, hSp, hcard⟩
    exact h (Or.inl ⟨m, n, hm, d.kBarCenterShape (P := fun Y _ => IsSpGp Y m n) hSp,
      Nat.pow_right_injective (le_refl 2) (hc.symm.trans hcard)⟩)
  · rintro ⟨m, n, hm, hSp, hcard⟩
    exact h (Or.inr (Or.inl ⟨m, n, hm,
      d.kBarCenterShape (P := fun Y _ => IsPSUGp Y m n) hSp,
      Nat.pow_right_injective (le_refl 2) (hc.symm.trans hcard)⟩))
  · rintro ⟨k, hk, hsym⟩
    exact h (Or.inr (Or.inr ⟨k, hk, d.kBarOddQuotShape hsym⟩))

end CFSG.LocalAnalysis.WeakClosure81

end
