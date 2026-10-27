module

public import CFSG.GH74.GLS.C3.Layer1.BkA6K
public import CFSG.GH74.GLS.C3.Layer1.BkL27K

public section

namespace CFSG.Quasithin.RonanE68

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.C3.Layer1.Bk

theorem involution_cases_L2_nine' {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (hF9 : Nat.card F = 9) {H : Type} [Group H] [Finite H] (e : H ≃* L2 F)
    (Sig : Subgroup (MulAut H)) (hInn : innAut H ≤ Sig)
    (hf : ∀ f ∈ fieldAutSub e, orderOf f = 2 → f ∈ Sig)
    {ρ : MulAut H} (hρ2 : ρ ^ 2 = 1) :
    ρ ∈ Sig ∨ Nat.card ↥(fixedSubgroup H ρ) = 10 := by
  by_cases hdiag : ρ ∈ innDiagSub e
  · by_cases hin : ρ ∈ innAut H
    · exact Or.inl (hInn hin)
    · have hρ1 : ρ ≠ 1 := fun h => hin (h ▸ Subgroup.one_mem _)
      have hord : orderOf ρ = 2 := orderOf_eq_prime hρ2 hρ1
      exact Or.inr (card_fixedSubgroup_of_outer_nine hF hF9 e hdiag hin hord)
  · left
    obtain ⟨c, hc, g, hg, hg2, rfl⟩ := decomp_of_not_innDiag hF hF9 e hdiag hρ2
    exact Sig.mul_mem (hInn hc) (hf g hg hg2)

theorem alt6_involution_cases' {H : Type} [Group H] [Finite H] (e : H ≃* alternatingGroup (Fin 6))
    {ρ : MulAut H} (hρ2 : ρ ^ 2 = 1) :
    (∃ σ : Equiv.Perm (Fin 6),
        MulAut.congr e ρ = MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ) ∨
      Nat.card ↥(fixedSubgroup H ρ) = 10 := by
  obtain ⟨F, _, _, e', hF9⟩ := exists_L2_nine_equiv e
  have hF : L2Field F := ⟨by rw [hF9]; decide, by rw [hF9]; norm_num⟩
  let SigH : Subgroup (MulAut H) :=
    (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.comap
      (MulAut.congr e).toMonoidHom
  have hmem : ∀ φ : MulAut H, φ ∈ SigH ↔ ∃ σ : Equiv.Perm (Fin 6),
      MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ = MulAut.congr e φ := fun φ => Iff.rfl
  have hconjcongr : ∀ h : H, MulAut.congr e (MulAut.conj h) = MulAut.conj (e h) := by
    intro h
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hInn : innAut H ≤ SigH := by
    rintro _ ⟨h, rfl⟩
    refine (hmem _).2 ⟨((e h : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)), ?_⟩
    rw [MulAut.conjNormal_val, hconjcongr]
  have hf : ∀ f ∈ fieldAutSub e', orderOf f = 2 → f ∈ SigH := by
    intro f hfF hf2
    let sH : MulAut H := (MulAut.congr e).symm swapAut
    have hcs : MulAut.congr e sH = swapAut := MulEquiv.apply_symm_apply _ _
    have hsH_mem : sH ∈ SigH := (hmem _).2 ⟨_, by rw [hcs]; rfl⟩
    have hsH2 : sH ^ 2 = 1 := by
      show ((MulAut.congr e).symm swapAut) ^ 2 = 1
      rw [← map_pow, swapAut_sq, map_one]
    have hsH1 : sH ≠ 1 := by
      intro h1
      have : swapAut = 1 := by rw [← hcs, h1, map_one]
      exact swapAut_not_inner ⟨1, by simpa using this.symm⟩
    have hsH_inn : sH ∉ innAut H := by
      rintro ⟨h, hh⟩
      apply swapAut_not_inner
      refine ⟨e h, ?_⟩
      rw [← hcs, ← hh, hconjcongr]
    have hsH_diag : sH ∉ innDiagSub e' := by
      intro hd
      have hord : orderOf sH = 2 := orderOf_eq_prime hsH2 hsH1
      have hcard := card_fixedSubgroup_of_outer_nine hF hF9 e' hd hsH_inn hord
      obtain ⟨g, hg4, hgfix⟩ := exists_order_four_fixed
      have hfix := Stage1.Thm3.Sec5.fixedSubgroup_congr e sH
      have hgmem : g ∈ fixedSubgroup (alternatingGroup (Fin 6)) (MulAut.congr e sH) := by
        rw [hcs]
        exact hgfix
      rw [hfix] at hgmem
      obtain ⟨g', hg', hg'e⟩ := hgmem
      have hg'4 : orderOf g' = 4 := by
        rw [← hg4, ← hg'e]
        exact (MulEquiv.orderOf_eq e g').symm
      have hdvd : orderOf (⟨g', hg'⟩ : ↥(fixedSubgroup H sH)) ∣ Nat.card ↥(fixedSubgroup H sH) :=
        orderOf_dvd_natCard _
      rw [hcard, Subgroup.orderOf_mk, hg'4] at hdvd
      omega
    obtain ⟨c, hc, g, hg, hg2, hsHeq⟩ := decomp_of_not_innDiag hF hF9 e' hsH_diag hsH2
    have hgS : g ∈ SigH := by
      have : g = c⁻¹ * sH := by rw [hsHeq]; group
      rw [this]
      exact SigH.mul_mem (SigH.inv_mem (hInn hc)) hsH_mem
    have hF2 := card_fieldAutSub_nine hF hF9 e'
    rw [eq_of_orderOf_two_of_card_two hF2 hg hfF hg2 hf2]
    exact hgS
  rcases involution_cases_L2_nine' hF hF9 e' SigH hInn hf hρ2 with h | h
  · obtain ⟨σ, hσ⟩ := (hmem ρ).1 h
    exact Or.inl ⟨σ, hσ.symm⟩
  · exact Or.inr h

end CFSG.Quasithin.RonanE68
