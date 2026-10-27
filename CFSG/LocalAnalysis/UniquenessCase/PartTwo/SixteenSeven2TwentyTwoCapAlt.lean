module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltSwap
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c167_transv_unique_alt {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {E : Subgroup W} {n : ℕ} (hn : 5 ≤ n)
    (hE : AlternatingNatural L E ⊥ n) {x y : MulAut W}
    (hxL : L.map (MulAut.conj x).toMonoidHom = L) (hyL : L.map (MulAut.conj y).toMonoidHom = L)
    (hxE : E.map x.toMonoidHom = E) (hyE : E.map y.toMonoidHom = E)
    {H : Subgroup W} (hHE : H ≤ E) (hH : E3.mQuot E H = 1)
    (hxH : ∀ e ∈ H, x e = e) (hyH : ∀ e ∈ H, y e = e)
    (hxT : ∀ e ∈ E, x e * e⁻¹ ∈ H) (hyT : ∀ e ∈ E, y e * e⁻¹ ∈ H) :
    (∀ e ∈ E, x e = e) ∨ (∀ e ∈ E, y e = e) ∨ (∀ e ∈ E, x e = y e) := by
  obtain ⟨π, ψ, hπ, hψ⟩ := s16c167_altNatural_equiv (by omega : 0 < n) hE
  obtain ⟨K, hKi, hK⟩ := s16c167_exists_hyperplane hW hH ψ
  have hLE : ∀ g : ↥L, ∀ e ∈ E, (g : MulAut W) e ∈ E := by
    obtain ⟨_, h⟩ := hE
    exact h.2.2.2.1
  obtain ⟨tx, hxe, hxn, hxK, hxK'⟩ :=
    s16c167_altNatural_transvection hπ hψ hLE hxL hxE hK hxH hxT
  obtain ⟨ty, hye, hyn, hyK, hyK'⟩ :=
    s16c167_altNatural_transvection hπ hψ hLE hyL hyE hK hyH hyT
  have hxmem : ∀ e ∈ E, x e ∈ E := fun e he => by
    rw [← hxE]; exact Subgroup.mem_map.2 ⟨e, he, rfl⟩
  have hymem : ∀ e ∈ E, y e ∈ E := fun e he => by
    rw [← hyE]; exact Subgroup.mem_map.2 ⟨e, he, rfl⟩
  by_cases hx1 : tx = AddEquiv.refl _
  · left
    intro e he
    have h := hxe e he (hxmem e he)
    rw [hx1] at h
    exact congrArg Subtype.val (ψ.injective (Multiplicative.toAdd.injective h))
  by_cases hy1 : ty = AddEquiv.refl _
  · right; left
    intro e he
    have h := hye e he (hymem e he)
    rw [hy1] at h
    exact congrArg Subtype.val (ψ.injective (Multiplicative.toAdd.injective h))
  right; right
  obtain ⟨σx, hσx, htx, hfx⟩ :=
    s16c167_altHeart_transvection_eq_swap hn tx hxn hKi hxK hxK' hx1
  obtain ⟨σy, hσy, hty, hfy⟩ :=
    s16c167_altHeart_transvection_eq_swap hn ty hyn hKi hyK hyK' hy1
  have hσ : σx = σy := s16c167_swap_eq_of_altAct_fixed_iff hn hσx hσy fun v =>
    (hfx v).trans (hfy v).symm
  subst hσ
  intro e he
  have h1 := hxe e he (hxmem e he)
  have h2 := hye e he (hymem e he)
  rw [htx] at h1
  rw [hty] at h2
  exact congrArg Subtype.val (ψ.injective (Multiplicative.toAdd.injective (h1.trans h2.symm)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
