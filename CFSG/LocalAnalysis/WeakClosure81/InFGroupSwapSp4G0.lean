module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver)

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

private theorem isMaxParabolicOver_map_conj (h : Setting L T P₀ P₁ n w) {x : Q} (hx : x ∈ T)
    {P : Subgroup Q} (hP : IsMaxParabolicOver L (T ⊓ L) P) :
    IsMaxParabolicOver L (T ⊓ L) (P.map (MulAut.conj x).toMonoidHom) := by
  haveI hLnorm : L.Normal := h.normal
  set f : Q →* Q := (MulAut.conj x).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj x).injective
  have hLmap : L.map f = L := Subgroup.Normal.map_conj_eq L x
  have hUmap : (T ⊓ L).map f = T ⊓ L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.le_normalizer_inf hx)
  have hNmap : (Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).map f =
      Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
    rw [Subgroup.map_equiv_normalizer_eq, hUmap]
  have hcomapL : Subgroup.comap f L = L := by
    have h := Subgroup.comap_map_eq_self_of_injective hf L
    rwa [hLmap] at h
  have hsurj : Function.Surjective f := (MulAut.conj x).surjective
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hLmap]
    exact Subgroup.map_mono hP.1
  · have h1 : (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).map f =
        L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
      rw [Subgroup.map_inf_eq _ _ f hf, hLmap, hNmap]
    calc L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)
        = (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).map f := h1.symm
      _ ≤ P.map f := Subgroup.map_mono hP.2.1
  · intro hPL
    have h1 : Subgroup.comap f (Subgroup.map f P) = P :=
      Subgroup.comap_map_eq_self_of_injective hf P
    rw [hPL, hcomapL] at h1
    exact hP.2.2.1 h1.symm
  · intro Q' hPQ' hQ'L
    have hcomap_le : Subgroup.comap f Q' ≤ L := by
      intro y hy
      rw [← hcomapL]
      exact hQ'L hy
    have hPle : P ≤ Subgroup.comap f Q' := fun p hp =>
      hPQ' (Subgroup.mem_map_of_mem f hp)
    rcases hP.2.2.2 _ hPle hcomap_le with hEq | hEq
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Q', hEq]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Q', hEq, hLmap]

theorem eq_or_eq_of_isMaxParabolicOver (h : Setting L T P₀ P₁ n w) {P : Subgroup Q}
    (hP : IsMaxParabolicOver L (T ⊓ L) P) : P = P₀ ∨ P = P₁ := by
  have hUP : T ⊓ L ≤ P :=
    (le_inf inf_le_right (Subgroup.le_normalizer (H := T ⊓ L))).trans hP.2.1
  have hPleL : P ≤ L := hP.1
  have hPltL : P < L := lt_of_le_of_ne hPleL hP.2.2.1
  rcases h.le_or_le P hUP hPltL with hle | hle
  · rcases hP.2.2.2 P₀ hle h.par₀.1 with hEq | hEq
    · exact Or.inl hEq.symm
    · exact absurd hEq h.par₀.2.2.1
  · rcases hP.2.2.2 P₁ hle h.par₁.1 with hEq | hEq
    · exact Or.inr hEq.symm
    · exact absurd hEq h.par₁.2.2.1

theorem map_conj_eq_or (h : Setting L T P₀ P₁ n w) {x : Q} (hx : x ∈ T) :
    (P₀.map (MulAut.conj x).toMonoidHom = P₀ ∧ P₁.map (MulAut.conj x).toMonoidHom = P₁) ∨
      (P₀.map (MulAut.conj x).toMonoidHom = P₁ ∧ P₁.map (MulAut.conj x).toMonoidHom = P₀) := by
  have hf : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have h0 := isMaxParabolicOver_map_conj h hx h.par₀
  have h1 := isMaxParabolicOver_map_conj h hx h.par₁
  have hne : P₀.map (MulAut.conj x).toMonoidHom ≠ P₁.map (MulAut.conj x).toMonoidHom :=
    fun he => h.par_ne (Subgroup.map_injective hf he)
  rcases eq_or_eq_of_isMaxParabolicOver h h0 with h0fix | h0swap
  · rcases eq_or_eq_of_isMaxParabolicOver h h1 with h1fix | h1swap
    · exact absurd (h0fix.trans h1fix.symm) hne
    · exact Or.inl ⟨h0fix, h1swap⟩
  · rcases eq_or_eq_of_isMaxParabolicOver h h1 with h1fix | h1swap
    · exact Or.inr ⟨h0swap, h1fix⟩
    · exact absurd (h0swap.trans h1swap.symm) hne

theorem exists_swap (h : Setting L T P₀ P₁ n w) :
    ∃ t ∈ T, P₀.map (MulAut.conj t).toMonoidHom = P₁ := by
  obtain ⟨t, htT, P, hP, hPne⟩ := h.swaps
  have hswap := map_conj_eq_or h htT
  rcases eq_or_eq_of_isMaxParabolicOver h hP with hP₀ | hP₁
  · subst hP₀
    rcases hswap with ⟨hfix, -⟩ | ⟨hsw, -⟩
    · exact absurd hfix hPne
    · exact ⟨t, htT, hsw⟩
  · subst hP₁
    rcases hswap with ⟨-, hfix⟩ | ⟨hsw, -⟩
    · exact absurd hfix hPne
    · exact ⟨t, htT, hsw⟩

theorem perfectCore_sup_perfectCore (h : Setting L T P₀ P₁ n w) :
    perfectCore P₀ ⊔ perfectCore P₁ = L := by
  have hUp : IsPGroup 2 ↥(T ⊓ L) :=
    IsPGroup.to_le (p := 2) (H := T ⊓ L) (K := T) h.sylow.isPGroup inf_le_left
  have hKL : perfectCore P₀ ⊔ perfectCore P₁ ≤ L :=
    sup_le ((perfectCore_le P₀).trans h.par₀.1) ((perfectCore_le P₁).trans h.par₁.1)
  have hU : T ⊓ L ≤ perfectCore P₀ ⊔ perfectCore P₁ :=
    h.concl₀.S_le.trans le_sup_left
  have hn0 : n ≠ 0 := by
    have := h.two_le
    omega
  have hpow : 2 ^ n ≠ 1 := ne_of_gt (Nat.one_lt_pow hn0 (by norm_num))
  by_contra hne
  have hlt : perfectCore P₀ ⊔ perfectCore P₁ < L := lt_of_le_of_ne hKL hne
  rcases h.le_or_le _ hU hlt with hle | hle
  · have hP₁le : perfectCore P₁ ≤ P₀ := le_sup_right.trans hle
    have hnorm : perfectCore P₁ ≤ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
      (le_inf hP₁le (perfectCore_le P₁)).trans h.inf_le
    have hUeq : T ⊓ L = pCoreOf 2 (perfectCore P₁) :=
      le_antisymm
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.concl₁.S_le hnorm hUp)
        (h.rad_le_inf (P := P₁) (Or.inr rfl))
    have hRle : pCoreOf 2 (perfectCore P₀) ≤ pCoreOf 2 (perfectCore P₁) := by
      have h1 := h.rad_le_inf (P := P₀) (Or.inl rfl)
      rwa [hUeq] at h1
    have hidx := h.concl₁.index_Q₁
    rw [h.sp4Q₁_one] at hidx
    have hrel : (pCoreOf 2 (perfectCore P₁) ⊓ pCoreOf 2 (perfectCore P₀)).relIndex
        (pCoreOf 2 (perfectCore P₀)) = 1 :=
      Subgroup.relIndex_eq_one.mpr (le_inf hRle le_rfl)
    rw [hrel] at hidx
    exact hpow hidx.symm
  · have hP₀le : perfectCore P₀ ≤ P₁ := le_sup_left.trans hle
    have hnorm : perfectCore P₀ ≤ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
      (le_inf (perfectCore_le P₀) hP₀le).trans h.inf_le
    have hUeq : T ⊓ L = pCoreOf 2 (perfectCore P₀) :=
      le_antisymm
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.concl₀.S_le hnorm hUp)
        (h.rad_le_inf (P := P₀) (Or.inl rfl))
    have hRle : pCoreOf 2 (perfectCore P₁) ≤ pCoreOf 2 (perfectCore P₀) := by
      have h1 := h.rad_le_inf (P := P₁) (Or.inr rfl)
      rwa [hUeq] at h1
    have hidx := h.concl₀.index_Q₁
    rw [h.sp4Q₁_zero] at hidx
    have hrel : (pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁)).relIndex
        (pCoreOf 2 (perfectCore P₁)) = 1 :=
      Subgroup.relIndex_eq_one.mpr (le_inf hRle le_rfl)
    rw [hrel] at hidx
    exact hpow hidx.symm

theorem eq_top_or_le_normalizer (h : Setting L T P₀ P₁ n w) {Y : Subgroup Q} (hTY : T ≤ Y) :
    Y = ⊤ ∨ Y ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  haveI hLnorm : L.Normal := h.normal
  by_cases hLY : L ≤ Y
  · left
    rw [eq_top_iff]
    calc ⊤ = L ⊔ T := h.sup_eq.symm
      _ ≤ Y := sup_le hLY hTY
  · right
    have hYL_lt : Y ⊓ L < L := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      exact hLY (heq ▸ inf_le_left)
    have hU_le : T ⊓ L ≤ Y ⊓ L := le_inf (inf_le_left.trans hTY) inf_le_right
    have hYLN : Y ⊓ L ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
      obtain ⟨t, htT, htP⟩ := h.exists_swap
      set f : Q →* Q := (MulAut.conj t).toMonoidHom
      have hf : Function.Injective f := (MulAut.conj t).injective
      have htP' : P₀.map f = P₁ := htP
      have hswap : P₁.map f = P₀ := by
        rcases map_conj_eq_or h htT with hfix | hsw
        · exact absurd (hfix.1.symm.trans htP') h.par_ne
        · exact hsw.2
      have hYmap : Y.map f = Y :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hTY htT))
      have hLmap : L.map f = L := Subgroup.Normal.map_conj_eq L t
      have hYLmap : (Y ⊓ L).map f = Y ⊓ L := by
        rw [Subgroup.map_inf_eq _ _ f hf, hYmap, hLmap]
      rcases h.le_or_le (Y ⊓ L) hU_le hYL_lt with hle0 | hle1
      · have hle : (Y ⊓ L).map f ≤ P₁ := by
          have h := Subgroup.map_mono (f := f) hle0
          rwa [htP'] at h
        rw [hYLmap] at hle
        exact (le_inf hle0 hle).trans h.inf_le
      · have hle : (Y ⊓ L).map f ≤ P₀ := by
          have h := Subgroup.map_mono (f := f) hle1
          rwa [hswap] at h
        rw [hYLmap] at hle
        exact (le_inf hle hle1).trans h.inf_le
    intro y hy
    have hyTop : y ∈ L ⊔ T := by
      rw [h.sup_eq]
      exact Subgroup.mem_top y
    obtain ⟨l, hlL, t, htT, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp hyTop
    have hlY : l ∈ Y := by
      have h1 : l = y * t⁻¹ := by
        rw [← hlt]
        group
      rw [h1]
      exact Y.mul_mem hy (Y.inv_mem (hTY htT))
    have hlN : l ∈ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := hYLN ⟨hlY, hlL⟩
    have htN : t ∈ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := h.le_normalizer_inf htT
    rw [← hlt]
    exact (normalizer ((T ⊓ L : Subgroup Q) : Set Q)).mul_mem hlN htN

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting