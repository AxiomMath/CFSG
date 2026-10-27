module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectIso
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSecA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem w1369_perfect_cent_hend (hw2 : ∀ w : W, w ^ 2 = 1) {U C : Subgroup W}
    {Λ : Subgroup (MulAut W)} (hCU : C ≤ U) (hΛ : StabPair Λ U C) {k : ℕ} {J : Fin k → Subgroup W}
    (hCJ : ∀ i, C ≤ J i) (hJU : ∀ i, J i ≤ U) (hirr : ∀ i, IsIrrOn Λ (J i) C)
    (hend : ∀ i, (∃ j, j ≠ i ∧ SecIsoOn Λ (J i) C (J j) C) →
      Subgroup.centralizer ((secSub (J i) C Λ : Subgroup (MulAut (Sect (J i) C))) :
        Set (MulAut (Sect (J i) C))) = ⊥) :
    ∀ i j, i ≠ j →
      SecIsoOn (secSub U C Λ) (w1369_im U C (J i)) ⊥ (w1369_im U C (J j)) ⊥ →
      ∀ f : Sect U C →* Sect U C,
        (∀ g ∈ secSub U C Λ, ∀ x, f (g x) = g (f x)) →
        (∀ x ∈ w1369_im U C (J i), f x ∈ w1369_im U C (J i)) →
        (∀ j', j' ≠ i → ∀ x ∈ w1369_im U C (J j'), f x = 1) →
        (∀ x ∈ w1369_im U C (J i), f x = x) ∨
          (∀ x ∈ w1369_im U C (J i), f x = 1) := by
  intro i j hij hiso f hf hfMi hfk
  have hisoJ : SecIsoOn Λ (J i) C (J j) C :=
    (w1369_secIsoOn_im_iff hw2 hΛ (hCJ i) (hJU i) (hCJ j) (hJU j)).mp hiso
  have hc : Subgroup.centralizer
      ((secSub (J i) C Λ : Subgroup (MulAut (Sect (J i) C))) :
        Set (MulAut (Sect (J i) C))) = ⊥ :=
    hend i ⟨j, Ne.symm hij, hisoJ⟩
  have hΛJ : StabPair Λ (J i) C := fun a ha => ⟨(hirr i).2.1 a ha, (hΛ a ha).2⟩
  have hLI : Λ ≤ stabSub (J i) := fun a ha =>
    mem_stabSub.mpr fun u => ⟨fun hu => by
      have h1 := (hΛJ a⁻¹ (Λ.inv_mem ha)).1 (a u) hu
      simpa using h1, (hΛJ a ha).1 u⟩
  have hLZ : Λ ≤ stabSub C := fun a ha =>
    mem_stabSub.mpr fun u => ⟨fun hu => by
      have h1 := (hΛJ a⁻¹ (Λ.inv_mem ha)).2 (a u) hu
      simpa using h1, (hΛJ a ha).2 u⟩
  have hLU : Λ ≤ stabSub U := fun a ha =>
    mem_stabSub.mpr fun u => ⟨fun hu => by
      have h1 := (hΛ a⁻¹ (Λ.inv_mem ha)).1 (a u) hu
      simpa using h1, (hΛ a ha).1 u⟩
  have hIrr : IsIrrOn (secSub (J i) C Λ) (⊤ : Subgroup (Sect (J i) C)) ⊥ := by
    have h := w1369_irr_transfer (U := J i) (C := C) (Λ := Λ) hΛJ (hCJ i) le_rfl (hirr i)
    rwa [w1369_im_top (J i) C] at h
  have hendI : ∀ f' : Sect (J i) C →* Sect (J i) C,
      (∀ g ∈ secSub (J i) C Λ, ∀ x, f' (g x) = g (f' x)) →
      f' = 1 ∨ f' = MonoidHom.id (Sect (J i) C) := by
    intro f' hf'
    have hKstable : StableUnder (secSub (J i) C Λ) f'.ker := by
      intro γ hγ x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [hf' γ hγ x, hx, map_one]
    rcases hIrr.2.2.2 f'.ker hKstable bot_le le_top with hbot | htop
    · right
      have hinj : Function.Injective f' := by
        rw [← MonoidHom.ker_eq_bot_iff]
        exact hbot
      have hbij : Function.Bijective f' :=
        ⟨hinj, (Finite.injective_iff_surjective (α := Sect (J i) C)).mp hinj⟩
      let φ : MulAut (Sect (J i) C) := MulEquiv.ofBijective f' hbij
      have hφmem : φ ∈ Subgroup.centralizer
          ((secSub (J i) C Λ : Subgroup (MulAut (Sect (J i) C))) :
            Set (MulAut (Sect (J i) C))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        ext x
        rw [MulAut.mul_apply, MulAut.mul_apply]
        change s (f' x) = f' (s x)
        rw [hf' s hs x]
      have hφ1 : φ = 1 := by
        have h := hφmem
        rw [hc] at h
        exact Subgroup.mem_bot.mp h
      ext x
      show f' x = x
      have hφx : φ x = x := by rw [hφ1]; rfl
      exact hφx
    · left
      exact MonoidHom.ker_eq_top_iff.mp htop
  exact s16h_secIncl_hend (L := Λ) C (J i) U (hCJ i) (hJU i) hLI hLZ hLU hendI f hf hfMi

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
