module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c13beta_rank_pts {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {X F : Subgroup (MulAut T)} {p k r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 3 < r)
    (hk : k < dParam p) {ι : Type} [Fintype ι] {Y : ι → Subgroup T} (hind : iSupIndep Y)
    (hrk : ∀ i, rk ↥(Y i) = dParam p) (hcard : r ≤ Fintype.card ι) (hFX : F ≤ X)
    (hF : IsElemAbelian p F) (hFn : p ^ r ≤ Nat.card F)
    (hFY : ∀ f ∈ F, ∀ i, (Y i).map f.toMonoidHom = Y i) :
    s16c13betaPts X p (k + 1) := by
  classical
  intro U hU
  set d := dParam p with hd
  have hk1 : k + 1 ≤ d := by omega
  have hsub : r - 2 ≤ (Finset.univ : Finset ι).card := by
    rw [Finset.card_univ]; omega
  obtain ⟨S, -, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := r - 2) hsub
  set W : Subgroup T := ⨆ i ∈ S, Y i with hWdef
  have hrkW : rk W = (r - 2) * d := by
    rw [hWdef, rk_iSup_biSup_eq_sum Y hind S]
    rw [Finset.sum_const_nat (s := S) (m := d) (fun i _ => hrk i)]
    simp [hScard]
  have h2d : 2 * d ≤ rk W := by
    rw [hrkW]
    exact Nat.mul_le_mul_right d (by omega : 2 ≤ r - 2)
  have hdltW : d < rk W := by
    have h2 : d < 2 * d := by omega
    exact lt_of_lt_of_le h2 h2d
  have hU_lt : rkIdx U < rk W := by omega
  have hinf : U ⊓ W ≠ ⊥ := by
    have hsup := rk_sup_add_rk_inf U W
    have htop : rk ↥(U ⊔ W) ≤ rk T := by
      have := rk_mono (le_top : U ⊔ W ≤ (⊤ : Subgroup T))
      rwa [rk_top] at this
    have hadd := rk_add_rkIdx U
    have hpos : 0 < rk ↥(U ⊓ W) := by omega
    intro hbot
    rw [hbot, rk_bot] at hpos
    omega
  obtain ⟨z, hzU, hzW, hz1⟩ : ∃ z : T, z ∈ U ∧ z ∈ W ∧ z ≠ 1 := by
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
    refine ⟨(z : T), (Subgroup.mem_inf.mp z.2).1, (Subgroup.mem_inf.mp z.2).2, ?_⟩
    intro hz
    exact hz1 (Subtype.ext (by simpa using hz))
  have hS : S.card + 2 ≤ r := by rw [hScard]; omega
  obtain ⟨E, hEF, hEp, hEnc, hEfix⟩ :=
    s16c13beta_exists_noncyclic_fix (n := r) hp hT hF hFn Y S
      (fun i _ => hrk i) (fun i _ f hf => hFY f hf i) hS
  refine ⟨z, hzU, hz1, E, hEF.trans hFX, hEp, hEnc, ?_⟩
  intro e he
  have hfix : W ≤ fixV (Subgroup.zpowers e) := by
    rw [hWdef]
    refine iSup₂_le ?_
    intro i hi y hy
    exact (mem_fixV_zpowers_iff_apply (g := e) (v := y)).mpr (hEfix i hi e he y hy)
  exact (mem_fixV_zpowers_iff_apply (g := e) (v := z)).mp (hfix hzW)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
