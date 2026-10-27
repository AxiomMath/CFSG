module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDim
public import CFSG.Quasithin.Background.B4ModelsApi
import CFSG.Quasithin.Background.G64NatSec
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmallMod
import CFSG.Quasithin.Background.F918Z8Ex2a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16nt_one_le_of_card {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) :
    1 ≤ a := by
  by_contra h0
  have h0' : a = 0 := by omega
  subst h0'
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  omega

theorem s16nt_rk_le_of_card_le {Z : Subgroup W} {c : ℕ} (h : Nat.card ↥Z ≤ 2 ^ c) :
    rk ↥Z ≤ c := by
  change padicValNat 2 (Nat.card ↥Z) ≤ c
  calc padicValNat 2 (Nat.card ↥Z) ≤ Nat.log 2 (Nat.card ↥Z) := padicValNat_le_nat_log _
    _ ≤ Nat.log 2 (2 ^ c) := Nat.log_mono_right h
    _ = c := Nat.log_pow (by norm_num) c

private theorem w183_rk_eq_of_realizes [Finite W] {D : FFModel} {d : ℕ}
    (hmod : Nat.card D.Mod = 2 ^ d) {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : D.Realizes L I Z) : rk ↥I = rk ↥Z + d := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥I = Nat.card D.Mod * Nat.card ↥Z :=
    CFSG.Quasithin.G64.RealizesVia.card_eq hπ
  have hcard : Nat.card ↥I = 2 ^ d * Nat.card ↥Z := by rw [h1, hmod]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : (2 : ℕ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  have hZne : Nat.card ↥Z ≠ 0 := Nat.card_pos.ne'
  calc rk ↥I = padicValNat 2 (Nat.card ↥I) := rfl
    _ = padicValNat 2 (2 ^ d * Nat.card ↥Z) := by rw [hcard]
    _ = d + padicValNat 2 (Nat.card ↥Z) := by
        rw [padicValNat.mul hpow hZne, padicValNat.prime_pow]
    _ = rk ↥Z + d := by unfold rk; omega

theorem s16nt_goal_of_model [Finite W] {D : FFModel} {c d : ℕ} (hD : S16BoundCover D c)
    (hcd : 2 * c ≤ d) (hmod : Nat.card D.Mod = 2 ^ d) (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hUc : commSub U L = U) (hZ : Z ≤ fixV L)
    (h : D.Realizes L U Z) : 3 * rk ↥Z ≤ rk ↥U := by
  have hUinv : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U := s16c1614_invariant_of_realizes h
  have hcard : Nat.card ↥Z ≤ 2 ^ c :=
    s16fh_cover_restrict hD hW2 hUinv hUc hZ h
  have hrkZ : rk ↥Z ≤ c := s16nt_rk_le_of_card_le hcard
  have hrkU : rk ↥U = rk ↥Z + d := w183_rk_eq_of_realizes hmod h
  omega

theorem s16nt_sumOfNat_gen [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ}
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} (hUc : commSub U L = U)
    (hZ : Z ≤ fixV L)
    (hinv : ∀ I : Subgroup W, N L I Z → ∀ l ∈ L, ∀ x ∈ I, l x ∈ I)
    (h : SumOfNat N L U Z k) :
    SumOfNat (fun H I Z' => N H I Z' ∧ commSub I H ⊔ Z' = I) L U Z k := by
  obtain ⟨I, hZI, hind, hsup, hNI⟩ := h
  have hIinv : ∀ i, ∀ l ∈ L, ∀ x ∈ I i, l x ∈ I i :=
    fun i => hinv (I i) (hNI i)
  have hIU : ∀ i, I i ≤ U := by
    intro i
    calc I i ≤ ⨆ i, I i := le_iSup _ i
      _ ≤ Z ⊔ ⨆ i, I i := le_sup_right
      _ = U := hsup
  have hZU : Z ≤ U := by rw [← hsup]; exact le_sup_left
  let J : Fin k → Subgroup W := fun i => commSub (I i) L
  have hJI : ∀ i, J i ≤ I i := fun i => commSub_le_of_invariant (hIinv i)
  have hJinv : ∀ i, ∀ l ∈ L, ∀ y ∈ J i, l y ∈ J i :=
    fun i => s16jp_commSub_stable (L := L) (Y := I i) (hIinv i)
  have hgen : ∀ y ∈ ⨆ i, I i, ∀ l ∈ L, l y * y⁻¹ ∈ ⨆ i, J i := by
    intro y hy
    refine Subgroup.iSup_induction (fun i => I i) hy
      (C := fun z => ∀ l ∈ L, l z * z⁻¹ ∈ ⨆ i, J i) ?_ ?_ ?_
    · intro i y hy l hl
      exact le_iSup (fun i => J i) i (Subgroup.subset_closure ⟨l, hl, y, hy, rfl⟩)
    · intro l hl
      simpa only [map_one, inv_one, one_mul] using Subgroup.one_mem (⨆ i, J i)
    · intro a b ha hb l hl
      rw [map_mul, mul_inv_rev]
      rw [show (l a * l b) * (b⁻¹ * a⁻¹) = (l a * a⁻¹) * (l b * b⁻¹) by ac_rfl]
      exact mul_mem (ha l hl) (hb l hl)
  have hUJ : U ≤ ⨆ i, J i := by
    rw [← hUc]
    change Subgroup.closure {c : W | ∃ x ∈ L, ∃ w ∈ U, x w * w⁻¹ = c} ≤ ⨆ i, J i
    rw [Subgroup.closure_le]
    rintro c ⟨l, hl, x, hx, rfl⟩
    have hx' : x ∈ Z ⊔ ⨆ i, I i := by rw [hsup]; exact hx
    obtain ⟨z, hz, y, hy, hzy⟩ := Subgroup.mem_sup.mp hx'
    have hzL : l z = z := (mem_fixV.mp (hZ hz)) l hl
    have hxy : l x * x⁻¹ = l y * y⁻¹ := by
      rw [← hzy, map_mul, mul_inv_rev, hzL]
      rw [show (z * l y) * (y⁻¹ * z⁻¹) = (z * z⁻¹) * (l y * y⁻¹) by ac_rfl]
      rw [mul_inv_cancel, one_mul]
    rw [hxy]
    exact hgen y hy l hl
  have hJU : (⨆ i, J i) ≤ U := iSup_le fun i => (hJI i).trans (hIU i)
  have hUeq : U = ⨆ i, J i := le_antisymm hUJ hJU
  have hgen_i : ∀ i, commSub (I i) L ⊔ Z = I i := by
    intro i
    refine le_antisymm (sup_le (hJI i) (hZI i)) ?_
    intro x hx
    have hxU : x ∈ U := hIU i hx
    have hxJ : x ∈ ⨆ b, J b := hUeq ▸ hxU
    obtain ⟨j, hj, hxprod⟩ := d321i_exists_prod_of_mem_iSup J hxJ
    have hxsplit : x = j i * ∏ b ∈ Finset.univ.erase i, j b := by
      rw [hxprod, Finset.mul_prod_erase Finset.univ j (Finset.mem_univ i)]
    have hyI : (∏ b ∈ Finset.univ.erase i, j b) ∈ I i := by
      rw [show (∏ b ∈ Finset.univ.erase i, j b) = (j i)⁻¹ * x by
        rw [hxsplit, inv_mul_cancel_left]]
      exact (I i).mul_mem ((I i).inv_mem (hJI i (hj i))) hx
    have hyMem : (∏ b ∈ Finset.univ.erase i, j b) ∈
        ⨆ (b : Fin k) (_ : b ≠ i), I b :=
      Subgroup.prod_mem _ fun b hb =>
        Subgroup.mem_iSup_of_mem b
          (Subgroup.mem_iSup_of_mem (Finset.mem_erase.mp hb).1 (hJI b (hj b)))
    have hyZ : (∏ b ∈ Finset.univ.erase i, j b) ∈ Z :=
      hind i (Subgroup.mem_inf.mpr ⟨hyI, Subgroup.mem_sup_right hyMem⟩)
    rw [hxsplit]
    exact Subgroup.mul_mem_sup (hj i) hyZ
  exact ⟨I, hZI, hind, hsup, fun i => ⟨hNI i, hgen_i i⟩⟩

theorem s16nt_goal_of_sum [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) {U Z : Subgroup W} (hUinv : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    (hUc : commSub U L = U) (hZ : Z ≤ fixV L)
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {k c d : ℕ}
    (hN : ∀ I : Subgroup W, N L I Z →
      ∃ D : FFModel, S16BoundCover D c ∧ D.Realizes L I Z ∧ Nat.card D.Mod = 2 ^ d)
    (hcd : 2 * c ≤ d) (h : SumOfNat N L U Z k) : 3 * rk ↥Z ≤ rk ↥U := by
  have hinv : ∀ I : Subgroup W, N L I Z → ∀ l ∈ L, ∀ x ∈ I, l x ∈ I := by
    intro I hI
    obtain ⟨D, -, hR, -⟩ := hN I hI
    exact s16c1614_invariant_of_realizes hR
  have hsum' : SumOfNat (fun H I Z' => N H I Z' ∧ commSub I H ⊔ Z' = I) L U Z k :=
    s16nt_sumOfNat_gen hUc hZ hinv h
  have hN' : ∀ I : Subgroup W,
      (fun H I Z' => N H I Z' ∧ commSub I H ⊔ Z' = I) L I Z →
      ∃ D : FFModel, S16BoundCover D c ∧ D.Realizes L I Z ∧ commSub I L ⊔ Z = I := by
    intro I hI
    obtain ⟨hNI, hgenI⟩ := hI
    obtain ⟨D, hD, hR, hmod⟩ := hN I hNI
    exact ⟨D, hD, hR, hgenI⟩
  have hcard : Nat.card ↥Z ≤ 2 ^ (c * k) :=
    s16fh_sum_cover hW2 hperf hUinv hUc hZ hN' hsum'
  have hrkZ : rk ↥Z ≤ c * k := s16nt_rk_le_of_card_le hcard
  have hm : ∀ I : Subgroup W,
      (fun H I Z' => N H I Z' ∧ commSub I H ⊔ Z' = I) L I Z →
      rk ↥I = rk ↥Z + d := by
    intro I hI
    obtain ⟨hNI, -⟩ := hI
    obtain ⟨D, -, hR, hmod⟩ := hN I hNI
    exact w183_rk_eq_of_realizes hmod hR
  have hrkU : rk ↥Z + k * d ≤ rk ↥U := s16fh_rk_sumOfNat_ge hsum' hm
  have hmul : 2 * c * k ≤ d * k := Nat.mul_le_mul_right k hcd
  have h2 : 2 * rk ↥Z ≤ k * d := by
    calc 2 * rk ↥Z ≤ 2 * (c * k) := Nat.mul_le_mul_left 2 hrkZ
      _ = 2 * c * k := by rw [Nat.mul_assoc]
      _ ≤ d * k := hmul
      _ = k * d := Nat.mul_comm d k
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
