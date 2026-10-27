module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreUnitary
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarCentralizer
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarQuotient
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.Assembly CFSG.Open
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag TableBUE
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.Proj

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUKCoordAux_card_le_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) :
    Nat.card X ≤ p ^ (d - 1) := by
  classical
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn0 : n ≠ 0 := by
      have h1 : 1 ≤ n := h.one_le
      omega
    have hodd : Odd (2 ^ n + 1) :=
      ((even_two : Even (2 : ℕ)).pow_of_ne_zero hn0).add_one
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpq)
  have hN := gu_subset_normalizer (d := d) h
  have hpK : p ∣ Nat.card K - 1 := by
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have he : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
    rw [hK, he]
    exact Dvd.dvd.mul_right hpq _
  set ρ := TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) with hρ
  set N₀ : Subgroup
      (Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) :=
    X.comap ρ with hN₀
  set χ : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) →*
      MulAut (projectiveSL d K) :=
    (conjAut d K).comp
      (Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))).subtype
    with hχ
  set Y := N₀.map χ with hY
  have hscal : ∀ M, ρ M = 1 → χ M = 1 := by
    intro M hM
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK hd hdq hp hpq hM
    rw [hχ, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hc, conjAut_scalar]
  have hYab : IsElemAbelian p Y := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, M, hM, rfl⟩ ⟨_, M', hM', rfl⟩
      apply Subtype.ext
      show χ M * χ M' = χ M' * χ M
      have hc : ρ (M * M' * M⁻¹ * M'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          TableB.IsElemAbelian.comm hX hM hM', mul_inv_cancel_right, mul_inv_cancel]
      have h1 := hscal _ hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc χ M * χ M' = χ M * χ M' * (χ M)⁻¹ * (χ M')⁻¹ * (χ M' * χ M) := by group
        _ = χ M' * χ M := by rw [h1, one_mul]
    · rintro _ ⟨M, hM, rfl⟩
      rw [← map_pow]
      exact hscal _ (by rw [map_pow]; exact hX.2 _ hM)
  have hYI : (Y : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro _ ⟨M, -, rfl⟩
    exact ⟨M, rfl⟩
  have hlift : ∀ x : X, ∃ M : Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)), ρ M = x := by
    intro x
    obtain ⟨M, hMgu, hMeq⟩ := TableB.exists_eq_projConj hN (hXI x.2)
    exact ⟨⟨M, hN hMgu⟩, hMeq.symm⟩
  choose Mf hMf using hlift
  have hMN : ∀ x : X, Mf x ∈ N₀ := fun x => by
    show ρ (Mf x) ∈ X
    rw [hMf x]
    exact x.2
  let f : X → Y := fun x => ⟨χ (Mf x), Mf x, hMN x, rfl⟩
  have hf : Function.Injective f := by
    intro a b hab'
    have h1 : χ ((Mf a)⁻¹ * Mf b) = 1 := by
      have := congrArg Subtype.val hab'
      simp only [f] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
    have hz := mem_scalars_of_eq_scalar hc
    have h2 : ρ ((Mf a)⁻¹ * Mf b) = 1 := by
      have he : (Mf a)⁻¹ * Mf b = ⟨_, TableB.scalar_mem_normalizer _ hz⟩ := Subtype.ext rfl
      rw [he]
      exact TableB.projConj_of_scalar _ hz
    have h3 : ρ (Mf a) = ρ (Mf b) := by
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2
    apply Subtype.ext
    rw [← hMf a, ← hMf b, h3]
  have hle := Nat.card_le_card_of_injective f hf
  exact hle.trans (TypeA.card_le_of_subset_conjAut_gen hp hp2 hpK (by omega) hYab hYI)

theorem hdRo7SUKCoordAux_mem_range_uConjAut_of_pow_three {F : Type} [Field F]
    (h : UnitaryFieldData 2 1 F) {N : ℕ} (hN : 4 ≤ N)
    (α : MulAut (StatedProj (StatedSU N (2 ^ 1) F))) (h3 : α ^ 3 = 1) :
    ∃ g : uU h N, uConjAut h (by omega) g = α := by
  have hN3 : 3 ≤ N := by omega
  have hq : ¬(N = 3 ∧ 2 ^ 1 = 2) := fun hh => by omega
  obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut h hN3 hq α
  have hφ3 : φ ^ 3 = 1 := by
    have := congrArg (uFactor h hN3 hq) h3
    rw [map_pow, hα, uFactor_apply, map_one] at this
    exact this
  rcases CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.ringEquiv_eq_refl_or_bar h φ with h1 | h1
  · refine ⟨A, ?_⟩
    have hφ1 : φ = 1 := h1
    subst hφ1
    rw [hα, map_one]
    exact (mul_one _).symm
  · exfalso
    obtain ⟨ω, hω0, hω1⟩ := CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.exists_ne_zero_ne_one
      (hF := h)
    have hb : ∀ a : F, φ a = a ^ 2 := fun a => by
      rw [h1 a, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply h a]
      norm_num
    haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
    haveI : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card, h.card]
      norm_num
    have hpow : ω ^ 4 = ω := by
      have := FiniteField.pow_card ω
      rw [hcard] at this
      exact this
    have h3ω : φ (φ (φ ω)) = ω := by
      have e3 : (φ ^ 3) ω = φ (φ (φ ω)) := by
        rw [pow_succ, pow_two]
        rfl
      rw [← e3, hφ3]
      rfl
    rw [hb, hb, hb] at h3ω
    have h8 : ω ^ 8 = ω ^ 2 := by
      calc ω ^ 8 = (ω ^ 4) ^ 2 := by rw [← pow_mul]
        _ = ω ^ 2 := by rw [hpow]
        _ = ω ^ 2 := rfl
    rw [show ((ω ^ 2) ^ 2) ^ 2 = ω ^ 8 by ring, h8] at h3ω
    have : ω * (ω - 1) = 0 := by linear_combination h3ω
    rcases mul_eq_zero.1 this with hh | hh
    · exact hω0 hh
    · exact hω1 (sub_eq_zero.1 hh)

theorem hdRo7SUKCoordAux_le_range_uConjAut_of_isElemAbelian {F : Type} [Field F]
    (h : UnitaryFieldData 2 1 F) {N : ℕ} (hN : 4 ≤ N)
    (A : Subgroup (MulAut (StatedProj (StatedSU N (2 ^ 1) F))))
    (hA : CFSG.Open.IsElemAbelian 3 A) :
    ∀ a ∈ A, ∃ g : uU h N, uConjAut h (by omega) g = a :=
  fun a ha => hdRo7SUKCoordAux_mem_range_uConjAut_of_pow_three h hN a (hA.2 a ha)

theorem hdRo7SUKCoordAux_range_uConjAut_subset {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)
    {N : ℕ} (hN : 1 ≤ N) :
    Set.range (uConjAut h hN) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) F (2 ^ 1)))
        (LargeEvenGUSet (Fin N) F (2 ^ 1)) := by
  rintro φ ⟨A, rfl⟩
  refine ⟨(A : GL (Fin N) F), ?_, ?_⟩
  · refine ⟨1, one_ne_zero, by norm_num, ?_⟩
    rw [one_smul]
    have hbar : (fun c : F => c ^ (2 ^ 1)) = h.bar := by
      funext c
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply h c]
    rw [hbar]
    exact (mem_uU h).mp A.2
  · intro g g' hgg'
    change uConjAut h hN A (projH (StatedSU N (2 ^ 1) F) g) =
      projH (StatedSU N (2 ^ 1) F) g'
    rw [uConjAut_proj h hN A g]
    congr 1
    apply Subtype.ext
    exact hgg'.symm

end CFSG.StandardType.HdRo7SU

end
