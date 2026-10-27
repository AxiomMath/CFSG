module

public import CFSG.Quasithin.Vol2.Ch10SecDXI5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem factXIrred
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    FactXIrred := by
  intro G _ _ T L I h h3 hc t v₁ v₂ hd Y hQY hYX hTY
  by_cases hYQ : Y ≤ pCoreOf 2 (Xz T L (v₁ * v₂))
  · exact Or.inl (le_antisymm hYQ hQY)
  right
  obtain ⟨y, hyY, hyQ⟩ := Set.not_subset.mp hYQ
  obtain ⟨x, hxL, hxX, hxo, hxC⟩ := exists_odd_mem_Xz h37 h38 h h3 hc hd
  have hd' := hd
  obtain ⟨ht, htn, hv1, -, -, -⟩ := hd'
  have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_mem h37 h38 h h3 hc hd (oTwoUpper_le _ hxX) hxo
  have hTX : T ≤ Subgroup.normalizer (Xz T L (v₁ * v₂) : Set G) :=
    T_le_normalizer_Xz (T_le_centralizer_z h37 h38 h h3 hc hd)
  have htr : ∀ g ∈ kOf (fsuUL T L I) v₁,
      t⁻¹ * g * t ∈ kOf ⁅fsuVM T L I, CFSG.conjugate L t⁆ v₂ := fun g hg =>
    conj_mem_kOf_of (fun w => by rw [V2_eq_conjugate ht, SecA.mem_conjugate_iff])
      (conj_v2 h37 h38 h h3 hc hd) hg
  have hKQ := kOf_inf_le_pCoreOf h37 h38 h hc hd
  have hpow3 : ∀ {i : ℕ} {g : G}, i % 3 = 0 → x ^ i * g ∈ kOf (fsuUL T L I) v₁ →
      g ∈ kOf (fsuUL T L I) v₁ := by
    intro i g hi hg
    rwa [show i = 3 * (i / 3) by omega, pow_mul, hx3, one_pow, one_mul] at hg
  have hxY : x ∈ Y := by
    obtain ⟨i, hi⟩ := exists_pow_mul_mem_kOf h37 h38 h h3 hc hd hxX hxo hxC (hYX hyY)
    by_cases hi3 : i % 3 = 0
    · have hyK1 := hpow3 hi3 hi
      have hyK2 : y ∉ kOf ⁅fsuVM T L I, CFSG.conjugate L t⁆ v₂ := fun hyK2 =>
        hyQ (hKQ ⟨⟨hYX hyY, hyK1⟩, hyK2⟩)
      have hy'Y : t * y * t⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hTY ht) y).mp hyY
      obtain ⟨j, hj⟩ := exists_pow_mul_mem_kOf h37 h38 h h3 hc hd hxX hxo hxC (hYX hy'Y)
      by_cases hj3 : j % 3 = 0
      · exfalso
        apply hyK2
        have h1 := htr _ (hpow3 hj3 hj)
        rwa [show t⁻¹ * (t * y * t⁻¹) * t = y by group] at h1
      · exact mem_of_pow_mul_mem h37 h38 h h3 hc hd hxL hxX hxo hxC hQY hYX hTY hy'Y hj3 hj
    · exact mem_of_pow_mul_mem h37 h38 h h3 hc hd hxL hxX hxo hxC hQY hYX hTY hyY hi3 hi
  have hx'X : t⁻¹ * x * t ∈ Xz T L (v₁ * v₂) := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hTX (T.inv_mem ht)) x).mp hxX
    rwa [inv_inv] at h1
  have hx'Y : t⁻¹ * x * t ∈ Y := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hTY (T.inv_mem ht)) x).mp hxY
    rwa [inv_inv] at h1
  have htt : t * t ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (X := T1 T L)
      (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I)) inf_le_right
      ⟨T.mul_mem ht ht, SecA.mul_self_mem_normalizer h37 h38 h ht htn⟩
  have hx'C : t⁻¹ * x * t ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu2 : t * u * t⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
      rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht), SecA.mem_conjugate_iff]
      have h1 := (Subgroup.mem_normalizer_iff.mp htt u).mp hu
      rwa [show t * (t * u * t⁻¹) * t⁻¹ = t * t * u * (t * t)⁻¹ by group]
    have hxu := (Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hu2)) x hxL
    calc u * (t⁻¹ * x * t) = t⁻¹ * ((t * u * t⁻¹) * x) * t := by group
      _ = t⁻¹ * (x * (t * u * t⁻¹)) * t := by rw [hxu]
      _ = t⁻¹ * x * t * u := by group
  have hpowc : ∀ n : ℕ, (t⁻¹ * x * t) ^ n = t⁻¹ * x ^ n * t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; group
  refine le_antisymm hYX (fun g hg => ?_)
  obtain ⟨i, hi⟩ := exists_pow_mul_mem_kOf h37 h38 h h3 hc hd hxX hxo hxC hg
  have hg1X : x ^ i * g ∈ Xz T L (v₁ * v₂) := Subgroup.mul_mem _ (Subgroup.pow_mem _ hxX i) hg
  have htg : t * (x ^ i * g) * t⁻¹ ∈ Xz T L (v₁ * v₂) :=
    (Subgroup.mem_normalizer_iff.mp (hTX ht) _).mp hg1X
  obtain ⟨j, hj⟩ := exists_pow_mul_mem_kOf h37 h38 h h3 hc hd hxX hxo hxC htg
  have hj2 := htr _ hj
  rw [show t⁻¹ * (x ^ j * (t * (x ^ i * g) * t⁻¹)) * t = (t⁻¹ * x * t) ^ j * (x ^ i * g) by
    rw [hpowc]; group] at hj2
  have hQ := hQY (hKQ ⟨⟨Subgroup.mul_mem _ (Subgroup.pow_mem _ hx'X j) hg1X,
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (mem_kOf_of_mem_centralizer hv1.1 hx'C) j) hi⟩, hj2⟩)
  rw [show g = (x ^ i)⁻¹ * ((t⁻¹ * x * t) ^ j)⁻¹ * ((t⁻¹ * x * t) ^ j * (x ^ i * g)) by group]
  exact Y.mul_mem (Y.mul_mem (Y.inv_mem (Y.pow_mem hxY i)) (Y.inv_mem (Y.pow_mem hx'Y j))) hQ

end CFSG.Quasithin.Vol2.Ch10.SecD
