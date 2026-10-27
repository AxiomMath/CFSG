module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQSzB
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.Transfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Matrix Subgroup

theorem exists_eq_mulVec_sub_of_sz {a : ℕ} (ha : 1 ≤ a)
    {Z : Subgroup ↥(Sz a)} (hZ : IsElemAbelian 2 Z) (hZcard : Nat.card Z = 2 ^ (2 * a + 1))
    {δ : ↥(Sz a) → (Fin 4 → GaloisField 2 (2 * a + 1))}
    (hδ : ∀ x y : ↥(Sz a), δ (x * y) = δ x +
      (((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ δ y))
    (hδZ : ∀ z ∈ Z, δ z = 0) :
    ∃ n : Fin 4 → GaloisField 2 (2 * a + 1),
      (∀ z ∈ Z, (((z : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n = n) ∧
      ∀ x : ↥(Sz a), δ x = (((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n) - n := by
  classical
  obtain ⟨S, hS⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha
    (MulEquiv.refl ↥(Sz a)) hZ hZcard
  have hnorm : Subgroup.normalizer (Z : Set ↥(Sz a)) =
      Subgroup.normalizer ((S : Subgroup ↥(Sz a)) : Set ↥(Sz a)) := by
    rw [hS]
    exact normalizer_inf_centralizer_eq_of_mulEquiv_sz ha (MulEquiv.refl _) S
  have hodd : ¬ 2 ∣ (Subgroup.normalizer (Z : Set ↥(Sz a))).index := by
    rw [hnorm]
    intro h2
    exact Sylow.not_dvd_index S
      (h2.trans (Subgroup.index_dvd_of_le Subgroup.le_normalizer))
  obtain ⟨n₀, hn₀fix, hn₀δ⟩ :=
    exists_eq_mulVec_sub_of_normalizer_sz ha hZ hZcard hδ hδZ
  let δ₁ : ↥(Sz a) → (Fin 4 → GaloisField 2 (2 * a + 1)) :=
    fun x => δ x - (((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n₀ - n₀)
  have hδ₁ : ∀ x y : ↥(Sz a), δ₁ (x * y) = δ₁ x +
      (((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ δ₁ y) := by
    intro x y
    simp only [δ₁]
    rw [hδ x y]
    have h1 : (((x * y : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n₀ =
        (((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ
          ((((y : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)))) *ᵥ n₀)) := by
      simp [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]
    rw [h1]
    simp only [mulVec_sub]
    abel
  have hδ₁B : ∀ z ∈ Subgroup.normalizer (Z : Set ↥(Sz a)), δ₁ z = 0 := by
    intro z hz
    simp only [δ₁]
    rw [hn₀δ z hz, sub_self]
  obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.exists_coboundary_of_odd_index
    (Subgroup.normalizer (Z : Set ↥(Sz a))) hodd δ₁
    (fun x y => by
      simpa [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec] using hδ₁ x y)
    hδ₁B
  refine ⟨n₀ + m, ?_, ?_⟩
  · intro z hz
    have hzB : z ∈ Subgroup.normalizer (Z : Set ↥(Sz a)) := Subgroup.le_normalizer hz
    have hmfix := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.fixed_of_coboundary_of_vanishes
      (Subgroup.normalizer (Z : Set ↥(Sz a))) δ₁ m hm hδ₁B
    have hmz : (((z : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ m = m := by
      simpa [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec] using hmfix z hzB
    rw [mulVec_add, hn₀fix z hz, hmz]
  · intro x
    have hx := hm x
    simp only [δ₁, Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec] at hx
    have hx' : δ x = ((((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ m) - m) +
        ((((x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n₀) - n₀) := by
      rw [← hx]
      abel
    rw [hx', mulVec_add]
    abel

end CFSG.LocalAnalysis.WeakClosure81

end
