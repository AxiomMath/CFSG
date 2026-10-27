module

public import CFSG.GF2Type.Smith1979.CaseI25Split
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.StandardType.GGFusionExceptionFull
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.Sporadic.Co1Patterson.SettingOmega
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S111ADisj
public import CFSG.LargeExtraspecial.S111AExists
public import CFSG.LargeExtraspecial.S12FourteenB
public import CFSG.LargeExtraspecial.S7Six
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.Timmesfeld.Special.TwoCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped MatrixGroups commutatorElement
open CFSG.StandardType CFSG.Assembly

namespace CFSG.StandardType
namespace GGPlaneA

variable {F : Type} [Field F] [Finite F] {m : ℕ}

def e (i : Fin m) : Fin m ⊕ Fin m → F := Pi.single (Sum.inl i) 1
def f (i : Fin m) : Fin m ⊕ Fin m → F := Pi.single (Sum.inr i) 1

lemma Q_update_inl (h2 : (2 : F) = 0) (v : Fin m ⊕ Fin m → F) (i : Fin m) (c : F) :
    ggFusionPlaneQuadratic F m (v + c • e (F := F) i) =
      ggFusionPlaneQuadratic F m v + c * (c + v (Sum.inr i)) := by
  have h : ggFusionPlaneQuadratic F m (v + c • e (F := F) i) -
      ggFusionPlaneQuadratic F m v = c * (c + v (Sum.inr i)) := by
    rw [ggFusionPlaneQuadratic, ggFusionPlaneQuadratic, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp only [e, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      ring_nf
      simp [h2]
    · intro j _ hji
      have h1 : (Sum.inl j : Fin m ⊕ Fin m) ≠ Sum.inl i := by simpa using hji
      have h2 : (Sum.inr j : Fin m ⊕ Fin m) ≠ Sum.inl i := by simp
      simp only [e, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne h1,
        Pi.single_eq_of_ne h2, smul_eq_mul, add_zero]
      ring
    · intro hi
      simp at hi
  calc ggFusionPlaneQuadratic F m (v + c • e (F := F) i)
      = (ggFusionPlaneQuadratic F m (v + c • e (F := F) i) -
          ggFusionPlaneQuadratic F m v) + ggFusionPlaneQuadratic F m v := by ring
    _ = c * (c + v (Sum.inr i)) + ggFusionPlaneQuadratic F m v := by rw [h]
    _ = ggFusionPlaneQuadratic F m v + c * (c + v (Sum.inr i)) := by ring

lemma Q_update_inr (h2 : (2 : F) = 0) (v : Fin m ⊕ Fin m → F) (i : Fin m) (c : F) :
    ggFusionPlaneQuadratic F m (v + c • f (F := F) i) =
      ggFusionPlaneQuadratic F m v + c * (c + v (Sum.inl i)) := by
  have h : ggFusionPlaneQuadratic F m (v + c • f (F := F) i) -
      ggFusionPlaneQuadratic F m v = c * (c + v (Sum.inl i)) := by
    rw [ggFusionPlaneQuadratic, ggFusionPlaneQuadratic, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp only [f, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      ring_nf
      simp [h2]
    · intro j _ hji
      have h1 : (Sum.inr j : Fin m ⊕ Fin m) ≠ Sum.inr i := by simpa using hji
      have h2 : (Sum.inl j : Fin m ⊕ Fin m) ≠ Sum.inr i := by simp
      simp only [f, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne h1,
        Pi.single_eq_of_ne h2, smul_eq_mul, add_zero]
      ring
    · intro hi
      simp at hi
  calc ggFusionPlaneQuadratic F m (v + c • f (F := F) i)
      = (ggFusionPlaneQuadratic F m (v + c • f (F := F) i) -
          ggFusionPlaneQuadratic F m v) + ggFusionPlaneQuadratic F m v := by ring
    _ = c * (c + v (Sum.inl i)) + ggFusionPlaneQuadratic F m v := by rw [h]
    _ = ggFusionPlaneQuadratic F m v + c * (c + v (Sum.inl i)) := by ring

section Matrices

variable (F m)

noncomputable def aGL (i : Fin m) : GL (Fin m ⊕ Fin m) F :=
  TauCeti.transvectionUnit (i := Sum.inl i) (j := Sum.inr i) (Sum.inl_ne_inr) 1

noncomputable def bGL (i : Fin m) : GL (Fin m ⊕ Fin m) F :=
  TauCeti.transvectionUnit (i := Sum.inr i) (j := Sum.inl i) (Sum.inr_ne_inl) 1

noncomputable def tauGL (i j : Fin m) : GL (Fin m ⊕ Fin m) F :=
  TauCeti.permutationGL (Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j))

variable {F m}

lemma aGL_mulVec (i : Fin m) (v : Fin m ⊕ Fin m → F) :
    Matrix.mulVec (aGL F m i : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) v =
      v + v (Sum.inr i) • e (F := F) i := by
  rw [aGL, TauCeti.coe_transvectionUnit]
  rw [show Matrix.mulVec (Matrix.transvection (Sum.inl i) (Sum.inr i) (1 : F)) v =
      v + ((1 : F) * v (Sum.inr i)) • Pi.single (Sum.inl i) 1 from by
    ext k
    by_cases hk : k = Sum.inl i
    · subst hk
      simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec]
    · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, hk]]
  simp [e, one_mul]

lemma bGL_mulVec (i : Fin m) (v : Fin m ⊕ Fin m → F) :
    Matrix.mulVec (bGL F m i : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) v =
      v + v (Sum.inl i) • f (F := F) i := by
  rw [bGL, TauCeti.coe_transvectionUnit]
  rw [show Matrix.mulVec (Matrix.transvection (Sum.inr i) (Sum.inl i) (1 : F)) v =
      v + ((1 : F) * v (Sum.inl i)) • Pi.single (Sum.inr i) 1 from by
    ext k
    by_cases hk : k = Sum.inr i
    · subst hk
      simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec]
    · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, hk]]
  simp [f, one_mul]

end Matrices

end GGPlaneA
end CFSG.StandardType

namespace CFSG.StandardType
namespace GGPlaneA

variable {F : Type} [Field F] [Finite F] {m : ℕ}

lemma Q_comp_sumCongr (σ : Equiv.Perm (Fin m)) (v : Fin m ⊕ Fin m → F) :
    ggFusionPlaneQuadratic F m (v ∘ ⇑(Equiv.Perm.sumCongr σ σ)) =
      ggFusionPlaneQuadratic F m v := by
  simp only [ggFusionPlaneQuadratic, Function.comp_apply, Equiv.Perm.sumCongr_apply,
    Sum.map_inl, Sum.map_inr]
  exact Equiv.sum_comp σ (fun i => v (Sum.inl i) ^ 2 + v (Sum.inl i) * v (Sum.inr i) +
    v (Sum.inr i) ^ 2)

lemma charP_two (hcard : Nat.card F = 2) : CharP F 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  apply charP_of_card_eq_prime
  rw [← Nat.card_eq_fintype_card]
  exact hcard

lemma two_eq_zero (hcard : Nat.card F = 2) : (2 : F) = 0 := by
  haveI : CharP F 2 := charP_two hcard
  exact CharP.cast_eq_zero F 2

lemma three_eq_one (hcard : Nat.card F = 2) : (3 : F) = 1 := by
  rw [show (3 : F) = (2 : F) + 1 by norm_num, two_eq_zero hcard, zero_add]

lemma five_eq_one (hcard : Nat.card F = 2) : (5 : F) = 1 := by
  rw [show (5 : F) = (2 : F) * 2 + 1 by norm_num, two_eq_zero hcard, zero_mul, zero_add]

lemma aGL_mem (hcard : Nat.card F = 2) (i : Fin m) :
    aGL F m i ∈ LargeEvenOrthGroup (ggFusionPlaneQuadratic F m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 := charP_two hcard
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  refine TableBSymp.mem_orthGroup_of_isometry fun v => ?_
  rw [aGL_mulVec, Q_update_inl h2]
  ring_nf
  simp [h2]

lemma bGL_mem (hcard : Nat.card F = 2) (i : Fin m) :
    bGL F m i ∈ LargeEvenOrthGroup (ggFusionPlaneQuadratic F m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 := charP_two hcard
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  refine TableBSymp.mem_orthGroup_of_isometry fun v => ?_
  rw [bGL_mulVec, Q_update_inr h2]
  ring_nf
  simp [h2]

lemma tauGL_mem (hcard : Nat.card F = 2) (i j : Fin m) :
    tauGL F m i j ∈ LargeEvenOrthGroup (ggFusionPlaneQuadratic F m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 := charP_two hcard
  refine TableBSymp.mem_orthGroup_of_isometry fun v => ?_
  rw [tauGL, TableBSymp.permutationGL_mulVec]
  have hπ : (Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j))⁻¹ =
      Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) := by
    rw [Equiv.Perm.sumCongr_inv, Equiv.swap_inv]
  rw [hπ]
  exact Q_comp_sumCongr (Equiv.swap i j) v

lemma aGL_sq (hcard : Nat.card F = 2) (i : Fin m) : aGL F m i * aGL F m i = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 := charP_two hcard
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  apply Units.ext
  rw [Units.val_mul, aGL, TauCeti.coe_transvectionUnit]
  rw [show Matrix.transvection (Sum.inl i) (Sum.inr i) (1 : F) *
      Matrix.transvection (Sum.inl i) (Sum.inr i) (1 : F) = 1 from by
    rw [Matrix.transvection_mul_transvection_same (i := Sum.inl i) (j := Sum.inr i)
      (h := Sum.inl_ne_inr) (c := 1) (d := 1)]
    rw [show (1 : F) + 1 = 0 by
      rw [show (1 : F) + 1 = (2 : F) by norm_num, h2]]
    simp [Matrix.transvection]]
  simp

lemma bGL_sq (hcard : Nat.card F = 2) (i : Fin m) : bGL F m i * bGL F m i = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 := charP_two hcard
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  apply Units.ext
  rw [Units.val_mul, bGL, TauCeti.coe_transvectionUnit]
  rw [show Matrix.transvection (Sum.inr i) (Sum.inl i) (1 : F) *
      Matrix.transvection (Sum.inr i) (Sum.inl i) (1 : F) = 1 from by
    rw [Matrix.transvection_mul_transvection_same (i := Sum.inr i) (j := Sum.inl i)
      (h := Sum.inr_ne_inl) (c := 1) (d := 1)]
    rw [show (1 : F) + 1 = 0 by
      rw [show (1 : F) + 1 = (2 : F) by norm_num, h2]]
    simp [Matrix.transvection]]
  simp

lemma tauGL_sq (i j : Fin m) : tauGL F m i j * tauGL F m i j = 1 := by
  have hπ : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) *
      Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) = 1 := by
    rw [Equiv.Perm.sumCongr_mul, Equiv.swap_mul_self,
      Equiv.Perm.sumCongr_one]
  rw [tauGL, ← map_mul, hπ, map_one]

end GGPlaneA
end CFSG.StandardType

namespace CFSG.StandardType
namespace GGPlaneA

open CFSG.Assembly
variable {F : Type} [Field F] [Finite F] {m : ℕ}

noncomputable def tGL (F : Type) [Field F] (m : ℕ) (i : Fin m) : GL (Fin m ⊕ Fin m) F :=
  ⁅aGL F m i, bGL F m i⁆

noncomputable def A (F : Type) [Field F] (m : ℕ) (i : Fin m) :
    (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) :=
  CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F (aGL F m i)

noncomputable def B (F : Type) [Field F] (m : ℕ) (i : Fin m) :
    (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) :=
  CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F (bGL F m i)

noncomputable def T (F : Type) [Field F] (m : ℕ) (i : Fin m) :
    (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) :=
  CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F (tGL F m i)

lemma A_apply (i : Fin m) (v : Fin m ⊕ Fin m → F) :
    A F m i v = v + v (Sum.inr i) • e (F := F) i := by
  rw [A, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, aGL_mulVec]

lemma B_apply (i : Fin m) (v : Fin m ⊕ Fin m → F) :
    B F m i v = v + v (Sum.inl i) • f (F := F) i := by
  rw [B, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, bGL_mulVec]

lemma T_eq (hcard : Nat.card F = 2) (i : Fin m) :
    T F m i = A F m i * B F m i * A F m i * B F m i := by
  have ha : (aGL F m i)⁻¹ = aGL F m i := inv_eq_of_mul_eq_one_right (aGL_sq hcard i)
  have hb : (bGL F m i)⁻¹ = bGL F m i := inv_eq_of_mul_eq_one_right (bGL_sq hcard i)
  simp only [T, tGL, commutatorElement_def, A, B, ha, hb, map_mul, map_inv]

lemma T_apply (hcard : Nat.card F = 2) (i : Fin m) (v : Fin m ⊕ Fin m → F) :
    T F m i v = (v (Sum.inl i) + v (Sum.inr i)) • e (F := F) i +
      v (Sum.inl i) • f (F := F) i +
      (v + v (Sum.inl i) • e (F := F) i + v (Sum.inr i) • f (F := F) i) := by
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  rw [T_eq hcard]
  simp only [LinearEquiv.mul_apply, A_apply, B_apply]
  ext j
  by_cases hj : j = Sum.inl i <;> by_cases hj2 : j = Sum.inr i <;>
    simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hj, hj2, Sum.inl_ne_inr,
      Sum.inr_ne_inl]
  all_goals ring_nf; simp [h2, three_eq_one hcard, five_eq_one hcard]

end GGPlaneA
end CFSG.StandardType

namespace CFSG.StandardType
namespace GGPlaneA
open CFSG.Assembly
variable {F : Type} [Field F] [Finite F] {m : ℕ}

noncomputable def E (F : Type) [Field F] (m : ℕ) (i : Fin m) :
    (Fin m ⊕ Fin m → F) →ₗ[F] (Fin m ⊕ Fin m → F) :=
  LinearMap.id + (LinearMap.proj (Sum.inl i)).smulRight (e (F := F) i) +
    (LinearMap.proj (Sum.inr i)).smulRight (f (F := F) i)

lemma E_apply (i : Fin m) (v : Fin m ⊕ Fin m → F) :
    E F m i v = v + v (Sum.inl i) • e (F := F) i + v (Sum.inr i) • f (F := F) i := by
  simp [E, LinearMap.smulRight_apply]

lemma T_sq_add_T_add_one_eq_E (hcard : Nat.card F = 2) (i : Fin m) :
    (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
        (T F m i : Module.End F (Fin m ⊕ Fin m → F)) +
      (T F m i : Module.End F (Fin m ⊕ Fin m → F)) + 1 = E F m i := by
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  apply LinearMap.ext
  intro v
  change T F m i (T F m i v) + T F m i v + v = E F m i v
  rw [T_apply hcard, T_apply hcard, E_apply]
  ext j
  rcases j with k | k <;> by_cases hk : k = i
  · subst k
    simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    ring_nf
    linear_combination (6 * v (Sum.inl i) + 3 * v (Sum.inr i)) * h2
  · simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hk]
    ring_nf
    linear_combination (v (Sum.inl k)) * h2
  · subst k
    simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    ring_nf
    linear_combination (3 * v (Sum.inl i) + 3 * v (Sum.inr i)) * h2
  · simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hk]
    ring_nf
    linear_combination (v (Sum.inr k)) * h2

end GGPlaneA
end CFSG.StandardType

namespace CFSG.StandardType
namespace GGPlaneA
open CFSG.Assembly
variable {F : Type} [Field F] [Finite F] {m : ℕ}

noncomputable def tauLE (F : Type) [Field F] (m : ℕ) (i j : Fin m) :
    (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) :=
  CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F (tauGL F m i j)

lemma tauLE_apply (i j : Fin m) (v : Fin m ⊕ Fin m → F) :
    tauLE F m i j v = v ∘ ⇑(Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j))⁻¹ := by
  rw [tauLE, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, tauGL,
    TableBSymp.permutationGL_mulVec]

lemma tauLE_sq (hcard : Nat.card F = 2) (i j : Fin m) :
    tauLE F m i j * tauLE F m i j = 1 := by
  have h := tauGL_sq (F := F) (m := m) i j
  rw [tauLE, ← map_mul, h, map_one]

lemma tauLE_coord_inr (hcard : Nat.card F = 2) {i j : Fin m} (hij : i ≠ j)
    (v : Fin m ⊕ Fin m → F) :
    tauLE F m i j v (Sum.inr i) = v (Sum.inr j) := by
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  rw [tauLE_apply]
  have hπ : (Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j))⁻¹ (Sum.inr i) =
      Sum.inr j := by
    rw [Equiv.Perm.sumCongr_inv, Equiv.swap_inv]
    simp [Equiv.Perm.sumCongr_apply, Equiv.swap_apply_left]
  rw [Function.comp_apply, hπ]

noncomputable def S (F : Type) [Field F] (m : ℕ) (i j : Fin m) :
    GL (Fin m ⊕ Fin m) F :=
  ⁅aGL F m i, tauGL F m i j⁆

noncomputable def SL (F : Type) [Field F] (m : ℕ) (i j : Fin m) :
    (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) :=
  CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F (S F m i j)

lemma S_eq (hcard : Nat.card F = 2) (i j : Fin m) :
    SL F m i j = A F m i * tauLE F m i j * A F m i * tauLE F m i j := by
  have ha : (aGL F m i)⁻¹ = aGL F m i := inv_eq_of_mul_eq_one_right (aGL_sq hcard i)
  have hτ : (tauGL F m i j)⁻¹ = tauGL F m i j :=
    inv_eq_of_mul_eq_one_right (tauGL_sq i j)
  simp only [SL, S, commutatorElement_def, A, tauLE, ha, hτ, map_mul, map_inv]

lemma SL_apply_of_supported (hcard : Nat.card F = 2) {i j : Fin m} (hij : i ≠ j)
    {v : Fin m ⊕ Fin m → F} (hv : ggFusionPlaneSupported m i v) :
    SL F m i j v = A F m i v := by
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  have hj : v (Sum.inr j) = 0 := (hv j hij.symm).2
  have hA : A F m i (tauLE F m i j v) = tauLE F m i j v := by
    rw [A_apply, tauLE_coord_inr hcard hij, hj, zero_smul, add_zero]
  rw [S_eq hcard, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hA]
  have hττ : tauLE F m i j (tauLE F m i j v) = v := by
    have h := tauLE_sq hcard i j
    have := congrArg (fun e : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) => e v) h
    simpa [LinearEquiv.mul_apply] using this
  rw [hττ]

end GGPlaneA
end CFSG.StandardType

namespace CFSG.StandardType
namespace GGPlaneA
open CFSG.Assembly
variable {F : Type} [Field F] [Finite F] {m : ℕ}

lemma S_mem (hcard : Nat.card F = 2) (i j : Fin m) :
    S F m i j ∈ ⁅LargeEvenOrthGroup (ggFusionPlaneQuadratic F m),
      LargeEvenOrthGroup (ggFusionPlaneQuadratic F m)⁆ :=
  Subgroup.commutator_mem_commutator (aGL_mem hcard i) (tauGL_mem hcard i j)

lemma one_add_one_eq_zero (hcard : Nat.card F = 2) : (1 : F) + 1 = 0 := by
  rw [show (1 : F) + 1 = (2 : F) by norm_num, two_eq_zero hcard]

lemma E_e (hcard : Nat.card F = 2) (i : Fin m) :
    E F m i (e (F := F) i) = 0 := by
  ext k
  by_cases hk : k = Sum.inl i <;>
    simp [E_apply, e, Pi.single_apply, hk, one_add_one_eq_zero hcard]

lemma E_f (hcard : Nat.card F = 2) (i : Fin m) :
    E F m i (f (F := F) i) = 0 := by
  ext k
  by_cases hk : k = Sum.inr i <;>
    simp [E_apply, f, Pi.single_apply, hk, one_add_one_eq_zero hcard]

lemma supported_of_E_eq_zero (hcard : Nat.card F = 2) {i : Fin m}
    {w : Fin m ⊕ Fin m → F} (hw : E F m i w = 0) :
    ggFusionPlaneSupported m i w := by
  intro j hj
  constructor
  · have h := congrFun hw (Sum.inl j)
    have h1 : (Sum.inl j : Fin m ⊕ Fin m) ≠ Sum.inl i := by simpa using hj
    have h2 : (Sum.inl j : Fin m ⊕ Fin m) ≠ Sum.inr i := by simp
    simpa [E_apply, e, f, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2] using h
  · have h := congrFun hw (Sum.inr j)
    have h1 : (Sum.inr j : Fin m ⊕ Fin m) ≠ Sum.inr i := by simpa using hj
    have h2 : (Sum.inr j : Fin m ⊕ Fin m) ≠ Sum.inl i := by simp
    simpa [E_apply, e, f, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2] using h

end GGPlaneA
end CFSG.StandardType

namespace CFSG.StandardType
namespace GGPlaneA
open CFSG.Assembly
variable {F : Type} [Field F] [Finite F] {m : ℕ}

lemma tGL_mem (hcard : Nat.card F = 2) (i : Fin m) :
    tGL F m i ∈ ⁅LargeEvenOrthGroup (ggFusionPlaneQuadratic F m),
      LargeEvenOrthGroup (ggFusionPlaneQuadratic F m)⁆ :=
  Subgroup.commutator_mem_commutator (aGL_mem hcard i) (bGL_mem hcard i)

lemma e_supported (i : Fin m) : ggFusionPlaneSupported m i (e (F := F) i) := by
  intro j hj
  constructor
  · have h1 : (Sum.inl j : Fin m ⊕ Fin m) ≠ Sum.inl i := by simpa using hj
    simp [e, Pi.single_eq_of_ne h1]
  · have h1 : (Sum.inr j : Fin m ⊕ Fin m) ≠ Sum.inl i := by simp
    simp [e, Pi.single_eq_of_ne h1]

lemma eq_smul_e_of_supported_of_inr_eq_zero (hcard : Nat.card F = 2) {i : Fin m}
    {w : Fin m ⊕ Fin m → F} (hw : ggFusionPlaneSupported m i w)
    (h0 : w (Sum.inr i) = 0) :
    w = w (Sum.inl i) • e (F := F) i := by
  ext k
  rcases k with k | k
  · by_cases hk : k = i
    · subst hk
      simp [e, Pi.single_eq_same]
    · have h1 : (Sum.inl k : Fin m ⊕ Fin m) ≠ Sum.inl i := by simpa using hk
      have h2 : (Sum.inl k : Fin m ⊕ Fin m) ≠ Sum.inr i := by simp
      simp [e, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, (hw k hk).1]
  · by_cases hk : k = i
    · subst hk
      simp [e, h0]
    · have h1 : (Sum.inr k : Fin m ⊕ Fin m) ≠ Sum.inl i := by simp
      simp [e, Pi.single_eq_of_ne h1, (hw k hk).2]

lemma T_T_e (hcard : Nat.card F = 2) (i : Fin m) :
    T F m i (T F m i (e (F := F) i)) = f (F := F) i := by
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  rw [T_apply hcard, T_apply hcard]
  ext k
  rcases k with k | k <;> by_cases hk : k = i
  · subst hk
    simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply, one_add_one_eq_zero hcard]
  · simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hk]
  · subst hk
    simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply, one_add_one_eq_zero hcard]
  · simp [e, f, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hk]

end GGPlaneA
end CFSG.StandardType

namespace CFSG.StandardType
namespace GGPlaneA
open CFSG.Assembly
variable {F : Type} [Field F] [Finite F] {m : ℕ}

lemma e_ne_zero (i : Fin m) : e (F := F) i ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl i)
  simp [e] at this

theorem eq_one_of_commute_aux (hcard : Nat.card F = 2) (hm : 2 ≤ m)
    (g : GL (Fin m ⊕ Fin m) F)
    (hg : ∀ w ∈ ⁅LargeEvenOrthGroup (ggFusionPlaneQuadratic F m),
        LargeEvenOrthGroup (ggFusionPlaneQuadratic F m)⁆, g * w = w * g) :
    g = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) = 0 := two_eq_zero hcard
  let Ge : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F g
  have hTcomm (i : Fin m) : Ge * T F m i = T F m i * Ge := by
    have h := hg (tGL F m i) (tGL_mem hcard i)
    have := congrArg (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F) h
    simpa [Ge, T, tGL, map_mul] using this
  have hEcomm (i : Fin m) :
      (Ge : Module.End F (Fin m ⊕ Fin m → F)) * E F m i =
        E F m i * (Ge : Module.End F (Fin m ⊕ Fin m → F)) := by
    have hpoly := T_sq_add_T_add_one_eq_E hcard i
    have hcomm : (Ge : Module.End F (Fin m ⊕ Fin m → F)) *
        (T F m i : Module.End F (Fin m ⊕ Fin m → F)) =
        (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
          (Ge : Module.End F (Fin m ⊕ Fin m → F)) := by
      exact congrArg (fun e : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) =>
        (e : Module.End F (Fin m ⊕ Fin m → F))) (hTcomm i)
    calc (Ge : Module.End F (Fin m ⊕ Fin m → F)) * E F m i
        = (Ge : Module.End F (Fin m ⊕ Fin m → F)) *
            ((T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                (T F m i : Module.End F (Fin m ⊕ Fin m → F)) +
              (T F m i : Module.End F (Fin m ⊕ Fin m → F)) + 1) := by rw [hpoly]
      _ = ((T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                (T F m i : Module.End F (Fin m ⊕ Fin m → F)) +
              (T F m i : Module.End F (Fin m ⊕ Fin m → F)) + 1) *
            (Ge : Module.End F (Fin m ⊕ Fin m → F)) := by
            calc (Ge : Module.End F (Fin m ⊕ Fin m → F)) *
                ((T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                    (T F m i : Module.End F (Fin m ⊕ Fin m → F)) +
                  (T F m i : Module.End F (Fin m ⊕ Fin m → F)) + 1)
                = (Ge : Module.End F (Fin m ⊕ Fin m → F)) *
                    (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                    (T F m i : Module.End F (Fin m ⊕ Fin m → F)) +
                  (Ge : Module.End F (Fin m ⊕ Fin m → F)) *
                    (T F m i : Module.End F (Fin m ⊕ Fin m → F)) +
                  (Ge : Module.End F (Fin m ⊕ Fin m → F)) := by noncomm_ring
              _ = (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                    (Ge : Module.End F (Fin m ⊕ Fin m → F)) *
                    (T F m i : Module.End F (Fin m ⊕ Fin m → F)) +
                  (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                    (Ge : Module.End F (Fin m ⊕ Fin m → F)) +
                  (Ge : Module.End F (Fin m ⊕ Fin m → F)) := by rw [hcomm]
              _ = (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                    ((T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                      (Ge : Module.End F (Fin m ⊕ Fin m → F))) +
                  (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                    (Ge : Module.End F (Fin m ⊕ Fin m → F)) +
                  (Ge : Module.End F (Fin m ⊕ Fin m → F)) := by
                    rw [show (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                        (Ge : Module.End F (Fin m ⊕ Fin m → F)) *
                        (T F m i : Module.End F (Fin m ⊕ Fin m → F)) =
                      (T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                        ((T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                          (Ge : Module.End F (Fin m ⊕ Fin m → F))) by
                        rw [mul_assoc, hcomm]]
              _ = ((T F m i : Module.End F (Fin m ⊕ Fin m → F)) *
                    (T F m i : Module.End F (Fin m ⊕ Fin m → F)) +
                  (T F m i : Module.End F (Fin m ⊕ Fin m → F)) + 1) *
                    (Ge : Module.End F (Fin m ⊕ Fin m → F)) := by noncomm_ring
      _ = E F m i * (Ge : Module.End F (Fin m ⊕ Fin m → F)) := by rw [hpoly]
  have hsupp_e (i : Fin m) :
      ggFusionPlaneSupported m i (Ge (e (F := F) i)) := by
    apply supported_of_E_eq_zero hcard
    have h := congrArg (fun f : Module.End F (Fin m ⊕ Fin m → F) => f (e (F := F) i))
      (hEcomm i)
    rw [Module.End.mul_apply, Module.End.mul_apply, E_e hcard i] at h
    simpa using h.symm
  have hsupp_f (i : Fin m) :
      ggFusionPlaneSupported m i (Ge (f (F := F) i)) := by
    apply supported_of_E_eq_zero hcard
    have h := congrArg (fun L : Module.End F (Fin m ⊕ Fin m → F) => L (f (F := F) i))
      (hEcomm i)
    rw [Module.End.mul_apply, Module.End.mul_apply, E_f hcard i] at h
    simpa using h.symm
  have hScomm (i j : Fin m) : Ge * SL F m i j = SL F m i j * Ge := by
    have h := hg (S F m i j) (S_mem hcard i j)
    have := congrArg (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F) h
    simpa [Ge, SL, S, map_mul] using this
  have h_e (i : Fin m) : Ge (e (F := F) i) = e (F := F) i := by
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    obtain ⟨j, hji⟩ := exists_ne i
    have hSL_e : SL F m i j (e (F := F) i) = e (F := F) i := by
      rw [SL_apply_of_supported hcard hji.symm (e_supported i), A_apply]
      simp [e]
    have h1 : Ge (e (F := F) i) = SL F m i j (Ge (e (F := F) i)) := by
      have h := congrArg (fun f : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) =>
        f (e (F := F) i)) (hScomm i j)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hSL_e] at h
      exact h
    have hAfix : A F m i (Ge (e (F := F) i)) = Ge (e (F := F) i) := by
      calc A F m i (Ge (e (F := F) i)) = SL F m i j (Ge (e (F := F) i)) :=
            (SL_apply_of_supported hcard hji.symm (hsupp_e i)).symm
        _ = Ge (e (F := F) i) := h1.symm
    have h0 : Ge (e (F := F) i) (Sum.inr i) = 0 := by
      have hw := congrArg (fun w : Fin m ⊕ Fin m → F => w (Sum.inl i)) hAfix
      simp only [A_apply, Pi.add_apply, Pi.smul_apply, e, Pi.single_eq_same, smul_eq_mul,
        mul_one, one_mul] at hw
      have hw' : Ge (e (F := F) i) (Sum.inl i) + Ge (e (F := F) i) (Sum.inr i) =
          Ge (e (F := F) i) (Sum.inl i) + 0 := by simpa [e] using hw
      simpa using add_left_cancel hw'
    have hw := eq_smul_e_of_supported_of_inr_eq_zero hcard (hsupp_e i) h0
    have hc_ne : Ge (e (F := F) i) (Sum.inl i) ≠ 0 := by
      intro hc
      have hzero : Ge (e (F := F) i) = 0 := by
        rw [hw, hc, zero_smul]
      have he0 : e (F := F) i = 0 := Ge.injective (by simpa [hzero])
      exact e_ne_zero (F := F) i he0
    rcases CFSG.StandardType.OrthRest.eq_zero_or_eq_one_of_card_two hcard
      (Ge (e (F := F) i) (Sum.inl i)) with hc | hc
    · exact absurd hc hc_ne
    · rw [hw, hc, one_smul]
  have h_f (i : Fin m) : Ge (f (F := F) i) = f (F := F) i := by
    have hTapply : ∀ v, Ge (T F m i v) = T F m i (Ge v) := by
      intro v
      have h := congrArg (fun e : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F) => e v)
        (hTcomm i)
      simpa [LinearEquiv.mul_apply] using h
    calc Ge (f (F := F) i) = Ge (T F m i (T F m i (e (F := F) i))) := by rw [T_T_e hcard i]
      _ = T F m i (Ge (T F m i (e (F := F) i))) := hTapply _
      _ = T F m i (T F m i (Ge (e (F := F) i))) := by rw [hTapply]
      _ = T F m i (T F m i (e (F := F) i)) := by rw [h_e]
      _ = f (F := F) i := T_T_e hcard i
  have hG1 : Ge = 1 := by
    apply LinearEquiv.toLinearMap_injective
    apply Module.Basis.ext (Pi.basisFun F (Fin m ⊕ Fin m))
    intro k
    rcases k with k | k
    · simpa [Pi.basisFun_apply, e] using h_e k
    · simpa [Pi.basisFun_apply, f] using h_f k
  have hgl : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F g = 1 := by
    simpa [Ge] using hG1
  exact (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) F).injective
    (by simpa using hgl)

end GGPlaneA
end CFSG.StandardType

namespace CFSG.StandardType

public theorem ggFusionPlane_eq_one_of_commute {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {m : ℕ} (hm : 2 ≤ m) {g : GL (Fin m ⊕ Fin m) F}
    (hg : ∀ w ∈ ⁅LargeEvenOrthGroup (ggFusionPlaneQuadratic F m),
      LargeEvenOrthGroup (ggFusionPlaneQuadratic F m)⁆, g * w = w * g) : g = 1 :=
  GGPlaneA.eq_one_of_commute_aux hF hm g hg

end CFSG.StandardType
