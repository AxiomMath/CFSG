module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClSpInv
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame
public import CFSG.Sporadic.Suz.Setup
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.Sporadic.Suz.W64Spec

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace WitSpNs

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped MatrixGroups

section RootMat

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

@[expose] noncomputable def rootMat (b : Module.Basis (Fin 2) K L) (ζ : L) :
    Matrix (Fin 2) (Fin 2) K :=
  LinearMap.toMatrix b b (Algebra.lmul K L ζ)

theorem rootMat_pow (b : Module.Basis (Fin 2) K L) (ζ : L) (m : ℕ) :
    rootMat b ζ ^ m = rootMat b (ζ ^ m) := by
  rw [rootMat, rootMat, LinearMap.toMatrix_pow, map_pow (Algebra.lmul K L) ζ m]

theorem rootMat_one (b : Module.Basis (Fin 2) K L) : rootMat b 1 = 1 := by
  rw [rootMat, map_one, LinearMap.toMatrix_one]

theorem repr_mul_basis (b : Module.Basis (Fin 2) K L) (ζ : L) (a c : Fin 2) :
    b.repr (ζ * b c) a = rootMat b ζ a c := by
  rw [rootMat, LinearMap.toMatrix_apply]
  rfl

theorem mul_basis (b : Module.Basis (Fin 2) K L) (ζ : L) (c : Fin 2) :
    ζ * b c = rootMat b ζ 0 c • b 0 + rootMat b ζ 1 c • b 1 := by
  rw [← repr_mul_basis, ← repr_mul_basis]
  have h := b.sum_repr (ζ * b c)
  rw [Fin.sum_univ_two] at h
  exact h.symm

theorem det_rootMat (b : Module.Basis (Fin 2) K L) (ζ : L) :
    (rootMat b ζ).det = Algebra.norm K ζ := by
  rw [rootMat, LinearMap.det_toMatrix]
  rfl

theorem isUnit_rootMat_pow_sub [Finite K] [FiniteDimensional K L] {p : ℕ} (hp : p.Prime)
    (hK : ¬ p ∣ Nat.card K - 1) (b : Module.Basis (Fin 2) K L) {ζ : L} (hζp : ζ ^ p = 1)
    (hζ1 : ζ ≠ 1) (j : ℕ) (hj : ¬ p ∣ j) (c : K) : IsUnit (rootMat b ζ ^ j - c • 1) := by
  refine SpNS.isUnit_toMatrix_pow_sub hp hK b (c := Algebra.lmul K L ζ)
    (by rw [← map_pow, hζp, map_one]) (fun d hd => ?_) j hj c
  have h1 : (ζ - 1) * d = 0 := by
    have : ζ * d = d := hd
    rw [sub_mul, this, one_mul, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hζ1)

end RootMat

section Frame

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V} {L : Type} [AddCommGroup L] [Module K L] {s : ℕ} {κ : Type}
  {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K L}

theorem frame_form_single
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (k l : Fin s) (x y : L) :
    B (Φ (Pi.single k x, 0)) (Φ (Pi.single l y, 0)) = if k = l then β x y else 0 := by
  classical
  rw [hdec, Prod.mk_zero_zero, map_zero, LinearMap.map_zero₂, add_zero,
    Finset.sum_eq_single k (fun i _ hi => by rw [Pi.single_eq_of_ne hi, LinearMap.map_zero₂])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same]
  by_cases hkl : k = l
  · subst hkl
    rw [Pi.single_eq_same, ite_eq_left rfl]
  · rw [Pi.single_eq_of_ne hkl, map_zero, ite_eq_right hkl]

theorem frame_form_zero_left
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (w : κ → K) (d' : Fin s → L) (w' : κ → K) :
    B (Φ (0, w)) (Φ (d', w')) = B (Φ (0, w)) (Φ (0, w')) := by
  rw [hdec]
  simp

theorem frame_block_nondegenerate (hnd : B.Nondegenerate)
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (k : Fin s) (u : L) (hu : ∀ v, β u v = 0) : u = 0 := by
  classical
  have h1 : ∀ y : V, B (Φ (Pi.single k u, 0)) y = 0 := by
    intro y
    obtain ⟨⟨d', w'⟩, rfl⟩ := Φ.surjective y
    rw [hdec, Prod.mk_zero_zero, map_zero, LinearMap.map_zero₂, add_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hik : i = k
    · subst hik
      rw [Pi.single_eq_same, hu]
    · rw [Pi.single_eq_of_ne hik, LinearMap.map_zero₂]
  have h2 := hnd.1 _ h1
  have h3 : ((Pi.single k u : Fin s → L), (0 : κ → K)) = 0 :=
    Φ.injective (h2.trans (map_zero Φ).symm)
  have h4 := congrArg (fun z : (Fin s → L) × (κ → K) => z.1 k) h3
  simpa using h4

end Frame

section Empty

variable {K : Type} [Field K] {n p : ℕ} {X' κ : Type} [AddCommGroup X'] [Module K X']

theorem isEmpty_of_frame (hn : 1 ≤ n) (Φ : (X' × (κ → K)) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (horth : ∀ w d' w', form (Φ (0, w)) (Φ (d', w')) = form (Φ (0, w)) (Φ (0, w')))
    (P : StatedSp n K → Prop) (hfix : ∀ X, P X → ∀ w, mat n K X *ᵥ Φ (0, w) = Φ (0, w))
    (hmax : ∀ Y : StatedSp n K, (∀ X, P X → Commute Y X) → Y ^ p = 1 → P Y)
    (T : SL(2, K)) (hTp : T ^ p = 1)
    (hT : ¬ ((T : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∧ (T : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)) :
    IsEmpty κ := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_contra hne
  rw [not_isEmpty_iff] at hne
  obtain ⟨k₀⟩ := hne
  set a := Φ (0, Pi.single k₀ 1) with ha
  have ha0 : a ≠ 0 := by
    intro h
    have h1 : ((0 : X'), (Pi.single k₀ (1 : K) : κ → K)) = 0 :=
      Φ.injective (by rw [← ha, h, map_zero])
    have h2 := congrArg (fun z : X' × (κ → K) => z.2 k₀) h1
    simp at h2
  obtain ⟨c, hc⟩ : ∃ c, a c ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 (funext h)
  have hav : form a (Pi.single (par c) 1) ≠ 0 := by
    rw [form_single_right, par_par]
    exact mul_ne_zero hc (sgn_ne_zero c)
  obtain ⟨⟨d', w'⟩, hdw⟩ := Φ.surjective (Pi.single (par c) 1)
  have hab' : form a (Φ (0, w')) ≠ 0 := by
    rw [ha, ← horth _ d', hdw]
    exact hav
  set b := (form a (Φ (0, w')))⁻¹ • Φ (0, w') with hb
  have hab : form a b = 1 := by
    rw [hb, form_smul_right, inv_mul_cancel₀ hab']
  obtain ⟨g, hg₁, hg₂⟩ := exists_sp_apply_eq a b hab
  set Y := g * longBlock K (m + 1) 0 T * g⁻¹ with hY
  have hfixab : ∀ X, P X → mat (m + 1) K X *ᵥ a = a ∧ mat (m + 1) K X *ᵥ b = b := by
    intro X hX
    refine ⟨hfix X hX _, ?_⟩
    rw [hb, Matrix.mulVec_smul, hfix X hX]
  have hcomm : ∀ X, P X → Commute Y X := by
    intro X hX
    have h₁ : mat (m + 1) K (g⁻¹ * X * g) *ᵥ Pi.single (Sum.inl 0) 1 =
        Pi.single (Sum.inl 0) 1 := by
      rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg₁,
        (hfixab X hX).1, ← hg₁, mulVec_inv_mulVec]
    have h₂ : mat (m + 1) K (g⁻¹ * X * g) *ᵥ Pi.single (Sum.inr 0) 1 =
        Pi.single (Sum.inr 0) 1 := by
      rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg₂,
        (hfixab X hX).2, ← hg₂, mulVec_inv_mulVec]
    have hc := (WitClSp.commute_longBlock_of_fix h₁ h₂ T).eq
    show Y * X = X * Y
    calc Y * X = g * (longBlock K (m + 1) 0 T * (g⁻¹ * X * g)) * g⁻¹ := by rw [hY]; group
      _ = g * ((g⁻¹ * X * g) * longBlock K (m + 1) 0 T) * g⁻¹ := by rw [hc]
      _ = X * Y := by rw [hY]; group
  have hYp : Y ^ p = 1 := by
    rw [hY, conj_pow, ← map_pow, hTp, map_one, mul_one, mul_inv_cancel]
  have hYa := (hfixab Y (hmax Y hcomm hYp)).1
  have he : mat (m + 1) K (longBlock K (m + 1) 0 T) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inl 0) 1 := by
    have h1 : mat (m + 1) K g⁻¹ *ᵥ a = Pi.single (Sum.inl 0) 1 := by
      rw [← hg₁, mulVec_inv_mulVec]
    rw [hY, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1] at hYa
    have h2 := congrArg (fun v => mat (m + 1) K g⁻¹ *ᵥ v) hYa
    simp only [mulVec_inv_mulVec] at h2
    rw [h2, h1]
  rw [mat_longBlock_eq_planeMat, planeMat_mulVec_inl, Function.update_self] at he
  apply hT
  constructor
  · have := congrFun he (Sum.inl 0)
    simpa using this
  · have := congrFun he (Sum.inr 0)
    simpa using this

end Empty

section Core

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical (spEnd spLin spLin_injective spLin_mem spForm_isAlt
  spForm_nondegenerate range_spLin)

variable {K : Type} [Field K] {n : ℕ}

theorem spEnd_mul (X X' : StatedSp n K) : spEnd (X * X') = spEnd X * spEnd X' := by
  show Units.val (spLin n K (X * X')) = Units.val (spLin n K X) * Units.val (spLin n K X')
  rw [map_mul, Units.val_mul]

theorem spEnd_pow (X : StatedSp n K) (m : ℕ) : spEnd (X ^ m) = spEnd X ^ m := by
  show Units.val (spLin n K (X ^ m)) = Units.val (spLin n K X) ^ m
  rw [map_pow, Units.val_pow_eq_pow_val]

theorem spEnd_injective : Function.Injective (spEnd (r := n) (K := K)) := fun _ _ h =>
  spLin_injective (Units.ext h)

theorem spEnd_eq_mulVec (X : StatedSp n K) (v : Fin n ⊕ Fin n → K) :
    spEnd X v = mat n K X *ᵥ v := rfl

theorem spForm_eq_form (u v : Fin n ⊕ Fin n → K) :
    CFSG.RankThree.Classical.spForm n K u v = form u v := by
  rw [CFSG.RankThree.Classical.spForm_apply]
  rfl

theorem mul_single_eq {L : Type} [Field L] {s : ℕ} (c : Fin s → L) (j : Fin s) (x : L) :
    (fun i => c i * (Pi.single j x : Fin s → L) i) = Pi.single j (c j * x) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Pi.single_eq_of_ne hij]

theorem frame_single_comb {V L κ : Type} [AddCommGroup V] [Module K V] [AddCommGroup L]
    [Module K L] {s : ℕ} (Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V) (j : Fin s) (a c : K) (x y : L) :
    Φ (Pi.single j (a • x + c • y), 0) =
      a • Φ (Pi.single j x, 0) + c • Φ (Pi.single j y, 0) := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  refine Prod.ext ?_ (by simp)
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Pi.single_eq_of_ne hij]

end Core

end WitSpNs

end CFSG.StandardType
