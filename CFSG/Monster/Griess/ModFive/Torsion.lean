module

public import CFSG.Monster.Griess.ModFive.Lattice

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess.ModFive

open CFSG.Monster CFSG.Monster.Spin Matrix Module Classical

theorem basisB_repr_inl (v : SpaceB) (z : PairIdx) :
    basisB.repr v (Sum.inl z) = symEntry v.1 z := by
  rw [basisB, Basis.prod_repr_inl, basisA, Basis.ofEquivFun_repr_apply]
  rfl

theorem basisB_repr_inr_inl (v : SpaceB) (c : ShortIdx) :
    basisB.repr v (Sum.inr (Sum.inl c)) = v.2.1 c := by
  rw [basisB, Basis.prod_repr_inr, Basis.prod_repr_inl, Pi.basisFun_repr]

theorem basisB_repr_inr_inr (v : SpaceB) (a : SpinIdx) (i : Fin 24) :
    basisB.repr v (Sum.inr (Sum.inr (a, i))) = v.2.2 a i := by
  rw [basisB, Basis.prod_repr_inr, Basis.prod_repr_inr]
  simp [Matrix.stdBasis]

theorem basisB_repr_mem_R5 {v : SpaceB} (hv : v ∈ L5) (k : BIdx) : basisB.repr v k ∈ R5 := by
  rcases k with z | c | ⟨a, i⟩
  · rw [basisB_repr_inl]
    induction z using Sym2.ind with | h i j => rw [symEntry_mk]; exact hv.1 i j
  · rw [basisB_repr_inr_inl]
    exact hv.2.1 c
  · rw [basisB_repr_inr_inr]
    exact hv.2.2 a i

theorem basisB_repr_mem_D5 {v : SpaceB} (hv : v ∈ M5) (k : BIdx) : basisB.repr v k ∈ D5 := by
  rcases k with z | c | ⟨a, i⟩
  · rw [basisB_repr_inl]
    induction z using Sym2.ind with | h i j => rw [symEntry_mk]; exact hv.1 i j
  · rw [basisB_repr_inr_inl]
    exact hv.2.1 c
  · rw [basisB_repr_inr_inr]
    exact hv.2.2 a i

theorem basisB_mem_L5 (k : BIdx) : basisB k ∈ L5 := by
  obtain ⟨h1, h2, h3⟩ := isDyadicVec_basisB k
  exact ⟨fun i j => dyadic_le_R5 (h1 i j), fun c => dyadic_le_R5 (h2 c),
    fun j i => dyadic_le_R5 (h3 j i)⟩

noncomputable def matR5 (f : SpaceB →ₗ[ℚ] SpaceB) (hf : ∀ v ∈ L5, f v ∈ L5) :
    Matrix BIdx BIdx R5 :=
  Matrix.of fun i j => ⟨LinearMap.toMatrixAlgEquiv basisB f i j, by
    rw [LinearMap.toMatrixAlgEquiv_apply]
    exact basisB_repr_mem_R5 (hf _ (basisB_mem_L5 j)) i⟩

theorem map_matR5 (f : SpaceB →ₗ[ℚ] SpaceB) (hf : ∀ v ∈ L5, f v ∈ L5) :
    (R5.subtype).mapMatrix (matR5 f hf) = LinearMap.toMatrixAlgEquiv basisB f := by
  ext i j
  rfl

theorem mapMatrix_subtype_injective :
    Function.Injective ((R5.subtype).mapMatrix : Matrix BIdx BIdx R5 → Matrix BIdx BIdx ℚ) :=
  fun _ _ h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)

theorem pow_mem_L5 {g : SpaceB ≃ₗ[ℚ] SpaceB} (hL : ∀ v ∈ L5, g v ∈ L5) (n : ℕ) :
    ∀ v ∈ L5, (g ^ n) v ∈ L5 := by
  induction n with
  | zero => exact fun v hv => hv
  | succ n ih =>
    intro v hv
    rw [pow_succ, LinearEquiv.mul_apply]
    exact ih _ (hL v hv)

theorem eq_one_of_sub_mem_M5 {g : SpaceB ≃ₗ[ℚ] SpaceB} (hfin : IsOfFinOrder g)
    (hL : ∀ v ∈ L5, g v ∈ L5) (h1 : ∀ v ∈ L5, g v - v ∈ M5) : g = 1 := by
  classical
  set n := orderOf g with hn
  have hn0 : 0 < n := hfin.orderOf_pos
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  have hsymm : g.symm = g ^ (n - 1) := by
    have h : g ^ (n - 1) * g = 1 := by rw [← pow_succ, Nat.sub_add_cancel hn0, hgn]
    exact (eq_inv_of_mul_eq_one_left h).symm
  have hL' : ∀ v ∈ L5, g.symm v ∈ L5 := by
    rw [hsymm]
    exact pow_mem_L5 hL _
  let ψ : (SpaceB ≃ₗ[ℚ] SpaceB) →* Matrix BIdx BIdx ℚ :=
    (LinearMap.toMatrixAlgEquiv basisB).toAlgHom.toRingHom.toMonoidHom.comp
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hψ : ∀ f : SpaceB ≃ₗ[ℚ] SpaceB, ψ f = LinearMap.toMatrixAlgEquiv basisB f.toLinearMap :=
    fun _ => rfl
  have hψinj : Function.Injective ψ := fun f f' h => by
    rw [hψ, hψ] at h
    exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrixAlgEquiv basisB).injective h)
  obtain ⟨M, hM⟩ : ∃ M, M = matR5 g.toLinearMap hL := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M', M' = matR5 g.symm.toLinearMap hL' := ⟨_, rfl⟩
  have hinv : g.symm = g⁻¹ := rfl
  have hMM' : M * M' = 1 := mapMatrix_subtype_injective (by
    rw [map_mul, map_one, hM, hM', map_matR5, map_matR5, ← hψ, ← hψ, ← map_mul, hinv,
      mul_inv_cancel, map_one])
  have hM'M : M' * M = 1 := mapMatrix_subtype_injective (by
    rw [map_mul, map_one, hM, hM', map_matR5, map_matR5, ← hψ, ← hψ, ← map_mul, hinv,
      inv_mul_cancel, map_one])
  let u : GL BIdx R5 := ⟨M, M', hMM', hM'M⟩
  have hu : (R5.subtype).mapMatrix (u : Matrix BIdx BIdx R5) = ψ g := by
    change (R5.subtype).mapMatrix M = _
    rw [hM, map_matR5]
    rfl
  have hupow : ∀ k : ℕ, (R5.subtype).mapMatrix ((u ^ k : GL BIdx R5) : Matrix BIdx BIdx R5) =
      ψ (g ^ k) := fun k => by
    rw [Units.val_pow_eq_pow_val, map_pow, hu, map_pow]
  have hfinu : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn0, Units.ext
    (mapMatrix_subtype_injective (by rw [hupow, hgn, map_one, Units.val_one, map_one]))⟩
  have hred : Matrix.GeneralLinearGroup.map (ratLocalRed 5) u = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hD : ((M i j : R5) : ℚ) - (((1 : Matrix BIdx BIdx R5) i j : R5) : ℚ) ∈ D5 := by
      have e1 : ((M i j : R5) : ℚ) = basisB.repr (g (basisB j)) i := by
        rw [hM]
        change LinearMap.toMatrixAlgEquiv basisB g.toLinearMap i j = _
        rw [LinearMap.toMatrixAlgEquiv_apply]
        rfl
      have e2 : (((1 : Matrix BIdx BIdx R5) i j : R5) : ℚ) = basisB.repr (basisB j) i := by
        rw [Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
        rcases eq_or_ne i j with rfl | h
        · simp
        · simp [h, h.symm]
      rw [e1, e2, ← Finsupp.sub_apply, ← map_sub]
      exact basisB_repr_mem_D5 (h1 _ (basisB_mem_L5 j)) i
    have h0 : ratLocalRed 5 (M i j - (1 : Matrix BIdx BIdx R5) i j) = 0 :=
      (ratLocalRed_eq_zero_iff_mem_D5 _).2 hD
    rw [map_sub, sub_eq_zero] at h0
    change ratLocalRed 5 (M i j) = ((1 : GL BIdx (ZMod 5)) : Matrix BIdx BIdx (ZMod 5)) i j
    rw [h0, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  have hu1 : u = 1 :=
    ((odd_prime_congruence_torsion_free 5 (by norm_num) BIdx).1 u hred hfinu)
  refine hψinj ?_
  rw [← hu, hu1, map_one, Units.val_one, map_one]

end CFSG.Monster.Griess.ModFive
