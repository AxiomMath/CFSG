module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open QuadraticMap CFSG.ComponentClassification.UnbalancedCatalog

section Symmetries

variable {K : Type} [Field K] [CharP K 2] {m : ℕ} {Q : QuadraticForm K (Fin m → K)}

private theorem polar_self_charTwo (x : Fin m → K) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

omit [CharP K 2] in
private theorem ne_zero_of_map_eq_one {x : Fin m → K} (hx : Q x = 1) : x ≠ 0 := by
  rintro rfl
  rw [QuadraticMap.map_zero] at hx
  exact zero_ne_one hx

private theorem symmetryGL_commute_iff (hQ : Q.polarBilin.Nondegenerate) {x y : Fin m → K}
    (hx : Q x = 1) (hy : Q y = 1) :
    symmetryGL Q x * symmetryGL Q y = symmetryGL Q y * symmetryGL Q x ↔ polar Q x y = 0 := by
  have h := mem_centralizer_symmetryGL_iff hQ hy (symmetryGL_mem Q x)
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  rw [h, symmetryGL_mulVec_of_charTwo hx, add_eq_left, smul_eq_zero]
  simp [ne_zero_of_map_eq_one hx]

private theorem orderOf_symmetryGL_mul (hQ : Q.polarBilin.Nondegenerate) {x y : Fin m → K}
    (hx : Q x = 1) (hy : Q y = 1) (hxy : polar Q x y = 1) :
    orderOf (symmetryGL Q x * symmetryGL Q y) = 3 := by
  have hyx : polar Q y x = 1 := by rw [polar_comm]; exact hxy
  have hinv : ∀ z : Fin m → K, (symmetryGL Q z)⁻¹ = symmetryGL Q z := fun z =>
    inv_eq_of_mul_eq_one_right (symmetryGL_mul_self Q z)
  have h1 : symmetryGL Q x * symmetryGL Q y * symmetryGL Q x = symmetryGL Q (y + x) := by
    have h := conj_symmetryGL (v := y) (symmetryGL_mem Q x)
    rwa [symmetryGL_mulVec_of_charTwo hx, hxy, one_smul, hinv] at h
  have h2 : symmetryGL Q y * symmetryGL Q x * symmetryGL Q y = symmetryGL Q (x + y) := by
    have h := conj_symmetryGL (v := x) (symmetryGL_mem Q y)
    rwa [symmetryGL_mulVec_of_charTwo hy, hyx, one_smul, hinv] at h
  have hpow : (symmetryGL Q x * symmetryGL Q y) ^ 3 = 1 := by
    calc (symmetryGL Q x * symmetryGL Q y) ^ 3 =
        (symmetryGL Q x * symmetryGL Q y * symmetryGL Q x) *
          (symmetryGL Q y * symmetryGL Q x * symmetryGL Q y) := by
          rw [pow_three]
          simp only [mul_assoc]
      _ = 1 := by rw [h1, h2, add_comm y x, symmetryGL_mul_self]
  have hne : symmetryGL Q x * symmetryGL Q y ≠ 1 := fun h => by
    have hxy' : symmetryGL Q x = symmetryGL Q y := by
      rw [← hinv y]
      exact eq_inv_of_mul_eq_one_left h
    rw [eq_of_symmetryGL_eq hQ hx hy hxy', polar_self_charTwo] at hxy
    exact zero_ne_one hxy
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hpow hne

end Symmetries

section Planes

variable {K : Type} [Field K] [CharP K 2] {m : ℕ} {Q : QuadraticForm K (Fin m → K)}

omit [CharP K 2] in
private theorem eq_zero_or_one_of_card [Fintype K] (hK : Fintype.card K = 2) (c : K) :
    c = 0 ∨ c = 1 := by
  by_contra h
  push Not at h
  have : 2 < Fintype.card K :=
    Fintype.two_lt_card_iff.mpr ⟨0, 1, c, zero_ne_one, h.1.symm, h.2.symm⟩
  omega

omit [CharP K 2] in
private theorem map_add_eq (x y : Fin m → K) : Q (x + y) = Q x + Q y + polar Q x y := by
  rw [polar]
  ring

private theorem exists_plane_pair [Fintype K] (hK : Fintype.card K = 2) {e f : Fin m → K}
    (hef : polar Q e f = 1) :
    ∃ z w : Fin m → K, z ∈ Submodule.span K {e, f} ∧ w ∈ Submodule.span K {e, f} ∧
      Q z = 1 ∧ polar Q z w = 1 := by
  have he : e ∈ Submodule.span K {e, f} := Submodule.subset_span (by simp)
  have hf : f ∈ Submodule.span K {e, f} := Submodule.subset_span (by simp)
  rcases eq_zero_or_one_of_card hK (Q e) with h0 | h1
  · rcases eq_zero_or_one_of_card hK (Q f) with h0' | h1'
    · refine ⟨e + f, e, Submodule.add_mem _ he hf, he, ?_, ?_⟩
      · rw [map_add_eq, h0, h0', hef, zero_add, zero_add]
      · rw [polar_add_left, polar_self_charTwo, zero_add, polar_comm, hef]
    · exact ⟨f, e, hf, he, h1', by rw [polar_comm]; exact hef⟩
  · exact ⟨e, f, he, hf, h1, hef⟩

omit [CharP K 2] in
private theorem polar_eq_zero_of_mem_span {a b c d x y : Fin m → K}
    (hac : polar Q a c = 0) (had : polar Q a d = 0) (hbc : polar Q b c = 0)
    (hbd : polar Q b d = 0) (hx : x ∈ Submodule.span K {a, b})
    (hy : y ∈ Submodule.span K {c, d}) : polar Q x y = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨s', t', rfl⟩ := Submodule.mem_span_pair.mp hy
  simp [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hac, had, hbc, hbd]

end Planes

theorem hasCoreStar_of_isOrthReflection_two {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥)
    {t : Y} {m : ℕ} (hm : 8 ≤ m) (h : IsOrthReflection Y m 1 t) : HasCoreStar Y t := by
  classical
  obtain ⟨K, _, _, _, Q, ψ, -, hcard, hQ, hψ, -, -, -, hrefl⟩ :=
    CFSG.OddTranspositions.PartFour.exists_symmetry_model_of_isOrthReflection hZ h
  have hK : Fintype.card K = 2 := by rw [hcard, pow_one]
  choose T hTc hTψ using hrefl
  have hcomm : ∀ x hx y hy, polar Q x y = 0 → T x hx * T y hy = T y hy * T x hx :=
    fun x hx y hy h => hψ (by
      rw [map_mul, map_mul, hTψ, hTψ]
      exact (symmetryGL_commute_iff hQ hx hy).mpr h)
  have hord : ∀ x hx y hy, polar Q x y = 1 → orderOf (T x hx * T y hy) = 3 :=
    fun x hx y hy h => by
      rw [← orderOf_injective ψ hψ, map_mul, hTψ, hTψ]
      exact orderOf_symmetryGL_mul hQ hx hy h
  have hne : ∀ x hx y hy, x ≠ y → T x hx ≠ T y hy := fun x hx y hy h e =>
    h (eq_of_symmetryGL_eq hQ hx hy (by rw [← hTψ x hx, ← hTψ y hy, e]))
  let B : LinearMap.BilinForm K (Fin m → K) := polarBilin Q
  have halt : B.IsAlt := fun x => by
    rw [polarBilin_apply_apply]
    exact polar_self_charTwo x
  have hBnd : B.Nondegenerate := hQ
  obtain ⟨k, bs, hbs⟩ := halt.exists_basis_toMatrix_eq_J hBnd
  have hk : 4 ≤ k := by
    have := Module.finrank_eq_card_basis bs
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hJ : ∀ a c, polar Q (bs a) (bs c) = Matrix.J (Fin k) K a c := fun a c => by
    rw [← polarBilin_apply_apply, ← LinearMap.BilinForm.toMatrix_apply bs, hbs]
  have hef : ∀ i, polar Q (bs (.inl i)) (bs (.inr i)) = 1 := fun i => by
    rw [hJ]
    simp [Matrix.J, CharTwo.neg_eq]
  have horth : ∀ i j, i ≠ j → ∀ x ∈ Submodule.span K {bs (.inl i), bs (.inr i)},
      ∀ y ∈ Submodule.span K {bs (.inl j), bs (.inr j)}, polar Q x y = 0 :=
    fun i j hij x hx y hy => polar_eq_zero_of_mem_span (by rw [hJ]; simp [Matrix.J])
      (by rw [hJ]; simp [Matrix.J, hij]) (by rw [hJ]; simp [Matrix.J, hij])
      (by rw [hJ]; simp [Matrix.J]) hx hy
  choose z w hzP hwP hz hzw using fun i => exists_plane_pair hK (hef i)
  obtain ⟨i₀, i₁, i₂, i₃, h01, h02, h03, h12, h13, h23⟩ :
      ∃ a b c d : Fin k, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], by simp [Fin.ext_iff]⟩
  have hp : ∀ i j, i ≠ j → polar Q (w i) (z j) = 0 := fun i j hij =>
    horth i j hij _ (hwP i) _ (hzP j)
  have hzz : ∀ i j, i ≠ j → polar Q (z i) (z j) = 0 := fun i j hij =>
    horth i j hij _ (hzP i) _ (hzP j)
  have hwz : ∀ i, polar Q (w i) (z i) = 1 := fun i => by rw [polar_comm]; exact hzw i
  set s := w i₁ + w i₂ + w i₃ with hs
  have hs1 : polar Q s (z i₁) = 1 := by
    rw [hs, polar_add_left, polar_add_left, hwz, hp _ _ h12.symm, hp _ _ h13.symm, add_zero,
      add_zero]
  have hs2 : polar Q s (z i₂) = 1 := by
    rw [hs, polar_add_left, polar_add_left, hwz, hp _ _ h12, hp _ _ h23.symm, zero_add,
      add_zero]
  have hs3 : polar Q s (z i₃) = 1 := by
    rw [hs, polar_add_left, polar_add_left, hwz, hp _ _ h13, hp _ _ h23, zero_add, zero_add]
  have hs0 : polar Q (z i₀) s = 0 := by
    rw [hs, polar_add_right, polar_add_right, polar_comm, hp _ _ h01.symm, polar_comm,
      hp _ _ h02.symm, polar_comm, hp _ _ h03.symm, add_zero, add_zero]
  obtain ⟨c, hc, hc1, hc2, hc3⟩ : ∃ c : Fin m → K, Q c = 1 ∧ polar Q c (z i₁) = 1 ∧
      polar Q c (z i₂) = 1 ∧ polar Q c (z i₃) = 1 := by
    rcases eq_zero_or_one_of_card hK (Q s) with h0 | h1
    · refine ⟨z i₀ + s, ?_, ?_, ?_, ?_⟩
      · rw [map_add_eq, hz, h0, hs0, add_zero, add_zero]
      · rw [polar_add_left, hzz _ _ h01, hs1, zero_add]
      · rw [polar_add_left, hzz _ _ h02, hs2, zero_add]
      · rw [polar_add_left, hzz _ _ h03, hs3, zero_add]
    · exact ⟨s, h1, hs1, hs2, hs3⟩
  have hzne : ∀ i j, i ≠ j → z i ≠ z j := fun i j hij e => by
    have h1 := hzw i
    rw [e, polar_comm, hp i j hij] at h1
    exact zero_ne_one h1
  exact hasCoreStar_of_center (hTc c hc) (hTc _ (hz i₁)) (hTc _ (hz i₂)) (hTc _ (hz i₃))
    (hord _ _ _ _ hc1) (hord _ _ _ _ hc2) (hord _ _ _ _ hc3)
    (hcomm _ _ _ _ (hzz _ _ h12)) (hcomm _ _ _ _ (hzz _ _ h13)) (hcomm _ _ _ _ (hzz _ _ h23))
    (hne _ _ _ _ (hzne _ _ h12)) (hne _ _ _ _ (hzne _ _ h13)) (hne _ _ _ _ (hzne _ _ h23))

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
