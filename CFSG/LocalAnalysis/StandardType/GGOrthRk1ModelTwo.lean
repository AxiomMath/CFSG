module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Model
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Unitary

public section

open Module
open scoped IsMulCommutative

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [CharP K 2] {D : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D] {c : D ≃ₗ[K] D} {p : ℕ}

private noncomputable def blk00 (h : Module.End K (D × D)) : Module.End K D :=
  (LinearMap.fst K D D).comp (h.comp (LinearMap.inl K D D))

private noncomputable def blk01 (h : Module.End K (D × D)) : Module.End K D :=
  (LinearMap.fst K D D).comp (h.comp (LinearMap.inr K D D))

private noncomputable def blk10 (h : Module.End K (D × D)) : Module.End K D :=
  (LinearMap.snd K D D).comp (h.comp (LinearMap.inl K D D))

private noncomputable def blk11 (h : Module.End K (D × D)) : Module.End K D :=
  (LinearMap.snd K D D).comp (h.comp (LinearMap.inr K D D))

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk_decomp (h : Module.End K (D × D)) (v : D × D) :
    h v = (blk00 h v.1 + blk01 h v.2, blk10 h v.1 + blk11 h v.2) := by
  have hv : v = LinearMap.inl K D D v.1 + LinearMap.inr K D D v.2 := by
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add]
  ext <;> simp [blk00, blk01, blk10, blk11, LinearMap.comp_apply]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk_inl (h : Module.End K (D × D)) (x : D) :
    h (LinearMap.inl K D D x) = (blk00 h x, blk10 h x) := by
  simp [blk00, blk10, LinearMap.comp_apply]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk_inr (h : Module.End K (D × D)) (y : D) :
    h (LinearMap.inr K D D y) = (blk01 h y, blk11 h y) := by
  simp [blk01, blk11, LinearMap.comp_apply]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk00_mul (h g : Module.End K (D × D)) :
    blk00 (h * g) = blk00 h * blk00 g + blk01 h * blk10 g := by
  ext x
  rw [show blk00 (h * g) x = (LinearMap.fst K D D) ((h * g) (LinearMap.inl K D D x)) from rfl,
    Module.End.mul_apply, blk_inl g x, blk_decomp h (blk00 g x, blk10 g x)]
  simp [blk00, blk01, blk10, blk11, LinearMap.comp_apply]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk01_mul (h g : Module.End K (D × D)) :
    blk01 (h * g) = blk00 h * blk01 g + blk01 h * blk11 g := by
  ext x
  rw [show blk01 (h * g) x = (LinearMap.fst K D D) ((h * g) (LinearMap.inr K D D x)) from rfl,
    Module.End.mul_apply, blk_inr g x, blk_decomp h (blk01 g x, blk11 g x)]
  simp [blk00, blk01, blk10, blk11, LinearMap.comp_apply]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk10_mul (h g : Module.End K (D × D)) :
    blk10 (h * g) = blk10 h * blk00 g + blk11 h * blk10 g := by
  ext x
  rw [show blk10 (h * g) x = (LinearMap.snd K D D) ((h * g) (LinearMap.inl K D D x)) from rfl,
    Module.End.mul_apply, blk_inl g x, blk_decomp h (blk00 g x, blk10 g x)]
  simp [blk00, blk01, blk10, blk11, LinearMap.comp_apply]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk11_mul (h g : Module.End K (D × D)) :
    blk11 (h * g) = blk10 h * blk01 g + blk11 h * blk11 g := by
  ext x
  rw [show blk11 (h * g) x = (LinearMap.snd K D D) ((h * g) (LinearMap.inr K D D x)) from rfl,
    Module.End.mul_apply, blk_inr g x, blk_decomp h (blk01 g x, blk11 g x)]
  simp [blk00, blk01, blk10, blk11, LinearMap.comp_apply]

private noncomputable def c2 (c : D ≃ₗ[K] D) : Module.End K (D × D) :=
  ((c : D →ₗ[K] D).comp (LinearMap.fst K D D)).prod
    ((c : D →ₗ[K] D).comp (LinearMap.snd K D D))

omit [CharP K 2] [FiniteDimensional K D] in
private theorem c2_apply (c : D ≃ₗ[K] D) (v : D × D) :
    c2 c v = (c v.1, c v.2) := rfl

omit [CharP K 2] [FiniteDimensional K D] in
private theorem c2_inl (c : D ≃ₗ[K] D) (x : D) :
    c2 c (LinearMap.inl K D D x) = LinearMap.inl K D D ((c : D →ₗ[K] D) x) := by
  rw [c2_apply]
  simp [LinearMap.inl_apply]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem c2_inr (c : D ≃ₗ[K] D) (y : D) :
    c2 c (LinearMap.inr K D D y) = LinearMap.inr K D D ((c : D →ₗ[K] D) y) := by
  rw [c2_apply]
  simp [LinearMap.inr_apply]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem pow_comm_c2 {h : Module.End K (D × D)}
    (hh : h * c2 c = c2 c * h) (n : ℕ) : h ^ n * c2 c = c2 c * h ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_assoc, hh, ← mul_assoc, ih, mul_assoc]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk00_commute {h : Module.End K (D × D)}
    (hh : h * c2 c = c2 c * h) :
    blk00 h ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ blk00 h := by
  ext x
  have key : h (c2 c (LinearMap.inl K D D x)) = c2 c (h (LinearMap.inl K D D x)) := by
    simpa only [Module.End.mul_apply] using
      congr_fun (congr_arg DFunLike.coe hh) (LinearMap.inl K D D x)
  have hc2inl : c2 c (LinearMap.inl K D D x) =
      LinearMap.inl K D D ((c : D →ₗ[K] D) x) := c2_inl c x
  simp only [LinearMap.comp_apply, blk00]
  rw [← hc2inl, key, c2_apply]
  simp

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk01_commute {h : Module.End K (D × D)}
    (hh : h * c2 c = c2 c * h) :
    blk01 h ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ blk01 h := by
  ext y
  have key : h (c2 c (LinearMap.inr K D D y)) = c2 c (h (LinearMap.inr K D D y)) := by
    simpa only [Module.End.mul_apply] using
      congr_fun (congr_arg DFunLike.coe hh) (LinearMap.inr K D D y)
  have hc2inr : c2 c (LinearMap.inr K D D y) =
      LinearMap.inr K D D ((c : D →ₗ[K] D) y) := c2_inr c y
  simp only [LinearMap.comp_apply, blk01]
  rw [← hc2inr, key, c2_apply]
  simp

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk10_commute {h : Module.End K (D × D)}
    (hh : h * c2 c = c2 c * h) :
    blk10 h ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ blk10 h := by
  ext x
  have key : h (c2 c (LinearMap.inl K D D x)) = c2 c (h (LinearMap.inl K D D x)) := by
    simpa only [Module.End.mul_apply] using
      congr_fun (congr_arg DFunLike.coe hh) (LinearMap.inl K D D x)
  have hc2inl : c2 c (LinearMap.inl K D D x) =
      LinearMap.inl K D D ((c : D →ₗ[K] D) x) := c2_inl c x
  simp only [LinearMap.comp_apply, blk10]
  rw [← hc2inl, key, c2_apply]
  simp

omit [CharP K 2] [FiniteDimensional K D] in
private theorem blk11_commute {h : Module.End K (D × D)}
    (hh : h * c2 c = c2 c * h) :
    blk11 h ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ blk11 h := by
  ext y
  have key : h (c2 c (LinearMap.inr K D D y)) = c2 c (h (LinearMap.inr K D D y)) := by
    simpa only [Module.End.mul_apply] using
      congr_fun (congr_arg DFunLike.coe hh) (LinearMap.inr K D D y)
  have hc2inr : c2 c (LinearMap.inr K D D y) =
      LinearMap.inr K D D ((c : D →ₗ[K] D) y) := c2_inr c y
  simp only [LinearMap.comp_apply, blk11]
  rw [← hc2inr, key, c2_apply]
  simp

private theorem mem_adjoin_of_comp_commute (hc : Rk1Block c p) {g : Module.End K D}
    (hg : g ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ g) :
    g ∈ Algebra.adjoin K ({((c : D →ₗ[K] D))} : Set (Module.End K D)) := by
  obtain ⟨a, b, rfl⟩ := Rk1Block.commute_eq hc hg
  exact Subalgebra.add_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) a)
    (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) b)

private abbrev adjoinC (c : D ≃ₗ[K] D) : Subalgebra K (Module.End K D) :=
  Algebra.adjoin K ({((c : D →ₗ[K] D))} : Set (Module.End K D))

private theorem det_mul_blocks {R : Type*} [CommRing R] (A B C E A' B' C' E' : R) :
    (A * A' + B * C') * (C * B' + E * E') - (A * B' + B * E') * (C * A' + E * C') =
      (A * E - B * C) * (A' * E' - B' * C') := by
  ring

omit [CharP K 2] [FiniteDimensional K D] in
private theorem det_mul_End {A B C E A' B' C' E' : Module.End K D}
    (hA : A ∈ adjoinC c) (hB : B ∈ adjoinC c) (hC : C ∈ adjoinC c) (hE : E ∈ adjoinC c)
    (hA' : A' ∈ adjoinC c) (hB' : B' ∈ adjoinC c) (hC' : C' ∈ adjoinC c)
    (hE' : E' ∈ adjoinC c) :
    (A * A' + B * C') * (C * B' + E * E') - (A * B' + B * E') * (C * A' + E * C') =
      (A * E - B * C) * (A' * E' - B' * C') := by
  have h := det_mul_blocks (⟨A, hA⟩ : adjoinC c) ⟨B, hB⟩ ⟨C, hC⟩ ⟨E, hE⟩
    ⟨A', hA'⟩ ⟨B', hB'⟩ ⟨C', hC'⟩ ⟨E', hE'⟩
  simpa using congrArg Subtype.val h

private noncomputable def Mdet (h : Module.End K (D × D)) : Module.End K D :=
  blk00 h * blk11 h - blk01 h * blk10 h

omit [CharP K 2] [FiniteDimensional K D] in
private theorem Mdet_one : Mdet (1 : Module.End K (D × D)) = 1 := by
  ext v
  simp [Mdet, blk00, blk01, blk10, blk11, LinearMap.comp_apply, Module.End.one_apply]

private theorem Mdet_mul (hc : Rk1Block c p) {h : Module.End K (D × D)}
    (hc2 : h * c2 c = c2 c * h) (n : ℕ) :
    Mdet (h ^ (n + 1)) = Mdet (h ^ n) * Mdet h := by
  have h00n := mem_adjoin_of_comp_commute hc (blk00_commute (pow_comm_c2 hc2 n))
  have h01n := mem_adjoin_of_comp_commute hc (blk01_commute (pow_comm_c2 hc2 n))
  have h10n := mem_adjoin_of_comp_commute hc (blk10_commute (pow_comm_c2 hc2 n))
  have h11n := mem_adjoin_of_comp_commute hc (blk11_commute (pow_comm_c2 hc2 n))
  have h00 := mem_adjoin_of_comp_commute hc (blk00_commute hc2)
  have h01 := mem_adjoin_of_comp_commute hc (blk01_commute hc2)
  have h10 := mem_adjoin_of_comp_commute hc (blk10_commute hc2)
  have h11 := mem_adjoin_of_comp_commute hc (blk11_commute hc2)
  rw [Mdet, Mdet, Mdet, pow_succ, blk00_mul, blk01_mul, blk10_mul, blk11_mul]
  exact det_mul_End h00n h01n h10n h11n h00 h01 h10 h11

private theorem Mdet_pow (hc : Rk1Block c p) {h : Module.End K (D × D)}
    (hc2 : h * c2 c = c2 c * h) (n : ℕ) : Mdet (h ^ n) = (Mdet h) ^ n := by
  induction n with
  | zero => simpa using Mdet_one
  | succ n ih => rw [Mdet_mul hc hc2 n, ih, pow_succ]

omit [CharP K 2] [FiniteDimensional K D] in
private theorem smul_id_mul_eq (a e : K) :
    (a • (LinearMap.id : D →ₗ[K] D)) * (e • LinearMap.id) = (a * e) • LinearMap.id := by
  ext x
  simp [Module.End.mul_apply, smul_smul, mul_comm a e]

theorem Rk1Block.exists_rk1ModelAct (hc : Rk1Block c p) {h : Module.End K (D × D)}
    (hcomm : ∀ v : D × D, h (c v.1, c v.2) = (c (h v).1, c (h v).2))
    (hiso : ∀ v : D × D,
      rk1Omega hc.finrank_eq (h v).1 (h v).2 = rk1Omega hc.finrank_eq v.1 v.2)
    {k : ℕ} (hk : h ^ (2 ^ k) = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v, h v = rk1ModelAct g v := by
  have hc2 : h * c2 c = c2 c * h := by
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, c2_apply]
    exact hcomm v
  have h1 : ∀ x, rk1Omega hc.finrank_eq (blk00 h x) (blk10 h x) = 0 := by
    intro x
    have hh := hiso (LinearMap.inl K D D x)
    rw [blk_inl h x] at hh
    simpa using hh
  have h2 : ∀ y, rk1Omega hc.finrank_eq (blk01 h y) (blk11 h y) = 0 := by
    intro y
    have hh := hiso (LinearMap.inr K D D y)
    rw [blk_inr h y] at hh
    simpa using hh
  have h3 : ∀ x y, rk1Omega hc.finrank_eq (blk00 h x) (blk11 h y) +
      rk1Omega hc.finrank_eq (blk01 h y) (blk10 h x) = rk1Omega hc.finrank_eq x y := by
    intro x y
    have hxy : h (x, y) = (blk00 h x + blk01 h y, blk10 h x + blk11 h y) := by
      simpa using blk_decomp h (x, y)
    have hh := hiso (x, y)
    rw [hxy] at hh
    simp only [map_add, LinearMap.add_apply, h1 x, h2 y, zero_add, add_zero] at hh
    rwa [add_comm] at hh
  have hMmem : Mdet h ∈ adjoinC c := by
    rw [Mdet]
    exact Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (mem_adjoin_of_comp_commute hc (blk00_commute hc2))
        (mem_adjoin_of_comp_commute hc (blk11_commute hc2)))
      (Subalgebra.mul_mem _ (mem_adjoin_of_comp_commute hc (blk01_commute hc2))
        (mem_adjoin_of_comp_commute hc (blk10_commute hc2)))
  have hcommM : Mdet h ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ Mdet h :=
    (Algebra.commute_of_mem_adjoin_self hMmem).symm.eq
  have hMk : (Mdet h) ^ (2 ^ k) = 1 := by
    have hh := Mdet_pow hc hc2 (2 ^ k)
    rw [hk] at hh
    rw [← hh, Mdet_one]
  have h4 : blk00 h * blk11 h + blk01 h * blk10 h = 1 := by
    have hh := Rk1Block.eq_one_of_commute hc hcommM hMk
    rw [Mdet] at hh
    have hneg : -(blk01 h * blk10 h) = blk01 h * blk10 h := by
      rw [← neg_one_smul K (blk01 h * blk10 h), CharTwo.neg_eq (1 : K), one_smul]
    rw [sub_eq_add_neg, hneg] at hh
    exact hh
  obtain ⟨a, b, c', e, hAeq, hBeq, hCeq, hEeq⟩ :=
    Rk1Block.scalar_of_unitary hc (blk00_commute hc2) (blk01_commute hc2)
      (blk10_commute hc2) (blk11_commute hc2) h1 h2 h3 h4
  have hae : a * e + b * c' = 1 := by
    have h4' : (a * e + b * c') • (LinearMap.id : D →ₗ[K] D) = 1 := by
      have h := h4
      rw [hAeq, hBeq, hCeq, hEeq, smul_id_mul_eq, smul_id_mul_eq, ← add_smul] at h
      exact h
    have hv : Module.finBasisOfFinrankEq K D hc.finrank_eq 0 ≠ 0 :=
      (Module.finBasisOfFinrankEq K D hc.finrank_eq).ne_zero 0
    have h := congr_fun (congr_arg DFunLike.coe h4')
      (Module.finBasisOfFinrankEq K D hc.finrank_eq 0)
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Module.End.one_apply] at h
    have h0 : (a * e + b * c' - 1) • (Module.finBasisOfFinrankEq K D hc.finrank_eq 0) = 0 := by
      rw [sub_smul, h, one_smul, sub_self]
    rcases smul_eq_zero.mp h0 with h1' | h1'
    · exact sub_eq_zero.mp h1'
    · exact absurd h1' hv
  have hg : (!![a, b; c', e] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of, CharTwo.sub_eq_add, hae]
  let g : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![a, b; c', e], hg⟩
  refine ⟨g, ?_⟩
  intro v
  rw [rk1ModelAct_apply, blk_decomp h v, hAeq, hBeq, hCeq, hEeq]
  simp [g, LinearMap.smul_apply]

end OrthTorus

end CFSG.StandardType

end
