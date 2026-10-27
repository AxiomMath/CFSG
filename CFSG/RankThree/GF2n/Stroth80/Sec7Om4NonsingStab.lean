module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

theorem sec7ns_sq_surj {K : Type} [Field K] [Finite K] [CharP K 2] (t : K) :
    ∃ μ : K, μ * μ = t := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hinj : Function.Injective fun μ : K => μ * μ := by
    intro a b h
    have h' : a * a = b * b := h
    have hsq : (a + b) * (a + b) = 0 := by
      linear_combination h' + (a * b + b * b) * h2
    have hab : a + b = 0 := mul_self_eq_zero.mp hsq
    linear_combination hab - b * h2
  obtain ⟨μ, hμ⟩ := Finite.surjective_of_injective hinj t
  exact ⟨μ, hμ⟩

theorem sec7ns_finrank_perp {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {c₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hc₀ : quadMinus 2 K b c c₀ ≠ 0) :
    Module.finrank K (LinearMap.ker (polarBilin (quadMinus 2 K b c) c₀)) = 3 := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hc0 : c₀ ≠ 0 := fun h => hc₀ (by rw [h, QuadraticMap.map_zero])
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hc0
  have hsurj : Function.Surjective (polarBilin (quadMinus 2 K b c) c₀) := by
    intro s
    refine ⟨(s / polar (quadMinus 2 K b c) c₀ y) • y, ?_⟩
    rw [map_smul, polarBilin_apply_apply, smul_eq_mul]
    field_simp
  have h := LinearMap.finrank_range_add_finrank_ker (polarBilin (quadMinus 2 K b c) c₀)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem sec7ns_natCard_perp {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {c₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hc₀ : quadMinus 2 K b c c₀ ≠ 0) :
    Nat.card (LinearMap.ker (polarBilin (quadMinus 2 K b c) c₀)) = Nat.card K ^ 3 := by
  have h := Module.natCard_eq_pow_finrank (K := K)
    (V := ↥(LinearMap.ker (polarBilin (quadMinus 2 K b c) c₀)))
  rw [h, sec7ns_finrank_perp hirr hc₀]

theorem sec7ns_natCard_space {K : Type} [Field K] [Finite K] :
    Nat.card (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) = Nat.card K ^ 4 := by
  have h := Module.natCard_eq_pow_finrank (K := K) (V := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)
  rw [h, Module.finrank_fintype_fun_eq_card]
  simp

theorem sec7ns_singular_lift {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {c₀ p : V} (hγ : Q c₀ ≠ 0)
    (hp : polar Q c₀ p = 0) : ∃ μ : K, Q (μ • c₀ + p) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨μ, hμ⟩ := sec7ns_sq_surj (Q p / Q c₀)
  refine ⟨μ, ?_⟩
  have hμQ : μ * μ * Q c₀ = Q p := by
    rw [hμ]
    field_simp
  rw [QuadraticMap.map_add (⇑Q) (μ • c₀) p, QuadraticMap.map_smul, polar_smul_left, hp, smul_zero,
    add_zero, smul_eq_mul, hμQ]
  linear_combination (Q p) * h2

theorem sec7ns_eichler_mem {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {y w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hy : quadMinus 2 K b c y = 0) (hw : polar (quadMinus 2 K b c) y w = 0) :
    ∃ A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K,
      A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c) ∧
      ∀ v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
        ((A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ v
          = eichler (quadMinus 2 K b c) y w v := by
  let E := ElemMatrixIso.minus (K := K) (m := 2) (b := b) (c := c) le_rfl hirr
  let A : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c) :=
    E.equiv.symm (eichlerG (quadMinus 2 K b c) y w)
  have h1 : E.equiv A = eichlerG (quadMinus 2 K b c) y w := MulEquiv.apply_symm_apply E.equiv _
  refine ⟨(A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K), A.2, fun v => ?_⟩
  have h2 := E.app A v
  rw [h1] at h2
  exact h2.symm

theorem sec7ns_line_mem {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {c₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hc₀ : quadMinus 2 K b c c₀ ≠ 0)
    (X : AddSubgroup (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))
    (hX1 : ∀ s : K, s • c₀ ∈ X)
    (hinv : ∀ A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K,
      A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c) →
      (∃ s : K, (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ c₀ = s • c₀) →
      ∀ x ∈ X, (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x ∈ X)
    {x y : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hx : x ∈ X)
    (hxH : polar (quadMinus 2 K b c) c₀ x = 0)
    (hy : quadMinus 2 K b c y = 0) (hyH : polar (quadMinus 2 K b c) c₀ y = 0)
    (hδ : polar (quadMinus 2 K b c) x y ≠ 0) (τ : K) : τ • y ∈ X := by
  set Q := quadMinus 2 K b c
  have hγ : Q c₀ ≠ 0 := hc₀
  obtain ⟨μ, hμ⟩ := sec7ns_sq_surj (τ / (Q c₀ * polar Q x y))
  have hcoef : μ * μ * Q c₀ * polar Q x y = τ := by
    rw [hμ]
    field_simp
  have hcc : polar Q c₀ c₀ = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hc0w : polar Q c₀ (μ • c₀) = 0 := by
    rw [polar_smul_right, hcc, smul_zero]
  have hyc' : polar Q y c₀ = 0 := by
    rw [polar_comm]
    exact hyH
  have hyw : polar Q y (μ • c₀) = 0 := by
    rw [polar_smul_right, hyc', smul_zero]
  obtain ⟨A, hA, hAv⟩ := sec7ns_eichler_mem hirr hy hyw
  have hAc : (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ c₀ = (1 : K) • c₀ := by
    rw [hAv, one_smul, eichler_apply_of_polar_eq_zero hyH hc0w]
  have hAx := hinv A hA ⟨1, hAc⟩ x hx
  have hxw : polar Q x (μ • c₀) = 0 := by
    rw [polar_smul_right, polar_comm, hxH, smul_zero]
  have hQw : Q (μ • c₀) = μ * μ * Q c₀ := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
  have hEx : (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x
      = x + polar Q x y • (μ • c₀) - (μ * μ * Q c₀ * polar Q x y) • y := by
    rw [hAv, eichler_apply hy hyw x, hxw, zero_add, hQw]
  have hτ : τ • y = (x + polar Q x y • (μ • c₀)) - (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x := by
    rw [hEx, hcoef]
    abel
  rw [hτ]
  refine X.sub_mem (X.add_mem hx ?_) hAx
  rw [smul_smul]
  exact hX1 _

theorem sec7ns_exists_polar_ne {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {c₀ u : V} (hc₀ : c₀ ≠ 0)
    (hu : ∀ s : K, u ≠ s • c₀) : ∃ p : V, polar Q c₀ p = 0 ∧ polar Q u p ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨e, he⟩ := exists_polar_ne_zero hQ hc₀
  obtain ⟨e', h1⟩ : ∃ e' : V, polar Q c₀ e' = 1 :=
    ⟨(polar Q c₀ e)⁻¹ • e, by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ he]⟩
  have key : ∀ x : V, polar Q (u - polar Q u e' • c₀) x = 0 := by
    intro x
    have hh : polar Q c₀ (x - polar Q c₀ x • e') = 0 := by
      rw [polar_sub_right, polar_smul_right, h1, smul_eq_mul, mul_one, sub_self]
    have hu' := hcon _ hh
    rw [polar_sub_right, polar_smul_right] at hu'
    rw [polar_sub_left, polar_smul_left]
    simp only [smul_eq_mul]
    linear_combination hu'
  have hz := eq_zero_of_polar_eq_zero hQ key
  exact hu _ (sub_eq_zero.mp hz)

theorem sec7ns_exists_inter {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Finite V] {c₀ : V} (hc₀ : c₀ ≠ 0) (H : Submodule K V)
    (X : AddSubgroup V) (hX1 : ∀ s : K, s • c₀ ∈ X) (hq : 2 ≤ Nat.card K)
    (hXcard : Nat.card X = Nat.card K ^ 3) (hHcard : Nat.card H = Nat.card K ^ 3)
    (hVcard : Nat.card V = Nat.card K ^ 4) :
    ∃ x ∈ X, x ∈ H ∧ ∀ s : K, x ≠ s • c₀ := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hindex : X.index * Nat.card X = Nat.card V := AddSubgroup.index_mul_card X
  rw [hXcard, hVcard] at hindex
  have hidx : X.index ≤ Nat.card K := by
    nlinarith [pow_pos hpos 3]
  have hidx0 : X.index ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hindex
    exact (pow_pos hpos 4).ne hindex
  have hrel1 : X.relIndex H.toAddSubgroup * Nat.card (X ⊓ H.toAddSubgroup : AddSubgroup V) =
      Nat.card H.toAddSubgroup := AddSubgroup.relIndex_mul_card X H.toAddSubgroup
  have hrel2 : X.relIndex H.toAddSubgroup ≤ Nat.card K := by
    have h1 : X.relIndex H.toAddSubgroup ≤ X.relIndex ⊤ :=
      AddSubgroup.relIndex_le_of_le_right le_top
        (by rw [AddSubgroup.relIndex_top_right]; exact hidx0)
    rw [AddSubgroup.relIndex_top_right] at h1
    exact h1.trans hidx
  have hsub : X ⊓ H.toAddSubgroup ≤ (Submodule.span K {c₀}).toAddSubgroup := by
    intro x hx
    obtain ⟨hxX, hxH⟩ := hx
    obtain ⟨s, rfl⟩ := hcon x hxX hxH
    rw [Submodule.mem_toAddSubgroup]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self c₀)
  have hL : Nat.card (Submodule.span K {c₀}).toAddSubgroup = Nat.card K := by
    haveI : FiniteDimensional K (Submodule.span K {c₀}) :=
      FiniteDimensional.span_of_finite K (Set.finite_singleton c₀)
    have h1 := Module.natCard_eq_pow_finrank (K := K) (V := ↥(Submodule.span K {c₀}))
    rw [finrank_span_singleton hc₀, pow_one] at h1
    exact h1
  have hle : Nat.card (X ⊓ H.toAddSubgroup : AddSubgroup V) ≤ Nat.card K :=
    (AddSubgroup.card_le_of_le hsub).trans hL.le
  have hHc : Nat.card H.toAddSubgroup = Nat.card K ^ 3 := hHcard
  have key : Nat.card K ^ 3 ≤ Nat.card K * Nat.card K := by
    calc Nat.card K ^ 3 = Nat.card H.toAddSubgroup := hHc.symm
      _ = X.relIndex H.toAddSubgroup * Nat.card (X ⊓ H.toAddSubgroup : AddSubgroup V) :=
        hrel1.symm
      _ ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hrel2 hle
  have h3 : Nat.card K ^ 3 = Nat.card K * Nat.card K * Nat.card K := by ring
  have hqq : 0 < Nat.card K * Nat.card K := Nat.mul_pos hpos hpos
  nlinarith

theorem sec7ns_perp_coord {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {c₀ u₁ u₂ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hc₀ : quadMinus 2 K b c c₀ ≠ 0) (hu₁ : quadMinus 2 K b c u₁ = 0)
    (hu₂ : quadMinus 2 K b c u₂ = 0)
    (h₁ : polar (quadMinus 2 K b c) c₀ u₁ = 0) (h₂ : polar (quadMinus 2 K b c) c₀ u₂ = 0)
    (h12 : polar (quadMinus 2 K b c) u₁ u₂ = 1) {x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hx : polar (quadMinus 2 K b c) c₀ x = 0) :
    ∃ s t r : K, x = s • c₀ + t • u₁ + r • u₂ := by
  have hc0 : c₀ ≠ 0 := fun h => hc₀ (by rw [h, QuadraticMap.map_zero])
  have hcc : polar (quadMinus 2 K b c) c₀ c₀ = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hu11 : polar (quadMinus 2 K b c) u₁ u₁ = 0 := polar_self_eq_zero hu₁
  have hu22 : polar (quadMinus 2 K b c) u₂ u₂ = 0 := polar_self_eq_zero hu₂
  have h21 : polar (quadMinus 2 K b c) u₂ u₁ = 1 := by
    rw [polar_comm, h12]
  have hli : LinearIndependent K ![c₀, u₁, u₂] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hg
    have e1 : polar (quadMinus 2 K b c) (g 0 • c₀ + g 1 • u₁ + g 2 • u₂) u₂ = 0 := by
      rw [hg, polar_zero_left]
    have e2 : polar (quadMinus 2 K b c) (g 0 • c₀ + g 1 • u₁ + g 2 • u₂) u₁ = 0 := by
      rw [hg, polar_zero_left]
    simp only [polar_add_left, polar_smul_left, h₂, h12, hu22, h₁, hu11, h21, smul_eq_mul,
      mul_zero, mul_one, zero_add, add_zero] at e1 e2
    have hg1 : g 1 = 0 := e1
    have hg2 : g 2 = 0 := e2
    rw [hg1, hg2, zero_smul, zero_smul, add_zero, add_zero] at hg
    have hg0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hc0
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  have hWH : Submodule.span K (Set.range ![c₀, u₁, u₂]) ≤
      LinearMap.ker (polarBilin (quadMinus 2 K b c) c₀) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simp [LinearMap.mem_ker, polarBilin_apply_apply, hcc]
    · simp [LinearMap.mem_ker, polarBilin_apply_apply, h₁]
    · simp [LinearMap.mem_ker, polarBilin_apply_apply, h₂]
  have hWfin : Module.finrank K (Submodule.span K (Set.range ![c₀, u₁, u₂])) = 3 := by
    rw [finrank_span_eq_card hli]
    simp
  have hWeq := Submodule.eq_of_le_of_finrank_eq hWH
    (by rw [hWfin, sec7ns_finrank_perp hirr hc₀])
  have hxW : x ∈ Submodule.span K (Set.range ![c₀, u₁, u₂]) := by
    rw [hWeq]
    simpa [LinearMap.mem_ker, polarBilin_apply_apply] using hx
  rw [Submodule.mem_span_range_iff_exists_fun] at hxW
  obtain ⟨c', hc'⟩ := hxW
  refine ⟨c' 0, c' 1, c' 2, ?_⟩
  rw [← hc', Fin.sum_univ_three]
  simp

theorem sec7_om4_nonsingular_stab {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {c₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hc₀ : quadMinus 2 K b c c₀ ≠ 0)
    (X : AddSubgroup (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))
    (hX1 : ∀ s : K, s • c₀ ∈ X) (hXcard : Nat.card X = Nat.card K ^ 3)
    (hinv : ∀ A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K,
      A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c) →
      (∃ s : K, (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ c₀ = s • c₀) →
      ∀ x ∈ X, (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x ∈ X) :
    ∀ x, x ∈ X ↔ polar (quadMinus 2 K b c) c₀ x = 0 := by
  have hq : 2 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hc0 : c₀ ≠ 0 := fun h => hc₀ (by rw [h, QuadraticMap.map_zero])
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hcc : polar (quadMinus 2 K b c) c₀ c₀ = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  let H : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
    LinearMap.ker (polarBilin (quadMinus 2 K b c) c₀)
  have hmemH : ∀ x, x ∈ H ↔ polar (quadMinus 2 K b c) c₀ x = 0 := fun x => by
    simp [H]
  have hHfin : Module.finrank K H = 3 := sec7ns_finrank_perp hirr hc₀
  have hHcard : Nat.card H = Nat.card K ^ 3 := sec7ns_natCard_perp hirr hc₀
  have hVcard : Nat.card (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) = Nat.card K ^ 4 :=
    sec7ns_natCard_space
  have hnot : ¬ H ≤ Submodule.span K {c₀} := by
    intro hle
    have h1 : Module.finrank K H ≤ Module.finrank K (Submodule.span K {c₀}) :=
      Submodule.finrank_mono hle
    rw [finrank_span_singleton hc0, hHfin] at h1
    omega
  obtain ⟨p₁, hp₁H, hp₁⟩ := SetLike.not_le_iff_exists.mp hnot
  have hp₁c : polar (quadMinus 2 K b c) c₀ p₁ = 0 := (hmemH p₁).mp hp₁H
  obtain ⟨μ₁, hμ₁⟩ := sec7ns_singular_lift hc₀ hp₁c
  obtain ⟨u₁, hu₁eq⟩ : ∃ u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      u = μ₁ • c₀ + p₁ := ⟨_, rfl⟩
  rw [← hu₁eq] at hμ₁
  have hu₁Q : quadMinus 2 K b c u₁ = 0 := hμ₁
  have hu₁c : polar (quadMinus 2 K b c) c₀ u₁ = 0 := by
    rw [hu₁eq, polar_add_right, polar_smul_right, hcc, smul_zero, zero_add, hp₁c]
  have hu₁u₁ : polar (quadMinus 2 K b c) u₁ u₁ = 0 := polar_self_eq_zero hu₁Q
  have hu₁nl : ∀ s : K, u₁ ≠ s • c₀ := by
    intro s hs
    have E : μ₁ • c₀ + p₁ = s • c₀ := hu₁eq.symm.trans hs
    exact hp₁ (by
      rw [show p₁ = (s - μ₁) • c₀ by linear_combination (norm := module) E]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c₀))
  obtain ⟨p₂, hp₂c, hp₂⟩ := sec7ns_exists_polar_ne hQ hc0 hu₁nl
  obtain ⟨μ₂, hμ₂⟩ := sec7ns_singular_lift hc₀ hp₂c
  obtain ⟨u₂', hu₂'eq⟩ : ∃ u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      u = μ₂ • c₀ + p₂ := ⟨_, rfl⟩
  rw [← hu₂'eq] at hμ₂
  have hu₂'c : polar (quadMinus 2 K b c) c₀ u₂' = 0 := by
    rw [hu₂'eq, polar_add_right, polar_smul_right, hcc, smul_zero, zero_add, hp₂c]
  have h1c : polar (quadMinus 2 K b c) u₁ c₀ = 0 := by
    rw [polar_comm]
    exact hu₁c
  have hβ : polar (quadMinus 2 K b c) u₁ u₂' ≠ 0 := by
    rw [hu₂'eq, polar_add_right, polar_smul_right, h1c, smul_zero, zero_add]
    exact hp₂
  obtain ⟨u₂, hu₂eq⟩ : ∃ u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      u = (polar (quadMinus 2 K b c) u₁ u₂')⁻¹ • u₂' := ⟨_, rfl⟩
  have hu₂Q : quadMinus 2 K b c u₂ = 0 := by
    rw [hu₂eq, QuadraticMap.map_smul, hμ₂, smul_zero]
  have hu₂c : polar (quadMinus 2 K b c) c₀ u₂ = 0 := by
    rw [hu₂eq, polar_smul_right, hu₂'c, smul_zero]
  have h12 : polar (quadMinus 2 K b c) u₁ u₂ = 1 := by
    rw [hu₂eq, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hβ]
  have hu₂u₂ : polar (quadMinus 2 K b c) u₂ u₂ = 0 := polar_self_eq_zero hu₂Q
  have h21 : polar (quadMinus 2 K b c) u₂ u₁ = 1 := by
    rw [polar_comm, h12]
  obtain ⟨x₀, hx₀X, hx₀H, hx₀s⟩ :=
    sec7ns_exists_inter hc0 H X hX1 hq hXcard hHcard hVcard
  have hx₀c : polar (quadMinus 2 K b c) c₀ x₀ = 0 := (hmemH x₀).mp hx₀H
  obtain ⟨s₀, t₀, r₀, hx₀eq⟩ := sec7ns_perp_coord hirr hc₀ hu₁Q hu₂Q hu₁c hu₂c h12 hx₀c
  have hpol1 : polar (quadMinus 2 K b c) x₀ u₁ = r₀ := by
    rw [hx₀eq]
    simp only [polar_add_left, polar_smul_left, hu₁c, hu₁u₁, h21, smul_zero, smul_eq_mul,
      mul_zero, mul_one, zero_add, add_zero]
  have hpol2 : polar (quadMinus 2 K b c) x₀ u₂ = t₀ := by
    rw [hx₀eq]
    simp only [polar_add_left, polar_smul_left, hu₂c, hu₂u₂, h12, smul_zero, smul_eq_mul,
      mul_zero, mul_one, zero_add, add_zero]
  have hlines : (∀ τ : K, τ • u₁ ∈ X) ∧ (∀ τ : K, τ • u₂ ∈ X) := by
    by_cases hr : r₀ = 0
    · have ht : t₀ ≠ 0 := by
        intro ht
        apply hx₀s s₀
        rw [hx₀eq, hr, ht, zero_smul, zero_smul, add_zero, add_zero]
      have hu₂X : ∀ τ : K, τ • u₂ ∈ X := fun τ =>
        sec7ns_line_mem hirr hc₀ X hX1 hinv hx₀X hx₀c hu₂Q hu₂c
          (by rw [hpol2]; exact ht) τ
      have hu₂mem : u₂ ∈ X := by simpa using hu₂X 1
      refine ⟨fun τ => sec7ns_line_mem hirr hc₀ X hX1 hinv hu₂mem hu₂c hu₁Q hu₁c
        (by rw [h21]; exact one_ne_zero) τ, hu₂X⟩
    · have hu₁X : ∀ τ : K, τ • u₁ ∈ X := fun τ =>
        sec7ns_line_mem hirr hc₀ X hX1 hinv hx₀X hx₀c hu₁Q hu₁c
          (by rw [hpol1]; exact hr) τ
      have hu₁mem : u₁ ∈ X := by simpa using hu₁X 1
      refine ⟨hu₁X, fun τ => sec7ns_line_mem hirr hc₀ X hX1 hinv hu₁mem hu₁c hu₂Q hu₂c
        (by rw [h12]; exact one_ne_zero) τ⟩
  have hHX : ∀ x, x ∈ H → x ∈ X := by
    intro x hx
    obtain ⟨s, t, r, hxeq⟩ :=
      sec7ns_perp_coord hirr hc₀ hu₁Q hu₂Q hu₁c hu₂c h12 ((hmemH x).mp hx)
    rw [hxeq]
    exact X.add_mem (X.add_mem (hX1 s) (hlines.1 t)) (hlines.2 r)
  have hHX' : H.toAddSubgroup ≤ X := fun x hx => hHX x hx
  have heq : H.toAddSubgroup = X :=
    AddSubgroup.eq_of_le_of_card_ge hHX' (le_of_eq (hXcard.trans hHcard.symm))
  intro x
  rw [← heq, Submodule.mem_toAddSubgroup]
  exact hmemH x

theorem sec7_om4_nonsingular_stab_of_hom {Γ : Type*} [Group Γ] {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {c₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hc₀ : quadMinus 2 K b c c₀ ≠ 0)
    (φ : Γ →* GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
    (hφ : φ.range = CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c))
    (X : AddSubgroup (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))
    (hX1 : ∀ s : K, s • c₀ ∈ X) (hXcard : Nat.card X = Nat.card K ^ 3)
    (hinv : ∀ g : Γ, (∃ s : K, ((φ g : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ c₀ =
          s • c₀) →
      ∀ x ∈ X, ((φ g : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x ∈
          X) :
    ∀ x, x ∈ X ↔ polar (quadMinus 2 K b c) c₀ x = 0 := by
  refine sec7_om4_nonsingular_stab hirr hc₀ X hX1 hXcard ?_
  intro A hA hs x hx
  obtain ⟨g, rfl⟩ : A ∈ φ.range := hφ ▸ hA
  exact hinv g hs x hx

end CFSG.RankThree.GF2n.Stroth80
