module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitTraceInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitBlockTrace
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSmallInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitInnerLift
public import CFSG.LocalAnalysis.ComponentInitial.BlockTwoFactorSylowShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem odd_normalizer_inner_longRootSL2 {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {n : ℕ} (hn : 2 ≤ n)
    {R : Subgroup SL(n, F)} {z : SL(n, F)} (hR : IsLongRootSL2 hn R z)
    {g : SL(n, F)} (hg : g ∈ normalizer (R : Set SL(n, F))) (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain ⟨c, hRc, -⟩ := hR
  let φ : SL(2, F) →* SL(n, F) :=
    (MulAut.conj c).toMonoidHom.comp (blockSL F n 2 0 (by omega))
  have hφ : Function.Injective φ :=
    (MulAut.conj c).injective.comp (blockSL_injective (by omega))
  have hφrange : φ.range = R := by
    rw [MonoidHom.range_comp]
    exact hRc.symm
  have htrace : ∀ x : SL(2, F),
      (φ x : Matrix (Fin n) (Fin n) F).trace =
        (1 : F) * (x : Matrix (Fin 2) (Fin 2) F).trace + (n - 2 : ℕ) := by
    intro x
    have heq : φ x = c * blockSL F n 2 0 hn x * c⁻¹ := rfl
    have hconj : ((c * blockSL F n 2 0 hn x * c⁻¹ : SL(n, F)) :
        Matrix (Fin n) (Fin n) F).trace =
        ((blockSL F n 2 0 hn x : SL(n, F)) : Matrix (Fin n) (Fin n) F).trace := by
      change ((c : Matrix (Fin n) (Fin n) F) *
        ((blockSL F n 2 0 hn x : SL(n, F)) : Matrix (Fin n) (Fin n) F) *
        ((c⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)).trace = _
      rw [Matrix.trace_mul_cycle]
      have hcc : ((c⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) *
          (c : Matrix (Fin n) (Fin n) F) = 1 :=
        congrArg (fun y : SL(n, F) => (y : Matrix (Fin n) (Fin n) F)) (inv_mul_cancel c)
      rw [hcc, Matrix.one_mul]
    exact (congrArg (fun y : SL(n, F) => (y : Matrix (Fin n) (Fin n) F).trace) heq).trans
      (hconj.trans (by simpa only [one_mul] using trace_blockSL hn x))
  obtain ⟨r, hr⟩ := exists_inner_normalizer_aut_of_trace hodd h3 φ hφ one_ne_zero htrace
    (by rwa [hφrange]) hgo
  refine ⟨φ r, hφrange ▸ ⟨r, rfl⟩, ?_⟩
  intro x hx
  have hxrange : x ∈ φ.range := by rwa [hφrange]
  obtain ⟨y, rfl⟩ := hxrange
  exact hr y

theorem odd_normalizer_inner_fundamental_psl {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {m : ℕ} (hm : 1 ≤ m)
    {R : Subgroup SL(m + 1, F)}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m F))
    {g : SL(m + 1, F)} (hg : g ∈ normalizer (R : Set SL(m + 1, F)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain ⟨z, hz⟩ := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
    (by omega) hR
  exact odd_normalizer_inner_longRootSL2 hodd h3 (by omega) hz hg hgo

theorem odd_normalizer_inner_longRootSL2_all {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {n : ℕ} (hn : 2 ≤ n)
    {R : Subgroup SL(n, F)} {z : SL(n, F)} (hR : IsLongRootSL2 hn R z)
    {g : SL(n, F)} (hg : g ∈ normalizer (R : Set SL(n, F))) (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  by_cases h3 : 3 < Nat.card F
  · exact odd_normalizer_inner_longRootSL2 hodd h3 hn hR hg hgo
  have hF : Nat.card F = 3 := by
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨c, hRc, -⟩ := hR
  let φ : SL(2, F) →* SL(n, F) :=
    (MulAut.conj c).toMonoidHom.comp (blockSL F n 2 0 hn)
  have hφ : Function.Injective φ :=
    (MulAut.conj c).injective.comp (blockSL_injective hn)
  have hφrange : φ.range = R := by rw [MonoidHom.range_comp]; exact hRc.symm
  obtain ⟨r, hr⟩ := exists_inner_normalizer_aut_of_card_three hF φ hφ
    (by rwa [hφrange]) hgo
  refine ⟨φ r, hφrange ▸ ⟨r, rfl⟩, ?_⟩
  intro x hx
  have hxrange : x ∈ φ.range := by rwa [hφrange]
  obtain ⟨y, rfl⟩ := hxrange
  exact hr y

theorem odd_normalizer_inner_fundamental_psl_all {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {m : ℕ} (hm : 1 ≤ m)
    {R : Subgroup SL(m + 1, F)}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m F))
    {g : SL(m + 1, F)} (hg : g ∈ normalizer (R : Set SL(m + 1, F)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain ⟨z, hz⟩ := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
    (by omega) hR
  exact odd_normalizer_inner_longRootSL2_all hodd (by omega) hz hg hgo

theorem odd_normalizer_inner_fundamental_psl_image {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {m : ℕ} (hm : 1 ≤ m)
    {X : Type} [Group X] (ψ : SL(m + 1, F) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center SL(m + 1, F)) {R : Subgroup SL(m + 1, F)}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m F))
    {g : X} (hg : g ∈ normalizer ((R.map ψ : Subgroup X) : Set X))
    (hgo : Odd (orderOf g)) :
    (R.map ψ).normalizerMonoidHom ⟨g, hg⟩ ∈
      (MulAut.conj : R.map ψ →* MulAut (R.map ψ)).range := by
  obtain ⟨z, hz⟩ := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
    (by omega) hR
  have hclass := hz.isClassicalSL2 (two_ne_zero_of_odd_natCard hodd)
  have hperf : Group.IsPerfect R := hclass.isPerfect (by omega)
  apply (CFSG.GroupTheory.normalizerMonoidHom_mem_range_conj_iff hg).mpr
  exact CFSG.GroupTheory.exists_inner_normalizer_of_central_image ψ hψ hker R hperf
    (fun y hy hyo => odd_normalizer_inner_fundamental_psl_all hodd hm hR hy hyo) hg hgo

theorem odd_normalizer_inner_fundamental_psl_image_all {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {m : ℕ} (hm : 1 ≤ m)
    {X : Type} [Group X] [Finite X] (ψ : SL(m + 1, F) →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center SL(m + 1, F))
    {R : Subgroup SL(m + 1, F)}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m F))
    (hdisj : R ⊓ ψ.ker = ⊥)
    {g : X} (hg : g ∈ normalizer ((R.map ψ : Subgroup X) : Set X))
    (hgo : Odd (orderOf g)) :
    (R.map ψ).normalizerMonoidHom ⟨g, hg⟩ ∈
      (MulAut.conj : R.map ψ →* MulAut (R.map ψ)).range := by
  by_cases h3 : 3 < Nat.card F
  · exact odd_normalizer_inner_fundamental_psl_image hodd h3 hm ψ hψ hker hR hg hgo
  have hF : Nat.card F = 3 := by
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨z, hz⟩ := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
    (by omega) hR
  obtain ⟨eR⟩ := (hz.isClassicalSL2 (two_ne_zero_of_odd_natCard hodd)).nonempty_mulEquiv
  exact normalizerMonoidHom_mem_range_conj_of_equiv_sl2_three hF
    ((CFSG.LocalAnalysis.ComponentInitial.equivMapOfInfKerEqBot ψ hdisj).symm.trans eR)
    hg hgo

end CFSG.LocalAnalysis.UniquenessCase.UC22
