module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusInterfaces
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQScaffold
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLabel
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFMain
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusPlane
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNodes
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTrivialRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusExceptionRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNodeZero
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped Matrix TensorProduct

private theorem c2slomqma9_finrank_range_conj {G k V : Type*} [Group G] [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {z : G} (g y : G)
    (hz : z = g * y * g⁻¹) :
    Module.finrank k (LinearMap.range (ρ z - 1)) =
      Module.finrank k (LinearMap.range (ρ y - 1)) := by
  subst hz
  have hconj : ρ (g * y * g⁻¹) - 1 = ρ g * (ρ y - 1) * ρ (g⁻¹) := by
    rw [map_mul, map_mul]
    have h2 : ρ g * ρ (g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g * ρ y * ρ (g⁻¹) - 1 = (ρ g * ρ y - ρ g) * ρ (g⁻¹) := by rw [sub_mul, h2]
      _ = ρ g * (ρ y - 1) * ρ (g⁻¹) := by rw [mul_sub, mul_one]
  have hsurj : Function.Surjective (ρ (g⁻¹)) := fun b =>
    ⟨ρ g b, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]⟩
  have hrange : LinearMap.range (ρ g * (ρ y - 1) * ρ (g⁻¹)) =
      (LinearMap.range (ρ y - 1)).map (ρ g) := by
    rw [show ρ g * (ρ y - 1) * ρ (g⁻¹) =
      (ρ g).comp ((ρ y - 1).comp (ρ (g⁻¹))) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hleft : Function.LeftInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩
  rw [hconj, hrange]
  exact e.finrank_map_eq (LinearMap.range (ρ y - 1))

theorem omq_omMinus_core_of_interfaces (h1l : OmqMinusWeightVectorLong)
    (h1s : OmqMinusWeightVectorShort) (h2 : OmqRankFromWeights) (h3 : OmqMinusDescent)
    {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ} (hn : 4 ≤ n)
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus n F b c)) V} (hρ : IsSimpleRep ρ)
    {y : spinGroup (quadMinus n F b c)} (hy2 : y * y = 1) (hρy : ρ y ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) ≤ 6) :
    ∃ T : V ≃+ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
      ∀ (s : spinGroup (quadMinus n F b c)) (v : V),
        T (ρ s v) = (spinMatrix (quadMinus n F b c) s :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ
            T v := by
  classical
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : ρ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mpr hρ
  haveI : Finite (CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.Spin.isFiniteType_cartanB (n - 1))).Group :=
    CFSG.LieType.RootSystem.finite_group
      (CFSG.LieType.Universal.Spin.isFiniteType_cartanB (n - 1))
  obtain ⟨k, _hk, _hkc, _hka, _halg, ι, s, y₀, χ, μ, hs, hE, hsimp, ht, hfrob, hrank, htriv⟩ :=
    omq_endfield_scaffold (SmallO8mCurtis.curtisDatum n hn hirr) (F := F) ρ
  let σ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : FiniteDimensional (Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (quadMinus n F b c))) ρ.asModule) ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  haveI : Module.Finite k (k ⊗[Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (quadMinus n F b c))) ρ.asModule] ρ.asModule) := inferInstance
  have hy1 : y ≠ 1 := fun h => hρy (by rw [h, map_one])
  have hσy : σ y ≠ 1 := fun h => hρy ((htriv y).mp h)
  obtain ⟨ι', hι'⟩ := omq_exists_shortField_embedding b c ι
  have hex : ∃ i : Fin (n - 1),
      μ i = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i :=
    omq_omMinus_exists_separating hn hirr hsimp ht hσy
  obtain ⟨g, x, π, e, he, hxr, hnW, hshape⟩ := omqnf_exists_conj_nW hn hirr hy2 hy1
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := ⟨_, rfl⟩
  have hsR : s * R ≤ 6 := by
    have hconj := c2slomqma9_finrank_range_conj σ g y hnW
    have h6 : s * Module.finrank k (LinearMap.range (σ y - 1)) ≤ 6 := by
      calc s * Module.finrank k (LinearMap.range (σ y - 1))
          = Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := (hrank y).symm
        _ ≤ 6 := hr
    rw [hRdef, hconj]
    exact h6
  have hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π e := hshape
  by_cases hχ1 : ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ h = 1
  · have h7 : 7 ≤ R := by
      rw [hRdef]
      exact omq_omMinus_trivial_rank h1s h2 hn hirr ι ι' hι' hsimp ht hex hχ1 hF hf hxr he hsh
    have h1R : R ≤ s * R := Nat.le_mul_of_pos_left _ hs
    omega
  · obtain ⟨h0, hh0, hχh0⟩ : ∃ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ h ≠ 1 := by
      by_contra hcon
      exact hχ1 (fun h hh => by
        by_contra hne
        exact hcon ⟨h, hh, hne⟩)
    have hs1 : s ≠ 1 := by
      intro hs1
      have hsq : χ h0 ^ 2 = χ h0 := by simpa [hs1] using hfrob h0 hh0
      have hne : χ h0 ≠ 0 := by
        intro hz
        have h1 : χ h0 * χ h0⁻¹ = 1 := by
          rw [← ht.chi_mul hh0 ((SmallO8mCurtis.curtisDatum n hn hirr).H.inv_mem hh0),
            mul_inv_cancel, ht.chi_one]
        rw [hz, zero_mul] at h1
        exact zero_ne_one h1
      have h2' : χ h0 * χ h0 = χ h0 * 1 := by rw [← pow_two, hsq, mul_one]
      exact hχh0 (mul_left_cancel₀ hne h2')
    have hs2 : 2 ≤ s := by omega
    have hR3 : R ≤ 3 := by
      have h2r : 2 * R ≤ s * R := Nat.mul_le_mul_right _ hs2
      omega
    have hmid : ∀ j : Fin (n - 1), 1 ≤ j.val → j.val + 2 ≤ n - 1 →
        μ j ≠ (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ j := by
      intro j h1 h2' hj
      have h4 : 4 ≤ R := by
        rw [hRdef]
        exact omq_omMinus_four_le_rank_of_long_node hn hirr hsimp ht hxr he hsh h1 h2' hj
      omega
    by_cases hS : μ ⟨n - 2, by omega⟩ =
        (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨n - 2, by omega⟩
    · by_cases hc : 5 ≤ n ∨ π = 1
      · have h4 : 4 ≤ R := by
          rw [hRdef]
          exact omq_omMinus_four_le_rank_of_short_node hn hirr hsimp ht hxr he hsh hS hc
        omega
      · have h5 : ¬ 5 ≤ n := fun h => hc (Or.inl h)
        have hπ : π ≠ 1 := fun h => hc (Or.inr h)
        have hn4 : n = 4 := by omega
        rcases hshape with hA | ⟨hπ1, _, _⟩
        · by_cases h0' : μ ⟨0, by omega⟩ =
              (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨0, by omega⟩
          · have h4 : 4 ≤ R := by
              rw [hRdef]
              exact omq_omMinus_four_le_rank_of_two_one_one hn hirr hsimp ht hxr hA h0' hS
            omega
          · have h2le : 2 ≤ R := by
              rw [hRdef]
              exact omq_omMinus_two_le_rank_of_short_node hn hirr hsimp ht hxr he hsh hS
            have hκ3 : s ≤ 3 := by
              have : s * 2 ≤ s * R := Nat.mul_le_mul_left _ h2le
              omega
            have hlong : ∀ i : Fin (n - 1), i.val + 1 < n - 1 →
                μ i ≠ (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i := by
              intro i hi
              by_cases hi0 : i.val = 0
              · have : i = ⟨0, by omega⟩ := Fin.ext hi0
                rw [this]; exact h0'
              · exact hmid i (by omega) (by omega)
            have h4 : 4 ≤ R := by
              rw [hRdef]
              exact omq_omMinus_exception_rank h1s h2 hn hn4 hirr ι ι' hι' hsimp ht hS hlong
                ⟨h0, hh0, hχh0⟩ (κ := s) (by omega) hκ3 hfrob hF hf hxr hA
            omega
        · exact absurd hπ1 hπ
    · have hfwd : ∀ i : Fin (n - 1),
          μ i = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i → i.val = 0 := by
        intro i hi
        by_contra hi0
        by_cases hlt : i.val + 2 ≤ n - 1
        · exact hmid i (by omega) hlt hi
        · have : i = ⟨n - 2, by omega⟩ :=
            Fin.ext (by have := i.isLt; show i.val = n - 2; omega)
          rw [this] at hi
          exact hS hi
      have hJ : ∀ i : Fin (n - 1),
          μ i = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i ↔ i.val = 0 := by
        intro i
        refine ⟨hfwd i, fun hi => ?_⟩
        obtain ⟨i0, hi0⟩ := hex
        have h0v : i0.val = 0 := hfwd i0 hi0
        have : i = i0 := Fin.ext (by rw [hi, h0v])
        rw [this]; exact hi0
      have hnz := omq_omMinus_node_zero_dichotomy h1l h2 hn hirr hF4 ι ι' hι' hsimp ht hJ hxr
        he hsh
      rcases hnz with ⟨a, β, hβ⟩ | h4
      · exact h3 hn hirr ρ ι a β hβ
      · have h4' : 4 ≤ R := by
          rw [hRdef]
          exact h4
        omega

end CFSG.LocalAnalysis.WeakClosure81
