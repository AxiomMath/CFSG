module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusExtendComp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFourRank
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFourTwist
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusNodeZero
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQScaffold
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQInstancePlus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQWeightDescentGlue
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisDescent
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisInterp
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisWeights

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis
open scoped Matrix TensorProduct

private noncomputable def w185_movedRank (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (T : V →ₗ[k] V) : ℕ :=
  Module.finrank k (LinearMap.range (T - 1))

theorem omq_omPlus_core_four_of_interfaces (h1 : OmqPlusWeightVector) (h2 : OmqRankFromWeights)
    (h3 : OmqPlusDescent) {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} (hρ : IsSimpleRep ρ)
    {y : spinGroup (quadPlus 4 F)} (hy2 : y * y = 1) (hρy : ρ y ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) ≤ 6) :
    ∃ (γ : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F))
      (T : V ≃+ (Fin 4 ⊕ Fin 4 → F)), ∀ (s : spinGroup (quadPlus 4 F)) (v : V),
      T (ρ (γ s) v) =
        (spinMatrix (quadPlus 4 F) s : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ T v := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : ρ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mpr hρ
  haveI : Finite (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD 4)).Group :=
    CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanD 4)
  let D := omPlusCurtisDatum 4 F hn3
  obtain ⟨k, _hk, _hkc, _hka, _halg, ι, s, y₀, χ, μ, hs, hE, hsimp, ht, hfrob, hrank, htriv⟩ :=
    omq_endfield_scaffold D (F := F) ρ
  let σ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  let Vm := k ⊗[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadPlus 4 F)))
      ρ.asModule] ρ.asModule
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : FiniteDimensional (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadPlus 4 F)))
      ρ.asModule) ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  haveI : Module.Finite k (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadPlus 4 F)))
      ρ.asModule] ρ.asModule) := inferInstance
  have hy1 : y ≠ 1 := fun h => hρy (by rw [h, map_one])
  have hσy : σ y ≠ 1 := fun h => hρy ((htriv y).mp h)
  have hrle : s * Module.finrank k (LinearMap.range (σ y - 1)) ≤ 6 := by
    calc s * Module.finrank k (LinearMap.range (σ y - 1))
        = Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := (hrank y).symm
      _ ≤ 6 := hr
  have hrpos : 1 ≤ Module.finrank k (LinearMap.range (σ y - 1)) := by
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    exact hσy (sub_eq_zero.mp (LinearMap.range_eq_bot.mp hbot))
  by_cases hs1 : s = 1
  · have hχ1 : ∀ h ∈ D.H, χ h = 1 := by
      intro h hh
      have hsq : χ h ^ 2 = χ h := by simpa [hs1] using hfrob h hh
      have hne : χ h ≠ 0 := by
        intro h0
        have h1 : χ h * χ h⁻¹ = 1 := by
          rw [← ht.chi_mul hh (D.H.inv_mem hh), mul_inv_cancel, ht.chi_one]
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      have h2 : χ h * χ h = χ h * 1 := by rw [← pow_two, hsq, mul_one]
      exact mul_left_cancel₀ hne h2
    have h7 := omq_omPlus_kappa_one_rank h1 h2 hn3 omqPlusSevenRoots_four hF4 ι hsimp ht
      hχ1 hy2 hσy
    have hr6 : Module.finrank k (LinearMap.range (σ y - 1)) ≤ 6 := by
      have h := hrle
      rw [hs1, one_mul] at h
      exact h
    change Module.finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) ≤ 6 at hr6
    omega
  · have hs2 : 2 ≤ s := by omega
    have hr3 : Module.finrank k (LinearMap.range (σ y - 1)) ≤ 3 := by
      have h2r : 2 * Module.finrank k (LinearMap.range (σ y - 1)) ≤
          s * Module.finrank k (LinearMap.range (σ y - 1)) := Nat.mul_le_mul_right _ hs2
      have h26 : 2 * Module.finrank k (LinearMap.range (σ y - 1)) ≤ 6 := le_trans h2r hrle
      omega
    change Module.finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) ≤ 3 at hr3
    have h1J : μ 1 ≠ D.dScalar χ 1 := fun hsep => by
      have h4 := omq_omPlus_four_le_rank_of_node_one hsimp ht hsep hy2 hy1
      omega
    have huniq : ∀ i j : Fin 4, μ i = D.dScalar χ i → μ j = D.dScalar χ j → i = j := by
      intro i j hsi hsj
      by_contra hij
      have hi : i.val ≠ 1 := fun hiv => h1J (by
        have hie : i = 1 := Fin.ext (by simpa using hiv)
        rw [← hie]
        exact hsi)
      have hj : j.val ≠ 1 := fun hjv => h1J (by
        have hje : j = 1 := Fin.ext (by simpa using hjv)
        rw [← hje]
        exact hsj)
      have h4 := omq_omPlus_four_le_rank_of_pair hsimp ht hij hi hj hsi hsj hy2 hy1
      omega
    obtain ⟨i0, hi0⟩ := omq_omPlus_exists_separating hn3 hsimp ht hσy
    have hJ : ∀ i : Fin 4, μ i = D.dScalar χ i ↔ i = i0 := by
      intro i
      constructor
      · intro hi
        exact huniq i i0 hi hi0
      · intro hi
        rw [hi]
        exact hi0
    have hi01 : i0.val ≠ 1 := fun hiv => h1J (by
      have hie : i0 = 1 := Fin.ext (by simpa using hiv)
      rw [← hie]
      exact hi0)
    obtain ⟨γ, χ', μ', ht', hJ'⟩ := exists_twist_node_zero ht hi01 hJ
    have hsimp' : IsSimpleRep (σ.comp γ.toMonoidHom) := isSimpleRep_comp_mulEquiv hsimp γ
    let g' := γ.symm y
    have hg2' : g' * g' = 1 := by
      show γ.symm y * γ.symm y = 1
      rw [← map_mul, hy2, map_one]
    have hgy : (σ.comp γ.toMonoidHom) g' = σ y := by simp [g']
    have hσg' : (σ.comp γ.toMonoidHom) g' ≠ 1 := by
      rw [hgy]
      exact hσy
    rcases omq_omPlus_node_zero_dichotomy h1 h2 hn3 hF4 ι hsimp' ht' hJ' hg2' hσg' with
      ⟨a, β, hβ⟩ | h4
    · haveI := CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isIrreducible_comp_mulEquiv ρ γ
      obtain ⟨hAlg, θ, hθ⟩ := exists_extendScalars_comp_equiv (k := k) ρ γ
      letI := hAlg
      obtain ⟨T, hT⟩ := h3 (n := 4) (le_refl 4) (F := F) (ρ.comp γ.toMonoidHom) ι a
        (θ.trans β) (by
          intro g v
          rw [LinearEquiv.trans_apply, hθ g v]
          exact hβ g (θ v))
      exact ⟨γ, T, fun s v => hT s v⟩
    · exfalso
      have hfin : Module.finrank k (LinearMap.range ((σ.comp γ.toMonoidHom) g' - 1)) =
          Module.finrank k (LinearMap.range (σ y - 1)) := by
        change w185_movedRank k Vm ((σ.comp γ.toMonoidHom) g') =
          w185_movedRank k Vm (σ y)
        exact congrArg (w185_movedRank k Vm) hgy
      have hge : 4 ≤ Module.finrank k (LinearMap.range
          (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) := by
        change 4 ≤ Module.finrank k (LinearMap.range (σ y - 1))
        exact le_of_le_of_eq h4 hfin
      omega

theorem omq_omPlus_core_four {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} (hρ : IsSimpleRep ρ)
    {y : spinGroup (quadPlus 4 F)} (hy2 : y * y = 1) (hρy : ρ y ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) ≤ 6) :
    ∃ (γ : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F))
      (T : V ≃+ (Fin 4 ⊕ Fin 4 → F)), ∀ (s : spinGroup (quadPlus 4 F)) (v : V),
      T (ρ (γ s) v) =
        (spinMatrix (quadPlus 4 F) s : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ T v :=
  omq_omPlus_core_four_of_interfaces
    (omqPlusWeightVector_of_interpolation @curtis_root_interpolation)
    (omqRankFromWeights_of_conj @le_finrank_range_sub_one_of_conj)
    (omqPlusDescent_of_extend @exists_addEquiv_of_extendScalars_equiv) hF hf hρ hy2 hρy hr

end CFSG.LocalAnalysis.WeakClosure81
