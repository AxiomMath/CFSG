module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusData
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusSingle
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOuterFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mModule
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped Matrix TensorProduct

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private theorem omMinusTwo_two_mul_finrank_range_le {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {T : Module.End (ZMod 2) V} (hT : T * T = 1) :
    2 * Module.finrank (ZMod 2) (LinearMap.range (T - 1)) ≤ Module.finrank (ZMod 2) V := by
  have : Module.Finite (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
  have hle : LinearMap.range (T - 1) ≤ LinearMap.ker (T - 1) := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hTT : T (T x) = x := by
      have h := LinearMap.congr_fun hT x
      simpa using h
    show (T - 1) ((T - 1) x) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_sub, hTT]
    rw [show x - T x - (T x - x) = (x + x) - (T x + T x) by abel]
    rw [show x + x = 0 from by
        rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul],
      show T x + T x = 0 from by
        rw [← two_smul (ZMod 2) (T x), show (2 : ZMod 2) = 0 by decide, zero_smul],
      sub_self]
  have hrank := Submodule.finrank_mono hle
  have hrn := LinearMap.finrank_range_add_finrank_ker (T - 1)
  omega

private theorem omMinusTwo_n_ne_one (i : Fin 3) : (o8mDatum hirrQ).n i ≠ 1 := by
  intro h
  have hXY : (o8mDatum hirrQ).X i ≤ (o8mDatum hirrQ).Y i := by
    intro x hx
    have hx' := (o8mDatum hirrQ).n_conjX i x hx
    rwa [h, one_mul, inv_one, mul_one] at hx'
  have hUL : (o8mDatum hirrQ).X i ≤ (o8mDatum hirrQ).U ⊓ (o8mDatum hirrQ).L :=
    le_inf ((o8mDatum hirrQ).X_le i) (hXY.trans ((o8mDatum hirrQ).Y_le i))
  rw [(o8mDatum hirrQ).U_inf_L] at hUL
  exact (o8mDatum hirrQ).X_ne_bot i (le_bot_iff.mp hUL)

private theorem omMinusTwo_n0_sq : (o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 0 = 1 := by
  rw [o8mDatum_n hirrQ 0, minusWeyl_of_lt 4 hirrQ (k := 0) (by norm_num)]
  rw [(minusFrame 4 b c).toHypFrame.longWeyl_mul_self
    (succ_ne_of_lt 4 (k := 0) (by norm_num)) true false]
  have hneg : (-1 : Kˣ) = 1 := by
    apply Units.ext
    simp [CharTwo.neg_eq]
  rw [hneg, map_one]

private theorem omMinusTwo_false_of_mu_zero
    {k : Type} [Field k] [CharP k 2]
    {W : Type} [AddCommGroup W] [Module k W] [Module.Finite k W]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) W} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1)
    {y : W} {χ : spinGroup (quadMinus 4 K b c) → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ 0)
    (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) : False := by
  obtain ⟨β, hβ⟩ := (o8mDatum hirrQ).iso_of_isCurtisType hρ
    (omMinus_isSimpleRep_trivial (spinGroup (quadMinus 4 K b c))) ht
    (isCurtisType_omMinus_two_trivial hirrQ hχ)
  obtain ⟨g, hg⟩ := hρ1
  refine hg ?_
  ext v
  exact β.injective (by simpa using hβ g v)

private theorem omMinusTwo_false_of_mu_natural (hK : Nat.card K = 2)
    {k : Type} [Field k] [CharP k 2]
    {W : Type} [AddCommGroup W] [Module k W] [Module.Finite k W]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) W} (hρ : IsSimpleRep ρ)
    {y : W} {χ : spinGroup (quadMinus 4 K b c) → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ
      (fun s : Fin 3 => if s.val = 0 then (1 : k) else 0))
    (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1)
    (hdim : Module.finrank k W = 16) : False := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let φ : K →+* k :=
    (ZMod.castHom (dvd_refl 2) k).comp
      ((ZMod.ringEquiv K hK').symm : K →+* ZMod 2)
  obtain ⟨β, -⟩ := (o8mDatum hirrQ).iso_of_isCurtisType hρ
    (SmallO8mCurtis.naturalRep_isSimple (m := 4) (by norm_num) hirrQ φ) ht
    (isCurtisType_omMinus_two_natural hirrQ hK φ hχ)
  have hfr := β.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card] at hfr
  simp at hfr
  omega

private theorem omMinusTwo_mu_eq_zero {k : Type} [Field k] {μ : Fin 3 → k}
    (h0 : μ 0 = 0) (h1 : μ 1 = 0) (h2 : μ 2 = 0) : μ = 0 := by
  funext s
  fin_cases s <;> simp [h0, h1, h2]

private theorem omMinusTwo_mu_eq_single_two {k : Type} [Field k] {μ : Fin 3 → k}
    (h0 : μ 0 = 0) (h1 : μ 1 = 0) (h2 : μ 2 = 1) : μ = Pi.single 2 (1 : k) := by
  funext s
  fin_cases s
  · show μ 0 = (Pi.single 2 (1 : k) : Fin 3 → k) 0
    rw [h0, Pi.single_eq_of_ne (show (0 : Fin 3) ≠ 2 by decide)]
  · show μ 1 = (Pi.single 2 (1 : k) : Fin 3 → k) 1
    rw [h1, Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  · show μ 2 = (Pi.single 2 (1 : k) : Fin 3 → k) 2
    rw [h2, Pi.single_eq_same]

private theorem omMinusTwo_mu_eq_single_one {k : Type} [Field k] {μ : Fin 3 → k}
    (h0 : μ 0 = 0) (h1 : μ 1 = 1) (h2 : μ 2 = 0) : μ = Pi.single 1 (1 : k) := by
  funext s
  fin_cases s
  · show μ 0 = (Pi.single 1 (1 : k) : Fin 3 → k) 0
    rw [h0, Pi.single_eq_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
  · show μ 1 = (Pi.single 1 (1 : k) : Fin 3 → k) 1
    rw [h1, Pi.single_eq_same]
  · show μ 2 = (Pi.single 1 (1 : k) : Fin 3 → k) 2
    rw [h2, Pi.single_eq_of_ne (show (2 : Fin 3) ≠ 1 by decide)]

private theorem omMinusTwo_mu_eq_natural {k : Type} [Field k] {μ : Fin 3 → k}
    (h0 : μ 0 = 1) (h1 : μ 1 = 0) (h2 : μ 2 = 0) :
    μ = (fun s : Fin 3 => if s.val = 0 then (1 : k) else 0) := by
  funext s
  fin_cases s <;> simp [h0, h1, h2]

private theorem omMinusTwo_false_of_curtisType (hK : Nat.card K = 2)
    {k : Type} [Field k] [CharP k 2]
    {W : Type} [AddCommGroup W] [Module k W] [Module.Finite k W]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) W} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1)
    {y : W} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ)
    (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1)
    (hdim : Module.finrank k W = 16) : False := by
  classical
  obtain ⟨hμ01, _⟩ := omMinus_two_mu_cases hirrQ hK ht
  rcases hμ01 0 with h0 | h0 <;> rcases hμ01 1 with h1 | h1 <;>
    rcases hμ01 2 with h2 | h2
  · exact omMinusTwo_false_of_mu_zero hirrQ hρ hρ1
      (by simpa [omMinusTwo_mu_eq_zero h0 h1 h2] using ht) hχ
  · have h17 := omMinus_two_seventeen_le_finrank_of_single hirrQ hK hρ ht hχ
      (Or.inr (omMinusTwo_mu_eq_single_two h0 h1 h2))
    omega
  · have h17 := omMinus_two_seventeen_le_finrank_of_single hirrQ hK hρ ht hχ
      (Or.inl (omMinusTwo_mu_eq_single_one h0 h1 h2))
    omega
  · have h17 := omMinus_two_seventeen_le_finrank_of_pair hirrQ hK hρ ht hχ
      (i := 1) (j := 2) (by decide) h1 h2
    omega
  · exact omMinusTwo_false_of_mu_natural hirrQ hK hρ
      (by simpa [omMinusTwo_mu_eq_natural h0 h1 h2] using ht) hχ hdim
  · have h17 := omMinus_two_seventeen_le_finrank_of_pair hirrQ hK hρ ht hχ
      (i := 0) (j := 2) (by decide) h0 h2
    omega
  · have h17 := omMinus_two_seventeen_le_finrank_of_pair hirrQ hK hρ ht hχ
      (i := 0) (j := 1) (by decide) h0 h1
    omega
  · have h17 := omMinus_two_seventeen_le_finrank_of_pair hirrQ hK hρ ht hχ
      (i := 0) (j := 1) (by decide) h0 h1
    omega

include hirrQ in
private theorem omMinusTwo_card_endRing_eq_two_of_small (hK : Nat.card K = 2) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v) (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀)
    (hsmall : 2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) <
      Module.finrank (ZMod 2) V) :
    Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) = 2 := by
  have hρirr : ρ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).2 hρ
  have hsymm : s.symm = s := by
    ext v
    have h := congrArg s.symm (hs v)
    simpa using h.symm
  have hN : ∀ g, ∃ g', ∀ w, s (ρ g (s w)) = ρ g' w := by
    intro g
    exact ⟨α g, fun w => by simpa [hsymm] using hα g w⟩
  have hcomm := commute_endRing_of_two_mul_finrank_range_lt ρ hρirr s hs hN hsmall
  exact omMinus_two_card_endRing_eq_two_of_outer hirrQ hK hρirr s α hα hα2 houter hcomm

private theorem omMinusTwo_chi_eq_one_on_H {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V}
    (hρirr : ρ.IsIrreducible) {k : Type} [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) k]
    {y : k ⊗[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule] ρ.asModule}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ μ)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) = 2) :
    ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1 := by
  have : Module.Finite (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
  have : Finite (spinGroup (quadMinus 4 K b c)) := inferInstance
  intro h hh
  have h2 : χ h ^ 2 = χ h := by
    have hpow := CFSG.HardMathSupport.GuralnickMalle.isCurtisType_chi_pow_card
      ρ (o8mDatum hirrQ) k ht hh
    simpa [hE] using hpow
  have hne : χ h ≠ 0 := by
    intro h0
    have hmul : χ h * χ h⁻¹ = 1 := by
      rw [← ht.chi_mul hh ((o8mDatum hirrQ).H.inv_mem hh), mul_inv_cancel, ht.chi_one]
    rw [h0, zero_mul] at hmul
    exact zero_ne_one hmul
  have hzero : χ h * (χ h - 1) = 0 := by
    rw [mul_sub, mul_one, ← sq, sub_eq_zero]
    exact h2
  rcases mul_eq_zero.mp hzero with h0 | h1
  · exact absurd h0 hne
  · exact sub_eq_zero.mp h1

include hirrQ in
theorem omMinus_two_false_of_card_endRing_eq_two (hK : Nat.card K = 2) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) = 2)
    (h16 : Module.finrank (ZMod 2) V = 16) : False := by
  have : Module.Finite (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
  have hρirr : ρ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).2 hρ
  let E := Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c))) ρ.asModule
  let k := AlgebraicClosure E
  have : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  let τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  have hτ : IsSimpleRep τ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  have : Finite (spinGroup (quadMinus 4 K b c)) := inferInstance
  have : Finite (CFSG.LieType.RootSystem.coxeterMatrix
      (isFiniteType_cartanB 3)).Group :=
    CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanB 3)
  obtain ⟨y, χ, μ, ht⟩ := (o8mDatum hirrQ).exists_isCurtisType
    (SmallO8mCurtis.curtisDatum_splitOver hirrQ) hτ
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hdim : Module.finrank k (k ⊗[E] ρ.asModule) = 16 := by
    have h :=
      CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.card_eq_pow_finrank_extendScalars ρ k
    rw [hcardV, h16,
      show Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
        ρ.asModule) = 2 from hE] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  have hχ1 : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1 :=
    omMinusTwo_chi_eq_one_on_H hirrQ hρirr ht hE
  have hτ1 : ∃ g, τ g ≠ 1 := by
    obtain ⟨g, hg⟩ := hρ1
    exact ⟨g, fun h => hg
      ((CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.extendScalars_endFieldRep_eq_one_iff
        ρ k g).mp h)⟩
  have : Module.Finite E ρ.asModule :=
    Module.finite_iff_finite.mpr (CFSG.HardMathSupport.GuralnickMalle.finite_asModule ρ)
  have : Module.Finite k (k ⊗[E] ρ.asModule) := Module.Finite.base_change E k ρ.asModule
  exact omMinusTwo_false_of_curtisType hirrQ hK hτ hτ1 ht hχ1 hdim

include hirrQ in
theorem omMinus_two_outer_four_le_of_finrank_eq_sixteen (hK : Nat.card K = 2) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) (h16 : Module.finrank (ZMod 2) V = 16)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v) (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) := by
  by_contra hlt
  have hlt' : Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) < 4 :=
    not_le.mp hlt
  have hsmall : 2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) <
      Module.finrank (ZMod 2) V := by
    rw [h16]; omega
  have hE := omMinusTwo_card_endRing_eq_two_of_small hirrQ hK hρ s hs α hα hα2 houter hsmall
  exact omMinus_two_false_of_card_endRing_eq_two hirrQ hK hρ hρ1 hE h16

include hirrQ in
theorem omMinus_two_outer_natural_or_four_le (hK : Nat.card K = 2) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v)
    (α : MulAut (spinGroup (quadMinus 4 K b c))) (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v)
    (hα2 : α * α = 1) (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    (∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) := by
  by_cases hnat : ∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K),
    f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v
  · exact Or.inl hnat
  · refine Or.inr ?_
    by_cases hsmall : 2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) <
        Module.finrank (ZMod 2) V
    · have hE :=
        omMinusTwo_card_endRing_eq_two_of_small hirrQ hK hρ s hs α hα hα2 houter hsmall
      exact omMinus_two_outer_four_le hirrQ hK hρ hρ1 hE hnat s α hα hα2 houter
    · have hge : Module.finrank (ZMod 2) V ≤
          2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) := not_lt.mp hsmall
      have : Module.Finite (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
      have hdim8 : 8 ≤ Module.finrank (ZMod 2) V := by
        have hrep := omMinus_two_natural_or_four_le hirrQ hK hρ hρ1
          (omMinusTwo_n0_sq hirrQ) (omMinusTwo_n_ne_one hirrQ 0)
        rcases hrep with hnat' | hfour
        · exact absurd hnat' hnat
        · have hT : ρ ((o8mDatum hirrQ).n 0) * ρ ((o8mDatum hirrQ).n 0) = 1 := by
            rw [← map_mul, omMinusTwo_n0_sq hirrQ, map_one]
          have hbound := omMinusTwo_two_mul_finrank_range_le
            (T := ρ ((o8mDatum hirrQ).n 0)) hT
          omega
      omega

end CFSG.LocalAnalysis.WeakClosure81
