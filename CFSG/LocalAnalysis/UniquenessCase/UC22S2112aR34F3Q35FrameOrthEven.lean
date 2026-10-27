module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.LieType.HighestRoot.CentTrialitySL2
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalGeometry
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Core
import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
import CFSG.ClassicalInvolution.RouteD.ExoticSingleFacts
import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
import CFSG.ClassicalInvolution.Asc77.AscR10E23
import CFSG.ClassicalInvolution.ModelFacts.Models
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationFrattini
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35OrthFour
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.GH74.Generic.S1.LinFull
import CFSG.LieType.HighestRoot.CentTrialityMain
import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Defs
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Solomon
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RRes
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)

section EvenOrthHelpers

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
open scoped MatrixGroups

private theorem commutator_pow_eq_one_of_commute' {G : Type} [Group G] {g u : G} {p : ℕ}
    (hz : Commute (g * u * g⁻¹ * u⁻¹) u) (hu : u ^ p = 1) : (g * u * g⁻¹ * u⁻¹) ^ p = 1 := by
  have h1 : g * u * g⁻¹ = (g * u * g⁻¹ * u⁻¹) * u := by group
  have h2 : (g * u * g⁻¹) ^ p = 1 := by rw [conj_pow, hu, mul_one, mul_inv_cancel]
  rwa [h1, hz.mul_pow, hu, mul_one] at h2

private theorem commute_map_of_pow_eq_one_of_scalars {K X F V : Type} [Group K] [Group X]
    [Field F] [AddCommGroup V] [Module F V] [Nontrivial V] {p : ℕ} [Fact p.Prime] [CharP F p]
    {ψ : K →* X} (hker : ψ.ker ≤ center K) {θ : K →* (V ≃ₗ[F] V)}
    (hθZ : ∀ z ∈ center K, θ z ∈ CFSG.ClassicalGroups.Orthogonal.scalars F V) {g y : K}
    (hc : Commute (ψ g) (ψ y)) (hyp : y ^ p = 1) : Commute (θ g) (θ y) := by
  have hzy : g * y * g⁻¹ * y⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hc.eq]
    group
  have hzc := hker hzy
  have hzpow : (g * y * g⁻¹ * y⁻¹) ^ p = 1 :=
    commutator_pow_eq_one_of_commute' (Subgroup.mem_center_iff.mp hzc y).symm hyp
  obtain ⟨c, hcz⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.mp (hθZ _ hzc)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hpow : ∀ k : ℕ, (θ (g * y * g⁻¹ * y⁻¹) ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, LinearEquiv.mul_apply, hcz, map_smul, ih, smul_smul, ← pow_succ']
  have hcp : c ^ p = 1 := by
    have h1 := hpow p
    rw [← map_pow, hzpow, map_one] at h1
    have h1' : v = c ^ p • v := h1
    have h4 : (c ^ p - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← h1', sub_self]
    rcases smul_eq_zero.mp h4 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  have hc1 : c = 1 := frobenius_inj F p (by rw [frobenius_def, frobenius_def, hcp, one_pow])
  have hz1 : θ (g * y * g⁻¹ * y⁻¹) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    rw [hcz, hc1, one_smul]
    rfl
  simp only [map_mul, map_inv] at hz1
  calc θ g * θ y = (θ g * θ y * (θ g)⁻¹ * (θ y)⁻¹) * (θ y * θ g) := by group
    _ = θ y * θ g := by rw [hz1, one_mul]

private theorem commute_map_of_mem_of_equiv_sl2 {K X F F' V : Type} [Group K] [Group X]
    [Field F] [Field F'] [AddCommGroup V] [Module F V] [Nontrivial V] {p : ℕ} [Fact p.Prime]
    [CharP F p] [CharP F' p] {ψ : K →* X} (hker : ψ.ker ≤ center K) {θ : K →* (V ≃ₗ[F] V)}
    (hθZ : ∀ z ∈ center K, θ z ∈ CFSG.ClassicalGroups.Orthogonal.scalars F V)
    {R : Subgroup K} (e : R ≃* SL(2, F')) {g : K}
    (hg : ψ g ∈ centralizer ((R.map ψ : Subgroup X) : Set X)) {y : K} (hy : y ∈ R) :
    Commute (θ g) (θ y) := by
  let S : Subgroup R :=
    (Subgroup.centralizer ({θ g} : Set (V ≃ₗ[F] V))).comap (θ.comp R.subtype)
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← CFSG.LieType.HighestRoot.closure_pow_eq_one_eq_top_of_mulEquiv p e,
      Subgroup.closure_le]
    intro z hz
    change θ z ∈ Subgroup.centralizer ({θ g} : Set (V ≃ₗ[F] V))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzpow : (z : K) ^ p = 1 := by
      have := congrArg (fun w : R => (w : K)) hz
      simpa using this
    have hc : Commute (ψ g) (ψ z) :=
      (Subgroup.mem_centralizer_iff.mp hg (ψ z) (Subgroup.mem_map_of_mem ψ z.2)).symm
    exact (commute_map_of_pow_eq_one_of_scalars hker hθZ hc hzpow).symm
  have hyS : (⟨y, hy⟩ : R) ∈ S := hS.symm ▸ Subgroup.mem_top _
  change θ y ∈ Subgroup.centralizer ({θ g} : Set (V ≃ₗ[F] V)) at hyS
  rw [Subgroup.mem_centralizer_singleton_iff] at hyS
  exact hyS.symm

private theorem forall_incl_eq_of_commute_frame {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} (h2 : (2 : F) ≠ 0) {r a : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {Fr : Frame Q} {h : V ≃ₗ[F] V}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ A : SL(2, F), h * Fr.La A = Fr.La A * h)
    (hR : ∀ A : SL(2, F), h * Fr.swap.La A = Fr.swap.La A * h) :
    ∀ X, h (Fr.incl X) = Fr.incl X := by
  obtain ⟨μ, hμ, hW⟩ := CFSG.ComponentClassification.HarrisLit.T1.S74.exists_smul_of_commute_La
    Fr h2 hhO (hL (-1)) hL hR
  have hv : Fr.incl (1 : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    intro h0
    apply one_ne_zero (α := Matrix (Fin 2) (Fin 2) F)
    exact Fr.incl_injective (by simpa using h0)
  have hμpow : μ ^ (r ^ a) = 1 := by
    have hsmul : ∀ k : ℕ, (h ^ k) (Fr.incl 1) = μ ^ k • Fr.incl 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, LinearEquiv.mul_apply, hW, map_smul, ih, smul_smul, ← pow_succ']
    have h1 : μ ^ (r ^ a) • Fr.incl 1 = 1 • Fr.incl 1 := by
      rw [← hsmul (r ^ a), hpow]
      simp
    exact smul_left_injective F hv (by simpa using h1)
  have hodd : Odd (r ^ a) := (Nat.Prime.odd_of_ne_two hr hr2).pow
  have hμeq : μ ^ (r ^ a) = μ := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, show μ ^ 2 = 1 by rw [pow_two, hμ], one_pow, one_mul]
  have hμ1 : μ = 1 := by rw [← hμeq, hμpow]
  intro X
  rw [hW X, hμ1, one_smul]

private theorem sq_eq_one_of_smul_mem_orthogonalGroup {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} (Fr : Frame Q) {h : V ≃ₗ[F] V}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {s : F} (hs : ∀ v, h v = s • v) :
    s ^ 2 = 1 := by
  have h1 := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hhO) (Fr.incl 1)
  rw [hs, QuadraticMap.map_smul, Frame.Q_incl, Matrix.det_one, smul_eq_mul, mul_one] at h1
  rw [pow_two]
  exact h1

private theorem not_dvd_mul_sq_sub_one_of_three_or_five {p r : ℕ} (hp35 : p = 3 ∨ p = 5)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) : ¬ r ∣ p ^ 1 * ((p ^ 1) ^ 2 - 1) := by
  intro hd
  have hle : r ≤ 120 := by
    have := Nat.le_of_dvd (by rcases hp35 with rfl | rfl <;> norm_num) hd
    rcases hp35 with rfl | rfl <;> norm_num at this <;> omega
  rcases hp35 with rfl | rfl <;> interval_cases r <;> (revert hd hr hrp; norm_num)

private theorem eq_bot_of_isPGroup_of_forall_pow {G : Type} [Group G] {r : ℕ} {B : Subgroup G}
    (hB : IsPGroup r B) (h : ∀ x ∈ B, ∀ a : ℕ, x ^ (r ^ a) = 1 → x = 1) : B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha⟩ := hB ⟨x, hx⟩
  exact Subgroup.mem_bot.2 (h x hx a (by simpa using congrArg Subtype.val ha))

private theorem factorization_two_eq_three_of_eq {N k : ℕ} (hN : N = 2 ^ 3 * k)
    (hk : ¬ 2 ∣ k) : N.factorization 2 = 3 := by
  subst hN
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (dvd_zero 2)
  rw [Nat.factorization_mul (by norm_num) hk0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hk]
  rfl

end EvenOrthHelpers

section EvenOrthLinear

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
open scoped MatrixGroups

private theorem fixes_pairs_of_commute_plusPairFrames {F : Type} [Field F]
    {n r a : ℕ} (hn : 3 ≤ n) (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    {h : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      h * (plusOrthogonalPairFrame F n hn j).La A =
        (plusOrthogonalPairFrame F n hn j).La A * h)
    (hR : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      h * (plusOrthogonalPairFrame F n hn j).swap.La A =
        (plusOrthogonalPairFrame F n hn j).swap.La A * h) :
    ∀ i : Fin n, i.val < 2 * (n / 2) →
      h (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inr i) 1 := by
  intro i hi
  have hlt : i.val / 2 < n / 2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  let j : Fin (n / 2) := ⟨i.val / 2, hlt⟩
  have hcases : i.val = 2 * j.val ∨ i.val = 2 * j.val + 1 := by
    have hmod := Nat.mod_two_eq_zero_or_one i.val
    have hdm : 2 * (i.val / 2) + i.val % 2 = i.val := Nat.div_add_mod i.val 2
    have hj : (j : ℕ) = i.val / 2 := rfl
    rw [hj]
    rcases hmod with h0 | h1 <;> omega
  have hfix := forall_incl_eq_of_commute_frame (Fr := plusOrthogonalPairFrame F n hn j) h2 hr hr2
    hhO hpow (hL j) (hR j)
  have h1 : (plusOrthogonalPairFrame F n hn j).incl (Matrix.single 0 0 1) =
      Pi.single (Sum.inl ⟨2 * j.val, by omega⟩) (1 : F) := by
    rw [Frame.incl_apply]
    simp
    rfl
  have h2' : (plusOrthogonalPairFrame F n hn j).incl (Matrix.single 1 1 1) =
      Pi.single (Sum.inr ⟨2 * j.val, by omega⟩) (1 : F) := by
    rw [Frame.incl_apply]
    simp
    rfl
  have h3 : (plusOrthogonalPairFrame F n hn j).incl (Matrix.single 0 1 (-1)) =
      Pi.single (Sum.inr ⟨2 * j.val + 1, by omega⟩) (1 : F) := by
    rw [Frame.incl_apply]
    simp
    rfl
  have h4 : (plusOrthogonalPairFrame F n hn j).incl (Matrix.single 1 0 1) =
      Pi.single (Sum.inl ⟨2 * j.val + 1, by omega⟩) (1 : F) := by
    rw [Frame.incl_apply]
    simp
    rfl
  rcases hcases with hcase | hcase
  · have hi' : i = ⟨2 * j.val, by omega⟩ := Fin.ext hcase
    rw [hi']
    refine ⟨?_, ?_⟩
    · have := hfix (Matrix.single 0 0 1)
      rwa [h1] at this
    · have := hfix (Matrix.single 1 1 1)
      rwa [h2'] at this
  · have hi' : i = ⟨2 * j.val + 1, by omega⟩ := Fin.ext hcase
    rw [hi']
    refine ⟨?_, ?_⟩
    · have := hfix (Matrix.single 1 0 1)
      rwa [h4] at this
    · have := hfix (Matrix.single 0 1 (-1))
      rwa [h3] at this

private theorem maps_residual_of_forall_fix_basis_plus {F : Type} [Field F] {n : ℕ}
    {g : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F))
    (hfix : ∀ i : Fin n, i.val < 2 * (n / 2) →
      g (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      g (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inr i) 1)
    {w : Fin n ⊕ Fin n → F}
    (hw : ∀ i : Fin n, i.val < 2 * (n / 2) →
      w (Sum.inl i) = 0 ∧ w (Sum.inr i) = 0) :
    ∀ i : Fin n, i.val < 2 * (n / 2) →
      (g w) (Sum.inl i) = 0 ∧ (g w) (Sum.inr i) = 0 := by
  intro i hi
  constructor
  · calc (g w) (Sum.inl i)
        = polar (quadPlus n F) (g w) (Pi.single (Sum.inr i) 1) :=
          (polar_quadPlus_single_inr n F (g w) i).symm
      _ = polar (quadPlus n F) (g w) (g (Pi.single (Sum.inr i) 1)) := by
          rw [(hfix i hi).2]
      _ = polar (quadPlus n F) w (Pi.single (Sum.inr i) 1) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO w _
      _ = w (Sum.inl i) := polar_quadPlus_single_inr n F w i
      _ = 0 := (hw i hi).1
  · calc (g w) (Sum.inr i)
        = polar (quadPlus n F) (g w) (Pi.single (Sum.inl i) 1) :=
          (polar_quadPlus_single_inl n F (g w) i).symm
      _ = polar (quadPlus n F) (g w) (g (Pi.single (Sum.inl i) 1)) := by
          rw [(hfix i hi).1]
      _ = polar (quadPlus n F) w (Pi.single (Sum.inl i) 1) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO w _
      _ = w (Sum.inr i) := polar_quadPlus_single_inl n F w i
      _ = 0 := (hw i hi).2

private theorem eq_one_of_commute_plusPairFrames_even {F : Type} [Field F] {m r a : ℕ}
    (hn : 3 ≤ 2 * m) (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    {h : (Fin (2 * m) ⊕ Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) ⊕ Fin (2 * m) → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus (2 * m) F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin ((2 * m) / 2)) (A : SL(2, F)),
      h * (plusOrthogonalPairFrame F (2 * m) hn j).La A =
        (plusOrthogonalPairFrame F (2 * m) hn j).La A * h)
    (hR : ∀ (j : Fin ((2 * m) / 2)) (A : SL(2, F)),
      h * (plusOrthogonalPairFrame F (2 * m) hn j).swap.La A =
        (plusOrthogonalPairFrame F (2 * m) hn j).swap.La A * h) :
    h = 1 := by
  have hpair := fixes_pairs_of_commute_plusPairFrames hn h2 hr hr2 hhO hpow hL hR
  have hall : ∀ i : Fin (2 * m), i.val < 2 * ((2 * m) / 2) := by
    intro i
    rw [show (2 * m) / 2 = m by omega]
    omega
  have hfix_all : ∀ x : Fin (2 * m) ⊕ Fin (2 * m),
      h (Pi.single x 1) = Pi.single x 1 := by
    rintro (i | i)
    · exact (hpair i (hall i)).1
    · exact (hpair i (hall i)).2
  have hlin : h.toLinearMap = 1 := by
    refine LinearMap.pi_ext fun x c' => ?_
    have hsingle : Pi.single x c' = c' • Pi.single x (1 : F) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    calc h (Pi.single x c') = h (c' • Pi.single x (1 : F)) := by rw [hsingle]
      _ = c' • h (Pi.single x 1) := map_smul h c' _
      _ = c' • Pi.single x 1 := by rw [hfix_all x]
      _ = Pi.single x c' := hsingle.symm
  exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun hlin v

private noncomputable def plusResidualSub (m : ℕ) (F : Type) [Field F] :
    Submodule F (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F) where
  carrier := {w | ∀ i : Fin (2 * m + 1), i.val < 2 * m →
    w (Sum.inl i) = 0 ∧ w (Sum.inr i) = 0}
  zero_mem' := by
    intro i _
    simp
  add_mem' {a b} ha hb := by
    intro i hi
    rw [Pi.add_apply, Pi.add_apply, (ha i hi).1, (hb i hi).1, (ha i hi).2, (hb i hi).2]
    simp
  smul_mem' c a ha := by
    intro i hi
    rw [Pi.smul_apply, Pi.smul_apply, (ha i hi).1, (ha i hi).2]
    simp

private theorem mem_plusResidualSub {m : ℕ} {F : Type} [Field F]
    {w : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F} :
    w ∈ plusResidualSub m F ↔ ∀ i : Fin (2 * m + 1), i.val < 2 * m →
      w (Sum.inl i) = 0 ∧ w (Sum.inr i) = 0 := Iff.rfl

private noncomputable def plusResidualCoord (m : ℕ) (F : Type) [Field F] :
    (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F) →ₗ[F] (Fin 1 ⊕ Fin 1 → F) where
  toFun v := fun x =>
    match x with
    | Sum.inl _ => v (Sum.inl ⟨2 * m, by omega⟩)
    | Sum.inr _ => v (Sum.inr ⟨2 * m, by omega⟩)
  map_add' v w := by
    funext x
    rcases x with i | i <;> simp
  map_smul' c v := by
    funext x
    rcases x with i | i <;> simp

private noncomputable def plusResidualIncl (m : ℕ) (F : Type) [Field F] :
    (Fin 1 ⊕ Fin 1 → F) →ₗ[F] (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F) where
  toFun t := fun x =>
    match x with
    | Sum.inl i => if i.val = 2 * m then t (Sum.inl 0) else 0
    | Sum.inr i => if i.val = 2 * m then t (Sum.inr 0) else 0
  map_add' t s := by
    funext x
    rcases x with i | i <;> by_cases hi : i.val = 2 * m <;> simp [hi]
  map_smul' c t := by
    funext x
    rcases x with i | i <;> by_cases hi : i.val = 2 * m <;> simp [hi]

private theorem plusResidualCoord_comp_incl (m : ℕ) (F : Type) [Field F]
    (t : Fin 1 ⊕ Fin 1 → F) :
    plusResidualCoord m F (plusResidualIncl m F t) = t := by
  funext x
  rcases x with i | i
  · have hi : i = 0 := Fin.fin_one_eq_zero i
    rw [hi]
    simp [plusResidualCoord, plusResidualIncl]
  · have hi : i = 0 := Fin.fin_one_eq_zero i
    rw [hi]
    simp [plusResidualCoord, plusResidualIncl]

private theorem plusResidualIncl_mem (m : ℕ) (F : Type) [Field F]
    (t : Fin 1 ⊕ Fin 1 → F) :
    plusResidualIncl m F t ∈ plusResidualSub m F := by
  intro i hi
  have hne : i.val ≠ 2 * m := by omega
  simp [plusResidualIncl, hne]

private theorem plusResidualIncl_coord_of_mem (m : ℕ) (F : Type) [Field F]
    {w : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F}
    (hw : w ∈ plusResidualSub m F) :
    plusResidualIncl m F (plusResidualCoord m F w) = w := by
  funext x
  rcases x with i | i
  · by_cases hi : i.val = 2 * m
    · have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hi
      rw [hi']
      simp [plusResidualIncl, plusResidualCoord]
    · have hlt : i.val < 2 * m := by omega
      have hw0 := (mem_plusResidualSub.mp hw) i hlt
      simp [plusResidualIncl, plusResidualCoord, hi, hw0.1]
  · by_cases hi : i.val = 2 * m
    · have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hi
      rw [hi']
      simp [plusResidualIncl, plusResidualCoord]
    · have hlt : i.val < 2 * m := by omega
      have hw0 := (mem_plusResidualSub.mp hw) i hlt
      simp [plusResidualIncl, plusResidualCoord, hi, hw0.2]

private noncomputable def plusResidualEquiv (m : ℕ) (F : Type) [Field F] :
    plusResidualSub m F ≃ₗ[F] (Fin 1 ⊕ Fin 1 → F) where
  toFun w := plusResidualCoord m F (w : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F)
  invFun t := ⟨plusResidualIncl m F t, plusResidualIncl_mem m F t⟩
  map_add' x y := map_add (plusResidualCoord m F)
    (x : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F)
    (y : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F)
  map_smul' c x := map_smul (plusResidualCoord m F) c
    (x : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F)
  left_inv w := Subtype.ext (plusResidualIncl_coord_of_mem m F w.2)
  right_inv t := plusResidualCoord_comp_incl m F t

private theorem quadPlus_comp_plusResidualSub (m : ℕ) (F : Type) [Field F]
    (w : plusResidualSub m F) :
    quadPlus (2 * m + 1) F w = quadPlus 1 F (plusResidualEquiv m F w) := by
  obtain ⟨v, hv⟩ := w
  have hlast : quadPlus (2 * m + 1) F v =
      v (Sum.inl (Fin.last (2 * m))) * v (Sum.inr (Fin.last (2 * m))) := by
    rw [quadPlus_apply, Fin.sum_univ_castSucc]
    have hzero : ∀ i : Fin (2 * m),
        v (Sum.inl (Fin.castSucc i)) * v (Sum.inr (Fin.castSucc i)) = 0 := by
      intro i
      have hi := (mem_plusResidualSub.mp hv) (Fin.castSucc i) (by simp)
      rw [hi.1, hi.2, mul_zero]
    rw [Finset.sum_eq_zero (fun i _ => hzero i), zero_add]
  have hfl : (Fin.last (2 * m) : Fin (2 * m + 1)) = ⟨2 * m, by omega⟩ := rfl
  rw [hlast, hfl]
  simp [plusResidualEquiv, plusResidualCoord, quadPlus_apply]

private theorem card_orthogonalGroup_plusResidual (m : ℕ) (F : Type) [Field F] [Finite F] :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadPlus (2 * m + 1) F).comp (plusResidualSub m F).subtype)) =
      2 * (Nat.card F - 1) := by
  let W₀ := plusResidualSub m F
  let iso : ((quadPlus (2 * m + 1) F).comp W₀.subtype).IsometryEquiv (quadPlus 1 F) :=
    { toLinearEquiv := plusResidualEquiv m F
      map_app' := fun w => (quadPlus_comp_plusResidualSub m F w).symm }
  rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr iso]
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := F) 0
  have h' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 1 F)) : ℤ) =
      2 * ((Nat.card F : ℤ) - 1) := by simpa using h
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hcast : ((2 * (Nat.card F - 1) : ℕ) : ℤ) = 2 * ((Nat.card F : ℤ) - 1) := by
    push_cast [hq1]
    ring
  rw [← hcast] at h'
  exact_mod_cast h'

private theorem eq_one_of_commute_plusPairFrames_odd {F : Type} [Field F] [Finite F]
    {m r a : ℕ} (hn : 3 ≤ 2 * m + 1) (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1))
    {h : (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F) ≃ₗ[F]
      (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus (2 * m + 1) F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin ((2 * m + 1) / 2)) (A : SL(2, F)),
      h * (plusOrthogonalPairFrame F (2 * m + 1) hn j).La A =
        (plusOrthogonalPairFrame F (2 * m + 1) hn j).La A * h)
    (hR : ∀ (j : Fin ((2 * m + 1) / 2)) (A : SL(2, F)),
      h * (plusOrthogonalPairFrame F (2 * m + 1) hn j).swap.La A =
        (plusOrthogonalPairFrame F (2 * m + 1) hn j).swap.La A * h) :
    h = 1 := by
  have hlt2 : 2 * ((2 * m + 1) / 2) = 2 * m := by omega
  have hpair := fixes_pairs_of_commute_plusPairFrames hn h2 hr hr2 hhO hpow hL hR
  have hpair' : ∀ i : Fin (2 * m + 1), i.val < 2 * m →
      h (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inr i) 1 :=
    fun i hi => hpair i (by rw [hlt2]; exact hi)
  have hfixinv : ∀ i : Fin (2 * m + 1), i.val < 2 * m →
      h⁻¹ (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h⁻¹ (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inr i) 1 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · have h1 : h⁻¹ (h (Pi.single (Sum.inl i) 1)) = Pi.single (Sum.inl i) 1 :=
        LinearEquiv.symm_apply_apply h _
      rw [(hpair' i hi).1] at h1
      exact h1
    · have h1 : h⁻¹ (h (Pi.single (Sum.inr i) 1)) = Pi.single (Sum.inr i) 1 :=
        LinearEquiv.symm_apply_apply h _
      rw [(hpair' i hi).2] at h1
      exact h1
  let W₀ := plusResidualSub m F
  have hsta : h ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub W₀ := by
    intro x
    constructor
    · intro hx
      have hx' : ∀ i : Fin (2 * m + 1), i.val < 2 * ((2 * m + 1) / 2) →
          x (Sum.inl i) = 0 ∧ x (Sum.inr i) = 0 :=
        fun i hi => hx i (by rw [hlt2] at hi; exact hi)
      have hx'' := maps_residual_of_forall_fix_basis_plus hhO
        (fun i hi => hpair' i (by rw [hlt2] at hi; exact hi)) hx'
      exact fun i hi => hx'' i (by rw [hlt2]; exact hi)
    · intro hx
      have hx' : ∀ i : Fin (2 * m + 1), i.val < 2 * ((2 * m + 1) / 2) →
          (h x) (Sum.inl i) = 0 ∧ (h x) (Sum.inr i) = 0 :=
        fun i hi => hx i (by rw [hlt2] at hi; exact hi)
      have hx'' := maps_residual_of_forall_fix_basis_plus (Subgroup.inv_mem _ hhO)
        (fun i hi => hfixinv i (by rw [hlt2] at hi; exact hi)) hx'
      have hx3 : ∀ i : Fin (2 * m + 1), i.val < 2 * ((2 * m + 1) / 2) →
          x (Sum.inl i) = 0 ∧ x (Sum.inr i) = 0 := by
        simpa [LinearEquiv.symm_apply_apply] using hx''
      exact fun i hi => hx3 i (by rw [hlt2]; exact hi)
  let ν : W₀ ≃ₗ[F] W₀ := CFSG.ClassicalGroups.Orthogonal.Small.resHom W₀ ⟨h, hsta⟩
  have hνO : ν ∈ TauCeti.QuadraticMap.orthogonalGroup
      ((quadPlus (2 * m + 1) F).comp W₀.subtype) :=
    CFSG.ClassicalGroups.Orthogonal.Small.resHom_mem_orthogonalGroup hhO hsta
  have hνpow : ν ^ (r ^ a) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    apply Subtype.ext
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_pow_apply hsta]
    rw [hpow]
    rfl
  have hcard := card_orthogonalGroup_plusResidual m F
  have hnotdvd : ¬ r ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadPlus (2 * m + 1) F).comp W₀.subtype)) := by
    rw [hcard]
    intro hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with h2q | hq
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2q)
    · have hq2 : r ∣ Nat.card F ^ 2 - 1 := by
        have hsq := Nat.sq_sub_sq (Nat.card F) 1
        rw [one_pow] at hsq
        rw [hsq]
        exact dvd_mul_of_dvd_right hq _
      exact hrq (dvd_mul_of_dvd_right hq2 _)
  have hcopN : Nat.Coprime (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadPlus (2 * m + 1) F).comp W₀.subtype))) (r ^ a) :=
    ((Nat.Prime.coprime_iff_not_dvd hr).2 hnotdvd).symm.pow_right a
  let ν₀ : TauCeti.QuadraticMap.orthogonalGroup
      ((quadPlus (2 * m + 1) F).comp W₀.subtype) := ⟨ν, hνO⟩
  have hν₀pow : ν₀ ^ (r ^ a) = 1 := Subtype.ext hνpow
  have hν1 : ν = 1 := by
    have hdvd : orderOf ν₀ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        ((quadPlus (2 * m + 1) F).comp W₀.subtype)) := orderOf_dvd_natCard ν₀
    have hcop : Nat.Coprime (orderOf ν₀) (r ^ a) := hcopN.of_dvd_left hdvd
    have h1 : ν₀ = 1 := orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hν₀pow))
    exact Subtype.ext_iff.mp h1
  have hfixW : ∀ w : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) → F, w ∈ W₀ → h w = w := by
    intro w hw
    have h1 : ν ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hν1]; rfl
    have h2 := congrArg Subtype.val h1
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply] at h2
    exact h2
  have hfix_all : ∀ x : Fin (2 * m + 1) ⊕ Fin (2 * m + 1),
      h (Pi.single x 1) = Pi.single x 1 := by
    rintro (i | i)
    · by_cases hi : i.val < 2 * m
      · exact (hpair' i hi).1
      · have hge : i.val = 2 * m := by have := i.isLt; omega
        have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hge
        rw [hi']
        refine hfixW _ ?_
        intro j hj
        have hne : (Sum.inl j : Fin (2 * m + 1) ⊕ Fin (2 * m + 1)) ≠
            Sum.inl ⟨2 * m, by omega⟩ := by
          simp [Fin.ext_iff]
          omega
        simp [hne]
    · by_cases hi : i.val < 2 * m
      · exact (hpair' i hi).2
      · have hge : i.val = 2 * m := by have := i.isLt; omega
        have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hge
        rw [hi']
        refine hfixW _ ?_
        intro j hj
        have hne : (Sum.inr j : Fin (2 * m + 1) ⊕ Fin (2 * m + 1)) ≠
            Sum.inr ⟨2 * m, by omega⟩ := by
          simp [Fin.ext_iff]
          omega
        simp [hne]
  have hlin : h.toLinearMap = 1 := by
    refine LinearMap.pi_ext fun x c' => ?_
    have hsingle : Pi.single x c' = c' • Pi.single x (1 : F) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    calc h (Pi.single x c') = h (c' • Pi.single x (1 : F)) := by rw [hsingle]
      _ = c' • h (Pi.single x 1) := map_smul h c' _
      _ = c' • Pi.single x 1 := by rw [hfix_all x]
      _ = Pi.single x c' := hsingle.symm
  exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun hlin v

private theorem eq_one_of_commute_plusPairFrames {F : Type} [Field F] [Finite F] {n r a : ℕ}
    (hn : 3 ≤ n) (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1))
    {h : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      h * (plusOrthogonalPairFrame F n hn j).La A = (plusOrthogonalPairFrame F n hn j).La A * h)
    (hR : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      h * (plusOrthogonalPairFrame F n hn j).swap.La A =
        (plusOrthogonalPairFrame F n hn j).swap.La A * h) :
    h = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact eq_one_of_commute_plusPairFrames_even hn h2 hr hr2 hhO hpow hL hR
  · exact eq_one_of_commute_plusPairFrames_odd hn h2 hr hr2 hrq hhO hpow hL hR

private theorem fixes_pairs_of_commute_minusPairFrames {F : Type} [Field F]
    {n r a : ℕ} {b c : F} (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    {h : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin ((n - 1) / 2)) (A : SL(2, F)),
      h * (minusOrthogonalPairFrame F n b c j).La A =
        (minusOrthogonalPairFrame F n b c j).La A * h)
    (hR : ∀ (j : Fin ((n - 1) / 2)) (A : SL(2, F)),
      h * (minusOrthogonalPairFrame F n b c j).swap.La A =
        (minusOrthogonalPairFrame F n b c j).swap.La A * h) :
    ∀ i : Fin (n - 1), i.val < 2 * ((n - 1) / 2) →
      h (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1 := by
  intro i hi
  have hlt : i.val / 2 < (n - 1) / 2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  let j : Fin ((n - 1) / 2) := ⟨i.val / 2, hlt⟩
  have hcases : i.val = 2 * j.val ∨ i.val = 2 * j.val + 1 := by
    have hmod := Nat.mod_two_eq_zero_or_one i.val
    have hdm : 2 * (i.val / 2) + i.val % 2 = i.val := Nat.div_add_mod i.val 2
    have hj : (j : ℕ) = i.val / 2 := rfl
    rw [hj]
    rcases hmod with h0 | h1 <;> omega
  have hfix := forall_incl_eq_of_commute_frame h2 hr hr2 hhO hpow (hL j) (hR j)
  have h1 : (minusOrthogonalPairFrame F n b c j).incl (Matrix.single 0 0 1) =
      Pi.single (Sum.inl ⟨2 * j.val, by omega⟩) (1 : F) := by
    rw [Frame.incl_apply]
    simp [minusOrthogonalPairFrame, CFSG.LieType.Universal.Spin.HypFrame.toFrame]
    rfl
  have h2' : (minusOrthogonalPairFrame F n b c j).incl (Matrix.single 1 1 1) =
      Pi.single (Sum.inr (Sum.inl ⟨2 * j.val, by omega⟩)) (1 : F) := by
    rw [Frame.incl_apply]
    simp [minusOrthogonalPairFrame, CFSG.LieType.Universal.Spin.HypFrame.toFrame]
    rfl
  have h3 : (minusOrthogonalPairFrame F n b c j).incl (Matrix.single 0 1 (-1)) =
      Pi.single (Sum.inr (Sum.inl ⟨2 * j.val + 1, by omega⟩)) (1 : F) := by
    rw [Frame.incl_apply]
    simp [minusOrthogonalPairFrame, CFSG.LieType.Universal.Spin.HypFrame.toFrame]
    rfl
  have h4 : (minusOrthogonalPairFrame F n b c j).incl (Matrix.single 1 0 1) =
      Pi.single (Sum.inl ⟨2 * j.val + 1, by omega⟩) (1 : F) := by
    rw [Frame.incl_apply]
    simp [minusOrthogonalPairFrame, CFSG.LieType.Universal.Spin.HypFrame.toFrame]
    rfl
  rcases hcases with hcase | hcase
  · have hi' : i = ⟨2 * j.val, by omega⟩ := Fin.ext hcase
    rw [hi']
    exact ⟨by rw [← h1]; exact hfix _, by rw [← h2']; exact hfix _⟩
  · have hi' : i = ⟨2 * j.val + 1, by omega⟩ := Fin.ext hcase
    rw [hi']
    exact ⟨by rw [← h4]; exact hfix _, by rw [← h3]; exact hfix _⟩

private theorem maps_minusResidual_of_forall_fix_basis {F : Type} [Field F] {n : ℕ} {b c : F}
    {g : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c))
    (hfix : ∀ i : Fin (n - 1), i.val < 2 * ((n - 1) / 2) →
      g (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      g (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1)
    {w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F}
    (hw : ∀ i : Fin (n - 1), i.val < 2 * ((n - 1) / 2) →
      w (Sum.inl i) = 0 ∧ w (Sum.inr (Sum.inl i)) = 0) :
    ∀ i : Fin (n - 1), i.val < 2 * ((n - 1) / 2) →
      (g w) (Sum.inl i) = 0 ∧ (g w) (Sum.inr (Sum.inl i)) = 0 := by
  intro i hi
  constructor
  · calc (g w) (Sum.inl i)
        = polar (quadMinus n F b c) (g w) (Pi.single (Sum.inr (Sum.inl i)) 1) :=
          (CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl n F b c (g w) i).symm
      _ = polar (quadMinus n F b c) (g w) (g (Pi.single (Sum.inr (Sum.inl i)) 1)) := by
          rw [(hfix i hi).2]
      _ = polar (quadMinus n F b c) w (Pi.single (Sum.inr (Sum.inl i)) 1) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO w _
      _ = w (Sum.inl i) :=
          CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl n F b c w i
      _ = 0 := (hw i hi).1
  · calc (g w) (Sum.inr (Sum.inl i))
        = polar (quadMinus n F b c) (g w) (Pi.single (Sum.inl i) 1) :=
          (CFSG.LieType.Universal.Spin.polar_quadMinus_single_inl n F b c (g w) i).symm
      _ = polar (quadMinus n F b c) (g w) (g (Pi.single (Sum.inl i) 1)) := by
          rw [(hfix i hi).1]
      _ = polar (quadMinus n F b c) w (Pi.single (Sum.inl i) 1) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO w _
      _ = w (Sum.inr (Sum.inl i)) :=
          CFSG.LieType.Universal.Spin.polar_quadMinus_single_inl n F b c w i
      _ = 0 := (hw i hi).2

private noncomputable def minusResidualSub (m ε : ℕ) (F : Type) [Field F] :
    Submodule F (Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F) where
  carrier := {w | ∀ i : Fin (2 * m + ε), i.val < 2 * m →
    w (Sum.inl i) = 0 ∧ w (Sum.inr (Sum.inl i)) = 0}
  zero_mem' := by
    intro i _
    simp
  add_mem' {a b} ha hb := by
    intro i hi
    rw [Pi.add_apply, Pi.add_apply, (ha i hi).1, (hb i hi).1, (ha i hi).2, (hb i hi).2]
    simp
  smul_mem' c a ha := by
    intro i hi
    rw [Pi.smul_apply, Pi.smul_apply, (ha i hi).1, (ha i hi).2]
    simp

private theorem mem_minusResidualSub {m ε : ℕ} {F : Type} [Field F]
    {w : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F} :
    w ∈ minusResidualSub m ε F ↔ ∀ i : Fin (2 * m + ε), i.val < 2 * m →
      w (Sum.inl i) = 0 ∧ w (Sum.inr (Sum.inl i)) = 0 := Iff.rfl

private noncomputable def minusResidualCoord (m ε : ℕ) (F : Type) [Field F] :
    (Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F) →ₗ[F]
      (Fin ε ⊕ Fin ε ⊕ Fin 2 → F) where
  toFun v := fun x =>
    match x with
    | Sum.inl i => v (Sum.inl ⟨2 * m + i.val, by omega⟩)
    | Sum.inr (Sum.inl i) => v (Sum.inr (Sum.inl ⟨2 * m + i.val, by omega⟩))
    | Sum.inr (Sum.inr k) => v (Sum.inr (Sum.inr k))
  map_add' v w := by
    funext x
    rcases x with i | i | k <;> simp
  map_smul' c v := by
    funext x
    rcases x with i | i | k <;> simp

private theorem minusResidualCoord_apply_inl (m ε : ℕ) (F : Type) [Field F]
    (v : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F) (i : Fin ε) :
    minusResidualCoord m ε F v (Sum.inl i) = v (Sum.inl ⟨2 * m + i.val, by omega⟩) := rfl

private theorem minusResidualCoord_apply_inr_inl (m ε : ℕ) (F : Type) [Field F]
    (v : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F) (i : Fin ε) :
    minusResidualCoord m ε F v (Sum.inr (Sum.inl i)) =
      v (Sum.inr (Sum.inl ⟨2 * m + i.val, by omega⟩)) := rfl

private theorem minusResidualCoord_apply_inr_inr (m ε : ℕ) (F : Type) [Field F]
    (v : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F) (k : Fin 2) :
    minusResidualCoord m ε F v (Sum.inr (Sum.inr k)) = v (Sum.inr (Sum.inr k)) := rfl

private noncomputable def minusResidualIncl (m ε : ℕ) (F : Type) [Field F] :
    (Fin ε ⊕ Fin ε ⊕ Fin 2 → F) →ₗ[F] (Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F) where
  toFun t := fun x =>
    match x with
    | Sum.inl i =>
      if h : 2 * m ≤ i.val then t (Sum.inl ⟨i.val - 2 * m, by omega⟩) else 0
    | Sum.inr (Sum.inl i) =>
      if h : 2 * m ≤ i.val then t (Sum.inr (Sum.inl ⟨i.val - 2 * m, by omega⟩)) else 0
    | Sum.inr (Sum.inr k) => t (Sum.inr (Sum.inr k))
  map_add' t s := by
    funext x
    rcases x with i | i | k
    · by_cases h : 2 * m ≤ i.val
      · simp [dif_pos h]
      · simp [dif_neg h]
    · by_cases h : 2 * m ≤ i.val
      · simp [dif_pos h]
      · simp [dif_neg h]
    · simp
  map_smul' c t := by
    funext x
    rcases x with i | i | k
    · by_cases h : 2 * m ≤ i.val
      · simp [dif_pos h]
      · simp [dif_neg h]
    · by_cases h : 2 * m ≤ i.val
      · simp [dif_pos h]
      · simp [dif_neg h]
    · simp

private theorem minusResidualIncl_apply_inl (m ε : ℕ) (F : Type) [Field F]
    (t : Fin ε ⊕ Fin ε ⊕ Fin 2 → F) (i : Fin (2 * m + ε)) :
    minusResidualIncl m ε F t (Sum.inl i) =
      (if h : 2 * m ≤ i.val then t (Sum.inl ⟨i.val - 2 * m, by omega⟩) else 0) := rfl

private theorem minusResidualIncl_apply_inr_inl (m ε : ℕ) (F : Type) [Field F]
    (t : Fin ε ⊕ Fin ε ⊕ Fin 2 → F) (i : Fin (2 * m + ε)) :
    minusResidualIncl m ε F t (Sum.inr (Sum.inl i)) =
      (if h : 2 * m ≤ i.val then t (Sum.inr (Sum.inl ⟨i.val - 2 * m, by omega⟩)) else 0) := rfl

private theorem minusResidualIncl_apply_inr_inr (m ε : ℕ) (F : Type) [Field F]
    (t : Fin ε ⊕ Fin ε ⊕ Fin 2 → F) (k : Fin 2) :
    minusResidualIncl m ε F t (Sum.inr (Sum.inr k)) = t (Sum.inr (Sum.inr k)) := rfl

private theorem minusResidualCoord_comp_incl (m ε : ℕ) (F : Type) [Field F]
    (t : Fin ε ⊕ Fin ε ⊕ Fin 2 → F) :
    minusResidualCoord m ε F (minusResidualIncl m ε F t) = t := by
  funext x
  rcases x with i | i | k
  · rw [minusResidualCoord_apply_inl, minusResidualIncl_apply_inl,
      dif_pos (show 2 * m ≤ 2 * m + i.val by omega)]
    have hfin : (⟨2 * m + i.val - 2 * m, by omega⟩ : Fin ε) = i :=
      Fin.ext (by omega : 2 * m + i.val - 2 * m = i.val)
    rw [hfin]
  · rw [minusResidualCoord_apply_inr_inl, minusResidualIncl_apply_inr_inl,
      dif_pos (show 2 * m ≤ 2 * m + i.val by omega)]
    have hfin : (⟨2 * m + i.val - 2 * m, by omega⟩ : Fin ε) = i :=
      Fin.ext (by omega : 2 * m + i.val - 2 * m = i.val)
    rw [hfin]
  · rw [minusResidualCoord_apply_inr_inr, minusResidualIncl_apply_inr_inr]

private theorem minusResidualIncl_mem (m ε : ℕ) (F : Type) [Field F]
    (t : Fin ε ⊕ Fin ε ⊕ Fin 2 → F) :
    minusResidualIncl m ε F t ∈ minusResidualSub m ε F := by
  intro i hi
  have hne : ¬ 2 * m ≤ i.val := by omega
  exact ⟨by rw [minusResidualIncl_apply_inl, dif_neg hne],
    by rw [minusResidualIncl_apply_inr_inl, dif_neg hne]⟩

private theorem minusResidualIncl_coord_of_mem (m ε : ℕ) (F : Type) [Field F]
    {w : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F}
    (hw : w ∈ minusResidualSub m ε F) :
    minusResidualIncl m ε F (minusResidualCoord m ε F w) = w := by
  funext x
  rcases x with i | i | k
  · by_cases hi : 2 * m ≤ i.val
    · rw [minusResidualIncl_apply_inl, dif_pos hi, minusResidualCoord_apply_inl]
      have hfin : (⟨2 * m + (i.val - 2 * m), by omega⟩ : Fin (2 * m + ε)) = i :=
        Fin.ext (by omega : 2 * m + (i.val - 2 * m) = i.val)
      rw [hfin]
    · have hlt : i.val < 2 * m := by omega
      rw [minusResidualIncl_apply_inl, dif_neg hi]
      exact ((mem_minusResidualSub.mp hw) i hlt).1.symm
  · by_cases hi : 2 * m ≤ i.val
    · rw [minusResidualIncl_apply_inr_inl, dif_pos hi, minusResidualCoord_apply_inr_inl]
      have hfin : (⟨2 * m + (i.val - 2 * m), by omega⟩ : Fin (2 * m + ε)) = i :=
        Fin.ext (by omega : 2 * m + (i.val - 2 * m) = i.val)
      rw [hfin]
    · have hlt : i.val < 2 * m := by omega
      rw [minusResidualIncl_apply_inr_inl, dif_neg hi]
      exact ((mem_minusResidualSub.mp hw) i hlt).2.symm
  · rw [minusResidualIncl_apply_inr_inr, minusResidualCoord_apply_inr_inr]

private noncomputable def minusResidualEquiv (m ε : ℕ) (F : Type) [Field F] :
    minusResidualSub m ε F ≃ₗ[F] (Fin ε ⊕ Fin ε ⊕ Fin 2 → F) where
  toFun w := minusResidualCoord m ε F (w : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F)
  invFun t := ⟨minusResidualIncl m ε F t, minusResidualIncl_mem m ε F t⟩
  left_inv w := Subtype.ext (minusResidualIncl_coord_of_mem m ε F w.2)
  right_inv t := minusResidualCoord_comp_incl m ε F t
  map_add' a b := map_add (minusResidualCoord m ε F)
    (a : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F)
    (b : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F)
  map_smul' c a := map_smul (minusResidualCoord m ε F) c
    (a : Fin (2 * m + ε) ⊕ Fin (2 * m + ε) ⊕ Fin 2 → F)

private noncomputable def minusResidualIsometryOdd (m : ℕ) (F : Type) [Field F] (b c : F) :
    ((quadMinus (2 * m + 1) F b c).comp (minusResidualSub m 0 F).subtype).IsometryEquiv
      (quadMinus 1 F b c) where
  toLinearEquiv := minusResidualEquiv m 0 F
  map_app' w := by
    have hsum : (∑ i : Fin ((2 * m + 1) - 1),
        (w.val : Fin ((2 * m + 1) - 1) ⊕ Fin ((2 * m + 1) - 1) ⊕ Fin 2 → F) (Sum.inl i) *
        (w.val : Fin ((2 * m + 1) - 1) ⊕ Fin ((2 * m + 1) - 1) ⊕ Fin 2 → F)
          (Sum.inr (Sum.inl i))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [((mem_minusResidualSub.mp w.2) i i.isLt).1, zero_mul]
    show quadMinus 1 F b c (minusResidualCoord m 0 F
      (w.val : Fin (2 * m + 0) ⊕ Fin (2 * m + 0) ⊕ Fin 2 → F)) = _
    rw [QuadraticMap.comp_apply, quadMinus_apply, quadMinus_apply, Submodule.subtype_apply, hsum,
      Fin.sum_univ_zero]
    rfl

private noncomputable def minusResidualIsometryEven (m : ℕ) (F : Type) [Field F] (b c : F) :
    ((quadMinus (2 * m + 2) F b c).comp (minusResidualSub m 1 F).subtype).IsometryEquiv
      (quadMinus 2 F b c) where
  toLinearEquiv := minusResidualEquiv m 1 F
  map_app' w := by
    have hsum : (∑ i : Fin ((2 * m + 2) - 1),
        (w.val : Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2 → F) (Sum.inl i) *
        (w.val : Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2 → F)
          (Sum.inr (Sum.inl i))) =
        (w.val : Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2 → F)
            (Sum.inl ⟨2 * m, by omega⟩) *
          (w.val : Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2 → F)
            (Sum.inr (Sum.inl ⟨2 * m, by omega⟩)) := by
      refine Finset.sum_eq_single (⟨2 * m, by omega⟩ : Fin ((2 * m + 2) - 1)) ?_ ?_
      · intro b _ hbne
        have hbv : b.val ≠ 2 * m := fun h => hbne (Fin.ext h)
        have hlt : b.val < 2 * m := by
          have := b.isLt
          omega
        rw [((mem_minusResidualSub.mp w.2) b hlt).1, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    show quadMinus 2 F b c (minusResidualCoord m 1 F
      (w.val : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F)) = _
    rw [QuadraticMap.comp_apply, quadMinus_apply, quadMinus_apply, Submodule.subtype_apply, hsum,
      Fin.sum_univ_one]
    rfl

private theorem card_orthogonalGroup_minusResidualOdd (m : ℕ) (F : Type) [Field F] [Finite F]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus (2 * m + 1) F b c).comp (minusResidualSub m 0 F).subtype)) =
      2 * (Nat.card F + 1) := by
  rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr
    (minusResidualIsometryOdd m F b c)]
  have hq := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := F) hirr 0
  have hq' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 F b c)) : ℤ) =
      2 * ((Nat.card F : ℤ) + 1) := by
    simpa using hq
  exact_mod_cast hq'

private theorem card_orthogonalGroup_minusResidualEven (m : ℕ) (F : Type) [Field F] [Finite F]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus (2 * m + 2) F b c).comp (minusResidualSub m 1 F).subtype)) =
      2 * Nat.card F ^ 2 * (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 - 1) := by
  rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr
    (minusResidualIsometryEven m F b c)]
  have hq := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := F) hirr 1
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hcast : ((2 * Nat.card F ^ 2 * (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 - 1) : ℕ) : ℤ) =
      2 * (Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 2 + 1) * ((Nat.card F : ℤ) ^ 2 - 1) := by
    push_cast
    rw [Nat.cast_sub hq2, Nat.cast_pow]
    ring
  have hq' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 F b c)) : ℤ) =
      2 * (Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 2 + 1) * ((Nat.card F : ℤ) ^ 2 - 1) := by
    simpa using hq
  have hgoal : ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 F b c)) : ℕ) : ℤ) =
      ((2 * Nat.card F ^ 2 * (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 - 1) : ℕ) : ℤ) := by
    rw [hcast]
    exact hq'
  exact_mod_cast hgoal

private theorem eq_one_of_commute_minusPairFramesOdd {F : Type} [Field F] [Finite F]
    {m r a : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1))
    {h : (Fin ((2 * m + 1) - 1) ⊕ Fin ((2 * m + 1) - 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin ((2 * m + 1) - 1) ⊕ Fin ((2 * m + 1) - 1) ⊕ Fin 2 → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (2 * m + 1) F b c))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin (((2 * m + 1) - 1) / 2)) (A : SL(2, F)),
      h * (minusOrthogonalPairFrame F (2 * m + 1) b c j).La A =
        (minusOrthogonalPairFrame F (2 * m + 1) b c j).La A * h)
    (hR : ∀ (j : Fin (((2 * m + 1) - 1) / 2)) (A : SL(2, F)),
      h * (minusOrthogonalPairFrame F (2 * m + 1) b c j).swap.La A =
        (minusOrthogonalPairFrame F (2 * m + 1) b c j).swap.La A * h) :
    h = 1 := by
  have hpair := fixes_pairs_of_commute_minusPairFrames h2 hr hr2 hhO hpow hL hR
  have hfixinv : ∀ i : Fin ((2 * m + 1) - 1), i.val < 2 * (((2 * m + 1) - 1) / 2) →
      h⁻¹ (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h⁻¹ (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · have h1 : h⁻¹ (h (Pi.single (Sum.inl i) 1)) = Pi.single (Sum.inl i) 1 :=
        LinearEquiv.symm_apply_apply h _
      rw [(hpair i hi).1] at h1
      exact h1
    · have h1 : h⁻¹ (h (Pi.single (Sum.inr (Sum.inl i)) 1)) =
          Pi.single (Sum.inr (Sum.inl i)) 1 :=
        LinearEquiv.symm_apply_apply h _
      rw [(hpair i hi).2] at h1
      exact h1
  let W₀ := minusResidualSub m 0 F
  have hsta : h ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub W₀ := by
    intro x
    constructor
    · intro hx
      have hx' : ∀ i : Fin ((2 * m + 1) - 1), i.val < 2 * (((2 * m + 1) - 1) / 2) →
          x (Sum.inl i) = 0 ∧ x (Sum.inr (Sum.inl i)) = 0 := by
        intro i hi
        have hi' : i.val < 2 * m := by
          rwa [show ((2 * m + 1) - 1) / 2 = m by omega] at hi
        exact hx i hi'
      have hx'' := maps_minusResidual_of_forall_fix_basis hhO hpair hx'
      intro i hi
      have hi' : i.val < 2 * (((2 * m + 1) - 1) / 2) := by
        rw [show ((2 * m + 1) - 1) / 2 = m by omega]
        exact hi
      exact hx'' i hi'
    · intro hx
      have hx' : ∀ i : Fin ((2 * m + 1) - 1), i.val < 2 * (((2 * m + 1) - 1) / 2) →
          (h x) (Sum.inl i) = 0 ∧ (h x) (Sum.inr (Sum.inl i)) = 0 := by
        intro i hi
        have hi' : i.val < 2 * m := by
          rwa [show ((2 * m + 1) - 1) / 2 = m by omega] at hi
        exact hx i hi'
      have hx'' := maps_minusResidual_of_forall_fix_basis (Subgroup.inv_mem _ hhO) hfixinv hx'
      have hx3 : ∀ i : Fin ((2 * m + 1) - 1), i.val < 2 * m →
          x (Sum.inl i) = 0 ∧ x (Sum.inr (Sum.inl i)) = 0 := by
        intro i hi
        have hi' : i.val < 2 * (((2 * m + 1) - 1) / 2) := by
          rw [show ((2 * m + 1) - 1) / 2 = m by omega]
          exact hi
        have h1 := hx'' i hi'
        simpa [LinearEquiv.symm_apply_apply] using h1
      intro i hi
      exact hx3 i hi
  let ν : W₀ ≃ₗ[F] W₀ := CFSG.ClassicalGroups.Orthogonal.Small.resHom W₀ ⟨h, hsta⟩
  have hνO : ν ∈ TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus (2 * m + 1) F b c).comp W₀.subtype) :=
    CFSG.ClassicalGroups.Orthogonal.Small.resHom_mem_orthogonalGroup hhO hsta
  have hνpow : ν ^ (r ^ a) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    apply Subtype.ext
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_pow_apply hsta]
    rw [hpow]
    rfl
  have hcard := card_orthogonalGroup_minusResidualOdd m F hirr
  have hnotdvd : ¬ r ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus (2 * m + 1) F b c).comp W₀.subtype)) := by
    rw [hcard]
    intro hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with h2r | hq
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2r)
    · have hq2 : r ∣ Nat.card F ^ 2 - 1 := by
        have h1 : r ∣ (Nat.card F + 1) * (Nat.card F - 1) := dvd_mul_of_dvd_left hq _
        have h2 : (Nat.card F + 1) * (Nat.card F - 1) = Nat.card F ^ 2 - 1 := by
          rw [← Nat.sq_sub_sq]
        rwa [h2] at h1
      exact hrq (dvd_mul_of_dvd_right hq2 _)
  have hcopN : Nat.Coprime (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus (2 * m + 1) F b c).comp W₀.subtype))) (r ^ a) := by
    exact ((Nat.Prime.coprime_iff_not_dvd hr).2 hnotdvd).symm.pow_right a
  let ν₀ : TauCeti.QuadraticMap.orthogonalGroup ((quadMinus (2 * m + 1) F b c).comp W₀.subtype) :=
    ⟨ν, hνO⟩
  have hν₀pow : ν₀ ^ (r ^ a) = 1 := Subtype.ext hνpow
  have hν1 : ν = 1 := by
    have hdvd : orderOf ν₀ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        ((quadMinus (2 * m + 1) F b c).comp W₀.subtype)) := orderOf_dvd_natCard ν₀
    have hcop : Nat.Coprime (orderOf ν₀) (r ^ a) := hcopN.of_dvd_left hdvd
    have h1 : ν₀ = 1 := orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hν₀pow))
    exact Subtype.ext_iff.mp h1
  have hfixW : ∀ w : Fin ((2 * m + 1) - 1) ⊕ Fin ((2 * m + 1) - 1) ⊕ Fin 2 → F,
      w ∈ W₀ → h w = w := by
    intro w hw
    have h1 : ν ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hν1]; rfl
    have h2 := congrArg Subtype.val h1
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply] at h2
    exact h2
  have hfix_all : ∀ x : Fin ((2 * m + 1) - 1) ⊕ Fin ((2 * m + 1) - 1) ⊕ Fin 2,
      h (Pi.single x 1) = Pi.single x 1 := by
    rintro (i | i | k)
    · have hi : i.val < 2 * (((2 * m + 1) - 1) / 2) := by
        rw [show ((2 * m + 1) - 1) / 2 = m by omega]
        exact i.isLt
      exact (hpair i hi).1
    · have hi : i.val < 2 * (((2 * m + 1) - 1) / 2) := by
        rw [show ((2 * m + 1) - 1) / 2 = m by omega]
        exact i.isLt
      exact (hpair i hi).2
    · refine hfixW _ ?_
      intro j hj
      simp
  have hlin : h.toLinearMap = 1 := by
    refine LinearMap.pi_ext fun x c' => ?_
    have hsingle : Pi.single x c' = c' • Pi.single x (1 : F) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    calc h (Pi.single x c') = h (c' • Pi.single x (1 : F)) := by rw [hsingle]
      _ = c' • h (Pi.single x 1) := map_smul h c' _
      _ = c' • Pi.single x 1 := by rw [hfix_all x]
      _ = Pi.single x c' := hsingle.symm
  exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun hlin v

private theorem eq_one_of_commute_minusPairFramesEven {F : Type} [Field F] [Finite F]
    {m r a : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1))
    (hrq' : ¬ r ∣ Nat.card F ^ 2 + 1)
    {h : (Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2 → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (2 * m + 2) F b c))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin (((2 * m + 2) - 1) / 2)) (A : SL(2, F)),
      h * (minusOrthogonalPairFrame F (2 * m + 2) b c j).La A =
        (minusOrthogonalPairFrame F (2 * m + 2) b c j).La A * h)
    (hR : ∀ (j : Fin (((2 * m + 2) - 1) / 2)) (A : SL(2, F)),
      h * (minusOrthogonalPairFrame F (2 * m + 2) b c j).swap.La A =
        (minusOrthogonalPairFrame F (2 * m + 2) b c j).swap.La A * h) :
    h = 1 := by
  have hpair := fixes_pairs_of_commute_minusPairFrames h2 hr hr2 hhO hpow hL hR
  have hfixinv : ∀ i : Fin ((2 * m + 2) - 1), i.val < 2 * (((2 * m + 2) - 1) / 2) →
      h⁻¹ (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h⁻¹ (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · have h1 : h⁻¹ (h (Pi.single (Sum.inl i) 1)) = Pi.single (Sum.inl i) 1 :=
        LinearEquiv.symm_apply_apply h _
      rw [(hpair i hi).1] at h1
      exact h1
    · have h1 : h⁻¹ (h (Pi.single (Sum.inr (Sum.inl i)) 1)) =
          Pi.single (Sum.inr (Sum.inl i)) 1 :=
        LinearEquiv.symm_apply_apply h _
      rw [(hpair i hi).2] at h1
      exact h1
  let W₀ := minusResidualSub m 1 F
  have hsta : h ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub W₀ := by
    intro x
    constructor
    · intro hx
      have hx' : ∀ i : Fin ((2 * m + 2) - 1), i.val < 2 * (((2 * m + 2) - 1) / 2) →
          x (Sum.inl i) = 0 ∧ x (Sum.inr (Sum.inl i)) = 0 := by
        intro i hi
        have hi' : i.val < 2 * m := by
          rwa [show ((2 * m + 2) - 1) / 2 = m by omega] at hi
        exact hx i hi'
      have hx'' := maps_minusResidual_of_forall_fix_basis hhO hpair hx'
      intro i hi
      have hi' : i.val < 2 * (((2 * m + 2) - 1) / 2) := by
        rw [show ((2 * m + 2) - 1) / 2 = m by omega]
        exact hi
      exact hx'' i hi'
    · intro hx
      have hx' : ∀ i : Fin ((2 * m + 2) - 1), i.val < 2 * (((2 * m + 2) - 1) / 2) →
          (h x) (Sum.inl i) = 0 ∧ (h x) (Sum.inr (Sum.inl i)) = 0 := by
        intro i hi
        have hi' : i.val < 2 * m := by
          rwa [show ((2 * m + 2) - 1) / 2 = m by omega] at hi
        exact hx i hi'
      have hx'' := maps_minusResidual_of_forall_fix_basis (Subgroup.inv_mem _ hhO) hfixinv hx'
      have hx3 : ∀ i : Fin ((2 * m + 2) - 1), i.val < 2 * m →
          x (Sum.inl i) = 0 ∧ x (Sum.inr (Sum.inl i)) = 0 := by
        intro i hi
        have hi' : i.val < 2 * (((2 * m + 2) - 1) / 2) := by
          rw [show ((2 * m + 2) - 1) / 2 = m by omega]
          exact hi
        have h1 := hx'' i hi'
        simpa [LinearEquiv.symm_apply_apply] using h1
      intro i hi
      exact hx3 i hi
  let ν : W₀ ≃ₗ[F] W₀ := CFSG.ClassicalGroups.Orthogonal.Small.resHom W₀ ⟨h, hsta⟩
  have hνO : ν ∈ TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus (2 * m + 2) F b c).comp W₀.subtype) :=
    CFSG.ClassicalGroups.Orthogonal.Small.resHom_mem_orthogonalGroup hhO hsta
  have hνpow : ν ^ (r ^ a) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    apply Subtype.ext
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_pow_apply hsta]
    rw [hpow]
    rfl
  have hcard := card_orthogonalGroup_minusResidualEven m F hirr
  have hnotdvd : ¬ r ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus (2 * m + 2) F b c).comp W₀.subtype)) := by
    rw [hcard]
    intro hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with hA | hB
    · rcases (Nat.Prime.dvd_mul hr).1 hA with h2q | hqp
      · rcases (Nat.Prime.dvd_mul hr).1 h2q with h2r | hq2
        · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2r)
        · have hq' : r ∣ Nat.card F := Nat.Prime.dvd_of_dvd_pow hr hq2
          exact hrq (dvd_mul_of_dvd_left hq' _)
      · exact hrq' hqp
    · exact hrq (dvd_mul_of_dvd_right hB _)
  have hcopN : Nat.Coprime (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus (2 * m + 2) F b c).comp W₀.subtype))) (r ^ a) := by
    exact ((Nat.Prime.coprime_iff_not_dvd hr).2 hnotdvd).symm.pow_right a
  let ν₀ : TauCeti.QuadraticMap.orthogonalGroup ((quadMinus (2 * m + 2) F b c).comp W₀.subtype) :=
    ⟨ν, hνO⟩
  have hν₀pow : ν₀ ^ (r ^ a) = 1 := Subtype.ext hνpow
  have hν1 : ν = 1 := by
    have hdvd : orderOf ν₀ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        ((quadMinus (2 * m + 2) F b c).comp W₀.subtype)) := orderOf_dvd_natCard ν₀
    have hcop : Nat.Coprime (orderOf ν₀) (r ^ a) := hcopN.of_dvd_left hdvd
    have h1 : ν₀ = 1 := orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hν₀pow))
    exact Subtype.ext_iff.mp h1
  have hfixW : ∀ w : Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2 → F,
      w ∈ W₀ → h w = w := by
    intro w hw
    have h1 : ν ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hν1]; rfl
    have h2 := congrArg Subtype.val h1
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply] at h2
    exact h2
  have hfix_all : ∀ x : Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2,
      h (Pi.single x 1) = Pi.single x 1 := by
    rintro (i | i | k)
    · by_cases hi : i.val < 2 * (((2 * m + 2) - 1) / 2)
      · exact (hpair i hi).1
      · have hge : i.val = 2 * m := by
          have h2m : ((2 * m + 2) - 1) / 2 = m := by omega
          have := i.isLt
          omega
        have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hge
        rw [hi']
        refine hfixW _ ?_
        intro j hj
        have hne : (Sum.inl j : Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕ Fin 2) ≠
            Sum.inl ⟨2 * m, by omega⟩ := by
          simp [Fin.ext_iff]
          omega
        simp [hne]
    · by_cases hi : i.val < 2 * (((2 * m + 2) - 1) / 2)
      · exact (hpair i hi).2
      · have hge : i.val = 2 * m := by
          have h2m : ((2 * m + 2) - 1) / 2 = m := by omega
          have := i.isLt
          omega
        have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hge
        rw [hi']
        refine hfixW _ ?_
        intro j hj
        have hne : (Sum.inr (Sum.inl j) : Fin ((2 * m + 2) - 1) ⊕ Fin ((2 * m + 2) - 1) ⊕
            Fin 2) ≠ Sum.inr (Sum.inl ⟨2 * m, by omega⟩) := by
          simp [Fin.ext_iff]
          omega
        simp [hne]
    · refine hfixW _ ?_
      intro j hj
      simp
  have hlin : h.toLinearMap = 1 := by
    refine LinearMap.pi_ext fun x c' => ?_
    have hsingle : Pi.single x c' = c' • Pi.single x (1 : F) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    calc h (Pi.single x c') = h (c' • Pi.single x (1 : F)) := by rw [hsingle]
      _ = c' • h (Pi.single x 1) := map_smul h c' _
      _ = c' • Pi.single x 1 := by rw [hfix_all x]
      _ = Pi.single x c' := hsingle.symm
  exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun hlin v

private theorem eq_one_of_commute_minusPairFrames {F : Type} [Field F] [Finite F] {n r a : ℕ}
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) (h2 : (2 : F) ≠ 0)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1))
    (hrq' : Even n → ¬ r ∣ Nat.card F ^ 2 + 1)
    {h : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃ₗ[F] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin ((n - 1) / 2)) (A : SL(2, F)),
      h * (minusOrthogonalPairFrame F n b c j).La A =
        (minusOrthogonalPairFrame F n b c j).La A * h)
    (hR : ∀ (j : Fin ((n - 1) / 2)) (A : SL(2, F)),
      h * (minusOrthogonalPairFrame F n b c j).swap.La A =
        (minusOrthogonalPairFrame F n b c j).swap.La A * h) :
    h = 1 := by
  rcases Nat.even_or_odd' (n - 2) with ⟨m, hm | hm⟩
  · have hn' : n = 2 * m + 2 := by omega
    subst hn'
    exact eq_one_of_commute_minusPairFramesEven (m := m) hirr h2 hr hr2 hrq
      (hrq' ⟨m + 1, by omega⟩) hhO hpow hL hR
  · have hn' : n = 2 * (m + 1) + 1 := by omega
    subst hn'
    exact eq_one_of_commute_minusPairFramesOdd (m := m + 1) hirr h2 hr hr2 hrq hhO hpow hL hR

end EvenOrthLinear

section EvenOrthBad

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
open CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open scoped MatrixGroups Pointwise

private noncomputable def minusFrameSub (m : ℕ) (F : Type) [Field F] :
    Submodule F (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F) where
  carrier := {u | (∀ i : Fin (2 * m + 1), 2 * m ≤ i.val →
    u (Sum.inl i) = 0 ∧ u (Sum.inr (Sum.inl i)) = 0) ∧ ∀ k : Fin 2, u (Sum.inr (Sum.inr k)) = 0}
  zero_mem' := ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
  add_mem' {a b} ha hb := by
    refine ⟨fun i hi => ?_, fun k => ?_⟩
    · rw [Pi.add_apply, Pi.add_apply, (ha.1 i hi).1, (hb.1 i hi).1, (ha.1 i hi).2,
        (hb.1 i hi).2]
      simp
    · rw [Pi.add_apply, ha.2 k, hb.2 k, add_zero]
  smul_mem' c a ha := by
    refine ⟨fun i hi => ?_, fun k => ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, (ha.1 i hi).1, (ha.1 i hi).2]
      simp
    · rw [Pi.smul_apply, ha.2 k, smul_zero]

private noncomputable def minusFrameFactor (m : ℕ) (F : Type) [Field F] (b c : F)
    (k : Fin ((2 * m + 2 - 1) / 2) × Bool) :
    Subgroup ((Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F)) :=
  if k.2 then (minusOrthogonalPairFrame F (2 * m + 2) b c k.1).swap.La.range
  else (minusOrthogonalPairFrame F (2 * m + 2) b c k.1).La.range

private theorem isCompl_minusResidualSub_minusFrameSub (m : ℕ) (F : Type) [Field F] :
    IsCompl (minusResidualSub m 1 F) (minusFrameSub m F) := by
  refine isCompl_iff.mpr ⟨?_, ?_⟩
  · rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    intro v hv
    rw [Submodule.mem_inf] at hv
    rw [Submodule.mem_bot]
    funext x
    rcases x with i | i | k
    · by_cases hi : i.val < 2 * m
      · exact (mem_minusResidualSub.mp hv.1 i hi).1
      · exact (hv.2.1 i (by omega)).1
    · by_cases hi : i.val < 2 * m
      · exact (mem_minusResidualSub.mp hv.1 i hi).2
      · exact (hv.2.1 i (by omega)).2
    · exact hv.2.2 k
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro v
    rw [Submodule.mem_sup]
    let w : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F := fun x =>
      match x with
      | Sum.inl i => if 2 * m ≤ i.val then v (Sum.inl i) else 0
      | Sum.inr (Sum.inl i) => if 2 * m ≤ i.val then v (Sum.inr (Sum.inl i)) else 0
      | Sum.inr (Sum.inr k) => v (Sum.inr (Sum.inr k))
    refine ⟨w, ?_, v - w, ?_, add_sub_cancel w v⟩
    · intro i hi
      have hgt : ¬ 2 * m ≤ i.val := by omega
      exact ⟨by simp [w, if_neg hgt], by simp [w, if_neg hgt]⟩
    · refine ⟨fun i hi => ?_, fun k => ?_⟩
      · have hle : 2 * m ≤ i.val := hi
        simp [Pi.sub_apply, w, if_pos hle]
      · simp [Pi.sub_apply, w]

private theorem polar_minusResidualSub_minusFrameSub (m : ℕ) {F : Type} [Field F] (b c : F) :
    ∀ w ∈ minusResidualSub m 1 F, ∀ u ∈ minusFrameSub m F,
      polar (quadMinus (2 * m + 2) F b c) w u = 0 := by
  intro w hw u hu
  rw [polar_quadMinus]
  have hsum : (∑ i : Fin (2 * m + 2 - 1),
      (w (Sum.inl i) * u (Sum.inr (Sum.inl i)) +
        u (Sum.inl i) * w (Sum.inr (Sum.inl i)))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i.val < 2 * m
    · rw [(mem_minusResidualSub.mp hw i hi).1, (mem_minusResidualSub.mp hw i hi).2]
      ring
    · have hge : 2 * m ≤ i.val := by omega
      rw [(hu.1 i hge).1, (hu.1 i hge).2]
      ring
  have h0 : u (Sum.inr (Sum.inr 0)) = 0 := hu.2 0
  have h1 : u (Sum.inr (Sum.inr 1)) = 0 := hu.2 1
  rw [hsum, h0, h1]
  ring

private theorem badFrame_coords_eq_zero {m : ℕ} {F : Type} [Field F] (b c : F)
    (k : Fin ((2 * m + 2 - 1) / 2)) {v : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F}
    (hv : ∀ i : Fin (2 * m + 1), i.val < 2 * m →
      v (Sum.inl i) = 0 ∧ v (Sum.inr (Sum.inl i)) = 0) :
    (minusOrthogonalPairFrame F (2 * m + 2) b c k).coords v = 0 := by
  have hv' : ∀ i : Fin (2 * m + 2 - 1), i.val < 2 * m →
      v (Sum.inl i) = 0 ∧ v (Sum.inr (Sum.inl i)) = 0 := fun i hi => hv i hi
  have h1 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).f₁ =
      Pi.single (Sum.inr (Sum.inl ⟨2 * k.val, by omega⟩)) (1 : F) := rfl
  have h2 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).f₂ =
      Pi.single (Sum.inl ⟨2 * k.val + 1, by omega⟩) (1 : F) := rfl
  have h3 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).e₂ =
      Pi.single (Sum.inr (Sum.inl ⟨2 * k.val + 1, by omega⟩)) (1 : F) := rfl
  have h4 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).e₁ =
      Pi.single (Sum.inl ⟨2 * k.val, by omega⟩) (1 : F) := rfl
  have h2k : 2 * k.val < 2 * m := by omega
  have h2k1 : 2 * k.val + 1 < 2 * m := by omega
  rw [Frame.coords_apply, h1, h2, h3, h4]
  ext a b2
  fin_cases a <;> fin_cases b2
  · rw [polar_quadMinus_single_inr_inl (2 * m + 2) F b c v ⟨2 * k.val, by omega⟩]
    exact (hv' ⟨2 * k.val, by omega⟩ h2k).1
  · rw [polar_quadMinus_single_inl (2 * m + 2) F b c v ⟨2 * k.val + 1, by omega⟩]
    exact neg_eq_zero.mpr (hv' ⟨2 * k.val + 1, by omega⟩ h2k1).2
  · rw [polar_quadMinus_single_inr_inl (2 * m + 2) F b c v ⟨2 * k.val + 1, by omega⟩]
    exact (hv' ⟨2 * k.val + 1, by omega⟩ h2k1).1
  · rw [polar_quadMinus_single_inl (2 * m + 2) F b c v ⟨2 * k.val, by omega⟩]
    exact (hv' ⟨2 * k.val, by omega⟩ h2k).2

private theorem badFrame_coords_swap_eq_zero {m : ℕ} {F : Type} [Field F] (b c : F)
    (k : Fin ((2 * m + 2 - 1) / 2)) {v : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F}
    (hv : ∀ i : Fin (2 * m + 1), i.val < 2 * m →
      v (Sum.inl i) = 0 ∧ v (Sum.inr (Sum.inl i)) = 0) :
    (minusOrthogonalPairFrame F (2 * m + 2) b c k).swap.coords v = 0 := by
  have hv' : ∀ i : Fin (2 * m + 2 - 1), i.val < 2 * m →
      v (Sum.inl i) = 0 ∧ v (Sum.inr (Sum.inl i)) = 0 := fun i hi => hv i hi
  have h1 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).swap.f₁ =
      Pi.single (Sum.inr (Sum.inl ⟨2 * k.val, by omega⟩)) (1 : F) := rfl
  have h2 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).swap.f₂ =
      Pi.single (Sum.inr (Sum.inl ⟨2 * k.val + 1, by omega⟩)) (1 : F) := rfl
  have h3 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).swap.e₂ =
      Pi.single (Sum.inl ⟨2 * k.val + 1, by omega⟩) (1 : F) := rfl
  have h4 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).swap.e₁ =
      Pi.single (Sum.inl ⟨2 * k.val, by omega⟩) (1 : F) := rfl
  have h2k : 2 * k.val < 2 * m := by omega
  have h2k1 : 2 * k.val + 1 < 2 * m := by omega
  rw [Frame.coords_apply, h1, h2, h3, h4]
  ext a b2
  fin_cases a <;> fin_cases b2
  · rw [polar_quadMinus_single_inr_inl (2 * m + 2) F b c v ⟨2 * k.val, by omega⟩]
    exact (hv' ⟨2 * k.val, by omega⟩ h2k).1
  · rw [polar_quadMinus_single_inr_inl (2 * m + 2) F b c v ⟨2 * k.val + 1, by omega⟩]
    exact neg_eq_zero.mpr (hv' ⟨2 * k.val + 1, by omega⟩ h2k1).1
  · rw [polar_quadMinus_single_inl (2 * m + 2) F b c v ⟨2 * k.val + 1, by omega⟩]
    exact (hv' ⟨2 * k.val + 1, by omega⟩ h2k1).2
  · rw [polar_quadMinus_single_inl (2 * m + 2) F b c v ⟨2 * k.val, by omega⟩]
    exact (hv' ⟨2 * k.val, by omega⟩ h2k).2

private theorem badFrame_coords_eq_zero_apply {m : ℕ} {F : Type} [Field F] (b c : F)
    (k : Fin ((2 * m + 2 - 1) / 2)) {v : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F}
    (h : (minusOrthogonalPairFrame F (2 * m + 2) b c k).coords v = 0) :
    v (Sum.inl ⟨2 * k.val, by omega⟩) = 0 ∧
      v (Sum.inr (Sum.inl ⟨2 * k.val, by omega⟩)) = 0 ∧
      v (Sum.inl ⟨2 * k.val + 1, by omega⟩) = 0 ∧
      v (Sum.inr (Sum.inl ⟨2 * k.val + 1, by omega⟩)) = 0 := by
  have h1 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).f₁ =
      Pi.single (Sum.inr (Sum.inl ⟨2 * k.val, by omega⟩)) (1 : F) := rfl
  have h2 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).f₂ =
      Pi.single (Sum.inl ⟨2 * k.val + 1, by omega⟩) (1 : F) := rfl
  have h3 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).e₂ =
      Pi.single (Sum.inr (Sum.inl ⟨2 * k.val + 1, by omega⟩)) (1 : F) := rfl
  have h4 : (minusOrthogonalPairFrame F (2 * m + 2) b c k).e₁ =
      Pi.single (Sum.inl ⟨2 * k.val, by omega⟩) (1 : F) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := congrFun (congrFun h 0) 0
    rw [Frame.coords_apply, h1,
      polar_quadMinus_single_inr_inl (2 * m + 2) F b c v ⟨2 * k.val, by omega⟩] at hh
    simpa using hh
  · have hh := congrFun (congrFun h 1) 1
    rw [Frame.coords_apply, h4,
      polar_quadMinus_single_inl (2 * m + 2) F b c v ⟨2 * k.val, by omega⟩] at hh
    simpa using hh
  · have hh := congrFun (congrFun h 1) 0
    rw [Frame.coords_apply, h3,
      polar_quadMinus_single_inr_inl (2 * m + 2) F b c v ⟨2 * k.val + 1, by omega⟩] at hh
    simpa using hh
  · have hh := congrFun (congrFun h 0) 1
    rw [Frame.coords_apply, h2,
      polar_quadMinus_single_inl (2 * m + 2) F b c v ⟨2 * k.val + 1, by omega⟩] at hh
    simpa using hh

private theorem mem_minusResidualSub_iff_forall_frameFactor (m : ℕ) {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) (b c : F) (v : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F) :
    v ∈ minusResidualSub m 1 F ↔ ∀ k, ∀ ℓ ∈ minusFrameFactor m F b c k, ℓ v = v := by
  constructor
  · intro hv k ℓ hℓ
    obtain ⟨j, s⟩ := k
    cases s
    · have hcoord := badFrame_coords_eq_zero b c j hv
      obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hℓ
      rw [← hA]
      exact Frame.La_apply_of_coords_eq_zero _ A hcoord
    · have hcoord := badFrame_coords_swap_eq_zero b c j hv
      obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hℓ
      rw [← hA]
      exact Frame.La_apply_of_coords_eq_zero _ A hcoord
  · intro hfix
    rw [mem_minusResidualSub]
    intro i hi
    have hjlt : i.val / 2 < (2 * m + 2 - 1) / 2 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      omega
    let j : Fin ((2 * m + 2 - 1) / 2) := ⟨i.val / 2, hjlt⟩
    let fr := minusOrthogonalPairFrame F (2 * m + 2) b c j
    have hmem : fr.La (-1) ∈ minusFrameFactor m F b c (j, false) := ⟨-1, rfl⟩
    have hfixj : fr.La (-1) v = v := hfix (j, false) (fr.La (-1)) hmem
    have hzero : fr.incl (fr.coords v) = 0 := by
      have hh := hfixj
      rw [Frame.La_neg_one_apply] at hh
      have h2s : (2 : F) • fr.incl (fr.coords v) = 0 := sub_eq_self.mp hh
      exact (smul_eq_zero.mp h2s).resolve_left h2
    have hc : fr.coords v = 0 := by
      have hh := congrArg fr.coords hzero
      simpa [Frame.coords_incl] using hh
    have hcoord := badFrame_coords_eq_zero_apply b c j hc
    have hmod := Nat.mod_two_eq_zero_or_one i.val
    have hdm : 2 * (i.val / 2) + i.val % 2 = i.val := Nat.div_add_mod i.val 2
    rcases hmod with h0 | h1
    · have hi' : i = ⟨2 * j.val, by omega⟩ := Fin.ext (by simp [j]; omega)
      rw [hi']
      exact ⟨hcoord.1, hcoord.2.1⟩
    · have hi' : i = ⟨2 * j.val + 1, by omega⟩ := Fin.ext (by simp [j]; omega)
      rw [hi']
      exact ⟨hcoord.2.2.1, hcoord.2.2.2⟩

private theorem mem_stabSub_minusResidualSub_of_map_conj (m : ℕ) {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) (b c : F)
    {g : (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F)}
    (hg : ∀ k, ∃ k', (minusFrameFactor m F b c k).map (MulAut.conj g).toMonoidHom =
      minusFrameFactor m F b c k')
    (hg' : ∀ k, ∃ k', (minusFrameFactor m F b c k).map (MulAut.conj g⁻¹).toMonoidHom =
      minusFrameFactor m F b c k') :
    g ∈ stabSub (minusResidualSub m 1 F) := by
  rw [mem_stabSub]
  intro x
  constructor
  · intro hx
    have hiff := (mem_minusResidualSub_iff_forall_frameFactor m h2 b c x).mp hx
    rw [mem_minusResidualSub_iff_forall_frameFactor m h2 b c (g x)]
    intro k ℓ hℓ
    obtain ⟨k', hk'⟩ := hg' k
    have hmem : MulAut.conj g⁻¹ ℓ ∈ minusFrameFactor m F b c k' := by
      rw [← hk']
      exact Subgroup.mem_map_of_mem _ hℓ
    have hx' : (MulAut.conj g⁻¹ ℓ) x = x := hiff k' _ hmem
    simp only [MulAut.conj_apply, inv_inv] at hx'
    calc ℓ (g x) = g ((g⁻¹ * ℓ * g) x) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
          simp
      _ = g x := by rw [hx']
  · intro hx
    have hiff := (mem_minusResidualSub_iff_forall_frameFactor m h2 b c (g x)).mp hx
    rw [mem_minusResidualSub_iff_forall_frameFactor m h2 b c x]
    intro k ℓ hℓ
    obtain ⟨k', hk'⟩ := hg k
    have hmem : MulAut.conj g ℓ ∈ minusFrameFactor m F b c k' := by
      rw [← hk']
      exact Subgroup.mem_map_of_mem _ hℓ
    have hx' : (MulAut.conj g ℓ) (g x) = g x := hiff k' _ hmem
    simp only [MulAut.conj_apply] at hx'
    calc ℓ x = g⁻¹ ((g * ℓ * g⁻¹) (g x)) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
          simp
      _ = g⁻¹ (g x) := by rw [hx']
      _ = x := by simp

private theorem mem_stabSub_and_fix_of_forall_fix_basis (m : ℕ) {F : Type} [Field F] {b c : F}
    {g : (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2 → F)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (2 * m + 2) F b c))
    (hfix : ∀ i : Fin (2 * m + 2 - 1), i.val < 2 * ((2 * m + 2 - 1) / 2) →
      g (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      g (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1) :
    g ∈ stabSub (minusResidualSub m 1 F) ∧ ∀ u ∈ minusFrameSub m F, g u = u := by
  have hfix_inv : ∀ i : Fin (2 * m + 2 - 1), i.val < 2 * ((2 * m + 2 - 1) / 2) →
      g⁻¹ (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      g⁻¹ (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hfix i hi
    constructor
    · have h := congrArg g.symm h1
      rw [LinearEquiv.symm_apply_apply] at h
      exact h.symm
    · have h := congrArg g.symm h2
      rw [LinearEquiv.symm_apply_apply] at h
      exact h.symm
  constructor
  · rw [mem_stabSub]
    intro x
    constructor
    · intro hx
      rw [mem_minusResidualSub] at hx ⊢
      intro i hi
      exact maps_minusResidual_of_forall_fix_basis (n := 2 * m + 2) (w := x) hgO hfix
        (fun j hj => hx j (by omega)) i (by omega)
    · intro hx
      rw [mem_minusResidualSub] at hx ⊢
      intro i hi
      have hmap := maps_minusResidual_of_forall_fix_basis (n := 2 * m + 2)
        (inv_mem hgO) hfix_inv (w := g x) (fun j hj => hx j (by omega))
      have := hmap i (by omega)
      simpa using this
  · intro u hu
    have hsum : u = ∑ x : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2,
        Pi.single x (u x) := (Finset.univ_sum_single u).symm
    calc g u = g (∑ x : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2,
          Pi.single x (u x)) := congrArg g hsum
      _ = ∑ x : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2,
          g (Pi.single x (u x)) := by simp only [map_sum]
      _ = ∑ x : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Fin 2,
          Pi.single x (u x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rcases x with i | i | k
        · by_cases hi : i.val < 2 * m
          · have hfixi := (hfix i (by omega)).1
            calc g (Pi.single (Sum.inl i) (u (Sum.inl i)))
                = g ((u (Sum.inl i)) • Pi.single (Sum.inl i) (1 : F)) := by
                  rw [← Pi.single_smul, smul_eq_mul, mul_one]
              _ = (u (Sum.inl i)) • g (Pi.single (Sum.inl i) (1 : F)) := by rw [map_smul]
              _ = (u (Sum.inl i)) • Pi.single (Sum.inl i) (1 : F) := by rw [hfixi]
              _ = Pi.single (Sum.inl i) (u (Sum.inl i)) := by
                  rw [← Pi.single_smul, smul_eq_mul, mul_one]
          · have hu0 := (hu.1 i (by omega)).1
            rw [hu0]
            simp
        · by_cases hi : i.val < 2 * m
          · have hfixi := (hfix i (by omega)).2
            calc g (Pi.single (Sum.inr (Sum.inl i)) (u (Sum.inr (Sum.inl i))))
                = g ((u (Sum.inr (Sum.inl i))) •
                    Pi.single (Sum.inr (Sum.inl i)) (1 : F)) := by
                  rw [← Pi.single_smul, smul_eq_mul, mul_one]
              _ = (u (Sum.inr (Sum.inl i))) •
                  g (Pi.single (Sum.inr (Sum.inl i)) (1 : F)) := by rw [map_smul]
              _ = (u (Sum.inr (Sum.inl i))) •
                  Pi.single (Sum.inr (Sum.inl i)) (1 : F) := by rw [hfixi]
              _ = Pi.single (Sum.inr (Sum.inl i)) (u (Sum.inr (Sum.inl i))) := by
                  rw [← Pi.single_smul, smul_eq_mul, mul_one]
          · have hu0 := (hu.1 i (by omega)).2
            rw [hu0]
            simp
        · have hu0 := hu.2 k
          rw [hu0]
          simp
      _ = u := hsum.symm

private theorem finrank_minusResidualSub (m : ℕ) (F : Type) [Field F] :
    Module.finrank F (minusResidualSub m 1 F) = 4 := by
  calc Module.finrank F (minusResidualSub m 1 F)
      = Module.finrank F (Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F) :=
        (minusResidualEquiv m 1 F).finrank_eq
    _ = 4 := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum]
        norm_num

private theorem not_exists_singular_plane_minusResidualSub (m : ℕ) {F : Type} [Field F]
    [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ¬ ∃ S : Submodule F (minusResidualSub m 1 F), Module.finrank F S = 2 ∧
      ∀ x ∈ S, (quadMinus (2 * m + 2) F b c).comp (minusResidualSub m 1 F).subtype x = 0 := by
  rintro ⟨S, hSrank, hS⟩
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      ((quadMinus (2 * m + 2) F b c).comp (minusResidualSub m 1 F).subtype) := by
    refine ⟨S, ?_, hS⟩
    rw [hSrank, finrank_minusResidualSub m F]
  have hplus' : CFSG.GroupTheory.WeirSylow.IsPlusType (quadMinus 2 F b c) :=
    CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv
      (minusResidualIsometryEven m F b c) hplus
  exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 2) (by norm_num) hirr hplus'

private theorem neg_not_mem_elementaryGroup_quadMinus_of_even {F : Type} [Field F] [Finite F]
    {b c : F} (h2 : (2 : F) ≠ 0) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 4 ≤ n)
    (he : Even n) :
    (LinearEquiv.neg F : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃ₗ[F]
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)) ∉ elementaryGroup (quadMinus n F b c) := by
  rw [CFSG.ClassicalInvolution.neg_mem_elementaryGroup_quadMinus_iff h2 hirr hn]
  rintro ⟨d, hd⟩
  have hodd : Odd (n - 1) := by
    obtain ⟨k, hk⟩ := he
    exact ⟨k - 1, by omega⟩
  rw [hodd.neg_one_pow] at hd
  apply hirr ((d - b) / 2)
  field_simp
  linear_combination (-1 : F) * hd

private theorem spinAction_center_eq_one_of_even {F : Type} [Field F] [Finite F] {b c : F}
    (h2 : (2 : F) ≠ 0) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 4 ≤ n)
    (he : Even n) {z : spinGroup (quadMinus n F b c)}
    (hz : z ∈ Subgroup.center (spinGroup (quadMinus n F b c))) :
    spinAction (quadMinus n F b c) z = 1 := by
  have hS := CFSG.ClassicalInvolution.RouteD.Exotic.spinAction_center_mem_scalars_minus hn hirr hz
  have hO : spinAction (quadMinus n F b c) z ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ z)
  have hv : ∃ v, quadMinus n F b c v ≠ 0 :=
    ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, by simp [quadMinus_apply]⟩
  rcases CFSG.ClassicalInvolution.eq_one_or_eq_neg_of_mem_scalars hS hO hv with h | h
  · exact h
  · have hE : spinAction (quadMinus n F b c) z ∈ elementaryGroup (quadMinus n F b c) := by
      rw [← range_spinAction_quadMinus hn hirr]
      exact ⟨z, rfl⟩
    rw [h] at hE
    exact absurd hE (neg_not_mem_elementaryGroup_quadMinus_of_even h2 hirr hn he)

private theorem exists_injective_comp_eq_of_ker_eq {K X Y : Type} [Group K] [Group X] [Group Y]
    {ψ : K →* X} (hψ : Function.Surjective ψ) {θ : K →* Y} (h1 : ψ.ker ≤ θ.ker)
    (h2 : θ.ker ≤ ψ.ker) : ∃ φ : X →* Y, Function.Injective φ ∧ ∀ g, φ (ψ g) = θ g := by
  let φ := ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ)
    ⟨θ, h1⟩
  have hφ : ∀ g, φ (ψ g) = θ g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨θ, h1⟩ g
  refine ⟨φ, (injective_iff_map_eq_one φ).mpr fun y hy => ?_, hφ⟩
  obtain ⟨g, rfl⟩ := hψ y
  rw [hφ] at hy
  exact h2 hy

end EvenOrthBad


section EvenOrthProof

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.ModelFacts
  (nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups)
open CFSG.ClassicalInvolution.RouteD
open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
open scoped MatrixGroups

private theorem exists_full_paired_frame_funSet_pOmegaPlus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn3 : 3 ≤ n)
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hX : LieModel X .POmegaPlus n p e)
    (η : (modelUniv .POmegaPlus n p e hp.out).K ≃* spinGroup (quadPlus n (GaloisField p e)))
    (hη : ∀ R : Subgroup (modelUniv .POmegaPlus n p e hp.out).K,
      R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D ↔
        R.map η.toMonoidHom ∈
          fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p e) hn3))
    (ψ : (modelUniv .POmegaPlus n p e hp.out).K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (modelUniv .POmegaPlus n p e hp.out).K) (P : Sylow 2 X) :
    ∃ (R : Fin (n / 2) × Bool → Subgroup (modelUniv .POmegaPlus n p e hp.out).K) (c : X),
      (∀ k, R k ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D ∧
        (R k).map ((spinAction (quadPlus n (GaloisField p e))).comp η.toMonoidHom) =
          if k.2 then (plusOrthogonalPairFrame (GaloisField p e) n hn3 k.1).swap.La.range
          else (plusOrthogonalPairFrame (GaloisField p e) n hn3 k.1).La.range) ∧
      FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k => (R k).map ((MulAut.conj c).toMonoidHom.comp ψ)) := by
  classical
  let F := GaloisField p e
  let Q := quadPlus n F
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd : Odd (Nat.card F) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  let π := (spinAction Q).comp η.toMonoidHom
  have hπker : π.ker ≤ center (modelUniv .POmegaPlus n p e hp.out).K := by
    intro x hx
    have hy : η x ∈ center (spinGroup Q) :=
      ker_spinAction_le_center Q (by simpa only [MonoidHom.mem_ker, π, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom] using hx)
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro y
    apply η.injective
    simpa only [map_mul] using hy (η y)
  have hsc : FundamentalSingleClass .POmegaPlus (plusDatum n F hn3) := by
    have hm := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus n p e
      hp.out trivial hadm (by decide) (by decide)
    have he := CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (p := p) (f := e) hn3
    change FundamentalSingleClass .POmegaPlus
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e hp.out).D at hm
    rw [he] at hm
    exact hm
  have hπmap : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D,
      ∃ H : Frame Q, R.map π = H.La.range := by
    intro R hR
    obtain ⟨i, H, hH, _⟩ := Gaps.map_mem_fundSet hn3 hsc ((hη R).mp hR)
    exact ⟨H, by simpa only [π, Subgroup.map_map] using hH⟩
  let A := plusOrthogonalPairFrame F n hn3
  have hex : ∀ k : Fin (n / 2) × Bool,
      ∃ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D,
        R.map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range := by
    intro k
    have hg : (if k.2 then (A k.1).swap.La.range else (A k.1).La.range) ∈ Gaps.fundSet Q := by
      cases k.2
      · exact ⟨_, IsFundamental.of_frame _⟩
      · exact ⟨_, IsFundamental.of_frame_swap _⟩
    obtain ⟨S, hS, hmap⟩ := Gaps.exists_map_eq hn3 hodd hg
    let R := S.map η.symm.toMonoidHom
    have hRmap : R.map η.toMonoidHom = S := by
      simp [R, Subgroup.map_map]
    refine ⟨R, (hη R).mpr (hRmap.symm ▸ hS), ?_⟩
    change R.map ((spinAction Q).comp η.toMonoidHom) = _
    rw [← Subgroup.map_map, hRmap]
    exact hmap
  choose R hR hmap using hex
  obtain ⟨c, hc⟩ := exists_full_paired_model_frame_funSet hp2 (by trivial) hadm hX
    (by simp) (by omega : 0 < n / 2) π hπker hπmap A
    (fun i j hij => spanOrth_plusOrthogonalPairFrame F n hn3 hij)
    (fun H h => not_spanOrth_all_plusOrthogonalPairFrame F n hn3 H h)
    R (fun k => ⟨hR k, hmap k⟩) h2 ψ hψ hker P
  exact ⟨R, c, fun k => ⟨hR k, hmap k⟩, hc⟩

private theorem exists_full_paired_frame_funSet_pOmegaMinus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) (hX : LieModel X .POmegaMinus n p e)
    (ψ : (modelUniv .POmegaMinus n p e hp.out).K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (modelUniv .POmegaMinus n p e hp.out).K) (P : Sylow 2 X) :
    ∃ (R : Fin ((n - 1) / 2) × Bool → Subgroup (modelUniv .POmegaMinus n p e hp.out).K) (c : X),
      (∀ k, R k ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D ∧
        (R k).map (spinAction (quadMinus n (GaloisField p e)
            (CFSG.LieType.Universal.minusCoeffs p e).1 (CFSG.LieType.Universal.minusCoeffs p e).2) :
            (modelUniv .POmegaMinus n p e hp.out).K →* _) =
          if k.2 then (minusOrthogonalPairFrame (GaloisField p e) n
              (CFSG.LieType.Universal.minusCoeffs p e).1
              (CFSG.LieType.Universal.minusCoeffs p e).2 k.1).swap.La.range
          else (minusOrthogonalPairFrame (GaloisField p e) n
              (CFSG.LieType.Universal.minusCoeffs p e).1
              (CFSG.LieType.Universal.minusCoeffs p e).2 k.1).La.range) ∧
      FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k => (R k).map ((MulAut.conj c).toMonoidHom.comp ψ)) := by
  classical
  let F := GaloisField p e
  let b := (CFSG.LieType.Universal.minusCoeffs p e).1
  let c := (CFSG.LieType.Universal.minusCoeffs p e).2
  let Q := quadMinus n F b c
  let π : (modelUniv .POmegaMinus n p e hp.out).K →* (_ ≃ₗ[F] _) := spinAction Q
  have hπker : π.ker ≤ center (modelUniv .POmegaMinus n p e hp.out).K :=
    ker_spinAction_le_center Q
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd : Odd (Nat.card F) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hcorr :
      (∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
        R.map π ∈ Gaps.fundSet Q) ∧
      ∀ L ∈ Gaps.fundSet Q,
        ∃ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
          R.map π = L := by
    by_cases hq : 5 ≤ p ^ e
    · exact Exotic.fundCorr_minus hp2 hq hadm
    · have hq3 := (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
        hp.out hp2 hadm.2.1).resolve_right hq
      exact Exotic.fundCorr_minus3 hq3 hadm
  have hπmap : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
      ∃ H : Frame Q, R.map π = H.La.range := by
    intro R hR
    obtain ⟨i, H, hH, _⟩ := hcorr.1 R hR
    exact ⟨H, hH⟩
  let A := minusOrthogonalPairFrame F n b c
  have hex : ∀ k : Fin ((n - 1) / 2) × Bool,
      ∃ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
        R.map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range := by
    intro k
    apply hcorr.2
    cases k.2
    · exact ⟨_, IsFundamental.of_frame _⟩
    · exact ⟨_, IsFundamental.of_frame_swap _⟩
  choose R hR hmap using hex
  obtain ⟨c', hc'⟩ := exists_full_paired_model_frame_funSet hp2 (by trivial) hadm hX
    (by simp) (by omega : 0 < (n - 1) / 2) π hπker hπmap A
    (fun i j hij => spanOrth_minusOrthogonalPairFrame F n b c hij)
    (fun H h => not_spanOrth_all_minusOrthogonalPairFrame F n (by omega)
      (CFSG.LieType.Universal.minusCoeffs_irr p e) hodd H h)
    R (fun k => ⟨hR k, hmap k⟩) h2 ψ hψ hker P
  exact ⟨R, c', fun k => ⟨hR k, hmap k⟩, hc'⟩

theorem eq_one_of_forall_funSet_pOmegaPlus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaPlus n p f) (hX : LieModel X .POmegaPlus n p f)
    (P : Sylow 2 X) {r a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ p ^ f * ((p ^ f) ^ 2 - 1)) {x : X} (hxr : x ^ (r ^ a) = 1)
    (hx : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x = 1 := by
  classical
  let F := GaloisField p f
  let Q := quadPlus n F
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨η, hη⟩ := plus_model_data (p := p) (e := f) hn3
  let θ := (spinAction Q).comp η.toMonoidHom
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .POmegaPlus n p f hp.out hp2 (by trivial) hadm X hX
  obtain ⟨R, c, hRdec, hfull⟩ :=
    exists_full_paired_frame_funSet_pOmegaPlus hp2 hn3 hadm hX η hη ψ hψ hker P
  let ψc := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (modelUniv .POmegaPlus n p f hp.out).K := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hy)
  have hηZ : ∀ z ∈ center (modelUniv .POmegaPlus n p f hp.out).K, η z ∈ center (spinGroup Q) := by
    intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := η.surjective y
    simpa only [map_mul] using congrArg η (hz y')
  have hθZ : ∀ z ∈ center (modelUniv .POmegaPlus n p f hp.out).K,
      θ z ∈ CFSG.ClassicalGroups.Orthogonal.scalars F (Fin n ⊕ Fin n → F) :=
    fun z hz => Gaps.spinAction_center_mem_scalars hn3 (hηZ z hz)
  have hθker : θ.ker ≤ center (modelUniv .POmegaPlus n p f hp.out).K := by
    intro y hy
    have hy' : η y ∈ center (spinGroup Q) :=
      ker_spinAction_le_center Q (by simpa only [MonoidHom.mem_ker, θ, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom] using hy)
    rw [Subgroup.mem_center_iff] at hy' ⊢
    intro z
    apply η.injective
    simpa only [map_mul] using hy' (η z)
  have hfull' : FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k => (R k).map ψc) := hfull
  have hA : ∀ k, IsFundamentalOver (p ^ f) ((R k).map ψc) := fun k =>
    ⟨.POmegaPlus, n, p, f, hp.out, hp2, rfl, trivial, hadm, ψc, hψc, hkerC, R k,
      (hRdec k).1, rfl⟩
  let k₀ : Fin (n / 2) × Bool := (⟨0, by omega⟩, false)
  obtain ⟨hZ, _, _, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX (by simp) (hA k₀)
  obtain ⟨g, rfl⟩ := hψc x
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hcommθ : ∀ (k : Fin (n / 2) × Bool) (u : (modelUniv .POmegaPlus n p f hp.out).K),
      u ∈ R k → Commute (θ g) (θ u) := by
    intro k u hu
    have hxK : ψc g ∈ centralizer ((R k).map ψc : Set X) :=
      hx _ (by rw [hfull']; exact Set.mem_range_self k)
    rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hp2 (by trivial) hadm (hRdec k).1 with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
    · exact commute_map_of_mem_of_equiv_sl2 hkerC hθZ eR hxK hu
    · exact commute_map_of_mem_of_equiv_sl2 hkerC hθZ eR hxK hu
  have hL : ∀ (j : Fin (n / 2)) (A : SL(2, F)), Commute (θ g)
      ((plusOrthogonalPairFrame F n hn3 j).La A) := by
    intro j A
    have hmem : (plusOrthogonalPairFrame F n hn3 j).La A ∈ (R (j, false)).map θ := by
      have hk : (R (j, false)).map θ = (plusOrthogonalPairFrame F n hn3 j).La.range :=
        (hRdec (j, false)).2
      rw [hk]
      exact ⟨A, rfl⟩
    obtain ⟨u, hu, hAu⟩ := Subgroup.mem_map.mp hmem
    rw [← hAu]
    exact hcommθ (j, false) u hu
  have hR : ∀ (j : Fin (n / 2)) (A : SL(2, F)), Commute (θ g)
      ((plusOrthogonalPairFrame F n hn3 j).swap.La A) := by
    intro j A
    have hmem : (plusOrthogonalPairFrame F n hn3 j).swap.La A ∈ (R (j, true)).map θ := by
      have hk : (R (j, true)).map θ = (plusOrthogonalPairFrame F n hn3 j).swap.La.range :=
        (hRdec (j, true)).2
      rw [hk]
      exact ⟨A, rfl⟩
    obtain ⟨u, hu, hAu⟩ := Subgroup.mem_map.mp hmem
    rw [← hAu]
    exact hcommθ (j, true) u hu
  have hhO : ∀ y, θ y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun y =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q (η y))
  obtain ⟨s, hs⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.mp
    (hθZ _ (hkerC (by rw [MonoidHom.mem_ker, map_pow, hxr])))
  have hs2 : s ^ 2 = 1 := sq_eq_one_of_smul_mem_orthogonalGroup
    (plusOrthogonalPairFrame F n hn3 ⟨0, by omega⟩) (hhO _) hs
  have hpow2 : (θ g ^ 2) ^ (r ^ a) = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, pow_two, LinearEquiv.mul_apply, hs, hs,
      smul_smul, ← pow_two, hs2, one_smul]
    rfl
  have hcard : Nat.card F = p ^ f := GaloisField.card p f (by have := hadm.2.1; omega)
  have hrq' : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [hcard]
    exact hrq
  have hh1 : θ g ^ 2 = 1 := eq_one_of_commute_plusPairFrames hn3 h2 hr hr2 hrq'
    (pow_mem (hhO g) 2) hpow2 (fun j A => ((hL j A).pow_left 2).eq)
    (fun j A => ((hR j A).pow_left 2).eq)
  have hg2 : g ^ 2 ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hh1
  have hx2 : ψc g ^ 2 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp (ψc.center_le_ker hψc hZ (hθker hg2))
  have hcop : Nat.gcd 2 (r ^ a) = 1 :=
    Nat.Coprime.pow_right a ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
  have h1 : ψc g ^ Nat.gcd 2 (r ^ a) = 1 := pow_gcd_eq_one.mpr ⟨hx2, hxr⟩
  rwa [hcop, pow_one] at h1

theorem eq_one_of_forall_funSet_pOmegaMinus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus n p f) (hX : LieModel X .POmegaMinus n p f)
    (P : Sylow 2 X) {r a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ p ^ f * ((p ^ f) ^ 2 - 1)) (hrq' : Even n → ¬ r ∣ (p ^ f) ^ 2 + 1)
    {x : X} (hxr : x ^ (r ^ a) = 1)
    (hx : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x = 1 := by
  classical
  let F := GaloisField p f
  let b := (CFSG.LieType.Universal.minusCoeffs p f).1
  let c₀ := (CFSG.LieType.Universal.minusCoeffs p f).2
  have hirr : ∀ s : F, s ^ 2 + b * s + c₀ ≠ 0 := CFSG.LieType.Universal.minusCoeffs_irr p f
  let Q := quadMinus n F b c₀
  let θ : (modelUniv .POmegaMinus n p f hp.out).K →* (_ ≃ₗ[F] _) := spinAction Q
  have hn4 : 4 ≤ n := hadm.2.2
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .POmegaMinus n p f hp.out hp2 (by trivial) hadm X hX
  obtain ⟨R, c, hRdec, hfull⟩ :=
    exists_full_paired_frame_funSet_pOmegaMinus hp2 hadm hX ψ hψ hker P
  let ψc := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (modelUniv .POmegaMinus n p f hp.out).K := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hy)
  have hθZ : ∀ z ∈ center (modelUniv .POmegaMinus n p f hp.out).K,
      θ z ∈ CFSG.ClassicalGroups.Orthogonal.scalars F
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) :=
    fun z hz => Exotic.spinAction_center_mem_scalars_minus hn4 hirr hz
  have hθker : θ.ker ≤ center (modelUniv .POmegaMinus n p f hp.out).K :=
    ker_spinAction_le_center Q
  have hfull' : FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k => (R k).map ψc) := hfull
  have hA : ∀ k, IsFundamentalOver (p ^ f) ((R k).map ψc) := fun k =>
    ⟨.POmegaMinus, n, p, f, hp.out, hp2, rfl, trivial, hadm, ψc, hψc, hkerC, R k,
      (hRdec k).1, rfl⟩
  let k₀ : Fin ((n - 1) / 2) × Bool := (⟨0, by omega⟩, false)
  obtain ⟨hZ, _, _, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX (by simp) (hA k₀)
  obtain ⟨g, rfl⟩ := hψc x
  have : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hcommθ : ∀ (k : Fin ((n - 1) / 2) × Bool) (u : (modelUniv .POmegaMinus n p f hp.out).K),
      u ∈ R k → Commute (θ g) (θ u) := by
    intro k u hu
    have hxK : ψc g ∈ centralizer ((R k).map ψc : Set X) :=
      hx _ (by rw [hfull']; exact Set.mem_range_self k)
    rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hp2 (by trivial) hadm (hRdec k).1 with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
    · exact commute_map_of_mem_of_equiv_sl2 hkerC hθZ eR hxK hu
    · exact commute_map_of_mem_of_equiv_sl2 hkerC hθZ eR hxK hu
  have hL : ∀ (j : Fin ((n - 1) / 2)) (A : SL(2, F)), Commute (θ g)
      ((minusOrthogonalPairFrame F n b c₀ j).La A) := by
    intro j A
    have hmem : (minusOrthogonalPairFrame F n b c₀ j).La A ∈ (R (j, false)).map θ := by
      have hk : (R (j, false)).map θ = (minusOrthogonalPairFrame F n b c₀ j).La.range :=
        (hRdec (j, false)).2
      rw [hk]
      exact ⟨A, rfl⟩
    obtain ⟨u, hu, hAu⟩ := Subgroup.mem_map.mp hmem
    rw [← hAu]
    exact hcommθ (j, false) u hu
  have hR : ∀ (j : Fin ((n - 1) / 2)) (A : SL(2, F)), Commute (θ g)
      ((minusOrthogonalPairFrame F n b c₀ j).swap.La A) := by
    intro j A
    have hmem : (minusOrthogonalPairFrame F n b c₀ j).swap.La A ∈ (R (j, true)).map θ := by
      have hk : (R (j, true)).map θ = (minusOrthogonalPairFrame F n b c₀ j).swap.La.range :=
        (hRdec (j, true)).2
      rw [hk]
      exact ⟨A, rfl⟩
    obtain ⟨u, hu, hAu⟩ := Subgroup.mem_map.mp hmem
    rw [← hAu]
    exact hcommθ (j, true) u hu
  have hhO : ∀ y, θ y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun y =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q y)
  obtain ⟨s, hs⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.mp
    (hθZ _ (hkerC (by rw [MonoidHom.mem_ker, map_pow, hxr])))
  have hs2 : s ^ 2 = 1 := sq_eq_one_of_smul_mem_orthogonalGroup
    (minusOrthogonalPairFrame F n b c₀ ⟨0, by omega⟩) (hhO _) hs
  have hpow2 : (θ g ^ 2) ^ (r ^ a) = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, pow_two, LinearEquiv.mul_apply, hs, hs,
      smul_smul, ← pow_two, hs2, one_smul]
    rfl
  have hcard : Nat.card F = p ^ f := GaloisField.card p f (by have := hadm.2.1; omega)
  have hrqF : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [hcard]
    exact hrq
  have hrqF' : Even n → ¬ r ∣ Nat.card F ^ 2 + 1 := by
    rw [hcard]
    exact hrq'
  have hh1 : θ g ^ 2 = 1 := eq_one_of_commute_minusPairFrames hirr hn4 h2 hr hr2 hrqF hrqF'
    (pow_mem (hhO g) 2) hpow2 (fun j A => ((hL j A).pow_left 2).eq)
    (fun j A => ((hR j A).pow_left 2).eq)
  have hg2 : g ^ 2 ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hh1
  have hx2 : ψc g ^ 2 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp (ψc.center_le_ker hψc hZ (hθker hg2))
  have hcop : Nat.gcd 2 (r ^ a) = 1 :=
    Nat.Coprime.pow_right a ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
  have h1 : ψc g ^ Nat.gcd 2 (r ^ a) = 1 := pow_gcd_eq_one.mpr ⟨hx2, hxr⟩
  rwa [hcop, pow_one] at h1

open CFSG.ClassicalGroups.Orthogonal.Small in
open scoped Pointwise in
theorem eq_bot_of_permutes_of_forall_funSet_pOmegaMinus_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus (2 * m + 2) p f)
    (hX : LieModel X .POmegaMinus (2 * m + 2) p f) (P : Sylow 2 X) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hr7 : r ≠ 7) (hr8 : ¬ 8 ∣ r - 1) (hrq : ¬ r ∣ p ^ f)
    (hr1 : ¬ r ∣ p ^ f - 1) (hr2 : ¬ r ∣ (p ^ f) ^ 2 - 1) (hr3 : ¬ r ∣ (p ^ f) ^ 3 - 1)
    (hN2 : ((p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) / 2).factorization 2 = 3)
    (hNr : ¬ r ^ 2 ∣ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) / 2) {B : Subgroup X} (hB : IsPGroup r B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (hcent : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  classical
  let F := GaloisField p f
  let b := (CFSG.LieType.Universal.minusCoeffs p f).1
  let c₀ := (CFSG.LieType.Universal.minusCoeffs p f).2
  have hirr : ∀ s : F, s ^ 2 + b * s + c₀ ≠ 0 := CFSG.LieType.Universal.minusCoeffs_irr p f
  let Q := quadMinus (2 * m + 2) F b c₀
  let θ : (modelUniv .POmegaMinus (2 * m + 2) p f hp.out).K →* (_ ≃ₗ[F] _) := spinAction Q
  have hn4 : 4 ≤ 2 * m + 2 := hadm.2.2
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card F) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  have hcard : Nat.card F = p ^ f := GaloisField.card p f (by have := hadm.2.1; omega)
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .POmegaMinus (2 * m + 2) p f hp.out hp2 (by trivial) hadm X hX
  obtain ⟨R, c, hRdec, hfull⟩ :=
    exists_full_paired_frame_funSet_pOmegaMinus hp2 hadm hX ψ hψ hker P
  let ψc := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (modelUniv .POmegaMinus (2 * m + 2) p f hp.out).K := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hy)
  have hfull' : FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k => (R k).map ψc) := hfull
  have hA : ∀ k, IsFundamentalOver (p ^ f) ((R k).map ψc) := fun k =>
    ⟨.POmegaMinus, 2 * m + 2, p, f, hp.out, hp2, rfl, trivial, hadm, ψc, hψc, hkerC, R k,
      (hRdec k).1, rfl⟩
  let k₀ : Fin ((2 * m + 2 - 1) / 2) × Bool := (⟨0, by omega⟩, false)
  obtain ⟨hZ, _, _, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX (by simp) (hA k₀)
  have hθZ : ∀ z ∈ center (modelUniv .POmegaMinus (2 * m + 2) p f hp.out).K, θ z = 1 :=
    fun z hz => spinAction_center_eq_one_of_even h2 hirr hn4 ⟨m + 1, by ring⟩ hz
  have hθker : θ.ker ≤ center (modelUniv .POmegaMinus (2 * m + 2) p f hp.out).K :=
    ker_spinAction_le_center Q
  obtain ⟨φ, hφinj, hφ⟩ := exists_injective_comp_eq_of_ker_eq hψc
    (fun z hz => MonoidHom.mem_ker.mpr (hθZ z (hkerC hz)))
    (fun z hz => ψc.center_le_ker hψc hZ (hθker hz))
  have hφθ : φ.comp ψc = θ := MonoidHom.ext hφ
  have hφO : ∀ x, φ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro x
    obtain ⟨g, rfl⟩ := hψc x
    rw [hφ]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q g)
  have hrange : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ φ.range := by
    rw [← range_spinAction_quadMinus_eq_commutator hn4 hirr]
    rintro _ ⟨g, rfl⟩
    exact ⟨ψc g, hφ g⟩
  have hLk : ∀ k, ((R k).map ψc).map φ = minusFrameFactor m F b c₀ k := by
    intro k
    rw [Subgroup.map_map, hφθ]
    exact (hRdec k).2
  have hmem : ∀ k, (R k).map ψc ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
    intro k
    rw [hfull']
    exact Set.mem_range_self k
  have hPL : ∀ y ∈ (P : Subgroup X), ∀ k, ∃ k',
      (minusFrameFactor m F b c₀ k).map (MulAut.conj (φ y)).toMonoidHom =
        minusFrameFactor m F b c₀ k' := by
    intro y hy k
    have hK := F14.mem_funSet_map_conj_of_mem_normalizer (𝔉 := fundPred (p ^ f))
      (fun g {_} hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK)
      (Subgroup.le_normalizer hy) (hmem k)
    rw [hfull'] at hK
    obtain ⟨k', hk'⟩ := hK
    dsimp only at hk'
    have hconj : ∀ H : Subgroup X, (H.map φ).map (MulAut.conj (φ y)).toMonoidHom =
        (H.map (MulAut.conj y).toMonoidHom).map φ := by
      intro H
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    refine ⟨k', ?_⟩
    rw [← hLk k, ← hLk k', hk']
    exact hconj _
  have hBL : ∀ x ∈ B, ∀ k, ∀ ℓ ∈ ((R k).map ψc).map φ, φ x * ℓ = ℓ * φ x := by
    intro x hx k ℓ hℓ
    obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.mp hℓ
    have hxκ := Subgroup.mem_centralizer_iff.mp (hcent _ (hmem k) hx) κ hκ
    rw [← map_mul, ← map_mul, hxκ]
  have hBfix : ∀ x ∈ B, φ x ∈ stabSub (minusResidualSub m 1 F) ∧
      ∀ u ∈ minusFrameSub m F, φ x u = u := by
    intro x hx
    obtain ⟨a, ha⟩ := hB ⟨x, hx⟩
    have hxa : x ^ (r ^ a) = 1 := by simpa using congrArg Subtype.val ha
    have hpow : φ x ^ (r ^ a) = 1 := by rw [← map_pow, hxa, map_one]
    have hL : ∀ (j : Fin ((2 * m + 2 - 1) / 2)) (A : SL(2, F)),
        φ x * (minusOrthogonalPairFrame F (2 * m + 2) b c₀ j).La A =
          (minusOrthogonalPairFrame F (2 * m + 2) b c₀ j).La A * φ x :=
      fun j A => hBL x hx (j, false) _ (by rw [hLk]; exact ⟨A, rfl⟩)
    have hR : ∀ (j : Fin ((2 * m + 2 - 1) / 2)) (A : SL(2, F)),
        φ x * (minusOrthogonalPairFrame F (2 * m + 2) b c₀ j).swap.La A =
          (minusOrthogonalPairFrame F (2 * m + 2) b c₀ j).swap.La A * φ x :=
      fun j A => hBL x hx (j, true) _ (by rw [hLk]; exact ⟨A, rfl⟩)
    exact mem_stabSub_and_fix_of_forall_fix_basis m (hφO x)
      (fixes_pairs_of_commute_minusPairFrames h2 hr (by omega) (hφO x) hpow hL hR)
  have hPW : ∀ y ∈ (P : Subgroup X), φ y ∈ stabSub (minusResidualSub m 1 F) := by
    intro y hy
    refine mem_stabSub_minusResidualSub_of_map_conj m h2 b c₀ (hPL y hy) fun k => ?_
    obtain ⟨k', hk'⟩ := hPL y⁻¹ (inv_mem hy) k
    exact ⟨k', by rw [← map_inv]; exact hk'⟩
  rw [← hcard] at hrq hr1 hr2 hr3 hN2 hNr
  exact eq_bot_of_stabSub_orthogonal_nonsplit_four hodd
    (nondegenerate_polarBilin_quadMinus_of_finite (2 * m + 2) F hirr)
    (isCompl_minusResidualSub_minusFrameSub m F) (polar_minusResidualSub_minusFrameSub m b c₀)
    (finrank_minusResidualSub m F) (not_exists_singular_plane_minusResidualSub m hirr)
    hφinj hφO hrange hr hr5 hr7 hr8 hrq hr1 hr2 hr3 hN2 hNr P hPW hB hperm
    (fun x hx => (hBfix x hx).1) (fun x hx => (hBfix x hx).2)

end EvenOrthProof

theorem eq_bot_of_forall_funSet_pOmegaPlus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p : ℕ}
    (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible .POmegaPlus n p 1)
    (hX : LieModel X .POmegaPlus n p 1) (P : Sylow 2 X) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ FunSet (fundPred p) X (P : Subgroup X), B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  refine eq_bot_of_isPGroup_of_forall_pow hB fun x hx a hxr =>
    eq_one_of_forall_funSet_pOmegaPlus hp2 hadm hX P hr (by omega)
      (not_dvd_mul_sq_sub_one_of_three_or_five hp35 hr hr5 hrp) hxr fun K hK => ?_
  rw [pow_one] at hK
  exact hcent K hK hx

theorem eq_bot_of_forall_funSet_pOmegaMinus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p : ℕ}
    (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible .POmegaMinus n p 1)
    (hX : LieModel X .POmegaMinus n p 1) (P : Sylow 2 X) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p)
    (hgood : ¬ (Even n ∧ ((p = 3 ∧ r = 5) ∨ (p = 5 ∧ r = 13)))) {B : Subgroup X}
    (hB : IsPGroup r B)
    (hcent : ∀ K ∈ FunSet (fundPred p) X (P : Subgroup X), B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hrq' : Even n → ¬ r ∣ (p ^ 1) ^ 2 + 1 := by
    intro hn hd
    refine hgood ⟨hn, ?_⟩
    have hle : r ≤ 26 := by
      have := Nat.le_of_dvd (by positivity) hd
      rcases hp35 with rfl | rfl <;> norm_num at this <;> omega
    rcases hp35 with rfl | rfl <;> interval_cases r <;> (revert hd hr hrp; norm_num)
  refine eq_bot_of_isPGroup_of_forall_pow hB fun x hx a hxr =>
    eq_one_of_forall_funSet_pOmegaMinus hp2 hadm hX P hr (by omega)
      (not_dvd_mul_sq_sub_one_of_three_or_five hp35 hr hr5 hrp) hrq' hxr fun K hK => ?_
  rw [pow_one] at hK
  exact hcent K hK hx

open scoped Pointwise in
theorem eq_bot_of_permutes_of_forall_funSet_pOmegaMinus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p : ℕ}
    (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible .POmegaMinus n p 1)
    (hX : LieModel X .POmegaMinus n p 1) (P : Sylow 2 X) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) {B : Subgroup X} (hB : IsPGroup r B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (hcent : ∀ K ∈ FunSet (fundPred p) X (P : Subgroup X), B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  by_cases hgood : Even n ∧ ((p = 3 ∧ r = 5) ∨ (p = 5 ∧ r = 13))
  swap
  · exact eq_bot_of_forall_funSet_pOmegaMinus hp35 hadm hX P hr hr5 hrp hgood hB hcent
  obtain ⟨hn, hpr⟩ := hgood
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := by
    obtain ⟨k, hk⟩ := hn
    have := hadm.2.2
    exact ⟨k - 1, by omega⟩
  have hcent' : ∀ K ∈ FunSet (fundPred (p ^ 1)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X) := by
    rw [pow_one]
    exact hcent
  rcases hpr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact eq_bot_of_permutes_of_forall_funSet_pOmegaMinus_even (by norm_num) hadm hX P hr hr5
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (factorization_two_eq_three_of_eq (k := 45) (by norm_num) (by norm_num)) (by norm_num)
      hB hperm hcent'
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact eq_bot_of_permutes_of_forall_funSet_pOmegaMinus_even (by norm_num) hadm hX P hr hr5
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (factorization_two_eq_three_of_eq (k := 975) (by norm_num) (by norm_num)) (by norm_num)
      hB hperm hcent'

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
