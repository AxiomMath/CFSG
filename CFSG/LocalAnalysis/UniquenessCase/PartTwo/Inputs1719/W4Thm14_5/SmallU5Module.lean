module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.FieldDegree
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
public import CFSG.LieType.Universal.Unitary.BinaryModel.CurtisType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.ScalarCore
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.EndField

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Module Finset Matrix
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.HardMathSupport.GuralnickMalle
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.RootSystem
open CFSG.LieType.SpecialLinear.ExteriorModel CFSG.Quasithin.SmithCurtis
open scoped MonoidAlgebra TensorProduct

theorem twentyOne_le_mul_movedTop_su54 {s : ℕ} (ε : Fin 2 → Finset (Fin 5))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin 5) ∉ ε r) (ht : ∃ r, ε r ≠ ∅)
    (hs : 2 ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hns : (∃ r, (ε r).image labelStar ≠ ε r) → 4 ≤ s)
    (hscal : 5 ∣ ∑ i : Fin 2, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ)) :
    21 ≤ s * movedTop (n := 5) (by norm_num) ε := by
  classical
  set T := univ.filter fun r => ε r ≠ ∅ with hT
  have hmemT : ∀ r, r ∈ T ↔ ε r ≠ ∅ := fun r => by simp [hT]
  have hsym1 : ∀ r, (ε r).card = 1 → (ε r).image labelStar ≠ ε r := by
    intro r h1 himg
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
    rw [hj, Finset.image_singleton, Finset.singleton_inj] at himg
    have hj0 : (j : ℕ) ≠ 0 := fun h =>
      h0 r (by rw [hj]; exact Finset.mem_singleton.mpr (Fin.ext h.symm))
    have hval := congrArg Fin.val himg
    rw [labelStar_apply] at hval
    have hj5 := j.isLt
    rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega
  have hcard_pos : ∀ r, ε r ≠ ∅ → 0 < (ε r).card := fun r hr =>
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hr)
  have hT2 : T.card ≤ 2 := (Finset.card_le_univ T).trans (by simp)
  by_cases h2 : T.card = 2
  ·
    have hT : T = univ := Finset.eq_univ_of_card T (by simpa using h2)
    have hε : ∀ r, ε r ≠ ∅ := fun r => (hmemT r).mp (hT ▸ Finset.mem_univ r)
    have hformula := movedTop_of_two (n := 5) (by norm_num) ε (i₁ := 0) (i₂ := 1) (by decide)
      (fun i h1 h2 => by fin_cases i <;> simp_all)
    have hN₁ := n_le_orbitSize (n := 5) (by norm_num) (h0 1) (hε 1)
    have hM₀ := two_le_movedOrbit (n := 5) (by norm_num) (h0 0) (hε 0)
    rw [hformula]
    by_cases hsym : ∃ r, (ε r).image labelStar ≠ ε r
    · have hs4 := hns hsym
      have h10 : 10 ≤ movedOrbit (n := 5) (by norm_num) (ε 0) * orbitSize (ε 1) :=
        (Nat.mul_le_mul hM₀ hN₁)
      nlinarith
    · push Not at hsym
      have hc0 : 2 ≤ (ε 0).card := by
        by_contra hc
        exact hsym1 0 (by have := hcard_pos 0 (hε 0); omega) (hsym 0)
      have hM := two_mul_two_mul_sub_three_le_movedOrbit (n := 5) (by norm_num) (h0 0)
        (by omega : 3 ≤ (ε 0).card + 1)
      have hs1 : 1 ≤ s := by
        rw [h2] at hs
        omega
      have h70 : 70 ≤ movedOrbit (n := 5) (by norm_num) (ε 0) * orbitSize (ε 1) :=
        (Nat.mul_le_mul hM hN₁)
      nlinarith
  ·
    have hTpos : 0 < T.card := by
      obtain ⟨r, hr⟩ := ht
      exact Finset.card_pos.mpr ⟨r, (hmemT r).mpr hr⟩
    have h1 : T.card = 1 := by omega
    obtain ⟨r₀, hT1⟩ := Finset.card_eq_one.mp h1
    have hr₀ : ε r₀ ≠ ∅ := (hmemT r₀).mp (by rw [hT1]; exact Finset.mem_singleton_self _)
    have hrest : ∀ r, r ≠ r₀ → ε r = ∅ := by
      intro r hr
      by_contra hne
      have hrT : r ∈ T := (hmemT r).mpr hne
      rw [hT1] at hrT
      exact hr (Finset.mem_singleton.mp hrT)
    have hmt := movedTop_of_one (n := 5) (by norm_num) ε r₀ hrest
    have hs2 : 2 ≤ s := by
      rw [h1, mul_one] at hs
      exact hs
    have hc : 2 ≤ (ε r₀).card := by
      by_contra hc
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by have := hcard_pos r₀ hr₀; omega :
        (ε r₀).card = 1)
      have h5 := prime_dvd_of_scalar_singleton Nat.prime_five (by norm_num) hrest hj hscal
      have hj0 : (j : ℕ) ≠ 0 := fun h =>
        h0 r₀ (by rw [hj]; exact Finset.mem_singleton.mpr (Fin.ext h.symm))
      have hj5 := j.isLt
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) h5
      omega
    have hM := two_mul_two_mul_sub_three_le_movedOrbit (n := 5) (by norm_num) (h0 r₀)
      (by omega : 3 ≤ (ε r₀).card + 1)
    rw [hmt]
    nlinarith

theorem eleven_le_finrank_range_su54 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 2) ^ 2) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 2) 5) W) (hirr : ρ.IsIrreducible)
    (hne : ∃ g, ρ g ≠ 1)
    (hscal : ∀ (c : Kˣ) (hc : GeneralLinearGroup.scalar (Fin 5) c ∈ SU (unitaryInvolution K 2 2) 5),
      ρ ⟨_, hc⟩ = 1)
    {x : SU (unitaryInvolution K 2 2) 5} (hx : x * x = 1) (hx1 : x ≠ 1) :
    11 ≤ finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : ρ.IsIrreducible := hirr
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let E := End (ZMod 2)[SU (unitaryInvolution K 2 2) 5] ρ.asModule
  obtain ⟨s, hs_pos, hE⟩ := exists_card_endField_eq_two_pow (ρ := ρ)
  let k := AlgebraicClosure E
  obtain ⟨φ₀⟩ := nonempty_ringHom_algebraicClosure (K := E) (F₀ := K) (p := 2)
  let : Algebra K k := φ₀.toAlgebra
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  let τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  have hsimp : IsSimpleRep τ := isSimpleRep_extendScalars_endFieldRep (ρ := ρ) (k := k)
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero (p := 2) hK
  let D := curtisDatum hK 5 (by norm_num) ζ hζ
  have hsplit : SplitOver k D.H := curtisDatum_splitOver hK 5 (by norm_num) ζ hζ k
  have : Finite (coxeterMatrix (isFiniteType_cartan 5)).Group :=
    finite_group (isFiniteType_cartan 5)
  obtain ⟨y, χ, μ, htype⟩ := D.exists_isCurtisType hsplit hsimp
  obtain ⟨ε, h0, hχ, -, β, hβ⟩ := exists_iso_suRep hK (by norm_num) ζ hζ φ₀ hsimp htype
  have hH : D.H = ⨆ i, levelTorus (unitaryInvolution K 2 2) (n := 5) i := by
    unfold D curtisDatum
    rfl
  have hχε : ∀ h ∈ ⨆ i, levelTorus (unitaryInvolution K 2 2) (n := 5) i,
      chiEps φ₀ ε h ^ 2 ^ s = chiEps φ₀ ε h := by
    intro h hh
    rw [← hH] at hh
    have h1 := isCurtisType_chi_pow_card (ρ := ρ) (D := D) (k := k) htype hh
    rw [hE] at h1
    rw [← hχ h hh]
    exact h1
  have ht : ∃ i, ε i ≠ ∅ := by
    by_contra hall
    push Not at hall
    obtain ⟨g, hg⟩ := hne
    apply hg
    have h1 := suRep_eq_one_of_forall_eq_empty φ₀ hall g
    exact (extendScalars_endFieldRep_eq_one_iff (ρ := ρ) (k := k) g).mp
      ((eq_one_iff_of_equiv β hβ g).mpr h1)
  have hs := le_mul_card_of_chiEps_pow hK (by norm_num) φ₀ h0 ht hs_pos hχε
  have hns : (∃ r, (ε r).image labelStar ≠ ε r) → 4 ≤ s := fun hns =>
    two_mul_le_of_chiEps_pow hK (by norm_num) φ₀ h0 hs_pos hχε
      ((Finset.card_le_univ _).trans (by simp)) hns
  have hKu : Nat.card Kˣ = 15 := by
    rw [Nat.card_units, hK]
    norm_num
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨c, hc5⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 5 (by rw [hKu]; norm_num)
  have hcS : GeneralLinearGroup.scalar (Fin 5) c ∈ CFSG.Open.StatedSU 5 (2 ^ 2) K := by
    refine (CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hK (by norm_num) c).mpr
      ⟨?_, ?_⟩
    · rw [← hc5]
      exact pow_orderOf_eq_one c
    · rw [show 2 ^ 2 + 1 = 5 by norm_num, ← hc5]
      exact pow_orderOf_eq_one c
  have hcSU := scalar_mem_SU_of_mem_statedSU hK hcS
  have hsuc : suRep φ₀ 5 ε ⟨_, hcSU⟩ = 1 :=
    (eq_one_iff_of_equiv β hβ _).mp
      ((extendScalars_endFieldRep_eq_one_iff (ρ := ρ) (k := k) _).mpr (hscal c hcSU))
  have hdiv := orderOf_dvd_of_suRep_scalar_eq_one φ₀ ε hcSU hsuc
  rw [hc5] at hdiv
  have h21 := twentyOne_le_mul_movedTop_su54 ε h0 ht hs hns hdiv
  have hrank := finrank_range_sub_one_eq_mul ρ hE k x
  have hrankβ := finrank_range_sub_one_eq_of_equiv β hβ x
  obtain ⟨π, hπ, hπ01, hrankπ⟩ := exists_perm_finrank_range_suRep_sub_one φ₀ (by norm_num) ε hx hx1
  have htop : movedTop (n := 5) (by norm_num) ε ≤
      2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
    unfold movedTop
    convert card_moved_top_le (k := k) ε (by norm_num) π hπ hπ01
  rw [hrankπ, ← hrankβ] at htop
  have hle : s * movedTop (n := 5) (by norm_num) ε ≤
      2 * finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
    rw [hrank]
    calc s * movedTop (n := 5) (by norm_num) ε
        ≤ s * (2 * finrank k (LinearMap.range (τ x - 1))) := Nat.mul_le_mul_left s htop
      _ = 2 * (s * finrank k (LinearMap.range (τ x - 1))) := by ring
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
