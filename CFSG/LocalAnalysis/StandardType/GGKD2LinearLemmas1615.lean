module

public import CFSG.LocalAnalysis.StandardType.GGKD2LinearBlock1615
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel
public import CFSG.RankThree.PartOne.FOC.PSLDecomp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
public import CFSG.Goldschmidt.Steps.G37Core

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.Open (StatedSL StatedProj)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma ltrclh1_sylow_two_projectiveSL {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ T : Sylow 2 (projectiveSL n F),
      Nat.card (T : Subgroup (projectiveSL n F)) = Nat.card F ^ (n * (n - 1) / 2) := by
  obtain ⟨T, hT⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
      (K := F) 2 (n := n) hn
  exact ⟨T, by rw [hT, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_projUnitriangular]⟩

private lemma ltrclh1_eq_two_of_equiv {k : ℕ} {E K₀ : Type}
    [Field E] [Finite E] [CharP E 2] [Field K₀] [Finite K₀] [CharP K₀ 2] (hk : 2 ≤ k)
    (e : projectiveSL k E ≃* projectiveSL 2 K₀) : k = 2 := by
  have hcard : Nat.card E = Nat.card K₀ :=
    CFSG.Quasithin.B69.card_eq_of_equiv_projectiveSL hk (by norm_num) e
  obtain ⟨T, hT⟩ := ltrclh1_sylow_two_projectiveSL (F := E) (n := k) (by omega)
  obtain ⟨T', hT'⟩ := ltrclh1_sylow_two_projectiveSL (F := K₀) (n := 2) (by norm_num)
  have hcardT : Nat.card (T : Subgroup (projectiveSL k E)) =
      Nat.card (T' : Subgroup (projectiveSL 2 K₀)) := by
    have hmap : Nat.card ((T : Subgroup (projectiveSL k E)).map e.toMonoidHom) =
        Nat.card (T : Subgroup (projectiveSL k E)) :=
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    have heq := Sylow.equiv (T.mapSurjective (f := e.toMonoidHom) e.surjective) T'
    calc Nat.card (T : Subgroup (projectiveSL k E))
        = Nat.card ((T : Subgroup (projectiveSL k E)).map e.toMonoidHom) := hmap.symm
      _ = Nat.card (T' : Subgroup (projectiveSL 2 K₀)) := Nat.card_congr heq.toEquiv
  have hpow : Nat.card E ^ (k * (k - 1) / 2) = Nat.card E ^ (2 * (2 - 1) / 2) := by
    rw [hT, hT', ← hcard] at hcardT
    exact hcardT
  have hq : 2 ≤ Nat.card E := by
    have := Finite.one_lt_card (α := E)
    omega
  have hexp : k * (k - 1) / 2 = 2 * (2 - 1) / 2 := Nat.pow_right_injective hq hpow
  have hk2 : k * (k - 1) = 2 := by
    have h := Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
    rw [hexp] at h
    omega
  have hk3 : k ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ k := by omega
    have h3 : 3 ≤ k - 1 := by omega
    have := Nat.mul_le_mul h4 h3
    omega
  interval_cases k <;> omega

theorem kd2Lin_numerology {k : ℕ} {E : Type} [Field E] [Finite E] (h2E : (2 : E) = 0)
    (hk : 2 ≤ k) {Q : Type} [Group Q] (φ : Q ≃* StatedProj (StatedSL k E))
    (hQ : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) Q) : k = 2 ∧ Nat.card E = 8 := by
  haveI hcharE : CharP E 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2E
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeLinear] at hQ
  obtain ⟨K₀, hfK₀, hfinK₀, hcardK₀, hQ0⟩ := hQ
  letI : Field K₀ := hfK₀
  letI : Finite K₀ := hfinK₀
  letI : Fintype K₀ := Fintype.ofFinite K₀
  obtain ⟨eQ⟩ := hQ0
  have hK8 : Nat.card K₀ = 8 := by
    rw [hcardK₀]
    norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharK : CharP K₀ 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 3) (by
      rw [← Nat.card_eq_fintype_card]
      exact hcardK₀)
  let ebridge : LargeEvenProj (LargeEvenSLGroup (Fin (1 + 1)) K₀) ≃*
      StatedProj (StatedSL 2 K₀) :=
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenProj_equiv_statedProj
      (a := 1 + 1) (E := K₀) (H := LargeEvenSLGroup (Fin (1 + 1)) K₀)
      (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := K₀) (1 + 1))).some
  have e1 : StatedProj (StatedSL k E) ≃* StatedProj (StatedSL 2 K₀) :=
    φ.symm.trans (eQ.trans ebridge)
  have e2 : projectiveSL k E ≃* projectiveSL 2 K₀ :=
    ((CFSG.ComponentClassification.SymmetricLocal.statedProjEquivProjectiveSL k E).symm.trans
        e1).trans
      (CFSG.ComponentClassification.SymmetricLocal.statedProjEquivProjectiveSL 2 K₀)
  have hcardE : Nat.card E = 8 := by
    have h := CFSG.Quasithin.B69.card_eq_of_equiv_projectiveSL (m := k) (n := 2) hk
      (by norm_num) e2
    rwa [hK8] at h
  exact ⟨ltrclh1_eq_two_of_equiv hk e2, hcardE⟩

theorem kd2Lin_actor {d : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] (ψ₀ : L' →* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    {a : MulAut L'} (β : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hβ : β ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
    (hβa : ∀ l : L', β (ψ₀ l) = ψ₀ (a l)) :
    ∃ (N : GL (Fin d) K) (hNnorm : N ∈ Subgroup.normalizer
        ((LargeEvenSLGroup (Fin d) K : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))),
      ∀ l : L', TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨N, hNnorm⟩ (ψ₀ l) = ψ₀ (a l) := by
  have hnorm : (Set.univ : Set (GL (Fin d) K)) ⊆ Subgroup.normalizer
      ((LargeEvenSLGroup (Fin d) K : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)) := by
    intro A _
    simp [Subgroup.normalizer_eq_top]
  obtain ⟨N, hA, hβN⟩ :=
    TableB.exists_eq_projConj (H := LargeEvenSLGroup (Fin d) K) hnorm hβ
  refine ⟨N, hnorm hA, ?_⟩
  intro l
  rw [← hβN]
  exact hβa l

private lemma ltrclh3_kernel_scalar {d n : ℕ} {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 2 ^ n) (hd : 2 ≤ d) (hdn : d = 2 → 2 ≤ n)
    (X : Subgroup.normalizer (LargeEvenSLGroup (Fin d) K : Set (GL (Fin d) K)))
    (hX : TableB.projConj (LargeEvenSLGroup (Fin d) K) X = 1) :
    (X : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := by
  have hperf : Group.IsPerfect ↥(LargeEvenSLGroup (Fin d) K) := by
    let e := MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL (K := K) d)
    haveI : Group.IsPerfect ↥(StatedSL d K) := by
      by_cases hd3 : 3 ≤ d
      · exact CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hd3 K
      · have hd2 : d = 2 := by omega
        rw [hd2]
        refine CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card ?_
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hdn hd2)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hker : (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin d) K) := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center
  have hcomm := CFSG.LocalAnalysis.GLTheoremA.T171Sh.commute_of_projConj_eq_one hperf hker X hX
  have hcenter : (X : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) :=
    CFSG.RankThree.PartOne.FOC.mem_center_of_commute_SL (X : GL (Fin d) K) fun s => by
      have hmem : Matrix.SpecialLinearGroup.toGL s ∈ LargeEvenSLGroup (Fin d) K := by
        rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff]
        exact s.2
      exact (hcomm _ hmem).symm
  rw [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact hcenter

theorem kd2Lin_zeta {d n : ℕ} {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2 ^ n)
    (hd : 2 ≤ d) (hdn : d = 2 → 2 ≤ n)
    {L' : Type} [Group L'] (ψ₀ : L' →* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hψ₀ : Function.Surjective ψ₀) {e a : MulAut L'} (hea : a * e = e * a)
    {M N : GL (Fin d) K}
    (hMN : M ∈ Subgroup.normalizer
      ((LargeEvenSLGroup (Fin d) K : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)))
    (hNN : N ∈ Subgroup.normalizer
      ((LargeEvenSLGroup (Fin d) K : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)))
    (hM3 : M ^ 3 = 1)
    (he : ∀ l : L', TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨M, hMN⟩ (ψ₀ l) = ψ₀ (e l))
    (ha : ∀ l : L', TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨N, hNN⟩ (ψ₀ l) = ψ₀ (a l)) :
    ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ N * M * N⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * M := by
  have hcomm : TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨N, hNN⟩ *
      TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨M, hMN⟩ =
      TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨M, hMN⟩ *
      TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨N, hNN⟩ := by
    ext x
    obtain ⟨l, rfl⟩ := hψ₀ x
    simp only [MulAut.mul_apply]
    rw [he l, ha (e l), ha l, he (a l)]
    congr 1
    have h := congrArg (fun f : MulAut L' => f l) hea
    simpa only [MulAut.mul_apply] using h
  let X : Subgroup.normalizer (LargeEvenSLGroup (Fin d) K : Set (GL (Fin d) K)) :=
    ⟨N, hNN⟩ * ⟨M, hMN⟩ * ⟨N, hNN⟩⁻¹ * ⟨M, hMN⟩⁻¹
  have hX : TableB.projConj (LargeEvenSLGroup (Fin d) K) X = 1 := by
    simp only [X]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hXmem : (X : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
    ltrclh3_kernel_scalar hcard hd hdn X hX
  rw [largeEvenScalars_def] at hXmem
  obtain ⟨ζ, hζ⟩ := hXmem
  have hXval : (X : GL (Fin d) K) = N * M * N⁻¹ * M⁻¹ := by
    simp only [X, Subgroup.coe_mul, Subgroup.coe_inv]
  have hDval : N * M * N⁻¹ * M⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ := by
    rw [← hXval]
    exact hζ.symm
  have hNM : N * M * N⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * M := by
    calc N * M * N⁻¹ = (N * M * N⁻¹ * M⁻¹) * M := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * M := by rw [hDval]
  have h3 : (N * M * N⁻¹) ^ 3 = 1 := by
    have hpow : (N * M * N⁻¹) ^ 3 = N * M ^ 3 * N⁻¹ := by
      rw [pow_three, pow_three]
      group
    rw [hpow, hM3, mul_one, mul_inv_cancel]
  have hcM : Commute M (Matrix.GeneralLinearGroup.scalar (Fin d) ζ) :=
    (Subgroup.mem_center_iff.mp
      (TableB.scalars_le_center (by rw [largeEvenScalars_def]; exact ⟨ζ, rfl⟩))) M
  have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) ζ) M := hcM.symm
  have hcube : (Matrix.GeneralLinearGroup.scalar (Fin d) ζ * M) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ 3) := by
    rw [hc.mul_pow, ← map_pow, hM3, mul_one]
  have hscalar1 : Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ 3) = 1 := by
    rw [← hcube, ← hNM]
    exact h3
  refine ⟨ζ, ?_, hNM⟩
  have hmat : ((Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ 3) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = 1 := by
    have h := congrArg (fun A : GL (Fin d) K => (A : Matrix (Fin d) (Fin d) K)) hscalar1
    simpa using h
  have h00 : (↑(ζ ^ 3) : K) = 1 := by
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) K =>
      A ⟨0, by omega⟩ ⟨0, by omega⟩) hmat
    rw [Matrix.GeneralLinearGroup.coe_scalar] at h
    simpa using h
  exact Units.ext h00

theorem kd2Lin_zeta_one {K E : Type} [Field K] [Field E] [Algebra K E] [Finite E]
    (hE : Nat.card E = 8) {ζ : Kˣ} (hζ : ζ ^ 3 = 1) : ζ = 1 := by
  have hcard7 : Nat.card Eˣ = 7 := by
    rw [Nat.card_units, hE]
  let φ : Kˣ →* Eˣ := Units.map (algebraMap K E).toMonoidHom
  have hφζ : φ ζ ^ 3 = 1 := by rw [← map_pow, hζ, map_one]
  have hdvd3 : orderOf (φ ζ) ∣ 3 := orderOf_dvd_of_pow_eq_one hφζ
  have hdvd7 : orderOf (φ ζ) ∣ 7 := by
    simpa [hcard7] using orderOf_dvd_natCard (φ ζ)
  have hφζ1 : φ ζ = 1 := by
    refine orderOf_eq_one_iff.mp (Nat.dvd_one.mp ?_)
    have hg : orderOf (φ ζ) ∣ Nat.gcd 3 7 := Nat.dvd_gcd hdvd3 hdvd7
    rwa [show Nat.gcd 3 7 = 1 by norm_num] at hg
  have hinj : Function.Injective (algebraMap K E) := by
    intro x y hxy
    have h : algebraMap K E (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    by_contra hne
    have hz : x - y ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
    have h1 : algebraMap K E (x - y) * algebraMap K E ((x - y)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hz, map_one]
    rw [h, zero_mul] at h1
    exact one_ne_zero h1.symm
  have hcoe : algebraMap K E (ζ : K) = 1 := by
    have := congrArg (fun u : Eˣ => (u : E)) hφζ1
    simpa [φ] using this
  have hval : (ζ : K) = 1 := by
    apply hinj
    rw [hcoe]
    simp
  exact Units.ext hval

private lemma ltrclh4_mulSingle_conj {ι : Type*} [DecidableEq ι] {G : ι → Type*}
    [∀ i, Group (G i)] (i : ι) (ν : ∀ k, G k) (γ : G i) :
    ν * MonoidHom.mulSingle G i γ * ν⁻¹ =
      MonoidHom.mulSingle G i (ν i * γ * (ν i)⁻¹) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [MonoidHom.mulSingle_apply, Pi.mulSingle_apply]
  · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_apply, hk]

theorem kd2Lin_inner_two {k : ℕ} (hk : k = 2) {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 8) (ν : GL (Fin k) E) :
    ∃ s ∈ StatedSL k E, ∀ γ : GL (Fin k) E, ν * γ * ν⁻¹ = s * γ * s⁻¹ := by
  subst hk
  have h2E : (2 : E) = 0 := by
    have h0 : Nat.card E • (1 : E) = 0 := card_nsmul_eq_zero'
    rw [nsmul_one, hE] at h0
    have h23 : ((8 : ℕ) : E) = (2 : E) ^ 3 := by norm_num
    rw [h23] at h0
    exact pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp h0
  haveI : CharP E 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2E
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (fun x : E => x ^ 2) := by
    have hinj : Function.Injective (fun x : E => x ^ 2) := by
      intro x y hxy
      exact frobenius_inj E 2 (by simpa [frobenius_def] using hxy)
    exact (Finite.injective_iff_surjective).mp hinj
  set c : Eˣ := Matrix.GeneralLinearGroup.det ν with hc
  obtain ⟨a, ha⟩ := hsurj (c : E)
  have hc0 : (c : E) ≠ 0 := c.ne_zero
  have ha0 : a ≠ 0 := by
    intro h
    apply hc0
    calc (c : E) = a ^ 2 := ha.symm
      _ = 0 := by rw [h]; simp
  let lam : Eˣ := Units.mk0 a ha0
  have hlamval : (lam : E) = a := rfl
  have hlam2 : lam ^ 2 = c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hlamval]
    exact ha
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ * ν, ?_, ?_⟩
  · rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    have hdet : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ * ν) = 1 := by
      rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hc]
      rw [inv_pow, hlam2, inv_mul_cancel]
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using
      congrArg (fun u : Eˣ => (u : E)) hdet
  · intro γ
    have hcμ : Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ ∈
        Subgroup.center (GL (Fin 2) E) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨lam⁻¹, rfl⟩
    have hcomm : ∀ x : GL (Fin 2) E,
        Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ * x =
          x * Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ :=
      fun x => (Subgroup.mem_center_iff.mp hcμ x).symm
    have hmem : (Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ * ν) * γ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ * ν)⁻¹ = ν * γ * ν⁻¹ := by
      calc (Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ * ν) * γ *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ * ν)⁻¹
          = Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ * (ν * γ * ν⁻¹) *
              (Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹)⁻¹ := by group
        _ = (ν * γ * ν⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹ *
              (Matrix.GeneralLinearGroup.scalar (Fin 2) lam⁻¹)⁻¹ := by
              rw [hcomm (ν * γ * ν⁻¹)]
        _ = ν * γ * ν⁻¹ := by group
    exact hmem.symm

theorem kd2Lin_inner {K : Type} [Field K] {d r : ℕ} {D : Fin r → Type} {e : Fin r → ℕ}
    [∀ i, Field (D i)] [∀ i, Finite (D i)]
    (θ : (∀ k, GL (Fin (e k)) (D k)) →* GL (Fin d) K) (i : Fin r) (hi : e i = 2)
    (hD : Nat.card (D i) = 8) {N : GL (Fin d) K} (hN : N ∈ θ.range) :
    ∃ s ∈ ((StatedSL (e i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i)).map θ,
      ∀ g ∈ ((StatedSL (e i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i)).map θ,
        N * g * N⁻¹ = s * g * s⁻¹ := by
  obtain ⟨ν, rfl⟩ := hN
  obtain ⟨s₀, hs₀, hsconj⟩ := kd2Lin_inner_two hi hD (ν i)
  refine ⟨θ (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i s₀), ?_, ?_⟩
  · exact Subgroup.mem_map.mpr
      ⟨_, Subgroup.mem_map.mpr ⟨s₀, hs₀, rfl⟩, rfl⟩
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hw
    have hkey : ν * MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i γ * ν⁻¹ =
        MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i (s₀ * γ * s₀⁻¹) := by
      rw [ltrclh4_mulSingle_conj, hsconj γ]
    calc θ ν * θ (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i γ) * (θ ν)⁻¹
        = θ (ν * MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i γ * ν⁻¹) := by
          simp only [map_mul, map_inv]
      _ = θ (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i (s₀ * γ * s₀⁻¹)) := by
          rw [hkey]
      _ = θ (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i s₀ *
              MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i γ *
              (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i s₀)⁻¹) := by
          simp only [map_mul, map_inv]
      _ = θ (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i s₀) *
            θ (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i γ) *
            (θ (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i s₀))⁻¹ := by
          simp only [map_mul, map_inv]

theorem kd2Lin_inner_of_conj {L' P : Type} [Group L'] [Group P] (ψ₀ : L' →* P)
    (hker : ψ₀.ker ≤ Subgroup.center L') {J : Subgroup L'} {a : MulAut L'}
    {u : MulAut P} (hu : ∀ l : L', u (ψ₀ l) = ψ₀ (a l)) {t : P} (ht : t ∈ J.map ψ₀)
    (hconj : ∀ x ∈ J.map ψ₀, u x = t * x * t⁻¹) :
    ∃ y : ↥J ⧸ Subgroup.center ↥J, ∀ j j' : ↥J, a (j : L') = (j' : L') →
      (j' : ↥J ⧸ Subgroup.center ↥J) = y * (j : ↥J ⧸ Subgroup.center ↥J) * y⁻¹ := by
  obtain ⟨j₀raw, hj₀J, hj₀eq⟩ := Subgroup.mem_map.mp ht
  let j₀ : ↥J := ⟨j₀raw, hj₀J⟩
  have hj₀eq' : ψ₀ (j₀ : L') = t := hj₀eq
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥J) j₀, ?_⟩
  intro j j' hajj'
  have hψj : ψ₀ (j : L') ∈ J.map ψ₀ := Subgroup.mem_map.mpr ⟨j, j.2, rfl⟩
  have key : ψ₀ ((j₀ * j * j₀⁻¹ : ↥J) : L') = ψ₀ (j' : L') := by
    have h1 : ψ₀ (j' : L') = t * ψ₀ (j : L') * t⁻¹ := by
      rw [← hajj', ← hu, hconj _ hψj]
    rw [h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv,
      hj₀eq']
  set d' : ↥J := (j₀ * j * j₀⁻¹)⁻¹ * j' with hd'def
  have hdker : (d' : L') ∈ ψ₀.ker := by
    rw [MonoidHom.mem_ker]
    have hcoeeq : (d' : L') = ((j₀ * j * j₀⁻¹ : ↥J) : L')⁻¹ * (j' : L') := by
      rw [hd'def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoeeq, map_mul, map_inv, key, inv_mul_cancel]
  have hdcenter : d' ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker hdker) (g : L')
  have hd1 : QuotientGroup.mk' (Subgroup.center ↥J) d' = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hdcenter
  have hjeq : j' = (j₀ * j * j₀⁻¹) * d' := by
    rw [hd'def]
    group
  show QuotientGroup.mk' (Subgroup.center ↥J) j' =
    QuotientGroup.mk' (Subgroup.center ↥J) j₀ *
      QuotientGroup.mk' (Subgroup.center ↥J) j *
      (QuotientGroup.mk' (Subgroup.center ↥J) j₀)⁻¹
  rw [hjeq, map_mul, hd1, mul_one, map_mul, map_mul, map_inv]

end CFSG.StandardType.KD2Pieces1615

end
