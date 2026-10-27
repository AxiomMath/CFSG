module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeANormal
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBLift
public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly

variable {d p : ℕ} {K : Type} [Field K]

section Pow

variable {G : Type} [Group G]

theorem GGIsTransvection.pow {p : ℕ} {E : Subgroup G} (hexp : ∀ e ∈ E, e ^ p = 1)
    {ψ : MulAut ↥E} (h : GGIsTransvection p ψ) {m : ℕ} (hm : Nat.Coprime m p) :
    GGIsTransvection p (ψ ^ m) := by
  have hpow : ∀ (e : ↥E) (n : ℕ), (ψ ^ n) e = e * (e⁻¹ * ψ e) ^ n := by
    intro e n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, h.2 e, pow_succ', ← mul_assoc,
        mul_inv_cancel_left]
  have hfix : ∀ e : ↥E, (ψ ^ m) e = e ↔ ψ e = e := by
    intro e
    rw [hpow]
    constructor
    · intro he
      have h1 : (e⁻¹ * ψ e) ^ m = 1 := by
        have := congrArg (e⁻¹ * ·) he
        simpa using this
      have h2 : (e⁻¹ * ψ e) ^ p = 1 := Subtype.ext (by simpa using hexp _ (e⁻¹ * ψ e).2)
      have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rw [Nat.Coprime.gcd_eq_one hm, pow_one] at h3
      rw [← mul_inv_cancel_left e (ψ e), h3, mul_one]
    · intro he
      rw [he, inv_mul_cancel, one_pow, mul_one]
  refine ⟨?_, fun e => ?_⟩
  · rw [← h.1]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight hfix)
  · rw [hpow e m, inv_mul_cancel_left, map_pow, (hfix _).mpr (h.2 e)]

end Pow

section Coord

variable [Finite K] (hd : 0 < d) (hpd : Nat.Coprime p d)
  {X : Subgroup (MulAut (projectiveSL d K))} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
  {A₀ : GL (Fin d) K}
  (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)

include hdiag in
theorem conjMat_mul_apply {g h : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc)
    (k : Fin d) : conjMat A₀ (g * h) k k = conjMat A₀ g k k * conjMat A₀ h k k := by
  rw [conjMat_mul, mul_apply, Finset.sum_eq_single k]
  · intro l _ hlk
    rw [hdiag g hg k l (Ne.symm hlk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

include hdiag in
theorem conjMat_inv_apply {g : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc)
    (k : Fin d) : conjMat A₀ g⁻¹ k k = (conjMat A₀ g k k)⁻¹ := by
  have h1 := conjMat_mul_apply hd hpd hXc hdiag (h := g) ((slLift hd hpd X hXc).inv_mem hg) k
  rw [inv_mul_cancel, conjMat_one, one_apply_eq] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

include hdiag in
theorem eq_of_conjMat_apply {g h : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc)
    (hh : h ∈ slLift hd hpd X hXc) (he : ∀ k, conjMat A₀ g k k = conjMat A₀ h k k) : g = h := by
  apply conjMat_injective (A := A₀)
  rw [(conjMat_diag hg.1 (hdiag g hg)).1, (conjMat_diag hh.1 (hdiag h hh)).1]
  congr 1
  funext k
  exact he k

end Coord

section Transvection

variable [Finite K]

theorem ggNoTransvectionTorus_psl (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd4 : 4 ≤ d) (hpd : Nat.Coprime p d) :
    GGNoTransvectionTorus p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro Eh hEhI hEhA hr h3 a htv
  have := Fact.mk hp
  have hd : 0 < d := by omega
  have hXc : ∀ x ∈ Eh, ∀ y ∈ Eh, x * y = y * x := fun x hx y hy => TableB.IsElemAbelian.comm hEhA hx hy
  have hXp : ∀ x ∈ Eh, x ^ p = 1 := hEhA.2
  have hXI : ∀ x ∈ Eh, ∃ A : GL (Fin d) K, conjAut d K A = x := fun x hx => hEhI hx
  obtain ⟨A₀, hdiag, hle, hfull⟩ := exists_diagonalizing_slLift hp hpK hd hpd Eh hXc hXp hXI
  have hfull' := hfull (le_antisymm hle hr)
  obtain ⟨e, m, hpm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos (a : MulAut (projectiveSL d K))).ne' p hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hodd : Odd (orderOf ((a : MulAut (projectiveSL d K)) ^ m)) := by
    rw [orderOf_pow' _ hm0, hn, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp
    (CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd
      (by omega) hodd)
  have htv' : GGIsTransvection p (Eh.normalizerMonoidHom (a ^ m)) := by
    rw [map_pow]
    exact GGIsTransvection.pow (fun x hx => hEhA.2 x hx) htv
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  have hb : ((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
      MulAut (projectiveSL d K)) = conjAut d K A * fieldAut d K σ := by
    rw [Subgroup.coe_pow, hAσ]
  have hN : ∀ x ∈ Eh, conjAut d K A * fieldAut d K σ * x * (conjAut d K A * fieldAut d K σ)⁻¹ ∈
      Eh := by
    intro x hx
    rw [← hb]
    exact (Subgroup.mem_normalizer_iff.mp (a ^ m).2 x).mp hx
  obtain ⟨π, -, hform⟩ := semilinear_normal_form hd hpd hXc hp hp2 hpK hXp hXI hdiag hfull' A σ hN
  set Y := slLift hd hpd Eh hXc with hY
  have himg : ∀ g ∈ Y, ∃ g₁ ∈ Y, conjAut d K (SpecialLinearGroup.toGL g₁) =
      conjAut d K A * fieldAut d K σ * conjAut d K (SpecialLinearGroup.toGL g) *
        (conjAut d K A * fieldAut d K σ)⁻¹ ∧
      ∀ l, conjMat A₀ g₁ l l = σ (conjMat A₀ g (π l) (π l)) := by
    intro g hg
    obtain ⟨g₁, hg₁, hgg₁⟩ := exists_mem_slLift_of_mem hd hpd hXc hXp hXI (hN _ hg.2)
    exact ⟨g₁, hg₁, hgg₁, hform g hg g₁ hg₁ hgg₁⟩
  have hident : ∀ g ∈ Y, ∀ g₁ ∈ Y, ∀ g₂ ∈ Y,
      conjAut d K (SpecialLinearGroup.toGL g₁) =
        conjAut d K A * fieldAut d K σ * conjAut d K (SpecialLinearGroup.toGL g) *
          (conjAut d K A * fieldAut d K σ)⁻¹ →
      conjAut d K (SpecialLinearGroup.toGL g₂) =
        conjAut d K A * fieldAut d K σ * conjAut d K (SpecialLinearGroup.toGL g₁) *
          (conjAut d K A * fieldAut d K σ)⁻¹ →
      ∀ l, conjMat A₀ g₂ l l = conjMat A₀ g₁ l l * (conjMat A₀ g l l)⁻¹ * conjMat A₀ g₁ l l := by
    intro g hg g₁ hg₁ g₂ hg₂ h1 h2 l
    have hid : ((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
        MulAut (projectiveSL d K)) * ((conjAut d K (SpecialLinearGroup.toGL g))⁻¹ *
          (((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
            MulAut (projectiveSL d K)) * conjAut d K (SpecialLinearGroup.toGL g) *
          (((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
            MulAut (projectiveSL d K)))⁻¹)) *
        (((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
          MulAut (projectiveSL d K)))⁻¹ =
        (conjAut d K (SpecialLinearGroup.toGL g))⁻¹ *
          (((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
            MulAut (projectiveSL d K)) * conjAut d K (SpecialLinearGroup.toGL g) *
          (((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
            MulAut (projectiveSL d K)))⁻¹) :=
      congrArg Subtype.val (htv'.2 ⟨conjAut d K (SpecialLinearGroup.toGL g), hg.2⟩)
    rw [hb, ← h1] at hid
    have h4 : conjAut d K A * fieldAut d K σ * ((conjAut d K (SpecialLinearGroup.toGL g))⁻¹ *
        conjAut d K (SpecialLinearGroup.toGL g₁)) * (conjAut d K A * fieldAut d K σ)⁻¹ =
        (conjAut d K A * fieldAut d K σ * conjAut d K (SpecialLinearGroup.toGL g) *
          (conjAut d K A * fieldAut d K σ)⁻¹)⁻¹ *
        (conjAut d K A * fieldAut d K σ * conjAut d K (SpecialLinearGroup.toGL g₁) *
          (conjAut d K A * fieldAut d K σ)⁻¹) := by group
    rw [h4, ← h1, ← h2] at hid
    have h3 : conjAut d K (SpecialLinearGroup.toGL g₂) =
        conjAut d K (SpecialLinearGroup.toGL (g₁ * g⁻¹ * g₁)) := by
      simp only [map_mul, map_inv]
      calc conjAut d K (SpecialLinearGroup.toGL g₂) =
            conjAut d K (SpecialLinearGroup.toGL g₁) * ((conjAut d K (SpecialLinearGroup.toGL g₁))⁻¹ *
              conjAut d K (SpecialLinearGroup.toGL g₂)) := by group
        _ = conjAut d K (SpecialLinearGroup.toGL g₁) * ((conjAut d K (SpecialLinearGroup.toGL g))⁻¹ *
              conjAut d K (SpecialLinearGroup.toGL g₁)) := by rw [hid]
        _ = _ := by group
    have hmem1 : g₁ * g⁻¹ ∈ Y := Y.mul_mem hg₁ (Y.inv_mem hg)
    have h5 : g₂ = g₁ * g⁻¹ * g₁ := eq_of_slLift hd hpd hg₂.1 (Y.mul_mem hmem1 hg₁).1 h3
    rw [h5, conjMat_mul_apply hd hpd hXc hdiag hmem1, conjMat_mul_apply hd hpd hXc hdiag hg₁,
      conjMat_inv_apply hd hpd hXc hdiag hg]
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hσζ : IsPrimitiveRoot (σ ζ) p := hζ.map_of_injective σ.injective
  have hsq : ∀ y : K, IsPrimitiveRoot y p → y * y ≠ 1 := by
    intro y hy h
    rw [← pow_two] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((hy.pow_eq_one_iff_dvd 2).mp h))
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  by_cases hπ : π = 1
  ·
    subst hπ
    have hd2 : 1 < d := by omega
    obtain ⟨i, hi⟩ : ∃ i : Fin d, i = ⟨0, hd⟩ := ⟨_, rfl⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin d, j = ⟨1, hd2⟩ := ⟨_, rfl⟩
    have hij : i ≠ j := by rw [hi, hj]; simp [Fin.ext_iff]
    obtain ⟨g, hg, hgt⟩ := hfull' (rootT ζ i j) (rootT_pow hζ.pow_eq_one i j)
      (prod_rootT hζ0 hij)
    obtain ⟨g₁, hg₁, h1, hT1⟩ := himg g hg
    obtain ⟨g₂, hg₂, h2, hT2⟩ := himg g₁ hg₁
    have hc := hident g hg g₁ hg₁ g₂ hg₂ h1 h2 i
    have hTg : ∀ l, conjMat A₀ g l l = rootT ζ i j l := fun l => by rw [hgt, diagonal_apply_eq]
    simp only [hT2, hT1, hTg, Equiv.Perm.one_apply, rootT_left] at hc
    have hfix : σ ζ = ζ := by
      by_contra hne
      have hσζ0 : σ ζ ≠ 0 := hσζ.ne_zero hp.ne_zero
      have hy1 : ζ⁻¹ * σ ζ ≠ 1 := fun h => hne ((inv_mul_eq_one₀ hζ0).mp h).symm
      have hyp : (ζ⁻¹ * σ ζ) ^ p = 1 := by
        rw [mul_pow, inv_pow, hζ.pow_eq_one, hσζ.pow_eq_one, inv_one, one_mul]
      have hσy : σ (ζ⁻¹ * σ ζ) = ζ⁻¹ * σ ζ := by
        rw [map_mul, map_inv₀, hc, mul_assoc, inv_mul_cancel_left₀ hσζ0]
      have hyprim : IsPrimitiveRoot (ζ⁻¹ * σ ζ) p :=
        IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hyp hy1)
      obtain ⟨k, -, hk⟩ := hyprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
      apply hne
      rw [← hk, map_pow, hσy]
    have hall : ∀ x : ↥Eh, Eh.normalizerMonoidHom (a ^ m) x = x := by
      intro x
      obtain ⟨g, hg, hgx⟩ := exists_mem_slLift_of_mem hd hpd hXc hXp hXI x.2
      obtain ⟨g₁, hg₁, h1, hT1⟩ := himg g hg
      have hgg : g₁ = g := eq_of_conjMat_apply hd hpd hXc hdiag hg₁ hg fun l => by
        rw [hT1, Equiv.Perm.one_apply]
        obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one ((conjMat_diag hg.1 (hdiag g hg)).2.1 l)
        rw [← hk, map_pow, hfix]
      apply Subtype.ext
      change ((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
          MulAut (projectiveSL d K)) * (x : MulAut (projectiveSL d K)) *
        (((a ^ m : Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K)))) :
          MulAut (projectiveSL d K)))⁻¹ = x
      rw [hb, ← hgx, ← h1, hgg]
    have hcard := htv'.1
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall)] at hcard
    have hpos : 0 < Nat.card Eh := lt_of_lt_of_le (pow_pos hp.pos 3) h3
    nlinarith [hp.two_le]
  ·
    obtain ⟨k, hk⟩ : ∃ k, π k ≠ k := by
      by_contra h
      push Not at h
      exact hπ (Equiv.Perm.ext h)
    obtain ⟨i, hi⟩ : ∃ i, i = π k := ⟨_, rfl⟩
    have hik : i ≠ k := hi ▸ hk
    have hπi : π i ≠ i := fun h => hik (π.injective (h.trans hi))
    obtain ⟨j, hji, hjk, hjπ⟩ : ∃ j : Fin d, j ≠ i ∧ j ≠ k ∧ j ≠ π i := by
      classical
      by_contra hne
      push Not at hne
      have hsub : (Finset.univ : Finset (Fin d)) ⊆ {i, k, π i} := fun j _ => by
        by_cases h1 : j = i
        · simp [h1]
        by_cases h2 : j = k
        · simp [h2]
        simp [hne j h1 h2]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at h1
      have h2 := Finset.card_le_three (a := i) (b := k) (c := π i)
      omega
    obtain ⟨g, hg, hgt⟩ := hfull' (rootT ζ i j) (rootT_pow hζ.pow_eq_one i j)
      (prod_rootT hζ0 (Ne.symm hji))
    obtain ⟨g₁, hg₁, h1, hT1⟩ := himg g hg
    obtain ⟨g₂, hg₂, h2, hT2⟩ := himg g₁ hg₁
    have hc := hident g hg g₁ hg₁ g₂ hg₂ h1 h2 k
    have hTg : ∀ l, conjMat A₀ g l l = rootT ζ i j l := fun l => by rw [hgt, diagonal_apply_eq]
    simp only [hT2, hT1, hTg, ← hi, rootT_left, rootT_other ζ hπi (Ne.symm hjπ),
      rootT_other ζ (Ne.symm hik) (Ne.symm hjk), map_one, inv_one, mul_one] at hc
    exact hsq (σ ζ) hσζ hc.symm

end Transvection

omit [Field K] in
theorem ggCenterCoprime_psl {K : Type} [Field K] (hp : p.Prime) (hpd : Nat.Coprime p d)
    (hsec : SLHasSections d K) : GGCenterCoprime p (projectiveSL d K) := by
  intro L' _ _ ψ hψ hker hperf hdvd
  have := Fact.mk hp
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ψ.ker) p hdvd
  obtain ⟨s, hs⟩ := hφs (z : L')
  have hs1 : proj d K s = 1 := by
    rw [← hφ, hs]
    exact z.2
  obtain ⟨c, hcd, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hs1)
  have hsd : s ^ d = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow, ← Units.val_pow_eq_pow_val, hcd,
      Units.val_one, map_one]
    rfl
  have hzd : z ^ d = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hs, ← map_pow, hsd, map_one]
    rfl
  have h1 := orderOf_dvd_of_pow_eq_one hzd
  rw [hz] at h1
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hpd h1)

section Line

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem det_permMatrix_char_two (τ : Equiv.Perm (Fin d)) : (τ.permMatrix K).det = 1 := by
  rw [det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h, CharTwo.neg_eq]

omit [Finite K] [CharP K 2] in
theorem permMatrix_mul_diagonal (τ : Equiv.Perm (Fin d)) (t : Fin d → K) :
    τ.permMatrix K * diagonal t = diagonal (t ∘ τ) * τ.permMatrix K := by
  ext i j
  simp only [mul_diagonal, diagonal_mul, Function.comp_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  split_ifs with h
  · rw [h, one_mul, mul_one]
  · rw [zero_mul, mul_zero]

omit [Finite K] in
@[expose] def permConj (A₀ : GL (Fin d) K) (τ : Equiv.Perm (Fin d)) :
    SpecialLinearGroup (Fin d) K :=
  ⟨((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * τ.permMatrix K *
      (A₀ : Matrix (Fin d) (Fin d) K), by
    rw [det_mul, det_mul, det_permMatrix_char_two, mul_one, ← det_mul, inv_mul_GL, det_one]⟩

omit [Finite K] in
theorem conjMat_permConj (A₀ : GL (Fin d) K) (τ : Equiv.Perm (Fin d)) :
    conjMat A₀ (permConj A₀ τ) = τ.permMatrix K := by
  change (A₀ : Matrix (Fin d) (Fin d) K) * (((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      τ.permMatrix K * (A₀ : Matrix (Fin d) (Fin d) K)) *
    ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_inv_GL, Matrix.one_mul, Matrix.mul_assoc,
    mul_inv_GL, Matrix.mul_one]

theorem ggNoInvariantLineTorus_psl (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd3 : 3 ≤ d)
    (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) :
    GGNoInvariantLineTorus p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro Eh hEhI hEhA hr _
  refine ⟨ggCenterCoprime_psl hp hpd hsec, fun Λ hΛ hΛp => ?_⟩
  have := Fact.mk hp
  have hd : 0 < d := by omega
  have hXc : ∀ x ∈ Eh, ∀ y ∈ Eh, x * y = y * x := fun x hx y hy =>
    TableB.IsElemAbelian.comm hEhA hx hy
  have hXp : ∀ x ∈ Eh, x ^ p = 1 := hEhA.2
  have hXI : ∀ x ∈ Eh, ∃ A : GL (Fin d) K, conjAut d K A = x := fun x hx => hEhI hx
  obtain ⟨A₀, hdiag, hle, hfull⟩ := exists_diagonalizing_slLift hp hpK hd hpd Eh hXc hXp hXI
  have hfull' := hfull (le_antisymm hle hr)
  set Y := slLift hd hpd Eh hXc with hY
  have hperm : ∀ (τ : Equiv.Perm (Fin d)) (g : SpecialLinearGroup (Fin d) K), g ∈ Y →
      permConj A₀ τ * g * (permConj A₀ τ)⁻¹ ∈ Y ∧
        ∀ l, conjMat A₀ (permConj A₀ τ * g * (permConj A₀ τ)⁻¹) l l =
          conjMat A₀ g (τ l) (τ l) := by
    intro τ g hg
    obtain ⟨t, ht⟩ : ∃ t : Fin d → K, t = fun l => conjMat A₀ g l l := ⟨_, rfl⟩
    have hgd := conjMat_diag hg.1 (hdiag g hg)
    have hgt : conjMat A₀ g = diagonal t := ht ▸ hgd.1
    have hMN : conjMat A₀ (permConj A₀ τ) * conjMat A₀ (permConj A₀ τ)⁻¹ = 1 := by
      rw [← conjMat_mul, mul_inv_cancel, conjMat_one]
    have hc : conjMat A₀ (permConj A₀ τ * g * (permConj A₀ τ)⁻¹) = diagonal (t ∘ τ) := by
      rw [conjMat_mul, conjMat_mul, hgt, conjMat_permConj, permMatrix_mul_diagonal,
        Matrix.mul_assoc, ← conjMat_permConj A₀ τ, hMN, Matrix.mul_one]
    obtain ⟨g'', hg'', hg''t⟩ := hfull' (t ∘ τ) (fun l => by rw [ht]; exact hgd.2.1 (τ l))
      (by simp only [Function.comp_apply]; rw [Equiv.prod_comp τ t, ht]; exact hgd.2.2)
    have heq : permConj A₀ τ * g * (permConj A₀ τ)⁻¹ = g'' :=
      conjMat_injective (A := A₀) (hc.trans hg''t.symm)
    refine ⟨heq ▸ hg'', fun l => ?_⟩
    rw [hc, hgt, diagonal_apply_eq, diagonal_apply_eq]
    rfl
  have hcw : ∀ (τ : Equiv.Perm (Fin d)) (g : SpecialLinearGroup (Fin d) K),
      MulAut.conj (MulAut.conj (proj d K (permConj A₀ τ)))
          (conjAut d K (SpecialLinearGroup.toGL g)) =
        conjAut d K (SpecialLinearGroup.toGL (permConj A₀ τ * g * (permConj A₀ τ)⁻¹)) := by
    intro τ g
    rw [MulAut.conj_apply, ← conjAut_toGL]
    simp only [map_mul, map_inv]
  have hnorm : ∀ τ : Equiv.Perm (Fin d), MulAut.conj (proj d K (permConj A₀ τ)) ∈
      Subgroup.normalizer (Eh : Set (MulAut (projectiveSL d K))) := by
    intro τ
    rw [mem_normalizer_iff_map_conj]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      obtain ⟨g, hg, rfl⟩ := exists_mem_slLift_of_mem hd hpd hXc hXp hXI he
      change MulAut.conj (MulAut.conj (proj d K (permConj A₀ τ)))
        (conjAut d K (SpecialLinearGroup.toGL g)) ∈ Eh
      rw [hcw]
      exact (hperm τ g hg).1.2
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  by_contra hcon
  push Not at hcon
  obtain ⟨e₀, he₀Λ, he₀1⟩ : ∃ e₀ ∈ Λ, e₀ ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one Λ with h | h
    · rw [h, Subgroup.card_bot] at hΛp
      exact absurd hΛp.symm hp.one_lt.ne'
    · exact h
  have hΛz : Λ = Subgroup.zpowers e₀ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr he₀Λ)
    rw [hΛp, Nat.card_zpowers, orderOf_eq_prime (hXp e₀ (hΛ he₀Λ)) he₀1]
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_mem_slLift_of_mem hd hpd hXc hXp hXI (hΛ he₀Λ)
  obtain ⟨t, ht⟩ : ∃ t : Fin d → K, t = fun l => conjMat A₀ g₀ l l := ⟨_, rfl⟩
  have hg₀d := conjMat_diag hg₀.1 (hdiag g₀ hg₀)
  have htp : ∀ l, t l ^ p = 1 := fun l => by rw [ht]; exact hg₀d.2.1 l
  have htprod : ∏ l, t l = 1 := by rw [ht]; exact hg₀d.2.2
  have hpow_coord : ∀ (k : ℕ) (l : Fin d), conjMat A₀ (g₀ ^ k) l l = t l ^ k := by
    intro k l
    rw [conjMat_pow, hg₀d.1, diagonal_pow, diagonal_apply_eq, Pi.pow_apply, ht]
  have hswap : ∀ a b : Fin d, ∃ k : ℕ, ∀ l, t (Equiv.swap a b l) = t l ^ k := by
    intro a b
    have h1 := hcon (proj d K (permConj A₀ (Equiv.swap a b))) (hnorm _) e₀ he₀Λ
    rw [hΛz] at h1
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr h1
    have hk' : e₀ ^ k = MulAut.conj (proj d K (permConj A₀ (Equiv.swap a b))) * e₀ *
        (MulAut.conj (proj d K (permConj A₀ (Equiv.swap a b))))⁻¹ := hk
    refine ⟨k, fun l => ?_⟩
    have h2 : g₀ ^ k = permConj A₀ (Equiv.swap a b) * g₀ * (permConj A₀ (Equiv.swap a b))⁻¹ := by
      apply eq_of_slLift hd hpd (by rw [← pow_mul, mul_comm, pow_mul, hg₀.1, one_pow])
        (hperm _ g₀ hg₀).1.1
      rw [map_pow, map_pow, hg₀e, hk', ← hcw, hg₀e, MulAut.conj_apply]
    rw [← hpow_coord k l, h2, (hperm _ g₀ hg₀).2 l, ht]
  have hconst : ∀ c, t c ≠ 1 → ∀ a b, a ≠ c → b ≠ c → t a = t b := by
    intro c hc a b hac hbc
    obtain ⟨k, hk⟩ := hswap a b
    have hcprim : IsPrimitiveRoot (t c) p :=
      IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (htp c) hc)
    have h1 : t c ^ k = t c := by
      rw [← hk c, Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
    have hpw : ∀ l, t l ^ k = t l := by
      intro l
      obtain ⟨j, -, hj⟩ := hcprim.eq_pow_of_pow_eq_one (htp l)
      rw [← hj, ← pow_mul, mul_comm, pow_mul, h1]
    have h3 := hk a
    rw [Equiv.swap_apply_left, hpw] at h3
    exact h3.symm
  have hg₀1 : g₀ ≠ 1 := by
    rintro rfl
    apply he₀1
    rw [← hg₀e, map_one, map_one]
  obtain ⟨c, hc⟩ : ∃ c, t c ≠ 1 := by
    by_contra h
    push Not at h
    apply hg₀1
    refine eq_of_conjMat_apply hd hpd hXc hdiag hg₀ (slLift hd hpd Eh hXc).one_mem fun l => ?_
    rw [conjMat_one, one_apply_eq]
    have := h l
    rw [ht] at this
    exact this
  obtain ⟨c', hc'c, hc'⟩ : ∃ c', c' ≠ c ∧ t c' ≠ 1 := by
    by_contra h
    push Not at h
    apply hc
    rw [← htprod, Finset.prod_eq_single c (fun l _ hl => h l hl)
      (fun h' => absurd (Finset.mem_univ c) h')]
  obtain ⟨e, hec, hec'⟩ : ∃ e : Fin d, e ≠ c ∧ e ≠ c' := by
    classical
    by_contra hne
    push Not at hne
    have hsub : (Finset.univ : Finset (Fin d)) ⊆ {c, c'} := fun j _ => by
      by_cases h1 : j = c
      · simp [h1]
      · simp [hne j h1]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Finset.card_le_two (a := c) (b := c')
    omega
  have hall : ∀ l, t l = t e := by
    intro l
    by_cases hlc : l = c
    · rw [hlc]
      exact hconst c' hc' c e (Ne.symm hc'c) hec'
    · exact hconst c hc l e hlc hec
  have hbd : t e ^ d = 1 := by
    rw [← htprod, Finset.prod_congr rfl (fun l _ => hall l), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hb1 : t e = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨htp e, hbd⟩
    rwa [Nat.Coprime.gcd_eq_one hpd, pow_one] at h
  exact hc (by rw [hall c, hb1])

end Line

section InnerDiag

omit [Field K] in
theorem mem_unitriangular_diag_conj {K : Type} [Field K] (P : GL (Fin d) K)
    (hP : (P : Matrix (Fin d) (Fin d) K) = diagonal (fun i => (P : Matrix (Fin d) (Fin d) K) i i))
    (σ : K ≃+* K) {v : SpecialLinearGroup (Fin d) K} (hv : v ∈ unitriangular d K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K P
      (SpecialLinearGroup.map σ.toRingHom v) ∈ unitriangular d K := by
  have h1 : ∀ u : Fin d → K, (P : Matrix (Fin d) (Fin d) K) * diagonal u =
      diagonal u * (P : Matrix (Fin d) (Fin d) K) := by
    intro u
    rw [hP, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hPinv : ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun i => ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) := by
    apply eq_diagonal_of_commute_diagonal
    intro u
    have e1 : ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (diagonal u * (P : Matrix (Fin d) (Fin d) K)) *
          ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal u := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_inv_GL, Matrix.mul_one]
    have e2 : ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((P : Matrix (Fin d) (Fin d) K) * diagonal u) *
          ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal u * ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      rw [← Matrix.mul_assoc, inv_mul_GL, Matrix.one_mul]
    rw [← e1, ← h1, e2]
  have hpq : ∀ i, (P : Matrix (Fin d) (Fin d) K) i i *
      ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
    intro i
    have h2 : ((P : Matrix (Fin d) (Fin d) K) * ((P⁻¹ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)) i i = 1 := by rw [mul_inv_GL, one_apply_eq]
    rwa [hP, hPinv, diagonal_mul_diagonal, diagonal_apply_eq] at h2
  rw [mem_unitriangular] at hv ⊢
  have hent : ∀ i j, ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K
      P (SpecialLinearGroup.map σ.toRingHom v) : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) i j =
      (P : Matrix (Fin d) (Fin d) K) i i * σ ((v : Matrix (Fin d) (Fin d) K) i j) *
        ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) j j := by
    intro i j
    obtain ⟨pv, hpv⟩ : ∃ pv : Fin d → K, pv = fun i => (P : Matrix (Fin d) (Fin d) K) i i :=
      ⟨_, rfl⟩
    obtain ⟨qv, hqv⟩ : ∃ qv : Fin d → K,
        qv = fun i => ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i := ⟨_, rfl⟩
    have hP' : (P : Matrix (Fin d) (Fin d) K) = diagonal pv := by rw [hpv]; exact hP
    have hPinv' : ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal qv := by
      rw [hqv]; exact hPinv
    rw [coe_slConjugation, SpecialLinearGroup.map_apply_coe, hP', hPinv', mul_diagonal,
      diagonal_mul, RingHom.mapMatrix_apply, Matrix.map_apply, diagonal_apply_eq,
      diagonal_apply_eq]
    rfl
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [hent, hv.1 i j hji, map_zero, mul_zero, zero_mul]
  · rw [hent, hv.2 i, map_one, mul_one, hpq]

omit [Field K] in
theorem transvection_mem_unitriangular {K : Type} [Field K] (hd : 2 ≤ d) :
    SpecialLinearGroup.transvection (show (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ by simp) (1 : K) ∈
      unitriangular d K := by
  rw [mem_unitriangular]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hji).symm,
      Matrix.single_apply, zero_add]
    split_ifs with h
    · exfalso
      obtain ⟨h2, h3⟩ := h
      rw [← h2, ← h3] at hji
      simp [Fin.lt_def] at hji
    · rfl
  · rw [CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.single_apply]
    split_ifs with h
    · exfalso
      obtain ⟨h2, h3⟩ := h
      rw [← h3] at h2
      simp [Fin.ext_iff] at h2
    · rw [add_zero]

omit [Field K] in
theorem unitriangular_conj_two {K : Type} [Field K] [Finite K] [CharP K 2] (hd : 2 ≤ d)
    (A₀ : GL (Fin d) K) :
    (projUnitriangular d K).map (conjAut d K A₀⁻¹).toMonoidHom ≠ ⊥ ∧
      IsPGroup 2 ((projUnitriangular d K).map (conjAut d K A₀⁻¹).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_⟩
  · intro hbot
    have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
    have hmem : (conjAut d K A₀⁻¹).toMonoidHom (proj d K (SpecialLinearGroup.transvection h01 1)) ∈
        (projUnitriangular d K).map (conjAut d K A₀⁻¹).toMonoidHom :=
      ⟨_, ⟨_, transvection_mem_unitriangular hd, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : proj d K (SpecialLinearGroup.transvection h01 (1 : K)) = 1 :=
      (conjAut d K A₀⁻¹).injective (hmem.trans (map_one _).symm)
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h1)
    have h2 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, by omega⟩ ⟨1, by omega⟩) hc
    simp [CFSG.LinearGroups.coe_transvection] at h2
  · obtain ⟨P2, hP2⟩ := exists_sylow_unitriangular (K := K) 2 (n := d) (by omega)
    have h2 : IsPGroup 2 (unitriangular d K) := hP2 ▸ P2.isPGroup'
    exact (h2.map (proj d K)).map _

variable [Finite K] [CharP K 2]

theorem ggInnerDiagBound_psl (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd3 : 3 ≤ d) (hpd : Nat.Coprime p d) :
    GGInnerDiagBound p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro Eb Eh hEbI hEbA hr _ hle hEhA _ _
  have := Fact.mk hp
  have hd : 0 < d := by omega
  have hXc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x := fun x hx y hy =>
    TableB.IsElemAbelian.comm hEbA hx hy
  have hXp : ∀ x ∈ Eb, x ^ p = 1 := hEbA.2
  have hXI : ∀ x ∈ Eb, ∃ A : GL (Fin d) K, conjAut d K A = x := fun x hx => hEbI hx
  obtain ⟨A₀, hdiag, hle', hfull⟩ := exists_diagonalizing_slLift hp hpK hd hpd Eb hXc hXp hXI
  have hfull' := hfull (le_antisymm hle' hr)
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  obtain ⟨hU, hU2⟩ := unitriangular_conj_two (K := K) (by omega) A₀
  refine ⟨_, hU, hU2, fun φ hφ u hu => ?_⟩
  have hodd : Odd (orderOf φ) := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hEhA.2 φ hφ)) with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hp.odd_of_ne_two hp2
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp
    (CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd
      (by omega) hodd)
  have hcomm : ∀ x ∈ Eb, conjAut d K A * fieldAut d K σ * x *
      (conjAut d K A * fieldAut d K σ)⁻¹ = x := by
    intro x hx
    rw [TableB.IsElemAbelian.comm hEhA hφ (hle hx), mul_inv_cancel_right]
  have hN : ∀ x ∈ Eb, conjAut d K A * fieldAut d K σ * x *
      (conjAut d K A * fieldAut d K σ)⁻¹ ∈ Eb := fun x hx => by rw [hcomm x hx]; exact hx
  obtain ⟨π, hπP, hform⟩ := semilinear_normal_form hd hpd hXc hp hp2 hpK hXp hXI hdiag hfull' A σ hN
  have hπ : π = 1 := by
    by_contra hπ
    obtain ⟨k, hk⟩ : ∃ k, π k ≠ k := by
      by_contra h
      push Not at h
      exact hπ (Equiv.Perm.ext h)
    obtain ⟨j, hjk, hjπ⟩ : ∃ j : Fin d, j ≠ k ∧ j ≠ π k := by
      classical
      by_contra hne
      push Not at hne
      have hsub : (Finset.univ : Finset (Fin d)) ⊆ {k, π k} := fun j _ => by
        by_cases h1 : j = k
        · simp [h1]
        · simp [hne j h1]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at h1
      have h2 := Finset.card_le_two (a := k) (b := π k)
      omega
    obtain ⟨g, hg, hgt⟩ := hfull' (rootT ζ k j) (rootT_pow hζ.pow_eq_one k j)
      (prod_rootT (hζ.ne_zero hp.ne_zero) (Ne.symm hjk))
    have h1 := hform g hg g hg (hcomm _ hg.2).symm k
    rw [hgt, diagonal_apply_eq, diagonal_apply_eq, rootT_left, rootT_other ζ hk (Ne.symm hjπ),
      map_one] at h1
    exact hζ.ne_one hp.one_lt h1
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin d) K,
      P = A₀ * A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹ := ⟨_, rfl⟩
  rw [← hP] at hπP
  have hPd : (P : Matrix (Fin d) (Fin d) K) =
      diagonal (fun i => (P : Matrix (Fin d) (Fin d) K) i i) := by
    apply eq_diagonal_of_commute_diagonal
    intro u
    have := hπP u
    rwa [hπ, Equiv.Perm.coe_one, Function.comp_id] at this
  have htrans := standard_automorphism_transport (K := K) (n := d)
  have hkey : conjAut d K A₀⁻¹ * (conjAut d K P * fieldAut d K σ) =
      conjAut d K A * fieldAut d K σ * conjAut d K A₀⁻¹ := by
    have e1 : conjAut d K A * fieldAut d K σ * conjAut d K A₀⁻¹ =
        conjAut d K (A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹) * fieldAut d K σ := by
      calc conjAut d K A * fieldAut d K σ * conjAut d K A₀⁻¹ =
            conjAut d K A * (fieldAut d K σ * conjAut d K A₀⁻¹ * (fieldAut d K σ)⁻¹) *
              fieldAut d K σ := by group
        _ = _ := by rw [htrans.2.2.1 σ A₀⁻¹, map_mul]
    have e2 : conjAut d K A₀⁻¹ * (conjAut d K P * fieldAut d K σ) =
        conjAut d K (A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹) * fieldAut d K σ := by
      rw [← mul_assoc, ← map_mul, hP]
      congr 2
      group
    rw [e1, e2]
  obtain ⟨y, hy, rfl⟩ := hu
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨proj d K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K P
    (SpecialLinearGroup.map σ.toRingHom v)), ⟨_, mem_unitriangular_diag_conj P hPd σ hv, rfl⟩, ?_⟩
  change (conjAut d K A₀⁻¹) (proj d K _) =
    (conjAut d K A * fieldAut d K σ) ((conjAut d K A₀⁻¹) (proj d K v))
  rw [← conjAut_proj, ← fieldAut_proj]
  have := congrArg (fun F : MulAut (projectiveSL d K) => F (proj d K v)) hkey
  simpa only [MulAut.mul_apply] using this

end InnerDiag

end CFSG.StandardType.TypeA
