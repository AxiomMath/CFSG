module

public import CFSG.RankThree.PartOne.U5K.Kf.Lift
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveDiagonalize
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

@[expose] def scalarU (c : Kˣ) (hc : c ^ (2 ^ f + 1) = 1) :
    primeFormUnitary h (idGram K 5) :=
  ⟨GeneralLinearGroup.scalar (Fin 5) c, by
    simp only [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, idGram,
      Units.val_one, Matrix.mul_one]
    rw [diagonal_map (by simp), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext s
    have := congrArg Units.val hc
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at this
    rw [UnitaryFieldData.bar_apply]
    exact this⟩

theorem scalarU_coe (c : Kˣ) (hc : c ^ (2 ^ f + 1) = 1) :
    ((scalarU (h := h) c hc : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) c := rfl

theorem det_norm_one (x : primeFormUnitary h (idGram K 5)) :
    h.bar (((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det) *
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  have hm := mem_primeFormUnitary.1 x.2
  have := congrArg Matrix.det hm
  simp only [idGram, Units.val_one, Matrix.mul_one, det_mul, det_transpose, det_one] at this
  rw [← this]
  congr 1
  have := RingHom.map_det h.bar ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  rw [this]
  rfl

theorem det_scalar_eq (κ : Kˣ) :
    Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 5) κ) = κ ^ 5 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, det_diagonal]
  simp

theorem ZetaData.exists_scalar_pow_eq_one (Z : ZetaData h p) (hp5 : p ≠ 5)
    (x : primeFormUnitary h (idGram K 5)) (hx : primeFormConjHom h (idGram K 5) x ^ p = 1) :
    ∃ c : primeFormUnitary h (idGram K 5), c ∈ idScalarKernel h 5 ∧ (c * x) ^ p = 1 := by
  have hxp : x ^ p ∈ idScalarKernel h 5 := by
    rw [← Z.conj_eq_one_iff, map_pow]
    exact hx
  obtain ⟨κ, hκq, hκ⟩ := hxp
  set dU : Kˣ := Matrix.GeneralLinearGroup.det (x : GL (Fin 5) K) with hdU
  have hdκ : dU ^ p = κ ^ 5 := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hκ
    rw [← det_scalar_eq]
    rw [← h1, hdU, ← map_pow]
    rfl
  have hdq : dU ^ (2 ^ f + 1) = 1 := by
    apply Units.ext
    have := det_norm_one x
    rw [UnitaryFieldData.bar_apply] at this
    simpa [hdU, Matrix.GeneralLinearGroup.val_det_apply, pow_succ] using this
  have hcop : IsCoprime (5 : ℤ) (p : ℤ) := by
    have : Nat.Coprime 5 p := (Nat.coprime_primes (by norm_num) (Fact.out : p.Prime)).2
      (Ne.symm hp5)
    exact Nat.isCoprime_iff_coprime.2 this
  obtain ⟨u, v, huv⟩ := hcop
  set e : Kˣ := dU ^ u * κ ^ v with he
  have hep : e ^ p = κ := by
    have h1 : (dU ^ u) ^ p = (κ ^ 5) ^ u := by
      rw [← _root_.zpow_natCast, _root_.zpow_comm, _root_.zpow_natCast, hdκ]
    have h2 : (κ ^ v) ^ p = (κ ^ p) ^ v := by
      rw [← _root_.zpow_natCast, _root_.zpow_comm, _root_.zpow_natCast]
    rw [he, mul_pow, h1, h2, ← _root_.zpow_natCast κ 5, ← _root_.zpow_natCast κ p,
      ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add]
    have : ((5 : ℕ) : ℤ) * u + ((p : ℕ) : ℤ) * v = 1 := by push_cast; linarith
    rw [this, _root_.zpow_one]
  have hc : ∀ (g : Kˣ) (m : ℤ) (n : ℕ), (g ^ m) ^ n = (g ^ n) ^ m := by
    intro g m n
    rw [← _root_.zpow_natCast, _root_.zpow_comm, _root_.zpow_natCast]
  have hq' : e⁻¹ ^ (2 ^ f + 1) = 1 := by
    have h1 : e ^ (2 ^ f + 1) = 1 := by
      rw [he, mul_pow, hc, hc, hdq, hκq]
      simp
    rw [inv_pow, h1, inv_one]
  refine ⟨scalarU (h := h) e⁻¹ hq', ⟨e⁻¹, hq', rfl⟩, ?_⟩
  apply Subtype.ext
  have hxp' : (x : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) κ := by
    simpa using hκ
  have hcomm : Commute (GeneralLinearGroup.scalar (Fin 5) e⁻¹ : GL (Fin 5) K) (x : GL (Fin 5) K) :=
    (commute_scalar e⁻¹ (x : GL (Fin 5) K)).symm
  rw [Subgroup.coe_pow, Subgroup.coe_mul, scalarU_coe, hcomm.mul_pow, hxp', ← map_pow, ← map_mul,
    inv_pow, hep, inv_mul_cancel, map_one]
  rfl

theorem commute_of_mem_idScalarKernel {A : primeFormUnitary h (idGram K 5)}
    (hA : A ∈ idScalarKernel h 5) (g : primeFormUnitary h (idGram K 5)) : A * g = g * A := by
  obtain ⟨c, -, hc⟩ := hA
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact ((commute_scalar c _).eq).symm

theorem isDiag_of_scalar_mul {A B : primeFormUnitary h (idGram K 5)}
    (hA : A ∈ idScalarKernel h 5)
    (hB : (((B : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K).IsDiag) :
    (((A * B : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K).IsDiag := by
  obtain ⟨c, -, hc⟩ := hA
  rw [Subgroup.coe_mul, Units.val_mul, hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  intro i j hij
  rw [Matrix.diagonal_mul, hB hij, mul_zero]

theorem ZetaData.exists_diagonalizing (Z : ZetaData h p)
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))} (hel : IsElementaryAbelian p ↥Ab)
    (hcard : p ^ 3 ≤ Nat.card Ab) (hD : Ab ≤ primeFormD h (idGram K 5)) :
    ∃ P : primeFormUnitary h (idGram K 5), ∀ x : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ Ab →
      (((P⁻¹ * x * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K).IsDiag := by
  have := hel
  set G : Subgroup (primeFormUnitary h (idGram K 5)) :=
    Ab.comap (primeFormConjHom h (idGram K 5)) with hG
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := fun x hx y hy =>
    Z.abelian_lift hel hcard hD hx hy
  by_cases hp5 : p = 5
  · subst hp5
    have hGpow : ∀ x ∈ G, x ^ 5 ∈ idScalarKernel h 5 := by
      intro x hx
      rw [← Z.conj_eq_one_iff, map_pow]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx
    have hGnc : ¬ IsCyclic G := by
      intro hcyc
      let π : G →* Ab := ((primeFormConjHom h (idGram K 5)).comp G.subtype).codRestrict Ab
        (fun x => x.2)
      have hπ : Function.Surjective π := by
        intro a
        obtain ⟨x, hx⟩ := hD a.2
        exact ⟨⟨x, by rw [hG, Subgroup.mem_comap, hx]; exact a.2⟩, Subtype.ext hx⟩
      have hAcyc : IsCyclic Ab := isCyclic_of_surjective π hπ
      have h1 := IsCyclic.exponent_eq_card (α := Ab)
      have h2 : Monoid.exponent Ab ∣ 5 := IsElementaryAbelian.exponent_dvd_p 5 Ab
      rw [h1] at h2
      have h3 := Nat.le_of_dvd (by norm_num) h2
      norm_num at hcard
      omega
    exact CFSG.RankThree.PartOne.KCEvenUnitaryFive.exists_unitary_diagonalizing h Z.dvd G hGcomm
      hGnc hGpow |>.imp fun P hP x hx => hP x hx
  · let G₁ : Subgroup (primeFormUnitary h (idGram K 5)) :=
      { carrier := {x | x ∈ G ∧ x ^ p = 1}
        mul_mem' := by
          rintro x y ⟨hxG, hx⟩ ⟨hyG, hy⟩
          refine ⟨G.mul_mem hxG hyG, ?_⟩
          rw [(show Commute x y from hGcomm x hxG y hyG).mul_pow, hx, hy, one_mul]
        one_mem' := ⟨G.one_mem, one_pow _⟩
        inv_mem' := by
          rintro x ⟨hxG, hx⟩
          refine ⟨G.inv_mem hxG, ?_⟩
          rw [inv_pow, hx, inv_one] }
    have hcomm₁ : ∀ x ∈ G₁, ∀ y ∈ G₁, x * y = y * x := fun x hx y hy => hGcomm x hx.1 y hy.1
    have hpow₁ : ∀ x ∈ G₁, x ^ p = 1 := fun x hx => hx.2
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h (Fact.out : p.Prime)
      Z.dvd G₁ hcomm₁ hpow₁
    refine ⟨P, fun x hx => ?_⟩
    obtain ⟨c, hc, hcx⟩ := Z.exists_scalar_pow_eq_one hp5 x
      (CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx)
    have hρc : primeFormConjHom h (idGram K 5) c = 1 := (Z.conj_eq_one_iff c).2 hc
    have hcxG : c * x ∈ G₁ := by
      refine ⟨?_, hcx⟩
      rw [hG, Subgroup.mem_comap, map_mul, hρc, one_mul]
      exact hx
    have h1 := hP (c * x) hcxG
    have hc' : c⁻¹ ∈ idScalarKernel h 5 := (idScalarKernel h 5).inv_mem hc
    have e : P⁻¹ * x * P = c⁻¹ * (P⁻¹ * (c * x) * P) := by
      have h2 : P⁻¹ * (c * x) * P = c * (P⁻¹ * x * P) := by
        calc P⁻¹ * (c * x) * P = (P⁻¹ * c) * x * P := by group
          _ = (c * P⁻¹) * x * P := by rw [← commute_of_mem_idScalarKernel hc P⁻¹]
          _ = c * (P⁻¹ * x * P) := by group
      rw [h2, inv_mul_cancel_left]
    rw [e]
    exact isDiag_of_scalar_mul hc' h1

end CFSG.RankThree.PartOne.U5K.Kf
