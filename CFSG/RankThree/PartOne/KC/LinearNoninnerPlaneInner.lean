module

public import CFSG.RankThree.PartOne.KC.LinearPlaneStatements
public import CFSG.RankThree.PartOne.KC.LinearCommutantSetting

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut SemiGL)
open CFSG.RankThree.PartOne.KCLinComm

namespace KCLinPlane

theorem exists_pow_eq_of_pow_eq {G : Type*} [CommGroup G] {m p n : ℕ} (hm : ∀ x : G, x ^ m = 1)
    (hcop : Nat.Coprime p (Nat.gcd n m)) {δ u : G} (h : δ ^ p = u ^ n) :
    ∃ w : G, w ^ n = δ := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (p : ℤ) ((Nat.gcd n m : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  have hg := Nat.gcd_eq_gcd_ab n m
  refine ⟨u ^ x * δ ^ (y * Nat.gcdA n m), ?_⟩
  have h1 : (u ^ x) ^ n = δ ^ (p * x) := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← h,
      ← zpow_natCast, ← _root_.zpow_mul]
  have h2 : (δ ^ (y * Nat.gcdA n m)) ^ n = δ ^ (y * Nat.gcdA n m * n) := by
    rw [← zpow_natCast, ← _root_.zpow_mul]
  have h3 : (p : ℤ) * x + y * Nat.gcdA n m * n = 1 + m * (-(y * Nat.gcdB n m)) := by
    have : (p : ℤ) * x + y * ((n : ℤ) * Nat.gcdA n m + m * Nat.gcdB n m) = 1 := by
      rw [← hg]
      linarith
    linarith
  rw [mul_pow, h1, h2, ← _root_.zpow_add, h3, _root_.zpow_add, zpow_one, _root_.zpow_mul,
    zpow_natCast, hm δ, _root_.one_zpow, mul_one]

theorem det_scalar_gl_units {n : ℕ} {K : Type} [Field K] (c : Kˣ) :
    Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) = c ^ n := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_scalar_gl, Units.val_pow_eq_pow_val]

theorem inner_of_mem_linearAut_of_pow_eq_one {n : ℕ} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hn : 3 ≤ n) (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)))
    {a : MulAut (projectiveSL n K)} (haD : a ∈ linearAutGroup n K) (hap : a ^ p = 1) :
    a ∈ innSL n K := by
  obtain ⟨g, rfl⟩ := mem_linearAutGroup_iff.mp haD
  have h1 : conjAut n K (g ^ p) = 1 := by rw [map_pow, hap]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn _).mp h1
  have hdet : (Matrix.GeneralLinearGroup.det g) ^ p = c ^ n := by
    rw [← map_pow, ← hc, det_scalar_gl_units]
  obtain ⟨u, hu⟩ := exists_pow_eq_of_pow_eq (m := Nat.card K - 1)
    (fun x : Kˣ => by rw [← Nat.card_units]; exact pow_card_eq_one') hcop hdet
  have hdet' : Matrix.GeneralLinearGroup.det
      (GeneralLinearGroup.scalar (Fin n) u⁻¹ * g) = 1 := by
    rw [map_mul, det_scalar_gl_units, ← hu, inv_pow, inv_mul_cancel]
  have hrange : GeneralLinearGroup.scalar (Fin n) u⁻¹ * g ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet'
  have h2 : conjAut n K g = conjAut n K (GeneralLinearGroup.scalar (Fin n) u⁻¹ * g) := by
    rw [map_mul, conjAut_scalar, one_mul]
  rw [h2]
  show _ ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
  rw [← map_toGL_range_eq_conj_range]
  exact ⟨_, hrange, rfl⟩

@[expose] noncomputable def sigmaE (n : ℕ) (K : Type) [Field K] [Finite K] (hn : 3 ≤ n) :
    ↥(semilinPsi n K).range →* (K ≃+* K) :=
  MonoidHom.liftOfRightInverse (semilinPsi n K).rangeRestrict
    (Function.surjInv (semilinPsi n K).rangeRestrict_surjective)
    (Function.rightInverse_surjInv (semilinPsi n K).rangeRestrict_surjective)
    ⟨SemidirectProduct.rightHom, fun g hg => by
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hg
      obtain ⟨A, σ⟩ := g
      rw [semilinPsi_mk] at hg
      exact MonoidHom.mem_ker.mpr (eq_one_of_conjAut_mul_fieldAut_eq_one hn A σ hg).1⟩

theorem sigmaE_semilinPsi {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    (g : SemiGL (Fin n) K) :
    sigmaE n K hn ⟨semilinPsi n K g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ = g.right :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem sigmaE_eq_one_iff {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    (α : ↥(semilinPsi n K).range) :
    sigmaE n K hn α = 1 ↔ (α : MulAut (projectiveSL n K)) ∈ linearAutGroup n K := by
  obtain ⟨α, ⟨⟨M, σ⟩, rfl⟩⟩ := α
  rw [sigmaE_semilinPsi]
  constructor
  · intro h
    have h' : σ = 1 := h
    subst h'
    show semilinPsi n K ⟨M, 1⟩ ∈ linearAutGroup n K
    rw [semilinPsi_mk, map_one, mul_one]
    exact conjAut_mem_linearAutGroup M
  · intro h
    have h0 : semilinPsi n K ⟨M, σ⟩ ∈ linearAutGroup n K := h
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp h0
    rw [semilinPsi_mk] at hA
    have h1 : conjAut n K (A⁻¹ * M) * fieldAut n K σ = 1 := by
      rw [map_mul, map_inv, mul_assoc, ← hA, inv_mul_cancel]
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ σ h1).1


theorem card_inf_inner_eq_prime {n : ℕ} {K : Type} [Field K] [Finite K] {p : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)))
    (hcyc : IsCyclic (K ≃+* K)) {A : Subgroup (MulAut (projectiveSL n K))}
    (hAE : A ≤ (semilinPsi n K).range) [IsElementaryAbelian p A] (hAcard : Nat.card A = p ^ 2)
    (hAH : ¬ A ≤ innSL n K) :
    Nat.card (A ⊓ innSL n K : Subgroup (MulAut (projectiveSL n K))) = p := by
  classical
  have hpA : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hAD : ∀ a ∈ A, a ∈ linearAutGroup n K → a ∈ innSL n K := fun a ha haD =>
    inner_of_mem_linearAut_of_pow_eq_one hn hcop haD (hpA a ha)
  have : Finite ↥A := inferInstance
  have hdvd : Nat.card (A ⊓ innSL n K : Subgroup (MulAut (projectiveSL n K))) ∣ p ^ 2 := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases i
  · exfalso
    have hbot : A ⊓ innSL n K = ⊥ := Subgroup.card_eq_one.mp (by simpa using hcard)
    let φ : ↥A →* (K ≃+* K) := (sigmaE n K hn).comp (Subgroup.inclusion hAE)
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : sigmaE n K hn ⟨(a : MulAut (projectiveSL n K)), hAE a.2⟩ = 1 := ha
      have h2 := (sigmaE_eq_one_iff hn _).mp h1
      have h3 : (a : MulAut (projectiveSL n K)) ∈ A ⊓ innSL n K := ⟨a.2, hAD a a.2 h2⟩
      rw [hbot] at h3
      exact Subtype.ext (Subgroup.mem_bot.mp h3)
    have : IsCyclic φ.range := Subgroup.isCyclic _
    have : IsCyclic ↥A :=
      isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm (MulEquiv.surjective _)
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hpA g g.2)
    have h4 := orderOf_dvd_of_pow_eq_one hgp
    rw [hg, hAcard] at h4
    have h5 := Nat.le_of_dvd hp.pos h4
    nlinarith [hp.two_le]
  · simpa using hcard
  · exfalso
    apply hAH
    have h6 : A ⊓ innSL n K = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hAcard])
    calc A = A ⊓ innSL n K := h6.symm
      _ ≤ innSL n K := inf_le_right

end KCLinPlane

end CFSG.RankThree.PartOne
