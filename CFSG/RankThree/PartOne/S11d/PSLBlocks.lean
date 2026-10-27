module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG Polynomial Matrix
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary

theorem exists_unique_pth_root {p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card Kˣ) (c : Kˣ) : ∃! γ : Kˣ, γ ^ p = c := by
  have hcop : (Nat.card Kˣ).Coprime p := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpK
  refine ⟨(powCoprime hcop).symm c, ?_, ?_⟩
  · have := (powCoprime hcop).apply_symm_apply c
    rwa [powCoprime_apply] at this
  · intro γ hγ
    apply (powCoprime hcop).injective
    rw [powCoprime_apply, hγ]
    exact ((powCoprime hcop).apply_symm_apply c).symm

theorem aeval_pow_sub_C_eq_zero {n p : ℕ} {K : Type} [Field K] {a : GL (Fin n) K} {c : Kˣ}
    (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    Polynomial.aeval (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))
      (Polynomial.X ^ p - Polynomial.C (c : K)) = 0 := by
  have hMp : (a : Matrix (Fin n) (Fin n) K) ^ p = algebraMap K (Matrix (Fin n) (Fin n) K) c := by
    have h1 : ((a ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (a : Matrix (Fin n) (Fin n) K) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hap, GeneralLinearGroup.coe_scalar]
    rfl
  have hX : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) =
      Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) :=
    (KCLinComm.toLinAlgEquiv'_eq_toLin' _).symm
  rw [hX]
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [← map_pow, hMp, AlgEquiv.commutes, sub_self]

theorem dvd_pow_sub_C_of_block {n p : ℕ} {K : Type} [Field K] {a : GL (Fin n) K} {c : Kˣ}
    (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c)
    {b : K[X]} (hb : b ∈ primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :
    b ∣ Polynomial.X ^ p - Polynomial.C (c : K) :=
  ((mem_primaryFactors.mp hb).2.2).trans (minpoly.dvd K _ (aeval_pow_sub_C_eq_zero hap))

theorem root_pow_of_block {n p : ℕ} {K : Type} [Field K] {a : GL (Fin n) K} {c : Kˣ}
    (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c)
    {b : K[X]} (hb : b ∈ primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :
    (AdjoinRoot.root b) ^ p = algebraMap K (AdjoinRoot b) (c : K) := by
  have h := AdjoinRoot.mk_eq_zero.mpr (dvd_pow_sub_C_of_block hap hb)
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

theorem exists_eq_X_sub_C_of_natDegree_eq_one {K : Type} [Field K] {b : K[X]} (hm : b.Monic)
    (hd : b.natDegree = 1) : ∃ β : K, b = X - C β := by
  refine ⟨-b.coeff 0, ?_⟩
  have h := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hd)
  have h1 : b.coeff 1 = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  rw [h1] at h
  rw [map_neg, sub_neg_eq_add, C_1, one_mul] at *
  exact h

theorem eq_X_sub_C_of_block_deg_one {n p : ℕ} {K : Type} [Field K] [Finite K]
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card Kˣ) {γ : Kˣ} (hγ : γ ^ p = c)
    {b : K[X]} (hb : b ∈ primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)))
    (hd : b.natDegree = 1) : b = X - C (γ : K) := by
  obtain ⟨β, hβ⟩ := exists_eq_X_sub_C_of_natDegree_eq_one (mem_primaryFactors.mp hb).2.1 hd
  have hdvd := dvd_pow_sub_C_of_block hap hb
  have hroot : β ^ p = (c : K) := by
    obtain ⟨q, hq⟩ := hdvd
    have := congrArg (Polynomial.eval β) hq
    rw [hβ] at this
    simpa [sub_eq_zero] using this
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hroot
    exact c.ne_zero hroot.symm
  have hu : (Units.mk0 β hβ0) ^ p = c := Units.ext (by simpa using hroot)
  have := (exists_unique_pth_root hp hpK c).unique hu hγ
  rw [hβ, ← this]
  rfl

theorem exists_orderOf_of_block_deg_ge_two {n p : ℕ} {K : Type} [Field K] [Finite K]
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hp : p.Prime) {γ : Kˣ} (hγ : γ ^ p = c) {b : K[X]}
    (hb : b ∈ primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)))
    (hd : 2 ≤ b.natDegree) :
    have : Fact (Irreducible b) := ⟨(mem_primaryFactors.mp hb).1⟩
    ∃ ω : (AdjoinRoot b)ˣ, orderOf ω = p ∧
      (ω : AdjoinRoot b) = AdjoinRoot.root b * (algebraMap K (AdjoinRoot b) (γ : K))⁻¹ := by
  have hirr : Irreducible b := (mem_primaryFactors.mp hb).1
  have : Fact (Irreducible b) := ⟨hirr⟩
  have : Fact p.Prime := ⟨hp⟩
  have hroot := root_pow_of_block hap hb
  have hγ' : (γ : K) ^ p = (c : K) := by rw [← Units.val_pow_eq_pow_val, hγ]
  have hγ0 : algebraMap K (AdjoinRoot b) (γ : K) ≠ 0 := by simp
  have hr0 : AdjoinRoot.root b ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hroot
    have h2 := hroot.symm
    rw [← map_zero (algebraMap K (AdjoinRoot b))] at h2
    exact c.ne_zero ((algebraMap K (AdjoinRoot b)).injective h2)
  set ω : (AdjoinRoot b)ˣ := Units.mk0 (AdjoinRoot.root b * (algebraMap K (AdjoinRoot b) (γ : K))⁻¹)
    (mul_ne_zero hr0 (inv_ne_zero hγ0)) with hω
  have hωp : ω ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hω, Units.val_mk0, mul_pow, inv_pow, hroot, ← map_pow, hγ']
    simp
  have hω1 : ω ≠ 1 := by
    intro h
    have h1 : AdjoinRoot.root b * (algebraMap K (AdjoinRoot b) (γ : K))⁻¹ = 1 := by
      have := congrArg Units.val h
      simpa [hω] using this
    have h2 : AdjoinRoot.root b = algebraMap K (AdjoinRoot b) (γ : K) := by
      field_simp at h1
      exact h1
    have h3 : Polynomial.aeval (AdjoinRoot.root b) b = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [h2, Polynomial.aeval_algebraMap_apply] at h3
    have h4 : b.IsRoot (γ : K) := by
      have := (algebraMap K (AdjoinRoot b)).injective (h3.trans (map_zero _).symm)
      simpa [Polynomial.aeval_def, Polynomial.IsRoot, Polynomial.eval₂_id] using this
    have h5 := Polynomial.degree_eq_one_of_irreducible_of_root hirr h4
    have h6 : b.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some h5
    omega
  exact ⟨ω, orderOf_eq_prime hωp hω1, by rw [hω]; rfl⟩

theorem blockTheta_eq_scalar {n : ℕ} {K : Type} [Field K] {x : Module.End K (Fin n → K)}
    (hx : Squarefree (minpoly K x)) {w : PiGL (Efac x) (mult x)} {l : Kˣ}
    (h : blockTheta hx w = GeneralLinearGroup.scalar (Fin n) l) (b : primaryFactors x) :
    ((w b : GL (Fin (mult x b)) (Efac x b)) :
      Matrix (Fin (mult x b)) (Fin (mult x b)) (Efac x b)) =
      Matrix.diagonal (fun _ => algebraMap K (Efac x b) (l : K)) := by
  set u : (commutant x)ˣ := thetaEquivUnits hx w with hu
  have h1 : commutantToMat x (u : commutant x) = Matrix.scalar (Fin n) (l : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h
    simpa [blockTheta, coe_commutantUnitsToGL, hu, GeneralLinearGroup.coe_scalar] using this
  have h2 : commutantToMat x (algebraMap K (commutant x) (l : K)) =
      Matrix.scalar (Fin n) (l : K) := by
    rw [AlgHom.commutes]
    exact Matrix.algebraMap_eq_diagonal _
  have h3 : (u : commutant x) = algebraMap K (commutant x) (l : K) :=
    commutantToMat_injective x (h1.trans h2.symm)
  have h4 := congrArg (commutantEquivMatrix hx) h3
  rw [AlgEquiv.commutes, hu, commutantEquivMatrix_thetaEquivUnits] at h4
  have h5 := congrFun h4 b
  rw [Pi.algebraMap_apply] at h5
  rw [h5]
  exact Matrix.algebraMap_eq_diagonal _

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem two_le_pRank_of_blocks {n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : Module.End K (Fin n → K)} (hx : Squarefree (minpoly K x)) (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card Kˣ) {u₁ u₂ : PiGL (Efac x) (mult x)} (hc : Commute u₁ u₂)
    (h₁ : u₁ ^ p = 1) (h₂ : u₂ ^ p = 1)
    (hind : ∀ (i j : ℤ) (l : Kˣ),
      (∀ b : primaryFactors x, (((u₁ ^ i * u₂ ^ j) b : GL (Fin (mult x b)) (Efac x b)) :
        Matrix (Fin (mult x b)) (Fin (mult x b)) (Efac x b)) =
          Matrix.diagonal (fun _ => algebraMap K (Efac x b) (l : K))) →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    2 ≤ CFSG.pRank p (projectiveSL n K) := by
  have hdet : ∀ u : PiGL (Efac x) (mult x), u ^ p = 1 →
      GeneralLinearGroup.det (blockTheta hx u) = 1 := by
    intro u hu
    have h1 : (GeneralLinearGroup.det (blockTheta hx u)) ^ p = 1 := by
      rw [← map_pow, ← map_pow, hu, map_one, map_one]
    have h2 : orderOf (GeneralLinearGroup.det (blockTheta hx u)) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (GeneralLinearGroup.det (blockTheta hx u)) ∣ Nat.card Kˣ :=
      orderOf_dvd_natCard _
    have hcop : Nat.Coprime p (Nat.card Kˣ) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpK
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)
  have hmem : ∀ u : PiGL (Efac x) (mult x), u ^ p = 1 →
      blockTheta hx u ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* _).range := by
    intro u hu
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact hdet u hu
  obtain ⟨σ₁, hσ₁⟩ := hmem u₁ h₁
  obtain ⟨σ₂, hσ₂⟩ := hmem u₂ h₂
  have hσc : Commute σ₁ σ₂ := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, hσ₁, hσ₂]
    exact (hc.map (blockTheta hx)).eq
  have hσp₁ : σ₁ ^ p = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, hσ₁, ← map_pow, h₁, map_one, map_one]
  have hσp₂ : σ₂ ^ p = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, hσ₂, ← map_pow, h₂, map_one, map_one]
  refine two_le_pRank_of_two_elements hp (e₁ := proj n K σ₁) (e₂ := proj n K σ₂)
    (hσc.map (proj n K)) ?_ ?_ ?_
  · rw [← map_pow, hσp₁, map_one]
  · rw [← map_pow, hσp₂, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow, ← map_mul, proj_eq_one_iff] at hij
    obtain ⟨l, -, hl⟩ := mem_scalars.mp hij
    have h1 : blockTheta hx (u₁ ^ i * u₂ ^ j) = GeneralLinearGroup.scalar (Fin n) l := by
      have e : blockTheta hx (u₁ ^ i * u₂ ^ j) =
          SpecialLinearGroup.toGL (σ₁ ^ i * σ₂ ^ j) := by
        rw [map_mul, map_zpow, map_zpow, map_mul, map_zpow, map_zpow, hσ₁, hσ₂]
      rw [e]
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      exact hl
    exact hind i j l (blockTheta_eq_scalar hx h1)

@[expose] noncomputable def pslDiagGL (m : ℕ) (E : Type*) [Field E] :
    (Fin m → Eˣ) →* GL (Fin m) E :=
  (Units.map (Matrix.diagonalRingHom (Fin m) E).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin m => E)).symm.toMonoidHom

theorem coe_pslDiagGL {m : ℕ} {E : Type*} [Field E] (d : Fin m → Eˣ) :
    ((pslDiagGL m E d : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      Matrix.diagonal (fun i => (d i : E)) := rfl

theorem unit_eq_one_of_pow_eq_one {p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card Kˣ) {l : Kˣ} (h : l ^ p = 1) : l = 1 := by
  have h2 : orderOf l ∣ p := orderOf_dvd_of_pow_eq_one h
  have h3 : orderOf l ∣ Nat.card Kˣ := orderOf_dvd_natCard _
  have hcop : Nat.Coprime p (Nat.card Kˣ) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpK
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)

open scoped _root_.Classical in
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem two_le_pRank_of_one_block {n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : Module.End K (Fin n → K)} (hx : Squarefree (minpoly K x)) (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card Kˣ) {b : primaryFactors x} (hm : 2 ≤ mult x b)
    {ω : (Efac x b)ˣ} (ho : orderOf ω = p) : 2 ≤ CFSG.pRank p (projectiveSL n K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hω : ω ^ p = 1 := by rw [← ho]; exact pow_orderOf_eq_one ω
  set r₁ : Fin (mult x b) := ⟨0, by omega⟩ with hr₁
  set r₂ : Fin (mult x b) := ⟨1, by omega⟩ with hr₂
  have hr12 : r₁ ≠ r₂ := by
    intro h
    have := congrArg Fin.val h
    simp [hr₁, hr₂] at this
  set u₁ : PiGL (Efac x) (mult x) :=
    Pi.mulSingle b (pslDiagGL (mult x b) (Efac x b) (Pi.mulSingle r₁ ω)) with hu₁
  set u₂ : PiGL (Efac x) (mult x) :=
    Pi.mulSingle b (pslDiagGL (mult x b) (Efac x b) (Pi.mulSingle r₂ ω)) with hu₂
  refine two_le_pRank_of_blocks hx hp hpK (u₁ := u₁) (u₂ := u₂) ?_ ?_ ?_ ?_
  · exact ((Commute.all (Pi.mulSingle r₁ ω : Fin (mult x b) → (Efac x b)ˣ)
      (Pi.mulSingle r₂ ω)).map (pslDiagGL (mult x b) (Efac x b))).map
        (MonoidHom.mulSingle (fun c => GL (Fin (mult x c)) (Efac x c)) b)
  · rw [hu₁, ← Pi.mulSingle_pow, ← map_pow, ← Pi.mulSingle_pow, hω, Pi.mulSingle_one, map_one]
    exact Pi.mulSingle_one b
  · rw [hu₂, ← Pi.mulSingle_pow, ← map_pow, ← Pi.mulSingle_pow, hω, Pi.mulSingle_one, map_one]
    exact Pi.mulSingle_one b
  · intro i j l hl
    have hb := hl b
    have e : ((u₁ ^ i * u₂ ^ j) b : GL (Fin (mult x b)) (Efac x b)) =
        pslDiagGL (mult x b) (Efac x b) (Pi.mulSingle r₁ (ω ^ i) * Pi.mulSingle r₂ (ω ^ j)) := by
      rw [Pi.mul_apply, hu₁, hu₂, ← Pi.mulSingle_zpow, ← Pi.mulSingle_zpow,
        Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, ← map_zpow, ← map_zpow, ← map_mul,
        ← Pi.mulSingle_zpow, ← Pi.mulSingle_zpow]
    rw [e, coe_pslDiagGL] at hb
    have hent₁ := congrFun (congrFun hb r₁) r₁
    have hent₂ := congrFun (congrFun hb r₂) r₂
    simp only [Matrix.diagonal_apply_eq, Pi.mul_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne hr12, Pi.mulSingle_eq_of_ne hr12.symm, mul_one, one_mul] at hent₁ hent₂
    have hl1 : l = 1 := by
      apply unit_eq_one_of_pow_eq_one hp hpK
      have h1 : ((ω ^ i : (Efac x b)ˣ) : Efac x b) ^ p = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm,
          _root_.zpow_mul, _root_.zpow_natCast, hω, _root_.one_zpow, Units.val_one]
      rw [hent₁] at h1
      apply Units.ext
      apply (algebraMap K (Efac x b)).injective
      rw [Units.val_pow_eq_pow_val, map_pow, h1, Units.val_one, map_one]
    subst hl1
    refine ⟨?_, ?_⟩
    · have h1 : ω ^ i = 1 := Units.ext (by simpa using hent₁)
      have := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [ho] at this
    · have h1 : ω ^ j = 1 := Units.ext (by simpa using hent₂)
      have := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [ho] at this

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem eq_X_sub_C_of_mult_ge_two {n p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card Kˣ) {γ : Kˣ} (hγ : γ ^ p = c)
    (hrank : CFSG.pRank p (projectiveSL n K) ≤ 1)
    (b : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)))
    (hb : 2 ≤ mult (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b) :
    (b : K[X]) = X - C (γ : K) := by
  have hpK' : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  have hsq := squarefree_minpoly_toLin'_of_pow_scalar hpK' hap
  by_cases hd : (b : K[X]).natDegree = 1
  · exact eq_X_sub_C_of_block_deg_one hap hp hpK hγ b.2 hd
  · exfalso
    have hd2 : 2 ≤ (b : K[X]).natDegree := by
      have hpos : 0 < (b : K[X]).natDegree := (mem_primaryFactors.mp b.2).1.natDegree_pos
      omega
    obtain ⟨ω, ho, -⟩ := exists_orderOf_of_block_deg_ge_two hap hp hγ b.2 hd2
    have := two_le_pRank_of_one_block hsq hp hpK hb ho
    omega

end CFSG.RankThree.PartOne
