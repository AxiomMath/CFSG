module

public import CFSG.RankThree.PartOne.S11d.PSLRational
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
public import CFSG.RankThree.PartOne.S11d.PSLAvg

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG Polynomial Matrix
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open scoped _root_.Classical

theorem blockImage_eq_commutator {n : ℕ} {K : Type} [Field K] [Finite K]
    {x : Module.End K (Fin n → K)} (hx : Squarefree (minpoly K x)) (hK : 4 ≤ Nat.card K)
    {b₀ : primaryFactors x} (hb₀ : 2 ≤ mult x b₀)
    (huniq : ∀ b : primaryFactors x, 2 ≤ mult x b → b = b₀) :
    ⁅(commutantUnitsToGL x).range, (commutantUnitsToGL x).range⁆ = blockImage hx b₀ := by
  rw [commutator_range_eq_iSup hx hK]
  apply le_antisymm
  · refine iSup_le fun b => ?_
    rw [huniq b.1 b.2]
  · exact le_iSup (fun b : {a : primaryFactors x // 2 ≤ mult x a} => blockImage hx b.1)
      ⟨b₀, hb₀⟩

theorem map_mem_blockImage {n : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {a : GL (Fin n) K} (hσa : (a : Matrix (Fin n) (Fin n) K).map σ = a)
    (hx : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))
    (hK : 4 ≤ Nat.card K) {b₀ : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))}
    (hb₀ : 2 ≤ mult (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b₀)
    (huniq : ∀ b : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)),
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b → b = b₀)
    {g : GL (Fin n) K} (hg : g ∈ blockImage hx b₀) :
    GeneralLinearGroup.map (n := Fin n) σ.toRingHom g ∈ blockImage hx b₀ := by
  set x := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) with hxdef
  set Gσ : GL (Fin n) K →* GL (Fin n) K := GeneralLinearGroup.map (n := Fin n) σ.toRingHom
    with hGσ
  have hGσa : Gσ a = a := by
    apply Units.ext
    exact hσa
  have hC : (commutantUnitsToGL x).range = Subgroup.centralizer ({a} : Set (GL (Fin n) K)) :=
    range_commutantUnitsToGL_eq_centralizer a rfl
  have hmap : (Subgroup.centralizer ({a} : Set (GL (Fin n) K))).map Gσ ≤
      Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := by
    rintro _ ⟨h, hh, rfl⟩
    have hh' : h ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := hh
    rw [Subgroup.mem_centralizer_singleton_iff] at hh'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg Gσ hh'
    rw [map_mul, map_mul, hGσa] at this
    exact this
  rw [← blockImage_eq_commutator hx hK hb₀ huniq] at hg ⊢
  rw [hC] at hg ⊢
  have h1 : Gσ g ∈ ⁅(Subgroup.centralizer ({a} : Set (GL (Fin n) K))).map Gσ,
      (Subgroup.centralizer ({a} : Set (GL (Fin n) K))).map Gσ⁆ := by
    rw [← Subgroup.map_commutator]
    exact ⟨g, hg, rfl⟩
  exact Subgroup.commutator_mono hmap hmap h1


theorem smul_inv_pow_eq_one {n p : ℕ} {K : Type} [Field K] {a : GL (Fin n) K} {γ : Kˣ}
    (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) (γ ^ p)) :
    (((γ⁻¹ : Kˣ) : K) • (a : Matrix (Fin n) (Fin n) K)) ^ p = 1 := by
  have hMp : (a : Matrix (Fin n) (Fin n) K) ^ p =
      algebraMap K (Matrix (Fin n) (Fin n) K) ((γ ^ p : Kˣ) : K) := by
    have h1 : ((a ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (a : Matrix (Fin n) (Fin n) K) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hap, GeneralLinearGroup.coe_scalar]
    rfl
  rw [_root_.smul_pow, hMp, Algebra.smul_def, ← map_mul, Units.val_pow_eq_pow_val, ← mul_pow,
    Units.inv_mul, one_pow, map_one]


theorem range_avgProj_eq {n p : ℕ} {K : Type} [Field K] [CharP K 2] (hp : Odd p)
    {a : GL (Fin n) K} {γ : Kˣ} (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) (γ ^ p)) :
    LinearMap.range (avgProj p (((γ⁻¹ : Kˣ) : K) • (a : Matrix (Fin n) (Fin n) K))).mulVecLin =
      primaryComponent (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) (X - C (γ : K)) := by
  set Bm : Matrix (Fin n) (Fin n) K := ((γ⁻¹ : Kˣ) : K) • (a : Matrix (Fin n) (Fin n) K) with hBm
  have hB : Bm ^ p = 1 := smul_inv_pow_eq_one hap
  have hP := avgProj_mul_self hp hB
  have hBP := mul_avgProj hB
  have key : ∀ v : Fin n → K,
      v ∈ LinearMap.range (avgProj p Bm).mulVecLin ↔ Bm.mulVec v = v := by
    intro v
    constructor
    · rintro ⟨u, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBP]
    · intro hv
      refine ⟨v, ?_⟩
      rw [Matrix.mulVecLin_apply]
      have hpow : ∀ i : ℕ, (Bm ^ i).mulVec v = v := by
        intro i
        induction i with
        | zero => simp
        | succ i ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hv]
      have h1 : (avgProj p Bm).mulVec v = ∑ i ∈ Finset.range p, (Bm ^ i).mulVec v := by
        unfold avgProj
        rw [Matrix.sum_mulVec]
      rw [h1, Finset.sum_congr rfl fun i _ => hpow i, Finset.sum_const, Finset.card_range]
      obtain ⟨m, rfl⟩ := hp
      have h2 : ((2 * m + 1 : ℕ) : K) = 1 := by
        push_cast
        rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2]
        ring
      rw [← Nat.cast_smul_eq_nsmul K, h2, one_smul]
  ext v
  rw [key, mem_primaryComponent]
  have hγ0 : (γ : K) ≠ 0 := γ.ne_zero
  have hx : (Polynomial.aeval (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))
      (X - C (γ : K))) v = (a : Matrix (Fin n) (Fin n) K).mulVec v - (γ : K) • v := by
    simp [Matrix.toLin'_apply', Module.algebraMap_end_apply]
  rw [hx, hBm, Matrix.smul_mulVec]
  constructor
  · intro h
    have h1 : (a : Matrix (Fin n) (Fin n) K).mulVec v = (γ : K) • v := by
      calc (a : Matrix (Fin n) (Fin n) K).mulVec v
          = (γ : K) • (((γ⁻¹ : Kˣ) : K) • (a : Matrix (Fin n) (Fin n) K).mulVec v) := by
            rw [smul_smul, Units.mul_inv, one_smul]
        _ = (γ : K) • v := by rw [h]
    rw [h1, sub_self]
  · intro h
    have h1 : (a : Matrix (Fin n) (Fin n) K).mulVec v = (γ : K) • v := sub_eq_zero.mp h
    rw [h1, smul_smul, Units.inv_mul, one_smul]


theorem mulVec_commutantUnitsToGL {n : ℕ} {K : Type} [Field K] (x : Module.End K (Fin n → K))
    (u : (commutant x)ˣ) (v : Fin n → K) :
    ((commutantUnitsToGL x u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v =
      ((u : commutant x) : Module.End K (Fin n → K)) v := by
  rw [coe_commutantUnitsToGL]
  have h1 : Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm (u : commutant x) :
      Matrix (Fin n) (Fin n) K) = ((u : commutant x) : Module.End K (Fin n → K)) :=
    AlgEquiv.apply_symm_apply _ _
  rw [← Matrix.toLin'_apply, ← toLinAlgEquiv'_eq_toLin']
  exact congrArg (fun f : Module.End K (Fin n → K) => f v) h1

theorem eq_one_of_apply_primary {n : ℕ} {K : Type} [Field K] [Finite K]
    {x : Module.End K (Fin n → K)} (hx : Squarefree (minpoly K x)) (b₀ : primaryFactors x)
    {g : GL (Fin n) K} (hg : g ∈ blockImage hx b₀)
    (h : ∀ v ∈ primaryComponent x (b₀ : K[X]),
      (g : Matrix (Fin n) (Fin n) K).mulVec v = v) : g = 1 := by
  obtain ⟨s, rfl⟩ := mem_blockImage.mp hg
  set w := blockEmbed (Efac x) (mult x) b₀ s with hw
  set u : (commutant x)ˣ := thetaEquivUnits hx w with hu
  have hgu : blockTheta hx w = commutantUnitsToGL x u := rfl
  have hr1 : ∀ v ∈ primaryComponent x (b₀ : K[X]),
      ((u : commutant x) : Module.End K (Fin n → K)) v = v := by
    intro v hv
    rw [← mulVec_commutantUnitsToGL, ← hgu]
    exact h v hv
  have hpi : commutantEquivPi hx (u : commutant x) b₀ = 1 := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [coe_commutantEquivPi_apply]
    exact hr1 _ v.2
  have hmat : commutantEquivMatrix hx (u : commutant x) b₀ = 1 := by
    change (LinearMap.toMatrixAlgEquiv (Module.finBasis (AdjoinRoot (b₀ : K[X]))
      (primaryComponent x (b₀ : K[X])))).restrictScalars K
        (commutantEquivPi hx (u : commutant x) b₀) = 1
    rw [hpi]
    exact map_one _
  have hwb : ((w b₀ : GL (Fin (mult x b₀)) (Efac x b₀)) :
      Matrix (Fin (mult x b₀)) (Fin (mult x b₀)) (Efac x b₀)) = 1 := by
    have := congrFun (commutantEquivMatrix_thetaEquivUnits hx w) b₀
    rw [← this]
    exact hmat
  have hwb0 : w b₀ = SpecialLinearGroup.toGL s := blockEmbed_apply_self b₀ s
  have hs : s = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_one]
    apply Units.ext
    rw [← hwb0, hwb, Units.val_one]
  rw [hw, hs, map_one, map_one]


noncomputable def slMulEquiv {m : ℕ} {E F : Type*} [Field E] [Field F] (f : E ≃+* F) :
    SpecialLinearGroup (Fin m) E ≃* SpecialLinearGroup (Fin m) F :=
  MulEquiv.ofBijective (SpecialLinearGroup.map f.toRingHom) ⟨by
    intro g₁ g₂ h
    ext i j
    have := congrArg (fun g : SpecialLinearGroup (Fin m) F => (g : Matrix (Fin m) (Fin m) F) i j) h
    exact f.injective this, by
    intro t
    refine ⟨SpecialLinearGroup.map f.symm.toRingHom t, ?_⟩
    ext i j
    simp⟩

noncomputable def adjoinRootLinearEquiv {K : Type} [Field K] {f : K[X]} [Fact (Irreducible f)]
    {γ : K} (hf : f = X - C γ) : K ≃+* AdjoinRoot f :=
  RingEquiv.ofBijective (algebraMap K (AdjoinRoot f)) ⟨(algebraMap K (AdjoinRoot f)).injective, by
    intro e
    induction e using AdjoinRoot.induction_on with
    | _ g =>
      refine ⟨Polynomial.eval γ g, ?_⟩
      have h1 : AdjoinRoot.root f = algebraMap K (AdjoinRoot f) γ := by
        have := AdjoinRoot.mk_self (f := f)
        rw [hf] at this ⊢
        simp only [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at this
        exact sub_eq_zero.mp this
      rw [← AdjoinRoot.aeval_eq, h1, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def,
        Algebra.algebraMap_self]
      rfl⟩

theorem card_blockImage {n : ℕ} {K : Type} [Field K] [Finite K]
    {x : Module.End K (Fin n → K)} (hx : Squarefree (minpoly K x)) (b₀ : primaryFactors x)
    {γ : K} (hb₀ : (b₀ : K[X]) = X - C γ) :
    Nat.card (blockImage hx b₀) = Nat.card (SpecialLinearGroup (Fin (mult x b₀)) K) := by
  have e1 : (blockSL (Efac x) (mult x) b₀) ≃* blockImage hx b₀ :=
    Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx)
  have e2 : SpecialLinearGroup (Fin (mult x b₀)) (Efac x b₀) ≃* blockSL (Efac x) (mult x) b₀ :=
    MonoidHom.ofInjective (blockEmbed_injective (E := Efac x) (m := mult x) b₀)
  have e3 : SpecialLinearGroup (Fin (mult x b₀)) K ≃* SpecialLinearGroup (Fin (mult x b₀))
      (Efac x b₀) := slMulEquiv (adjoinRootLinearEquiv hb₀)
  rw [Nat.card_congr e1.symm.toEquiv, Nat.card_congr e2.symm.toEquiv, Nat.card_congr e3.toEquiv]


theorem exists_blockCoord {n p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : Odd p)
    (σ : K ≃+* K) {a : GL (Fin n) K} {γ : Kˣ}
    (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) (γ ^ p))
    (hσa : (a : Matrix (Fin n) (Fin n) K).map σ = a) (hσγ : σ (γ : K) = γ)
    {x : Module.End K (Fin n → K)} (hax : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) = x)
    (hsq : Squarefree (minpoly K x))
    (hK : 4 ≤ Nat.card K) (b₀ : primaryFactors x) (hb₀ : (b₀ : K[X]) = X - C (γ : K))
    (hm2 : 2 ≤ mult x b₀) :
    ∃ (m : ℕ) (C : Matrix (Fin n) (Fin m) K)
      (Φ : blockImage hsq b₀ ≃* SpecialLinearGroup (Fin m) K),
      C.map σ = C ∧ 2 ≤ m ∧
      (∀ g : blockImage hsq b₀, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * C =
        C * (Φ g : Matrix (Fin m) (Fin m) K)) ∧
      ∀ g g' : blockImage hsq b₀, ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ →
          Φ g' = SpecialLinearGroup.map σ.toRingHom (Φ g) := by
  set Bm : Matrix (Fin n) (Fin n) K := ((γ⁻¹ : Kˣ) : K) • (a : Matrix (Fin n) (Fin n) K) with hBm
  set P := avgProj p Bm with hPdef
  have hBσ : Bm.map σ = Bm := by
    rw [hBm]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    have h1 : σ ((γ⁻¹ : Kˣ) : K) = ((γ⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hσγ]
    rw [h1]
    have := congrFun (congrFun hσa i) j
    simp only [Matrix.map_apply] at this
    rw [this]
  have hPσ : P.map σ = P := by
    have h1 : σ.toRingHom.mapMatrix P = P := by
      rw [hPdef]
      unfold avgProj
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow]
      have : σ.toRingHom.mapMatrix Bm = Bm := hBσ
      rw [this]
    exact h1
  obtain ⟨m, ⟨R⟩, hfin⟩ := exists_rational_columns σ P hPσ
  have hrange : LinearMap.range P.mulVecLin = primaryComponent x (b₀ : K[X]) := by
    rw [hb₀, ← hax]
    exact range_avgProj_eq hp hap
  have hnd : (b₀ : K[X]).natDegree = 1 := by
    rw [hb₀]
    exact natDegree_X_sub_C _
  have hmult : mult x b₀ = m := by
    have h1 := finrank_primaryComponent x (b₀ : K[X])
    rw [hnd, one_mul] at h1
    rw [← hfin, hrange]
    exact h1.symm
  subst hmult
  set B := blockImage hsq b₀ with hB
  have hBC : B ≤ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := by
    rw [← range_commutantUnitsToGL_eq_centralizer (x := x) a hax]
    exact blockImage_le_range hsq b₀
  have hcomm : ∀ g ∈ B, (g : Matrix (Fin n) (Fin n) K) * P = P * g := by
    intro g hg
    have h1 : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp (hBC hg)
    have h2 : (g : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) =
        (a : Matrix (Fin n) (Fin n) K) * g := by
      have := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h1
      simpa using this
    have h3 : Commute (g : Matrix (Fin n) (Fin n) K) Bm := by
      show (g : Matrix (Fin n) (Fin n) K) * Bm = Bm * g
      rw [hBm, Matrix.mul_smul, Matrix.smul_mul, h2]
    have h4 : Commute (g : Matrix (Fin n) (Fin n) K) P := by
      rw [hPdef]
      unfold avgProj
      exact Commute.sum_right _ _ _ fun i _ => h3.pow_right i
    exact h4.eq
  have hperf : Group.IsPerfect ↥B := isPerfect_blockImage hsq hK b₀ hm2
  have hdet : ∀ g : B, (coordMon R B hcomm g).det = 1 := by
    intro g
    have h := KCUnitary.eq_one_of_perfect_of_comm hperf (fun u v : Kˣ => mul_comm u v)
      (GeneralLinearGroup.det.comp (MonoidHom.toHomUnits (coordMon R B hcomm))) g
    have h3 := congrArg (fun u : Kˣ => (u : K)) h
    simpa [GeneralLinearGroup.val_det_apply] using h3
  let Φ' : B →* SpecialLinearGroup (Fin (mult x b₀)) K :=
    { toFun := fun g => ⟨coordMon R B hcomm g, hdet g⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun g₁ g₂ => Subtype.ext (map_mul _ _ _) }
  have hinj : Function.Injective Φ' := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : coordMon R B hcomm g = 1 := congrArg Subtype.val hg
    have h2 := mul_coordMon R B hcomm g
    rw [h1, Matrix.mul_one] at h2
    apply Subtype.ext
    apply eq_one_of_apply_primary hsq b₀ g.2
    intro v hv
    rw [← hrange, ← R.range_eq] at hv
    obtain ⟨w, rfl⟩ := hv
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h2]
  have hbij : Function.Bijective Φ' := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [← card_blockImage hsq b₀ hb₀]
  refine ⟨mult x b₀, R.C, MulEquiv.ofBijective Φ' hbij, R.map_C, hm2, ?_, ?_⟩
  · intro g
    exact mul_coordMon R B hcomm g
  · intro g g' hgg
    apply Subtype.ext
    exact coordMon_map R B hcomm g g' hgg

end CFSG.RankThree.PartOne
