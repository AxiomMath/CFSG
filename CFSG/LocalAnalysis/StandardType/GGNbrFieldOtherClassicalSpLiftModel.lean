module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftSL2
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

open CFSG.LieType.SteinbergBR.EvenSp

variable {K : Type} [Field K]

section Torus

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_matrixTorus_of_sl2Pi [Finite K] [CharP K 2] {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {H : Subgroup (GL ι K)}
    (Φ : (Fin k → Matrix.SpecialLinearGroup (Fin 2) K) →* GL ι K)
    (Y : Multiplicative K →* GL ι K)
    (hΦinj : Function.Injective Φ) (hΦH : ∀ a, Φ a ∈ H) (hYH : ∀ c, Y c ∈ H)
    (hY1 : Y (Multiplicative.ofAdd 1) ∉ LargeEvenScalars ι K) (hY2 : ∀ c, Y c ^ 2 = 1)
    (hΦY : ∀ a c, Φ a * Y c = Y c * Φ a) :
    ∃ (τ : (Fin k → Multiplicative (ZMod p)) →* GL ι K) (X : Multiplicative K →* GL ι K),
      (∀ f, τ f ∈ H) ∧ (∀ f, τ f ∈ LargeEvenScalars ι K → f = 1) ∧
      (∀ i j : Fin k, ∃ w ∈ H, w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
        (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j)) ∧
      (∀ c, X c ∈ H) ∧ X (Multiplicative.ofAdd 1) ∉ LargeEvenScalars ι K ∧
      (∀ c, X c ^ 2 = 1) ∧ (∀ f c, ∃ c', τ f * X c * (τ f)⁻¹ = X c') := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s, n, hso, hn⟩ :=
    CFSG.StandardType.GGPlusLiftSL2.exists_order_p_inverting_sl2 hp hp2 hpq
  have hsp : s ^ p = 1 := by rw [← hso]; exact pow_orderOf_eq_one s
  let ρ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K := zmodPowHom hsp
  let τ : (Fin k → Multiplicative (ZMod p)) →* GL ι K :=
    Φ.comp (MonoidHom.pi fun i =>
      ρ.comp (Pi.evalMonoidHom (fun _ : Fin k => Multiplicative (ZMod p)) i))
  have hτ_apply : ∀ f, τ f = Φ (fun i => ρ (f i)) := fun _ => rfl
  have hbasis : ∀ i : Fin k, torusBasis τ i = Φ (Pi.mulSingle i s) := by
    intro i
    rw [torusBasis, hτ_apply]
    congr 1
    funext j
    by_cases hji : j = i
    · subst hji
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      simpa [ρ] using zmodPowHom_natCast hsp 1
    · rw [Pi.mulSingle_eq_of_ne hji, Pi.mulSingle_eq_of_ne hji]
      exact map_one ρ
  have hτs : ∀ f, τ f ∈ LargeEvenScalars ι K → f = 1 := by
    intro f hsc
    have hι : Nonempty ι := by
      rcases isEmpty_or_nonempty ι with h | h
      · exfalso
        refine hY1 ?_
        rw [largeEvenScalars_def]
        exact ⟨1, by
          rw [map_one]
          apply Units.ext
          ext i j
          exact (IsEmpty.false i).elim⟩
      · exact h
    obtain ⟨i⟩ := hι
    rw [largeEvenScalars_def] at hsc
    obtain ⟨c, hc⟩ := hsc
    have hfp : f ^ p = 1 := by
      funext j
      rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f j), ← ofAdd_nsmul, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul, ofAdd_zero]
    have hτpow : (τ f) ^ p = 1 := by rw [← map_pow, hfp, map_one]
    have hcpow : c ^ p = 1 := by
      have hmat : Matrix.GeneralLinearGroup.scalar ι (c ^ p) = 1 := by
        rw [map_pow, hc, hτpow]
      have hentry : ((c ^ p : Kˣ) : K) = 1 := by
        have h := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i i) hmat
        rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.diagonal_apply_eq] at h
        simpa using h
      exact Units.ext hentry
    have hord : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcpow
    have hordK : orderOf c ∣ Nat.card K - 1 := by
      rw [← Nat.card_units (α := K)]
      exact orderOf_dvd_natCard c
    have hpK : ¬ p ∣ Nat.card K - 1 := by
      intro hpdvd
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have h1 : p ≤ Nat.card K + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
        have h2 : 2 ≤ p := hp.two_le
        omega
      have h2d : p ∣ 2 := by
        rw [← hsub]
        exact Nat.dvd_sub hpq hpdvd
      exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2d) hp.two_le)
    have hc1 : c = 1 := by
      rcases hp.eq_one_or_self_of_dvd (orderOf c) hord with h1 | hp'
      · rw [← orderOf_eq_one_iff]; exact h1
      · exact absurd (hp' ▸ hordK) hpK
    have hτ1 : τ f = 1 := by rw [← hc, hc1, map_one]
    have hfun : (fun i => ρ (f i)) = 1 :=
      hΦinj (by rw [hτ_apply] at hτ1; rw [hτ1, map_one])
    funext i
    exact (zmodPowHom_eq_one_iff hsp hso).mp (congrFun hfun i)
  have hinv : ∀ i j : Fin k, ∃ w ∈ H, w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
      (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j) := by
    intro i j
    refine ⟨Φ (Pi.mulSingle i n), hΦH _, ?_, ?_⟩
    · rw [hbasis i, ← map_inv, ← map_mul, ← map_mul, ← Pi.mulSingle_inv, ← Pi.mulSingle_mul,
        ← Pi.mulSingle_mul, hn, Pi.mulSingle_inv, map_inv]
    · intro hji
      rw [hbasis j]
      let G : Fin k → Type := fun _ => Matrix.SpecialLinearGroup (Fin 2) K
      have hcomm : Commute (Pi.mulSingle (M := G) i n) (Pi.mulSingle (M := G) j s) :=
        Pi.mulSingle_commute (f := G) hji.symm n s
      rw [(hcomm.map Φ).eq, mul_inv_cancel_right]
  have hτX : ∀ f c, ∃ c', τ f * Y c * (τ f)⁻¹ = Y c' := by
    intro f c
    refine ⟨c, ?_⟩
    rw [hτ_apply, hΦY, mul_inv_cancel_right]
  exact ⟨τ, Y, fun f => hΦH _, hτs, hinv, hYH, hY1, hY2, hτX⟩

end Torus

section Model

variable {m : ℕ}

private noncomputable def slBlocksExtend {k : ℕ} (m : ℕ) :
    (Fin k → Matrix.SpecialLinearGroup (Fin 2) K) →* (Fin m → GL (Fin 2) K) where
  toFun a j := if h : (j : ℕ) < k then Matrix.SpecialLinearGroup.toGL (a ⟨j, h⟩) else 1
  map_one' := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [h]
  map_mul' a b := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [h]

private lemma slBlocksExtend_apply {k : ℕ} (a : Fin k → Matrix.SpecialLinearGroup (Fin 2) K)
    (j : Fin m) :
    slBlocksExtend m a j =
      if h : (j : ℕ) < k then Matrix.SpecialLinearGroup.toGL (a ⟨j, h⟩) else 1 :=
  rfl

private lemma slBlocksExtend_injective {k : ℕ} (hk : k ≤ m) :
    Function.Injective (slBlocksExtend (K := K) (k := k) m) := by
  intro a b h
  funext i
  have hi := congrFun h (Fin.castLE hk i)
  have hlt : ((Fin.castLE hk i : Fin m) : ℕ) < k := by simp
  rw [slBlocksExtend_apply, slBlocksExtend_apply, dif_pos hlt, dif_pos hlt] at hi
  exact Matrix.SpecialLinearGroup.toGL_injective hi

private lemma slBlocksExtend_det {k : ℕ} (a : Fin k → Matrix.SpecialLinearGroup (Fin 2) K)
    (j : Fin m) :
    ((slBlocksExtend m a j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [slBlocksExtend_apply]
  by_cases h : (j : ℕ) < k
  · rw [dif_pos h]
    simpa using Matrix.SpecialLinearGroup.det_coe (a ⟨j, h⟩)
  · rw [dif_neg h]
    simp

theorem exists_nsSpModelFin [CharP K 2] {k : ℕ} (hk : k < m) :
    ∃ (Φ : (Fin k → Matrix.SpecialLinearGroup (Fin 2) K) →* GL (Fin m ⊕ Fin m) K)
      (Y : Multiplicative K →* GL (Fin m ⊕ Fin m) K),
      Function.Injective Φ ∧ (∀ a, Φ a ∈ LargeEvenSpGroup K m) ∧
      (∀ c, Y c ∈ LargeEvenSpGroup K m) ∧
      Y (Multiplicative.ofAdd 1) ∉ LargeEvenScalars (Fin m ⊕ Fin m) K ∧
      (∀ c, Y c ^ 2 = 1) ∧ (∀ a c, Φ a * Y c = Y c * Φ a) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  let i : Fin m := ⟨k, hk⟩
  let Y : Multiplicative K →* GL (Fin m ⊕ Fin m) K :=
    planeHom.comp ((MonoidHom.mulSingle (fun _ => GL (Fin 2) K) i).comp
      (TauCeti.transvectionHom h01))
  have hY : ∀ c, Y c = planeHom (Pi.mulSingle i (TauCeti.transvectionHom h01 c)) := fun _ => rfl
  refine ⟨planeHom.comp (slBlocksExtend m), Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : planeHom (slBlocksExtend m a) = planeHom (slBlocksExtend m b) := hab
    exact slBlocksExtend_injective hk.le (planeHom_injective hab')
  · intro a
    exact planeHom_mem_statedSp _ (slBlocksExtend_det a)
  · intro c
    rw [hY]
    refine planeHom_mem_statedSp _ fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, TauCeti.transvectionHom_apply, TauCeti.coe_transvectionUnit,
        Matrix.det_transvection_of_ne _ _ h01]
    · rw [Pi.mulSingle_eq_of_ne hj, Units.val_one, Matrix.det_one]
  · intro hmem
    rw [largeEvenScalars_def] at hmem
    obtain ⟨c, hc⟩ := hmem
    have e := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i) (Sum.inr i)) hc
    simp only [hY, planeHom_val, planeMat, Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply_eq,
      Pi.mulSingle_eq_same, TauCeti.transvectionHom_apply, TauCeti.coe_transvectionUnit,
      toAdd_ofAdd, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e
    rw [Matrix.diagonal_apply_ne _ Sum.inl_ne_inr, Matrix.transvection, Matrix.add_apply,
      Matrix.one_apply_ne h01, Matrix.single_apply_same, zero_add] at e
    exact zero_ne_one e
  · intro c
    rw [← map_pow]
    have hc2 : c ^ 2 = 1 := by
      rw [← ofAdd_toAdd c, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [hc2, map_one]
  · intro a c
    rw [MonoidHom.comp_apply, hY, ← map_mul, ← map_mul]
    congr 1
    funext j
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hj : j = i
    · have hik : ¬ ((i : ℕ) < k) := lt_irrefl k
      rw [hj, Pi.mulSingle_eq_same, slBlocksExtend_apply, dif_neg hik, one_mul, mul_one]
    · rw [Pi.mulSingle_eq_of_ne hj, one_mul, mul_one]

end Model

end TableBSymp

end CFSG.StandardType

end
