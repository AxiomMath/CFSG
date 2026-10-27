module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRestSp
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSpFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestPlane
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Witt

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Symplectic

open TauCeti.GLSymplecticFin (RootSubgroupIndex)

namespace RootPlaneSp

variable {F : Type} [Field F] {n e s r : ℕ}

@[expose] def SpBlockMat (A₀ : GL (Fin n ⊕ Fin n) F) (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    (C : Matrix (Fin e) (Fin e) F) (X : StatedSp n F) (k : Fin s → ℕ) : Prop :=
  ((X : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
    (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (SLNS.nsCore C k).submatrix ε ε *
      ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)

@[expose] def PlaneSupp (k : Fin s → ℕ) : Prop :=
  ∀ i : Fin s, 2 ≤ (i : ℕ) → k i = 0

theorem planeSupp_planeExp {p : ℕ} (hs : 2 ≤ s) (a : ZMod p × ZMod p) :
    PlaneSupp (RestSL.planeExp (⟨0, by omega⟩ : Fin s) ⟨1, by omega⟩ a) := by
  intro i hi
  refine RestSL.planeExp_eq_zero_of_ne ?_ ?_ a
  · intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  · intro h
    have := congrArg Fin.val h
    simp only at this
    omega

open CFSG.ClassicalInvolution.Models.SymplecticPairs (form form_mulVec form_antisymm
  exists_sp_apply_eq sgn par sgn_inl sgn_inr par_inl par_inr par_par)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt elt)

section Root

variable {K : Type} [Field K]

theorem mul_single_mul_apply' {ι : Type} [Fintype ι] [DecidableEq ι] (P R : Matrix ι ι K)
    (a b : ι) (c : K) (x y : ι) : (P * Matrix.single a b c * R) x y = P x a * c * R b y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [Matrix.single_apply_same]
    · intro k _ hk
      rw [Matrix.single_apply_of_row_ne hk.symm, mul_zero]
    · simp
  · intro k _ hk
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro l _
    rw [Matrix.single_apply_of_col_ne _ _ hk.symm, mul_zero]
  · simp

theorem form_single_inl_left {m : ℕ} (z : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    form (Pi.single (Sum.inl 0) (1 : K)) z = z (Sum.inr 0) := by
  rw [form_antisymm, CFSG.ClassicalInvolution.Models.SymplecticPairs.form_single_right, par_inl,
    sgn_inr]
  ring

theorem elt_positiveLong_commute {m : ℕ} (h : StatedSp (m + 1) K)
    (hh : mat (m + 1) K h *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1) (c : K) :
    h * elt (.positiveLong 0) c = elt (.positiveLong 0) c * h := by
  classical
  apply mat_injective
  have hcol : ∀ i, mat (m + 1) K h i (Sum.inl 0) =
      (Pi.single (Sum.inl 0) (1 : K) : Fin (m + 1) ⊕ Fin (m + 1) → K) i := by
    intro i
    have := congrFun hh i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  have hrow : ∀ j, mat (m + 1) K h (Sum.inr 0) j =
      (Pi.single j (1 : K) : Fin (m + 1) ⊕ Fin (m + 1) → K) (Sum.inr 0) := by
    intro j
    have h1 := form_mulVec h (Pi.single (Sum.inl 0) 1) (Pi.single j 1)
    rw [hh, form_single_inl_left, form_single_inl_left, Matrix.mulVec_single_one,
      Matrix.col_apply] at h1
    exact h1
  have key : mat (m + 1) K h * Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K) =
      Matrix.single (Sum.inl 0) (Sum.inr 0) 1 * mat (m + 1) K h := by
    ext x y
    have e1 := mul_single_mul_apply' (mat (m + 1) K h) 1 (Sum.inl 0) (Sum.inr 0) (1 : K) x y
    have e2 := mul_single_mul_apply' 1 (mat (m + 1) K h) (Sum.inl 0) (Sum.inr 0) (1 : K) x y
    rw [Matrix.mul_one] at e1
    rw [Matrix.one_mul] at e2
    rw [e1, e2, hcol, hrow]
    simp only [Pi.single_apply, Matrix.one_apply]
  rw [map_mul, map_mul, mat_elt]
  change mat (m + 1) K h * (1 + c • Matrix.single (Sum.inl 0) (Sum.inr 0) 1) =
    (1 + c • Matrix.single (Sum.inl 0) (Sum.inr 0) 1) * mat (m + 1) K h
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, key]

theorem exists_conj_root_commute {m : ℕ} {v : Fin (m + 1) ⊕ Fin (m + 1) → K} (hv : v ≠ 0) :
    ∃ u : StatedSp (m + 1) K, ∀ X : StatedSp (m + 1) K, mat (m + 1) K X *ᵥ v = v → ∀ c : K,
      X * (u * elt (.positiveLong 0) c * u⁻¹) = u * elt (.positiveLong 0) c * u⁻¹ * X := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra h
    exact hv (funext fun a => not_not.mp fun ha => h ⟨a, ha⟩)
  have hsgn : sgn K a ≠ 0 := by
    rcases a with i | i
    · rw [sgn_inl]
      exact one_ne_zero
    · rw [sgn_inr]
      exact neg_ne_zero.mpr one_ne_zero
  set w : Fin (m + 1) ⊕ Fin (m + 1) → K := (v a * sgn K a)⁻¹ • Pi.single (par a) 1 with hw
  have hvw : form v w = 1 := by
    have hlin : form v w = (v a * sgn K a)⁻¹ * form v (Pi.single (par a) 1) := by
      rw [hw, CFSG.ClassicalInvolution.Models.SymplecticPairs.form, Matrix.mulVec_smul,
        dotProduct_smul, smul_eq_mul, CFSG.ClassicalInvolution.Models.SymplecticPairs.form]
    rw [hlin, CFSG.ClassicalInvolution.Models.SymplecticPairs.form_single_right, par_par]
    exact inv_mul_cancel₀ (mul_ne_zero ha hsgn)
  obtain ⟨g, hg, -⟩ := exists_sp_apply_eq v w hvw
  refine ⟨g, fun X hX c => ?_⟩
  have hh : mat (m + 1) K (g⁻¹ * X * g) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 := by
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec, hX, ← hg,
      Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  have hc := elt_positiveLong_commute (g⁻¹ * X * g) hh c
  calc X * (g * elt (.positiveLong 0) c * g⁻¹) =
      g * ((g⁻¹ * X * g) * elt (.positiveLong 0) c) * g⁻¹ := by group
    _ = g * (elt (.positiveLong 0) c * (g⁻¹ * X * g)) * g⁻¹ := by rw [hc]
    _ = g * elt (.positiveLong 0) c * g⁻¹ * X := by group

end Root

section Fix

variable {K : Type} [Field K] {n e s r : ℕ}

theorem nsCore_col_of_zero {C : Matrix (Fin e) (Fin e) K} {k : Fin s → ℕ} {j : Fin s}
    (hj : k j = 0) (x₀ : Fin e) (c : (Fin e × Fin s) ⊕ Fin r) :
    SLNS.nsCore (r := r) C k c (Sum.inl (x₀, j)) = if c = Sum.inl (x₀, j) then 1 else 0 := by
  rcases c with ⟨x, i⟩ | u
  · simp only [SLNS.nsCore, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [hj, pow_zero]
      by_cases hx : x = x₀
      · subst hx
        simp
      · simp [hx, Matrix.one_apply_ne hx]
    · simp [hij]
  · simp [SLNS.nsCore, Matrix.fromBlocks_apply₂₁]

theorem fix_of_zero {A₀ : GL (Fin n ⊕ Fin n) K} {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r}
    {C : Matrix (Fin e) (Fin e) K} {X : StatedSp n K} {k : Fin s → ℕ} (hX : SpBlockMat A₀ ε C X k)
    {j : Fin s} (hj : k j = 0) (x₀ : Fin e) :
    mat n K X *ᵥ ((A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      Pi.single (ε.symm (Sum.inl (x₀, j))) 1) =
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
        Pi.single (ε.symm (Sum.inl (x₀, j))) 1 := by
  classical
  have hA : ((A₀⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hN : (SLNS.nsCore C k).submatrix ε ε *ᵥ
      (Pi.single (ε.symm (Sum.inl (x₀, j))) 1 : Fin n ⊕ Fin n → K) =
      Pi.single (ε.symm (Sum.inl (x₀, j))) 1 := by
    funext a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply,
      nsCore_col_of_zero hj, Pi.single_apply]
    by_cases ha : a = ε.symm (Sum.inl (x₀, j))
    · rw [ha, Equiv.apply_symm_apply]
      simp
    · have hne : ε a ≠ Sum.inl (x₀, j) := fun h => ha (by rw [← h, Equiv.symm_apply_apply])
      simp [ha, hne]
  calc mat n K X *ᵥ ((A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
        Pi.single (ε.symm (Sum.inl (x₀, j))) 1) =
      ((A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * (SLNS.nsCore C k).submatrix ε ε *
        ((A₀⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) *ᵥ
        ((A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
          Pi.single (ε.symm (Sum.inl (x₀, j))) 1) := by
        rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, hX]
    _ = (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ ((SLNS.nsCore C k).submatrix ε ε *ᵥ
        ((((A₀⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) *ᵥ
            Pi.single (ε.symm (Sum.inl (x₀, j))) 1)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [hA, Matrix.one_mulVec, hN]

end Fix

end RootPlaneSp

@[expose] def GGSpNonsplitPlaneInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n e s r p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card F - 1 → 2 ≤ e → 4 ≤ s →
    ∀ (C : Matrix (Fin e) (Fin e) F) (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
      (A₀ : GL (Fin n ⊕ Fin n) F), C ^ p = 1 →
      (∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) →
      (∀ k : Fin s → ℕ, ∃ X : StatedSp n F, RootPlaneSp.SpBlockMat A₀ ε C X k) →
      (∃ (ρ : RootSubgroupIndex n) (u : StatedSp n F), ∀ (X : StatedSp n F) (k : Fin s → ℕ),
          RootPlaneSp.PlaneSupp k → RootPlaneSp.SpBlockMat A₀ ε C X k → ∀ c : F,
            X * (u * SpExtras.elt ρ c * u⁻¹) = u * SpExtras.elt ρ c * u⁻¹ * X) ∧
      ∀ (X : StatedSp n F) (k : Fin s → ℕ), RootPlaneSp.PlaneSupp k →
        RootPlaneSp.SpBlockMat A₀ ε C X k → X ≠ 1 →
        ∃ L : Subgroup (StatedSp n F), IsComponentOf L (Subgroup.centralizer {X}) ∧
          ∀ (Y : StatedSp n F) (k' : Fin s → ℕ), RootPlaneSp.SpBlockMat A₀ ε C Y k' →
            Y ∈ Subgroup.centralizer (L : Set (StatedSp n F)) →
              ∀ i : Fin s, 2 ≤ (i : ℕ) → p ∣ k' i

@[expose] def GGSpNonsplitCompInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n e s r p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card F - 1 → 2 ≤ e → 4 ≤ s →
    ∀ (C : Matrix (Fin e) (Fin e) F) (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
      (A₀ : GL (Fin n ⊕ Fin n) F), C ^ p = 1 →
      (∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) →
      (∀ k : Fin s → ℕ, ∃ X : StatedSp n F, RootPlaneSp.SpBlockMat A₀ ε C X k) →
      ∀ (X : StatedSp n F) (k : Fin s → ℕ), RootPlaneSp.PlaneSupp k →
        RootPlaneSp.SpBlockMat A₀ ε C X k → X ≠ 1 →
        ∃ L : Subgroup (StatedSp n F), IsComponentOf L (Subgroup.centralizer {X}) ∧
          ∀ (Y : StatedSp n F) (k' : Fin s → ℕ), RootPlaneSp.SpBlockMat A₀ ε C Y k' →
            Y ∈ Subgroup.centralizer (L : Set (StatedSp n F)) →
              ∀ i : Fin s, 2 ≤ (i : ℕ) → p ∣ k' i

theorem ggSpNonsplitPlaneInput_of_comp (hC : GGSpNonsplitCompInput) : GGSpNonsplitPlaneInput := by
  intro F _ _ _ n e s r p hp hp2 hns he hs C ε A₀ hCp hcunit hreal
  refine ⟨?_, hC F n e s r p hp hp2 hns he hs C ε A₀ hCp hcunit hreal⟩
  have hcardn : n + n = e * s + r := by
    have := Fintype.card_congr ε
    simpa [Fintype.card_sum, Fintype.card_prod, mul_comm] using this
  have h8 : 2 * 4 ≤ e * s := Nat.mul_le_mul he hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set w : Fin (m + 1) ⊕ Fin (m + 1) → F :=
    Pi.single (ε.symm (Sum.inl ((⟨0, by omega⟩ : Fin e), (⟨2, by omega⟩ : Fin s)))) 1 with hw
  have hv : (A₀ : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) *ᵥ w ≠ 0 := by
    intro h0
    have hA : ((A₀⁻¹ : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
        Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) *
        (A₀ : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h1 := congrArg (fun z => ((A₀⁻¹ : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
      Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) *ᵥ z) h0
    simp only [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    have h2 := congrFun h1 (ε.symm (Sum.inl ((⟨0, by omega⟩ : Fin e), (⟨2, by omega⟩ : Fin s))))
    simp [hw] at h2
  obtain ⟨u, hu⟩ := RootPlaneSp.exists_conj_root_commute hv
  exact ⟨.positiveLong 0, u, fun X k hk hX c =>
    hu X (RootPlaneSp.fix_of_zero hX (hk _ (le_refl 2)) _) c⟩

section Inputs

theorem RootPlaneSp.rootPlane_psp_nonsplit (hF : GGSpNonsplitFrameInput)
    (hM : GGSpNonsplitPlaneInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (Symplectic.rootDatum n (GaloisField 2 f)) .PSp n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hns : ¬ p ∣ 2 ^ f - 1) :
    ∃ (E : Subgroup G) (γ : Fin (Symplectic.rootDatum n (GaloisField 2 f)).rank → ℤ)
      (u : StatedSp n (GaloisField 2 f)) (r : G),
        E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        GGRootClass (Symplectic.rootDatum n (GaloisField 2 f)) .PSp γ ∧
        E ≤ Subgroup.centralizer
          (ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ γ u : Set G) ∧
        r ∈ ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ γ u ∧ orderOf r = 2 ∧
        ∀ e ∈ E, e ≠ 1 → e ∈ D ∨ ∃ L₁ : Subgroup G,
          IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  have hrk : 2 ≤ n := hctx.2.2.2.1.2
  have : NeZero n := ⟨by omega⟩
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hpp := hctx.prime
  have hp2 := hctx.ne_two
  have : NeZero p := ⟨hpp.ne_zero⟩
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [AutPSp.center_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
  have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  have hcard : p ^ 4 ≤ Nat.card Bs :=
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hr4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  obtain ⟨e, s, r, C, ε, A₀, hCp, hcunit, hreal, hframe⟩ :=
    hF G p B Bs x L D J n f ψ hctx s1.1 hns
  have hcongr : ∀ {b : G} {k k' : Fin s → ℕ}, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k →
      (∀ i, k i % p = k' i % p) → NoOffPSLRest.SpFrameRep ψ A₀ ε C b k' := by
    rintro b k k' ⟨X, hX1, hX2⟩ hkk
    exact ⟨X, hX1, by rw [hX2, NoOffPSLRest.nsCore_congr hCp hkk]⟩
  have hone : NoOffPSLRest.SpFrameRep ψ A₀ ε C 1 0 := by
    refine ⟨1, (map_one ψ).symm, ?_⟩
    rw [SLNS.nsCore_zero, Matrix.submatrix_one_equiv, Matrix.mul_one, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
    rfl
  have he0 : e ≠ 0 := by
    intro he0
    have hsub : Bs ≤ ⊥ := fun b hb => by
      obtain ⟨k, X, rfl, hX⟩ := hframe b hb
      have hX1 : X = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [hX, NoOffPSLRest.nsCore_eq_one_of_e_zero he0, Matrix.submatrix_one_equiv,
          Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      rw [hX1, map_one]
      exact Subgroup.one_mem _
    have h1 : Nat.card Bs ≤ 1 := by
      have := Subgroup.card_le_of_le hsub
      rwa [Subgroup.card_bot] at this
    have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) hpp.one_lt
    omega
  have he2 : 2 ≤ e := by
    by_contra he
    obtain rfl : e = 1 := by omega
    have hu := hcunit 1 (Nat.Prime.not_dvd_one hpp) (C 0 0)
    have h0 : C ^ 1 - C 0 0 • (1 : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) = 0 := by
      ext a b
      rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
      simp
    rw [h0] at hu
    exact not_isUnit_zero hu
  have hinjBs : Function.Injective (fun b : Bs => fun i : Fin s =>
      ((NoOffPSLRest.spExp ψ A₀ ε C b i : ℕ) : ZMod p)) := by
    intro b b' hbb
    have hb := NoOffPSLRest.spExp_spec (hframe b b.2)
    have hb' := NoOffPSLRest.spExp_spec (hframe b' b'.2)
    have hmod : ∀ i, NoOffPSLRest.spExp ψ A₀ ε C b' i % p =
        NoOffPSLRest.spExp ψ A₀ ε C b i % p := by
      intro i
      have := congrFun hbb i
      simp only at this
      rw [ZMod.natCast_eq_natCast_iff'] at this
      exact this.symm
    exact Subtype.ext (hb.eq (hcongr hb' hmod))
  have hBsle : Nat.card Bs ≤ p ^ s := by
    calc Nat.card Bs ≤ Nat.card (Fin s → ZMod p) := Nat.card_le_card_of_injective _ hinjBs
      _ = p ^ s := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin s),
          Fintype.card_fin]
  have hs4 : 4 ≤ s := (Nat.pow_le_pow_iff_right hpp.one_lt).mp (hcard.trans hBsle)
  set i₀ : Fin s := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin s := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [hi₀, hi₁] at this
  choose bOf hbOf hbRep using fun a : ZMod p × ZMod p => hreal (RestSL.planeExp i₀ i₁ a)
  let θ : Multiplicative (ZMod p × ZMod p) →* G :=
    { toFun := fun a => bOf (Multiplicative.toAdd a)
      map_one' := by
        have h0 : NoOffPSLRest.SpFrameRep ψ A₀ ε C 1
            (RestSL.planeExp i₀ i₁ (0 : ZMod p × ZMod p)) := by
          rw [RestSL.planeExp_zero]
          exact hone
        exact (hbRep 0).eq h0
      map_mul' := fun a b => by
        have h := (hbRep (Multiplicative.toAdd a)).mul (hbRep (Multiplicative.toAdd b))
        exact (hbRep (Multiplicative.toAdd a + Multiplicative.toAdd b)).eq
          (hcongr h fun i => (RestSL.planeExp_add_mod i₀ i₁ _ _ i).symm) }
  have hθ : ∀ a, θ a = bOf (Multiplicative.toAdd a) := fun a => rfl
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hrep := hbRep (Multiplicative.toAdd a)
    rw [← hθ, ha] at hrep
    have hmod := fun i => NoOffPSLRest.SpFrameRep.mod_eq hψ he0 hpp.pos hCp hcunit hrep hone i
    have hv0 : (Multiplicative.toAdd a).1.val = 0 := by
      have h1 := hmod i₀
      rw [RestSL.planeExp_left, Pi.zero_apply, Nat.zero_mod,
        Nat.mod_eq_of_lt (ZMod.val_lt _)] at h1
      exact h1
    have hv1 : (Multiplicative.toAdd a).2.val = 0 := by
      have h1 := hmod i₁
      rw [RestSL.planeExp_right h01, Pi.zero_apply, Nat.zero_mod,
        Nat.mod_eq_of_lt (ZMod.val_lt _)] at h1
      exact h1
    have h0 : Multiplicative.toAdd a = 0 :=
      Prod.ext ((ZMod.val_eq_zero _).mp hv0) ((ZMod.val_eq_zero _).mp hv1)
    rw [← ofAdd_toAdd a, h0, ofAdd_zero]
  have hpow : ∀ a : Multiplicative (ZMod p × ZMod p), a ^ p = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext <;> simp [nsmul_eq_mul]
  have hEcard : Nat.card θ.range = p ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv]
    change Nat.card (ZMod p × ZMod p) = p ^ 2
    rw [Nat.card_prod, Nat.card_zmod, sq]
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hnsF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [hcardF]
    exact hns
  have hrealX : ∀ k : Fin s → ℕ, ∃ X : StatedSp n (GaloisField 2 f),
      RootPlaneSp.SpBlockMat A₀ ε C X k := by
    intro k
    obtain ⟨b, -, X, -, hX⟩ := hreal k
    exact ⟨X, hX⟩
  obtain ⟨⟨ρ, u, hρu⟩, hcomp⟩ :=
    hM (GaloisField 2 f) n e s r p hpp hp2 hnsF he2 hs4 C ε A₀ hCp hcunit hrealX
  have hsupp : ∀ a : ZMod p × ZMod p, RootPlaneSp.PlaneSupp (RestSL.planeExp i₀ i₁ a) :=
    RootPlaneSp.planeSupp_planeExp (by omega)
  obtain ⟨γ, hγ, hγr⟩ := CFSG.LieType.Steinberg.Sp.exists_root_of_stdVec ρ
  have hroot : ∀ z, z ∈ Symplectic.rootGroup n (GaloisField 2 f) γ ↔
      ∃ c : GaloisField 2 f, z = SpExtras.elt ρ c := fun z => SpExtras.mem_rootGroup_iff hγr.symm
  have hmapC : ∀ X : StatedSp n (GaloisField 2 f),
      (Subgroup.centralizer {X}).map ψ = ψ.range ⊓ Subgroup.centralizer {ψ X} := by
    intro X
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hψ (by rw [map_mul, map_mul]; exact hy), rfl⟩
  refine ⟨θ.range, γ, u, ψ (u * SpExtras.elt ρ 1 * u⁻¹), ?_, ?_, hEcard, ⟨hγ, fun h => ?_⟩, ?_,
    ⟨_, ⟨SpExtras.elt ρ 1, (hroot _).mpr ⟨1, rfl⟩, rfl⟩, rfl⟩,
    RestSp.orderOf_psi_conj_elt ψ hker u ρ, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hbOf _
  · refine ⟨⟨⟨fun v w => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, rfl⟩ := v
      obtain ⟨_, b, rfl⟩ := w
      apply Subtype.ext
      change θ a * θ b = θ b * θ a
      rw [← map_mul, ← map_mul, mul_comm a b]
    · rintro _ ⟨a, rfl⟩
      change θ a ^ p = 1
      rw [← map_pow, hpow a, map_one]
  · rcases h with h | h | h <;> cases h
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (hroot z).mp hz
    obtain ⟨X, hX1, hX2⟩ := hbRep (Multiplicative.toAdd a)
    change ψ (u * SpExtras.elt ρ c * u⁻¹) * θ a = θ a * ψ (u * SpExtras.elt ρ c * u⁻¹)
    rw [hθ, hX1, ← map_mul, ← map_mul, hρu X _ (hsupp _) hX2 c]
  · rintro _ ⟨a, rfl⟩ hb1
    obtain ⟨X, hX1, hX2⟩ := hbRep (Multiplicative.toAdd a)
    have hθa : θ a = ψ X := hX1
    have hX1ne : X ≠ 1 := by
      rintro rfl
      exact hb1 (hθa.trans (map_one ψ))
    obtain ⟨L₀, hL₀, hL₀c⟩ := hcomp X _ (hsupp _) hX2 hX1ne
    refine Or.inr ⟨L₀.map ψ, ?_, ?_⟩
    · have h1 := isComponentOf_map_of_injective ψ hψ hL₀
      rw [hmapC, hctx.range_eq, ← hθa] at h1
      exact h1
    · refine le_trans (Subgroup.card_le_of_le ?_) hEcard.le
      rintro b' ⟨hb'B, hb'C⟩
      obtain ⟨k', Y, hY1, hY2⟩ := hframe b' hb'B
      have hYc : Y ∈ Subgroup.centralizer (L₀ : Set (StatedSp n (GaloisField 2 f))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        apply hψ
        have := (Subgroup.mem_centralizer_iff.mp hb'C) (ψ l) ⟨l, hl, rfl⟩
        rw [map_mul, map_mul, ← hY1]
        exact this
      have hdvd := hL₀c Y k' hY2 hYc
      refine ⟨Multiplicative.ofAdd (((k' i₀ : ℕ) : ZMod p), ((k' i₁ : ℕ) : ZMod p)), ?_⟩
      change bOf (((k' i₀ : ℕ) : ZMod p), ((k' i₁ : ℕ) : ZMod p)) = b'
      refine (hbRep _).eq (hcongr ⟨Y, hY1, hY2⟩ fun i => ?_)
      by_cases hi0 : i = i₀
      · rw [hi0, RestSL.planeExp_left, ZMod.val_natCast, Nat.mod_mod]
      · by_cases hi1 : i = i₁
        · rw [hi1, RestSL.planeExp_right h01, ZMod.val_natCast, Nat.mod_mod]
        · rw [RestSL.planeExp_eq_zero_of_ne hi0 hi1, Nat.zero_mod]
          have h2 : 2 ≤ (i : ℕ) := by
            have h0' : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext (by rw [h]))
            have h1' : (i : ℕ) ≠ 1 := fun h => hi1 (Fin.ext (by rw [h]))
            omega
          exact Nat.mod_eq_zero_of_dvd (hdvd i h2)

theorem ggRootPlaneInputOn_PSpNonsplit_of_frame (hF : GGSpNonsplitFrameInput)
    (hM : GGSpNonsplitPlaneInput) : GGRootPlaneInputOn GGPSpNonsplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1
  obtain ⟨rfl, hns⟩ := hP
  exact RootPlaneSp.rootPlane_psp_nonsplit hF hM (ψ := ψ) hctx s1 hns

theorem ggRootPlaneInputOn_PSpNonsplit_of_frame_comp (hF : GGSpNonsplitFrameInput)
    (hC : GGSpNonsplitCompInput) : GGRootPlaneInputOn GGPSpNonsplit :=
  ggRootPlaneInputOn_PSpNonsplit_of_frame hF (ggSpNonsplitPlaneInput_of_comp hC)

theorem ggRootPlaneAt_PSp_of_frame_plane (hF : GGSpNonsplitFrameInput)
    (hM : GGSpNonsplitPlaneInput) : GGRootPlaneAt .PSp :=
  ggRootPlaneAt_PSp_of_nonsplit (ggRootPlaneInputOn_PSpNonsplit_of_frame hF hM)

end Inputs

end CFSG.StandardType
