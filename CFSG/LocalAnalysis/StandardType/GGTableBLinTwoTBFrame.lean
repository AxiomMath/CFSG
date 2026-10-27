module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBData
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.LinTwoTB

open Polynomial Matrix Multiplicative CoordSL CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.StandardType.LinTwoTv

variable {K : Type} [Field K] [Finite K] {d : ℕ}

@[expose] noncomputable def glEquivSL (hK : Nat.card K = 2) :
    GL (Fin d) K ≃* SpecialLinearGroup (Fin d) K :=
  MulEquiv.ofBijective (TwoThree.toSLHom hK)
    ⟨fun A B h => Units.ext (congrArg Subtype.val h),
      fun s => ⟨SpecialLinearGroup.toGL s, Subtype.ext rfl⟩⟩

theorem wtGL_mulAut (hK : Nat.card K = 2) (hd : 3 ≤ d) (φ : MulAut (GL (Fin d) K))
    (B : GL (Fin d) K) : wtGL (φ B) = wtGL B := by
  classical
  set ρ : GL (Fin d) K ≃* projectiveSL d K :=
    (glEquivSL hK).trans (StandardType.LineL2.projEquivTwo hK) with hρ
  have hρconj : ∀ C : GL (Fin d) K, conjAut d K C = MulAut.conj (ρ C) := by
    intro C
    have h1 := conjAut_toGL (n := d) (K := K) (TwoThree.toSLHom hK C)
    rw [TwoThree.toGL_toSLHom] at h1
    exact h1
  obtain ⟨Θ, hΘw, hΘ⟩ := exists_rank_pres_hom hK hd (MulAut.congr ρ φ)
  have h1 : conjAut d K (φ B) = conjAut d K (Θ B) := by
    rw [← hΘ B, hρconj B, hρconj (φ B), TorusData.mulAut_conj_conj]
    simp [MulAut.congr_apply]
  have h2 : φ B = Θ B := TwoThree.conjAut_injective hK (by omega) h1
  rw [h2, hΘw]

theorem exists_move_invol (g : K[X]) [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (π : Equiv.Perm (Fin s))
    (σ : Fin s → (AdjoinRoot g ≃ₐ[K] AdjoinRoot g)) (hπ : ∀ i, π (π i) = i)
    (hσ : ∀ i x, σ i (σ (π i) x) = x) :
    ∃ M : Matrix (Fin n) (Fin n) K, M * M = 1 ∧ ∀ k k' : Fin s → ℕ,
      (∀ i, AdjoinRoot.root g ^ k i = σ i (AdjoinRoot.root g) ^ k' (π i)) →
        SLNS.nsMat ε (rootMat g) k * M = M * SLNS.nsMat ε (rootMat g) k' := by
  classical
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  set f : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (frameCoords g ε).symm.trans ((moveEquiv g π σ).trans (frameCoords g ε)) with hf
  set M₀ := LinearMap.toMatrix' (f : (Fin n → K) →ₗ[K] (Fin n → K)) with hM₀
  refine ⟨M₀, ?_, ?_⟩
  · have hff : ∀ v, f (f v) = v := by
      intro v
      obtain ⟨x, rfl⟩ := (frameCoords g ε).surjective v
      simp only [hf, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      have hmm : moveEquiv g π σ (moveEquiv g π σ x) = x := by
        refine Prod.ext (funext fun i => ?_) rfl
        change σ i (σ (π i) (x.1 (π (π i)))) = x.1 i
        rw [hπ i, hσ i]
      rw [hmm]
    rw [hM₀, ← LinearMap.toMatrix'_comp]
    have h1 : (f : (Fin n → K) →ₗ[K] (Fin n → K)).comp (f : (Fin n → K) →ₗ[K] (Fin n → K)) =
        LinearMap.id := LinearMap.ext hff
    rw [h1, LinearMap.toMatrix'_id]
  · intro k k' hk
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hM₀, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := (frameCoords g ε).surjective v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      nsMat_mulVec_frameCoords]
    simp only [hf, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [nsMat_mulVec_frameCoords]
    congr 1
    refine Prod.ext (funext fun i => ?_) rfl
    change AdjoinRoot.root g ^ k i * σ i (x.1 (π i)) =
      σ i (AdjoinRoot.root g ^ k' (π i) * x.1 (π i))
    rw [map_mul, map_pow, hk i]

theorem exists_frob (hK : Nat.card K = 2) {g : K[X]} [Fact (Irreducible g)]
    (hζ : AdjoinRoot.root g ^ 3 = 1) :
    ∃ σ : AdjoinRoot g ≃ₐ[K] AdjoinRoot g, σ (AdjoinRoot.root g) = AdjoinRoot.root g ^ 2 ∧
      ∀ x, σ (σ x) = x := by
  obtain ⟨σ, hσ⟩ := LineL2.neg_one_mem_galExp hK hζ
  have h2 : σ (AdjoinRoot.root g) = AdjoinRoot.root g ^ 2 := by
    have hv : (((-1 : (ZMod 3)ˣ) : ZMod 3)).val = 2 := by decide
    rw [hσ, hv]
  refine ⟨σ, h2, fun x => ?_⟩
  have h4 : AdjoinRoot.root g ^ 4 = AdjoinRoot.root g := by
    rw [show 4 = 3 + 1 from rfl, pow_succ, hζ, one_mul]
  have hroot : σ (σ (AdjoinRoot.root g)) = AdjoinRoot.root g := by
    rw [h2, map_pow, h2, ← pow_mul, h4]
  have hcomp : (σ : AdjoinRoot g →ₐ[K] AdjoinRoot g).comp (σ : AdjoinRoot g →ₐ[K] AdjoinRoot g) =
      AlgHom.id K (AdjoinRoot g) := by
    apply AdjoinRoot.algHom_ext
    exact hroot
  exact congrArg (fun f : AdjoinRoot g →ₐ[K] AdjoinRoot g => f x) hcomp

theorem root_pow_neg {K : Type} [Field K] {g : K[X]} (hζ : AdjoinRoot.root g ^ 3 = 1)
    (t : ZMod 3) :
    AdjoinRoot.root g ^ t.val = (AdjoinRoot.root g ^ 2) ^ (-t).val := by
  rw [← pow_mul, pow_eq_pow_mod _ hζ, pow_eq_pow_mod (2 * (-t).val) hζ]
  congr 1
  have : ∀ x : ZMod 3, x.val % 3 = (2 * (-x).val) % 3 := by decide
  exact this t

variable (hK : Nat.card K = 2)
include hK

theorem exists_torusData_with_rank_bound {E : Subgroup (GL (Fin d) K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ (d / 2) ≤ Nat.card E) :
    ∃ (s e : ℕ) (D : TorusData (GL (Fin d) K) s), D.ι.range = E ∧ s ≤ d / 2 ∧ 0 < e ∧
      ∀ v, wtGL (D.el v) = e * hamWt v := by
  classical
  have hchar : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three K
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; decide
  have hC : (rootMat g).det = 1 := det_rootMat Nat.prime_three hnsplit hp3 hgd
  have hCp : rootMat g ^ 3 = 1 := rootMat_pow_eq_one Nat.prime_three hp3 hgd
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (root_isPrimitiveRoot Nat.prime_three hp3 hgd).pow_eq_one
  have hunit : ∀ j : ℕ, ¬ 3 ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1) := fun j hj c =>
    isUnit_rootMat_pow_sub Nat.prime_three hnsplit hp3 hgd j hj c
  have he2 : 2 ≤ (rootPB g).dim := two_le_rootPB_dim (fun c => hunit 1 (by decide) c)
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame g Nat.prime_three hp3 hgd
    (Set.range fun x : E => ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have h := congrArg (fun z : GL (Fin d) K => (z : Matrix (Fin d) (Fin d) K))
        (TableB.IsElemAbelian.comm hE x.2 y.2)
      simpa [Commute, SemiconjBy, Units.val_mul] using h)
    (by
      rintro _ ⟨x, rfl⟩
      have h1 := hE.2 (x : GL (Fin d) K) x.2
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
  set ι := frameHom (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin d) K →* GL (Fin d) K) A₀
    ε hC hCp with hι
  have hιinj : Function.Injective ι := by
    refine frameHom_injective _ A₀ ε hC hCp ?_ (rootPB_dim_pos g) hunit
    intro x hx
    have : x = 1 := by
      apply Subtype.ext
      have := congrArg Units.val (MonoidHom.mem_ker.mp hx)
      simpa using this
    rw [this]
    exact Subgroup.one_mem _
  have hEle : E ≤ ι.range := by
    intro b hb
    obtain ⟨k, hk⟩ := hframe _ ⟨⟨b, hb⟩, rfl⟩
    refine ⟨ofAdd fun i => (k i : ZMod 3), ?_⟩
    rw [hι, frameHom_natCast, SLRep.ggFrame_apply]
    apply Units.ext
    have h2 : (A₀ : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    change (A₀ : Matrix (Fin d) (Fin d) K) * SLNS.nsMat ε (rootMat g) k *
      ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (b : Matrix (Fin d) (Fin d) K)
    have hk' : (b : Matrix (Fin d) (Fin d) K) * (A₀ : Matrix (Fin d) (Fin d) K) =
        (A₀ : Matrix (Fin d) (Fin d) K) * SLNS.nsMat ε (rootMat g) k := hk
    rw [← hk', Matrix.mul_assoc, h2, Matrix.mul_one]
  have hcardι : Nat.card ι.range = 3 ^ s := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have hsd : s ≤ d / 2 := by
    have hcd : Fintype.card (Fin d) = Fintype.card ((Fin (rootPB g).dim × Fin s) ⊕ Fin r) :=
      Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at hcd
    have : 2 * s ≤ d := by nlinarith
    omega
  have hEeq : E = ι.range := by
    apply Subgroup.eq_of_le_of_card_ge hEle
    rw [hcardι]
    exact (Nat.pow_le_pow_right (by norm_num) hsd).trans hcard
  have hlift : ∀ (π : Equiv.Perm (Fin s)) (σ : Fin s → (AdjoinRoot g ≃ₐ[K] AdjoinRoot g)),
      (∀ i, π (π i) = i) → (∀ i x, σ i (σ (π i) x) = x) →
      ∃ L : GL (Fin d) K, L * L = 1 ∧ ∀ t t' : Fin s → ZMod 3,
        (∀ i, AdjoinRoot.root g ^ (t i).val = σ i (AdjoinRoot.root g) ^ (t' (π i)).val) →
        L * ι (ofAdd t) * L⁻¹ = ι (ofAdd t') := by
    intro π σ hπ hσ
    obtain ⟨M, hMM, hM⟩ := exists_move_invol g ε π σ hπ hσ
    set Ai : Matrix (Fin d) (Fin d) K :=
      ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) with hAi
    set Am : Matrix (Fin d) (Fin d) K := (A₀ : Matrix (Fin d) (Fin d) K) with hAm
    have hAiA : Ai * Am = 1 := by
      rw [hAi, hAm, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hLL : (Am * M * Ai) * (Am * M * Ai) = 1 := by
      have hAAi : Am * Ai = 1 := by
        rw [hAi, hAm, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one]
      calc (Am * M * Ai) * (Am * M * Ai) = Am * M * (Ai * Am) * M * Ai := by
            simp only [Matrix.mul_assoc]
        _ = Am * (M * M) * Ai := by rw [hAiA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = 1 := by rw [hMM, Matrix.mul_one, hAAi]
    set L : GL (Fin d) K := ⟨Am * M * Ai, Am * M * Ai, hLL, hLL⟩ with hL
    have hLsq : L * L = 1 := Units.ext hLL
    refine ⟨L, hLsq, fun t t' ht => ?_⟩
    have hLinv : L⁻¹ = L := inv_eq_of_mul_eq_one_right hLsq
    rw [hLinv]
    apply Units.ext
    have hmat : ((L * ι (ofAdd t) * L : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (Am * M * Ai) * (Am * SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * Ai) *
          (Am * M * Ai) := by
      rw [Units.val_mul, Units.val_mul, hι, coe_frameHom_toGL ε A₀ hC hCp t]
    have hMN : SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * M =
        M * SLNS.nsMat ε (rootMat g) (fun i => (t' i).val) :=
      hM _ _ fun i => ht i
    have e1 : M * SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * M =
        SLNS.nsMat ε (rootMat g) (fun i => (t' i).val) := by
      calc M * SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * M
          = M * (SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * M) := Matrix.mul_assoc _ _ _
        _ = M * (M * SLNS.nsMat ε (rootMat g) (fun i => (t' i).val)) := by rw [hMN]
        _ = (M * M) * SLNS.nsMat ε (rootMat g) (fun i => (t' i).val) :=
            (Matrix.mul_assoc _ _ _).symm
        _ = SLNS.nsMat ε (rootMat g) (fun i => (t' i).val) := by rw [hMM, Matrix.one_mul]
    rw [hmat]
    show _ = ((ι (ofAdd t') : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
    rw [hι, coe_frameHom_toGL ε A₀ hC hCp t', ← e1]
    calc (Am * M * Ai) * (Am * SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * Ai) *
          (Am * M * Ai)
        = Am * M * (Ai * Am) * SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * (Ai * Am) * M *
            Ai := by simp only [Matrix.mul_assoc]
      _ = Am * (M * SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * M) * Ai := by
          rw [hAiA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [e1]
  obtain ⟨frob, hfrob, hfrob2⟩ := exists_frob hK hζ
  have hsg : ∀ i : Fin s, ∃ L : GL (Fin d) K, L * L = 1 ∧ ∀ t : Fin s → ZMod 3,
      L * ι (ofAdd t) * L⁻¹ = ι (ofAdd (signV i t)) := by
    intro i
    obtain ⟨L, hL, hLt⟩ := hlift 1 (fun j => if j = i then frob else AlgEquiv.refl)
      (fun _ => rfl) (fun j x => by
        by_cases hj : j = i
        · simp only [hj, if_true, Equiv.Perm.coe_one, id_eq]
          exact hfrob2 x
        · simp [hj])
    refine ⟨L, hL, fun t => hLt t _ (fun j => ?_)⟩
    by_cases hj : j = i
    · subst hj
      simp only [if_true, Equiv.Perm.coe_one, id_eq, hfrob, signV_self]
      exact root_pow_neg hζ (t j)
    · simp [hj, signV_of_ne hj]
  have hsw : ∀ i j : Fin s, ∃ L : GL (Fin d) K, L * L = 1 ∧ ∀ t : Fin s → ZMod 3,
      L * ι (ofAdd t) * L⁻¹ = ι (ofAdd (swapV i j t)) := by
    intro i j
    obtain ⟨L, hL, hLt⟩ := hlift (Equiv.swap i j) (fun _ => AlgEquiv.refl)
      (fun k => Equiv.swap_apply_self i j k) (fun _ _ => rfl)
    refine ⟨L, hL, fun t => hLt t _ (fun k => ?_)⟩
    simp [swapV, Equiv.swap_apply_self]
  choose Lg hLg2 hLg using hsg
  choose Lw hLw2 hLw using hsw
  exact ⟨s, (rootPB g).dim, ⟨ι, hιinj, Lg, hLg2, hLg, Lw, hLw2, hLw⟩, hEeq.symm, hsd,
    rootPB_dim_pos g, fun v => wtGL_frameHom hK hp3 hgd ε A₀ hC hCp v⟩

theorem exists_torusData {E : Subgroup (GL (Fin d) K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ (d / 2) ≤ Nat.card E) :
    ∃ (s e : ℕ) (D : TorusData (GL (Fin d) K) s), D.ι.range = E ∧ 0 < e ∧
      ∀ v, wtGL (D.el v) = e * hamWt v := by
  obtain ⟨s, e, D, hD, _hsd, he, hwt⟩ :=
    exists_torusData_with_rank_bound hK hE hcard
  exact ⟨s, e, D, hD, he, hwt⟩

end CFSG.StandardType.LinTwoTB

end
