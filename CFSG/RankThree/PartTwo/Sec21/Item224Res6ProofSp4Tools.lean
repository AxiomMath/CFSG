module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofWt
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofTools
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.RankThree.PartTwo.KFacts.KP14Monomial
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofTv

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open Matrix CFSG.LieType.BorelTits Module
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Classical
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {F : Type} [Field F]

theorem eq_one_of_commute_E9_sp4 [Finite F] [CharP F 2] {ζ : F} (hζ : IsPrimitiveRoot ζ 3)
    (E₀ : Subgroup (StatedSp 2 F)) (hcard : Nat.card E₀ = 9) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) {s : StatedSp 2 F}
    (hs : ∀ e ∈ E₀, s * e = e * s) {k : ℕ} (hk : s ^ 2 ^ k = 1) : s = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Fintype E₀ := Fintype.ofFinite _
  let : CommGroup E₀ :=
    { (inferInstance : Group E₀) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  set ρ : E₀ →* Module.End F (Fin 2 ⊕ Fin 2 → F) := (natRep (StatedSp 2 F)).comp E₀.subtype
    with hρdef
  have : Finite (Additive E₀) := Finite.of_equiv E₀ Additive.ofMul
  have : Finite (Additive E₀ →+ ZMod 3) := Finite.of_injective _ DFunLike.coe_injective
  let : Fintype (Additive E₀ →+ ZMod 3) := Fintype.ofFinite _
  have hσζ : (spForm 2 F).σ ζ = ζ := rfl
  have hρ : ∀ g u v, (spForm 2 F).β (ρ g u) (ρ g v) = (spForm 2 F).β u v := fun g u v =>
    isIsometric_natRep_statedSp 2 F (g : StatedSp 2 F) u v
  have hexpΓ : ∀ g : E₀, g ^ 3 = 1 := fun g => Subtype.ext (hexp g g.2)
  have hΓ : (Fintype.card E₀ : F) ≠ 0 := by
    rw [Fintype.card_eq_nat_card, hcard]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h9 : ((9 : ℕ) : F) = 1 := by
      rw [Nat.cast_ofNat]
      linear_combination 4 * h2
    rw [h9]
    exact one_ne_zero
  have hfaith : ∀ g : E₀, ρ g = 1 → g = 1 := by
    intro g hg
    apply Subtype.ext
    apply natRep_injective (StatedSp 2 F)
    rw [Subgroup.coe_one, map_one]
    exact hg
  have hdim : finrank F (Fin 2 ⊕ Fin 2 → F) = 4 ∨ finrank F (Fin 2 ⊕ Fin 2 → F) = 5 := by
    left
    rw [Module.finrank_fintype_fun_eq_card]
    rfl
  obtain ⟨hle, -⟩ := weights_dim_four_five (spForm 2 F) hζ hσζ hρ hexpΓ hΓ hcard hfaith hdim
  apply natRep_injective (StatedSp 2 F)
  rw [map_one]
  refine eq_one_of_commute_of_pow hζ hexpΓ hΓ hle (k := k) ?_ fun g => ?_
  · rw [← map_pow, hk, map_one]
  · change natRep (StatedSp 2 F) s * natRep (StatedSp 2 F) (g : StatedSp 2 F) =
      natRep (StatedSp 2 F) (g : StatedSp 2 F) * natRep (StatedSp 2 F) s
    rw [← map_mul, ← map_mul, hs g g.2]

@[expose] noncomputable def spIter (g : StatedSp 2 F) (φ : F ≃+* F) : ℕ → StatedSp 2 F
  | 0 => 1
  | j + 1 => g * fieldSp 2 F φ (spIter g φ j)

theorem conj_field_apply_proj (g w : StatedSp 2 F) (φ : F ≃+* F) :
    (MulAut.conj (proj 2 F g) * fieldAut 2 F φ) (proj 2 F w) =
      proj 2 F (g * fieldSp 2 F φ w * g⁻¹) := by
  rw [MulAut.mul_apply, fieldAut_proj, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem conj_field_pow_sp4 (g : StatedSp 2 F) (φ : F ≃+* F) (j : ℕ) :
    (MulAut.conj (proj 2 F g) * fieldAut 2 F φ) ^ j =
      MulAut.conj (proj 2 F (spIter g φ j)) * fieldAut 2 F (φ ^ j) := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero, map_one, mul_one]
    change 1 = MulAut.conj (proj 2 F 1)
    rw [map_one, map_one]
  | succ j ih =>
    have h1 : fieldAut 2 F φ * MulAut.conj (proj 2 F (spIter g φ j)) * (fieldAut 2 F φ)⁻¹ =
        MulAut.conj (proj 2 F (fieldSp 2 F φ (spIter g φ j))) := by
      rw [Item224KFactsProof.mul_conj_mul_inv, fieldAut_proj]
    rw [pow_succ', ih, pow_succ']
    calc MulAut.conj (proj 2 F g) * fieldAut 2 F φ *
          (MulAut.conj (proj 2 F (spIter g φ j)) * fieldAut 2 F (φ ^ j)) =
        MulAut.conj (proj 2 F g) * (fieldAut 2 F φ * MulAut.conj (proj 2 F (spIter g φ j)) *
          (fieldAut 2 F φ)⁻¹) * (fieldAut 2 F φ * fieldAut 2 F (φ ^ j)) := by group
      _ = MulAut.conj (proj 2 F (spIter g φ (j + 1))) * fieldAut 2 F (φ * φ ^ j) := by
        rw [h1, ← map_mul (fieldAut 2 F), ← map_mul (MulAut.conj), ← map_mul (proj 2 F)]
        rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def semPsi (A : GL ι F) (φ : F ≃+* F) : (ι → F) ≃+ (ι → F) where
  toFun v := (A : Matrix ι ι F) *ᵥ fun i => φ (v i)
  invFun v := fun i => φ.symm ((((A⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ v) i)
  left_inv v := by
    funext i
    change φ.symm ((((A⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ
      ((A : Matrix ι ι F) *ᵥ fun j => φ (v j))) i) = v i
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact φ.symm_apply_apply (v i)
  right_inv v := by
    change (A : Matrix ι ι F) *ᵥ (fun i => φ (φ.symm _)) = v
    simp only [RingEquiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  map_add' u v := by
    change (A : Matrix ι ι F) *ᵥ (fun i => φ (u i + v i)) = _
    simp only [map_add]
    exact Matrix.mulVec_add _ _ _

theorem semPsi_apply (A : GL ι F) (φ : F ≃+* F) (v : ι → F) :
    semPsi A φ v = (A : Matrix ι ι F) *ᵥ fun i => φ (v i) :=
  rfl

theorem semPsi_smul (A : GL ι F) (φ : F ≃+* F) (c : F) (v : ι → F) :
    semPsi A φ (c • v) = φ c • semPsi A φ v := by
  rw [semPsi_apply, semPsi_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem natRep_conj_semPsi (A h : GL ι F) (φ : F ≃+* F) (v : ι → F) :
    ((A * glFieldEquiv ι φ h * A⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ v =
      semPsi A φ ((h : Matrix ι ι F) *ᵥ (semPsi A φ).symm v) := by
  rw [semPsi_apply]
  have hφ : (fun i => φ (((h : Matrix ι ι F) *ᵥ (semPsi A φ).symm v) i)) =
      ((h : Matrix ι ι F).map φ) *ᵥ (((A⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ v) := by
    funext i
    have := RingHom.map_mulVec (φ : F →+* F) (h : Matrix ι ι F) ((semPsi A φ).symm v) i
    rw [RingEquiv.coe_toRingHom] at this
    rw [this]
    congr 1
    funext j
    change φ (φ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  rw [hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rfl

theorem semPsi_tv (Fm : ReflForm F (ι → F)) (A : GL ι F) (φ : F ≃+* F)
    (hβ : ∀ u v, Fm.β (semPsi A φ u) (semPsi A φ v) = φ (Fm.β u v)) (a v : ι → F) :
    semPsi A φ (tv Fm a ((semPsi A φ).symm v)) = tv Fm (semPsi A φ a) v := by
  rw [tv_apply, tv_apply, map_add, semPsi_smul, AddEquiv.apply_symm_apply, ← hβ,
    AddEquiv.apply_symm_apply]

theorem semPsi_iterate (g : StatedSp 2 F) (φ : F ≃+* F) (j : ℕ) (v : Fin 2 ⊕ Fin 2 → F) :
    (⇑(semPsi (g : GL (Fin 2 ⊕ Fin 2) F) φ))^[j] v =
      (((spIter g φ j : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ fun i => (φ ^ j) (v i) := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply]
    change v = ((1 : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ _
    rw [Units.val_one, Matrix.one_mulVec]
    rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, semPsi_apply]
    change _ = (((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((((spIter g φ j : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map φ)) *ᵥ _
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    have := RingHom.map_mulVec (φ : F →+* F)
      ((((spIter g φ j : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (fun i => (φ ^ j) (v i)) i
    rw [RingEquiv.coe_toRingHom] at this
    rw [this, pow_succ']
    rfl

theorem semPsi_β (g : StatedSp 2 F) (φ : F ≃+* F) (u v : Fin 2 ⊕ Fin 2 → F) :
    (spForm 2 F).β (semPsi (g : GL (Fin 2 ⊕ Fin 2) F) φ u)
      (semPsi (g : GL (Fin 2 ⊕ Fin 2) F) φ v) = φ ((spForm 2 F).β u v) := by
  rw [semPsi_apply, semPsi_apply]
  have h1 := isIsometric_natRep_statedSp 2 F g (fun i => φ (u i)) (fun i => φ (v i))
  rw [natRep_apply, natRep_apply] at h1
  rw [h1, spForm_β, spForm_β]
  have hJ : (spJ 2 F).map φ = spJ 2 F :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.formJ_map φ
  have h2 : (spJ 2 F *ᵥ fun i => φ (v i)) = fun i => φ ((spJ 2 F *ᵥ v) i) := by
    funext i
    have := RingHom.map_mulVec (φ : F →+* F) (spJ 2 F) v i
    rw [RingEquiv.coe_toRingHom, hJ] at this
    rw [this]
    rfl
  rw [h2, dotProduct, dotProduct, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul]

theorem spForm_symm [CharP F 2] (u v : Fin 2 ⊕ Fin 2 → F) :
    (spForm 2 F).β v u = (spForm 2 F).σ ((spForm 2 F).β u v) := by
  rw [(spForm 2 F).β_swap_of_alt (spForm_self 2 F) u v, CharTwo.neg_eq]
  rfl

theorem exists_tvSp (a : Fin 2 ⊕ Fin 2 → F) :
    ∃ g : StatedSp 2 F, natRep (StatedSp 2 F) g = tv (spForm 2 F) a := by
  obtain ⟨g, hg⟩ := exists_natRep_eq_of_isometry 2 F (tv (spForm 2 F) a) fun u v => by
    rw [tv_apply, tv_apply]
    exact (spForm 2 F).β_transvection rfl (spForm_self 2 F) a u v
  exact ⟨g, LinearMap.ext hg⟩

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
