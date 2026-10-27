module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Frame
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvRank
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvSign

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.LinTwoTv

open Polynomial Matrix Multiplicative CoordSL CFSG.Assembly

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem two_le_rootPB_dim {g : K[X]} [Fact (Irreducible g)]
    (hunit : ∀ c : K, IsUnit (rootMat g ^ 1 - c • (1 : Matrix _ _ K))) : 2 ≤ (rootPB g).dim := by
  by_contra hlt
  have hpos : 0 < (rootPB g).dim := rootPB_dim_pos g
  have h1 : (rootPB g).dim = 1 := by omega
  set i0 : Fin (rootPB g).dim := ⟨0, hpos⟩ with hi0
  have hsub : ∀ a : Fin (rootPB g).dim, a = i0 := fun a => Fin.ext (by
    have := a.2
    simp only [hi0]
    omega)
  have hu := hunit (rootMat g i0 i0)
  have h0 : (rootMat g ^ 1 - (rootMat g i0 i0) • (1 : Matrix _ _ K)) = 0 := by
    ext a b
    rw [hsub a, hsub b]
    simp [Matrix.one_apply]
  rw [h0] at hu
  haveI : Nonempty (Fin (rootPB g).dim) := ⟨i0⟩
  exact not_isUnit_zero hu

theorem coe_frameHom_toGL {s r : ℕ} {g : K[X]} [Fact (Irreducible g)]
    (ε : Fin d ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (A₀ : SpecialLinearGroup (Fin d) K)
    (hC : (rootMat g).det = 1) (hCp : rootMat g ^ 3 = 1) (t : Fin s → ZMod 3) :
    ((frameHom (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin d) K →* GL (Fin d) K) A₀ ε hC
        hCp (ofAdd t) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (A₀ : Matrix (Fin d) (Fin d) K) * SLNS.nsMat ε (rootMat g) (fun i => (t i).val) *
        ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  rw [frameHom_apply]
  rfl

theorem wtGL_frameHom {s r : ℕ} {g : K[X]} [Fact (Irreducible g)] (hK : Nat.card K = 2)
    (hp3 : ((3 : ℕ) : K) ≠ 0) (hgd : g ∣ cyclotomic 3 K)
    (ε : Fin d ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (A₀ : SpecialLinearGroup (Fin d) K)
    (hC : (rootMat g).det = 1) (hCp : rootMat g ^ 3 = 1) (t : Fin s → ZMod 3) :
    wtGL (frameHom (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin d) K →* GL (Fin d) K) A₀ ε
      hC hCp (ofAdd t)) = (rootPB g).dim * hamWt t := by
  classical
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; decide
  have h1 : wtGL (frameHom (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin d) K →*
      GL (Fin d) K) A₀ ε hC hCp (ofAdd t)) =
      (SLNS.nsMat ε (rootMat g) (fun i => (t i).val) - 1).rank := by
    rw [wtGL, coe_frameHom_toGL]
    have h2 : (A₀ : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h3 : ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (A₀ : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h4 : (A₀ : Matrix (Fin d) (Fin d) K) *
        SLNS.nsMat ε (rootMat g) (fun i => (t i).val) *
          ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1 =
        (A₀ : Matrix (Fin d) (Fin d) K) *
          (SLNS.nsMat ε (rootMat g) (fun i => (t i).val) - 1) *
            ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2]
    rw [h4]
    exact rank_conj_eq h2 h3
  rw [h1, rank_nsMat_sub_one ε (rootMat g) _ (Finset.univ.filter fun i => t i ≠ 0)]
  · rfl
  · intro i hi
    have hti : t i = 0 := by simpa using hi
    simp [hti]
  · intro i hi
    have hti : t i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hdvd : ¬ 3 ∣ (t i).val := by
      intro h
      apply hti
      rw [← ZMod.natCast_zmod_val (t i), (ZMod.natCast_eq_zero_iff _ _).mpr h]
    have := isUnit_rootMat_pow_sub Nat.prime_three hnsplit hp3 hgd _ hdvd 1
    simpa using this

theorem eq_of_rank_pres_sq (hK : Nat.card K = 2) {E : Subgroup (GL (Fin d) K)}
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ (d / 2) ≤ Nat.card E)
    (Θ : GL (Fin d) K →* GL (Fin d) K) (hw : ∀ B, wtGL (Θ B) = wtGL B)
    (hΘ : ∀ b ∈ E, Θ b ∈ E) (hsq : ∀ b ∈ E, Θ (b⁻¹ * Θ b) = b⁻¹ * Θ b) :
    ∀ b ∈ E, Θ b = b := by
  classical
  have hchar : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three K
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; decide
  have hC : (rootMat g).det = 1 := det_rootMat Nat.prime_three hnsplit hp3 hgd
  have hCp : rootMat g ^ 3 = 1 := rootMat_pow_eq_one Nat.prime_three hp3 hgd
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
  have hmemE : ∀ t : Fin s → ZMod 3, ι (ofAdd t) ∈ E := fun t => hEeq ▸ ⟨_, rfl⟩
  have hex : ∀ t : Fin s → ZMod 3, ∃ t' : Fin s → ZMod 3, Θ (ι (ofAdd t)) = ι (ofAdd t') := by
    intro t
    have h1 : Θ (ι (ofAdd t)) ∈ ι.range := hEeq ▸ hΘ _ (hmemE t)
    obtain ⟨a, ha⟩ := h1
    exact ⟨toAdd a, by rw [ofAdd_toAdd]; exact ha.symm⟩
  choose τ hτ using hex
  have hadd : ∀ x y, τ (x + y) = τ x + τ y := by
    intro x y
    have h := hιinj (a₁ := ofAdd (τ (x + y))) (a₂ := ofAdd (τ x + τ y)) (by
      rw [← hτ, ofAdd_add, map_mul, map_mul, hτ, hτ, ofAdd_add, map_mul])
    exact ofAdd.injective h
  let τl : (Fin s → ZMod 3) →ₗ[ZMod 3] (Fin s → ZMod 3) :=
    AddMonoidHom.toZModLinearMap 3 (AddMonoidHom.mk' τ hadd)
  have hτl : ∀ v, τl v = τ v := fun v => rfl
  have hw' : ∀ v, hamWt (τl v) = hamWt v := by
    intro v
    have h1 : wtGL (ι (ofAdd (τ v))) = (rootPB g).dim * hamWt (τ v) :=
      wtGL_frameHom hK hp3 hgd ε A₀ hC hCp (τ v)
    have h2 : wtGL (ι (ofAdd v)) = (rootPB g).dim * hamWt v :=
      wtGL_frameHom hK hp3 hgd ε A₀ hC hCp v
    have h4 : (rootPB g).dim * hamWt (τ v) = (rootPB g).dim * hamWt v := by
      rw [← h1, ← h2, ← hτ v, hw]
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  have hsq' : ∀ v, τl (τl v - v) = τl v - v := by
    intro v
    have h1 := hsq (ι (ofAdd v)) (hmemE v)
    have h2 : (ι (ofAdd v))⁻¹ * Θ (ι (ofAdd v)) = ι (ofAdd (τ v - v)) := by
      rw [hτ, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add, neg_add_eq_sub]
    rw [h2, hτ] at h1
    exact ofAdd.injective (hιinj h1)
  have hid := eq_id_of_hamWt_sq τl hw' hsq'
  intro b hb
  rw [hEeq] at hb
  obtain ⟨a, rfl⟩ := hb
  rw [← ofAdd_toAdd a, hτ]
  congr 2
  exact hid (toAdd a)

end CFSG.StandardType.LinTwoTv

end
