module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankCount
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.RankThree.PartOne.S11d.OrthFixedLayer
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.StandardType

namespace D4Rank

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix

variable {K : Type} [Field K]

section Rep

noncomputable abbrev omRep : Om8 K →* Module.End K (Fin (2 * 4) → K) :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := Fin (2 * 4) → K)).comp
    (matrixLinearIso.toMonoidHom.comp (matrixDerived (coordinateQuadPlus 4 K)).subtype)

theorem omRep_apply (x : Om8 K) (v : Fin (2 * 4) → K) :
    omRep x v = (x : GL (Fin (2 * 4)) K).val *ᵥ v := rfl

noncomputable abbrev omFixDim (x : Om8 K) : ℕ := fixDim (omRep x)

theorem mem_ker_omRep_sub_one {x : Om8 K} {v : Fin (2 * 4) → K} :
    v ∈ LinearMap.ker (omRep x - 1) ↔ (x : GL (Fin (2 * 4)) K).val *ᵥ v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, omRep_apply]

theorem fixDim_conj {V : Type*} [AddCommGroup V] [Module K V] {f u w : Module.End K V}
    (huw : u * w = 1) (hwu : w * u = 1) : fixDim (u * f * w) = fixDim f := by
  let e : V ≃ₗ[K] V := LinearEquiv.ofLinearMap u w huw hwu
  have hwu' : ∀ v, w (u v) = v := fun v => by rw [← Module.End.mul_apply, hwu]; rfl
  have huw' : ∀ v, u (w v) = v := fun v => by rw [← Module.End.mul_apply, huw]; rfl
  have h : LinearMap.ker (u * f * w - 1) = (LinearMap.ker (f - 1)).map e.toLinearMap := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
      sub_eq_zero, Submodule.mem_map]
    constructor
    · intro hv
      refine ⟨w v, ?_, huw' v⟩
      have := congrArg w hv
      rwa [hwu'] at this
    · rintro ⟨y, hy, rfl⟩
      change u (f (w (u y))) = u y
      rw [hwu', hy]
  rw [fixDim, fixDim, h, LinearEquiv.finrank_map_eq]

theorem omFixDim_conj (γ x : Om8 K) : omFixDim (MulAut.conj γ x) = omFixDim x := by
  rw [omFixDim, omFixDim, MulAut.conj_apply, map_mul, map_mul]
  exact fixDim_conj (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_mul, inv_mul_cancel, map_one])

theorem fieldAutP_val (σ : K ≃+* K) (x : Om8 K) :
    ((AutOm.fieldAutP 4 σ x : Om8 K) : GL (Fin (2 * 4)) K) =
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin (2 * 4)) K σ
        (x : GL (Fin (2 * 4)) K) := by
  rw [AutOm.fieldAutP_apply, conjAct_apply, matrixDerivedConjugation_val]
  simp only [CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair_left,
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair_right, one_mul, inv_one, mul_one]

theorem omFixDim_fieldAutP [Finite K] (σ : K ≃+* K) (x : Om8 K) :
    omFixDim (AutOm.fieldAutP 4 σ x) = omFixDim x := by
  set y := AutOm.fieldAutP 4 σ x
  have hfix : ∀ (τ : K ≃+* K) (A : GL (Fin (2 * 4)) K) (v : Fin (2 * 4) → K), A.val *ᵥ v = v →
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin (2 * 4)) K τ
        A).val *ᵥ coordinateFieldMap (2 * 4) τ v = coordinateFieldMap (2 * 4) τ v := by
    intro τ A v hv
    have := coordinateFieldMap_matrix τ A v
    rw [matrixLinearEquiv_apply, hv, matrixLinearEquiv_apply] at this
    exact this.symm
  have hyx : CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin (2 * 4)) K
      σ.symm (y : GL (Fin (2 * 4)) K) = (x : GL (Fin (2 * 4)) K) := by
    rw [fieldAutP_val]
    ext i j
    exact σ.symm_apply_apply _
  have hσσ : ∀ v : Fin (2 * 4) → K, coordinateFieldMap (2 * 4) σ.symm
      (coordinateFieldMap (2 * 4) σ v) = v := fun v => by
    funext i; simp [coordinateFieldMap_apply]
  have hσσ' : ∀ v : Fin (2 * 4) → K, coordinateFieldMap (2 * 4) σ
      (coordinateFieldMap (2 * 4) σ.symm v) = v := fun v => by
    funext i; simp [coordinateFieldMap_apply]
  have e : LinearMap.ker (omRep x - 1) ≃ LinearMap.ker (omRep y - 1) :=
    { toFun := fun v => ⟨coordinateFieldMap (2 * 4) σ v, by
        rw [mem_ker_omRep_sub_one, fieldAutP_val]
        exact hfix σ _ v (mem_ker_omRep_sub_one.mp v.2)⟩
      invFun := fun v => ⟨coordinateFieldMap (2 * 4) σ.symm v, by
        rw [mem_ker_omRep_sub_one, ← hyx]
        exact hfix σ.symm _ v (mem_ker_omRep_sub_one.mp v.2)⟩
      left_inv := fun v => Subtype.ext (hσσ v)
      right_inv := fun v => Subtype.ext (hσσ' v) }
  have hc := Nat.card_congr e
  rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (omRep x - 1)),
    Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (omRep y - 1))] at hc
  have h2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
    omega
  exact (Nat.pow_right_injective h2 hc).symm

theorem omFixDim_even [CharP K 2] (x : Om8 K) (hx : x ^ 3 = 1) : Even (omFixDim x) := by
  have hO : (x : GL (Fin (2 * 4)) K) ∈ matrixIsometries (coordinateQuadPlus 4 K) :=
    matrixDerived_le_isometries _ x.2
  have hodd : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry (coordinateQuadPlus 4 K) 3
      (matrixLinearEquiv (x : GL (Fin (2 * 4)) K)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2
        ((mem_matrixIsometries_iff _ _).1 hO)
    · have : ((x : GL (Fin (2 * 4)) K)) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
      change matrixLinearIso ((x : GL (Fin (2 * 4)) K)) ^ 3 = 1
      rw [← map_pow, this, map_one]
    · intro h
      have := (CharP.cast_eq_zero_iff K 2 3).mp h
      omega
    · intro v hv
      have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
      exact hnd.1 v fun w => by simpa [QuadraticMap.polarBilin_apply_apply] using hv w
  exact hodd.even_finrank_fixed

theorem eq_one_of_omFixDim {x : Om8 K} (h : omFixDim x = 8) : x = 1 := by
  have htop : LinearMap.ker (omRep x - 1) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h)
  apply Subtype.ext
  apply Units.ext
  change (x : GL (Fin (2 * 4)) K).val = 1
  ext i j
  have hv := (mem_ker_omRep_sub_one (x := x)).mp (htop ▸ Submodule.mem_top (x := Pi.single j 1))
  have := congrFun hv i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

end Rep

section Group

variable {G : Type*} [Group G]

theorem mulAut_mul_conj (β : MulAut G) (γ : G) :
    β * MulAut.conj γ = MulAut.conj (β γ) * β := by
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_mul_sq (β : MulAut G) (γ : G) :
    (MulAut.conj γ * β) ^ 2 = MulAut.conj (γ * β γ) * β ^ 2 := by
  rw [sq, sq, mul_assoc, ← mul_assoc β, mulAut_mul_conj, map_mul]
  group

theorem conj_mul_cube (β : MulAut G) (γ : G) :
    ∃ γ' : G, (MulAut.conj γ * β) ^ 3 = MulAut.conj γ' * β ^ 3 := by
  refine ⟨γ * β γ * (β ^ 2) γ, ?_⟩
  calc (MulAut.conj γ * β) ^ 3 = (MulAut.conj γ * β) ^ 2 * (MulAut.conj γ * β) := pow_succ _ 2
    _ = MulAut.conj (γ * β γ) * (β ^ 2 * MulAut.conj γ) * β := by rw [conj_mul_sq]; group
    _ = MulAut.conj (γ * β γ) * (MulAut.conj ((β ^ 2) γ) * β ^ 2) * β := by
        rw [mulAut_mul_conj]
    _ = MulAut.conj (γ * β γ * (β ^ 2) γ) * β ^ 3 := by
        rw [map_mul (MulAut.conj) (γ * β γ), pow_succ β 2]; group

theorem beta_cube {t r f : G} (h1 : t * f = f * t) (h2 : r * f = f * r)
    (h3 : r * t * r = t⁻¹) : (t * (r * f)) ^ 3 = t * (r * f ^ 3) := by
  have hsq : (t * (r * f)) ^ 2 = f ^ 2 := by
    calc (t * (r * f)) ^ 2 = t * r * (f * t) * r * f := by rw [sq]; group
      _ = t * r * (t * f) * r * f := by rw [h1]
      _ = t * (r * t) * (f * r) * f := by group
      _ = t * (r * t) * (r * f) * f := by rw [h2]
      _ = t * (r * t * r) * f * f := by group
      _ = f ^ 2 := by rw [h3, sq]; group
  have hf2t : f ^ 2 * t = t * f ^ 2 := ((Commute.pow_left (h1.symm : Commute f t) 2)).eq
  have hf2r : f ^ 2 * r = r * f ^ 2 := ((Commute.pow_left (h2.symm : Commute f r) 2)).eq
  calc (t * (r * f)) ^ 3 = (t * (r * f)) ^ 2 * (t * (r * f)) := pow_succ _ 2
    _ = f ^ 2 * t * (r * f) := by rw [hsq, mul_assoc]
    _ = t * (f ^ 2 * r) * f := by rw [hf2t]; group
    _ = t * (r * f ^ 3) := by rw [hf2r]; group

theorem conj_pow_inv {t r : G} (hr : r * r = 1) (h3 : r * t * r = t⁻¹) (j : ℕ) :
    r * t ^ j * r = (t ^ j)⁻¹ := by
  induction j with
  | zero => rw [pow_zero, mul_one, hr, inv_one]
  | succ j ih =>
    calc r * t ^ (j + 1) * r = (r * t ^ j * r) * (r * t * r) := by
          rw [pow_succ]
          calc r * (t ^ j * t) * r = r * t ^ j * 1 * t * r := by group
            _ = r * t ^ j * (r * r) * t * r := by rw [hr]
            _ = r * t ^ j * r * (r * t * r) := by group
      _ = (t ^ (j + 1))⁻¹ := by rw [ih, h3, pow_succ, mul_inv_rev]; group

end Group

section Aut

variable [Finite K] [CharP K 2]

theorem theta_pow_ne_one {k : ℕ} (hk : k = 1 ∨ k = 2) : (theta : MulAut (Om8 K)) ^ k ≠ 1 := by
  have h1 : (theta : MulAut (Om8 K)) ≠ 1 := fun h =>
    conjAct_ne_theta (1 : similarityPairs (coordinateQuadPlus 4 K)) (by rw [map_one, h])
  rcases hk with rfl | rfl
  · rwa [pow_one]
  · rw [theta_sq]
    exact fun h => h1 (inv_eq_one.mp h)

theorem exists_conj_theta_pow_fieldAutP (α : MulAut (Om8 K)) (hα3 : α ^ 3 = 1)
    (hns : ∀ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g ≠ α) :
    ∃ (γ : Om8 K) (k : ℕ) (σ : K ≃+* K), (k = 1 ∨ k = 2) ∧
      α = MulAut.conj γ * (theta ^ k * AutOm.fieldAutP 4 σ) := by
  obtain ⟨ι, hι, k, c, hc, hα⟩ := exists_inner_mul_theta_pow_mul α
  obtain ⟨γ, rfl⟩ := hι
  have hk : (theta : MulAut (Om8 K)) ^ k = theta ^ (k % 3) := pow_eq_pow_mod k theta_cube
  rw [hk] at hα
  have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hk0 : k % 3 ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hα
    obtain ⟨g₁, hg₁⟩ := exists_pair_of_mem_inner (K := K) ⟨γ, rfl⟩
    obtain ⟨g₂, hg₂⟩ := exists_pair_of_mem_plusCompl hc
    exact hns (g₁ * g₂) (by rw [map_mul, hg₁, hg₂, hα])
  have hk12 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  obtain ⟨σ, rfl | rfl⟩ := hc
  · exact ⟨γ, k % 3, σ, hk12, hα⟩
  · exfalso
    set t : MulAut (Om8 K) := theta ^ (k % 3)
    set r : MulAut (Om8 K) := AutOm.plusRefl one_le_four
    set f : MulAut (Om8 K) := AutOm.fieldAutP 4 σ
    have hr : r * r = 1 := AutOm.plusRefl_mul_self one_le_four
    have h1 : t * f = f * t := ((Commute.pow_left (theta_fieldAutP σ : Commute theta f)
      (k % 3))).eq
    have h2 : r * f = f * r := AutOm.plusRefl_mul_fieldAutP one_le_four σ
    have h3 : r * t * r = t⁻¹ := conj_pow_inv hr plusRefl_theta_plusRefl (k % 3)
    obtain ⟨γ', hγ'⟩ := conj_mul_cube (t * (r * f)) γ
    rw [← hα, hα3, beta_cube h1 h2 h3] at hγ'
    have hmem : t * (r * f ^ 3) ∈ inner (Om8 K) := by
      have : t * (r * f ^ 3) = MulAut.conj γ'⁻¹ := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_right hγ'.symm
      rw [this]
      exact ⟨_, rfl⟩
    have hf3 : f ^ 3 = AutOm.fieldAutP 4 (σ ^ 3) := (map_pow _ σ 3).symm
    rw [hf3] at hmem
    exact theta_pow_ne_one hk12
      (theta_pow_mul_mem_inner (k % 3) ⟨σ ^ 3, Or.inr rfl⟩ hmem).1

end Aut

@[expose] def GGD4TrialityClassInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (x : Om8 K), x ^ 3 = 1 →
    (omFixDim x = 6 → omFixDim (theta x) = 0 ∧ omFixDim (theta⁻¹ x) = 0) ∧
      (omFixDim x = 0 → omFixDim (theta x) = 6 ∨ omFixDim (theta⁻¹ x) = 6)

section Bound

variable [Finite K] [CharP K 2]

theorem card_le_nine_of_classInput (hcls : GGD4TrialityClassInput) (α : MulAut (Om8 K))
    (hα3 : α ^ 3 = 1) (hns : ∀ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g ≠ α)
    (E : Subgroup (Om8 K)) (hE : CFSG.Assembly.IsElemAbelian 3 E) (hfix : ∀ e ∈ E, α e = e) :
    Nat.card E ≤ 9 := by
  obtain ⟨γ, k, σ, hk, rfl⟩ := exists_conj_theta_pow_fieldAutP α hα3 hns
  set φ := AutOm.fieldAutP 4 σ with hφ
  have hθφ : ∀ j : ℕ, ∀ y : Om8 K, (theta ^ j) (φ y) = φ ((theta ^ j) y) := by
    intro j y
    rw [← MulAut.mul_apply, ← MulAut.mul_apply,
      (Commute.pow_left (theta_fieldAutP σ : Commute theta φ) j).eq]
  have hpair : ((theta : MulAut (Om8 K)) ^ k = theta ∧ (theta : MulAut (Om8 K)) ^ (k + k) =
      theta⁻¹) ∨ ((theta : MulAut (Om8 K)) ^ k = theta⁻¹ ∧
        (theta : MulAut (Om8 K)) ^ (k + k) = theta) := by
    rcases hk with rfl | rfl
    · exact Or.inl ⟨pow_one _, theta_sq⟩
    · refine Or.inr ⟨theta_sq, ?_⟩
      rw [show 2 + 2 = 3 + 1 from rfl, pow_succ, theta_cube, one_mul]
  have hd1 : ∀ e ∈ E, omFixDim ((theta ^ k) (φ e)) = omFixDim e := by
    intro e he
    have h := hfix e he
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    rw [← omFixDim_conj γ, h]
  have hd2 : ∀ e ∈ E, omFixDim ((theta ^ (k + k)) (φ (φ e))) = omFixDim e := by
    intro e he
    have h2 : (MulAut.conj γ * (theta ^ k * φ)) ^ 2 =
        MulAut.conj (γ * (theta ^ k * φ : MulAut (Om8 K)) γ) * (theta ^ (k + k) * (φ * φ)) := by
      rw [conj_mul_sq, sq (theta ^ k * φ), mul_assoc, ← mul_assoc φ,
        ← (Commute.pow_left (theta_fieldAutP σ : Commute theta φ) k).eq, mul_assoc,
        ← mul_assoc (theta ^ k), ← pow_add]
    have hα2 : ((MulAut.conj γ * (theta ^ k * φ) : MulAut (Om8 K)) ^ 2) e = e := by
      rw [sq, MulAut.mul_apply, hfix e he, hfix e he]
    rw [h2, MulAut.mul_apply] at hα2
    have h := omFixDim_conj (γ * (theta ^ k * φ : MulAut (Om8 K)) γ)
      ((theta ^ (k + k) * (φ * φ) : MulAut (Om8 K)) e)
    rw [hα2] at h
    exact h.symm
  have hd : ∀ e ∈ E, e ≠ 1 → omFixDim e = 2 ∨ omFixDim e = 4 := by
    intro e he he1
    have he3 : e ^ 3 = 1 := hE.2 e he
    have hy3 : φ e ^ 3 = 1 := by rw [← map_pow, he3, map_one]
    have hdy : omFixDim (φ e) = omFixDim e := omFixDim_fieldAutP σ e
    have hle : omFixDim e ≤ 8 := by
      have := Submodule.finrank_le (LinearMap.ker (omRep e - 1))
      rwa [Module.finrank_fin_fun] at this
    have h8 : omFixDim e ≠ 8 := fun h => he1 (eq_one_of_omFixDim h)
    obtain ⟨j, hj⟩ := omFixDim_even e he3
    have h6 : omFixDim e ≠ 6 := by
      intro h6
      obtain ⟨ha, hb⟩ := (hcls K (φ e) hy3).1 (hdy.trans h6)
      have h1 := hd1 e he
      rcases hpair with ⟨hk1, -⟩ | ⟨hk1, -⟩ <;> rw [hk1] at h1 <;> omega
    have h0 : omFixDim e ≠ 0 := by
      intro h0
      have h := (hcls K (φ e) hy3).2 (hdy.trans h0)
      have h1 := hd1 e he
      have h2 := hd2 e he
      rw [hθφ, omFixDim_fieldAutP] at h2
      rcases hpair with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩ <;> rw [hk1] at h1 <;> rw [hk2] at h2 <;>
        rcases h with h | h <;> omega
    omega
  by_contra hlt
  push Not at hlt
  have : IsMulCommutative E := hE.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hexp : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (hE.2 x x.2)
  have hp : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h27 : 27 ≤ Nat.card E := by
    rw [hn] at hlt ⊢
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num at hlt
    · calc 27 = 3 ^ 3 := rfl
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
  exact false_of_fixDim_two_four (CharP.cast_eq_zero K 2) (Module.finrank_fin_fun K)
    (omRep.comp E.subtype) hexp h27 fun x hx => hd x x.2 fun h => hx (Subtype.ext h)

end Bound

end D4Rank

end CFSG.StandardType
