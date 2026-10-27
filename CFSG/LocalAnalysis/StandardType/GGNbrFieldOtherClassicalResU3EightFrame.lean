module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSub

public section

namespace CFSG.StandardType

namespace ResU3Eight

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)
open ResU3Three

variable {k : Type} [Field k] {m : ℕ}

theorem reg_or_frame_U3Eight (h₀ : UnitaryFieldData 2 m k) (h3 : 3 ∣ 2 ^ m + 1)
    {S : Subgroup (GL (Fin 3) k)}
    (hSc : ∀ x ∈ S, ∀ y ∈ S, ∃ c : kˣ,
      x * y = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (y * x))
    (hS3 : ∀ x ∈ S, ∃ c : kˣ, x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hSz : ∀ c : kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ S)
    {B₀ : GL (Fin 3) k} (hB₀ : B₀ ∈ LargeEvenGUSet (Fin 3) k (2 ^ m)) (hB₀S : B₀ ∈ S)
    (hB₀s : ∀ c : kˣ, B₀ ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) c) {e₀ : kˣ}
    (he₀ : B₀ ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (e₀ ^ 3))
    (hcomm : ∀ B ∈ S, B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m) → B * B₀ = B₀ * B) :
    RegU3Three (B₀ : Matrix (Fin 3) (Fin 3) k) ∨
      ∃ (P : GL (Fin 3) k) (σ : Fin 3 → kˣ) (u v : Fin 3),
        P ∈ primeFormUnitary h₀ (idGram k 3) ∧
        (∀ B ∈ S, B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m) →
          ∃ τ : Fin 3 → kˣ, P⁻¹ * B * P = diagHom 3 τ) ∧
        P⁻¹ * B₀ * P = diagHom 3 σ ∧ ¬ Function.Injective σ ∧ σ u ≠ σ v := by
  classical
  haveI : CharP k 2 := h₀.charP
  have hconjDiag : ∀ {Q B : GL (Fin 3) k} {τ : Fin 3 → kˣ}, Q⁻¹ * B * Q = diagHom 3 τ →
      ((Q⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k) *
        (Q : Matrix (Fin 3) (Fin 3) k) = diagonal fun i => (τ i : k) := by
    intro Q B τ h
    have h1 := congrArg Units.val h
    rwa [Units.val_mul, Units.val_mul, coe_diagHom] at h1
  set X : GL (Fin 3) k := Matrix.GeneralLinearGroup.scalar (Fin 3) e₀⁻¹ * B₀ with hXdef
  have hcomm₀ : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) e₀⁻¹) B₀ :=
    scalar_mul_comm_U3Three e₀⁻¹ B₀
  have hX3 : X ^ 3 = 1 := by
    rw [hXdef, hcomm₀.mul_pow, he₀, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hXU : X ∈ primeFormUnitary h₀ (idGram k 3) :=
    TableBUD.mem_primeFormUnitary_of_pow_eq_one h₀ h3 (by norm_num) hB₀
      (c := ((e₀⁻¹ : kˣ) : k)) (coe_scalar_mul_U3Three e₀⁻¹ B₀) hX3
  have hB₀X : B₀ = Matrix.GeneralLinearGroup.scalar (Fin 3) e₀ * X := by
    rw [hXdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hg3 : (⟨X, hXU⟩ : primeFormUnitary h₀ (idGram k 3)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hX3)
  obtain ⟨P₁, hP₁⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h₀ Nat.prime_three h3
    (Subgroup.zpowers (⟨X, hXU⟩ : primeFormUnitary h₀ (idGram k 3)))
    (fun x hx y hy => by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow_self _ a b).eq)
    (fun x hx => by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hg3,
        _root_.one_zpow])
  set Q₁ : GL (Fin 3) k := (P₁ : GL (Fin 3) k) with hQ₁
  have hD₁ : ((Q₁⁻¹ * X * Q₁ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).IsDiag := by
    have h1 := hP₁ _ (Subgroup.mem_zpowers _)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  obtain ⟨σ₁, hσ₁⟩ := TableBUE.exists_diagHom_of_isDiag hD₁
  by_cases hinj₁ : Function.Injective σ₁
  · left
    have hXreg : RegU3Three (X : Matrix (Fin 3) (Fin 3) k) :=
      regU3Three_of_conj Q₁ (fun a b h => hinj₁ (Units.ext h)) (hconjDiag hσ₁)
    rw [hB₀X, coe_scalar_mul_U3Three]
    exact hXreg.smul e₀.ne_zero
  have hnc₁ : ∃ a b, σ₁ a ≠ σ₁ b := by
    by_contra hc
    push Not at hc
    have h1 := eq_scalar_of_conj_U3Three (hσ₁.trans (diagHom_eq_scalar_U3Three hc))
    apply hB₀s (e₀ * σ₁ 0)
    rw [hB₀X, h1, ← map_mul]
  obtain ⟨i, hi⟩ := exists_odd_U3Three hinj₁ hnc₁
  set v : Fin 3 → k := (Q₁ : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single i 1 with hvdef
  have hv0 : v ≠ 0 := by
    intro h
    have h1 : ((Q₁⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = Pi.single i 1 := by
      rw [hvdef, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at h1
    have h2 := congrFun h1 i
    simp at h2
  have heig : ∀ B ∈ S, B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m) →
      ∃ c : kˣ, (B : Matrix (Fin 3) (Fin 3) k) *ᵥ v = (c : k) • v := by
    intro B hBS hBgu
    have hBX : B * X = X * B := by
      rw [hXdef, ← mul_assoc, ← scalar_mul_comm_U3Three, mul_assoc, hcomm B hBS hBgu,
        mul_assoc]
    set Mc : Matrix (Fin 3) (Fin 3) k := ((Q₁⁻¹ * B * Q₁ : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) with hMcdef
    have hMc : Mc * diagonal (fun t => (σ₁ t : k)) = diagonal (fun t => (σ₁ t : k)) * Mc := by
      have h1 : (Q₁⁻¹ * B * Q₁) * (Q₁⁻¹ * X * Q₁) = (Q₁⁻¹ * X * Q₁) * (Q₁⁻¹ * B * Q₁) := by
        calc (Q₁⁻¹ * B * Q₁) * (Q₁⁻¹ * X * Q₁) = Q₁⁻¹ * (B * X) * Q₁ := by group
          _ = Q₁⁻¹ * (X * B) * Q₁ := by rw [hBX]
          _ = (Q₁⁻¹ * X * Q₁) * (Q₁⁻¹ * B * Q₁) := by group
      rw [hσ₁] at h1
      have h2 := congrArg Units.val h1
      rwa [Units.val_mul, Units.val_mul, coe_diagHom] at h2
    have hcol : ∀ t, t ≠ i → Mc t i = 0 := by
      intro t ht
      have h1 := congrFun (congrFun hMc t) i
      rw [mul_diagonal, diagonal_mul] at h1
      have hne : (σ₁ i : k) - σ₁ t ≠ 0 := sub_ne_zero.mpr fun h => hi t ht (Units.ext h).symm
      have h2 : Mc t i * ((σ₁ i : k) - σ₁ t) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_right hne
    have hMcv : Mc *ᵥ Pi.single i 1 = Mc i i • Pi.single i 1 := by
      ext t
      rw [Matrix.mulVec_single_one]
      by_cases ht : t = i
      · subst ht
        simp
      · rw [Matrix.col_apply, hcol t ht]
        simp [ht]
    have hQ : (B : Matrix (Fin 3) (Fin 3) k) * (Q₁ : Matrix (Fin 3) (Fin 3) k) =
        (Q₁ : Matrix (Fin 3) (Fin 3) k) * Mc := by
      rw [hMcdef, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    have hBv : (B : Matrix (Fin 3) (Fin 3) k) *ᵥ v = Mc i i • v := by
      rw [hvdef, Matrix.mulVec_mulVec, hQ, ← Matrix.mulVec_mulVec, hMcv, Matrix.mulVec_smul]
    have hc0 : Mc i i ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hBv
      apply hv0
      have h1 := congrArg (fun w => ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ w) hBv
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
      rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact ⟨Units.mk0 _ hc0, by rw [Units.val_mk0]; exact hBv⟩
  let Gv : Subgroup (primeFormUnitary h₀ (idGram k 3)) :=
    { carrier := {x | ((x : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v}
      mul_mem' := fun {x y} hx hy => by
        change (((x : GL (Fin 3) k) * y : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hy, hx]
      one_mem' := by
        change (((1 : GL (Fin 3) k) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v
        rw [Units.val_one, Matrix.one_mulVec]
      inv_mem' := fun {x} hx => by
        change (((x : GL (Fin 3) k)⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v
        conv_lhs => rw [← hx]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec] }
  let G : Subgroup (primeFormUnitary h₀ (idGram k 3)) :=
    Gv ⊓ S.comap (primeFormUnitary h₀ (idGram k 3)).subtype
  have hmemG : ∀ x, x ∈ G ↔ ((x : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v ∧
      (x : GL (Fin 3) k) ∈ S := fun x => Iff.rfl
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    rw [hmemG] at hx hy
    obtain ⟨c, hc'⟩ := hSc _ hx.2 _ hy.2
    have hv' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) *ᵥ v = v := by
      have h1 : (((x : GL (Fin 3) k) * y : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hy.1, hx.1]
      have h2 : (((y : GL (Fin 3) k) * x : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx.1, hy.1]
      rw [hc', Units.val_mul, ← Matrix.mulVec_mulVec, h2] at h1
      exact h1
    have hc1 := scalar_eq_one_of_fix_U3Three hv0 hv'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc', hc1, map_one, one_mul]
  have hGpow : ∀ x ∈ G, x ^ 3 = 1 := by
    intro x hx
    rw [hmemG] at hx
    obtain ⟨c, hc'⟩ := hS3 _ hx.2
    have hv' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) *ᵥ v = v := by
      rw [← hc', Units.val_pow_eq_pow_val, pow_three, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hx.1, hx.1, hx.1]
    have hc1 := scalar_eq_one_of_fix_U3Three hv0 hv'
    apply Subtype.ext
    rw [Subgroup.coe_pow, hc', hc1, map_one]
    rfl
  obtain ⟨P₂, hP₂⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h₀ Nat.prime_three h3 G hGcomm hGpow
  set Q₂ : GL (Fin 3) k := (P₂ : GL (Fin 3) k) with hQ₂
  have hdiagAll : ∀ B ∈ S, B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m) →
      ∃ τ : Fin 3 → kˣ, Q₂⁻¹ * B * Q₂ = diagHom 3 τ := by
    intro B hBS hBgu
    obtain ⟨c, hc⟩ := heig B hBS hBgu
    set Y : GL (Fin 3) k := Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ * B with hYdef
    have hYv : (Y : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v := by
      rw [hYdef, coe_scalar_mul_U3Three, Matrix.smul_mulVec, hc, smul_smul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul]
    have hYS : Y ∈ S := S.mul_mem (hSz c⁻¹) hBS
    have hY3 : Y ^ 3 = 1 := by
      obtain ⟨z, hz'⟩ := hS3 Y hYS
      have hv' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) z : GL (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) *ᵥ v = v := by
        rw [← hz', Units.val_pow_eq_pow_val, pow_three, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hYv, hYv, hYv]
      rw [hz', scalar_eq_one_of_fix_U3Three hv0 hv', map_one]
    have hYU : Y ∈ primeFormUnitary h₀ (idGram k 3) :=
      TableBUD.mem_primeFormUnitary_of_pow_eq_one h₀ h3 (by norm_num) hBgu
        (c := ((c⁻¹ : kˣ) : k)) (coe_scalar_mul_U3Three c⁻¹ B) hY3
    have hYG : (⟨Y, hYU⟩ : primeFormUnitary h₀ (idGram k 3)) ∈ G := by
      rw [hmemG]
      exact ⟨hYv, hYS⟩
    have hdY := hP₂ _ hYG
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hdY
    obtain ⟨τY, hτY⟩ := TableBUE.exists_diagHom_of_isDiag hdY
    refine ⟨fun t => c * τY t, ?_⟩
    have hBY : B = Matrix.GeneralLinearGroup.scalar (Fin 3) c * Y := by
      rw [hYdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    calc Q₂⁻¹ * B * Q₂ = (Q₂⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) c * Q₂) *
          (Q₂⁻¹ * Y * Q₂) := by rw [hBY]; group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c * diagHom 3 τY := by
          rw [conj_scalar_U3Three, hτY]
      _ = diagHom 3 (fun t => c * τY t) := by
          rw [scalar_eq_diagHom_U3Three, ← map_mul]
          rfl
  obtain ⟨σ, hσ⟩ := hdiagAll B₀ hB₀S hB₀
  by_cases hinj : Function.Injective σ
  · left
    exact regU3Three_of_conj Q₂ (fun a b h => hinj (Units.ext h)) (hconjDiag hσ)
  · right
    have hnc : ∃ a b, σ a ≠ σ b := by
      by_contra hc
      push Not at hc
      exact hB₀s _ (eq_scalar_of_conj_U3Three (hσ.trans (diagHom_eq_scalar_U3Three hc)))
    obtain ⟨u, v', huv⟩ := hnc
    exact ⟨Q₂, σ, u, v', P₂.2, hdiagAll, hσ, hinj, huv⟩

end ResU3Eight

end CFSG.StandardType

end
