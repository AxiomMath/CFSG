module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreLine
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

namespace ResU3Three

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv diagHom_commute)

@[expose] def regSetU3Three {k K : Type} [Field k] [Field K] (j : k →+* K) (q : ℕ) :
    Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) k q))) :=
  {φ | ∃ (B : GL (Fin 3) k)
    (hB : B ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin 3) k q : Set (GL (Fin 3) k))),
      B ∈ LargeEvenGUSet (Fin 3) k q ∧ RegU3Three ((B : Matrix (Fin 3) (Fin 3) k).map j) ∧
        φ = TableB.projConj _ ⟨B, hB⟩}

section Mat

variable {k : Type} [Field k]

theorem dq_ne_U3Three {m : ℕ} (hm : 2 ≤ m) : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := by
  intro h
  have h2 : 2 ^ m = 2 := congrArg Prod.snd h
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem scalar_eq_diagHom_U3Three (c : kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c = diagHom 3 (fun _ => c) := by
  apply Units.ext
  rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem diagHom_eq_scalar_U3Three {σ : Fin 3 → kˣ} (hσ : ∀ a b, σ a = σ b) :
    diagHom 3 σ = Matrix.GeneralLinearGroup.scalar (Fin 3) (σ 0) := by
  rw [scalar_eq_diagHom_U3Three]
  congr 1
  funext a
  exact hσ a 0

theorem scalar_mul_comm_U3Three (c : kˣ) (X : GL (Fin 3) k) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c * X =
      X * Matrix.GeneralLinearGroup.scalar (Fin 3) c :=
  TypeA.PGLTor.scalar_mul_comm c X

theorem conj_scalar_U3Three (P : GL (Fin 3) k) (c : kˣ) :
    P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) c * P =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  rw [mul_assoc, scalar_mul_comm_U3Three, ← mul_assoc, inv_mul_cancel, one_mul]

theorem eq_scalar_of_conj_U3Three {P X : GL (Fin 3) k} {c : kˣ}
    (h : P⁻¹ * X * P = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    X = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  calc X = P * (P⁻¹ * X * P) * P⁻¹ := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      rw [h, mul_assoc, scalar_mul_comm_U3Three, ← mul_assoc, mul_inv_cancel, one_mul]

theorem coe_scalar_mul_U3Three (c : kˣ) (X : GL (Fin 3) k) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) c * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (c : k) • (X : Matrix (Fin 3) (Fin 3) k) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_eq_diagonal_mul]

theorem eq_one_of_smul_eq_U3Three {c : k} {v : Fin 3 → k} (hv : v ≠ 0) (h : c • v = v) : c = 1 := by
  obtain ⟨t, ht⟩ : ∃ t, v t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  have h1 := congrFun h t
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  have h2 : (c - 1) * v t = 0 := by linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ht)

theorem scalar_eq_one_of_fix_U3Three {c : kˣ} {v : Fin 3 → k} (hv : v ≠ 0)
    (h : ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) *ᵥ v = v) : c = 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h
  have h' : (c : k) • v = v := by
    funext t
    have := congrFun h t
    rw [Matrix.mulVec_diagonal] at this
    simpa using this
  exact Units.ext (eq_one_of_smul_eq_U3Three hv h')

theorem det_scalar_U3Three (c : kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k).det = (c : k) ^ 3 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Mat

section Proj

variable {k : Type} [Field k] [Finite k] {m : ℕ}

local notation "H₀" => LargeEvenSUGroup (Fin 3) k (2 ^ m)
local notation "N₀" => Subgroup.normalizer (LargeEvenSUGroup (Fin 3) k (2 ^ m) : Set (GL (Fin 3) k))
local notation "ρ₀" => TableB.projConj (LargeEvenSUGroup (Fin 3) k (2 ^ m))

theorem exists_scalar_of_projConj_eq_one_U3Three (hk : Nat.card k = (2 ^ m) ^ 2) (hm : 2 ≤ m)
    (h3 : 3 ∣ 2 ^ m + 1) {M : N₀} (hM : ρ₀ M = 1) :
    ∃ c : kˣ, (M : GL (Fin 3) k) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  have h₀ := TableBU.unitaryFieldData_of_card hk (by omega)
  obtain ⟨c, hc⟩ := TableBUE.mem_scalars_of_projConj_eq_one h₀ hk le_rfl (dq_ne_U3Three hm)
    Nat.prime_three h3 hM
  exact ⟨c, hc.symm⟩

theorem eq_scalar_mul_of_projConj_eq_U3Three (hk : Nat.card k = (2 ^ m) ^ 2) (hm : 2 ≤ m)
    (h3 : 3 ∣ 2 ^ m + 1) {M M' : N₀} (h : ρ₀ M = ρ₀ M') :
    ∃ c : kˣ, (M : GL (Fin 3) k) = Matrix.GeneralLinearGroup.scalar (Fin 3) c * M' := by
  obtain ⟨c, hc⟩ := exists_scalar_of_projConj_eq_one_U3Three hk hm h3 (M := M * M'⁻¹)
    (by rw [map_mul, map_inv, h, mul_inv_cancel])
  refine ⟨c, ?_⟩
  rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]

theorem exists_comm_scalar_U3Three (hk : Nat.card k = (2 ^ m) ^ 2) (hm : 2 ≤ m)
    (h3 : 3 ∣ 2 ^ m + 1) {M M' : N₀} (h : ρ₀ M * ρ₀ M' = ρ₀ M' * ρ₀ M) :
    ∃ c : kˣ, (M : GL (Fin 3) k) * M' =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * ((M' : GL (Fin 3) k) * M) := by
  obtain ⟨c, hc⟩ := eq_scalar_mul_of_projConj_eq_U3Three hk hm h3 (M := M * M') (M' := M' * M)
    (by rw [map_mul, map_mul, h])
  exact ⟨c, hc⟩

theorem exists_cube_scalar_U3Three (hk : Nat.card k = (2 ^ m) ^ 2) (hm : 2 ≤ m)
    (h3 : 3 ∣ 2 ^ m + 1) {M : N₀} (h : ρ₀ M ^ 3 = 1) :
    ∃ c : kˣ, (M : GL (Fin 3) k) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨c, hc⟩ := exists_scalar_of_projConj_eq_one_U3Three hk hm h3 (M := M ^ 3)
    (by rw [map_pow, h])
  exact ⟨c, by rw [← hc, Subgroup.coe_pow]⟩

omit [Finite k] in
theorem projConj_scalar_mul_U3Three (c : kˣ) {B : GL (Fin 3) k} (hB : B ∈ N₀)
    (hcB : Matrix.GeneralLinearGroup.scalar (Fin 3) c * B ∈ N₀) :
    ρ₀ ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) c * B, hcB⟩ = ρ₀ ⟨B, hB⟩ := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ LargeEvenScalars (Fin 3) k := ⟨c, rfl⟩
  have e := map_mul ρ₀ ⟨_, TableB.scalar_mem_normalizer _ hz⟩ ⟨B, hB⟩
  rw [TableB.projConj_of_scalar _ hz, one_mul] at e
  exact e

theorem act_of_lift_U3Three (hk : Nat.card k = (2 ^ m) ^ 2) (hm : 2 ≤ m) {L'' : Type} [Group L'']
    {ψ : L'' →* LargeEvenProj H₀} (hker : ψ.ker ≤ Subgroup.center L'') {α : H₀ →* L''}
    (hα : ∀ g, ψ (α g) = LargeEvenProjMk H₀ g) {a : MulAut L''} (M : N₀)
    (hind : ∀ l, ρ₀ M (ψ l) = ψ (a l)) (s : H₀) :
    a (α s) = α ((LargeEvenSUGroup (Fin 3) k (2 ^ m)).normalizerMonoidHom M s) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect H₀ :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := m) hk le_rfl (dq_ne_U3Three hm)
  refine CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hker hperf
    ((a : L'' ≃* L'').toMonoidHom.comp α)
    (α.comp ((LargeEvenSUGroup (Fin 3) k (2 ^ m)).normalizerMonoidHom M).toMonoidHom)
    (fun u => ?_) s
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← hind, hα, hα]
  rfl

omit [Finite k] in
theorem regU3Three_of_partner_GL [CharP k 2] {ω : k} (hω : ω ^ 2 + ω + 1 = 0)
    {B₀ B : GL (Fin 3) k} {e₀ : kˣ}
    (he₀ : B₀ ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (e₀ ^ 3)) {ζ : kˣ}
    (hζ : B * B₀ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (B₀ * B)) (hζ1 : ζ ≠ 1) :
    RegU3Three (B₀ : Matrix (Fin 3) (Fin 3) k) := by
  have hdet := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k).det) hζ
  simp only [Units.val_mul, Matrix.det_mul, det_scalar_U3Three] at hdet
  have hne : (B : Matrix (Fin 3) (Fin 3) k).det * (B₀ : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
    mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero
      ((Matrix.isUnit_iff_isUnit_det _).mp B₀.isUnit).ne_zero
  have hζ3 : (ζ : k) ^ 3 = 1 := by
    have h1 : ((ζ : k) ^ 3 - 1) * ((B : Matrix (Fin 3) (Fin 3) k).det *
        (B₀ : Matrix (Fin 3) (Fin 3) k).det) = 0 := by linear_combination -hdet
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hne)
  have hζ1' : (ζ : k) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hζ1 (Units.ext h)
  have hζ' : (ζ : k) ^ 2 + ζ + 1 = 0 := by
    have h1 : ((ζ : k) - 1) * ((ζ : k) ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.mp h1).resolve_left hζ1'
  set X : Matrix (Fin 3) (Fin 3) k := ((e₀⁻¹ : kˣ) : k) • (B₀ : Matrix (Fin 3) (Fin 3) k)
    with hXdef
  have hB₀3 : (B₀ : Matrix (Fin 3) (Fin 3) k) ^ 3 = ((e₀ : k) ^ 3) • 1 := by
    have h1 := congrArg Units.val he₀
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Units.val_pow_eq_pow_val] at h1
    exact h1
  have hX3 : X ^ 3 = 1 := by
    rw [hXdef, smul_pow, hB₀3, smul_smul, ← mul_pow, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_pow, one_smul]
  have hBB₀ : (B : Matrix (Fin 3) (Fin 3) k) * B₀ =
      (ζ : k) • ((B₀ : Matrix (Fin 3) (Fin 3) k) * B) := by
    have h1 := congrArg Units.val hζ
    rwa [Units.val_mul, coe_scalar_mul_U3Three, Units.val_mul] at h1
  have hYX : (B : Matrix (Fin 3) (Fin 3) k) * X = (ζ : k) • (X * B) := by
    rw [hXdef, Matrix.mul_smul, hBB₀, smul_comm, smul_mul_assoc]
  have hreg := regU3Three_of_partner hω hX3 B.isUnit hζ' hYX
  have hB₀X : (B₀ : Matrix (Fin 3) (Fin 3) k) = (e₀ : k) • X := by
    rw [hXdef, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  rw [hB₀X]
  exact hreg.smul e₀.ne_zero

theorem reg_or_frame_U3Three (h₀ : UnitaryFieldData 2 m k) (hk : Nat.card k = (2 ^ m) ^ 2)
    (hm : 2 ≤ m) (h3 : 3 ∣ 2 ^ m + 1) {Ab : Subgroup (MulAut (LargeEvenProj H₀))}
    (hAb : IsElemAbelian 3 Ab) {B₀ : GL (Fin 3) k} (hB₀ : B₀ ∈ LargeEvenGUSet (Fin 3) k (2 ^ m))
    (hB₀N : B₀ ∈ N₀) (hB₀A : ρ₀ ⟨B₀, hB₀N⟩ ∈ Ab)
    (hB₀s : ∀ c : kˣ, B₀ ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) c) {e₀ : kˣ}
    (he₀ : B₀ ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (e₀ ^ 3))
    (hcomm : ∀ (B : GL (Fin 3) k) (hB : B ∈ N₀), ρ₀ ⟨B, hB⟩ ∈ Ab →
      B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m) → B * B₀ = B₀ * B) :
    RegU3Three (B₀ : Matrix (Fin 3) (Fin 3) k) ∨
      ∃ (P : GL (Fin 3) k) (σ : Fin 3 → kˣ) (u v : Fin 3),
        P ∈ primeFormUnitary h₀ (idGram k 3) ∧
        (∀ (B : GL (Fin 3) k) (hB : B ∈ N₀), ρ₀ ⟨B, hB⟩ ∈ Ab →
          B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m) → ∃ τ : Fin 3 → kˣ, P⁻¹ * B * P = diagHom 3 τ) ∧
        P⁻¹ * B₀ * P = diagHom 3 σ ∧ ¬ Function.Injective σ ∧ σ u ≠ σ v := by
  classical
  haveI : CharP k 2 := h₀.charP
  have hN := TableBUE.gu_subset_normalizer (d := 3) h₀
  have hNU : ∀ {x : GL (Fin 3) k}, x ∈ primeFormUnitary h₀ (idGram k 3) → x ∈ N₀ :=
    fun hx => hN (TableBUD.mem_guSet_of_mem_primeFormUnitary h₀ hx)
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
  have heig : ∀ (B : GL (Fin 3) k) (hB : B ∈ N₀), ρ₀ ⟨B, hB⟩ ∈ Ab →
      B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m) →
        ∃ c : kˣ, (B : Matrix (Fin 3) (Fin 3) k) *ᵥ v = (c : k) • v := by
    intro B hB hBA hBgu
    have hBX : B * X = X * B := by
      rw [hXdef, ← mul_assoc, ← scalar_mul_comm_U3Three, mul_assoc, hcomm B hB hBA hBgu,
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
  have hUN : primeFormUnitary h₀ (idGram k 3) ≤ N₀ := fun x hx => hNU hx
  set ιU : primeFormUnitary h₀ (idGram k 3) →* N₀ := Subgroup.inclusion hUN with hιU
  have hιU : ∀ x, ((ιU x : N₀) : GL (Fin 3) k) = (x : GL (Fin 3) k) := fun _ => rfl
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
  let G : Subgroup (primeFormUnitary h₀ (idGram k 3)) := Gv ⊓ Ab.comap (MonoidHom.comp ρ₀ ιU)
  have hmemG : ∀ x, x ∈ G ↔ ((x : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v ∧
      ρ₀ (ιU x) ∈ Ab := fun x => Iff.rfl
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    rw [hmemG] at hx hy
    obtain ⟨c, hc⟩ := exists_comm_scalar_U3Three hk hm h3 (M := ιU x) (M' := ιU y)
      (TableB.IsElemAbelian.comm hAb hx.2 hy.2)
    have hc' : (x : GL (Fin 3) k) * y =
        Matrix.GeneralLinearGroup.scalar (Fin 3) c * ((y : GL (Fin 3) k) * x) := by
      rw [← hιU x, ← hιU y]
      exact hc
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
    obtain ⟨c, hc⟩ := exists_cube_scalar_U3Three hk hm h3 (M := ιU x) (hAb.2 _ hx.2)
    have hc' : (x : GL (Fin 3) k) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hιU x]
      exact hc
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
  have hdiagAll : ∀ (B : GL (Fin 3) k) (hB : B ∈ N₀), ρ₀ ⟨B, hB⟩ ∈ Ab →
      B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m) → ∃ τ : Fin 3 → kˣ, Q₂⁻¹ * B * Q₂ = diagHom 3 τ := by
    intro B hB hBA hBgu
    obtain ⟨c, hc⟩ := heig B hB hBA hBgu
    set Y : GL (Fin 3) k := Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ * B with hYdef
    have hYv : (Y : Matrix (Fin 3) (Fin 3) k) *ᵥ v = v := by
      rw [hYdef, coe_scalar_mul_U3Three, Matrix.smul_mulVec, hc, smul_smul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul]
    have hYN : Y ∈ N₀ := Subgroup.mul_mem _ (TableB.scalar_mem_normalizer _ ⟨c⁻¹, rfl⟩) hB
    have hYρ : ρ₀ ⟨Y, hYN⟩ = ρ₀ ⟨B, hB⟩ := projConj_scalar_mul_U3Three c⁻¹ hB hYN
    have hY3 : Y ^ 3 = 1 := by
      obtain ⟨z, hz⟩ := exists_cube_scalar_U3Three hk hm h3 (M := ⟨Y, hYN⟩)
        (by rw [hYρ]; exact hAb.2 _ hBA)
      have hz' : Y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) z := hz
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
      refine ⟨hYv, ?_⟩
      have e : ιU ⟨Y, hYU⟩ = ⟨Y, hYN⟩ := Subtype.ext rfl
      rw [e, hYρ]
      exact hBA
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
  obtain ⟨σ, hσ⟩ := hdiagAll B₀ hB₀N hB₀A hB₀
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

omit [Finite k] in
theorem exists_omega_U3Three (h₀ : UnitaryFieldData 2 m k) (h3 : 3 ∣ 2 ^ m + 1) :
    ∃ ω : k, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h₀ Nat.prime_three h3
  refine ⟨ζ, ?_⟩
  have h := hζ.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h
  linear_combination h

theorem ggTorusNoLineTwoKX_u3Three
    {K : Type} [Field K] [CharP K 2] (j : k →+* K)
    (hk : Nat.card k = (2 ^ m) ^ 2) (hm : 2 ≤ m) (h3 : 3 ∣ 2 ^ m + 1)
    (hcube : ∀ c : k, ∃ e : K, e ^ 3 = j c) (Kp : ℕ → Prop) :
    GGTorusNoLineTwoKX 3 Kp (LargeEvenProj H₀)
      (LargeEvenMatConjImage (LargeEvenProjMk H₀) (LargeEvenGUSet (Fin 3) k (2 ^ m)))
      (regSetU3Three j (2 ^ m)) := by
  classical
  intro L'' _ _ ψ hψ hker hperf _ A hA hAI _ _
  have h₀ : UnitaryFieldData 2 m k := TableBU.unitaryFieldData_of_card hk (by omega)
  haveI : CharP k 2 := h₀.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdq := dq_ne_U3Three hm
  have hN := TableBUE.gu_subset_normalizer (d := 3) h₀
  obtain ⟨ω, hω⟩ := exists_omega_U3Three h₀ h3
  haveI : Finite H₀ := Finite.of_injective
    (fun x : H₀ => ((x : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  obtain ⟨α, -, hα⟩ := exists_cover_of_sections (LargeEvenProjMk H₀)
    (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := k) (p := 2) (f := m) hk (by omega) le_rfl (by decide) hdq hπ hcen)
    ψ hψ hker hperf
  have hlift : ∀ a ∈ A, ∃ B : GL (Fin 3) k, ∃ hB : B ∈ LargeEvenGUSet (Fin 3) k (2 ^ m),
      ∀ l, ρ₀ ⟨B, hN hB⟩ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨B, hB, rfl⟩ := TableB.exists_eq_projConj hN hφI
    exact ⟨B, hB, hφ⟩
  choose Bf hBgu hBind using hlift
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAb : IsElemAbelian 3 Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hBAb : ∀ a (ha : a ∈ A), ρ₀ ⟨Bf a ha, hN (hBgu a ha)⟩ ∈ Ab :=
    fun a ha => ⟨a, ha, hBind a ha⟩
  refine ⟨{n | ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹},
    fun n hn => hn, fun _ a₀ ha₀ hne => ?_⟩
  have hB₀N := hN (hBgu a₀ ha₀)
  have hB₀s : ∀ c : kˣ, Bf a₀ ha₀ ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    intro c hc
    apply hne
    refine ggAut_eq_one_of_induced_one ψ hker hperf a₀ fun l => ?_
    rw [← hBind a₀ ha₀ l]
    have hz : Bf a₀ ha₀ ∈ LargeEvenScalars (Fin 3) k := ⟨c, hc.symm⟩
    rw [TableB.projConj_of_scalar _ hz]
    rfl
  obtain ⟨s₀, hs₀⟩ := exists_cube_scalar_U3Three hk hm h3 (M := ⟨Bf a₀ ha₀, hB₀N⟩)
    (hAb.2 _ (hBAb a₀ ha₀))
  have hs₀' : Bf a₀ ha₀ ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) s₀ := hs₀
  have hleft : RegU3Three ((Bf a₀ ha₀ : Matrix (Fin 3) (Fin 3) k).map j) →
      ∃ φ ∈ regSetU3Three j (2 ^ m), ∀ l, φ (ψ l) = ψ (a₀ l) :=
    fun hreg => ⟨_, ⟨Bf a₀ ha₀, hB₀N, hBgu a₀ ha₀, hreg, rfl⟩, hBind a₀ ha₀⟩
  by_cases hcub : ∃ e₀ : kˣ, e₀ ^ 3 = s₀
  swap
  ·
    left
    apply hleft
    push Not at hcub
    obtain ⟨e, he⟩ := hcube s₀
    refine regU3Three_of_not_cube j hω (s := (s₀ : k)) ?_ (fun e' he' => ?_) he
    · have h1 := congrArg Units.val hs₀'
      rwa [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal] at h1
    · have he'0 : e' ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num)] at he'
        exact s₀.ne_zero he'.symm
      exact hcub (Units.mk0 e' he'0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0,
        he']))
  obtain ⟨e₀, he₀⟩ := hcub
  have he₀' : Bf a₀ ha₀ ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (e₀ ^ 3) := by
    rw [he₀]
    exact hs₀'
  by_cases hpart : ∃ (B : GL (Fin 3) k) (hB : B ∈ N₀), ρ₀ ⟨B, hB⟩ ∈ Ab ∧
      B * Bf a₀ ha₀ ≠ Bf a₀ ha₀ * B
  ·
    obtain ⟨B, hB, hBA, hBne⟩ := hpart
    left
    apply hleft
    obtain ⟨ζ, hζ⟩ := exists_comm_scalar_U3Three hk hm h3 (M := ⟨B, hB⟩)
      (M' := ⟨Bf a₀ ha₀, hB₀N⟩) (TableB.IsElemAbelian.comm hAb hBA (hBAb a₀ ha₀))
    have hζ' : B * Bf a₀ ha₀ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (Bf a₀ ha₀ * B) := hζ
    have hζ1 : ζ ≠ 1 := fun h => hBne (by rw [hζ', h, map_one, one_mul])
    exact (regU3Three_of_partner_GL hω he₀' hζ' hζ1).map j
  push Not at hpart
  rcases reg_or_frame_U3Three h₀ hk hm h3 hAb (hBgu a₀ ha₀) hB₀N (hBAb a₀ ha₀) hB₀s he₀'
      (fun B hB hBA _ => hpart B hB hBA) with hreg | ⟨P, σ, u, v, hPU, hdiag, hσ, hninj, huv⟩
  · left
    exact hleft (hreg.map j)
  right
  set cP : MulAut (GL (Fin 3) k) := MulAut.conj P⁻¹ with hcPdef
  have hcP : ∀ X, cP X = P⁻¹ * X * P := fun X => by rw [hcPdef, MulAut.conj_apply, inv_inv]
  have hcPs : ∀ c : kˣ, cP (Matrix.GeneralLinearGroup.scalar (Fin 3) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := fun c => by rw [hcP, conj_scalar_U3Three]
  set τ : Equiv.Perm (Fin 3) := Equiv.swap u v with hτ
  have hτmem : permGL τ ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 m k 3 :=
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.permGL_mem_su τ
  set w : H₀ := (TableBUE.conjSU h₀ P hPU).symm ⟨permGL τ, hτmem⟩ with hwdef
  have hw : (w : GL (Fin 3) k) = P * permGL τ * P⁻¹ := rfl
  have hcPw : cP (w : GL (Fin 3) k) = permGL τ := by rw [hcP, hw]; group
  have hdiag' : ∀ a (ha : a ∈ A), ∃ σa : Fin 3 → kˣ, cP (Bf a ha) = diagHom 3 σa := by
    intro a ha
    obtain ⟨σa, h⟩ := hdiag (Bf a ha) (hN (hBgu a ha)) (hBAb a ha) (hBgu a ha)
    exact ⟨σa, by rw [hcP]; exact h⟩
  refine ⟨α w, fun a ha => ?_, ?_⟩
  ·
    obtain ⟨σa, hσa⟩ := hdiag' a ha
    obtain ⟨sa, hsa⟩ := exists_cube_scalar_U3Three hk hm h3 (M := ⟨Bf a ha, hN (hBgu a ha)⟩)
      (hAb.2 _ (hBAb a ha))
    have hsa' : Bf a ha ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) sa := hsa
    have hσa3 : ∀ t, σa t ^ 3 = sa := by
      have h1 : diagHom 3 (σa ^ 3) = diagHom 3 (fun _ => sa) := by
        rw [map_pow, ← hσa, ← map_pow, hsa', hcPs, scalar_eq_diagHom_U3Three]
      intro t
      exact congrFun (diagHom_injective 3 h1) t
    rw [act_of_lift_U3Three hk hm hker hα ⟨Bf a ha, hN (hBgu a ha)⟩ (hBind a ha) w, ← map_inv,
      ← map_mul]
    set y : H₀ := w * ((LargeEvenSUGroup (Fin 3) k (2 ^ m)).normalizerMonoidHom
      ⟨Bf a ha, hN (hBgu a ha)⟩ w)⁻¹ with hydef
    have hy : (y : GL (Fin 3) k) = (w : GL (Fin 3) k) * Bf a ha * (w : GL (Fin 3) k)⁻¹ *
        (Bf a ha)⁻¹ := by
      rw [hydef, Subgroup.coe_mul, Subgroup.coe_inv]
      change (w : GL (Fin 3) k) * (Bf a ha * (w : GL (Fin 3) k) * (Bf a ha)⁻¹)⁻¹ = _
      group
    have hcPy : cP (y : GL (Fin 3) k) = diagHom 3 (σa ∘ τ.symm * σa⁻¹) := by
      rw [hy, map_mul, map_mul, map_mul, map_inv, map_inv, hcPw, hσa,
        permGL_mul_diagHom_mul_inv, ← map_inv, ← map_mul]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [← map_pow]
      have hy3 : y ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        apply cP.injective
        rw [map_pow, hcPy, ← map_pow, map_one]
        have h1 : (σa ∘ τ.symm * σa⁻¹) ^ 3 = 1 := by
          funext t
          simp only [Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, Function.comp_apply,
            Pi.one_apply, mul_pow, inv_pow, hσa3, mul_inv_cancel]
        rw [h1, map_one]
      rw [hy3, map_one]
    · obtain ⟨σa', hσa'⟩ := hdiag' a' ha'
      rw [act_of_lift_U3Three hk hm hker hα ⟨Bf a' ha', hN (hBgu a' ha')⟩ (hBind a' ha') y]
      congr 1
      apply Subtype.ext
      change Bf a' ha' * (y : GL (Fin 3) k) * (Bf a' ha')⁻¹ = y
      have hc : Bf a' ha' * (y : GL (Fin 3) k) = (y : GL (Fin 3) k) * Bf a' ha' := by
        apply cP.injective
        rw [map_mul, map_mul, hσa', hcPy]
        exact (diagHom_commute _ _).eq
      rw [hc, mul_inv_cancel_right]
  ·
    intro hmem
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : ρ₀ ⟨Bf a₀ ha₀, hB₀N⟩ ^ t = MulAut.conj (ψ (α w)) * ρ₀ ⟨Bf a₀ ha₀, hB₀N⟩ *
        (MulAut.conj (ψ (α w)))⁻¹ := by
      apply ggInduced_unique hψ (a := a₀ ^ t)
      · exact TableBUD.induced_zpow (hBind a₀ ha₀) t
      · intro l
        rw [ht]
        exact ggInduced_conj_mul_conj_inv ψ (α w) (hBind a₀ ha₀) l
    have hwN : (w : GL (Fin 3) k) ∈ N₀ := Subgroup.le_normalizer w.2
    have hcw : MulAut.conj (ψ (α w)) = ρ₀ ⟨w, hwN⟩ := by
      rw [hα w]
      exact (TableB.projConj_of_mem _ (w : GL (Fin 3) k) w.2).symm
    rw [hcw] at h1
    have h2 : ρ₀ (⟨Bf a₀ ha₀, hB₀N⟩ ^ t) =
        ρ₀ (⟨w, hwN⟩ * ⟨Bf a₀ ha₀, hB₀N⟩ * (⟨w, hwN⟩ : N₀)⁻¹) := by
      rw [map_zpow, map_mul, map_mul, map_inv, h1]
    obtain ⟨z, hz⟩ := eq_scalar_mul_of_projConj_eq_U3Three hk hm h3 h2
    have hz' : Bf a₀ ha₀ ^ t = Matrix.GeneralLinearGroup.scalar (Fin 3) z *
        ((w : GL (Fin 3) k) * Bf a₀ ha₀ * (w : GL (Fin 3) k)⁻¹) := by
      simpa only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] using hz
    have hσ' : cP (Bf a₀ ha₀) = diagHom 3 σ := by rw [hcP]; exact hσ
    have h3' : diagHom 3 (σ ^ t) = diagHom 3 ((fun _ => z) * (σ ∘ τ.symm)) := by
      have h4 := congrArg cP hz'
      rw [map_zpow, hσ', map_mul, hcPs, map_mul, map_mul, map_inv, hcPw, hσ',
        permGL_mul_diagHom_mul_inv, scalar_eq_diagHom_U3Three, ← map_zpow, ← map_mul] at h4
      exact h4
    apply not_forall_swap_U3Three hninj huv z⁻¹ t
    intro i
    have h5 := congrFun (diagHom_injective 3 h3') i
    simp only [Pi.pow_apply, Pi.mul_apply, Function.comp_apply, hτ, Equiv.symm_swap] at h5
    rw [h5, inv_mul_cancel_left]

end Proj

end ResU3Three

end CFSG.StandardType

end
