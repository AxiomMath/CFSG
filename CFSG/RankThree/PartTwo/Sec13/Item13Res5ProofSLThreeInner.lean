module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofTools
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix
open scoped commutatorElement

namespace Res5Proof

theorem exists_orderOf_eq_three_fixed_of_invariant {X : Type*} [Group X] [Finite X]
    {B : Subgroup (MulAut X)} (hB : ∀ β ∈ B, β ^ 3 = 1) {H : Subgroup X}
    (hH : ∀ β ∈ B, ∀ h ∈ H, β h ∈ H) (h3 : 3 ∣ Nat.card H) :
    ∃ x ∈ H, orderOf x = 3 ∧ ∀ β ∈ B, β x = x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 B := fun β => ⟨1, Subtype.ext (by simpa using hB β β.2)⟩
  let _ : MulAction B H :=
    { smul := fun β h => ⟨(β : MulAut X) h, hH β β.2 h h.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl }
  have hmod := hBp.card_modEq_card_fixedPoints H
  let F : Subgroup H :=
    { carrier := {h | ∀ β ∈ B, β (h : X) = h}
      mul_mem' := by
        intro a b ha hb β hβ
        change β ((a : X) * b) = (a : X) * b
        rw [map_mul, ha β hβ, hb β hβ]
      one_mem' := fun β _ => by
        change β (1 : X) = 1
        exact map_one β
      inv_mem' := by
        intro a ha β hβ
        change β ((a : X)⁻¹) = (a : X)⁻¹
        rw [map_inv, ha β hβ] }
  have hfix : Nat.card (MulAction.fixedPoints B H) = Nat.card F := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => ?_)
    constructor
    · intro hh β hβ
      exact congrArg Subtype.val (hh ⟨β, hβ⟩)
    · intro hh β
      exact Subtype.ext (hh β β.2)
  have hF3 : 3 ∣ Nat.card F := by
    rw [hfix] at hmod
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 3 hF3
  refine ⟨((x : H) : X), (x : H).2, ?_, x.2⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]

section Matrices

variable {K : Type} [Field K]

@[expose] def swapTwelve (K : Type) [Field K] : GL (Fin 3) K :=
  ⟨!![-1, 0, 0; 0, 0, -1; 0, -1, 0], !![-1, 0, 0; 0, 0, -1; 0, -1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapTwelve : ((swapTwelve K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![-1, 0, 0; 0, 0, -1; 0, -1, 0] :=
  rfl

theorem swapTwelve_inv : (swapTwelve K)⁻¹ = swapTwelve K :=
  rfl

theorem swapTwelve_mem_slPi {π : Bool} {p f : ℕ} (hπ : π = false → UnitaryFieldData p f K) :
    swapTwelve K ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((swapTwelve K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_swapTwelve, det_fin_three]
    simp
  cases π
  · have h := hπ rfl
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    rw [coe_swapTwelve]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, transpose_apply]
  · rw [mem_slPi_true]
    exact hdet

theorem swapTwelve_comm_diagE (e : Kˣ) : swapTwelve K * diagE e = diagE e * swapTwelve K := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swapTwelve, coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal]

theorem diagTau_comm_diagE {τ : K} (hτ : τ ^ 3 = 1) (e : Kˣ) :
    diagTau hτ * diagE e = diagE e * diagTau hτ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagTau, coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal, mul_comm]

@[expose] def diagOneTau {τ : K} (hτ : τ ^ 3 = 1) : GL (Fin 3) K :=
  ⟨!![1, 0, 0; 0, τ, 0; 0, 0, τ ^ 2], !![1, 0, 0; 0, τ ^ 2, 0; 0, 0, τ],
    by
      have h : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
      have h' : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h, h'],
    by
      have h : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
      have h' : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h, h']⟩

theorem coe_diagOneTau {τ : K} (hτ : τ ^ 3 = 1) :
    ((diagOneTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, τ, 0; 0, 0, τ ^ 2] :=
  rfl

theorem commutator_swapTwelve_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    swapTwelve K * diagTau hτ * (swapTwelve K)⁻¹ * (diagTau hτ)⁻¹ = diagOneTau hτ := by
  rw [mul_inv_eq_iff_eq_mul, swapTwelve_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_swapTwelve, coe_diagTau, coe_diagOneTau]
  have h3 : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h3]

theorem diagOneTau_ne_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : diagOneTau hτ ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) h
  simp only [coe_diagOneTau, Units.val_one] at h1
  simp at h1
  exact hτ1 h1

theorem diagOneTau_pow_three {τ : K} (hτ : τ ^ 3 = 1) : diagOneTau hτ ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_diagOneTau, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination hτ | linear_combination (τ ^ 3 + 1) * hτ

theorem diagTau_ne_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : diagTau hτ ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [coe_diagTau, Units.val_one] at h1
  simp at h1
  exact hτ1 h1

theorem diagTau_ne_scalar {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (c : Kˣ) :
    diagTau hτ ≠ GeneralLinearGroup.scalar (Fin 3) c := by
  intro h
  have h0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) h
  simp only [coe_diagTau, GeneralLinearGroup.coe_scalar] at h0 h2
  simp at h0 h2
  exact hτ1 (h0.trans h2.symm)

end Matrices

section Inner

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem conj_mul_scalar_eq {y : slPi π 3 (p ^ f) K} {y₀ : slPi π 3 (p ^ f) K} {c : Kˣ}
    (h : (y₀ : GL (Fin 3) K) = (y : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c) :
    MulAut.conj y₀ = MulAut.conj y := by
  refine MulEquiv.ext fun s => Subtype.ext ?_
  change (y₀ : GL (Fin 3) K) * s * (y₀ : GL (Fin 3) K)⁻¹ = (y : GL (Fin 3) K) * s *
    (y : GL (Fin 3) K)⁻¹
  rw [h]
  have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (s : GL (Fin 3) K)).eq
  calc (y : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c * s *
        ((y : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c)⁻¹ =
      (y : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) c * s) *
        (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * (y : GL (Fin 3) K)⁻¹ := by group
    _ = (y : GL (Fin 3) K) * (s * GeneralLinearGroup.scalar (Fin 3) c) *
        (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * (y : GL (Fin 3) K)⁻¹ := by rw [hc]
    _ = _ := by group

theorem map_mem_commutator_centralizer {G : Type*} [Group G] {y : G} {β : MulAut G}
    (hβ : β y = y) {k : G}
    (hk : k ∈ ⁅Subgroup.centralizer {y}, Subgroup.centralizer {y}⁆) :
    β k ∈ ⁅Subgroup.centralizer {y}, Subgroup.centralizer {y}⁆ := by
  have hC : (Subgroup.centralizer ({y} : Set G)).map β.toMonoidHom ≤
      Subgroup.centralizer {y} := by
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    change β c * y = y * β c
    rw [← hβ, ← map_mul, ← map_mul, hc]
  have h1 : β k ∈ (⁅Subgroup.centralizer {y}, Subgroup.centralizer {y}⁆).map β.toMonoidHom :=
    ⟨k, hk, rfl⟩
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hC hC h1

theorem exists_smul_of_commute_conj_diagE {g c : GL (Fin 3) K} {e : Kˣ} (he : (e : K) ≠ 1)
    (hc : c * (g * diagE e * g⁻¹) = g * diagE e * g⁻¹ * c) :
    ∃ a : K, (c : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ
      Pi.single 0 1) = a • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1) := by
  set M : GL (Fin 3) K := g⁻¹ * c * g with hM
  have hMd : M * diagE e = diagE e * M := by
    rw [hM]
    calc g⁻¹ * c * g * diagE e = g⁻¹ * (c * (g * diagE e * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * diagE e * g⁻¹ * c) * g := by rw [hc]
      _ = diagE e * (g⁻¹ * c * g) := by group
  have hMd' := congrArg Units.val hMd
  rw [Units.val_mul, Units.val_mul, coe_diagE] at hMd'
  have h10 : (M : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 :=
    entry_eq_zero_of_commute_diagonal hMd' (by simpa using Ne.symm he)
  have h20 : (M : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    entry_eq_zero_of_commute_diagonal hMd' (by simpa using Ne.symm he)
  have hMe : (M : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 =
      (M : Matrix (Fin 3) (Fin 3) K) 0 0 • Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, h10, h20, Pi.single_apply]
  refine ⟨(M : Matrix (Fin 3) (Fin 3) K) 0 0, ?_⟩
  have hcg : (c : Matrix (Fin 3) (Fin 3) K) * g = g * M := by
    rw [hM, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  rw [mulVec_mulVec, hcg, ← mulVec_mulVec, hMe, mulVec_smul]

theorem commutator_mulVec_eq {a b : GL (Fin 3) K} {v : Fin 3 → K} {x y : K}
    (ha : (a : Matrix (Fin 3) (Fin 3) K) *ᵥ v = x • v)
    (hb : (b : Matrix (Fin 3) (Fin 3) K) *ᵥ v = y • v) (hv : v ≠ 0) :
    ((a * b * a⁻¹ * b⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
  have hinv : ∀ (u : GL (Fin 3) K) (z : K), (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v = z • v →
      z ≠ 0 ∧ ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = z⁻¹ • v := by
    intro u z hu
    have hz : z ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hu
      apply hv
      have := congrArg (fun w => ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) hu
      simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
        mulVec_zero] at this
      exact this
    refine ⟨hz, ?_⟩
    have := congrArg (fun w => ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) hu
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      mulVec_smul] at this
    calc ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
        z⁻¹ • (z • ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = z⁻¹ • v := by rw [← this]
  obtain ⟨hx, hai⟩ := hinv a x ha
  obtain ⟨hy, hbi⟩ := hinv b y hb
  simp only [Units.val_mul, ← mulVec_mulVec, hbi, mulVec_smul, hai, hb, ha, smul_smul]
  rw [show y⁻¹ * (x⁻¹ * (y * x)) = 1 by field_simp, one_smul]

theorem mulVec_single_ne_zero (g : GL (Fin 3) K) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 ≠ 0 := by
  intro h
  have := congrArg (fun w => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) h
  simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
    mulVec_zero] at this
  have h0 := congrFun this 0
  simp at h0

theorem false_of_conj_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {B : Subgroup (MulAut (slPi π 3 (p ^ f) K))} (hB : ∀ β ∈ B, β ^ 3 = 1)
    (hF1 : ∀ x : slPi π 3 (p ^ f) K, orderOf x = 3 → (∀ β ∈ B, β x = x) →
      x ∈ Subgroup.center (slPi π 3 (p ^ f) K))
    (hNP : ∀ y : slPi π 3 (p ^ f) K, MulAut.conj y ∈ B → ∀ β ∈ B, β y = y)
    {y : slPi π 3 (p ^ f) K} (hyB : MulAut.conj y ∈ B) (hy1 : MulAut.conj y ≠ 1) : False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hfix := hNP y hyB
  set Y : GL (Fin 3) K := (y : GL (Fin 3) K) with hYdef
  have hYH : Y ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ y.2
  have hYZ : Y ∉ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    rintro ⟨-, c, hc⟩
    apply hy1
    refine MulEquiv.ext fun s => Subtype.ext ?_
    change Y * s * Y⁻¹ = s
    rw [← hc, ← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (s : GL (Fin 3) K)).eq,
      mul_inv_cancel_right]
  have hY3 : Y ^ 3 ∈ zPi π 3 (p ^ f) K := by
    have hc3 : MulAut.conj (y ^ 3) = 1 := by rw [map_pow]; exact hB _ hyB
    have hcen : y ^ 3 ∈ Subgroup.center (slPi π 3 (p ^ f) K) := by
      rw [Subgroup.mem_center_iff]
      intro s
      have h1 := congrArg (fun α : MulAut (slPi π 3 (p ^ f) K) => α s) hc3
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc s * y ^ 3 = y ^ 3 * s * (y ^ 3)⁻¹ * y ^ 3 := by rw [h1]
        _ = y ^ 3 * s := by group
    obtain ⟨ζ, -, hζ⟩ := KFacts.exists_scalar_of_mem_center hK hq hcen
    rw [zPi_eq hπ hq' hτ hτ1]
    refine ⟨pow_mem hYH 3, ζ, ?_⟩
    rw [← hζ]
    rfl
  have hinner : ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K,
      Y * m * Y⁻¹ = l * m * l⁻¹ := ⟨Y, y.2, fun _ _ => rfl⟩
  rcases (rank3II_4_10_two hK hq hτ hτ1 hYH hYZ hY3).mp hinner with
      ⟨y₀, ⟨z, hz, rfl⟩, g, hg, hgy⟩ | ⟨⟨y₀, ⟨z, hz, rfl⟩, g, hg, e, he, hgy⟩, -⟩
  ·
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
    have hy₀ : Y * z = g * diagTau hτ * g⁻¹ := by rw [← hgy]; group
    have hy₀L : Y * z ∈ slPi π 3 (p ^ f) K := by
      rw [hy₀]
      exact conj_mem_slPi hπ hg (diagTau_mem_slPi hπ hq' hτ)
    set y₀' : slPi π 3 (p ^ f) K := ⟨Y * z, hy₀L⟩ with hy₀'
    have hconj : MulAut.conj y₀' = MulAut.conj y :=
      conj_mul_scalar_eq (c := ξ) (by rw [hξ])
    have hfix₀ := hNP y₀' (hconj ▸ hyB)
    have hord : orderOf y₀' = 3 := by
      refine orderOf_eq_prime (Subtype.ext ?_) ?_
      · change (Y * z) ^ 3 = 1
        rw [hy₀, conj_pow, diagTau_pow_three hτ, mul_one, mul_inv_cancel]
      · intro h1
        apply diagTau_ne_one hτ hτ1
        have h2 : Y * z = 1 := congrArg Subtype.val h1
        rw [hy₀] at h2
        calc diagTau hτ = g⁻¹ * (g * diagTau hτ * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
    obtain ⟨ζ, -, hζ⟩ := KFacts.exists_scalar_of_mem_center hK hq (hF1 y₀' hord hfix₀)
    apply diagTau_ne_scalar hτ hτ1 ζ
    rw [← hgy]
    change g⁻¹ * (y₀' : GL (Fin 3) K) * g = _
    rw [hζ, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g⁻¹).eq, inv_mul_cancel_right]
  ·
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
    have he1 : (e : K) ≠ 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ1
      · intro h2
        apply hτ1
        calc τ = τ ^ 3 / τ ^ 2 := by
              have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
              field_simp
          _ = 1 := by rw [hτ, h2, div_one]
    set C : Subgroup (slPi π 3 (p ^ f) K) := Subgroup.centralizer {y} with hCdef
    set K₀ : Subgroup (slPi π 3 (p ^ f) K) := ⁅C, C⁆ with hK₀def
    have hinv : ∀ β ∈ B, ∀ k ∈ K₀, β k ∈ K₀ := fun β hβ k hk =>
      map_mem_commutator_centralizer (hfix β hβ) hk
    have hY₀ : Y * z = g * diagE e * g⁻¹ := by rw [← hgy]; group
    have hzc : ∀ m : GL (Fin 3) K, z * m = m * z := fun m => by
      rw [← hξ]
      exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ξ m).eq.symm
    have hcommY : ∀ m : GL (Fin 3) K, m * (g * diagE e * g⁻¹) = (g * diagE e * g⁻¹) * m →
        m * Y = Y * m := by
      intro m hm
      rw [← hY₀] at hm
      calc m * Y = m * (Y * z) * z⁻¹ := by group
        _ = (Y * z) * m * z⁻¹ := by rw [hm]
        _ = Y * (z * m) * z⁻¹ := by group
        _ = Y * (m * z) * z⁻¹ := by rw [hzc]
        _ = Y * m := by group
    have hYcomm : ∀ m : GL (Fin 3) K, m * Y = Y * m →
        m * (g * diagE e * g⁻¹) = (g * diagE e * g⁻¹) * m := by
      intro m hm
      rw [← hY₀]
      calc m * (Y * z) = (m * Y) * z := by group
        _ = (Y * m) * z := by rw [hm]
        _ = Y * (m * z) := by group
        _ = Y * (z * m) := by rw [hzc]
        _ = Y * z * m := by group
    have hconjD : ∀ d : GL (Fin 3) K, d * diagE e = diagE e * d →
        (g * d * g⁻¹) * (g * diagE e * g⁻¹) = (g * diagE e * g⁻¹) * (g * d * g⁻¹) := by
      intro d hd
      calc (g * d * g⁻¹) * (g * diagE e * g⁻¹) = g * (d * diagE e) * g⁻¹ := by group
        _ = g * (diagE e * d) * g⁻¹ := by rw [hd]
        _ = (g * diagE e * g⁻¹) * (g * d * g⁻¹) := by group
    have hPL := conj_mem_slPi hπ hg (swapTwelve_mem_slPi (K := K) hπ)
    have hDL := conj_mem_slPi hπ hg (diagTau_mem_slPi hπ hq' hτ)
    set P' : slPi π 3 (p ^ f) K := ⟨g * swapTwelve K * g⁻¹, hPL⟩ with hP'
    set D' : slPi π 3 (p ^ f) K := ⟨g * diagTau hτ * g⁻¹, hDL⟩ with hD'
    have hmemC : ∀ c : slPi π 3 (p ^ f) K, (c : GL (Fin 3) K) * Y = Y * c → c ∈ C := by
      intro c hc
      rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hc
    have hP'C : P' ∈ C := hmemC P' (hcommY _ (hconjD _ (swapTwelve_comm_diagE e)))
    have hD'C : D' ∈ C := hmemC D' (hcommY _ (hconjD _ (diagTau_comm_diagE hτ e)))
    have hx₀ : ⁅P', D'⁆ ∈ K₀ := Subgroup.commutator_mem_commutator hP'C hD'C
    have hx₀val : ((⁅P', D'⁆ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        g * diagOneTau hτ * g⁻¹ := by
      rw [← commutator_swapTwelve_diagTau hτ, commutatorElement_def]
      change g * swapTwelve K * g⁻¹ * (g * diagTau hτ * g⁻¹) * (g * swapTwelve K * g⁻¹)⁻¹ *
        (g * diagTau hτ * g⁻¹)⁻¹ = _
      group
    have h3 : 3 ∣ Nat.card K₀ := by
      refine three_dvd_card_of_mem hx₀ (Subtype.ext ?_) ?_
      · change ((⁅P', D'⁆ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 = 1
        rw [hx₀val, conj_pow, diagOneTau_pow_three hτ, mul_one, mul_inv_cancel]
      · intro h1
        apply diagOneTau_ne_one hτ hτ1
        have h2 := congrArg Subtype.val h1
        change ((⁅P', D'⁆ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = 1 at h2
        rw [hx₀val] at h2
        calc diagOneTau hτ = g⁻¹ * (g * diagOneTau hτ * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
    set v : Fin 3 → K := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := mulVec_single_ne_zero g
    have heig : ∀ c ∈ C, ∃ a : K,
        ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = a • v := by
      intro c hc
      rw [hCdef, Subgroup.mem_centralizer_singleton_iff] at hc
      exact exists_smul_of_commute_conj_diagE he1 (hYcomm _ (congrArg Subtype.val hc))
    let Stab : Subgroup (slPi π 3 (p ^ f) K) :=
      { carrier := {s | ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
        mul_mem' := by
          intro a b ha hb
          change (((a * b : slPi π 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            v = v
          rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
          change ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v at hb
          change ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v at ha
          rw [hb, ha]
        one_mem' := by
          change (((1 : slPi π 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            v = v
          simp
        inv_mem' := by
          intro a ha
          change ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v at ha
          change (((a⁻¹ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            v = v
          have := congrArg (fun w => (((a⁻¹ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ w) ha
          simp only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
            Subgroup.coe_one, Units.val_one, one_mulVec] at this
          exact this.symm }
    have hK₀S : K₀ ≤ Stab := by
      rw [hK₀def, Subgroup.commutator_le]
      intro c₁ h₁ c₂ h₂
      obtain ⟨a₁, ha₁⟩ := heig c₁ h₁
      obtain ⟨a₂, ha₂⟩ := heig c₂ h₂
      change (((⁅c₁, c₂⁆ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        v = v
      rw [commutatorElement_def]
      exact commutator_mulVec_eq ha₁ ha₂ hv0
    obtain ⟨x, hxK, hx3, hxfix⟩ := exists_orderOf_eq_three_fixed_of_invariant hB hinv h3
    obtain ⟨ζ, -, hζ⟩ := KFacts.exists_scalar_of_mem_center hK hq (hF1 x hx3 hxfix)
    have hxv : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := hK₀S hxK
    rw [hζ, GeneralLinearGroup.coe_scalar, scalar_apply] at hxv
    have hζ1 : (ζ : K) = 1 := by
      by_contra hne
      apply hv0
      funext i
      have := congrFun hxv i
      rw [mulVec_diagonal] at this
      simp only [Pi.zero_apply]
      have h' : ((ζ : K) - 1) * v i = 0 := by rw [sub_mul, one_mul, this, sub_self]
      exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
    have hx1 : x = 1 := by
      apply Subtype.ext
      rw [hζ, show ζ = 1 from Units.ext hζ1, map_one]
      rfl
    rw [hx1, orderOf_one] at hx3
    norm_num at hx3

end Inner

end Res5Proof

end CFSG.RankThree.PartTwo.Sec13
