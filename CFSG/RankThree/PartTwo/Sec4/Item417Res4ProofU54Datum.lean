module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL52
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherUTools
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

namespace U54

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item434SmallTwoOther CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.Assembly.RankThreeEven (projSU)
open scoped Matrix

local notation "𝕂" => GaloisField 2 (2 * 2)
local notation "σ₁₆" => unitaryInvolution (GaloisField 2 (2 * 2)) 2 2

theorem hσ : ∀ c : 𝕂, σ₁₆ (σ₁₆ c) = c := UTools.isUnitaryInvolution_gf16.invol

@[expose] noncomputable def Q : UTools.HypQuad σ₁₆ 5 := UTools.stdQuad UTools.W₁₆ (by norm_num)

@[expose] noncomputable def d : UTools.Z₃ × UTools.Z₃ →* SUid σ₁₆ 5 :=
  UTools.torusHom hσ Q UTools.Z₃ UTools.fix_Z₃

@[expose] noncomputable def δ : UTools.Z₃ × UTools.Z₃ →* projSU 5 2 2 := (UTools.piSU 5).comp d

theorem d_smul (p : UTools.Z₃ × UTools.Z₃) (x : Fin 5 → 𝕂) :
    d p • x = x + ((((p.1 : 𝕂ˣ) : 𝕂) - 1) * herm σ₁₆ Q.P₁.f x) • Q.P₁.e +
      ((((p.1 : 𝕂ˣ) : 𝕂)⁻¹ - 1) * herm σ₁₆ Q.P₁.e x) • Q.P₁.f +
      ((((p.2 : 𝕂ˣ) : 𝕂) - 1) * herm σ₁₆ Q.P₂.f x) • Q.P₂.e +
      ((((p.2 : 𝕂ˣ) : 𝕂)⁻¹ - 1) * herm σ₁₆ Q.P₂.e x) • Q.P₂.f := by
  rw [d, UTools.torusHom_apply, mul_smul, UTools.planeHom_apply, UTools.planeHom_apply,
    UTools.planeElt_smul, UTools.planeElt_smul]
  simp only [herm_add_right, herm_smul_right, Q.hf₁e₂, Q.hf₁f₂, Q.he₁e₂, Q.he₁f₂, mul_zero,
    add_zero]
  abel

@[expose] noncomputable def tr (g : SUid σ₁₆ 5) : 𝕂 :=
  Matrix.trace ((g : GL (Fin 5) 𝕂) : Matrix (Fin 5) (Fin 5) 𝕂)

theorem tr_eq_sum (g : SUid σ₁₆ 5) :
    tr g = ∑ i : Fin 5, (g • (Pi.single i (1 : 𝕂) : Fin 5 → 𝕂)) i := by
  rw [tr, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_def, Matrix.mulVec_single_one]
  rfl

theorem sum_herm_single (c : 𝕂) (u w : Fin 5 → 𝕂) :
    ∑ i : Fin 5, ((c * herm σ₁₆ u (Pi.single i 1)) • w) i = c * herm σ₁₆ u w := by
  simp only [Pi.smul_apply, smul_eq_mul, herm_single_right, mul_one]
  rw [herm_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tr_d (p : UTools.Z₃ × UTools.Z₃) :
    tr (d p) = 5 + (((p.1 : 𝕂ˣ) : 𝕂) - 1) + ((((p.1 : 𝕂ˣ) : 𝕂))⁻¹ - 1) +
      (((p.2 : 𝕂ˣ) : 𝕂) - 1) + ((((p.2 : 𝕂ˣ) : 𝕂))⁻¹ - 1) := by
  rw [tr_eq_sum]
  simp only [d_smul, Pi.add_apply]
  simp only [Finset.sum_add_distrib, sum_herm_single]
  rw [UTools.HypPair.hfe _ hσ, Q.P₁.hef, UTools.HypPair.hfe _ hσ, Q.P₂.hef]
  simp only [Pi.single_eq_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem tr_conj (g h : SUid σ₁₆ 5) : tr (g * h * g⁻¹) = tr h := by
  rw [tr, tr, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem tr_of_smul_eq {g h : SUid σ₁₆ 5} {c : 𝕂} (H : ∀ v : Fin 5 → 𝕂, g • v = c • (h • v)) :
    tr g = c * tr h := by
  rw [tr_eq_sum, tr_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [H]
  rfl

@[expose] noncomputable def w : UTools.Z₃ := ⟨UTools.ω₁₆, Subgroup.mem_zpowers _⟩

theorem w_pow_three : w ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact UTools.orderOf_ω₁₆ ▸ pow_orderOf_eq_one UTools.ω₁₆

theorem w_ne_one : w ≠ 1 := fun h => UTools.ω₁₆_ne_one (congrArg Subtype.val h)

theorem w_inv_ne_one : w⁻¹ ≠ 1 := fun h => w_ne_one (inv_eq_one.mp h)

theorem w_ne_inv : w ≠ w⁻¹ := by
  intro h
  apply w_ne_one
  have h2 : w * w = 1 := by
    calc w * w = w * w⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel w
  have h3 := w_pow_three
  calc w = w ^ 3 * (w * w)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem Z₃_cases (a : UTools.Z₃) : a = 1 ∨ a = w ∨ a = w⁻¹ := by
  classical
  have ha : (a : 𝕂ˣ) ∈ Subgroup.zpowers UTools.ω₁₆ := a.2
  rw [mem_zpowers_iff_mem_range_orderOf, UTools.orderOf_ω₁₆] at ha
  obtain ⟨k, hk, hka⟩ := Finset.mem_image.mp ha
  have hk3 : k < 3 := Finset.mem_range.mp hk
  interval_cases k
  · left
    exact Subtype.ext (by rw [← hka, pow_zero]; rfl)
  · right; left
    exact Subtype.ext (by rw [← hka, pow_one]; rfl)
  · right; right
    apply Subtype.ext
    rw [← hka]
    have h3 : w ^ 3 = 1 := w_pow_three
    have : w ^ 2 = w⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3]
    exact congrArg Subtype.val this

theorem sum_sub_one_of_ne {a : UTools.Z₃} (ha : a ≠ 1) :
    ((a : 𝕂ˣ) : 𝕂) - 1 + (((a : 𝕂ˣ) : 𝕂)⁻¹ - 1) = 1 := by
  set x : 𝕂 := ((a : 𝕂ˣ) : 𝕂) with hx
  have h3 : x ^ 3 = 1 := by
    rcases Z₃_cases a with rfl | rfl | rfl
    · exact absurd rfl ha
    · have := congrArg (fun z : UTools.Z₃ => ((z : 𝕂ˣ) : 𝕂)) w_pow_three
      simpa using this
    · have := congrArg (fun z : UTools.Z₃ => ((z : 𝕂ˣ) : 𝕂)) w_pow_three
      have h : x = (((w : 𝕂ˣ) : 𝕂))⁻¹ := by simp [hx]
      rw [h, inv_pow]
      simpa using this
  have hx1 : x ≠ 1 := by
    intro h
    apply ha
    exact Subtype.ext (Units.ext h)
  have hq : x ^ 2 + x + 1 = 0 := by
    have h : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hx1)
  have hinv : x⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right (by linear_combination h3)
  rw [hinv]
  linear_combination hq - 2 * UTools.two_eq_zero_gf16

theorem sum_sub_one_of_eq {a : UTools.Z₃} (ha : a = 1) :
    ((a : 𝕂ˣ) : 𝕂) - 1 + (((a : 𝕂ˣ) : 𝕂)⁻¹ - 1) = 0 := by
  subst ha
  simp

theorem tr_d_eq_zero_iff (p : UTools.Z₃ × UTools.Z₃) :
    tr (d p) = 0 ↔ (p.1 ≠ 1 ∧ p.2 = 1) ∨ (p.1 = 1 ∧ p.2 ≠ 1) := by
  have h5 : (5 : 𝕂) = 1 := by linear_combination 2 * UTools.two_eq_zero_gf16
  have htr : tr (d p) = 1 + (((p.1 : 𝕂ˣ) : 𝕂) - 1 + ((((p.1 : 𝕂ˣ) : 𝕂))⁻¹ - 1)) +
      (((p.2 : 𝕂ˣ) : 𝕂) - 1 + ((((p.2 : 𝕂ˣ) : 𝕂))⁻¹ - 1)) := by
    rw [tr_d]
    linear_combination h5
  have h11 : (1 : 𝕂) + 1 = 0 := by linear_combination UTools.two_eq_zero_gf16
  rw [htr]
  by_cases h1 : p.1 = 1 <;> by_cases h2 : p.2 = 1
  · rw [sum_sub_one_of_eq h1, sum_sub_one_of_eq h2]
    simp [h1, h2]
  · rw [sum_sub_one_of_eq h1, sum_sub_one_of_ne h2]
    simp [h1, h2, h11]
  · rw [sum_sub_one_of_ne h1, sum_sub_one_of_eq h2]
    simp [h1, h2, h11]
  · rw [sum_sub_one_of_ne h1, sum_sub_one_of_ne h2, h11, zero_add]
    simp [h1, h2]

theorem δ_injective : Function.Injective δ :=
  UTools.injective_comp_torusHom UTools.isUnitaryInvolution_gf16 UTools.two_eq_zero_gf16 Q
    UTools.fix_Z₃ (UTools.piSU 5) UTools.piSU_eq_one

local notation "P5" => (UTools.P₀U 5 (by norm_num) : Subgroup (projSU 5 2 2))

theorem δ_mem (p : UTools.Z₃ × UTools.Z₃) : δ p ∈ P5 := ⟨p, rfl⟩

@[expose] noncomputable def α : UTools.P₀U 5 (by norm_num) := ⟨δ (w, 1), δ_mem _⟩

@[expose] noncomputable def β : UTools.P₀U 5 (by norm_num) := ⟨δ (1, w), δ_mem _⟩

@[expose] noncomputable def t : Fin 4 → UTools.P₀U 5 (by norm_num) := ![α, α⁻¹, β, β⁻¹]

theorem coe_α_zpow_mul (i j : ℤ) :
    ((α ^ i * β ^ j : UTools.P₀U 5 (by norm_num)) : projSU 5 2 2) = δ (w ^ i, w ^ j) := by
  rw [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow, α, β, ← map_zpow, ← map_zpow,
    ← map_mul]
  congr 1
  ext <;> simp

theorem exists_zpow_mul (y : UTools.P₀U 5 (by norm_num)) : ∃ i j : ℤ, y = α ^ i * β ^ j := by
  obtain ⟨⟨a, b⟩, hy⟩ := y.2
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
  refine ⟨i, j, Subtype.ext ?_⟩
  rw [coe_α_zpow_mul, ← hy]
  congr 1
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [Subgroup.coe_zpow]
    exact hi.symm
  · rw [Subgroup.coe_zpow]
    exact hj.symm

theorem mulAut_ext {φ ψ : MulAut (UTools.P₀U 5 (by norm_num))} (hα : φ α = ψ α)
    (hβ : φ β = ψ β) : φ = ψ := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul y
  rw [map_mul, map_zpow, map_zpow, map_mul, map_zpow, map_zpow, hα, hβ]

theorem exists_t_of_tr {p : UTools.Z₃ × UTools.Z₃} (hp : tr (d p) = 0) :
    ∃ i : Fin 4, δ p = (t i : projSU 5 2 2) := by
  obtain ⟨a, b⟩ := p
  rw [tr_d_eq_zero_iff] at hp
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · dsimp only at ha hb
    subst hb
    rcases Z₃_cases a with rfl | rfl | rfl
    · exact absurd rfl ha
    · exact ⟨0, rfl⟩
    · refine ⟨1, ?_⟩
      change δ (w⁻¹, 1) = ((α⁻¹ : UTools.P₀U 5 (by norm_num)) : projSU 5 2 2)
      rw [Subgroup.coe_inv, α, ← map_inv]
      simp
  · dsimp only at ha hb
    subst ha
    rcases Z₃_cases b with rfl | rfl | rfl
    · exact absurd rfl hb
    · exact ⟨2, rfl⟩
    · refine ⟨3, ?_⟩
      change δ (1, w⁻¹) = ((β⁻¹ : UTools.P₀U 5 (by norm_num)) : projSU 5 2 2)
      rw [Subgroup.coe_inv, β, ← map_inv]
      simp

theorem tr_d_w_one : tr (d (w, 1)) = 0 :=
  (tr_d_eq_zero_iff _).mpr (Or.inl ⟨w_ne_one, rfl⟩)

theorem tr_d_one_w : tr (d (1, w)) = 0 :=
  (tr_d_eq_zero_iff _).mpr (Or.inr ⟨rfl, w_ne_one⟩)

theorem add_self_vec (v : Fin 5 → 𝕂) : v + v = 0 := by
  funext k
  simp only [Pi.add_apply, Pi.zero_apply]
  linear_combination v k * UTools.two_eq_zero_gf16

theorem herm_e₁f₁ : herm σ₁₆ (Q.P₁.e + Q.P₁.f) (Q.P₁.e + Q.P₁.f) = 0 := by
  rw [herm_add_left, herm_add_right, herm_add_right, Q.P₁.hee, Q.P₁.hff, Q.P₁.hef,
    UTools.HypPair.hfe _ hσ]
  linear_combination UTools.two_eq_zero_gf16

theorem one_add_σ_one : (1 : 𝕂) + σ₁₆ 1 = 0 := by
  rw [map_one]
  linear_combination UTools.two_eq_zero_gf16

@[expose] noncomputable def s : SUid σ₁₆ 5 := tv hσ herm_e₁f₁ one_add_σ_one

theorem s_smul (v : Fin 5 → 𝕂) :
    s • v = v + (1 * herm σ₁₆ (Q.P₁.e + Q.P₁.f) v) • (Q.P₁.e + Q.P₁.f) :=
  tv_smul hσ herm_e₁f₁ one_add_σ_one v

theorem s_e₁ : s • Q.P₁.e = Q.P₁.f := by
  rw [s_smul, herm_add_left, Q.P₁.hee, UTools.HypPair.hfe _ hσ, zero_add, one_mul, one_smul,
    ← add_assoc, add_self_vec, zero_add]

theorem s_f₁ : s • Q.P₁.f = Q.P₁.e := by
  rw [s_smul, herm_add_left, Q.P₁.hef, Q.P₁.hff, add_zero, one_mul, one_smul, add_comm Q.P₁.e,
    ← add_assoc, add_self_vec, zero_add]

theorem s_e₂ : s • Q.P₂.e = Q.P₂.e := by
  rw [s_smul, herm_add_left, Q.he₁e₂, Q.hf₁e₂, add_zero, mul_zero, zero_smul, add_zero]

theorem s_f₂ : s • Q.P₂.f = Q.P₂.f := by
  rw [s_smul, herm_add_left, Q.he₁f₂, Q.hf₁f₂, add_zero, mul_zero, zero_smul, add_zero]

@[expose] def π₀ : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem det_π₀ : (π₀.permMatrix 𝕂).det = 1 := by
  rw [Matrix.det_permutation, π₀, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  simp

theorem isometry_π₀ (x y : Fin 5 → 𝕂) :
    herm σ₁₆ (π₀.permMatrix 𝕂 *ᵥ x) (π₀.permMatrix 𝕂 *ᵥ y) = herm σ₁₆ x y := by
  rw [Matrix.permMatrix_mulVec, Matrix.permMatrix_mulVec, herm_def, herm_def]
  exact Equiv.sum_comp π₀ (fun i => σ₁₆ (x i) * y i)

@[expose] noncomputable def u : SUid σ₁₆ 5 := mkSU σ₁₆ (π₀.permMatrix 𝕂) det_π₀ isometry_π₀

theorem u_smul (v : Fin 5 → 𝕂) : u • v = v ∘ π₀ := Matrix.permMatrix_mulVec π₀

theorem single_comp_π₀ (c c' : 𝕂) :
    (Pi.single 0 c + Pi.single 1 c' : Fin 5 → 𝕂) ∘ π₀ = Pi.single 2 c + Pi.single 3 c' := by
  funext k
  fin_cases k <;> simp [π₀, Equiv.swap_apply_def]

theorem single_comp_π₀' (c c' : 𝕂) :
    (Pi.single 2 c + Pi.single 3 c' : Fin 5 → 𝕂) ∘ π₀ = Pi.single 0 c + Pi.single 1 c' := by
  funext k
  fin_cases k <;> simp [π₀, Equiv.swap_apply_def]

theorem e₁_eq : Q.P₁.e = Pi.single 0 1 + Pi.single 1 UTools.W₁₆.u := rfl

theorem f₁_eq : Q.P₁.f = (1 - UTools.W₁₆.ω)⁻¹ •
    (Pi.single 0 1 + Pi.single 1 (UTools.W₁₆.u * UTools.W₁₆.ω)) := rfl

theorem e₂_eq : Q.P₂.e = Pi.single 2 1 + Pi.single 3 UTools.W₁₆.u := rfl

theorem f₂_eq : Q.P₂.f = (1 - UTools.W₁₆.ω)⁻¹ •
    (Pi.single 2 1 + Pi.single 3 (UTools.W₁₆.u * UTools.W₁₆.ω)) := rfl

theorem u_e₁ : u • Q.P₁.e = Q.P₂.e := by
  rw [u_smul, e₁_eq, single_comp_π₀, e₂_eq]

theorem u_f₁ : u • Q.P₁.f = Q.P₂.f := by
  rw [u_smul, f₁_eq, f₂_eq, ← single_comp_π₀]
  rfl

theorem u_e₂ : u • Q.P₂.e = Q.P₁.e := by
  rw [u_smul, e₂_eq, single_comp_π₀', e₁_eq]

theorem u_f₂ : u • Q.P₂.f = Q.P₁.f := by
  rw [u_smul, f₁_eq, f₂_eq, ← single_comp_π₀']
  rfl

theorem conj_d_smul (g : SUid σ₁₆ 5) (p : UTools.Z₃ × UTools.Z₃) (v : Fin 5 → 𝕂) :
    (g * d p * g⁻¹) • v = v + ((((p.1 : 𝕂ˣ) : 𝕂) - 1) * herm σ₁₆ (g • Q.P₁.f) v) • (g • Q.P₁.e) +
      ((((p.1 : 𝕂ˣ) : 𝕂)⁻¹ - 1) * herm σ₁₆ (g • Q.P₁.e) v) • (g • Q.P₁.f) +
      ((((p.2 : 𝕂ˣ) : 𝕂) - 1) * herm σ₁₆ (g • Q.P₂.f) v) • (g • Q.P₂.e) +
      ((((p.2 : 𝕂ˣ) : 𝕂)⁻¹ - 1) * herm σ₁₆ (g • Q.P₂.e) v) • (g • Q.P₂.f) := by
  have key : ∀ x : Fin 5 → 𝕂, herm σ₁₆ x (g⁻¹ • v) = herm σ₁₆ (g • x) v := fun x => by
    rw [← herm_smul_smul σ₁₆ g x (g⁻¹ • v), smul_inv_smul]
  rw [mul_smul, mul_smul, d_smul]
  simp only [smul_add, key, smul_inv_smul]
  simp only [smul_comm g (_ : 𝕂) (_ : Fin 5 → 𝕂)]

theorem s_conj (p : UTools.Z₃ × UTools.Z₃) : s * d p * s⁻¹ = d (p.1⁻¹, p.2) := by
  apply ext_smul
  intro v
  rw [conj_d_smul, d_smul, s_e₁, s_f₁, s_e₂, s_f₂]
  simp only [InvMemClass.coe_inv, Units.val_inv_eq_inv_val, inv_inv]
  abel

theorem u_conj (p : UTools.Z₃ × UTools.Z₃) : u * d p * u⁻¹ = d (p.2, p.1) := by
  apply ext_smul
  intro v
  rw [conj_d_smul, d_smul, u_e₁, u_f₁, u_e₂, u_f₂]
  abel

theorem piS_conj (p : UTools.Z₃ × UTools.Z₃) :
    UTools.piSU 5 s * δ p * (UTools.piSU 5 s)⁻¹ = δ (p.1⁻¹, p.2) := by
  rw [δ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, s_conj]

theorem piR_conj (p : UTools.Z₃ × UTools.Z₃) :
    UTools.piSU 5 (s * u) * δ p * (UTools.piSU 5 (s * u))⁻¹ = δ (p.2⁻¹, p.1) := by
  have h : s * u * d p * (s * u)⁻¹ = s * (u * d p * u⁻¹) * s⁻¹ := by group
  rw [δ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, h, u_conj,
    s_conj]

theorem mem_normalizer_of {x : projSU 5 2 2} (h : ∀ p, ∃ q, x * δ p * x⁻¹ = δ q) :
    x ∈ Subgroup.normalizer (P5 : Set (projSU 5 2 2)) := by
  have := UTools.finite_projSU_gf16 5
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨p, rfl⟩ := hn
  obtain ⟨q, hq⟩ := h p
  change x * δ p * x⁻¹ ∈ (P5 : Set (projSU 5 2 2))
  rw [hq]
  exact δ_mem q

@[expose] noncomputable def nS : Subgroup.normalizer (P5 : Set (projSU 5 2 2)) :=
  ⟨UTools.piSU 5 s, mem_normalizer_of fun p => ⟨_, piS_conj p⟩⟩

@[expose] noncomputable def nR : Subgroup.normalizer (P5 : Set (projSU 5 2 2)) :=
  ⟨UTools.piSU 5 (s * u), mem_normalizer_of fun p => ⟨_, piR_conj p⟩⟩

@[expose] noncomputable def σA : MulAut (UTools.P₀U 5 (by norm_num)) :=
  Subgroup.normalizerMonoidHom P5 nS

@[expose] noncomputable def ρA : MulAut (UTools.P₀U 5 (by norm_num)) :=
  Subgroup.normalizerMonoidHom P5 nR

theorem nmh_apply (h : Subgroup.normalizer (P5 : Set (projSU 5 2 2)))
    (x : UTools.P₀U 5 (by norm_num)) :
    ((Subgroup.normalizerMonoidHom P5 h x : UTools.P₀U 5 (by norm_num)) : projSU 5 2 2) =
      (h : projSU 5 2 2) * (x : projSU 5 2 2) * (h : projSU 5 2 2)⁻¹ :=
  rfl

theorem coe_α_inv : ((α⁻¹ : UTools.P₀U 5 (by norm_num)) : projSU 5 2 2) = δ (w⁻¹, 1) := by
  rw [Subgroup.coe_inv, α, ← map_inv, Prod.inv_mk, inv_one]

theorem coe_β_inv : ((β⁻¹ : UTools.P₀U 5 (by norm_num)) : projSU 5 2 2) = δ (1, w⁻¹) := by
  rw [Subgroup.coe_inv, β, ← map_inv, Prod.inv_mk, inv_one]

theorem σA_α : σA α = α⁻¹ :=
  Subtype.ext (by rw [σA, nmh_apply, coe_α_inv]; exact piS_conj (w, 1))

theorem σA_β : σA β = β :=
  Subtype.ext (by rw [σA, nmh_apply]; exact (piS_conj (1, w)).trans (by rw [inv_one]; rfl))

theorem ρA_α : ρA α = β :=
  Subtype.ext (by rw [ρA, nmh_apply]; exact (piR_conj (w, 1)).trans (by rw [inv_one]; rfl))

theorem ρA_β : ρA β = α⁻¹ :=
  Subtype.ext (by rw [ρA, nmh_apply, coe_α_inv]; exact piR_conj (1, w))

theorem ne_of_δ {x y : UTools.P₀U 5 (by norm_num)} {p q : UTools.Z₃ × UTools.Z₃}
    (hx : (x : projSU 5 2 2) = δ p) (hy : (y : projSU 5 2 2) = δ q) (hpq : p ≠ q) : x ≠ y := by
  intro h
  apply hpq
  apply δ_injective
  rw [← hx, ← hy, h]

theorem α_ne_inv : α ≠ α⁻¹ :=
  ne_of_δ rfl coe_α_inv fun h => w_ne_inv (congrArg Prod.fst h)

theorem β_ne_inv : β ≠ β⁻¹ :=
  ne_of_δ rfl coe_β_inv fun h => w_ne_inv (congrArg Prod.snd h)

theorem β_ne_α_inv : β ≠ α⁻¹ :=
  ne_of_δ rfl coe_α_inv fun h => w_inv_ne_one (congrArg Prod.fst h).symm

theorem β_ne_α : β ≠ α :=
  ne_of_δ rfl rfl fun h => w_ne_one (congrArg Prod.fst h).symm

theorem β_inv_ne_α_inv : β⁻¹ ≠ α⁻¹ :=
  ne_of_δ coe_β_inv coe_α_inv fun h => w_inv_ne_one (congrArg Prod.fst h).symm

theorem tr_eq_zero_of_conj {x : projSU 5 2 2}
    (hx : x ∈ Subgroup.normalizer (P5 : Set (projSU 5 2 2))) {p : UTools.Z₃ × UTools.Z₃}
    (hp : tr (d p) = 0) : ∃ p', x * δ p * x⁻¹ = δ p' ∧ tr (d p') = 0 := by
  obtain ⟨g, rfl⟩ := UTools.piSU_surjective 5 x
  obtain ⟨p', hp'⟩ := (Subgroup.mem_normalizer_iff.mp hx (δ p)).mp (δ_mem p)
  change δ p' = _ at hp'
  refine ⟨p', hp'.symm, ?_⟩
  have h1 : UTools.piSU 5 ((d p')⁻¹ * (g * d p * g⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv]
    change (δ p')⁻¹ * (UTools.piSU 5 g * δ p * (UTools.piSU 5 g)⁻¹) = 1
    rw [hp', inv_mul_cancel]
  obtain ⟨c, hc⟩ := UTools.piSU_eq_one _ h1
  have H : ∀ v : Fin 5 → 𝕂, (g * d p * g⁻¹) • v = c • (d p' • v) := fun v => by
    have hv := hc v
    rw [mul_smul] at hv
    calc (g * d p * g⁻¹) • v = d p' • ((d p')⁻¹ • ((g * d p * g⁻¹) • v)) := by
          rw [smul_inv_smul]
      _ = d p' • (c • v) := by rw [hv]
      _ = c • (d p' • v) := smul_comm _ _ _
  have h2 := tr_of_smul_eq H
  rw [tr_conj, hp] at h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hv := H (Pi.single 0 1)
    rw [zero_smul] at hv
    have h0 : (g * d p * g⁻¹) • (Pi.single 0 1 : Fin 5 → 𝕂) = (g * d p * g⁻¹) • 0 := by
      rw [hv, smul_zero]
    have h01 := MulAction.injective (g * d p * g⁻¹) h0
    have := congrFun h01 0
    simp at this
  exact (mul_eq_zero.mp h2.symm).resolve_left hc0

theorem t_sqIdx (i : Fin 4) : t (sqIdx i) = (t i)⁻¹ := by
  fin_cases i <;> simp [t, sqIdx]

theorem words_spec (k : Fin 4) (l : Fin 2) :
    (ρA ^ (k : ℕ) * σA ^ (l : ℕ)) α = t (img1 k l) ∧
      (ρA ^ (k : ℕ) * σA ^ (l : ℕ)) β = t (img2 k l) := by
  fin_cases k <;> fin_cases l <;>
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, ρA_α, ρA_β, σA_α,
      σA_β, map_inv, inv_inv] <;>
    simp [img1, img2, t]

theorem mem_autIn {φ : MulAut (UTools.P₀U 5 (by norm_num))} (hφ : φ ∈ autIn ⊤ P5) :
    ∃ k : Fin 4, ∃ l : Fin 2, φ = ρA ^ (k : ℕ) * σA ^ (l : ℕ) := by
  obtain ⟨g, hN, -, rfl⟩ := mem_autIn_iff.mp hφ
  have himg : ∀ p, tr (d p) = 0 → ∃ i : Fin 4, g * δ p * g⁻¹ = (t i : projSU 5 2 2) := by
    intro p hp
    obtain ⟨p', hp', htr⟩ := tr_eq_zero_of_conj hN hp
    obtain ⟨i, hi⟩ := exists_t_of_tr htr
    exact ⟨i, hp'.trans hi⟩
  obtain ⟨i, hi⟩ := himg _ tr_d_w_one
  obtain ⟨j, hj⟩ := himg _ tr_d_one_w
  have hji : j ≠ i := by
    rintro rfl
    apply β_ne_α
    apply Subtype.ext
    have h1 : g * δ (1, w) * g⁻¹ = g * δ (w, 1) * g⁻¹ := by rw [hi, hj]
    simpa [α, β] using h1
  have hji2 : j ≠ sqIdx i := by
    rintro rfl
    apply β_ne_α_inv
    apply Subtype.ext
    have h1 : g * δ (1, w) * g⁻¹ = (g * δ (w, 1) * g⁻¹)⁻¹ := by
      rw [hj, hi, t_sqIdx, Subgroup.coe_inv]
    rw [coe_α_inv]
    have h2 : (g * δ (w, 1) * g⁻¹)⁻¹ = g * δ (w⁻¹, 1) * g⁻¹ := by
      rw [← coe_α_inv, Subgroup.coe_inv]
      change (g * (α : projSU 5 2 2) * g⁻¹)⁻¹ = g * (α : projSU 5 2 2)⁻¹ * g⁻¹
      group
    rw [h2] at h1
    simpa [β] using h1
  obtain ⟨k, l, hk1, hk2⟩ := img_cover i j hji hji2
  refine ⟨k, l, ?_⟩
  obtain ⟨hw1, hw2⟩ := words_spec k l
  refine mulAut_ext ?_ ?_
  · rw [hw1, hk1]
    exact Subtype.ext hi
  · rw [hw2, hk2]
    exact Subtype.ext hj

theorem σA_mem : σA ∈ autIn ⊤ P5 :=
  mem_autIn_iff.mpr ⟨_, nS.2, Subgroup.mem_top _, rfl⟩

theorem ρA_mem : ρA ∈ autIn ⊤ P5 :=
  mem_autIn_iff.mpr ⟨_, nR.2, Subgroup.mem_top _, rfl⟩

theorem ρA_pow_four_apply (x : UTools.P₀U 5 (by norm_num)) :
    (ρA ^ 4) x = ρA (ρA (ρA (ρA x))) := by
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]

theorem ρA_pow_four : ρA ^ 4 = 1 := by
  refine mulAut_ext ?_ ?_
  · rw [ρA_pow_four_apply, ρA_α, ρA_β, map_inv, ρA_α, map_inv, ρA_β, inv_inv, MulAut.one_apply]
  · rw [ρA_pow_four_apply, ρA_β, map_inv, ρA_α, map_inv, ρA_β, inv_inv, ρA_α, MulAut.one_apply]

theorem ρA_sq_ne_one : ρA ^ 2 ≠ 1 := by
  intro h
  have h1 := congrArg (fun φ : MulAut (UTools.P₀U 5 (by norm_num)) => φ α) h
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, ρA_α, ρA_β] at h1
  exact α_ne_inv h1.symm

theorem orderOf_ρA : orderOf ρA = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : ρA ^ 2 ^ (1 + 1) = 1 := ρA_pow_four
  have h2 : ¬ ρA ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact ρA_sq_ne_one
  exact orderOf_eq_prime_pow h2 h4

theorem σA_sq : σA ^ 2 = 1 :=
  mulAut_ext
    (by simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, σA_α, map_inv,
      inv_inv])
    (by simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, σA_β])

theorem σA_ρA_σA : σA * ρA * σA = ρA ^ 3 :=
  mulAut_ext
    (by simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, ρA_α, ρA_β, σA_α, σA_β, map_inv])
    (by simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, ρA_α, ρA_β, σA_α, σA_β, map_inv,
      inv_inv])

theorem σA_ρA : σA * ρA * σA⁻¹ = ρA⁻¹ := by
  have hσ : σA⁻¹ = σA := inv_eq_of_mul_eq_one_right ((sq σA).symm.trans σA_sq)
  have hρ : ρA⁻¹ = ρA ^ 3 := inv_eq_of_mul_eq_one_right ((pow_succ' ρA 3).symm.trans ρA_pow_four)
  rw [hσ, hρ, σA_ρA_σA]

theorem σA_not_mem : σA ∉ Subgroup.zpowers ρA := by
  classical
  have := UTools.finite_projSU_gf16 5
  have : Finite (MulAut (UTools.P₀U 5 (by norm_num))) := MulEquiv.finite_left
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_ρA] at h
  obtain ⟨k, hk, hks⟩ := Finset.mem_image.mp h
  have hk4 : k < 4 := Finset.mem_range.mp hk
  have h1 := congrArg (fun φ : MulAut (UTools.P₀U 5 (by norm_num)) => φ α) hks
  have h2 := congrArg (fun φ : MulAut (UTools.P₀U 5 (by norm_num)) => φ β) hks
  simp only [σA_α, σA_β] at h1 h2
  interval_cases k <;>
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, ρA_α, ρA_β,
      map_inv, inv_inv] at h1 h2
  · exact α_ne_inv h1
  · exact β_ne_α_inv h1
  · exact β_ne_inv h2.symm
  · exact β_inv_ne_α_inv h1

theorem nonempty_autIn_P₀ : Nonempty (autIn ⊤ P5 ≃* DihedralGroup 4) := by
  have := UTools.finite_projSU_gf16 5
  have : Finite (MulAut (UTools.P₀U 5 (by norm_num))) := MulEquiv.finite_left
  set ρ' : autIn ⊤ P5 := ⟨ρA, ρA_mem⟩
  set σ' : autIn ⊤ P5 := ⟨σA, σA_mem⟩
  have hgen : (⊤ : Subgroup (autIn ⊤ P5)) = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    refine (eq_top_iff.mpr fun x _ => ?_).symm
    obtain ⟨k, l, hkl⟩ := mem_autIn x.2
    have hx : x = ρ' ^ (k : ℕ) * σ' ^ (l : ℕ) := Subtype.ext (by simpa [ρ', σ'] using hkl)
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers _)) _) (Subgroup.pow_mem _ (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers _)) _)
  have hσ2 : σ' ^ 2 = 1 := Subtype.ext (by simpa [σ'] using σA_sq)
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := Subtype.ext (by simpa [σ', ρ'] using σA_ρA)
  have hσρ : σ' ∉ Subgroup.zpowers ρ' := by
    intro h
    apply σA_not_mem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa [ρ', σ'] using congrArg Subtype.val hn⟩
  have hord : orderOf ρ' = 4 := (Subgroup.orderOf_mk ρA ρA_mem).trans orderOf_ρA
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ' σ' hgen hσ2 hrel hσρ
  rw [hord] at e
  exact ⟨e⟩

end U54

open Item434SmallTwoOther in
theorem k417DatumU54_holds : K417DatumU54 := by
  intro D hD
  obtain ⟨hDe, -, F, hFD, hF9, -⟩ := hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := UTools.finite_projSU_gf16 5
  have hD3 : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hDe.2 x x.2)⟩
  have hle := Item434AltPerm.card_le_of_isPGroup hD3
  rw [Item434SmallTwoOther.U54.factorization_card_U54] at hle
  have hge : 9 ≤ Nat.card D := hF9.trans (Subgroup.card_le_of_le hFD)
  have hD9 : Nat.card D = 9 := by
    have : Nat.card D ≤ 9 := by simpa using hle
    omega
  refine ⟨hD9, ?_⟩
  obtain ⟨g, hg⟩ := Res423Two.exists_map_conj_eq_of_card_nine
    Item434SmallTwoOther.U54.factorization_card_U54 hD9 (UTools.card_P₀U (n := 5) (by norm_num))
  have f2 := Sporadic.autInTopCongr (MulAut.conj g) D
  rw [hg] at f2
  obtain ⟨e⟩ := U54.nonempty_autIn_P₀
  exact ⟨f2.trans e⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Four
