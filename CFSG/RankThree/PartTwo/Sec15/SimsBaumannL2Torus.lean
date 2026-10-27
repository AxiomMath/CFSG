module

import CFSG.GH74.GLS.IVK.L2.TorusMatrices
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open Matrix
open scoped MatrixGroups

section Torus

variable {F : Type} [Field F]

private def sbT_tor (u : Fˣ) : SL(2, F) :=
  ⟨!![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

private theorem sbT_tor_mul (u v : Fˣ) : sbT_tor (u * v) = sbT_tor u * sbT_tor v := by
  apply Subtype.ext
  change (!![((u * v : Fˣ) : F), 0; 0, (((u * v)⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) =
    !![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)] * !![(v : F), 0; 0, ((v⁻¹ : Fˣ) : F)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem sbT_tor_one : sbT_tor (1 : Fˣ) = (1 : SL(2, F)) :=
  Subtype.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [sbT_tor])

private def sbT_torHom : Fˣ →* SL(2, F) where
  toFun := sbT_tor
  map_one' := sbT_tor_one
  map_mul' := sbT_tor_mul

private theorem sbT_tor_inv (u : Fˣ) : sbT_tor u⁻¹ = (sbT_tor u)⁻¹ :=
  map_inv sbT_torHom u

private theorem sbT_tor_pow (u : Fˣ) (m : ℕ) : sbT_tor (u ^ m) = sbT_tor u ^ m :=
  map_pow sbT_torHom u m

private theorem sbT_tor_injective : Function.Injective (sbT_tor : Fˣ → SL(2, F)) := by
  intro u v h
  have h' : (sbT_tor u).1 0 0 = (sbT_tor v).1 0 0 := by rw [h]
  exact Units.ext (by simpa [sbT_tor] using h')

private theorem sbT_mul_tor_01 (k : SL(2, F)) (u : Fˣ) :
    (k * sbT_tor u).1 0 1 = k.1 0 1 * ((u⁻¹ : Fˣ) : F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [sbT_tor, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sbT_mul_tor_10 (k : SL(2, F)) (u : Fˣ) :
    (k * sbT_tor u).1 1 0 = k.1 1 0 * (u : F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [sbT_tor, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sbT_tor_mul_01 (k : SL(2, F)) (u : Fˣ) :
    (sbT_tor u * k).1 0 1 = (u : F) * k.1 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [sbT_tor, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sbT_tor_mul_10 (k : SL(2, F)) (u : Fˣ) :
    (sbT_tor u * k).1 1 0 = ((u⁻¹ : Fˣ) : F) * k.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [sbT_tor, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sbT_exists_tor {k : SL(2, F)} (h01 : k.1 0 1 = 0) (h10 : k.1 1 0 = 0) :
    ∃ u : Fˣ, k = sbT_tor u := by
  have hdet : k.1 0 0 * k.1 1 1 = 1 := by
    have := k.2
    rw [Matrix.det_fin_two, h10, h01] at this
    simpa using this
  have h0 : k.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ h0, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sbT_tor, h01, h10, inv_eq_of_mul_eq_one_right hdet]

private theorem sbT_exists_tor_of_comm {ω : Fˣ} (hω : ω ≠ ω⁻¹) {k : SL(2, F)}
    (hk : k * sbT_tor ω = sbT_tor ω * k) : ∃ u : Fˣ, k = sbT_tor u := by
  apply sbT_exists_tor
  · have h : (k * sbT_tor ω).1 0 1 = (sbT_tor ω * k).1 0 1 := by rw [hk]
    rw [sbT_mul_tor_01, sbT_tor_mul_01] at h
    have h' : k.1 0 1 * (((ω⁻¹ : Fˣ) : F) - ω) = 0 := by linear_combination h
    exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 fun h => hω (Units.ext h.symm))
  · have h : (k * sbT_tor ω).1 1 0 = (sbT_tor ω * k).1 1 0 := by rw [hk]
    rw [sbT_mul_tor_10, sbT_tor_mul_10] at h
    have h' : k.1 1 0 * ((ω : F) - ((ω⁻¹ : Fˣ) : F)) = 0 := by linear_combination h
    exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 fun h => hω (Units.ext h))

private theorem sbT_trace_conj (p N : SL(2, F)) : (p * N * p⁻¹).1.trace = N.1.trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

private theorem sbT_sq_eq_one_of_trace_eq_zero [CharP F 2] (a : SL(2, F))
    (h : a.1 0 0 + a.1 1 1 = 0) : a ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hd := a.2
  rw [Matrix.det_fin_two] at hd
  have e00 : a.1 0 0 * a.1 0 0 + a.1 0 1 * a.1 1 0 = 1 := by
    linear_combination a.1 0 0 * h - hd - h2
  have e01 : a.1 0 0 * a.1 0 1 + a.1 0 1 * a.1 1 1 = 0 := by
    linear_combination a.1 0 1 * h
  have e10 : a.1 1 0 * a.1 0 0 + a.1 1 1 * a.1 1 0 = 0 := by
    linear_combination a.1 1 0 * h
  have e11 : a.1 1 0 * a.1 0 1 + a.1 1 1 * a.1 1 1 = 1 := by
    linear_combination a.1 1 1 * h - hd - h2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using e00
  · simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using e01
  · simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using e10
  · simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using e11

private theorem sbT_conj_pow {G : Type*} [Group G] (P X : G) (m : ℕ) :
    (P⁻¹ * X * P) ^ m = P⁻¹ * X ^ m * P := by
  have := conj_pow (a := P⁻¹) (b := X) (i := m)
  rwa [inv_inv] at this

private theorem sbT_exists_diag [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hev : Even n) {a : SL(2, F)} (ha3 : orderOf a = 3) :
    ∃ (P : SL(2, F)) (ω : Fˣ), ω ^ 3 = 1 ∧ ω ≠ 1 ∧ a = P * sbT_tor ω * P⁻¹ := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have : Fintype F := Fintype.ofFinite F
  have ha1 : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  have hmod : 2 ^ n % 3 = 1 := by
    obtain ⟨r, hr⟩ := hev
    rw [hr, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hpow : a ^ Fintype.card F = a := by
    rw [← Nat.card_eq_fintype_card, hF]
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 3 * k + 1 := ⟨2 ^ n / 3, by omega⟩
    rw [hk, pow_succ, pow_mul, ha1, one_pow, one_mul]
  have hmat : a.1 ^ Fintype.card F = a.1 := by
    have := congrArg Subtype.val hpow
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  obtain ⟨r, hr⟩ := IVK.L2Torus.exists_det_sub_eq_zero F a.1 hmat
  have hr_tr := IVK.L2Torus.trace_eq_of_det_sub_eq_zero hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr_tr
  have hr1 : r ≠ 1 := by
    rintro rfl
    have htr0 : a.1 0 0 + a.1 1 1 = 0 := by linear_combination hr_tr + h2
    have h32 : 3 ∣ 2 := ha3 ▸ orderOf_dvd_of_pow_eq_one (sbT_sq_eq_one_of_trace_eq_zero a htr0)
    omega
  have hrne : r ≠ r⁻¹ := by
    intro h
    apply hr1
    have hrr : r * r = 1 := by
      calc r * r = r * r⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hr0
    have h' : (r - 1) * (r - 1) = 0 := by linear_combination hrr + (1 - r) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h')
  have hab : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
  have htr : a.1 0 0 + a.1 1 1 = r + r⁻¹ := by
    field_simp
    linear_combination hr_tr
  obtain ⟨P, hP⟩ := IVK.L2Torus.exists_conj_mem_diagSub_of_eigenvalue hab hrne htr
  obtain ⟨hP01, hP10⟩ := IVK.L2Torus.mem_diagSub.1 hP
  obtain ⟨ω, hω⟩ := sbT_exists_tor hP01 hP10
  have hω3 : sbT_tor ω ^ 3 = 1 := by
    rw [← hω, sbT_conj_pow, ha1]
    group
  refine ⟨P, ω, ?_, ?_, ?_⟩
  · apply sbT_tor_injective
    rw [sbT_tor_pow, hω3, sbT_tor_one]
  · intro h1
    rw [h1, sbT_tor_one] at hω
    have ha : a = 1 := by
      calc a = P * (P⁻¹ * a * P) * P⁻¹ := by group
        _ = 1 := by rw [hω]; group
    rw [ha, orderOf_one] at ha3
    omega
  · rw [← hω]
    group

private theorem sbT_map_tor (σ : F ≃+* F) (u : Fˣ) :
    (Matrix.SpecialLinearGroup.map σ.toRingHom (sbT_tor u)).1.trace =
      σ (u : F) + (σ (u : F))⁻¹ := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.trace_fin_two]
  simp [sbT_tor, RingHom.mapMatrix_apply, Matrix.map_apply, map_inv₀]

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField in
private theorem sbT_semilinear {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (α : SL(2, F) ≃* SL(2, F)) :
    ∃ (p : SL(2, F)) (σ : F ≃+* F),
      ∀ x, α x = p * Matrix.SpecialLinearGroup.map σ.toRingHom x * p⁻¹ := by
  obtain ⟨⟨p, σ⟩, hpσ, -⟩ := (even_SL2_full_automorphism_semilinear_model hn hF).2.2.2.2 α
  exact ⟨p, σ, hpσ⟩

private theorem sbT_core [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 4 ≤ n)
    {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (α : SL(2, F) ≃* SL(2, F))
    (hαω : α (sbT_tor ω) = sbT_tor ω) (hαα : ∀ x, α (α x) = x)
    (hcomm : ∀ k : SL(2, F), k * sbT_tor ω = sbT_tor ω * k → (α k * k⁻¹) ^ 12 = 1) :
    ∃ p : SL(2, F), ∀ x, α x = p * x * p⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hω3F : (ω : F) ^ 3 = 1 := by
    have := congrArg Units.val hω3
    simpa using this
  have hω1F : (ω : F) - 1 ≠ 0 := sub_ne_zero.2 fun h => hω1 (Units.ext (by simpa using h))
  have hωF : (ω : F) ^ 2 + ω + 1 = 0 := by
    have h : ((ω : F) - 1) * ((ω : F) ^ 2 + ω + 1) = 0 := by linear_combination hω3F
    exact (mul_eq_zero.1 h).resolve_left hω1F
  have hωinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hω3)
  have hne : ω ≠ ω⁻¹ := by
    intro h
    rw [hωinv] at h
    apply hω1
    have h' : ω * 1 = ω * ω := by rw [mul_one, ← sq]; exact h
    exact (mul_left_cancel h').symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgω : sbT_tor g * sbT_tor ω = sbT_tor ω * sbT_tor g := by
    rw [← sbT_tor_mul, ← sbT_tor_mul, mul_comm]
  have hαk : α (sbT_tor g) * sbT_tor ω = sbT_tor ω * α (sbT_tor g) := by
    calc α (sbT_tor g) * sbT_tor ω = α (sbT_tor g) * α (sbT_tor ω) := by rw [hαω]
      _ = α (sbT_tor g * sbT_tor ω) := (map_mul α _ _).symm
      _ = α (sbT_tor ω * sbT_tor g) := by rw [hgω]
      _ = α (sbT_tor ω) * α (sbT_tor g) := map_mul α _ _
      _ = sbT_tor ω * α (sbT_tor g) := by rw [hαω]
  obtain ⟨μ, hμ⟩ := sbT_exists_tor_of_comm hne hαk
  have hc := hcomm (sbT_tor g) hgω
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, u = μ * g⁻¹ := ⟨_, rfl⟩
  have hμu : μ = u * g := by rw [hu, inv_mul_cancel_right]
  have hu12 : u ^ 12 = 1 := by
    apply sbT_tor_injective
    rw [sbT_tor_pow, sbT_tor_one, hu, sbT_tor_mul, sbT_tor_inv, ← hμ]
    exact hc
  have hu12F : (u : F) ^ 12 = 1 := by
    have := congrArg Units.val hu12
    simpa using this
  have hfour : ∀ x : F, x ^ 4 = 1 → x = 1 := by
    intro x hx
    have h4 : (x - 1) ^ 4 = 0 := by
      linear_combination hx + (-2 * x ^ 3 + 3 * x ^ 2 - 2 * x + 1) * h2
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h4)
  have hu3F : (u : F) ^ 3 = 1 := hfour _ (by rw [← pow_mul]; exact hu12F)
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa using hu3F)
  have hucases : u = 1 ∨ u = ω ∨ u = ω ^ 2 := by
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    · right
      have hu1F : (u : F) - 1 ≠ 0 := sub_ne_zero.2 fun h => hu1 (Units.ext (by simpa using h))
      have hq : (u : F) ^ 2 + u + 1 = 0 := by
        have h : ((u : F) - 1) * ((u : F) ^ 2 + u + 1) = 0 := by linear_combination hu3F
        exact (mul_eq_zero.1 h).resolve_left hu1F
      have hprod : ((u : F) - ω) * ((u : F) - ω ^ 2) = 0 := by
        linear_combination hq - (u : F) * hωF + hω3F
      rcases mul_eq_zero.1 hprod with h | h
      · exact Or.inl (Units.ext (sub_eq_zero.1 h))
      · exact Or.inr (Units.ext (by simpa using sub_eq_zero.1 h))
  have hαu : α (sbT_tor u) = sbT_tor u := by
    rcases hucases with h | h | h
    · rw [h, sbT_tor_one, map_one]
    · rw [h]; exact hαω
    · rw [h, sbT_tor_pow, map_pow, hαω]
  have hμg : μ = g := by
    have h1 : α (sbT_tor μ) = sbT_tor g := by rw [← hμ, hαα]
    have hmul : sbT_tor u * (sbT_tor u * sbT_tor g) = sbT_tor g := by
      calc sbT_tor u * (sbT_tor u * sbT_tor g) = sbT_tor u * sbT_tor μ := by
            rw [hμu, sbT_tor_mul]
        _ = α (sbT_tor u) * α (sbT_tor g) := by rw [hαu, hμ]
        _ = α (sbT_tor u * sbT_tor g) := (map_mul α _ _).symm
        _ = α (sbT_tor μ) := by rw [hμu, sbT_tor_mul]
        _ = sbT_tor g := h1
    have h3 : u * (u * g) = g :=
      sbT_tor_injective (by rw [sbT_tor_mul, sbT_tor_mul]; exact hmul)
    have h4 : u * u = 1 := by
      have : u * u * g = 1 * g := by rw [mul_assoc, h3, one_mul]
      exact mul_right_cancel this
    have hu1 : u = 1 := by
      calc u = u * (u * u) := by rw [h4, mul_one]
        _ = u ^ 3 := by rw [pow_three]
        _ = 1 := hu3
    rw [hμu, hu1, one_mul]
  have hαg : α (sbT_tor g) = sbT_tor g := by rw [hμ, hμg]
  obtain ⟨p, σ, hpσ'⟩ := sbT_semilinear (by omega) hF α
  have htr : (α (sbT_tor g)).1.trace =
      (Matrix.SpecialLinearGroup.map σ.toRingHom (sbT_tor g)).1.trace := by
    rw [hpσ' (sbT_tor g)]
    exact sbT_trace_conj p _
  rw [hαg] at htr
  have hxx : (g : F) + (g : F)⁻¹ = σ (g : F) + (σ (g : F))⁻¹ := by
    rw [sbT_map_tor] at htr
    simpa [sbT_tor, Matrix.trace_fin_two] using htr
  have hg0 : (g : F) ≠ 0 := g.ne_zero
  have hs0 : σ (g : F) ≠ 0 := by simpa using hg0
  have hsplit : σ (g : F) = g ∨ σ (g : F) = (g : F)⁻¹ := by
    have h : (σ (g : F) - g) * (σ (g : F) - (g : F)⁻¹) = 0 := by
      linear_combination (-(σ (g : F))) * hxx + mul_inv_cancel₀ hg0 - mul_inv_cancel₀ hs0
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hgen : ∀ y : F, y ≠ 0 → ∃ m : ℤ, y = (g : F) ^ m := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg (Units.mk0 y hy))
    refine ⟨m, ?_⟩
    have := congrArg Units.val hm
    simpa using this.symm
  rcases hsplit with hA | hB
  ·
    have hσid : ∀ y : F, σ y = y := by
      intro y
      by_cases hy : y = 0
      · simp [hy]
      · obtain ⟨m, rfl⟩ := hgen y hy
        rw [map_zpow₀, hA]
    refine ⟨p, fun x => ?_⟩
    have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom x = x := by
      apply Subtype.ext
      ext i j
      simp [hσid]
    rw [hpσ' x, hmap]
  ·
    exfalso
    have hσinv : ∀ y : F, y ≠ 0 → σ y = y⁻¹ := by
      intro y hy
      obtain ⟨m, rfl⟩ := hgen y hy
      rw [map_zpow₀, hB, _root_.inv_zpow]
    have hg3F : (g : F) ^ 3 = 1 := by
      by_cases h1 : (1 : F) + g = 0
      · have hg1 : (g : F) = 1 := by linear_combination h1 - h2
        rw [hg1]
        norm_num
      · have hs : σ (1 + (g : F)) = (1 + (g : F))⁻¹ := hσinv _ h1
        rw [map_add, map_one, hB] at hs
        have hmul : (1 + (g : F)) * (1 + (g : F)⁻¹) = 1 := by
          rw [hs]
          exact mul_inv_cancel₀ h1
        have hgi : (g : F) * (g : F)⁻¹ = 1 := mul_inv_cancel₀ hg0
        have hgq : (g : F) ^ 2 + g + 1 = 0 := by
          linear_combination (g : F) * hmul - (1 + (g : F)) * hgi
        linear_combination ((g : F) - 1) * hgq
    have hgo : orderOf g = 2 ^ n - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
    have hg3 : g ^ 3 = 1 := Units.ext (by simpa using hg3F)
    have hdvd : 2 ^ n - 1 ∣ 3 := by
      rw [← hgo]
      exact orderOf_dvd_of_pow_eq_one hg3
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have h16 : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega

private theorem sbT_inner [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 4 ≤ n)
    (hev : Even n) (α : SL(2, F) ≃* SL(2, F)) {a : SL(2, F)} (ha3 : orderOf a = 3)
    (hαa : α a = a) (hαα : ∀ x, α (α x) = x)
    (hcomm : ∀ k : SL(2, F), k * a = a * k → (α k * k⁻¹) ^ 12 = 1) :
    ∃ p : SL(2, F), ∀ x, α x = p * x * p⁻¹ := by
  obtain ⟨P, ω, hω3, hω1, rfl⟩ := sbT_exists_diag hF hev ha3
  obtain ⟨β, hβ⟩ : ∃ β : SL(2, F) ≃* SL(2, F), ∀ x, β x = P⁻¹ * α (P * x * P⁻¹) * P :=
    ⟨(MulAut.conj P).trans (α.trans (MulAut.conj P⁻¹)), fun x => by simp⟩
  have hβω : β (sbT_tor ω) = sbT_tor ω := by
    rw [hβ, hαa]
    group
  have hββ : ∀ x, β (β x) = x := by
    intro x
    rw [hβ, hβ]
    have hx : P * (P⁻¹ * α (P * x * P⁻¹) * P) * P⁻¹ = α (P * x * P⁻¹) := by group
    rw [hx, hαα]
    group
  have hβc : ∀ k : SL(2, F), k * sbT_tor ω = sbT_tor ω * k → (β k * k⁻¹) ^ 12 = 1 := by
    intro k hk
    have hk' : (P * k * P⁻¹) * (P * sbT_tor ω * P⁻¹) =
        (P * sbT_tor ω * P⁻¹) * (P * k * P⁻¹) := by
      calc (P * k * P⁻¹) * (P * sbT_tor ω * P⁻¹) = P * (k * sbT_tor ω) * P⁻¹ := by group
        _ = P * (sbT_tor ω * k) * P⁻¹ := by rw [hk]
        _ = (P * sbT_tor ω * P⁻¹) * (P * k * P⁻¹) := by group
    have h12 := hcomm _ hk'
    have hx : β k * k⁻¹ = P⁻¹ * (α (P * k * P⁻¹) * (P * k * P⁻¹)⁻¹) * P := by
      rw [hβ]
      group
    rw [hx, sbT_conj_pow, h12]
    group
  obtain ⟨p', hp'⟩ := sbT_core hF hn hω3 hω1 β hβω hββ hβc
  refine ⟨P * p' * P⁻¹, fun x => ?_⟩
  have hx : P * (P⁻¹ * x * P) * P⁻¹ = x := by group
  have h1 : α x = P * β (P⁻¹ * x * P) * P⁻¹ := by
    rw [hβ, hx]
    group
  rw [h1, hp']
  group

end Torus

private theorem sbT_projSL_eq_range (F : Type) [Field F] :
    CFSG.Assembly.RankThreeEven.projSL 2 F =
      (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).range := by
  rw [CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
    Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

private noncomputable def sbT_slEquiv (F : Type) [Field F] [CharP F 2] :
    SL(2, F) ≃* CFSG.Assembly.RankThreeEven.projSL 2 F :=
  MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).codRestrict
      (CFSG.Assembly.RankThreeEven.projSL 2 F) (fun A => by
        rw [sbT_projSL_eq_range]
        exact ⟨A, rfl⟩))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro A hA
      have h : A ∈ (Matrix.SpecialLinearGroup.toPGL :
          SL(2, F) →* ProjGenLinGroup (Fin 2) F).ker := by
        rw [MonoidHom.mem_ker] at hA ⊢
        exact congrArg Subtype.val hA
      rw [Matrix.SpecialLinearGroup.toPGL_ker,
        CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.sl2_center_eq_bot] at h
      exact h,
     by
      rintro ⟨x, hx⟩
      rw [sbT_projSL_eq_range] at hx
      obtain ⟨A, rfl⟩ := hx
      exact ⟨A, rfl⟩⟩

theorem false_of_commutator_pow_twelve {Y : Type} [Group Y] [Finite Y] {Lb : Subgroup Y}
    [Lb.Normal] {n : ℕ} (hn : 4 ≤ n) (hev : Even n)
    (e : ↥Lb ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    (hC : Subgroup.centralizer (Lb : Set Y) = ⊥)
    {a t : Y} (ha : a ∈ Lb) (ha3 : orderOf a = 3) (ht : t ∉ Lb) (ht2 : t ^ 2 = 1)
    (hat : t * a = a * t)
    (hcomm : ∀ k ∈ Lb, k * a = a * k → (t * k * t⁻¹ * k⁻¹) ^ 12 = 1) : False := by
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨φ⟩ : Nonempty (SL(2, GaloisField 2 n) ≃* ↥Lb) :=
    ⟨(sbT_slEquiv (GaloisField 2 n)).trans e.symm⟩
  obtain ⟨α, hα⟩ : ∃ α : SL(2, GaloisField 2 n) ≃* SL(2, GaloisField 2 n),
      ∀ x, φ (α x) = MulAut.conjNormal t (φ x) :=
    ⟨(φ.trans (MulAut.conjNormal t)).trans φ.symm, fun x => by simp⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : SL(2, GaloisField 2 n), φ a₀ = ⟨a, ha⟩ := ⟨φ.symm ⟨a, ha⟩, by simp⟩
  have ha₀3 : orderOf a₀ = 3 := by
    rw [← MulEquiv.orderOf_eq φ a₀, ha₀, ← ha3]
    exact (Subgroup.orderOf_coe (⟨a, ha⟩ : ↥Lb)).symm
  have hαα : ∀ x, α (α x) = x := by
    intro x
    apply φ.injective
    rw [hα, hα]
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
    calc t * (t * (φ x : Y) * t⁻¹) * t⁻¹ = (t * t) * (φ x : Y) * (t * t)⁻¹ := by group
      _ = (φ x : Y) := by rw [ht2']; group
  have hαa : α a₀ = a₀ := by
    apply φ.injective
    rw [hα, ha₀]
    apply Subtype.ext
    show t * a * t⁻¹ = a
    rw [hat]
    group
  have hcomm₀ : ∀ k : SL(2, GaloisField 2 n), k * a₀ = a₀ * k → (α k * k⁻¹) ^ 12 = 1 := by
    intro k hk
    have hφk : φ k * (⟨a, ha⟩ : ↥Lb) = (⟨a, ha⟩ : ↥Lb) * φ k := by
      have := congrArg φ hk
      simpa [ha₀] using this
    have hcom' : (φ k : Y) * a = a * (φ k : Y) := congrArg Subtype.val hφk
    apply φ.injective
    rw [map_pow, map_mul, map_inv, hα, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
      Subgroup.coe_one]
    exact hcomm (φ k) (φ k).2 hcom'
  obtain ⟨p, hp⟩ := sbT_inner hF hn hev α ha₀3 hαa hαα hcomm₀
  apply ht
  have hcent : (φ p : Y)⁻¹ * t ∈ Subgroup.centralizer (Lb : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hconj : t * y * t⁻¹ = (φ p : Y) * y * (φ p : Y)⁻¹ := by
      have h1 := congrArg φ (hp (φ.symm ⟨y, hy⟩))
      simp only [hα, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      exact congrArg Subtype.val h1
    have h2 : t * y = (φ p : Y) * y * (φ p : Y)⁻¹ * t := by
      calc t * y = (t * y * t⁻¹) * t := by group
        _ = (φ p : Y) * y * (φ p : Y)⁻¹ * t := by rw [hconj]
    calc y * ((φ p : Y)⁻¹ * t) = (φ p : Y)⁻¹ * ((φ p : Y) * y * (φ p : Y)⁻¹ * t) := by group
      _ = (φ p : Y)⁻¹ * (t * y) := by rw [h2]
      _ = (φ p : Y)⁻¹ * t * y := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  rw [← hcent]
  exact (φ p).2

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
