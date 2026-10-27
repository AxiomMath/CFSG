module

public import CFSG.Quasithin.Background.SmithB51Sp4Desc
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.Quasithin.Background.HSp4M

public section

namespace CFSG.Quasithin

namespace FFC

namespace Sp4Off

open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

omit [Fintype ι] [DecidableEq ι] in
theorem sq_eq_one_stdMod [CharP K 2] (v : StdMod ι K) : v ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul]
  funext i
  exact CharTwo.add_self_eq_zero _

omit [Fintype ι] [DecidableEq ι] in
theorem card_inf_fixV_eq {a : MulAut (StdMod ι K)} {F : Subgroup (MulAut (StdMod ι K))}
    (hF : F ≤ linSub) :
    Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ fixV F) =
      Nat.card {v : ι → K // v ∈ fixLin F hF ∧ toAddMap a v = v} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, fun y hy => ?_, ?_⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.1, ?_, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }
  · exact congrArg Multiplicative.toAdd (x.2.2 y hy)
  · exact congrArg Multiplicative.toAdd (mem_fixV_zpowers_iff.mp x.2.1)
  · exact mem_fixV_zpowers_iff.mpr (congrArg Multiplicative.ofAdd v.2.2)
  · exact fun y hy => congrArg Multiplicative.ofAdd (v.2.1 y hy)

omit [Fintype ι] in
theorem orderOf_eq_two [Nonempty ι] {a : MulAut (StdMod ι K)} {σ : K ≃+* K}
    (ha : IsSemilinear a σ) (hσ : σ ≠ RingEquiv.refl K) (ha2 : a * a = 1) : orderOf σ = 2 := by
  have h1 : IsSemilinear (a * a) (σ.trans σ) := ha.mul ha
  rw [ha2] at h1
  have h2 : σ ^ 2 = 1 := by
    have := h1.unique isSemilinear_one
    rw [sq]
    exact this
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hσ
  · exact h

theorem mul_succ_le_six {d k : ℕ} (h : k + d = 4) : d * (k + 1) ≤ 6 := by
  have hd : d ≤ 4 := by omega
  interval_cases d <;> omega

theorem card_mul_card_fix_le [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (hι : Fintype.card ι = 4) {a : MulAut (StdMod ι K)}
    {σ : K ≃+* K} (ha : IsSemilinear a σ) (hσ : σ ≠ RingEquiv.refl K) (ha2 : a * a = 1)
    {E₀ : Subgroup (MulAut (StdMod ι K))} (hlin : E₀ ≤ linSub)
    (hcomm : ∀ x ∈ E₀, x * a = a * x) (hE : IsElemAbelian2 E₀) :
    Nat.card E₀ * Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ fixV E₀) ≤ 2 ^ (3 * n) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have : Finite (StdMod ι K) := Pi.finite
  have hord := orderOf_eq_two ha hσ ha2
  obtain ⟨b, hb⟩ := exists_basis_fixed_of_semilinear hn hK ha hord (by rw [sq]; exact ha2)
  set W := fixV (Subgroup.zpowers a) with hW
  have hmemW : ∀ v : ι → K, Multiplicative.ofAdd v ∈ W ↔ toAddMap a v = v := fun v =>
    mem_fixV_zpowers_iff.trans ⟨fun h => congrArg Multiplicative.toAdd h,
      fun h => congrArg Multiplicative.ofAdd h⟩
  have hEW : E₀ ≤ stabSub W := by
    refine B1.le_stabSub_of_invariant fun x hx w hw => ?_
    rw [hW, mem_fixV_zpowers_iff] at hw ⊢
    change (a * x) w = x w
    rw [← hcomm x hx]
    change x (a w) = x w
    rw [hw]
  have hfaith : E₀ ⊓ centSub W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine eq_one_of_linear_of_fix_basis (hlin hx.1) b fun i => ?_
    exact congrArg Multiplicative.toAdd (hx.2 _ ((hmemW (b i)).mpr (hb i)))
  have hc1 : Nat.card ↥(E₀ ⊓ centSub W) = 1 := by
    rw [hfaith, Subgroup.card_bot]
  set D := autSub E₀ W with hD
  have hDcard : Nat.card D = Nat.card E₀ := by
    have := card_autSub_mul hEW
    rwa [hc1, mul_one] at this
  have hDfix : Nat.card (fixV D) = Nat.card ↥(W ⊓ fixV E₀) := by
    rw [← map_subtype_fixV_autSub hEW, Subgroup.card_map_of_injective W.subtype_injective]
  have hDel : IsElemAbelian2 D := by
    refine ⟨fun φ hφ ψ hψ => ?_, fun φ hφ => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      obtain ⟨k, hk, rfl⟩ := mem_autSub.mp hψ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hE.1 _ hg _ hk)
    · obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (by simpa using hE.2 _ hg)
      rw [this, map_one]
  have hVW : ∀ w : W, w ^ 2 = 1 := B1.sq_eq_one_sub sq_eq_one_stdMod W
  let val : Subgroup (MulAut W) → ℕ := fun F => Nat.card F * Nat.card (fixV F)
  obtain ⟨Fm, hFmD, hFmax⟩ := Set.exists_max_image {F : Subgroup (MulAut W) | F ≤ D} val
    (Set.toFinite _) ⟨D, (le_refl D : D ≤ D)⟩
  have hDval : Nat.card E₀ * Nat.card ↥(W ⊓ fixV E₀) ≤ val Fm := by
    rw [← hDcard, ← hDfix]
    exact hFmax D (le_refl D : D ≤ D)
  have hWsq : Nat.card W ^ 2 = 2 ^ (4 * n) := by
    have h1 := card_fix_sq ha hσ ha2 ⊤ fun v _ => trivial
    have h2 : Nat.card {v : ι → K // v ∈ (⊤ : Submodule K (ι → K)) ∧ toAddMap a v = v} =
        Nat.card W := by
      refine Nat.card_congr
        { toFun := fun v => ⟨Multiplicative.ofAdd v.1, (hmemW v.1).mpr v.2.2⟩
          invFun := fun w => ⟨Multiplicative.toAdd w.1, trivial, (hmemW _).mp w.2⟩
          left_inv := fun v => rfl
          right_inv := fun w => rfl }
    rw [h2, Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_fun, hK,
      Nat.card_eq_fintype_card (α := ι), hι, ← pow_mul] at h1
    rw [h1, mul_comm]
  have hquad : ∀ F : Subgroup (MulAut W), F ≤ D → IsQuadratic F → val F ≤ 2 ^ (3 * n) := by
    intro F hFD hFq
    set Fh := B1.preB E₀ W F with hFh
    have hFhE : Fh ≤ E₀ := B1.preB_le E₀ W F
    have hFhlin : Fh ≤ linSub := hFhE.trans hlin
    have htr := B1.card_transfer hEW hFD
    rw [hc1, mul_one] at htr
    have hval : val F = Nat.card Fh * Nat.card ↥(W ⊓ fixV Fh) := htr
    have hq : ∀ x ∈ Fh, ∀ y ∈ Fh, ∀ v, toAddMap a v = v →
        toAddMap y (toAddMap x v - v) = toAddMap x v - v := by
      intro x hx y hy v hv
      obtain ⟨-, hxs, hxF⟩ := B1.mem_preB.mp hx
      obtain ⟨-, hys, hyF⟩ := B1.mem_preB.mp hy
      set w : W := ⟨Multiplicative.ofAdd v, (hmemW v).mpr hv⟩
      have hc : resHom W ⟨x, hxs⟩ w * w⁻¹ ∈ fixV F :=
        hFq (Subgroup.subset_closure ⟨_, hxF, w, rfl⟩)
      have h1 := congrArg (fun z : W => Multiplicative.toAdd (z : StdMod ι K))
        (hc _ hyF)
      simp only [resHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
        toAdd_mul, toAdd_inv] at h1
      rw [toAddMap_sub]
      change Multiplicative.toAdd (y (x (Multiplicative.ofAdd v))) -
          Multiplicative.toAdd (y (Multiplicative.ofAdd v)) =
        Multiplicative.toAdd (x (Multiplicative.ofAdd v)) - v
      rw [sub_eq_add_neg, sub_eq_add_neg]
      exact h1
    have hFhcomm : ∀ x ∈ Fh, x * a = a * x := fun x hx => hcomm x (hFhE hx)
    have hcard := card_le_pow_finrank b hb hFhlin hFhcomm hq
    set C := fixLin Fh hFhlin with hC
    set c := Nat.card {v : ι → K // v ∈ C ∧ toAddMap a v = v} with hcdef
    have hcsq : c ^ 2 = 2 ^ (n * Module.finrank K C) := by
      rw [hcdef, card_fix_sq ha hσ ha2 C fun v hv => toAddMap_mem_fixLin hFhcomm hv,
        Module.natCard_eq_pow_finrank (K := K) (V := C), hK, ← pow_mul]
    have hdim : Module.finrank K ((ι → K) ⧸ C) + Module.finrank K C = 4 := by
      rw [Submodule.finrank_quotient_add_finrank, Module.finrank_fintype_fun_eq_card, hι]
    have hWF : Nat.card ↥(W ⊓ fixV Fh) = c := card_inf_fixV_eq hFhlin
    rw [hval, hWF]
    set k := Module.finrank K ((ι → K) ⧸ C)
    set d := Module.finrank K C
    have h1 : Nat.card Fh * c ≤ c ^ (k + 1) := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right c hcard
    have h2 : (c ^ (k + 1)) ^ 2 ≤ (2 ^ (3 * n)) ^ 2 := by
      rw [← pow_mul, mul_comm (k + 1), pow_mul, hcsq, ← pow_mul, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num)
        (by nlinarith [mul_succ_le_six hdim])
    have h3 : c ^ (k + 1) ≤ 2 ^ (3 * n) :=
      (Nat.pow_le_pow_iff_left (by norm_num)).mp h2
    exact h1.trans h3
  by_cases hFm0 : Fm = ⊥
  · have h0 : val Fm = Nat.card W := by
      change Nat.card Fm * Nat.card (fixV Fm) = _
      rw [hFm0, B1.card_bot_mul_card_fixV]
    have hW3 : Nat.card W ≤ 2 ^ (3 * n) := by
      have : Nat.card W ^ 2 ≤ (2 ^ (3 * n)) ^ 2 := by
        rw [hWsq, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
    rw [← h0] at hW3
    exact hDval.trans hW3
  · have hoff : IsFFStarOffender D Fm := by
      refine ⟨hFmD, hFm0, ⟨fun x hx y hy => hDel.1 x (hFmD hx) y (hFmD hy),
        fun x hx => hDel.2 x (hFmD hx)⟩, fun B hB => ?_⟩
      exact hFmax B (hB.trans hFmD)
    obtain ⟨F, hFFm, -, hFq, hFval, -, -⟩ := exists_quadratic_offender_le hVW hoff
    have hFval' : val Fm = val F := hFval.symm
    rw [hFval'] at hDval
    exact hDval.trans (hquad F (hFFm.trans hFmD) hFq)

section Natural

theorem mem_natImage_of_linear [Finite K] [CharP K 2] {x : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hxN : x ∈ natNorm (StatedSp 2 K)) (hxl : x ∈ linSub) (hx2 : x * x = 1) :
    x ∈ natImage (StatedSp 2 K) := by
  obtain ⟨B, σ, D, -, hxf⟩ := Sp4.exists_eq_of_mem_natNorm hxN
  have hsl : IsSemilinear x σ := by
    intro c v
    rw [hxf, hxf]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [show (fun i => σ c * σ (v i)) = σ c • fun i => σ (v i) from rfl, Matrix.mulVec_smul,
      smul_comm]
  have hσ : σ = RingEquiv.refl K := hsl.unique hxl
  subst hσ
  have hx' : ∀ v, toAddMap x v = D • (((B : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := fun v => hxf v
  obtain ⟨hxB, -⟩ := Sp4.eq_of_smul_sq B D hx' hx2
  exact ⟨B, hxB.symm⟩

theorem card_mul_card_fixV_lt [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {E : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))}
    (hEN : E ≤ natNorm (StatedSp 2 K)) (hE : IsElemAbelian2 E)
    (hnot : ¬ E ≤ natImage (StatedSp 2 K)) :
    Nat.card E * Nat.card (fixV E) < Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) := by
  set E₀ := E ⊓ linSub with hE₀
  have h2 : Nat.card E ≤ 2 * Nat.card E₀ :=
    card_le_two_mul_card_inf_linSub Sp4.hasScalarCommutant_statedSp (by omega) hK hEN
      fun x hx => hE.2 x hx
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE.2 x hx
  have hE₀ : E₀ ≤ natImage (StatedSp 2 K) := fun x hx =>
    mem_natImage_of_linear (hEN hx.1) hx.2 (hsq x hx.1)
  obtain ⟨a, haE, haL⟩ : ∃ a ∈ E, a ∉ linSub (ι := Fin 2 ⊕ Fin 2) (K := K) := by
    by_contra h
    push Not at h
    exact hnot fun x hx => hE₀ ⟨hx, h x hx⟩
  obtain ⟨σ, ha⟩ := exists_semilinear Sp4.hasScalarCommutant_statedSp (hEN haE)
  have hσ : σ ≠ RingEquiv.refl K := fun h => haL (mem_linSub.mpr (h ▸ ha))
  have hcomm : ∀ x ∈ E₀, x * a = a * x := fun x hx => hE.1 x hx.1 a haE
  have hE₀el : IsElemAbelian2 E₀ :=
    ⟨fun x hx y hy => hE.1 x hx.1 y hy.1, fun x hx => hE.2 x hx.1⟩
  have hkey := card_mul_card_fix_le (by omega) hK (by simp) ha hσ (hsq a haE) inf_le_right
    hcomm hE₀el
  have hfix : Nat.card (fixV E) ≤ Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ fixV E₀) :=
    Subgroup.card_le_of_le (le_inf (B1.fixV_le_fixV (Subgroup.zpowers_le.mpr haE))
      (B1.fixV_le_fixV inf_le_left))
  have hS : Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) = 2 ^ (4 * n) := by
    rw [card_stdMod, hK, ← pow_mul]
    simp [mul_comm]
  have h3 : 2 * 2 ^ (3 * n) < 2 ^ (4 * n) := by
    rw [← pow_succ']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc Nat.card E * Nat.card (fixV E)
      ≤ (2 * Nat.card E₀) * Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ fixV E₀) :=
        Nat.mul_le_mul h2 hfix
    _ = 2 * (Nat.card E₀ * Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ fixV E₀)) := by ring
    _ ≤ 2 * 2 ^ (3 * n) := Nat.mul_le_mul_left 2 hkey
    _ < Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) := by rw [hS]; exact h3

end Natural

end Sp4Off

end FFC

end CFSG.Quasithin
