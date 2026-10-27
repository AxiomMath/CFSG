module

public import CFSG.RankThree.PartOne.N1322.MonoAux
import Mathlib.Tactic.LinearCombination
public import CFSG.RankThree.PartOne.N1322.MonoFrame

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open Equiv

variable {K : Type*} [Field K]

theorem Lmono {d : CoreData K}
    (hL2 : ∀ l ∈ d.Lm, ∃ σ a, l = mono σ a ∧ σ 2 = 2 ∧ a 2 = 1)
    (x : d.Lm) {σ : Perm (Fin 3)} (hx : HasPerm (x : GL (Fin 3) K) σ) :
    σ 2 = 2 ∧ ∃ a, (x : GL (Fin 3) K) = mono σ a ∧ a 2 = 1 := by
  obtain ⟨σ', a, hxa, hσ', ha⟩ := hL2 x x.2
  have hσ : σ' = σ := HasPerm.unique ⟨a, hxa⟩ hx
  subst hσ
  exact ⟨hσ', a, hxa, ha⟩

theorem mono_aU_inv (x : Kˣ) :
    ((mono 1 (aU 0 1 x) : GL (Fin 3) K))⁻¹ = mono 1 (aU 0 1 x⁻¹) := by
  rw [mono_inv]
  refine congrArg₂ mono (by simp) ?_
  funext j
  simp only [inv_one, Perm.one_apply]
  exact congrFun (aU_inv 0 1 x) j

theorem mono_one_mulVec (a : Fin 3 → Kˣ) (w : Fin 3 → K) :
    ((mono 1 a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = fun j => (a j : K) * w j := by
  funext j
  simpa using mono_mulVec_apply 1 a w j

theorem mono_one_mul (a b : Fin 3 → Kˣ) :
    (mono 1 a : GL (Fin 3) K) * mono 1 b = mono 1 (fun j => a j * b j) := by
  rw [mono_mul]
  exact congrArg₂ mono (by simp) (by funext j; simp)

theorem mem_span_c_of_coord {μ : K} (hμ : μ ≠ 0) {c : Fin 3 → K} (hc : c = μ • Pi.single 2 1)
    {z : Fin 3 → K} (h0 : z 0 = 0) (h1 : z 1 = 0) : z ∈ Submodule.span K {c} := by
  refine Submodule.mem_span_singleton.2 ⟨z 2 / μ, ?_⟩
  funext j
  fin_cases j
  · simp [hc, h0]
  · simp [hc, h1]
  · simp [hc, div_mul_cancel₀ _ hμ]

theorem frame_a_false_kU (h2 : (2 : K) ≠ 0) {d : CoreData K} (hkU : NF7H.KUMat d.X d.Lm d.c)
    (hm : MonoStd d.X) {μ : K} (hμ : μ ≠ 0) (hc : d.c = μ • Pi.single 2 1)
    {ρ : d.Lm} (hρ4 : ρ ^ 4 = 1) (hρ2 : ρ ^ 2 ≠ 1) {x : Kˣ}
    (hρx : (ρ : GL (Fin 3) K) = mono 1 (aU 0 1 x)) : False := by
  have hρ2e : ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) = mono 1 (fun j => aU 0 1 x j * aU 0 1 x j) := by
    rw [Subgroup.coe_pow, sq, hρx, mono_one_mul]
  have hρ22 : ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) * ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) = 1 := by
    rw [← Subgroup.coe_mul, ← pow_add]
    show ((ρ ^ 4 : d.Lm) : GL (Fin 3) K) = 1
    rw [hρ4]
    rfl
  have hxx4 : (x * x) * (x * x) = 1 := by
    rw [hρ2e, mono_one_mul, ← mono_one] at hρ22
    have := congrFun (mono_injective hρ22).2 0
    simpa [aU_left] using this
  have hxx1 : x * x ≠ 1 := by
    intro h1
    apply hρ2
    apply Subtype.ext
    rw [hρ2e]
    show _ = ((1 : GL (Fin 3) K))
    rw [← mono_one]
    congr 1
    funext j
    fin_cases j
    · simpa [aU_left] using h1
    · have : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, h1, inv_one]
      simpa [aU_right (by decide : (0 : Fin 3) ≠ 1)] using this
    · simp [aU_other]
  have hxx : x * x = -1 := by
    have h3 : ((x : K) * x) * ((x : K) * x) = 1 := by
      have := congrArg Units.val hxx4
      simpa using this
    rcases mul_self_eq_one_iff.1 h3 with h | h
    · exact absurd (Units.ext (by simpa using h)) hxx1
    · exact Units.ext (by simpa using h)
  have hxinv : x⁻¹ = -x := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [mul_neg, hxx, neg_neg]
  have hxi : x⁻¹ * x⁻¹ = -1 := by
    rw [hxinv, neg_mul_neg, hxx]
  obtain ⟨N, hN⟩ : ∃ N : Fin 3 → Kˣ, N = fun j => if j = 2 then 1 else -1 := ⟨_, rfl⟩
  have hρ2N : ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) = mono 1 N := by
    rw [hρ2e, hN]
    congr 1
    funext j
    fin_cases j
    · simpa [aU_left] using hxx
    · simpa [aU_right (by decide : (0 : Fin 3) ≠ 1)] using hxi
    · simp [aU_other]
  have hsq : ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) * ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) = 1 := hρ22
  have hmod : ∀ w : Fin 3 → K, (((ρ ^ 2 : d.Lm) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w + w ∈
      Submodule.span K {d.c} := by
    intro w
    rw [hρ2N, mono_one_mulVec]
    refine mem_span_c_of_coord hμ hc ?_ ?_
    · simp [hN]
    · simp [hN]
  obtain ⟨y, hyX, σy, ay, hy, hσy⟩ := hm.trans 0 2
  have hv : y * ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) * y⁻¹ = mono 1 (fun j => N (σy⁻¹ j)) := by
    rw [hy, hρ2N, mono_mul_diag_mul_inv]
  have hstab : ∃ μ' : K, ((y * ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) * y⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ d.c = μ' • d.c := by
    refine ⟨((N (σy⁻¹ 2) : Kˣ) : K), ?_⟩
    rw [hv, hc, Matrix.mulVec_smul, mono_mulVec_single, Perm.one_apply, single_eq_smul, smul_comm]
  have hσ2 : σy⁻¹ 2 = 0 := by
    rw [Perm.inv_eq_iff_eq]
    exact hσy.symm
  obtain ⟨lam, hlam2, hE0, hE1⟩ : ∃ lam : Kˣ, lam * lam = -1 ∧
      N (σy⁻¹ 0) * (aU 0 1 x 0)⁻¹ = lam ∧ N (σy⁻¹ 1) * (aU 0 1 x 1)⁻¹ = lam := by
    rcases perm_zero_two σy hσy with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine ⟨x⁻¹, hxi, ?_, ?_⟩
      · rw [h0]
        simp [hN, aU_left]
      · rw [h1, aU_right (by decide : (0 : Fin 3) ≠ 1), inv_inv, hxinv]
        have hN1 : N 1 = -1 := by simp [hN]
        rw [hN1]
        simp
    · refine ⟨x, hxx, ?_, ?_⟩
      · rw [h0, aU_left, hxinv]
        simp [hN]
      · rw [h1, aU_right (by decide : (0 : Fin 3) ≠ 1)]
        simp [hN]
  have hE2 : N (σy⁻¹ 2) * (aU 0 1 x 2)⁻¹ = -1 := by
    rw [hσ2]
    simp [hN, aU_other]
  have hprod : y * ((ρ ^ 2 : d.Lm) : GL (Fin 3) K) * y⁻¹ * ((ρ : d.Lm) : GL (Fin 3) K)⁻¹ =
      mono 1 (fun j => N (σy⁻¹ j) * (aU 0 1 x j)⁻¹) := by
    rw [hv, hρx, mono_inv, mono_mul]
    exact congrArg₂ mono (by simp) (by funext j; simp)
  have hfin := hkU y hyX _ (ρ ^ 2 : d.Lm).2 hsq hmod hstab _ ρ.2 (lam : K) (by
    intro w
    rw [hprod, mono_one_mulVec]
    refine mem_span_c_of_coord hμ hc ?_ ?_
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hE0]
      ring
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hE1]
      ring)
  have hm1 : ((lam : K) * lam) = -1 := by
    have := congrArg Units.val hlam2
    simpa using this
  apply h2
  linear_combination hm1 - hfin

theorem frame_a_false (h2 : (2 : K) ≠ 0) {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X)
    (hc2 : ∃ μ : K, μ ≠ 0 ∧ d.c = μ • Pi.single 2 1)
    (hL2 : ∀ l ∈ d.Lm, ∃ σ a, l = mono σ a ∧ σ 2 = 2 ∧ a 2 = 1)
    (hcover : ∀ x : d.Lm, IsNCInv x → (x : GL (Fin 3) K) ∈ d.D)
    {ρ t₀ : d.Lm} (hg : DihGens d.Lm d.n ρ t₀)
    (hρ : HasPerm (ρ : GL (Fin 3) K) 1) (ht : HasPerm (t₀ : GL (Fin 3) K) (swap 0 1)) :
    False := by
  obtain ⟨μ, hμ, hc⟩ := hc2
  obtain ⟨-, at', hat, hat2⟩ := Lmono hL2 t₀ ht
  have hsq : (t₀ : GL (Fin 3) K) * t₀ = 1 := by
    have := congrArg Subtype.val hg.sq
    simpa using this
  rw [hat] at hsq
  have hat0 : at' 1 * at' 0 = 1 := by
    have := (mono_sq_eq_one hsq).2 0
    simpa using this
  have hat' : at' = aU 0 1 (at' 0) := aU_eq_of_swap01 hat2 hat0
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Kˣ, r₀ = at' 0 := ⟨_, rfl⟩
  rw [← hr₀] at hat'
  have ht_eq : (t₀ : GL (Fin 3) K) = aref 0 1 r₀ := by
    rw [hat, aref]
    exact congrArg (mono (swap 0 1)) hat'
  obtain ⟨-, aρ, hρa, hρ2⟩ := Lmono hL2 ρ hρ
  have hconj : (t₀ : GL (Fin 3) K) * ρ * (t₀ : GL (Fin 3) K)⁻¹ = (ρ : GL (Fin 3) K)⁻¹ := by
    have := congrArg Subtype.val hg.inv
    simpa using this
  rw [ht_eq, hρa, aref, mono_mul_diag_mul_inv, mono_inv] at hconj
  have hρ1 : aρ 1 = (aρ 0)⁻¹ := by
    have := congrFun (mono_injective hconj).2 0
    simpa using this
  obtain ⟨x, hx⟩ : ∃ x : Kˣ, x = aρ 0 := ⟨_, rfl⟩
  rw [← hx] at hρ1
  have hρaU : aρ = aU 0 1 x := by
    funext m
    fin_cases m
    · simp [aU, hx]
    · simpa [aU] using hρ1
    · simpa [aU] using hρ2
  rcases h.kHU with hkH | ⟨hn4, hkU⟩
  swap
  · have hρ4 : ρ ^ 4 = 1 := by rw [← hn4, ← hg.ord]; exact pow_orderOf_eq_one ρ
    have hρ2' : ρ ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hg.ord, hn4]; norm_num)
    exact frame_a_false_kU h2 hkU hm hμ hc hρ4 hρ2' (x := x) (by rw [hρa, hρaU])
  obtain ⟨y, hyX, σy, ay, hy, hσy⟩ := hm.trans 0 2
  obtain ⟨Dy, hDy⟩ : ∃ Dy : Fin 3 → Kˣ, ∀ j, Dy j = aρ (σy⁻¹ j) := ⟨_, fun _ => rfl⟩
  have hDy' : Dy = fun j => aρ (σy⁻¹ j) := funext hDy
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : GL (Fin 3) K, g₁ = y * (ρ : GL (Fin 3) K) * y⁻¹ := ⟨_, rfl⟩
  have hg1 : g₁ = mono 1 Dy := by
    rw [hg₁, hy, hρa, hDy']
    exact mono_mul_diag_mul_inv σy ay aρ
  have hg1X : g₁ ∈ d.X := by
    rw [hg₁]
    exact d.X.mul_mem (d.X.mul_mem hyX (h.Lle ρ.2)) (d.X.inv_mem hyX)
  have hstab : ∃ μ' : K, (g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c = μ' • d.c := by
    refine ⟨(Dy 2 : K), ?_⟩
    rw [hg1, hc, Matrix.mulVec_smul, mono_mulVec_single, Perm.one_apply, single_eq_smul,
      smul_comm]
  obtain ⟨u, hu, hq⟩ : ∃ u : Kˣ, (u = x ∨ u = x⁻¹) ∧ Dy 1 * r₀ * (Dy 0)⁻¹ = u * r₀ := by
    rcases perm_zero_two σy hσy with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine ⟨x⁻¹, Or.inr rfl, ?_⟩
      rw [hDy, hDy, h0, h1, hρ2, hρ1]
      simp
    · refine ⟨x, Or.inl rfl, ?_⟩
      rw [hDy, hDy, h0, h1, hρ2, hρ1]
      simp [mul_comm]
  have htD : (t₀ : GL (Fin 3) K) ∈ d.D := hcover t₀ ((hg.nc_iff t₀).mpr ⟨0, by simp⟩)
  have hs'L : g₁ * t₀ * g₁⁻¹ ∈ d.Lm := h.N g₁ hg1X hstab _ t₀.2
  have hs'D : g₁ * t₀ * g₁⁻¹ ∈ d.D := h.Dconj g₁ hg1X _ htD
  have hs'eq : g₁ * (t₀ : GL (Fin 3) K) * g₁⁻¹ = aref 0 1 (u * r₀) := by
    rw [hg1, ht_eq, diag_conj_aref (by decide : (0 : Fin 3) ≠ 1), hq]
  have hprod : (t₀ : GL (Fin 3) K) * aref 0 1 (u * r₀) = mono 1 (aU 0 1 u) := by
    rw [ht_eq, aref_mul_aref (by decide : (0 : Fin 3) ≠ 1)]
    refine congrArg (mono 1) (congrArg (aU 0 1) ?_)
    rw [mul_comm u r₀, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨ε, hε, hts⟩ : ∃ ε : ℤ, Odd ε ∧
      t₀ * (⟨g₁ * t₀ * g₁⁻¹, hs'L⟩ : d.Lm) = ρ ^ ε := by
    rcases hu with hux | hux
    · refine ⟨1, odd_one, Subtype.ext ?_⟩
      show (t₀ : GL (Fin 3) K) * (g₁ * (t₀ : GL (Fin 3) K) * g₁⁻¹) =
        ((ρ ^ (1 : ℤ) : d.Lm) : GL (Fin 3) K)
      rw [hs'eq, hprod, hux, zpow_one, hρa, hρaU]
    · refine ⟨-1, ⟨-1, by norm_num⟩, Subtype.ext ?_⟩
      show (t₀ : GL (Fin 3) K) * (g₁ * (t₀ : GL (Fin 3) K) * g₁⁻¹) =
        ((ρ ^ (-1 : ℤ) : d.Lm) : GL (Fin 3) K)
      rw [hs'eq, hprod, hux, Subgroup.coe_zpow, zpow_neg_one, hρa, hρaU, mono_aU_inv]
  have hs'₀ : (⟨g₁ * t₀ * g₁⁻¹, hs'L⟩ : d.Lm) = t₀ * ρ ^ ε := by
    rw [eq_inv_mul_of_mul_eq hts, hg.t0_inv]
  have hdiff : ∀ l ∈ d.Lm, l * (t₀ : GL (Fin 3) K) * l⁻¹ ≠ g₁ * t₀ * g₁⁻¹ := by
    intro l hl heq
    have hne := hg.not_conj 0 ε (by simpa using hε) ⟨l, hl⟩
    rw [zpow_zero, mul_one, ← hs'₀] at hne
    apply hne
    apply Subtype.ext
    simpa using heq
  exact hkH g₁ hg1X hstab t₀ htD _ hs'D t₀.2 hs'L hdiff rfl

end CFSG.RankThree.PartOne.N1322
