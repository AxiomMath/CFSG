module

public import CFSG.Timmesfeld.ARS.CaseHF4

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

theorem conj_commutatorElement (g a b : G) : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]
  [CharP F 2]

omit [CharP E 2] [CharP F 2] in
theorem d_conj_x4 (l : Fˣ) (z : F) : c.d l * c.x4 z * (c.d l)⁻¹ = c.x4 ((l : F) * l * z) := by
  rw [d, x4, x4, ← map_mul, ← map_inv, ← map_mul, diag3_mul_tv, mul_inv_cancel_right]
  congr 2
  simp [dvec]
  ring

omit [CharP E 2] [CharP F 2] in
theorem k_conj_x4 (μ : Eˣ) (z : F) : c.k μ * c.x4 z * (c.k μ)⁻¹ = c.x4 z := by
  rw [← Subgroup.mem_centralizer_iff.1 (c.k_mem_centralizer μ) _
    (Subgroup.mem_sup_left (c.x4_mem z)), mul_inv_cancel_right]

omit [CharP E 2] [CharP F 2] in
theorem conjSub_U5_k (μ : Eˣ) :
    conjSub (shortRoot R P' ⁅A₀, P⁆ A) (c.k μ) = shortRoot R P' ⁅A₀, P⁆ A := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_P'_k, c.conjSub_Q_k, c.conjSub_A_k]

omit [CharP F 2] in
theorem conj_nf {g : G} (hP' : conjSub P' g = P')
    (hU3 : conjSub (shortRoot R P ⁅A₀, P'⁆ A) g = shortRoot R P ⁅A₀, P'⁆ A)
    (hU5 : conjSub (shortRoot R P' ⁅A₀, P⁆ A) g = shortRoot R P' ⁅A₀, P⁆ A) {κ : F → F}
    (hA : ∀ z, g * c.x4 z * g⁻¹ = c.x4 (κ z)) (v : F) (r : E) (z : F) (w : E) :
    ∃ v' r' w', g * c.nf v r z w * g⁻¹ = c.nf v' r' (κ z) w' := by
  obtain ⟨v', hv'⟩ := c.x2_surjective (hP' ▸ conj_mem_conjSub g (c.x2_mem v))
  obtain ⟨r', hr'⟩ := c.x3_surjective (hU3 ▸ conj_mem_conjSub g (c.x3_mem r))
  obtain ⟨w', hw'⟩ := c.x5_surjective (hU5 ▸ conj_mem_conjSub g (c.x5_mem w))
  refine ⟨v', r', w', ?_⟩
  rw [nf, nf, y, y, hv', hr', hw', ← hA]
  group

theorem exists_comm16_eq (s : E) : ∃ z, ⁅c.x1 s, c.x6 1⁆ = c.nf (c.N s) (c.sharp s) z s := by
  have hH := commutator_mem_H S (c.x1_mem s) (c.x6_mem 1)
  obtain ⟨a, ha, hg⟩ := S.exists_eq_mul ⟨_, c.comm1_mem s⟩
  obtain ⟨z, rfl⟩ := c.x4_surjective ha
  obtain ⟨hp1, hp5⟩ := S.proj_H hH
  have hp1' : ((S.proj ⟨_, c.comm1_mem s⟩).1 : G) = 1 := by rw [hp1]; rfl
  have hp5' : ((S.proj ⟨_, c.comm1_mem s⟩).2.1 : G) = c.x5 s := hp5
  refine ⟨z + c.Tp (c.sharp s) s, ?_⟩
  have hg' : ⁅c.x1 s, c.x6 1⁆ = c.x5 s * c.x3 (c.sharp s) * c.x2 (c.N s) * c.x4 z := by
    rw [c.x3_sharp, c.x2_N]
    simpa only [hp1', hp5', one_mul, n2, n3] using hg
  rw [hg', nf, ← c.x5_mul_y, y, (c.commute_x2_x3 _ _).eq]
  group

@[expose] noncomputable def Nt (s : E) : F := Classical.choose (c.exists_comm16_eq s)

theorem comm16_eq (s : E) : ⁅c.x1 s, c.x6 1⁆ = c.nf (c.N s) (c.sharp s) (c.Nt s) s :=
  Classical.choose_spec (c.exists_comm16_eq s)

theorem polar_Nt (s₀ s : E) :
    c.Nt (s₀ + s) = c.Nt s + c.F4 s₀ s + c.Nt s₀ + c.Tp (c.sharp s₀) s := by
  have h : ⁅c.x1 (s₀ + s), c.x6 1⁆ =
      c.x1 s₀ * ⁅c.x1 s, c.x6 1⁆ * (c.x1 s₀)⁻¹ * ⁅c.x1 s₀, c.x6 1⁆ := by
    rw [c.x1_add]
    simp only [commutatorElement_def]
    group
  rw [c.comm16_eq, c.comm16_eq, c.comm16_eq, c.x1_conj_nf, c.nf_mul] at h
  exact (c.nf_injective h).2.2.1

theorem Nt_mul_sq [Finite F] (μ : Eˣ) (s : E) :
    c.Nt ((μ : E) * μ * s) = (c.nu μ)⁻¹ * (c.nu μ)⁻¹ * c.Nt s := by
  have := S.hyp.finite
  set l : Fˣ := (Units.mk0 (c.nu μ) (c.nu_ne_zero μ))⁻¹ with hl
  set g := c.d l * c.k μ with hg
  have hP' : conjSub P' g = P' := by
    rw [hg, conjSub_mul, c.conjSub_P'_k, c.conjSub_d _ c.hψP' l]
  have hU3 : conjSub (shortRoot R P ⁅A₀, P'⁆ A) g = shortRoot R P ⁅A₀, P'⁆ A := by
    rw [hg, conjSub_mul, c.conjSub_U3_k, c.conjSub_U3_d]
  have hU5 : conjSub (shortRoot R P' ⁅A₀, P⁆ A) g = shortRoot R P' ⁅A₀, P⁆ A := by
    rw [hg, conjSub_mul, c.conjSub_U5_k, c.conjSub_U5_d]
  have hA : ∀ z, g * c.x4 z * g⁻¹ = c.x4 ((l : F) * l * z) := fun z => by
    rw [hg, show c.d l * c.k μ * c.x4 z * (c.d l * c.k μ)⁻¹ =
      c.d l * (c.k μ * c.x4 z * (c.k μ)⁻¹) * (c.d l)⁻¹ by group, c.k_conj_x4, c.d_conj_x4]
  have h1 : g * c.x1 s * g⁻¹ = c.x1 ((μ : E) * μ * s) := by
    rw [hg, show c.d l * c.k μ * c.x1 s * (c.d l * c.k μ)⁻¹ =
      c.d l * (c.k μ * c.x1 s * (c.k μ)⁻¹) * (c.d l)⁻¹ by group, c.k_conj_x1, c.d_conj_x1]
  have h6 : g * c.x6 1 * g⁻¹ = c.x6 1 := by
    rw [hg, show c.d l * c.k μ * c.x6 1 * (c.d l * c.k μ)⁻¹ =
      c.d l * (c.k μ * c.x6 1 * (c.k μ)⁻¹) * (c.d l)⁻¹ by group, c.k_conj_x6, c.d_conj_x6, hl,
      Units.val_inv_eq_inv_val, Units.val_mk0, mul_one, inv_mul_cancel₀ (c.nu_ne_zero μ)]
  obtain ⟨v', r', w', h⟩ := c.conj_nf hP' hU3 hU5 hA (c.N s) (c.sharp s) (c.Nt s) s
  rw [← c.comm16_eq, conj_commutatorElement, h1, h6, c.comm16_eq] at h
  rw [(c.nf_injective h).2.2.1, hl, Units.val_inv_eq_inv_val, Units.val_mk0]

variable [Finite F] [Finite E] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))

include hτ0 hτ in
omit [Finite E] in
theorem N_mul_sq (μ : Eˣ) (s : E) :
    c.N ((μ : E) * μ * s) = (c.nu μ)⁻¹ * (c.nu μ)⁻¹ * c.N s := by
  have h := c.N_mul hτ ((μ : E) * μ) s
  have hμ : ((μ : E) * μ) ≠ 0 := mul_ne_zero μ.ne_zero μ.ne_zero
  rw [c.N_eq hτ hμ, show Units.mk0 ((μ : E) * μ) hμ = μ * μ from Units.ext rfl, c.nu_inv,
    c.nu_mul, mul_inv] at h
  exact mul_left_cancel₀ hτ0 (by rw [h]; ring)

include he hτ0 hτ in
theorem Nt_eq (hβ : ∀ s, c.beta s = s) (hna : ¬ ∀ x y : E, c.N (x + y) = c.N x + c.N y) (s : E) :
    c.Nt s = c.N s := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hadd : ∀ x y : E, c.Nt (x + y) + c.N (x + y) = (c.Nt x + c.N x) + (c.Nt y + c.N y) :=
    fun x y => by
      rw [c.polar_Nt, (c.F4_F3 hβ x y).1, c.Tp_eq e he, add_comm x y, c.polar_N e he]
      linear_combination (c.F2 y x + c.T y (c.sharp x)) * h2
  have hD0 : c.Nt 0 = 0 := by
    have := hadd 0 0
    rw [add_zero, c.N_zero, add_zero] at this
    linear_combination -this
  have hmul : ∀ (x t : E), c.Nt (x * t) + c.N (x * t) = τ⁻¹ * c.N x * (c.Nt t + c.N t) := by
    intro x t
    by_cases hx : x = 0
    · rw [hx, zero_mul, c.N_zero, mul_zero, zero_mul, hD0, add_zero]
    obtain ⟨μ, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq E 2) x
    have hμ : μ ≠ 0 := fun h => hx (by rw [h, mul_zero])
    have e1 := c.Nt_mul_sq (Units.mk0 μ hμ) t
    have e2 := c.N_mul_sq hτ0 hτ (Units.mk0 μ hμ) t
    have e3 := c.N_mul_sq hτ0 hτ (Units.mk0 μ hμ) 1
    simp only [Units.val_mk0, mul_one] at e1 e2 e3
    rw [e1, e2, e3, c.N_one hτ]
    have ht : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ0
    linear_combination (-((c.nu (Units.mk0 μ hμ))⁻¹ * (c.nu (Units.mk0 μ hμ))⁻¹) *
      (c.Nt t + c.N t)) * ht
  by_contra hne
  apply hna
  intro x y
  have hD : c.Nt s + c.N s ≠ 0 := fun h => hne (by linear_combination h - c.N s * h2)
  have k := hmul (x + y) s
  rw [add_mul, hadd, hmul x s, hmul y s] at k
  have k' : (τ⁻¹ * (c.Nt s + c.N s)) * (c.N (x + y) - (c.N x + c.N y)) = 0 := by
    linear_combination -k
  rcases mul_eq_zero.1 k' with h | h
  · exact absurd h (mul_ne_zero (inv_ne_zero hτ0) hD)
  · exact sub_eq_zero.1 h

include he hτ0 hτ in
theorem not_additive_N_G2 (hsq : ∀ s, c.sharp s = s ^ 2) {l : E} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    ¬ ∀ x y : E, c.N (x + y) = c.N x + c.N y := by
  intro hadd
  have hN := (c.G2_structure e he hτ0 hτ hsq).1
  have h := congrArg (fun z => e (τ⁻¹ * z)) (hadd 1 l)
  simp only [mul_add, map_add] at h
  rw [hN, hN, hN] at h
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have h3 : l * (l + 1) = 0 := by linear_combination h - (l + l ^ 2) * h2
  rcases mul_eq_zero.1 h3 with h | h
  · exact hl0 h
  · exact hl1 (by linear_combination h - h2)

include hτ0 hτ in
omit [Finite E] in
theorem card_le_of_additive_N (hadd : ∀ x y : E, c.N (x + y) = c.N x + c.N y) :
    Nat.card E ≤ Nat.card F := by
  let ν : E →+* F :=
    { toFun := fun x => τ⁻¹ * c.N x
      map_one' := by rw [c.N_one hτ, inv_mul_cancel₀ hτ0]
      map_mul' := fun x y => by
        have h := c.N_mul hτ x y
        calc τ⁻¹ * c.N (x * y) = τ⁻¹ * τ⁻¹ * (τ * c.N (x * y)) := by field_simp
          _ = τ⁻¹ * c.N x * (τ⁻¹ * c.N y) := by rw [h]; ring
      map_zero' := by rw [c.N_zero, mul_zero]
      map_add' := fun x y => by rw [hadd, mul_add] }
  exact Nat.card_le_card_of_injective ν ν.injective

include he in
omit [Finite F] [Finite E] in
theorem comm16_eq_nf (hNt : ∀ s, c.Nt s = c.N s) (s : E) (u : F) :
    ⁅c.x1 s, c.x6 u⁆ = c.nf (u * c.N s) (e u * c.sharp s) (u * u * c.N s) (e u * s) := by
  by_cases hu : u = 0
  · subst hu
    simp only [c.x6_zero, commutatorElement_one_right, zero_mul, map_zero, nf, y, c.x2_zero,
      c.x3_zero, c.x4_zero, c.x5_zero, one_mul]
  set l := Units.mk0 u hu with hl
  have h1 : c.d l * c.x1 s * (c.d l)⁻¹ = c.x1 s := c.d_conj_x1 l s
  have h6 : c.d l * c.x6 1 * (c.d l)⁻¹ = c.x6 u := by rw [c.d_conj_x6, hl, Units.val_mk0, mul_one]
  have h : c.d l * ⁅c.x1 s, c.x6 1⁆ * (c.d l)⁻¹ =
      c.d l * c.nf (c.N s) (c.sharp s) (c.Nt s) s * (c.d l)⁻¹ := by
    rw [c.comm16_eq]
  rw [conj_commutatorElement, h1, h6, hNt, nf, y] at h
  rw [h, nf, y, show c.d l * (c.x2 (c.N s) * c.x3 (c.sharp s) * c.x4 (c.N s) * c.x5 s) *
    (c.d l)⁻¹ = (c.d l * c.x2 (c.N s) * (c.d l)⁻¹) * (c.d l * c.x3 (c.sharp s) * (c.d l)⁻¹) *
      (c.d l * c.x4 (c.N s) * (c.d l)⁻¹) * (c.d l * c.x5 s * (c.d l)⁻¹) by group, c.d_conj_x2,
    c.d_conj_x3 e he, c.d_conj_x4, c.d_conj_x5 e he, hl, Units.val_mk0]

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
