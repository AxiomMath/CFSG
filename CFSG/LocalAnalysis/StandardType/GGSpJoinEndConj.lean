module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndAut
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.StandardType.SpJoin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]

private lemma spEnd_endNode_mul_self {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    (a * b * a) * (a * b * a) = 1 := by
  calc (a * b * a) * (a * b * a) = a * (b * (a * a) * b) * a := by group
    _ = a * (b * b) * a := by rw [ha, mul_one]
    _ = a * a := by rw [hb, mul_one]
    _ = 1 := ha

private lemma spEnd_conj_inv_of_conj {t x y : G} (ht : t * t = 1) (h : t * x * t⁻¹ = y) :
    t * y * t⁻¹ = x := by
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hsq : t⁻¹ * t⁻¹ = 1 := by rw [hinv, ht]
  calc t * y * t⁻¹ = t * (t * x * t⁻¹) * t⁻¹ := by rw [h]
    _ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = x := by rw [ht, hsq]; group

private lemma spEnd_mul_eq_of_mul_inv {t x y : G} (ht : t * t = 1) (h : t * x * t⁻¹ = y) :
    t * x * t = y := by
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  calc t * x * t = t * x * t⁻¹ := by rw [hinv]
    _ = y := h

private lemma spEnd_mul_eq_mul_of_conj {t x y : G} (ht : t * t = 1) (h : t * x * t⁻¹ = y) :
    t * x = y * t := by
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  calc t * x = t * x * 1 := by rw [mul_one]
    _ = t * x * (t⁻¹ * t) := by rw [inv_mul_cancel]
    _ = (t * x * t⁻¹) * t := by group
    _ = y * t := by rw [h]

private lemma spEnd_conj_eq_of_commute {p q : G} (h : p * q = q * p) : p * q * p⁻¹ = q := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private lemma spEnd_conj_chain {a b X Y Z W : G} (hT : (a * b * a) * (a * b * a) = 1)
    (h1 : a * X * a = Y) (h2 : b * Y * b = Z) (h3 : a * Z * a = W) :
    (a * b * a) * X * (a * b * a)⁻¹ = W := by
  have hinv : (a * b * a)⁻¹ = a * b * a := inv_eq_of_mul_eq_one_right hT
  rw [hinv]
  calc (a * b * a) * X * (a * b * a) = a * b * (a * X * a) * b * a := by group
    _ = a * b * Y * b * a := by rw [h1]
    _ = a * (b * Y * b) * a := by group
    _ = a * Z * a := by rw [h2]
    _ = W := h3

private lemma spEnd_sq_mul_commute_of_conj {t u x : G} (ht : t * t = 1)
    (hu : t * u * t⁻¹ = u) (hx : t * x * t⁻¹ = u * x * u⁻¹) :
    (u * u) * x = x * (u * u) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h2 : t⁻¹ * (t * x * t⁻¹) * t = (t⁻¹ * u * t) * (t⁻¹ * x * t) * (t⁻¹ * u * t)⁻¹ := by
    rw [hx]; group
  have h3 : t⁻¹ * u * t = u := by
    rw [htinv]
    exact spEnd_mul_eq_of_mul_inv ht hu
  have h4 : t⁻¹ * x * t = u * x * u⁻¹ := by
    rw [htinv]
    rw [htinv] at hx
    exact hx
  have key : x = u * (u * x * u⁻¹) * u⁻¹ := by
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = (t⁻¹ * u * t) * (t⁻¹ * x * t) * (t⁻¹ * u * t)⁻¹ := h2
      _ = u * (u * x * u⁻¹) * u⁻¹ := by rw [h3, h4]
  have step1 : x * u = u * (u * x * u⁻¹) := by
    conv_lhs => rw [key]
    group
  have step2 : x * (u * u) = (u * u) * x := by
    calc x * (u * u) = (x * u) * u := by group
      _ = (u * (u * x * u⁻¹)) * u := by rw [step1]
      _ = (u * u) * x := by group
  exact step2.symm

private lemma spEnd_eq_one_of_commute_all {r : ℕ} [NeZero r]
    {x : SpecialLinearGroup (Fin 2) F}
    (hx : ∀ y : StatedSp r F, lam (0 : Fin r) x * y = y * lam (0 : Fin r) x) : x = 1 := by
  have hcen : lam (0 : Fin r) x ∈ Subgroup.center (StatedSp r F) :=
    Subgroup.mem_center_iff.mpr fun y => (hx y).symm
  have hbot : lam (0 : Fin r) x = 1 := by
    have hcenter : Subgroup.center (StatedSp r F) = ⊥ := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq r F,
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    rw [hcenter] at hcen
    exact Subgroup.mem_bot.mp hcen
  exact lam_injective (0 : Fin r) (by rw [hbot, map_one])

private lemma spEnd_lam_one_eq_levi (k : ℕ) (x : SpecialLinearGroup (Fin 2) F) :
    lam (1 : Fin (k + 2 + 1)) x = spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) x) := by
  rw [spLeviBlock_lam]; rfl

private lemma spEnd_eq_one_of_lam_one_centralizes_levi {k : ℕ}
    {x : SpecialLinearGroup (Fin 2) F}
    (hx : ∀ h : StatedSp (k + 2) F, lam (1 : Fin (k + 2 + 1)) x * spLeviBlock (k + 2) F h =
      spLeviBlock (k + 2) F h * lam (1 : Fin (k + 2 + 1)) x) : x = 1 := by
  have hlam := spEnd_lam_one_eq_levi k x
  apply spEnd_eq_one_of_commute_all (r := k + 2)
  intro y
  have h := hx y
  rw [hlam, ← map_mul, ← map_mul] at h
  exact spLeviBlock_injective h

private lemma spEnd_n0_lam_zero {k : ℕ} (h2 : (2 : F) = 0) (g : SpecialLinearGroup (Fin 2) F) :
    weylRep (k + 2 + 1) F 0 * lam (0 : Fin (k + 2 + 1)) g * weylRep (k + 2 + 1) F 0 =
      lam (1 : Fin (k + 2 + 1)) g :=
  spEnd_mul_eq_of_mul_inv
    (spWeylRep_mul_self (k + 2 + 1) h2 (0 : Fin (k + 2 + 1)))
    (weylRep_conj_lam_swap h2 (0 : Fin (k + 2 + 1)) (by simp) g)

private lemma spEnd_n0_lam_one {k : ℕ} (h2 : (2 : F) = 0) (g : SpecialLinearGroup (Fin 2) F) :
    weylRep (k + 2 + 1) F 0 * lam (1 : Fin (k + 2 + 1)) g * weylRep (k + 2 + 1) F 0 =
      lam (0 : Fin (k + 2 + 1)) g := by
  have hsq : weylRep (k + 2 + 1) F 0 * weylRep (k + 2 + 1) F 0 = 1 :=
    spWeylRep_mul_self (k + 2 + 1) h2 (0 : Fin (k + 2 + 1))
  have hs0 := spEnd_n0_lam_zero (k := k) h2 g
  have key : weylRep (k + 2 + 1) F 0 *
      (weylRep (k + 2 + 1) F 0 * lam (0 : Fin (k + 2 + 1)) g * weylRep (k + 2 + 1) F 0) *
        weylRep (k + 2 + 1) F 0 = lam (0 : Fin (k + 2 + 1)) g := by
    calc weylRep (k + 2 + 1) F 0 *
        (weylRep (k + 2 + 1) F 0 * lam (0 : Fin (k + 2 + 1)) g * weylRep (k + 2 + 1) F 0) *
          weylRep (k + 2 + 1) F 0
        = (weylRep (k + 2 + 1) F 0 * weylRep (k + 2 + 1) F 0) *
            lam (0 : Fin (k + 2 + 1)) g *
              (weylRep (k + 2 + 1) F 0 * weylRep (k + 2 + 1) F 0) := by group
      _ = lam (0 : Fin (k + 2 + 1)) g := by rw [hsq]; group
  calc weylRep (k + 2 + 1) F 0 * lam (1 : Fin (k + 2 + 1)) g * weylRep (k + 2 + 1) F 0
      = weylRep (k + 2 + 1) F 0 *
          (weylRep (k + 2 + 1) F 0 * lam (0 : Fin (k + 2 + 1)) g * weylRep (k + 2 + 1) F 0) *
            weylRep (k + 2 + 1) F 0 := by rw [hs0]
    _ = lam (0 : Fin (k + 2 + 1)) g := key

private lemma spEnd_n0_lam_zero_inv {k : ℕ} (h2 : (2 : F) = 0) (g : SpecialLinearGroup (Fin 2) F) :
    weylRep (k + 2 + 1) F 0 * (lam (0 : Fin (k + 2 + 1)) g)⁻¹ * weylRep (k + 2 + 1) F 0 =
      lam (1 : Fin (k + 2 + 1)) (g⁻¹) := by
  have h := spEnd_mul_eq_of_mul_inv
    (spWeylRep_mul_self (k + 2 + 1) h2 (0 : Fin (k + 2 + 1)))
    (weylRep_conj_lam_swap h2 (0 : Fin (k + 2 + 1)) (by simp) (g⁻¹))
  rw [map_inv] at h
  exact h

theorem spEnd_endNode_of_range_conj {m : ℕ} (hm : 3 ≤ m)
    (φ₁ φ₂ : StatedSp (m + 1) F →* G) (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    (hβ : ∀ h : StatedSp m F, φ₁ (spLeviBlock m F h) = φ₂ (spLeviBlock m F h))
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {T : G}
    (hT : T = φ₁ (weylRep (m + 1) F 0) * φ₂ (weylRep (m + 1) F 0) * φ₁ (weylRep (m + 1) F 0))
    (hrange : φ₁.range.map (MulAut.conj T).toMonoidHom = φ₂.range)
    (hyK : ∀ w, φ₁ (lam (0 : Fin (m + 1)) g) * φ₂ w = φ₂ w * φ₁ (lam (0 : Fin (m + 1)) g))
    (hxa : φ₁ (weylRep (m + 1) F 0) * φ₂ (lam (0 : Fin (m + 1)) g) =
      φ₂ (lam (0 : Fin (m + 1)) g) * φ₁ (weylRep (m + 1) F 0)) :
    (∀ w, T * φ₁ w * T⁻¹ = φ₂ w) ∧ GGSpEndNode φ₁ T := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 1 ≤ k := by omega
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  subst hT
  set a : G := φ₁ (weylRep (k + 2 + 1) F 0) with ha
  set b : G := φ₂ (weylRep (k + 2 + 1) F 0) with hb
  have haa : a * a = 1 := by
    rw [ha, ← map_mul, spWeylRep_mul_self (k + 2 + 1) h2 (0 : Fin (k + 2 + 1)), map_one]
  have hbb : b * b = 1 := by
    rw [hb, ← map_mul, spWeylRep_mul_self (k + 2 + 1) h2 (0 : Fin (k + 2 + 1)), map_one]
  have hTT : (a * b * a) * (a * b * a) = 1 := spEnd_endNode_mul_self haa hbb
  have hlam1 : ∀ x : SpecialLinearGroup (Fin 2) F,
      lam (1 : Fin (k + 2 + 1)) x = spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) x) :=
    fun x => spEnd_lam_one_eq_levi k x
  have hβ1 : ∀ x : SpecialLinearGroup (Fin 2) F,
      φ₁ (lam (1 : Fin (k + 2 + 1)) x) = φ₂ (lam (1 : Fin (k + 2 + 1)) x) := by
    intro x
    have h := hβ (lam (0 : Fin (k + 2)) x)
    rwa [spLeviBlock_lam] at h
  have hlevi : ∀ h : StatedSp (k + 1) F,
      (a * b * a) * φ₁ (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) * (a * b * a)⁻¹ =
        φ₂ (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) := by
    intro h
    set W : StatedSp (k + 2 + 1) F := spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) with hW
    have hWφ : φ₁ W = φ₂ W := hβ (spLeviBlock (k + 1) F h)
    have hc : weylRep (k + 2 + 1) F 0 * W = W * weylRep (k + 2 + 1) F 0 :=
      spEnd_commute_weylRep_zero_levi_two (k := k) h
    have haW : a * φ₁ W = φ₁ W * a := by
      simp only [ha, ← map_mul, hc]
    have hbW : b * φ₂ W = φ₂ W * b := by
      simp only [hb, ← map_mul, hc]
    have h1 : a * φ₁ W * a = φ₁ W := by rw [haW, mul_assoc, haa, mul_one]
    have h1' : b * φ₂ W * b = φ₂ W := by rw [hbW, mul_assoc, hbb, mul_one]
    have h2 : b * φ₁ W * b = φ₁ W := by rw [hWφ]; exact h1'
    calc (a * b * a) * φ₁ W * (a * b * a)⁻¹ = φ₁ W := spEnd_conj_chain hTT h1 h2 h1
      _ = φ₂ W := hWφ
  have hs0 : weylRep (k + 2 + 1) F 0 * lam (0 : Fin (k + 2 + 1)) g *
      weylRep (k + 2 + 1) F 0 = lam (1 : Fin (k + 2 + 1)) g := spEnd_n0_lam_zero h2 g
  have hs1 : weylRep (k + 2 + 1) F 0 * lam (1 : Fin (k + 2 + 1)) g *
      weylRep (k + 2 + 1) F 0 = lam (0 : Fin (k + 2 + 1)) g := spEnd_n0_lam_one h2 g
  have hfam0 : (a * b * a) * φ₁ (lam (0 : Fin (k + 2 + 1)) g) * (a * b * a)⁻¹ =
      φ₂ (lam (0 : Fin (k + 2 + 1)) g) := by
    have hstep1 : a * φ₁ (lam (0 : Fin (k + 2 + 1)) g) * a = φ₁ (lam (1 : Fin (k + 2 + 1)) g) := by
      simp only [ha, ← map_mul, hs0]
    have hstep2 : b * φ₁ (lam (1 : Fin (k + 2 + 1)) g) * b = φ₂ (lam (0 : Fin (k + 2 + 1)) g) := by
      simp only [hβ1 g, hb, ← map_mul, hs1]
    have hstep3 : a * φ₂ (lam (0 : Fin (k + 2 + 1)) g) * a = φ₂ (lam (0 : Fin (k + 2 + 1)) g) := by
      rw [hxa, mul_assoc, haa, mul_one]
    exact spEnd_conj_chain hTT hstep1 hstep2 hstep3
  have hfam1 : (a * b * a) * φ₁ (lam (1 : Fin (k + 2 + 1)) g) * (a * b * a)⁻¹ =
      φ₂ (lam (1 : Fin (k + 2 + 1)) g) := by
    have hstepA : a * φ₁ (lam (1 : Fin (k + 2 + 1)) g) * a = φ₁ (lam (0 : Fin (k + 2 + 1)) g) := by
      simp only [ha, ← map_mul, hs1]
    have hstepB : b * φ₁ (lam (0 : Fin (k + 2 + 1)) g) * b = φ₁ (lam (0 : Fin (k + 2 + 1)) g) := by
      have hcomm : b * φ₁ (lam (0 : Fin (k + 2 + 1)) g) = φ₁ (lam (0 : Fin (k + 2 + 1)) g) * b := by
        rw [hb]
        exact (hyK (weylRep (k + 2 + 1) F 0)).symm
      rw [hcomm, mul_assoc, hbb, mul_one]
    have hstepC : a * φ₁ (lam (0 : Fin (k + 2 + 1)) g) * a = φ₁ (lam (1 : Fin (k + 2 + 1)) g) := by
      simp only [ha, ← map_mul, hs0]
    calc (a * b * a) * φ₁ (lam (1 : Fin (k + 2 + 1)) g) * (a * b * a)⁻¹ = φ₁ (lam (1 : Fin (k + 2 + 1)) g) :=
          spEnd_conj_chain hTT hstepA hstepB hstepC
      _ = φ₂ (lam (1 : Fin (k + 2 + 1)) g) := hβ1 g
  let ρ : StatedSp (k + 2 + 1) F →* G := (MulAut.conj (a * b * a)).toMonoidHom.comp φ₁
  have hρ : Function.Injective ρ := (MulAut.conj (a * b * a)).injective.comp hφ₁
  have hρrange : ρ.range = φ₁.range.map (MulAut.conj (a * b * a)).toMonoidHom := by
    rw [show ρ = (MulAut.conj (a * b * a)).toMonoidHom.comp φ₁ from rfl, MonoidHom.range_comp]
  have h0 : ρ (lam (0 : Fin (k + 2 + 1)) g) = φ₂ (lam (0 : Fin (k + 2 + 1)) g) := hfam0
  have h1 : ρ (lam (1 : Fin (k + 2 + 1)) g) = φ₂ (lam (1 : Fin (k + 2 + 1)) g) := hfam1
  have hM : ∀ h : StatedSp (k + 1) F,
      ρ (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) =
        φ₂ (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) := fun h => hlevi h
  obtain ⟨s, t, hsg, htg, hall⟩ :=
    spEnd_exists_conj_lam_lam_of_embeddings (k := k) hk ρ φ₂ hρ hφ₂
      (by rw [hρrange]; exact hrange) htr h0 h1 hM
  have hconj : ∀ w : StatedSp (k + 2 + 1) F,
      (a * b * a) * φ₁ w * (a * b * a)⁻¹ =
        φ₂ ((lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t) * w *
          (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t)⁻¹) := fun w => hall w
  set u : G := φ₁ (lam (1 : Fin (k + 2 + 1)) t) with hu_def
  have hu_levi : φ₁ (spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) t)) = u := by
    rw [spLeviBlock_lam]; rfl
  have hcW : ∀ h : StatedSp (k + 2) F,
      (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t) * spLeviBlock (k + 2) F h *
        (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t)⁻¹ =
      spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) t * h * (lam (0 : Fin (k + 2)) t)⁻¹) := by
    intro h
    have hst : Commute (lam (0 : Fin (k + 2 + 1)) s) (lam (1 : Fin (k + 2 + 1)) t) := by
      have h0' := lam_zero_commute_spLeviBlock (m := k + 2) s (lam (0 : Fin (k + 2)) t)
      rwa [spLeviBlock_lam] at h0'
    have hsW : Commute (lam (0 : Fin (k + 2 + 1)) s) (spLeviBlock (k + 2) F h) :=
      lam_zero_commute_spLeviBlock (m := k + 2) s h
    have hprod : Commute (lam (0 : Fin (k + 2 + 1)) s)
        (lam (1 : Fin (k + 2 + 1)) t * spLeviBlock (k + 2) F h *
          (lam (1 : Fin (k + 2 + 1)) t)⁻¹) :=
      (hst.mul_right hsW).mul_right hst.inv_right
    calc (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t) * spLeviBlock (k + 2) F h *
          (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t)⁻¹
        = lam (0 : Fin (k + 2 + 1)) s *
            (lam (1 : Fin (k + 2 + 1)) t * spLeviBlock (k + 2) F h *
              (lam (1 : Fin (k + 2 + 1)) t)⁻¹) * (lam (0 : Fin (k + 2 + 1)) s)⁻¹ := by group
      _ = lam (1 : Fin (k + 2 + 1)) t * spLeviBlock (k + 2) F h *
            (lam (1 : Fin (k + 2 + 1)) t)⁻¹ := spEnd_conj_eq_of_commute hprod.eq
      _ = spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) t * h * (lam (0 : Fin (k + 2)) t)⁻¹) := by
            simp only [hlam1, ← map_mul, ← map_inv]
  have hstep1 : ∀ h : StatedSp (k + 2) F,
      (a * b * a) * φ₁ (spLeviBlock (k + 2) F h) * (a * b * a)⁻¹ =
        u * φ₁ (spLeviBlock (k + 2) F h) * u⁻¹ := by
    intro h
    calc (a * b * a) * φ₁ (spLeviBlock (k + 2) F h) * (a * b * a)⁻¹
        = φ₂ ((lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t) *
            spLeviBlock (k + 2) F h *
              (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t)⁻¹) := hconj _
      _ = φ₂ (spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) t * h * (lam (0 : Fin (k + 2)) t)⁻¹)) := by
            rw [hcW h]
      _ = φ₁ (spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) t * h * (lam (0 : Fin (k + 2)) t)⁻¹)) :=
            (hβ _).symm
      _ = φ₁ (lam (1 : Fin (k + 2 + 1)) t * spLeviBlock (k + 2) F h *
              (lam (1 : Fin (k + 2 + 1)) t)⁻¹) := by
            simp only [hlam1, ← map_mul, ← map_inv]
      _ = u * φ₁ (spLeviBlock (k + 2) F h) * u⁻¹ := by
            rw [hu_def]
            calc φ₁ (lam (1 : Fin (k + 2 + 1)) t * spLeviBlock (k + 2) F h *
                  (lam (1 : Fin (k + 2 + 1)) t)⁻¹)
                = φ₁ (lam (1 : Fin (k + 2 + 1)) t * spLeviBlock (k + 2) F h) *
                    φ₁ ((lam (1 : Fin (k + 2 + 1)) t)⁻¹) := map_mul _ _ _
              _ = (φ₁ (lam (1 : Fin (k + 2 + 1)) t) * φ₁ (spLeviBlock (k + 2) F h)) *
                    φ₁ ((lam (1 : Fin (k + 2 + 1)) t)⁻¹) := by rw [map_mul]
              _ = (φ₁ (lam (1 : Fin (k + 2 + 1)) t) * φ₁ (spLeviBlock (k + 2) F h)) *
                    (φ₁ (lam (1 : Fin (k + 2 + 1)) t))⁻¹ := by rw [map_inv]
  have hu : (a * b * a) * u * (a * b * a)⁻¹ = u := by
    have h := hstep1 (lam (0 : Fin (k + 2)) t)
    rw [hu_levi] at h
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using h
  have hcomm : ∀ h : StatedSp (k + 2) F,
      (u * u) * φ₁ (spLeviBlock (k + 2) F h) = φ₁ (spLeviBlock (k + 2) F h) * (u * u) := fun h =>
    spEnd_sq_mul_commute_of_conj hTT hu (hstep1 h)
  have ht2 : t * t = 1 := by
    have hu2 : u * u = φ₁ (spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) (t * t))) := by
      rw [hu_def]
      calc φ₁ (lam (1 : Fin (k + 2 + 1)) t) * φ₁ (lam (1 : Fin (k + 2 + 1)) t)
          = φ₁ (lam (1 : Fin (k + 2 + 1)) t * lam (1 : Fin (k + 2 + 1)) t) := by rw [map_mul]
        _ = φ₁ (lam (1 : Fin (k + 2 + 1)) (t * t)) := by rw [← map_mul]
        _ = φ₁ (spLeviBlock (k + 2) F (lam (0 : Fin (k + 2)) (t * t))) := by
            rw [spEnd_lam_one_eq_levi]
    have hcenter : ∀ h : StatedSp (k + 2) F,
        lam (0 : Fin (k + 2)) (t * t) * h = h * lam (0 : Fin (k + 2)) (t * t) := by
      intro h
      have h1 := hcomm h
      simp only [hu2, ← map_mul] at h1
      exact spLeviBlock_injective (hφ₁ h1)
    exact spEnd_eq_one_of_commute_all hcenter
  have ht1 : t = 1 := spEnd_eq_one_of_mul_self_of_commute htr htg ht2
  have hall1 : ∀ w : StatedSp (k + 2 + 1) F,
      (a * b * a) * φ₁ w * (a * b * a)⁻¹ =
        φ₂ (lam (0 : Fin (k + 2 + 1)) s * w * (lam (0 : Fin (k + 2 + 1)) s)⁻¹) := by
    intro w
    have h := hconj w
    simpa only [ht1, map_one, one_mul, inv_one, mul_one] using h
  have hsecond : ∀ w : StatedSp (k + 2 + 1) F,
      (a * b * a) * φ₂ w * (a * b * a)⁻¹ =
        φ₁ ((lam (0 : Fin (k + 2 + 1)) s)⁻¹ * w * lam (0 : Fin (k + 2 + 1)) s) := by
    intro w
    have h := hall1 ((lam (0 : Fin (k + 2 + 1)) s)⁻¹ * w * lam (0 : Fin (k + 2 + 1)) s)
    have hw : lam (0 : Fin (k + 2 + 1)) s *
        ((lam (0 : Fin (k + 2 + 1)) s)⁻¹ * w * lam (0 : Fin (k + 2 + 1)) s) *
          (lam (0 : Fin (k + 2 + 1)) s)⁻¹ = w := by group
    rw [hw] at h
    exact spEnd_conj_inv_of_conj hTT h
  have hU1 : (a * b)^3 = φ₂ (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) (s⁻¹)) := by
    have hinv : (a * b * a)⁻¹ = a * b * a := inv_eq_of_mul_eq_one_right hTT
    have hp : (a * b)^3 = a * b * a * b * a * b := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
      group
    have e : (a * b)^3 = (a * b * a) * a * (a * b * a)⁻¹ * b := by
      rw [hinv, hp]
      rw [show (a * b * a) * a * (a * b * a) * b = a * b * a * (a * a) * b * a * b from by group, haa]
      group
    have hsswap : weylRep (k + 2 + 1) F 0 * (lam (0 : Fin (k + 2 + 1)) s)⁻¹ *
        weylRep (k + 2 + 1) F 0 = lam (1 : Fin (k + 2 + 1)) (s⁻¹) :=
      spEnd_n0_lam_zero_inv h2 s
    rw [e]
    change (a * b * a) * φ₁ (weylRep (k + 2 + 1) F 0) * (a * b * a)⁻¹ * b =
      φ₂ (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) (s⁻¹))
    rw [hall1 (weylRep (k + 2 + 1) F 0), hb, ← map_mul]
    congr 1
    calc (lam (0 : Fin (k + 2 + 1)) s) * weylRep (k + 2 + 1) F 0 *
          (lam (0 : Fin (k + 2 + 1)) s)⁻¹ * weylRep (k + 2 + 1) F 0
        = (lam (0 : Fin (k + 2 + 1)) s) *
            (weylRep (k + 2 + 1) F 0 * (lam (0 : Fin (k + 2 + 1)) s)⁻¹ *
              weylRep (k + 2 + 1) F 0) := by group
      _ = (lam (0 : Fin (k + 2 + 1)) s) * (lam (1 : Fin (k + 2 + 1)) (s⁻¹)) := by rw [hsswap]
  have hU2 : (a * b)^3 =
      φ₁ ((lam (0 : Fin (k + 2 + 1)) s)⁻¹ * lam (1 : Fin (k + 2 + 1)) s) := by
    have hinv : (a * b * a)⁻¹ = a * b * a := inv_eq_of_mul_eq_one_right hTT
    have hp : (a * b)^3 = a * b * a * b * a * b := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
      group
    have e : (a * b)^3 = (a * b * a) * b * (a * b * a)⁻¹ * a := by
      rw [hinv, hp]
      rw [show (a * b * a) * b * (a * b * a) * a = (a * b) * (a * b) * (a * b) * (a * a) from by group, haa]
      group
    have hs2 : weylRep (k + 2 + 1) F 0 * lam (0 : Fin (k + 2 + 1)) s *
        weylRep (k + 2 + 1) F 0 = lam (1 : Fin (k + 2 + 1)) s := spEnd_n0_lam_zero h2 s
    rw [e]
    change (a * b * a) * φ₂ (weylRep (k + 2 + 1) F 0) * (a * b * a)⁻¹ * a =
      φ₁ ((lam (0 : Fin (k + 2 + 1)) s)⁻¹ * lam (1 : Fin (k + 2 + 1)) s)
    rw [hsecond (weylRep (k + 2 + 1) F 0), ha, ← map_mul]
    congr 1
    calc (lam (0 : Fin (k + 2 + 1)) s)⁻¹ * weylRep (k + 2 + 1) F 0 *
          lam (0 : Fin (k + 2 + 1)) s * weylRep (k + 2 + 1) F 0
        = (lam (0 : Fin (k + 2 + 1)) s)⁻¹ *
            (weylRep (k + 2 + 1) F 0 * lam (0 : Fin (k + 2 + 1)) s *
              weylRep (k + 2 + 1) F 0) := by group
      _ = (lam (0 : Fin (k + 2 + 1)) s)⁻¹ * lam (1 : Fin (k + 2 + 1)) s := by rw [hs2]
  have hAB : φ₁ (lam (1 : Fin (k + 2 + 1)) (s * s)) =
      φ₁ (lam (0 : Fin (k + 2 + 1)) s) * φ₂ (lam (0 : Fin (k + 2 + 1)) s) := by
    have h := hU1.symm.trans hU2
    simp only [map_mul, map_inv] at h
    rw [← hβ1 s] at h
    have h2' : φ₂ (lam (0 : Fin (k + 2 + 1)) s) =
        (φ₁ (lam (0 : Fin (k + 2 + 1)) s))⁻¹ * φ₁ (lam (1 : Fin (k + 2 + 1)) s) *
          φ₁ (lam (1 : Fin (k + 2 + 1)) s) := by
      have hc := congrArg (fun z => z * φ₁ (lam (1 : Fin (k + 2 + 1)) s)) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hc
    have hmul : φ₁ (lam (1 : Fin (k + 2 + 1)) (s * s)) =
        φ₁ (lam (1 : Fin (k + 2 + 1)) s) * φ₁ (lam (1 : Fin (k + 2 + 1)) s) := by
      rw [← map_mul, ← map_mul]
    rw [h2', hmul]
    group
  have hs2 : s * s = 1 := by
    apply spEnd_eq_one_of_lam_one_centralizes_levi (k := k)
    intro h
    apply hφ₁
    have hAs : φ₁ (lam (0 : Fin (k + 2 + 1)) s) * φ₁ (spLeviBlock (k + 2) F h) =
        φ₁ (spLeviBlock (k + 2) F h) * φ₁ (lam (0 : Fin (k + 2 + 1)) s) := by
      calc φ₁ (lam (0 : Fin (k + 2 + 1)) s) * φ₁ (spLeviBlock (k + 2) F h)
          = φ₁ (lam (0 : Fin (k + 2 + 1)) s * spLeviBlock (k + 2) F h) := (map_mul _ _ _).symm
        _ = φ₁ (spLeviBlock (k + 2) F h * lam (0 : Fin (k + 2 + 1)) s) := by
            rw [(lam_zero_commute_spLeviBlock (m := k + 2) s h).eq]
        _ = φ₁ (spLeviBlock (k + 2) F h) * φ₁ (lam (0 : Fin (k + 2 + 1)) s) := map_mul _ _ _
    have hBs : φ₂ (lam (0 : Fin (k + 2 + 1)) s) * φ₁ (spLeviBlock (k + 2) F h) =
        φ₁ (spLeviBlock (k + 2) F h) * φ₂ (lam (0 : Fin (k + 2 + 1)) s) := by
      rw [hβ h]
      calc φ₂ (lam (0 : Fin (k + 2 + 1)) s) * φ₂ (spLeviBlock (k + 2) F h)
          = φ₂ (lam (0 : Fin (k + 2 + 1)) s * spLeviBlock (k + 2) F h) := (map_mul _ _ _).symm
        _ = φ₂ (spLeviBlock (k + 2) F h * lam (0 : Fin (k + 2 + 1)) s) := by
            rw [(lam_zero_commute_spLeviBlock (m := k + 2) s h).eq]
        _ = φ₂ (spLeviBlock (k + 2) F h) * φ₂ (lam (0 : Fin (k + 2 + 1)) s) := map_mul _ _ _
    calc φ₁ (lam (1 : Fin (k + 2 + 1)) (s * s) * spLeviBlock (k + 2) F h)
        = φ₁ (lam (1 : Fin (k + 2 + 1)) (s * s)) * φ₁ (spLeviBlock (k + 2) F h) := map_mul _ _ _
      _ = (φ₁ (lam (0 : Fin (k + 2 + 1)) s) * φ₂ (lam (0 : Fin (k + 2 + 1)) s)) *
            φ₁ (spLeviBlock (k + 2) F h) := by rw [hAB]
      _ = φ₁ (lam (0 : Fin (k + 2 + 1)) s) *
            (φ₂ (lam (0 : Fin (k + 2 + 1)) s) * φ₁ (spLeviBlock (k + 2) F h)) := by group
      _ = φ₁ (lam (0 : Fin (k + 2 + 1)) s) *
            (φ₁ (spLeviBlock (k + 2) F h) * φ₂ (lam (0 : Fin (k + 2 + 1)) s)) := by rw [hBs]
      _ = (φ₁ (lam (0 : Fin (k + 2 + 1)) s) * φ₁ (spLeviBlock (k + 2) F h)) *
            φ₂ (lam (0 : Fin (k + 2 + 1)) s) := by group
      _ = (φ₁ (spLeviBlock (k + 2) F h) * φ₁ (lam (0 : Fin (k + 2 + 1)) s)) *
            φ₂ (lam (0 : Fin (k + 2 + 1)) s) := by rw [hAs]
      _ = φ₁ (spLeviBlock (k + 2) F h) *
            (φ₁ (lam (0 : Fin (k + 2 + 1)) s) * φ₂ (lam (0 : Fin (k + 2 + 1)) s)) := by group
      _ = φ₁ (spLeviBlock (k + 2) F h) * φ₁ (lam (1 : Fin (k + 2 + 1)) (s * s)) := by rw [hAB]
      _ = φ₁ (spLeviBlock (k + 2) F h * lam (1 : Fin (k + 2 + 1)) (s * s)) :=
            (map_mul _ _ _).symm
  have hs1 : s = 1 := spEnd_eq_one_of_mul_self_of_commute htr hsg hs2
  have hmain : ∀ w : StatedSp (k + 2 + 1) F, (a * b * a) * φ₁ w * (a * b * a)⁻¹ = φ₂ w := by
    intro w
    have h := hall1 w
    simpa only [hs1, map_one, one_mul, inv_one, mul_one] using h
  have hcube : ∀ j : Fin (k + 2 + 1), j.val = 0 →
      ((a * b * a) * φ₁ (weylRep (k + 2 + 1) F j)) ^ 3 = 1 := by
    intro j hj
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    rw [hj0]
    have hTa : (a * b * a) * φ₁ (weylRep (k + 2 + 1) F 0) = a * b := by
      calc (a * b * a) * φ₁ (weylRep (k + 2 + 1) F 0) = (a * b * a) * a := by rw [ha]
        _ = a * b := by
            calc (a * b * a) * a = a * b * (a * a) := by group
              _ = a * b := by rw [haa, mul_one]
    simp [hTa, hU1, hs1]
  have hlevelt : ∀ r : TauCeti.GLSymplecticFin.RootSubgroupIndex (k + 2 + 1),
      (∀ j : Fin (k + 2 + 1), j.val = 0 → stdVec r j = 0) → ∀ c : F,
        (a * b * a) * φ₁ (CFSG.LieType.Universal.Symplectic.SpExtras.elt r c) =
          φ₁ (CFSG.LieType.Universal.Symplectic.SpExtras.elt r c) * (a * b * a) := by
    intro r hr c
    have hr0 : stdVec r (0 : Fin (k + 2 + 1)) = 0 := hr 0 (by simp)
    obtain ⟨r', hr'⟩ := exists_spShift_of_stdVec_zero (n := k + 2) (r' := r) hr0
    have helt : spLeviBlock (k + 2) F (CFSG.LieType.Universal.Symplectic.SpExtras.elt r' c) =
        CFSG.LieType.Universal.Symplectic.SpExtras.elt r c := by
      rw [spLeviBlock_elt, hr']
    have hβelt : φ₂ (CFSG.LieType.Universal.Symplectic.SpExtras.elt r c) =
        φ₁ (CFSG.LieType.Universal.Symplectic.SpExtras.elt r c) := by
      rw [← helt]
      exact (hβ (CFSG.LieType.Universal.Symplectic.SpExtras.elt r' c)).symm
    have hcj := spEnd_mul_eq_mul_of_conj hTT (hmain (CFSG.LieType.Universal.Symplectic.SpExtras.elt r c))
    rwa [hβelt] at hcj
  exact ⟨hmain, hTT, hcube, hlevelt⟩

end CFSG.StandardType
