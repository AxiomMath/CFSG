module

public import CFSG.Quasithin.Background.C124YLH6Elim2

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.H6

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

theorem actHom_scalar {K : Type} [Field K] {Γ₀ : Subgroup (GL (Fin 3) K)} {z0 : ↥Γ₀} {ω : K}
    (h : mat Γ₀ z0 = ω • (1 : Matrix (Fin 3) (Fin 3) K)) (q : Multiplicative (Fin 3 → K)) :
    actHom z0 q = Multiplicative.ofAdd (ω • Multiplicative.toAdd q) := by
  simp only [actHom_apply, natAct]
  congr 1
  show (mat Γ₀ z0).mulVec _ = _
  rw [h, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem zpow_two_cases {G : Type*} [Group G] {r : G} (hr2 : r * r = 1) (k : ℤ) :
    r ^ k = 1 ∨ r ^ k = r := by
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hr2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hr2, one_zpow, one_mul, zpow_one]

namespace HatCtx

variable {W : Type*} [CommGroup W] [Finite W] {K : Type} [Field K] [Finite K]
  {Γ₀ : Subgroup (GL (Fin 3) K)} {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : HatCtx K Γ₀ Ls U Z)

include C in
theorem no_outer_offender {Xs : Subgroup (MulAut W)} (hLX : Ls ≤ Xs)
    (hnorm : ∀ x ∈ Xs, x ∈ Subgroup.normalizer (Ls : Set (MulAut W)))
    (hF : quasithinGenFitting Xs = Ls)
    (hU : ∀ x ∈ Xs, ∀ u, u ∈ U ↔ x u ∈ U) (hZ : ∀ x ∈ Xs, ∀ z, z ∈ Z ↔ x z ∈ Z)
    {r : MulAut W} (hr : r ∈ Xs) (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hoff : Nat.card U ≤ 2 * Nat.card (liftFix U Z (Subgroup.zpowers r))) : False := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  have hzr : Subgroup.zpowers r ≤ Xs := Subgroup.zpowers_le.2 hr
  have hZB : Z ≤ liftFix U Z (Subgroup.zpowers r) := by
    intro z hz
    refine mem_liftFix.2 ⟨hc.Z_le hz, fun b hb => ?_⟩
    exact Z.mul_mem ((hZ b (hzr hb) z).1 hz) (Z.inv_mem hz)
  have hcardF : 32 ≤ Nat.card (fixImg U Z c (Subgroup.zpowers r)) := by
    have h1 := hc.card_U
    have h2 := hc.card_liftFix hZB
    rw [h1, h2, C.card_Q] at hoff
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    by_contra hlt
    push Not at hlt
    nlinarith [Nat.mul_le_mul_left (Nat.card Z) (Nat.le_of_lt_succ hlt)]
  let T : Monoid.End (Multiplicative (Fin 3 → K)) := indHom hc Xs hU hZ ⟨r, hr⟩
  have hfixeq : ∀ q, q ∈ fixImg U Z c (Subgroup.zpowers r) ↔ T q = q := by
    intro q
    rw [mem_fixImg_iff_ind hc Xs hU hZ hzr q]
    constructor
    · intro h
      exact h ⟨r, hr⟩ (Subgroup.mem_zpowers r)
    · intro h x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      rcases zpow_two_cases hr2 k with h1 | h1
      · have hx1 : x = 1 := Subtype.ext (by rw [← hk, h1]; rfl)
        rw [hx1, map_one]
        rfl
      · have hx1 : x = ⟨r, hr⟩ := Subtype.ext (by rw [← hk, h1])
        rw [hx1]
        exact h
  have hFeq : fixImg U Z c (Subgroup.zpowers r) = MonoidHom.eqLocus T (MonoidHom.id _) := by
    ext q
    exact hfixeq q
  have hcardE : 32 ≤
      Nat.card ↥(MonoidHom.eqLocus T (MonoidHom.id (Multiplicative (Fin 3 → K)))) := by
    rw [← hFeq]
    exact hcardF
  obtain ⟨z0, ω, hz0c, hz01, hz3, hω1, hω3, hωm, hcent⟩ := C.exists_center
  obtain ⟨γ', hγ'c, hγ'1, hconj⟩ := C.conj_center hnorm hz0c hz01 hr
  have hrel : ∀ q, T (actHom z0 q) = actHom γ' (T q) := by
    intro q
    have key : (⟨r, hr⟩ : ↥Xs) * ⟨C.phi z0, hLX (C.phi_mem z0)⟩ =
        ⟨C.phi γ', hLX (C.phi_mem γ')⟩ * ⟨r, hr⟩ := by
      apply Subtype.ext
      show r * C.phi z0 = C.phi γ' * r
      rw [← hconj]
      group
    have h1 := congrArg (fun x : ↥Xs => indHom hc Xs hU hZ x q) key
    simp only [map_mul, indHom_phi C hc hequiv hLX hU hZ] at h1
    exact h1
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω3
    norm_num at hω3
  rcases hcent γ' hγ'c with h | h | h
  · exact hγ'1 h
  ·
    subst h
    have hcomm : ∀ y : Fin 3 → K, T (Multiplicative.ofAdd (ω • y)) =
        Multiplicative.ofAdd (ω • Multiplicative.toAdd (T (Multiplicative.ofAdd y))) := by
      intro y
      have := hrel (Multiplicative.ofAdd y)
      rwa [actHom_scalar hωm, actHom_scalar hωm, toAdd_ofAdd] at this
    have hT1 := eq_one_of_linear C.hK hω1 hω3 T hcomm hcardE
    have hLfaith : ∀ l : ↥Ls, indHom hc Xs hU hZ ⟨l, hLX l.2⟩ = 1 → l = 1 := by
      intro l hl
      obtain ⟨γ, hγ⟩ : (l : MulAut W) ∈ C.phi.range := C.phi_range.ge l.2
      have e : (⟨C.phi γ, hLX (C.phi_mem γ)⟩ : ↥Xs) = ⟨l, hLX l.2⟩ := Subtype.ext hγ
      have hq : ∀ q, actHom γ q = q := fun q => by
        have h2 := congrArg (fun f : Monoid.End (Multiplicative (Fin 3 → K)) => f q) hl
        rw [← e, indHom_phi C hc hequiv hLX hU hZ γ] at h2
        exact h2
      have hγ1 : γ = 1 := by
        apply eq_one_of_mulVec
        intro y
        exact congrArg Multiplicative.toAdd (hq (Multiplicative.ofAdd y))
      apply Subtype.ext
      rw [← hγ, hγ1, map_one]
      rfl
    have hr1' : (⟨r, hr⟩ : ↥Xs) = 1 :=
      faithful_of_fstar hc hLX hnorm hF hU hZ hLfaith ⟨r, hr⟩ (MonoidHom.ext hT1)
    exact hr1 (congrArg Subtype.val hr1')
  ·
    subst h
    have hT : ∀ q, T (actHom z0 q) = actHom z0 (actHom z0 (T q)) := by
      intro q
      rw [hrel q, actHom_mul]
    have hinj : Function.Injective (actHom z0) := by
      intro a b hab
      rw [actHom_scalar hωm, actHom_scalar hωm] at hab
      have := smul_right_injective (Fin 3 → K) hω0 (Multiplicative.ofAdd.injective hab)
      exact Multiplicative.toAdd.injective this
    have hfp : ∀ q, actHom z0 q = q → q = 1 := by
      intro q hq
      rw [actHom_scalar hωm] at hq
      have h2 : (ω - 1) • Multiplicative.toAdd q = 0 := by
        rw [sub_smul, one_smul]
        have := congrArg Multiplicative.toAdd hq
        rw [toAdd_ofAdd] at this
        rw [this, sub_self]
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact absurd (sub_eq_zero.1 h3) hω1
      · exact Multiplicative.toAdd.injective (by simpa using h3)
    have hsq := card_sq_le_semilinear (actHom z0) T hinj hfp hT
    rw [C.card_Q] at hsq
    nlinarith

end HatCtx

end CFSG.Quasithin.C124.YL.H6
