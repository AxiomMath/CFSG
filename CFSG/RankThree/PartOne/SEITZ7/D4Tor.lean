module

public import CFSG.RankThree.PartOne.SEITZ7.D4Rel

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3
open scoped commutatorElement

variable {K : Type} [Field K] (σ : K →+* K)

theorem torusElement_conj_xd (i : Fin d4.rank) {p : ℕ} (hp : p < 24) (t : Kˣ) (c : K) :
    torusElement d4 K i t * xd p c * (torusElement d4 K i t)⁻¹ =
      xd p (((t ^ (∑ j, d4.cartan i j * (d4Root p) j) : Kˣ) : K) * c) := by
  have hγ : IsRoot d4 (d4Root p) := isRoot_d4 hp
  have := (rootOperatorFamily d4).torusElement_mul_eltElement_mul_inv (K := K) i t
    ⟨d4Root p, hγ⟩ c
  rw [← xPar_of_isRoot hγ] at this
  rw [← xPar_of_isRoot hγ] at this
  exact this

theorem weylElement_conj_xd [CharP K 2] (i : Fin d4.rank) {p q : ℕ} (hp : p < 24)
    (h : reflect d4 i (d4Root p) = d4Root q) (c : K) :
    weylElement d4 K i * xd p c * (weylElement d4 K i)⁻¹ = xd q c := by
  have hγ : IsRoot d4 (d4Root p) := isRoot_d4 hp
  have hq : IsRoot d4 (d4Root q) := h ▸ IsRoot.reflect i hγ
  have hF := (rootOperatorFamily d4).weylElement_mul_eltElement_mul_inv (K := K) i
    ⟨d4Root p, hγ⟩ c
  have hsign : (((rootOperatorFamily d4).sign i ⟨d4Root p, hγ⟩ : ℤ) : K) = 1 := by
    rcases (rootOperatorFamily d4).sign_eq i ⟨d4Root p, hγ⟩ with h1 | h1 <;> rw [h1] <;>
      simp [CharTwo.neg_eq]
  rw [hsign, one_mul] at hF
  have e : simple d4 i • (⟨d4Root p, hγ⟩ : Root d4) = ⟨d4Root q, hq⟩ := by
    rw [simple_smul_eq_sRoot]
    exact Subtype.ext h
  rw [e] at hF
  simpa [xPar_of_isRoot hγ, xPar_of_isRoot hq] using hF

theorem sum_cartan_check : (∑ j, d4.cartan (nd 2) j * (d4Root 22) j = 1) ∧
    (∑ j, d4.cartan (nd 2) j * (d4Root 19) j = -1) ∧
    (∀ i : Fin d4.rank, i ≠ nd 2 → ∑ j, d4.cartan i j * (d4Root 22) j = 0) := by
  decide +kernel

theorem hB_xH (s : Kˣ) (d : K) :
    torusElement d4 K (nd 2) s * xH d * (torusElement d4 K (nd 2) s)⁻¹ = xH (s * d) := by
  have := torusElement_conj_xd (K := K) (nd 2) (p := 22) (by norm_num) s d
  rw [sum_cartan_check.1, zpow_one] at this
  exact this

theorem hB_xN (s : Kˣ) (d : K) :
    torusElement d4 K (nd 2) s * xN d * (torusElement d4 K (nd 2) s)⁻¹ = xN ((s⁻¹ : Kˣ) * d) := by
  have := torusElement_conj_xd (K := K) (nd 2) (p := 19) (by norm_num) s d
  rw [sum_cartan_check.2.1, zpow_neg, zpow_one] at this
  exact this

theorem hOuter_xH {i : Fin d4.rank} (hi : i ≠ nd 2) (t : Kˣ) (d : K) :
    torusElement d4 K i t * xH d * (torusElement d4 K i t)⁻¹ = xH d := by
  have := torusElement_conj_xd (K := K) i (p := 22) (by norm_num) t d
  rw [sum_cartan_check.2.2 i hi, zpow_zero, Units.val_one, one_mul] at this
  exact this

theorem hShort_xH (t : Kˣ) (d : K) :
    hShortHom σ t * xH d * (hShortHom σ t)⁻¹ = xH d := by
  rw [hShortHom_apply]
  have e : ∀ (a b c : adjointGroup d4 K) (x : adjointGroup d4 K),
      a * b * c * x * (a * b * c)⁻¹ = a * (b * (c * x * c⁻¹) * b⁻¹) * a⁻¹ := by
    intro a b c x; group
  rw [e, hOuter_xH (by decide) _ _, hOuter_xH (by decide) _ _, hOuter_xH (by decide) _ _]

@[expose] noncomputable def Wt : adjointGroup d4 K :=
  weylElement d4 K (nd 2) * (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) *
    weylElement d4 K (nd 3))

theorem reflect_W_check :
    reflect d4 (nd 3) (d4Root 2) = d4Root 9 ∧ reflect d4 (nd 1) (d4Root 9) = d4Root 15 ∧
    reflect d4 (nd 0) (d4Root 15) = d4Root 19 ∧ reflect d4 (nd 2) (d4Root 19) = d4Root 22 ∧
    reflect d4 (nd 3) (d4Root 8) = d4Root 16 ∧ reflect d4 (nd 1) (d4Root 16) = d4Root 20 ∧
    reflect d4 (nd 0) (d4Root 20) = d4Root 21 ∧ reflect d4 (nd 2) (d4Root 21) = d4Root 23 := by
  decide +kernel

theorem Wt_xB [CharP K 2] (c : K) : Wt * xd 2 c * Wt⁻¹ = xd 22 c := by
  obtain ⟨h1, h2, h3, h4, -⟩ := reflect_W_check
  have e : Wt * xd 2 c * Wt⁻¹ = weylElement d4 K (nd 2) * (weylElement d4 K (nd 0) *
      (weylElement d4 K (nd 1) * (weylElement d4 K (nd 3) * xd 2 c *
        (weylElement d4 K (nd 3))⁻¹) * (weylElement d4 K (nd 1))⁻¹) *
          (weylElement d4 K (nd 0))⁻¹) * (weylElement d4 K (nd 2))⁻¹ := by
    unfold Wt; group
  rw [e, weylElement_conj_xd (nd 3) (by norm_num) h1, weylElement_conj_xd (nd 1) (by norm_num) h2,
    weylElement_conj_xd (nd 0) (by norm_num) h3, weylElement_conj_xd (nd 2) (by norm_num) h4]

theorem Wt_xBneg [CharP K 2] (c : K) : Wt * xd 8 c * Wt⁻¹ = xd 23 c := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := reflect_W_check
  have e : Wt * xd 8 c * Wt⁻¹ = weylElement d4 K (nd 2) * (weylElement d4 K (nd 0) *
      (weylElement d4 K (nd 1) * (weylElement d4 K (nd 3) * xd 8 c *
        (weylElement d4 K (nd 3))⁻¹) * (weylElement d4 K (nd 1))⁻¹) *
          (weylElement d4 K (nd 0))⁻¹) * (weylElement d4 K (nd 2))⁻¹ := by
    unfold Wt; group
  rw [e, weylElement_conj_xd (nd 3) (by norm_num) h1, weylElement_conj_xd (nd 1) (by norm_num) h2,
    weylElement_conj_xd (nd 0) (by norm_num) h3, weylElement_conj_xd (nd 2) (by norm_num) h4]

theorem torusElement_mul_d4 (i : Fin d4.rank) (s t : Kˣ) :
    torusElement d4 K i (s * t) = torusElement d4 K i s * torusElement d4 K i t :=
  (torusHom (τ := d4) K i).map_mul s t

theorem torusElement_one_d4 (i : Fin d4.rank) : torusElement d4 K i (1 : Kˣ) = 1 :=
  (torusHom (τ := d4) K i).map_one

theorem weylElement_torus_d4 (i j : Fin d4.rank) (t : Kˣ) :
    weylElement d4 K i * torusElement d4 K j t * (weylElement d4 K i)⁻¹ =
      torusElement d4 K j t * torusElement d4 K i (t ^ (-d4.cartan j i)) := by
  apply Subtype.ext
  exact weylElt_one_mul_torusElt_mul_inv d4 K i j t

theorem cartan_check : d4.cartan (nd 2) (nd 3) = -1 ∧ d4.cartan (nd 2) (nd 1) = -1 ∧
    d4.cartan (nd 2) (nd 0) = -1 ∧ d4.cartan (nd 3) (nd 1) = 0 ∧ d4.cartan (nd 3) (nd 0) = 0 ∧
    d4.cartan (nd 1) (nd 0) = 0 ∧ d4.cartan (nd 2) (nd 2) = 2 ∧ d4.cartan (nd 0) (nd 2) = -1 ∧
    d4.cartan (nd 1) (nd 2) = -1 ∧ d4.cartan (nd 3) (nd 2) = -1 := by
  decide +kernel

theorem rearr3 {G : Type*} [Group G] {a b d c : G} (hac : a * c = c * a) (hbc : b * c = c * b)
    (hdc : d * c = c * d) : a * c * (b * c) * (d * c) = c * c * c * (a * b * d) := by
  have hac' : ∀ z, a * (c * z) = c * (a * z) := fun z => by rw [← mul_assoc, hac, mul_assoc]
  have hbc' : ∀ z, b * (c * z) = c * (b * z) := fun z => by rw [← mul_assoc, hbc, mul_assoc]
  simp only [mul_assoc, hac', hbc', hac, hbc, hdc]

theorem Wt_hB (s : Kˣ) :
    Wt * torusElement d4 K (nd 2) s * Wt⁻¹ = torusElement d4 K (nd 2) (s ^ 2) *
      (torusElement d4 K (nd 0) s * torusElement d4 K (nd 1) s * torusElement d4 K (nd 3) s) := by
  obtain ⟨c23, c21, c20, c31, c30, c10, c22, c02, c12, c32⟩ := cartan_check
  have hW := weylElement_torus_d4 (K := K)
  have conj2 : ∀ (n x y : adjointGroup d4 K), n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) :=
    fun n x y => by group
  have conj3 : ∀ (n x y z : adjointGroup d4 K),
      n * (x * y * z) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) * (n * z * n⁻¹) :=
    fun n x y z => by group
  have conj4 : ∀ (n w x y z : adjointGroup d4 K), n * (w * x * y * z) * n⁻¹ =
      (n * w * n⁻¹) * (n * x * n⁻¹) * (n * y * n⁻¹) * (n * z * n⁻¹) :=
    fun n w x y z => by group
  have h3 : weylElement d4 K (nd 3) * torusElement d4 K (nd 2) s * (weylElement d4 K (nd 3))⁻¹ =
      torusElement d4 K (nd 2) s * torusElement d4 K (nd 3) s := by
    rw [hW, c23]; simp
  have h1 : weylElement d4 K (nd 1) * (torusElement d4 K (nd 2) s * torusElement d4 K (nd 3) s) *
      (weylElement d4 K (nd 1))⁻¹ =
      torusElement d4 K (nd 2) s * torusElement d4 K (nd 1) s * torusElement d4 K (nd 3) s := by
    rw [conj2, hW (nd 1) (nd 2), hW (nd 1) (nd 3), c21, c31]
    simp [torusElement_one_d4]
  have h0 : weylElement d4 K (nd 0) * (torusElement d4 K (nd 2) s * torusElement d4 K (nd 1) s *
      torusElement d4 K (nd 3) s) * (weylElement d4 K (nd 0))⁻¹ =
      torusElement d4 K (nd 2) s * torusElement d4 K (nd 0) s * torusElement d4 K (nd 1) s *
        torusElement d4 K (nd 3) s := by
    rw [conj3, hW (nd 0) (nd 2), hW (nd 0) (nd 1), hW (nd 0) (nd 3), c20, c10, c30]
    simp [torusElement_one_d4]
  have h2 : weylElement d4 K (nd 2) * (torusElement d4 K (nd 2) s * torusElement d4 K (nd 0) s *
      torusElement d4 K (nd 1) s * torusElement d4 K (nd 3) s) * (weylElement d4 K (nd 2))⁻¹ =
      torusElement d4 K (nd 2) (s ^ 2) *
        (torusElement d4 K (nd 0) s * torusElement d4 K (nd 1) s * torusElement d4 K (nd 3) s) := by
    rw [conj4, hW (nd 2) (nd 2), hW (nd 2) (nd 0), hW (nd 2) (nd 1), hW (nd 2) (nd 3), c22, c02,
      c12, c32]
    simp only [neg_neg, zpow_one]
    have hac : torusElement d4 K (nd 0) s * torusElement d4 K (nd 2) s =
        torusElement d4 K (nd 2) s * torusElement d4 K (nd 0) s :=
      (torusElement_commute (nd 0) (nd 2) s s).eq
    have hbc : torusElement d4 K (nd 1) s * torusElement d4 K (nd 2) s =
        torusElement d4 K (nd 2) s * torusElement d4 K (nd 1) s :=
      (torusElement_commute (nd 1) (nd 2) s s).eq
    have hdc : torusElement d4 K (nd 3) s * torusElement d4 K (nd 2) s =
        torusElement d4 K (nd 2) s * torusElement d4 K (nd 3) s :=
      (torusElement_commute (nd 3) (nd 2) s s).eq
    have hm : torusElement d4 K (nd 2) s * torusElement d4 K (nd 2) (s ^ (-2 : ℤ)) *
        torusElement d4 K (nd 2) s * torusElement d4 K (nd 2) s *
          torusElement d4 K (nd 2) s = torusElement d4 K (nd 2) (s ^ 2) := by
      rw [← torusElement_mul_d4, ← torusElement_mul_d4, ← torusElement_mul_d4,
        ← torusElement_mul_d4]
      congr 1
      group
    calc _ = torusElement d4 K (nd 2) s * torusElement d4 K (nd 2) (s ^ (-2 : ℤ)) *
          (torusElement d4 K (nd 0) s * torusElement d4 K (nd 2) s *
            (torusElement d4 K (nd 1) s * torusElement d4 K (nd 2) s) *
              (torusElement d4 K (nd 3) s * torusElement d4 K (nd 2) s)) := by
          simp only [mul_assoc]
      _ = torusElement d4 K (nd 2) s * torusElement d4 K (nd 2) (s ^ (-2 : ℤ)) *
          (torusElement d4 K (nd 2) s * torusElement d4 K (nd 2) s * torusElement d4 K (nd 2) s *
            (torusElement d4 K (nd 0) s * torusElement d4 K (nd 1) s *
              torusElement d4 K (nd 3) s)) := by rw [rearr3 hac hbc hdc]
      _ = _ := by rw [← hm]; group
  have e : Wt * torusElement d4 K (nd 2) s * Wt⁻¹ = weylElement d4 K (nd 2) *
      (weylElement d4 K (nd 0) * (weylElement d4 K (nd 1) * (weylElement d4 K (nd 3) *
        torusElement d4 K (nd 2) s * (weylElement d4 K (nd 3))⁻¹) * (weylElement d4 K (nd 1))⁻¹) *
          (weylElement d4 K (nd 0))⁻¹) * (weylElement d4 K (nd 2))⁻¹ := by
    unfold Wt; group
  rw [e, h3, h1, h0, h2]

end CFSG.RankThree.PartOne.SEITZ7
