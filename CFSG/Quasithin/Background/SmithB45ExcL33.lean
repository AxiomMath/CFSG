module

public import CFSG.Quasithin.Background.SmithB45ExcL33Mat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bRank
public import Certificates.Certificate260383
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.Quasithin.Background.SmithB45ExcL2

public section

namespace CFSG.Quasithin.B45Exc

open Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank CFSG.Quasithin
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family


namespace L33

theorem l33_check :
    (∀ (K : Type) [Field K] [CharP K 3], (∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) →
      ∀ A : Matrix (Fin 3) (Fin 3) K, Aᵀ = A → A.det ≠ 0 →
        ∃ Y : Matrix (Fin 3) (Fin 3) K, Y.det = 1 ∧ Y * A = A * Yᵀ ∧ Y ^ 13 = 1 ∧ Y ≠ 1) ∧
    (∀ (K : Type) [Field K] [CharP K 3], (∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) →
      ∀ T U : Matrix (Fin 3) (Fin 3) K, T.det = 1 → U.det = 1 → T * T = 1 → T ≠ 1 →
        U * U = 1 → U ≠ 1 → T ≠ U → T * U = U * T →
        ∃ G Gi : Matrix (Fin 3) (Fin 3) K, G.det = 1 ∧ G * T = T * G ∧ G * Gi = 1 ∧
          (U * (G * U * Gi)) ^ 4 = 1 ∧ (U * (G * U * Gi)) ^ 2 ≠ 1) ∧
    (∀ (K : Type) [Field K] [CharP K 3], (∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) →
      ∀ A T U : Matrix (Fin 3) (Fin 3) K, Aᵀ = A → A.det ≠ 0 → T.det = 1 → U.det = 1 →
        T * T = 1 → T ≠ 1 → U * U = 1 → U ≠ 1 → T ≠ U → T * U = U * T → T * A * Tᵀ = A →
        U * A * Uᵀ = A →
        ∃ X₁ Y₁ X₂ Y₂ X₃ Y₃ : Matrix (Fin 3) (Fin 3) K, X₁.det = 1 ∧ X₂.det = 1 ∧ X₃.det = 1 ∧
          X₁ * Y₁ = 1 ∧ X₂ * Y₂ = 1 ∧ X₃ * Y₃ = 1 ∧ X₁ * A * X₁ᵀ = A ∧
          X₂ * (T * A) * X₂ᵀ = T * A ∧ X₃ * (U * A) * X₃ᵀ = U * A ∧
          ((X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃)) ^ 13 = 1 ∧
          (X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃) ≠ 1) :=
  Certificates.certificate260383

theorem index_fixV_eq_two_pow_rank {W : Type} [CommGroup W] [Finite W]
    [Fact (∀ w : W, w * w = 1)] (g : MulAut W) :
    (fixV (Subgroup.zpowers g)).index =
      2 ^ finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin g))) := by
  have hker : (dispHom g).ker = fixV (Subgroup.zpowers g) := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff_dispHom]
  rw [← hker, Subgroup.index_ker]
  have : Nat.card (dispHom g).range = Nat.card (Set.range fun v : W => g v * v⁻¹) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [MonoidHom.mem_range]; rfl)
  rw [this]
  exact card_range_displacement g

section Main

variable {W : Type} [CommGroup W] [Finite W] {K : Type} [Field K] [CharP K 3]
  {L : Subgroup (MulAut W)} (D : CoverData3 K L)

theorem outer_index_ge (hW : ∀ w : W, w * w = 1) (hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k)
    (hφ : Function.Injective D.φ) (hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K))
    {b : MulAut W} (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1)
    (A : GL (Fin 3) K) (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A)
    (hβ : D.beta hb = conjAut 3 K A * dualAut 3 K) :
    2 ^ 6 ≤ (fixV (Subgroup.zpowers b)).index := by
  have hAdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
  obtain ⟨Y, hYdet, hYA, hY13, hY1⟩ := l33_check.1 K hrep _ hA hAdet
  set y₀ : SpecialLinearGroup (Fin 3) K := ⟨Y, hYdet⟩ with hy₀
  have hσ : sigA A y₀ = y₀⁻¹ := sigA_eq_inv hYA
  have hrel := D.conj_eq hperf hb (sigA A) (hβ.trans (descendAut_sigA A).symm)
  set y : MulAut W := (D.φ y₀ : MulAut W) with hy
  have hby : b * y * b⁻¹ = y⁻¹ := by
    rw [hy, hrel, hσ, map_inv, Subgroup.coe_inv]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hy₀13 : y₀ ^ 13 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hY13)
  have hy13 : y ^ 13 = 1 := by
    rw [hy, ← Subgroup.coe_pow, ← map_pow, hy₀13, map_one, Subgroup.coe_one]
  have hy1 : y ≠ 1 := by
    intro h
    apply hY1
    have h1 : y₀ = 1 := hφ (Subtype.ext (by rw [map_one]; exact h))
    have := congrArg (fun z : SpecialLinearGroup (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [hy₀] using this
  have hbyb : b * y⁻¹ * b = y := by
    have h1 : (b * y * b⁻¹)⁻¹ = b * y⁻¹ * b⁻¹ := by group
    rw [hby, inv_inv, hbinv] at h1
    exact h1.symm
  set c : MulAut W := b * (y⁻¹ * b * y⁻¹⁻¹) with hc
  have hcy : c = y ^ 2 := by
    rw [hc, inv_inv, ← mul_assoc, ← mul_assoc, hbyb, pow_two]
  have hc13 : c ^ 13 = 1 := by
    rw [hcy, ← pow_mul, show 2 * 13 = 13 * 2 by norm_num, pow_mul, hy13, one_pow]
  have hc1 : c ≠ 1 := by
    intro h
    apply hy1
    rw [hcy] at h
    calc y = (y ^ 2) ^ 6 * y := by rw [h, one_pow, one_mul]
      _ = y ^ 13 := by rw [← pow_mul, ← pow_succ]
      _ = 1 := hy13
  have : Fact (Nat.Prime 13) := fact_prime_thirteen
  have h12 := X5.two_pow_orderOf_le_index_fixV hW (ℓ := 13) (by norm_num) hc13 hc1
  rw [orderOf_two_zmod_13] at h12
  have h2 := X5.index_fixV_mul_le b (y⁻¹ * b * y⁻¹⁻¹)
  rw [X5.index_fixV_conj] at h2
  have h3 : 2 ^ 12 ≤ (fixV (Subgroup.zpowers b)).index * (fixV (Subgroup.zpowers b)).index :=
    h12.trans h2
  by_contra hlt
  push Not at hlt
  have h4 : (fixV (Subgroup.zpowers b)).index * (fixV (Subgroup.zpowers b)).index < 2 ^ 12 := by
    calc (fixV (Subgroup.zpowers b)).index * (fixV (Subgroup.zpowers b)).index
        < 2 ^ 6 * 2 ^ 6 := Nat.mul_lt_mul'' hlt hlt
      _ = 2 ^ 12 := by norm_num
  omega

omit [Finite W] [CharP K 3] in
theorem eq_of_coe_phi_eq (hφ : Function.Injective D.φ) {x y : SpecialLinearGroup (Fin 3) K}
    (h : (D.φ x : MulAut W) = D.φ y) : x = y :=
  hφ (Subtype.ext h)

omit [Finite W] [CharP K 3] in
theorem exists_lift_inv (hφ : Function.Injective D.φ) {t : MulAut W} (htL : t ∈ L)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ t₀ : SpecialLinearGroup (Fin 3) K, (D.φ t₀ : MulAut W) = t ∧ t₀ * t₀ = 1 ∧ t₀ ≠ 1 := by
  obtain ⟨t₀, ht₀⟩ := D.surj ⟨t, htL⟩
  have et : (D.φ t₀ : MulAut W) = t := congrArg Subtype.val ht₀
  refine ⟨t₀, et, eq_of_coe_phi_eq D hφ ?_, ?_⟩
  · rw [map_mul, Subgroup.coe_mul, et, ht2, map_one, Subgroup.coe_one]
  · rintro rfl
    apply ht1
    rw [← et, map_one, Subgroup.coe_one]

omit [CharP K 3] in
theorem coe_inv_facts {t : SpecialLinearGroup (Fin 3) K} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    (t : Matrix (Fin 3) (Fin 3) K) * t = 1 ∧ (t : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
  refine ⟨by rw [← Matrix.SpecialLinearGroup.coe_mul, ht2, Matrix.SpecialLinearGroup.coe_one],
    fun h => ht1 (Subtype.ext h)⟩

omit [CharP K 3] in
theorem coe_ne_of_ne {t u : SpecialLinearGroup (Fin 3) K} (h : t ≠ u) :
    (t : Matrix (Fin 3) (Fin 3) K) ≠ u := fun h' => h (Subtype.ext h')

omit [CharP K 3] in
theorem coe_comm {t u : SpecialLinearGroup (Fin 3) K} (h : t * u = u * t) :
    (t : Matrix (Fin 3) (Fin 3) K) * u = u * t := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_mul]

theorem inner_four_false (hW : ∀ w : W, w * w = 1)
    (hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) (hφ : Function.Injective D.φ)
    (hin : ∀ s ∈ L, s ≠ 1 → s * s = 1 → 2 ^ 4 ≤ (fixV (Subgroup.zpowers s)).index)
    {t u : MulAut W} (htL : t ∈ L) (huL : u ∈ L) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u)
    (ht2 : t * t = 1) (hu2 : u * u = 1) (hc : t * u = u * t)
    (hfix : fixV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers u))
    (hidx : (fixV (Subgroup.zpowers t)).index ≤ 2 ^ 4) : False := by
  obtain ⟨t₀, et, ht₀2, ht₀1⟩ := exists_lift_inv D hφ htL ht1 ht2
  obtain ⟨u₀, eu, hu₀2, hu₀1⟩ := exists_lift_inv D hφ huL hu1 hu2
  have htu₀ : t₀ ≠ u₀ := by
    rintro rfl
    exact htu (et.symm.trans eu)
  have hc₀ : t₀ * u₀ = u₀ * t₀ :=
    eq_of_coe_phi_eq D hφ (by rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, et, eu, hc])
  obtain ⟨hT2, hT1⟩ := coe_inv_facts ht₀2 ht₀1
  obtain ⟨hU2, hU1⟩ := coe_inv_facts hu₀2 hu₀1
  obtain ⟨G, Gi, hG, hGT, hGGi, hw4, hw2⟩ := l33_check.2.1 K hrep _ _ t₀.2 u₀.2 hT2 hT1
    hU2 hU1 (coe_ne_of_ne htu₀) (coe_comm hc₀)
  set g₀ : SpecialLinearGroup (Fin 3) K := ⟨G, hG⟩ with hg₀
  have hg₀i : ((g₀⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Gi :=
    coe_inv_eq hGGi
  set w₀ : SpecialLinearGroup (Fin 3) K := u₀ * (g₀ * u₀ * g₀⁻¹) with hw₀
  have hw₀m : (w₀ : Matrix (Fin 3) (Fin 3) K) = u₀ * (G * u₀ * Gi) := by
    simp only [hw₀, Matrix.SpecialLinearGroup.coe_mul, hg₀i]
    rfl
  have hw₀4 : w₀ ^ 4 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, hw₀m, Matrix.SpecialLinearGroup.coe_one]
    exact hw4)
  have hw₀2 : w₀ ^ 2 ≠ 1 := fun h => hw2 (by
    rw [← hw₀m, ← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one])
  have hg₀t : g₀ * t₀ = t₀ * g₀ := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hGT)
  set g : MulAut W := (D.φ g₀ : MulAut W) with hg
  set w : MulAut W := (D.φ w₀ : MulAut W) with hw
  have hwu : w = u * (g * u * g⁻¹) := by
    rw [hw, hw₀, map_mul, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, eu]
  have hgt : g * t = t * g := by
    rw [hg, ← et, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hg₀t]
  have hw4' : w ^ 4 = 1 := by
    rw [hw, ← Subgroup.coe_pow, ← map_pow, hw₀4, map_one, Subgroup.coe_one]
  have hw2' : w ^ 2 ≠ 1 := fun h => hw₀2 (eq_of_coe_phi_eq D hφ (by
    rw [map_pow, Subgroup.coe_pow, map_one, Subgroup.coe_one]
    exact h))
  have htw : fixV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers w) := by
    rw [hwu]
    exact fixV_le_fixV_mul hfix (fixV_le_fixV_conj hfix hgt)
  have hw2L : w ^ 2 ∈ L := by
    rw [hw, ← Subgroup.coe_pow]
    exact (D.φ w₀ ^ 2).2
  have hw22 : w ^ 2 * w ^ 2 = 1 := by rw [← pow_add]; exact hw4'
  exact false_of_order_four hW htw hw4' hw2' (hidx.trans (hin _ hw2L hw2' hw22))

theorem outer_eight_false (hW : ∀ w : W, w * w = 1)
    (hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) (hφ : Function.Injective D.φ)
    (hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K)) {b t u : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (A : GL (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A) (hβ : D.beta hb = conjAut 3 K A * dualAut 3 K)
    (htL : t ∈ L) (huL : u ∈ L) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) (ht2 : t * t = 1)
    (hu2 : u * u = 1) (hc : t * u = u * t) (hbt : b * t = t * b) (hbu : b * u = u * b)
    (hfbt : fixV (Subgroup.zpowers (b * t)) = fixV (Subgroup.zpowers b))
    (hfbu : fixV (Subgroup.zpowers (b * u)) = fixV (Subgroup.zpowers b))
    (hft : fixV (Subgroup.zpowers b) ≤ fixV (Subgroup.zpowers t))
    (hidx : (fixV (Subgroup.zpowers b)).index ≤ 2 ^ 6) : False := by
  have hAdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
  obtain ⟨t₀, et, ht₀2, ht₀1⟩ := exists_lift_inv D hφ htL ht1 ht2
  obtain ⟨u₀, eu, hu₀2, hu₀1⟩ := exists_lift_inv D hφ huL hu1 hu2
  have htu₀ : t₀ ≠ u₀ := by
    rintro rfl
    exact htu (et.symm.trans eu)
  have hc₀ : t₀ * u₀ = u₀ * t₀ :=
    eq_of_coe_phi_eq D hφ (by rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, et, eu, hc])
  have hrel := D.conj_eq hperf hb (sigA A) (hβ.trans (descendAut_sigA A).symm)
  have hcent : ∀ x : SpecialLinearGroup (Fin 3) K, ∀ s : MulAut W, (D.φ x : MulAut W) = s →
      b * s = s * b → sigA A x = x := by
    intro x s hs hbs
    apply eq_of_coe_phi_eq D hφ
    rw [← hrel, hs, hbs, mul_inv_cancel_right]
  have hσt : sigA A t₀ = t₀ := hcent t₀ t et hbt
  have hσu : sigA A u₀ = u₀ := hcent u₀ u eu hbu
  obtain ⟨hT2, hT1⟩ := coe_inv_facts ht₀2 ht₀1
  obtain ⟨hU2, hU1⟩ := coe_inv_facts hu₀2 hu₀1
  obtain ⟨X₁, Y₁, X₂, Y₂, X₃, Y₃, d1, d2, d3, i1, i2, i3, s1, s2, s3, hZ13, hZ1⟩ :=
    l33_check.2.2 K hrep _ _ _ hA hAdet t₀.2 u₀.2 hT2 hT1 hU2 hU1 (coe_ne_of_ne htu₀)
      (coe_comm hc₀) (form_of_sigA_eq_self hσt) (form_of_sigA_eq_self hσu)
  set x₁ : SpecialLinearGroup (Fin 3) K := ⟨X₁, d1⟩ with hx₁
  set x₂ : SpecialLinearGroup (Fin 3) K := ⟨X₂, d2⟩ with hx₂
  set x₃ : SpecialLinearGroup (Fin 3) K := ⟨X₃, d3⟩ with hx₃
  have hx₁i : ((x₁⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Y₁ :=
    coe_inv_eq i1
  have hx₂i : ((x₂⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Y₂ :=
    coe_inv_eq i2
  have hx₃i : ((x₃⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Y₃ :=
    coe_inv_eq i3
  have hσ₁ : sigA A x₁ = x₁ := sigA_eq_self s1
  have hσ₂ : t₀ * sigA A x₂ * t₀⁻¹ = x₂ := conj_sigA_eq_self s2
  have hσ₃ : u₀ * sigA A x₃ * u₀⁻¹ = x₃ := conj_sigA_eq_self s3
  have hconj : ∀ (s : MulAut W) (s₀ : SpecialLinearGroup (Fin 3) K), (D.φ s₀ : MulAut W) = s →
      sigA A s₀ = s₀ → ∀ x : SpecialLinearGroup (Fin 3) K, s₀ * sigA A x * s₀⁻¹ = x →
      (D.φ x : MulAut W) * (b * s) = (b * s) * (D.φ x : MulAut W) := by
    intro s s₀ hs hσs x hx
    have h1 : (b * s) * (D.φ x : MulAut W) * (b * s)⁻¹ = (D.φ x : MulAut W) := by
      calc (b * s) * (D.φ x : MulAut W) * (b * s)⁻¹
          = b * (D.φ (s₀ * x * s₀⁻¹) : MulAut W) * b⁻¹ := by
            rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
              hs]
            group
        _ = (D.φ (sigA A (s₀ * x * s₀⁻¹)) : MulAut W) := hrel _
        _ = (D.φ x : MulAut W) := by
            rw [map_mul (sigA A), map_mul (sigA A), map_inv (sigA A), hσs, hx]
    calc (D.φ x : MulAut W) * (b * s) = ((b * s) * (D.φ x : MulAut W) * (b * s)⁻¹) * (b * s) := by
          rw [h1]
      _ = (b * s) * (D.φ x : MulAut W) := by group
  have hc₁ : (D.φ x₁ : MulAut W) * b = b * (D.φ x₁ : MulAut W) := by
    have := hrel x₁
    rw [hσ₁] at this
    calc (D.φ x₁ : MulAut W) * b = (b * (D.φ x₁ : MulAut W) * b⁻¹) * b := by rw [this]
      _ = b * (D.φ x₁ : MulAut W) := by group
  have hc₂ := hconj t t₀ et hσt x₂ hσ₂
  have hc₃ := hconj u u₀ eu hσu x₃ hσ₃
  have hfbt' : fixV (Subgroup.zpowers (b * t)) ≤ fixV (Subgroup.zpowers t) := hfbt ▸ hft
  have hfbu' : fixV (Subgroup.zpowers (b * u)) ≤ fixV (Subgroup.zpowers t) := hfbu ▸ hft
  have hF1 := fixV_le_fixV_conj hft hc₁
  have hF2 := fixV_le_fixV_conj hfbt' hc₂
  have hF3 := fixV_le_fixV_conj hfbu' hc₃
  rw [hfbt] at hF2
  rw [hfbu] at hF3
  have hF := fixV_le_fixV_mul (fixV_le_fixV_mul hF1 hF2) hF3
  set z₀ : SpecialLinearGroup (Fin 3) K := (x₁ * t₀ * x₁⁻¹) * (x₂ * t₀ * x₂⁻¹) * (x₃ * t₀ * x₃⁻¹)
    with hz₀
  have hz₀m : (z₀ : Matrix (Fin 3) (Fin 3) K) =
      (X₁ * t₀ * Y₁) * (X₂ * t₀ * Y₂) * (X₃ * t₀ * Y₃) := by
    simp only [hz₀, Matrix.SpecialLinearGroup.coe_mul, hx₁i, hx₂i, hx₃i]
    rfl
  have hz₀13 : z₀ ^ 13 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, hz₀m, Matrix.SpecialLinearGroup.coe_one]
    exact hZ13)
  have hz₀1 : z₀ ≠ 1 := fun h => hZ1 (by rw [← hz₀m, h, Matrix.SpecialLinearGroup.coe_one])
  have hz : (D.φ z₀ : MulAut W) =
      ((D.φ x₁ : MulAut W) * t * (D.φ x₁ : MulAut W)⁻¹) *
        ((D.φ x₂ : MulAut W) * t * (D.φ x₂ : MulAut W)⁻¹) *
        ((D.φ x₃ : MulAut W) * t * (D.φ x₃ : MulAut W)⁻¹) := by
    simp only [hz₀, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, et]
  have hz13 : (D.φ z₀ : MulAut W) ^ 13 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hz₀13, map_one, Subgroup.coe_one]
  have hz1 : (D.φ z₀ : MulAut W) ≠ 1 := fun h => hz₀1 (eq_of_coe_phi_eq D hφ (by
    rw [map_one, Subgroup.coe_one]
    exact h))
  have : Fact (Nat.Prime 13) := fact_prime_thirteen
  have h12 := X5.two_pow_orderOf_le_index_fixV hW (ℓ := 13) (by norm_num) hz13 hz1
  rw [orderOf_two_zmod_13, hz] at h12
  have h3 := Subgroup.index_antitone hF
  have : (2 : ℕ) ^ 6 < 2 ^ 12 := by norm_num
  omega

end Main

end L33

open L33

theorem l33Exclusion2F (W : Type) [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    (Lb : Subgroup (MulAut W)) (hperf : Group.IsPerfect ↥Lb) (hirr : X1.IsIrrOn Lb)
    (hmod : StatedClassicalModel (CQ Lb) .PSL 3 3 1) (B : Subgroup (MulAut W))
    (hBN : B ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (hB1 : B ≠ ⊥)
    (hB2 : IsElemAbelian2 B) : Nat.card B ^ 2 * Nat.card (fixV B) < Nat.card W := by
  classical
  have hp : Nat.Prime 3 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hKp : Nat.card K = 3 := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hKp
  have : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 1) (by rw [pow_one]; exact hKcard)
  have hoddK : Odd (Fintype.card K) := by rw [hKcard]; decide
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h3 := three_eq_zero (K := K)
    have h1 : (1 : K) = 0 := by linear_combination h3 - h
    exact one_ne_zero h1
  have hKprime : ∀ k : K, ∃ n : ℕ, (n : K) = k := exists_natCast_of_card_prime hKp
  have hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k := by
    intro k
    obtain ⟨n, rfl⟩ := hKprime k
    exact ⟨n % 3, Nat.mod_lt _ (by norm_num), natCast_mod_three n⟩
  have hσ : ∀ σ : K ≃+* K, σ = 1 := fun σ => RingEquiv.ext fun k => by
    obtain ⟨n, rfl⟩ := hKprime k
    simp
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  obtain ⟨D⟩ := exists_coverData3 hp (by norm_num) hperf hodd hKp e
  have hφ : Function.Injective D.φ := (injective_iff_map_eq_one D.φ).2 fun g hg =>
    eq_one_of_mem_center (D.ker_central g (MonoidHom.mem_ker.2 hg))
  have hkerodd : Odd (Nat.card D.φ.ker) :=
    odd_card_of_pow_three fun g => Subtype.ext (by simpa using center_cube (D.ker_central g.1 g.2))
  let ρ₀ : SpecialLinearGroup (Fin 3) K →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    binaryLin.comp (Lb.subtype.comp D.φ)
  have hρ : ∀ g, ρ₀ g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro g hg
    have h1 : (D.φ g : MulAut W) = 1 := binaryLin_injective (by rw [map_one]; exact hg)
    exact D.ker_central g (MonoidHom.mem_ker.2 (Subtype.ext h1))
  have hB2' : ∀ a ∈ B, a * a = 1 := fun a ha => by
    have := hB2.2 a ha
    rwa [pow_two] at this
  have hbN : ∀ a ∈ B, a ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := fun a ha => hBN ha
  have hin : ∀ s ∈ Lb, s ≠ 1 → s * s = 1 → 2 ^ 4 ≤ (fixV (Subgroup.zpowers s)).index := by
    intro s hsL hs1 hs2
    obtain ⟨s₀, es, hs₀2, hs₀1⟩ := exists_lift_inv D hφ hsL hs1 hs2
    have h4 := inner_rank_ge_four ρ₀ h2 hKprime hoddK hρ hs₀2 hs₀1
    have e1 : ρ₀ s₀ = binaryLin s := by simp [ρ₀, es]
    rw [e1] at h4
    rw [index_fixV_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by norm_num) h4
  have hout : ∀ a ∈ B, a ∉ Lb → 2 ^ 6 ≤ (fixV (Subgroup.zpowers a)).index := by
    intro a haB haL
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a haB) (hB2' a haB) with h | ⟨A, hA, hβ⟩
    · exact absurd h haL
    · exact outer_index_ge D hW hrep hφ hperfSL (hbN a haB) (hB2' a haB) A hA hβ
  have hcard : ∀ T : Subgroup (MulAut W), T ≤ B → T ≤ Lb → Nat.card T ≤ 4 := by
    intro T hTB hTL
    have hcT : Nat.card (T.subgroupOf Lb) ≤ 4 := by
      refine card_le_of_lifts D.φ (fun g hg h => ?_) hkerodd 4
        (fun T' hT' => card_le_four_SL3 h2 T' hT') (T.subgroupOf Lb)
        (fun x _ => MonoidHom.mem_range.2 (D.surj x)) (fun x hx => ?_) (fun x hx y hy => ?_)
      · exact (Subgroup.mem_center_iff.1 (D.ker_central g hg) h).symm
      · exact Subtype.ext (hB2' _ (hTB hx))
      · exact Subtype.ext (hB2.1 _ (hTB hx) _ (hTB hy))
    have : Nat.card (T.subgroupOf Lb) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    omega
  have hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ Lb → a' ∉ Lb → a * a' ∈ Lb := by
    intro a haB a' ha'B haL ha'L
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a haB) (hB2' a haB) with h | ⟨A, -, hβ⟩
    · exact absurd h haL
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a' ha'B) (hB2' a' ha'B) with
      h' | ⟨A', -, hβ'⟩
    · exact absurd h' ha'L
    have hsq : a * a' * (a * a') = 1 := by
      calc a * a' * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [hB2.1 a' ha'B a haB]
        _ = (a * a) * (a' * a') := by group
        _ = 1 := by rw [hB2' a haB, hB2' a' ha'B, one_mul]
    exact D.mul_mem_of_dual hperfSL hW hirr.2 hodd (hbN a haB) (hbN a' ha'B) hβ hβ' hsq
  by_contra hne
  have hoff : (fixV B).index ≤ Nat.card B ^ 2 := index_le_sq_of_offender2 B (not_lt.1 hne)
  obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
  by_cases hBL : ∀ a ∈ B, a ∈ Lb
  ·
    have hc4 : Nat.card B ≤ 4 := hcard B le_rfl hBL
    have h16 := hin t (hBL t htB) ht1 (hB2' t htB)
    have hle := index_zpowers_le_index B htB
    by_cases hc2 : Nat.card B ≤ 2
    · have : Nat.card B ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hc2 2
      omega
    · obtain ⟨t', ht'B, u, huB, ht'1, hu1, htu⟩ := exists_two_ne_one hc2
      have hB16 : (fixV B).index ≤ 2 ^ 4 :=
        hoff.trans ((Nat.pow_le_pow_left hc4 2).trans (by norm_num))
      have hfix : fixV B = fixV (Subgroup.zpowers t') :=
        fixV_eq_of_index_le ht'B (hB16.trans (hin t' (hBL t' ht'B) ht'1 (hB2' t' ht'B)))
      exact inner_four_false D hW hrep hφ hin (hBL t' ht'B) (hBL u huB) ht'1 hu1 htu
        (hB2' t' ht'B) (hB2' u huB) (hB2.1 t' ht'B u huB) (hfix ▸ fixV_le_fixV_zpowers huB)
        (hfix ▸ hB16)
  · push Not at hBL
    obtain ⟨b, hbB, hbL⟩ := hBL
    have h64 := hout b hbB hbL
    have hle := index_zpowers_le_index B hbB
    set T : Subgroup (MulAut W) := B ⊓ Lb with hT
    have hTB : T ≤ B := inf_le_left
    have hTL : T ≤ Lb := inf_le_right
    have hT4 : Nat.card T ≤ 4 := hcard T hTB hTL
    have hBT : Nat.card B ≤ 2 * Nat.card T := by
      let f : B → T ⊕ T := fun x =>
        if hx : (x : MulAut W) ∈ Lb then Sum.inl ⟨x, x.2, hx⟩
        else Sum.inr ⟨b * x, B.mul_mem hbB x.2, hidx b hbB x x.2 hbL hx⟩
      have hf : Function.Injective f := by
        intro x y hxy
        by_cases hx : (x : MulAut W) ∈ Lb <;> by_cases hy : (y : MulAut W) ∈ Lb
        · simp only [f, hx, hy, dite_true, Sum.inl.injEq] at hxy
          exact Subtype.ext (congrArg (fun z : T => (z : MulAut W)) hxy)
        · simp [f, hx, hy] at hxy
        · simp [f, hx, hy] at hxy
        · simp only [f, hx, hy, dite_false, Sum.inr.injEq] at hxy
          exact Subtype.ext (mul_left_cancel (congrArg (fun z : T => (z : MulAut W)) hxy))
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_sum, ← two_mul] at this
    by_cases hT2 : Nat.card T ≤ 2
    · have hB4 : Nat.card B ≤ 4 := by omega
      have : Nat.card B ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hB4 2
      omega
    · obtain ⟨t', ht'T, u, huT, ht'1, hu1, htu⟩ := exists_two_ne_one hT2
      have ht'B : t' ∈ B := hTB ht'T
      have huB : u ∈ B := hTB huT
      have ht'L : t' ∈ Lb := hTL ht'T
      have huL : u ∈ Lb := hTL huT
      have hB64 : (fixV B).index ≤ 2 ^ 6 :=
        hoff.trans ((Nat.pow_le_pow_left (show Nat.card B ≤ 8 by omega) 2).trans (by norm_num))
      have hout' : ∀ s ∈ Lb, b * s ∈ B → fixV B = fixV (Subgroup.zpowers (b * s)) := by
        intro s hsL hsB
        have hbsL : b * s ∉ Lb := fun h => hbL (by
          have := Lb.mul_mem h (Lb.inv_mem hsL)
          rwa [mul_inv_cancel_right] at this)
        exact fixV_eq_of_index_le hsB (hB64.trans (hout _ hsB hbsL))
      have hfb : fixV B = fixV (Subgroup.zpowers b) := fixV_eq_of_index_le hbB (hB64.trans h64)
      have hfbt := hout' t' ht'L (B.mul_mem hbB ht'B)
      have hfbu := hout' u huL (B.mul_mem hbB huB)
      rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN b hbB) (hB2' b hbB) with h | ⟨A, hA, hβ⟩
      · exact hbL h
      · exact outer_eight_false D hW hrep hφ hperfSL (hbN b hbB) A hA hβ ht'L huL ht'1 hu1 htu
          (hB2' t' ht'B) (hB2' u huB) (hB2.1 t' ht'B u huB) (hB2.1 b hbB t' ht'B)
          (hB2.1 b hbB u huB) (hfbt.symm.trans hfb) (hfbu.symm.trans hfb)
          (hfb ▸ fixV_le_fixV_zpowers ht'B) (hfb ▸ hB64)

end CFSG.Quasithin.B45Exc
