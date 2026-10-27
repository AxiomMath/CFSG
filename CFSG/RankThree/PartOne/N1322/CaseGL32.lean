module

public import CFSG.RankThree.PartOne.N1322.CasePair
public import CFSG.RankThree.PartOne.N1322.CaseInner
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.RankThree.PartOne.NF7H.StabSwap
public import CFSG.RankThree.PartOne.NF7H.SwapFin

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory
open CFSG.QuasithinUnique.Setup.Family (GL32 aut_GL32_cases center_GL32 slEquivGL)
open CFSG.LieType.SteinbergBR.AutGL32 (tau tau_val tau_mul_tau tau_mul_conj conj_injective)

abbrev Mat2 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem mat_orders9 : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] : Mat2).det = 1 →
    (!![a, b, c; d, e, f; g, h, i] : Mat2) ^ 4 = 1 ∨ (!![a, b, c; d, e, f; g, h, i] : Mat2) ^ 3 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Mat2) ^ 7 = 1 := by decide

theorem mat_orders (M : Mat2) (h : M.det = 1) : M ^ 4 = 1 ∨ M ^ 3 = 1 ∨ M ^ 7 = 1 := by
  have := mat_orders9 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2)
  rw [← Matrix.eta_fin_three M] at this
  exact this h

abbrev A0m : Mat2 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

theorem A0m_det : A0m.det = 1 := by decide

theorem mat_conj_invol : ∀ B : Mat2, B.det = 1 → B * B = 1 → B ≠ 1 →
    ∃ K : Mat2, K.det = 1 ∧ K * A0m = B * K := by
  decide +kernel

theorem mat_outer : ∀ S : Mat2, S.det = 1 → Sᵀ = S →
    ∃ X : Mat2, X.det = 1 ∧ X ^ 7 = 1 ∧ X ≠ 1 ∧ S * (X ^ 6)ᵀ = X ^ 6 * S := by
  decide +kernel

theorem mat_noncomm : ∃ A B : Mat2, A.det = 1 ∧ B.det = 1 ∧ A * B ≠ B * A := by
  decide +kernel

theorem det_GL32 (g : GL32) : (g : Mat2).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

@[expose] noncomputable def matUnit (M : Mat2) (h : M.det = 1) : GL32 :=
  ((Matrix.isUnit_iff_isUnit_det M).mpr (by rw [h]; exact isUnit_one)).unit

theorem matUnit_val (M : Mat2) (h : M.det = 1) : ((matUnit M h : GL32) : Mat2) = M := rfl

theorem G32_orders (g : GL32) : g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 7 = 1 := by
  rcases mat_orders (g : Mat2) (det_GL32 g) with h | h | h
  · left; apply Units.ext; rw [Units.val_pow_eq_pow_val, h]; rfl
  · right; left; apply Units.ext; rw [Units.val_pow_eq_pow_val, h]; rfl
  · right; right; apply Units.ext; rw [Units.val_pow_eq_pow_val, h]; rfl

theorem G32_conj_inv (a b : GL32) (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b * b = 1) (hb1 : b ≠ 1) :
    ∃ k : GL32, k * a * k⁻¹ = b := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : GL32, (a₀ : Mat2) = A0m := ⟨matUnit A0m A0m_det, rfl⟩
  have hinv : ∀ c : GL32, c * c = 1 → c ≠ 1 → ∃ k : GL32, k * a₀ * k⁻¹ = c := by
    intro c hc hc1
    have hsqc : (c : Mat2) * c = 1 := by
      have := congrArg (fun x : GL32 => (x : Mat2)) hc
      simpa using this
    have hnec : (c : Mat2) ≠ 1 := fun h => hc1 (Units.ext (by simpa using h))
    obtain ⟨K, hK, hKc⟩ := mat_conj_invol c (det_GL32 c) hsqc hnec
    obtain ⟨k, hk⟩ : ∃ k : GL32, (k : Mat2) = K := ⟨matUnit K hK, rfl⟩
    refine ⟨k, ?_⟩
    have h1 : k * a₀ = c * k := Units.ext (by rw [Units.val_mul, Units.val_mul, hk, ha₀]; exact hKc)
    rw [h1]
    group
  obtain ⟨ka, hka⟩ := hinv a ha ha1
  obtain ⟨kb, hkb⟩ := hinv b hb hb1
  refine ⟨kb * ka⁻¹, ?_⟩
  rw [← hka, ← hkb]
  group

theorem tau_eq_transpose (x : GL32) : ((tau x : GL32) : Mat2) = ((x⁻¹ : GL32) : Mat2)ᵀ := tau_val x

theorem G32_outer (s : GL32) (hs : s * tau s = 1) :
    ∃ x : GL32, x ^ 7 = 1 ∧ x ≠ 1 ∧ s * tau x * s⁻¹ = x⁻¹ := by
  have hts : tau s = s⁻¹ := eq_inv_of_mul_eq_one_right hs
  have h1 : ((s⁻¹ : GL32) : Mat2)ᵀ = ((s⁻¹ : GL32) : Mat2) := by
    rw [← tau_eq_transpose, hts]
  have h2 : ((s⁻¹ : GL32) : Mat2) * (s : Mat2) = 1 := Units.inv_mul s
  have h4 : (s : Mat2)ᵀ * ((s⁻¹ : GL32) : Mat2)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  rw [h1] at h4
  have hsym : (s : Mat2)ᵀ = s := by
    calc (s : Mat2)ᵀ = (s : Mat2)ᵀ * (((s⁻¹ : GL32) : Mat2) * (s : Mat2)) := by rw [h2, Matrix.mul_one]
      _ = ((s : Mat2)ᵀ * ((s⁻¹ : GL32) : Mat2)) * (s : Mat2) := (Matrix.mul_assoc _ _ _).symm
      _ = (s : Mat2) := by rw [h4, Matrix.one_mul]
  obtain ⟨X, hXdet, hX7, hX1, hXS⟩ := mat_outer (s : Mat2) (det_GL32 s) hsym
  obtain ⟨x, hxv⟩ : ∃ x : GL32, (x : Mat2) = X := ⟨matUnit X hXdet, rfl⟩
  have hx7 : x ^ 7 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hxv, hX7]; rfl)
  have hx1 : x ≠ 1 := fun h => hX1 (by
    have := congrArg (fun u : GL32 => (u : Mat2)) h
    simpa [hxv] using this)
  have hxinv : x⁻¹ = x ^ 6 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx7)
  refine ⟨x, hx7, hx1, ?_⟩
  have hxv6 : ((x ^ 6 : GL32) : Mat2) = X ^ 6 := by rw [Units.val_pow_eq_pow_val, hxv]
  have htx : ((tau x : GL32) : Mat2) = (X ^ 6)ᵀ := by rw [tau_eq_transpose, hxinv, hxv6]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, htx, hxinv, hxv6]
  calc (s : Mat2) * (X ^ 6)ᵀ * ((s⁻¹ : GL32) : Mat2) = X ^ 6 * (s : Mat2) * ((s⁻¹ : GL32) : Mat2) := by
        rw [hXS]
    _ = X ^ 6 * ((s : Mat2) * ((s⁻¹ : GL32) : Mat2)) := by rw [Matrix.mul_assoc]
    _ = X ^ 6 := by rw [Units.mul_inv, Matrix.mul_one]

theorem G32_noncomm : ∃ a b : GL32, a * b ≠ b * a := by
  obtain ⟨A, B, hA, hB, hAB⟩ := mat_noncomm
  obtain ⟨a, ha⟩ : ∃ a : GL32, (a : Mat2) = A := ⟨matUnit A hA, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : GL32, (b : Mat2) = B := ⟨matUnit B hB, rfl⟩
  refine ⟨a, b, fun h => hAB ?_⟩
  have := congrArg (fun u : GL32 => (u : Mat2)) h
  simpa [ha, hb] using this

theorem isPerfect_GL32 : Group.IsPerfect GL32 := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  exact Group.IsPerfect.ofSurjective (f := (slEquivGL 3).toMonoidHom) (slEquivGL 3).surjective

theorem refl_inner_of_gl32 {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hnorm : ∀ g ∈ d.X, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hHX : H ≤ d.X) (e : H ≃* GL32) {t : GL (Fin 3) (ZMod p)} (htD : t ∈ d.D) :
    ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹ := by
  have htX : t ∈ d.X := mem_X_of_mem_D h htD
  have ht2 : t * t = 1 := (h.refl t htD).sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨a, ha⟩ : ∃ a : H ≃* H, ∀ x : H, ((a x : H) : GL (Fin 3) (ZMod p)) = t * x * t⁻¹ :=
    ⟨actOn hnorm htX, fun x => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : MulAut GL32, ∀ x : H, β (e x) = e (a x) :=
    ⟨(e.symm.trans a).trans e, fun x => by simp⟩
  have hββ : β * β = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [MulAut.mul_apply, hβ, hβ, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [ha, ha, htinv]
    calc t * (t * (x : GL (Fin 3) (ZMod p)) * t) * t
        = (t * t) * (x : GL (Fin 3) (ZMod p)) * (t * t) := by group
      _ = x := by rw [ht2]; group
  rcases aut_GL32_cases β with ⟨s, hs⟩ | ⟨s, hs⟩
  · refine ⟨((e.symm s : H) : GL (Fin 3) (ZMod p)), (e.symm s).2, fun x hx => ?_⟩
    have h1 := congrArg (fun φ : MulAut GL32 => φ (e ⟨x, hx⟩)) hs
    simp only [hβ, MulAut.conj_apply] at h1
    have h2 : a ⟨x, hx⟩ = e.symm s * ⟨x, hx⟩ * (e.symm s)⁻¹ := by
      apply e.injective
      rw [h1]
      simp
    have h3 := congrArg Subtype.val h2
    rw [ha] at h3
    simpa using h3
  · exfalso
    have hss : s * tau s = 1 := by
      have h1 : MulAut.conj (s * tau s) = 1 := by
        calc MulAut.conj (s * tau s) = MulAut.conj s * MulAut.conj (tau s) := map_mul _ _ _
          _ = MulAut.conj s * MulAut.conj (tau s) * (tau * tau) := by rw [tau_mul_tau, mul_one]
          _ = MulAut.conj s * (MulAut.conj (tau s) * tau) * tau := by simp only [mul_assoc]
          _ = MulAut.conj s * (tau * MulAut.conj s) * tau := by rw [tau_mul_conj]
          _ = (MulAut.conj s * tau) * (MulAut.conj s * tau) := by simp only [mul_assoc]
          _ = 1 := by rw [← hs]; exact hββ
      exact conj_injective (by rw [h1, map_one])
    obtain ⟨x, hx7, hx1, hxinv⟩ := G32_outer s hss
    have hβx : β x = x⁻¹ := by
      rw [hs, MulAut.mul_apply, MulAut.conj_apply]
      exact hxinv
    obtain ⟨x', hx'⟩ : ∃ x' : H, e x' = x := ⟨e.symm x, e.apply_symm_apply x⟩
    have hx'7 : (x' : GL (Fin 3) (ZMod p)) ^ 7 = 1 := by
      have : x' ^ 7 = 1 := by
        apply e.injective
        rw [map_pow, hx', map_one]
        exact hx7
      simpa using congrArg Subtype.val this
    have hx'1 : (x' : GL (Fin 3) (ZMod p)) ≠ 1 := by
      intro h1
      apply hx1
      have : x' = 1 := Subtype.ext (by simpa using h1)
      rw [← hx', this, map_one]
    have hconj : t * (x' : GL (Fin 3) (ZMod p)) * t⁻¹ = (x' : GL (Fin 3) (ZMod p))⁻¹ := by
      have h1 : e (a x') = e x'⁻¹ := by
        rw [← hβ, hx', hβx, map_inv, hx']
      have h2 : a x' = x'⁻¹ := e.injective h1
      have h3 := congrArg Subtype.val h2
      rw [ha] at h3
      simpa using h3
    have hx'X : (x' : GL (Fin 3) (ZMod p)) ∈ d.X := hHX x'.2
    have ht'D : (x' : GL (Fin 3) (ZMod p)) * t * (x' : GL (Fin 3) (ZMod p))⁻¹ ∈ d.D :=
      h.Dconj _ hx'X t htD
    have hko := h.kO t htD _ ht'D
    have hprod : t * ((x' : GL (Fin 3) (ZMod p)) * t * (x' : GL (Fin 3) (ZMod p))⁻¹) =
        ((x' : GL (Fin 3) (ZMod p))⁻¹) ^ 2 := by
      calc t * ((x' : GL (Fin 3) (ZMod p)) * t * (x' : GL (Fin 3) (ZMod p))⁻¹)
          = (t * (x' : GL (Fin 3) (ZMod p)) * t) * (x' : GL (Fin 3) (ZMod p))⁻¹ := by group
        _ = (t * (x' : GL (Fin 3) (ZMod p)) * t⁻¹) * (x' : GL (Fin 3) (ZMod p))⁻¹ := by rw [htinv]
        _ = (x' : GL (Fin 3) (ZMod p))⁻¹ * (x' : GL (Fin 3) (ZMod p))⁻¹ := by rw [hconj]
        _ = ((x' : GL (Fin 3) (ZMod p))⁻¹) ^ 2 := (sq _).symm
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hord : orderOf (x' : GL (Fin 3) (ZMod p)) = 7 := orderOf_eq_prime hx'7 hx'1
    have hord2 : orderOf (((x' : GL (Fin 3) (ZMod p))⁻¹) ^ 2) = 7 := by
      rw [Nat.Coprime.orderOf_pow (by rw [orderOf_inv, hord]; norm_num), orderOf_inv, hord]
    rw [hprod, hord2] at hko
    have := hko (by decide)
    omega

theorem case4_false {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHX : H ≤ d.X)
    (hnorm : ∀ g ∈ d.X, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (e : H ≃* GL32) : False := by
  have h4 := four_ne_zero_of_five_le h.p5
  have : Group.IsPerfect GL32 := isPerfect_GL32
  have : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 :=
    fun x hx => det_eq_one_of_perfect hx
  have hZ3 : ∀ z ∈ H, (∀ g : GL (Fin 3) (ZMod p), g * z = z * g) → z ^ 3 = 1 := by
    intro z hz hc
    have hz1 : z = 1 := by
      have hmem : e ⟨z, hz⟩ ∈ Subgroup.center GL32 := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨w, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hc w)
      rw [center_GL32, Subgroup.mem_bot] at hmem
      have := e.injective (hmem.trans (map_one e).symm)
      exact congrArg Subtype.val this
    rw [hz1]
    simp
  have hsch := scalar_commutant_of_noncomm hirr (by
    obtain ⟨x, y, hxy⟩ := G32_noncomm
    refine ⟨(e.symm x : GL (Fin 3) (ZMod p)), (e.symm x).2, (e.symm y : GL (Fin 3) (ZMod p)),
      (e.symm y).2, fun hc => hxy ?_⟩
    have h1 : e.symm (x * y) = e.symm (y * x) := by
      rw [map_mul, map_mul]
      exact Subtype.ext hc
    exact e.symm.injective h1)
  obtain ⟨ρ, t₀, hg, ht₀D, hs₀D⟩ := exists_refl_pair h
  obtain ⟨h₁, hh₁, hin₁⟩ := refl_inner_of_gl32 h hnorm hHX e ht₀D
  obtain ⟨a₁, ha₁, ha₁sq, ht₁⟩ := refl_neg_of_inner hdet hZ3 hsch (h.refl _ ht₀D) hh₁ hin₁
  obtain ⟨h₂, hh₂, hin₂⟩ := refl_inner_of_gl32 h hnorm hHX e hs₀D
  obtain ⟨a₂, ha₂, ha₂sq, ht₂⟩ := refl_neg_of_inner hdet hZ3 hsch (h.refl _ hs₀D) hh₂ hin₂
  have hprod : (t₀ : GL (Fin 3) (ZMod p)) * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) =
      (ρ : GL (Fin 3) (ZMod p)) := by
    have := congrArg Subtype.val (show t₀ * (t₀ * ρ) = ρ by rw [← mul_assoc, hg.sq, one_mul])
    simpa using this
  have hmul : a₁ * a₂ = (ρ : GL (Fin 3) (ZMod p)) := by
    calc a₁ * a₂ = ((-1 : GL (Fin 3) (ZMod p)) * (-1)) * a₁ * a₂ := by
          rw [neg_one_mul_neg_one, one_mul]
      _ = (-1) * ((-1) * a₁) * a₂ := by group
      _ = (-1) * (a₁ * (-1)) * a₂ := by rw [neg_one_comm a₁]
      _ = ((-1) * a₁) * ((-1) * a₂) := by group
      _ = (t₀ : GL (Fin 3) (ZMod p)) * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) := by
          rw [← ht₁, ← ht₂]
      _ = ρ := hprod
  have hmem : a₁ * a₂ ∈ H := H.mul_mem ha₁ ha₂
  have hord : orderOf (a₁ * a₂) = d.n := by
    rw [hmul, ← hg.ord]
    exact Subgroup.orderOf_coe ρ
  have hord' : orderOf (e ⟨a₁ * a₂, hmem⟩) = d.n := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hord]
  have hn4 : d.n = 4 := by
    have hdiv : d.n ∣ 4 ∨ d.n ∣ 3 ∨ d.n ∣ 7 := by
      rcases G32_orders (e ⟨a₁ * a₂, hmem⟩) with hp | hp | hp
      · left; rw [← hord']; exact orderOf_dvd_of_pow_eq_one hp
      · right; left; rw [← hord']; exact orderOf_dvd_of_pow_eq_one hp
      · right; right; rw [← hord']; exact orderOf_dvd_of_pow_eq_one hp
    rcases h.n_mem with hn | hn | hn
    · exact hn
    · rw [hn] at hdiv; omega
    · rw [hn] at hdiv; omega
  have hinv1 : ∀ (a : GL (Fin 3) (ZMod p)) (ha : a ∈ H), a * a = 1 →
      (-1 : GL (Fin 3) (ZMod p)) * a ∈ d.D → e ⟨a, ha⟩ ≠ 1 := by
    intro a ha hsq hD h1
    have h2 : (⟨a, ha⟩ : H) = 1 := e.injective (h1.trans (map_one e).symm)
    have h3 : a = 1 := congrArg Subtype.val h2
    apply IsRefl.ne_neg_one h4 (h.refl _ hD)
    rw [h3, mul_one]
    simp
  have hD₁ : (-1 : GL (Fin 3) (ZMod p)) * a₁ ∈ d.D := by rw [← ht₁]; exact ht₀D
  have hD₂ : (-1 : GL (Fin 3) (ZMod p)) * a₂ ∈ d.D := by rw [← ht₂]; exact hs₀D
  have hi₁ : e ⟨a₁, ha₁⟩ * e ⟨a₁, ha₁⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a₁, ha₁⟩ : H) * ⟨a₁, ha₁⟩ = 1 := Subtype.ext ha₁sq
    rw [this, map_one]
  have hi₂ : e ⟨a₂, ha₂⟩ * e ⟨a₂, ha₂⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a₂, ha₂⟩ : H) * ⟨a₂, ha₂⟩ = 1 := Subtype.ext ha₂sq
    rw [this, map_one]
  obtain ⟨k, hk⟩ := G32_conj_inv _ _ hi₁ (hinv1 a₁ ha₁ ha₁sq hD₁) hi₂ (hinv1 a₂ ha₂ ha₂sq hD₂)
  obtain ⟨kH, hkH⟩ : ∃ kH : H, e kH = k := ⟨e.symm k, e.apply_symm_apply k⟩
  have hk' : (kH : GL (Fin 3) (ZMod p)) * a₁ * (kH : GL (Fin 3) (ZMod p))⁻¹ = a₂ := by
    have h1 : e (kH * ⟨a₁, ha₁⟩ * kH⁻¹) = e ⟨a₂, ha₂⟩ := by
      rw [map_mul, map_mul, map_inv, hkH, hk]
    have h2 := e.injective h1
    simpa using congrArg Subtype.val h2
  have hDall : ∀ t ∈ d.D, ∃ a ∈ H, a * a = 1 ∧ a ≠ 1 ∧ t = (-1 : GL (Fin 3) (ZMod p)) * a := by
    intro t htD
    obtain ⟨h₀, hh₀, hin⟩ := refl_inner_of_gl32 h hnorm hHX e htD
    obtain ⟨a, ha, hasq, hta⟩ := refl_neg_of_inner hdet hZ3 hsch (h.refl _ htD) hh₀ hin
    refine ⟨a, ha, hasq, fun ha1 => ?_, hta⟩
    exact IsRefl.ne_neg_one h4 (h.refl _ htD) (by rw [hta, ha1, mul_one]; simp)
  have hDall' : ∀ a ∈ H, a * a = 1 → a ≠ 1 → (-1 : GL (Fin 3) (ZMod p)) * a ∈ d.D := by
    intro a ha hasq ha1
    have hia : e ⟨a, ha⟩ * e ⟨a, ha⟩ = 1 := by
      rw [← map_mul]
      have : (⟨a, ha⟩ : H) * ⟨a, ha⟩ = 1 := Subtype.ext hasq
      rw [this, map_one]
    have hna : e ⟨a, ha⟩ ≠ 1 := by
      intro h1
      exact ha1 (congrArg Subtype.val (e.injective (h1.trans (map_one e).symm)))
    obtain ⟨kk, hkk⟩ := G32_conj_inv _ _ hi₁ (hinv1 a₁ ha₁ ha₁sq hD₁) hia hna
    obtain ⟨kH', hkH'⟩ : ∃ kH' : H, e kH' = kk := ⟨e.symm kk, e.apply_symm_apply kk⟩
    have hka : (kH' : GL (Fin 3) (ZMod p)) * a₁ * (kH' : GL (Fin 3) (ZMod p))⁻¹ = a := by
      have h1 : e (kH' * ⟨a₁, ha₁⟩ * kH'⁻¹) = e ⟨a, ha⟩ := by
        rw [map_mul, map_mul, map_inv, hkH', hkk]
      have h2 := e.injective h1
      simpa using congrArg Subtype.val h2
    have hmemD := h.Dconj _ (hHX kH'.2) _ hD₁
    have heq : (kH' : GL (Fin 3) (ZMod p)) * ((-1 : GL (Fin 3) (ZMod p)) * a₁) *
        (kH' : GL (Fin 3) (ZMod p))⁻¹ = (-1) * a := by
      calc (kH' : GL (Fin 3) (ZMod p)) * ((-1) * a₁) * (kH' : GL (Fin 3) (ZMod p))⁻¹
          = ((kH' : GL (Fin 3) (ZMod p)) * (-1)) * a₁ * (kH' : GL (Fin 3) (ZMod p))⁻¹ := by
            simp only [mul_assoc]
        _ = ((-1) * (kH' : GL (Fin 3) (ZMod p))) * a₁ * (kH' : GL (Fin 3) (ZMod p))⁻¹ := by
            rw [← neg_one_comm (kH' : GL (Fin 3) (ZMod p))]
        _ = (-1) * ((kH' : GL (Fin 3) (ZMod p)) * a₁ * (kH' : GL (Fin 3) (ZMod p))⁻¹) := by
            simp only [mul_assoc]
        _ = (-1) * a := by rw [hka]
    rw [← heq]
    exact hmemD
  have hprod' : e ⟨a₁ * a₂, hmem⟩ = e ⟨a₁, ha₁⟩ * e ⟨a₂, ha₂⟩ := map_mul e ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
  have hab4 : (e ⟨a₁, ha₁⟩ * e ⟨a₂, ha₂⟩) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (e ⟨a₁ * a₂, hmem⟩)
    rwa [hord', hn4, hprod'] at this
  have hab2 : (e ⟨a₁, ha₁⟩ * e ⟨a₂, ha₂⟩) ^ 2 ≠ 1 := by
    intro h1
    rw [← hprod'] at h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord', hn4] at this
    omega
  have hns : ¬ ∃ μ : ZMod p, ((kH : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ d.c =
      μ • d.c := by
    intro hstab
    obtain ⟨j, hj⟩ := NF7H.stab_swap_form h hn4 hg
      (NF7H.neg_one_not_mem (two_ne_zero_of_five_le h.p5) hZ3) ha₁ ha₂ kH.2 (hHX kH.2) ht₁ ht₂ hmul
      hstab
    refine NF7H.GL32_swap_false (a := e ⟨a₁, ha₁⟩) (b := e ⟨a₂, ha₂⟩) (k := e kH) hi₁ hi₂ hab4 hab2
      (by rw [hkH]; exact hk) j ?_
    have h1 : kH * (⟨a₂, ha₂⟩ : H) * kH⁻¹ =
        ⟨a₁, ha₁⟩ * (⟨a₁, ha₁⟩ * ⟨a₂, ha₂⟩) ^ (j : ℕ) := Subtype.ext (by simpa using hj)
    have h2 := congrArg e h1
    simpa only [map_mul, map_inv, map_pow] using h2
  rcases h.kAL with hkA | hL32
  · refine pair_not_X_conj hkA hn4 hg ht₀D hs₀D (k := (kH : GL (Fin 3) (ZMod p))) (hHX kH.2) hns ?_
    rw [ht₁, ht₂]
    calc (kH : GL (Fin 3) (ZMod p)) * ((-1) * a₁) * (kH : GL (Fin 3) (ZMod p))⁻¹
        = ((kH : GL (Fin 3) (ZMod p)) * (-1)) * a₁ * (kH : GL (Fin 3) (ZMod p))⁻¹ := by
          simp only [mul_assoc]
      _ = ((-1) * (kH : GL (Fin 3) (ZMod p))) * a₁ * (kH : GL (Fin 3) (ZMod p))⁻¹ := by
          rw [← neg_one_comm (kH : GL (Fin 3) (ZMod p))]
      _ = (-1) * ((kH : GL (Fin 3) (ZMod p)) * a₁ * (kH : GL (Fin 3) (ZMod p))⁻¹) := by
          simp only [mul_assoc]
      _ = (-1) * a₂ := by rw [hk']
  · exact hL32 H hHX e hDall hDall'

end CFSG.RankThree.PartOne.N1322
