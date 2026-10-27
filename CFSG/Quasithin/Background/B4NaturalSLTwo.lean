module

public import CFSG.Quasithin.Background.G64Realize
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {V : Type*} [CommGroup V]

private theorem exists_coeff_of_specialLinear_two {K : Type} [Field K]
    (b : Module.Basis (Fin 2) K (Fin 2 → K)) {v : Fin 2 → K} (hb1 : b 1 = v)
    {A : Matrix (Fin 2) (Fin 2) K} (hAdet : A.det = 1) (hA1 : A ≠ 1)
    (hAv : A *ᵥ v = v) :
    ∃ a : K, a ≠ 0 ∧ ∀ x : Fin 2 → K,
      A *ᵥ x = x + (a * (b.coord 0) x) • v := by
  classical
  let L : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := Matrix.toLin' A
  let M : Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrix b b L
  have hLv : L v = v := by rw [show L v = A *ᵥ v from Matrix.toLin'_apply A v, hAv]
  have hMdet : M.det = 1 := by
    rw [show M = LinearMap.toMatrix b b L from rfl, LinearMap.det_toMatrix,
      show L = Matrix.toLin' A from rfl, LinearMap.det_toLin', hAdet]
  have hM01 : M 0 1 = 0 := by
    rw [show M = LinearMap.toMatrix b b L from rfl, LinearMap.toMatrix_apply, hb1, hLv,
      ← hb1, Module.Basis.repr_self]
    simp
  have hM11 : M 1 1 = 1 := by
    rw [show M = LinearMap.toMatrix b b L from rfl, LinearMap.toMatrix_apply, hb1, hLv,
      ← hb1, Module.Basis.repr_self]
    simp
  have hM00 : M 0 0 = 1 := by
    have hdet := hMdet
    rw [Matrix.det_fin_two] at hdet
    rw [hM01, hM11, mul_one, zero_mul, sub_zero] at hdet
    exact hdet
  have hLb0 : L (b 0) = b 0 + M 1 0 • v := by
    have hrepr := LinearMap.toMatrix_mulVec_repr b b L (b 0)
    rw [show (LinearMap.toMatrix b b L) = M from rfl] at hrepr
    have hreprw : b.repr (b 0) = Finsupp.single 0 1 := by
      rw [Module.Basis.repr_self]
    rw [hreprw] at hrepr
    have h0 : b.repr (L (b 0)) 0 = 1 := by
      rw [← hrepr]
      simp [hM00]
    have h1 : b.repr (L (b 0)) 1 = M 1 0 := by
      rw [← hrepr]
      simp
    conv_lhs => rw [← b.sum_repr (L (b 0))]
    rw [Fin.sum_univ_two, h0, h1, hb1, one_smul]
  let φ : (Fin 2 → K) →ₗ[K] K := b.coord 0
  have hφv : φ v = 0 := by
    rw [show φ = b.coord 0 from rfl, Module.Basis.coord_apply, ← hb1, Module.Basis.repr_self]
    simp
  have hφb0 : φ (b 0) = 1 := by
    rw [show φ = b.coord 0 from rfl, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp
  have hact_lin : Matrix.toLin' A =
      LinearMap.id + (LinearMap.toSpanSingleton K (Fin 2 → K) v).comp
        ((M 1 0 : K) • φ) := by
    apply Module.Basis.ext b
    intro i
    fin_cases i
    · change (Matrix.toLin' A) (b 0) =
        ((LinearMap.id + (LinearMap.toSpanSingleton K (Fin 2 → K) v).comp
          ((M 1 0 : K) • φ)) : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) (b 0)
      change L (b 0) = b 0 + (M 1 0 • φ (b 0)) • v
      rw [hLb0, hφb0]
      simp
    · change (Matrix.toLin' A) (b 1) =
        ((LinearMap.id + (LinearMap.toSpanSingleton K (Fin 2 → K) v).comp
          ((M 1 0 : K) • φ)) : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) (b 1)
      rw [hb1]
      change L v = v + (M 1 0 • φ v) • v
      rw [hLv, hφv]
      simp
  have hact : ∀ x, A *ᵥ x = x + (M 1 0 * φ x) • v := by
    intro x
    have h := congrArg (fun f : (Fin 2 → K) →ₗ[K] (Fin 2 → K) => f x) hact_lin
    simpa [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.toSpanSingleton_apply, Matrix.toLin'_apply, smul_eq_mul] using h
  have ha : M 1 0 ≠ 0 := by
    intro h0
    apply hA1
    have hM1 : M = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hM00, hM01, h0, hM11]
    have hL1 : L = 1 := (LinearMap.toMatrix b b).injective (by simpa using hM1)
    have hAx : ∀ x, A *ᵥ x = x := by
      intro x
      rw [← Matrix.toLin'_apply A x]
      exact congrArg (fun f : (Fin 2 → K) →ₗ[K] (Fin 2 → K) => f x) hL1
    ext i j
    have h := congrFun (hAx (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h
  exact ⟨M 1 0, ha, fun x => by simpa [φ] using hact x⟩

theorem exists_common_functional_of_specialLinear_two {K : Type} [Field K]
    {A B : Matrix (Fin 2) (Fin 2) K} (hAdet : A.det = 1) (hBdet : B.det = 1)
    (hA1 : A ≠ 1) (hB1 : B ≠ 1) {v : Fin 2 → K} (hv : v ≠ 0)
    (hAv : A *ᵥ v = v) (hBv : B *ᵥ v = v) :
    ∃ (φ : (Fin 2 → K) →ₗ[K] K) (a b : K), a ≠ 0 ∧ b ≠ 0 ∧ φ v = 0 ∧
      (∃ w, φ w = 1) ∧ (∀ x, φ x = 0 ↔ x ∈ Submodule.span K {v}) ∧
      (∀ x, A *ᵥ x = x + (a * φ x) • v) ∧
      (∀ x, B *ᵥ x = x + (b * φ x) • v) := by
  classical
  have hw : ∃ w : Fin 2 → K, w ∉ Submodule.span K {v} := by
    by_contra h
    push Not at h
    have htop : Submodule.span K {v} = ⊤ := Submodule.eq_top_iff'.2 h
    have hdim : Module.finrank K (Submodule.span K {v}) = 1 := finrank_span_singleton hv
    rw [htop, finrank_top K (Fin 2 → K), Module.finrank_fin_fun] at hdim
    omega
  obtain ⟨w, hw⟩ := hw
  have hli : LinearIndependent K ![w, v] := by
    rw [linearIndependent_fin2]
    exact ⟨hv, fun a ha => hw (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)⟩
  let b : Module.Basis (Fin 2) K (Fin 2 → K) :=
    basisOfLinearIndependentOfCardEqFinrank' ![w, v] hli (by simp)
  have hb0 : b 0 = w := by simp [b]
  have hb1 : b 1 = v := by simp [b]
  obtain ⟨a, ha, hAact⟩ := exists_coeff_of_specialLinear_two b hb1 hAdet hA1 hAv
  obtain ⟨bcoef, hb, hBact⟩ := exists_coeff_of_specialLinear_two b hb1 hBdet hB1 hBv
  let φ : (Fin 2 → K) →ₗ[K] K := b.coord 0
  have hφv : φ v = 0 := by
    rw [show φ = b.coord 0 from rfl, Module.Basis.coord_apply, ← hb1, Module.Basis.repr_self]
    simp
  have hφw : φ w = 1 := by
    rw [show φ = b.coord 0 from rfl, Module.Basis.coord_apply, ← hb0, Module.Basis.repr_self]
    simp
  have hφker : ∀ x, φ x = 0 ↔ x ∈ Submodule.span K {v} := by
    intro x
    constructor
    · intro hx
      have hx' : (b.coord 0) x = 0 := by
        simpa [show φ = b.coord 0 from rfl] using hx
      have hx0 : b.repr x 0 = 0 := by
        simpa [Module.Basis.coord_apply] using hx'
      rw [← b.sum_repr x]
      rw [Fin.sum_univ_two, hx0, hb0, hb1, zero_smul, zero_add]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
    · intro hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_smul, hφv, smul_zero]
  exact ⟨φ, a, bcoef, ha, hb, hφv, ⟨w, hφw⟩, hφker,
    fun x => by simpa [φ] using hAact x, fun x => by simpa [φ] using hBact x⟩

theorem card_fixed_eq_of_specialLinear_two {K : Type} [Field K] [Finite K]
    {A : Matrix (Fin 2) (Fin 2) K} (hAdet : A.det = 1) (hA1 : A ≠ 1)
    {v : Fin 2 → K} (hv : v ≠ 0) (hAv : A *ᵥ v = v) :
    Nat.card {x : Fin 2 → K // A *ᵥ x = x} = Nat.card K := by
  obtain ⟨φ, a, b, ha, hb, hφv, ⟨w, hφw⟩, hφker, hAact, -⟩ :=
    exists_common_functional_of_specialLinear_two hAdet hAdet hA1 hA1 hv hAv hAv
  have hfixed : ∀ x : Fin 2 → K, (A *ᵥ x = x) ↔ φ x = 0 := by
    intro x
    rw [hAact x]
    constructor
    · intro h
      have h1 : (a * φ x) • v = 0 := by
        have h' : x + (a * φ x) • v = x + 0 := by simpa using h
        simpa using (add_left_cancel h')
      rcases smul_eq_zero.mp h1 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 ha
        · exact h3
      · exact absurd h2 hv
    · intro h
      simp [h]
  let e : {x : Fin 2 → K // A *ᵥ x = x} ≃ LinearMap.ker φ :=
    Equiv.subtypeEquivRight fun x => by
      rw [LinearMap.mem_ker]
      exact hfixed x
  have hker : LinearMap.ker φ = Submodule.span K {v} := by
    ext x
    rw [LinearMap.mem_ker, hφker x]
  calc Nat.card {x : Fin 2 → K // A *ᵥ x = x}
      = Nat.card (LinearMap.ker φ) := Nat.card_congr e
    _ = Nat.card (Submodule.span K {v}) := by rw [hker]
    _ = Nat.card K := by
        letI : Fintype K := Fintype.ofFinite K
        letI : Fintype (Submodule.span K {v}) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card (α := Submodule.span K {v}),
          Nat.card_eq_fintype_card (α := K),
          Module.card_eq_pow_finrank (K := K) (V := Submodule.span K {v}),
          finrank_span_singleton hv, pow_one]

private theorem exists_coordinates {H : Subgroup (MulAut V)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 2 n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (e : V ≃* Multiplicative (Fin 2 → K))
        (A : H → Matrix.SpecialLinearGroup (Fin 2) K),
        (∀ h : H, (A h : Matrix (Fin 2) (Fin 2) K).det = 1) ∧
        (∀ (h : H), h ≠ 1 → (A h : Matrix (Fin 2) (Fin 2) K) ≠ 1) ∧
        ∀ (h : H) (w : V), e ((h : MulAut V) w) = Multiplicative.ofAdd
          ((A h : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd (e w)) := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, π, hreal⟩ := hH
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.nat (StatedSL 2 K)) rfl hreal
  let e : V ≃* Multiplicative (Fin 2 → K) :=
    E.trans (Subgroup.topEquiv : ↥(FFModel.nat (StatedSL 2 K)).sec ≃*
      (FFModel.nat (StatedSL 2 K)).Amb)
  have he : ∀ (γ : ↥(StatedSL 2 K)) (v : V),
      e (((π γ : ↥H) : MulAut V) v) = Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          Multiplicative.toAdd (e v)) := by
    intro γ v
    change ((E (((π γ : ↥H) : MulAut V) v) : ↥(FFModel.nat (StatedSL 2 K)).sec) :
      (FFModel.nat (StatedSL 2 K)).Amb) = Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          Multiplicative.toAdd ((E v : ↥(FFModel.nat (StatedSL 2 K)).sec) :
            (FFModel.nat (StatedSL 2 K)).Amb))
    exact hE γ v
  let γ : H → ↥(StatedSL 2 K) := fun h => Classical.choose (hreal.1 h)
  have hγ : ∀ h : H, π (γ h) = h := fun h => Classical.choose_spec (hreal.1 h)
  let A : H → Matrix.SpecialLinearGroup (Fin 2) K := fun h =>
    (specialLinearGroupEquivStatedSL 2 K).symm (γ h)
  have hAcoe : ∀ h : H, γ h = specialLinearGroupEquivStatedSL 2 K (A h) := fun h =>
    ((specialLinearGroupEquivStatedSL 2 K).apply_symm_apply (γ h)).symm
  have hAdet : ∀ h : H, (A h : Matrix (Fin 2) (Fin 2) K).det = 1 := fun h =>
    Matrix.SpecialLinearGroup.det_coe (A h)
  have hAne : ∀ (h : H), h ≠ 1 → (A h : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro h hh hA
    apply hh
    have hAeq : A h = 1 := Subtype.ext hA
    have hγ1 : γ h = 1 := by rw [hAcoe h, hAeq]; exact map_one _
    have h1 : π (γ h) = 1 := by rw [hγ1]; exact map_one π
    rw [hγ h] at h1
    exact h1
  have hact : ∀ (h : H) (w : V), e ((h : MulAut V) w) = Multiplicative.ofAdd
      ((A h : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd (e w)) := by
    intro h w
    have h2 : ((π (γ h) : ↥H) : MulAut V) = (h : MulAut V) := by rw [hγ h]
    have h1 : e ((h : MulAut V) w) = Multiplicative.ofAdd
        (((γ h : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) *ᵥ
          Multiplicative.toAdd (e w)) := by
      refine (congrArg (fun g : MulAut V => e (g w)) h2).symm.trans ?_
      exact he (γ h) w
    rw [hAcoe h, specialLinearGroupEquivStatedSL_coe] at h1
    exact h1
  exact ⟨K, hKfield, hKfin, hKcard, e, A, hAdet, hAne, hact⟩

theorem BinaryNaturalSL.card_fixed_eq {H : Subgroup (MulAut V)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 2 n) {s : MulAut V} (hs : s ∈ H) (hs1 : s ≠ 1)
    {z : V} (hz : z ≠ 1) (hsz : s z = z) :
    Nat.card {v : V // s v = v} = 2 ^ n := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, e, A, hAdet, hAne, hact⟩ := exists_coordinates hH
  letI : Field K := hKfield
  letI : Finite K := hKfin
  let sH : H := ⟨s, hs⟩
  have hsH1 : sH ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  let As : Matrix.SpecialLinearGroup (Fin 2) K := A sH
  have hAsdet : (As : Matrix (Fin 2) (Fin 2) K).det = 1 := hAdet sH
  have hAs1 : (As : Matrix (Fin 2) (Fin 2) K) ≠ 1 := hAne sH hsH1
  let v : Fin 2 → K := Multiplicative.toAdd (e z)
  have hv : v ≠ 0 := by
    intro h0
    apply hz
    have h1 : Multiplicative.ofAdd v = 1 := by rw [h0]; rfl
    simpa [v] using h1
  have hAv : (As : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
    have h1 := hact sH z
    rw [show ((sH : H) : MulAut V) z = z from hsz] at h1
    have h2 : Multiplicative.ofAdd ((As : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        Multiplicative.ofAdd v := by
      simpa [As, v] using h1.symm
    exact Multiplicative.ofAdd.injective h2
  let e' : V ≃ (Fin 2 → K) := e.toEquiv.trans Multiplicative.toAdd
  have hiff : ∀ x : V, s x = x ↔ (As : Matrix (Fin 2) (Fin 2) K) *ᵥ e' x = e' x := by
    intro x
    have h1 := hact sH x
    constructor
    · intro hx
      have h2 : Multiplicative.ofAdd ((As : Matrix (Fin 2) (Fin 2) K) *ᵥ e' x) =
          Multiplicative.ofAdd (e' x) := by
        have h3 := h1.symm.trans (congrArg e hx)
        simpa [As, e'] using h3
      exact Multiplicative.ofAdd.injective h2
    · intro hx
      apply e.injective
      rw [h1]
      change Multiplicative.ofAdd ((As : Matrix (Fin 2) (Fin 2) K) *ᵥ e' x) = e x
      rw [hx]
      simp [e']
  calc Nat.card {x : V // s x = x}
      = Nat.card {x : Fin 2 → K // (As : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x} :=
        Nat.card_congr (Equiv.subtypeEquiv e' hiff)
    _ = Nat.card K := card_fixed_eq_of_specialLinear_two hAsdet hAs1 hv hAv
    _ = 2 ^ n := hKcard

private theorem eq_one_of_pow_two_pow_eq_one {K : Type} [Field K] [Finite K] {n k : ℕ}
    (hKcard : Nat.card K = 2 ^ n) {c : K} (hcne : c ≠ 0) (hcpow : c ^ (2 ^ k) = 1) :
    c = 1 := by
  let u : Kˣ := Units.mk0 c hcne
  have horder : orderOf u ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    apply Units.ext
    simp [u, hcpow]
  have horderK : orderOf u ∣ Nat.card K - 1 := by
    have h := orderOf_dvd_natCard u
    rwa [Nat.card_units] at h
  have hn1 : 1 ≤ n := by
    by_contra h0
    have hzero : n = 0 := by omega
    rw [hzero, pow_zero] at hKcard
    have hlt : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨t, ht, ht1⟩ : ∃ t, 2 ^ n = 2 * t ∧ 1 ≤ t :=
      ⟨2 ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel hn1], Nat.one_le_two_pow⟩
    exact ⟨t - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K - 1) := by
    rw [hKcard]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  have hdvd1 : orderOf u ∣ 1 := by
    have h := Nat.dvd_gcd horder horderK
    rwa [Nat.coprime_iff_gcd_eq_one.mp hcop] at h
  have hu1 : u = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  exact Units.ext_iff.mp hu1

private theorem fixed_mul_inv_final {K : Type} [Field K]
    {e : V ≃* Multiplicative (Fin 2 → K)} {s f : MulAut V}
    {A : Matrix (Fin 2) (Fin 2) K} {v : Fin 2 → K}
    (Fadd : (Fin 2 → K) →+ (Fin 2 → K))
    (hFapply : ∀ x, Fadd x =
      Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x)))))
    (φ : (Fin 2 → K) →ₗ[K] K) {a : K}
    (hAact : ∀ x, A *ᵥ x = x + (a * φ x) • v)
    (hφF : ∀ x, φ (Fadd x) = φ x)
    (he_s : ∀ w : V, e (s w) = Multiplicative.ofAdd
      (A *ᵥ Multiplicative.toAdd (e w))) :
    ∀ x : V, s (f x * x⁻¹) = f x * x⁻¹ := by
  intro x
  let y : Fin 2 → K := Multiplicative.toAdd (e x)
  have hφy : φ (Fadd y - y) = 0 := by
    rw [map_sub, hφF y, sub_self]
  have hAy : A *ᵥ (Fadd y - y) = Fadd y - y := by
    rw [hAact (Fadd y - y), hφy, mul_zero, zero_smul, add_zero]
  have hsub : Multiplicative.toAdd (e (f x * x⁻¹)) = Fadd y - y := by
    have h1 : Fadd y = Multiplicative.toAdd (e (f x)) := by
      rw [hFapply]
      simp [y]
    rw [h1]
    simp [y, map_mul, map_inv, sub_eq_add_neg]
  have he_lhs : e (s (f x * x⁻¹)) = Multiplicative.ofAdd (Fadd y - y) := by
    have h1 := he_s (f x * x⁻¹)
    rw [h1, hsub, hAy]
  have he_rhs : e (f x * x⁻¹) = Multiplicative.ofAdd (Fadd y - y) := by
    rw [← hsub]
    simp
  rw [← he_rhs] at he_lhs
  exact e.injective he_lhs


private theorem fixed_mul_inv_aux {K : Type} [Field K] [Finite K] {n : ℕ}
    (hKcard : Nat.card K = 2 ^ n)
    {e : V ≃* Multiplicative (Fin 2 → K)}
    {s f : MulAut V} {A B : Matrix (Fin 2) (Fin 2) K} {v : Fin 2 → K}
    (hAdet : A.det = 1) (hBdet : B.det = 1) (hA1 : A ≠ 1) (hB1 : B ≠ 1)
    (hv : v ≠ 0) (hAv : A *ᵥ v = v) (hBv : B *ᵥ v = v)
    (he_s : ∀ w : V, e (s w) = Multiplicative.ofAdd
      (A *ᵥ Multiplicative.toAdd (e w)))
    (he_s' : ∀ w : V, e ((f * s * f⁻¹) w) = Multiplicative.ofAdd
      (B *ᵥ Multiplicative.toAdd (e w)))
    (hfix : ∀ x : V, s x = x → f x = x) {k : ℕ} (hf : f ^ (2 ^ k) = 1) :
    ∀ x : V, s (f x * x⁻¹) = f x * x⁻¹ := by
  obtain ⟨φ, a, b, ha, hb, -, ⟨w, hφw⟩, hφker, hAact, hBact⟩ :=
    exists_common_functional_of_specialLinear_two hAdet hBdet hA1 hB1 hv hAv hBv
  let Fadd : (Fin 2 → K) →+ (Fin 2 → K) :=
    { toFun := fun x => Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x))))
      map_zero' := by simp
      map_add' := by
        intro x y
        have h : Multiplicative.ofAdd (x + y) =
            Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
        rw [h, map_mul, map_mul, map_mul]
        rfl }
  have hFapply : ∀ x, Fadd x = Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x)))) :=
    fun x => rfl
  have hrel : ∀ x, Fadd (A *ᵥ x) = B *ᵥ Fadd x := by
    intro x
    have hAx : Multiplicative.ofAdd (A *ᵥ x) =
        e (s (e.symm (Multiplicative.ofAdd x))) := by
      simpa using (he_s (e.symm (Multiplicative.ofAdd x))).symm
    have hleft : Fadd (A *ᵥ x) =
        Multiplicative.toAdd (e (f (s (e.symm (Multiplicative.ofAdd x))))) := by
      rw [hFapply, hAx]
      simp
    have hright : B *ᵥ Fadd x =
        Multiplicative.toAdd (e ((f * s * f⁻¹) (f (e.symm (Multiplicative.ofAdd x))))) := by
      rw [hFapply]
      exact (he_s' (f (e.symm (Multiplicative.ofAdd x)))).symm
    rw [hleft, hright]
    congr 1
    simp [MulAut.mul_apply]
  have hfixline : ∀ c : K, Fadd (c • v) = c • v := by
    intro c
    have hAc : A *ᵥ (c • v) = c • v := by
      rw [Matrix.mulVec_smul, hAv]
    have hfixed_s : s (e.symm (Multiplicative.ofAdd (c • v))) =
        e.symm (Multiplicative.ofAdd (c • v)) := by
      apply e.injective
      have h1 := he_s (e.symm (Multiplicative.ofAdd (c • v)))
      simpa [hAc] using h1
    calc Fadd (c • v) = Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd (c • v))))) :=
          hFapply _
      _ = Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd (c • v)))) := by
          rw [hfix _ hfixed_s]
      _ = c • v := by simp
  have hrel_phi : ∀ x, a * φ x = b * φ (Fadd x) := by
    intro x
    have h := hrel x
    have h1 : Fadd (A *ᵥ x) = Fadd x + (a * φ x) • v := by
      rw [hAact x, map_add, hfixline]
    have h2 : B *ᵥ Fadd x = Fadd x + (b * φ (Fadd x)) • v := hBact (Fadd x)
    rw [h1, h2] at h
    have h3 : (a * φ x) • v = (b * φ (Fadd x)) • v := add_left_cancel h
    exact smul_left_injective K hv h3
  let c : K := b / a
  have hcne : c ≠ 0 := div_ne_zero hb ha
  have hstep : ∀ x, φ x = c * φ (Fadd x) := by
    intro x
    have h := hrel_phi x
    have h' : a * φ x = a * (c * φ (Fadd x)) := by
      rw [show a * (c * φ (Fadd x)) = b * φ (Fadd x) by
        simp only [c, div_mul_eq_mul_div, mul_div_assoc]
        field_simp [ha]]
      exact h
    exact mul_left_cancel₀ ha h'
  have hiter : ∀ m x, φ x = c ^ m * φ ((Fadd^[m]) x) := by
    intro m x
    induction m with
    | zero => simp
    | succ m ih =>
        rw [ih, Function.iterate_succ_apply', hstep, pow_succ]
        ring
  have hFiter : ∀ m x, (Fadd^[m]) x =
      Multiplicative.toAdd (e ((f ^ m) (e.symm (Multiplicative.ofAdd x)))) := by
    intro m x
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ']
        simp [Fadd]
  have hFid : ∀ x, (Fadd^[2 ^ k]) x = x := by
    intro x
    rw [hFiter, hf]
    simp
  have hcpow : c ^ (2 ^ k) = 1 := by
    have h1 := hiter (2 ^ k) w
    rw [hFid w, hφw, mul_one] at h1
    exact h1.symm
  have hc1 : c = 1 := eq_one_of_pow_two_pow_eq_one hKcard hcne hcpow
  have hφF : ∀ x, φ (Fadd x) = φ x := by
    intro x
    rw [hstep x, hc1, one_mul]
  exact fixed_mul_inv_final Fadd hFapply φ hAact hφF he_s

theorem BinaryNaturalSL.fixed_mul_inv {H : Subgroup (MulAut V)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 2 n) {s f : MulAut V}
    (hs : s ∈ H) (hs1 : s ≠ 1) {z : V} (hz : z ≠ 1) (hsz : s z = z)
    (hfs : f * s * f⁻¹ ∈ H) (hfix : ∀ v, s v = v → f v = v)
    {k : ℕ} (hf : f ^ (2 ^ k) = 1) :
    ∀ v : V, s (f v * v⁻¹) = f v * v⁻¹ := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, e, A, hAdet, hAne, hact⟩ := exists_coordinates hH
  letI : Field K := hKfield
  letI : Finite K := hKfin
  let sH : H := ⟨s, hs⟩
  let s'H : H := ⟨f * s * f⁻¹, hfs⟩
  have hsH1 : sH ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hsH'1 : s'H ≠ 1 := fun h => hs1 (conj_eq_one_iff.mp (congrArg Subtype.val h))
  let As : Matrix.SpecialLinearGroup (Fin 2) K := A sH
  let Bs : Matrix.SpecialLinearGroup (Fin 2) K := A s'H
  have hAsdet : (As : Matrix (Fin 2) (Fin 2) K).det = 1 := hAdet sH
  have hBsdet : (Bs : Matrix (Fin 2) (Fin 2) K).det = 1 := hAdet s'H
  have hAs1 : (As : Matrix (Fin 2) (Fin 2) K) ≠ 1 := hAne sH hsH1
  have hBs1 : (Bs : Matrix (Fin 2) (Fin 2) K) ≠ 1 := hAne s'H hsH'1
  let v : Fin 2 → K := Multiplicative.toAdd (e z)
  have hv : v ≠ 0 := by
    intro h0
    apply hz
    have h1 : Multiplicative.ofAdd v = 1 := by rw [h0]; rfl
    simpa [v] using h1
  have hAv : (As : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
    have h1 := hact sH z
    rw [show ((sH : H) : MulAut V) z = z from hsz] at h1
    have h2 : Multiplicative.ofAdd ((As : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        Multiplicative.ofAdd v := by
      simpa [As, v] using h1.symm
    exact Multiplicative.ofAdd.injective h2
  have hfz : f z = z := hfix z hsz
  have hBv : (Bs : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
    have h1 := hact s'H (f z)
    have hcancel : ((s'H : H) : MulAut V) (f z) = f z := by
      change (f * s * f⁻¹) (f z) = f z
      simp [MulAut.mul_apply, hsz]
    rw [hcancel, hfz] at h1
    have h2 : Multiplicative.ofAdd ((Bs : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        Multiplicative.ofAdd v := by
      simpa [Bs, v] using h1.symm
    exact Multiplicative.ofAdd.injective h2
  have he_s : ∀ w : V, e (s w) = Multiplicative.ofAdd
      ((As : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd (e w)) := by
    intro w
    exact hact sH w
  have he_s' : ∀ w : V, e ((f * s * f⁻¹) w) = Multiplicative.ofAdd
      ((Bs : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd (e w)) := by
    intro w
    exact hact s'H w
  exact fixed_mul_inv_aux hKcard hAsdet hBsdet hAs1 hBs1 hv hAv hBv he_s he_s' hfix hf


private theorem det_one_add_vecMulVec_of_dotProduct_eq_zero {K : Type} [Field K]
    {u v : Fin 2 → K} (h : v ⬝ᵥ u = 0) :
    (1 + Matrix.vecMulVec u v).det = 1 := by
  rw [Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow, h, add_zero]

private theorem add_vecMulVec_mulVec {K : Type} [Field K]
    (u v x : Fin 2 → K) :
    (1 + Matrix.vecMulVec u v) *ᵥ x = x + (v ⬝ᵥ x) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

private theorem addCoord_sub_mem_span {K : Type} [Field K]
    {e : V ≃* Multiplicative (Fin 2 → K)} {f s : MulAut V}
    {A : Matrix (Fin 2) (Fin 2) K} {a : K} {w0 : Fin 2 → K}
    {φ : (Fin 2 → K) →ₗ[K] K}
    (F : (Fin 2 → K) →+ (Fin 2 → K))
    (hFapply : ∀ x, F x =
      Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x)))))
    (ha : a ≠ 0) (hw0 : w0 ≠ 0)
    (hact : ∀ w : V, e (s w) = Multiplicative.ofAdd
      (A *ᵥ Multiplicative.toAdd (e w)))
    (hmod : ∀ v : V, s (f v * v⁻¹) = f v * v⁻¹)
    (hAact : ∀ x, A *ᵥ x = x + (a * φ x) • w0)
    (hφker : ∀ x, φ x = 0 ↔ x ∈ Submodule.span K {w0}) :
    ∀ x, F x - x ∈ Submodule.span K {w0} := by
  intro x
  let v : V := e.symm (Multiplicative.ofAdd x)
  have hmem : s (f v * v⁻¹) = f v * v⁻¹ := hmod v
  have hcomm : f v * v⁻¹ = e.symm (Multiplicative.ofAdd (F x - x)) := by
    apply e.injective
    simp [v, hFapply, map_mul, map_inv, sub_eq_add_neg]
  have h1 : Multiplicative.ofAdd (A *ᵥ (F x - x)) = e (s (f v * v⁻¹)) := by
    rw [hact (f v * v⁻¹)]
    rw [hcomm, MulEquiv.apply_symm_apply]
    rfl
  have h2 : e (s (f v * v⁻¹)) = Multiplicative.ofAdd (F x - x) := by
    rw [hmem, hcomm, MulEquiv.apply_symm_apply]
  have hAfix : A *ᵥ (F x - x) = F x - x :=
    Multiplicative.ofAdd.injective (h1.trans h2)
  have hzero : (a * φ (F x - x)) • w0 = 0 := by
    have h := hAact (F x - x)
    rw [hAfix] at h
    have h' : (F x - x) + 0 = (F x - x) + (a * φ (F x - x)) • w0 := by
      rw [add_zero]
      exact h
    exact (add_left_cancel h').symm
  have hcoe : a * φ (F x - x) = 0 :=
    smul_left_injective K hw0 (by simpa using hzero)
  exact (hφker (F x - x)).mp (by
    rcases mul_eq_zero.mp hcoe with h | h
    · exact absurd h ha
    · exact h)

private theorem exists_lamS_of_addCoord {K : Type} [Field K]
    {w0 w1 : Fin 2 → K} {φ : (Fin 2 → K) →ₗ[K] K}
    (F : (Fin 2 → K) →+ (Fin 2 → K))
    (hw0 : w0 ≠ 0) (hφw1 : φ w1 = 1)
    (hφker : ∀ x, φ x = 0 ↔ x ∈ Submodule.span K {w0})
    (hFdiff : ∀ x, F x - x ∈ Submodule.span K {w0})
    (hfix_line : ∀ c : K, F (c • w0) = c • w0) :
    ∃ lamS : K → K, ∀ x, F x = x + lamS (φ x) • w0 := by
  let lam : (Fin 2 → K) → K :=
    fun x => Classical.choose (Submodule.mem_span_singleton.mp (hFdiff x))
  have hlam : ∀ x, F x - x = lam x • w0 := fun x =>
    (Classical.choose_spec (Submodule.mem_span_singleton.mp (hFdiff x))).symm
  have hF_eq : ∀ x, F x = x + lam x • w0 := by
    intro x
    calc F x = (F x - x) + x := by abel
      _ = lam x • w0 + x := by rw [hlam x]
      _ = x + lam x • w0 := by rw [add_comm]
  have hlam_add : ∀ x y, lam (x + y) = lam x + lam y := by
    intro x y
    have h1 : F (x + y) = F x + F y := map_add F x y
    rw [hF_eq, hF_eq, hF_eq] at h1
    have h2 : (x + y) + lam (x + y) • w0 =
        (x + y) + (lam x + lam y) • w0 := by
      rw [h1, add_smul]
      module
    exact smul_left_injective K hw0 (add_left_cancel h2)
  let lamS : K → K := fun c => lam (c • w1)
  refine ⟨lamS, ?_⟩
  intro x
  have hφy : φ (x - (φ x) • w1) = 0 := by
    rw [map_sub, map_smul, hφw1, smul_eq_mul, mul_one, sub_self]
  obtain ⟨c, hc⟩ :=
    Submodule.mem_span_singleton.mp ((hφker (x - (φ x) • w1)).mp hφy)
  have hx : (φ x) • w1 + (x - (φ x) • w1) = x := by abel
  have h1 : F ((φ x) • w1) = (φ x) • w1 + lamS (φ x) • w0 := by
    rw [hF_eq]
  have h2 : F (x - (φ x) • w1) = x - (φ x) • w1 := by
    rw [← hc, hfix_line c]
  calc F x = F ((φ x) • w1 + (x - (φ x) • w1)) := by rw [hx]
    _ = F ((φ x) • w1) + F (x - (φ x) • w1) := map_add F _ _
    _ = ((φ x) • w1 + lamS (φ x) • w0) + (x - (φ x) • w1) := by rw [h1, h2]
    _ = x + lamS (φ x) • w0 := by module

private theorem addCoord_fix_line {K : Type} [Field K]
    {e : V ≃* Multiplicative (Fin 2 → K)} {f s : MulAut V}
    {A : Matrix (Fin 2) (Fin 2) K} {w0 : Fin 2 → K}
    (F : (Fin 2 → K) →+ (Fin 2 → K))
    (hFapply : ∀ x, F x =
      Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x)))))
    (hact : ∀ w : V, e (s w) = Multiplicative.ofAdd
      (A *ᵥ Multiplicative.toAdd (e w)))
    (hfix : ∀ v : V, s v = v → f v = v) (hAw0 : A *ᵥ w0 = w0) :
    ∀ c : K, F (c • w0) = c • w0 := by
  intro c
  have hAc : A *ᵥ (c • w0) = c • w0 := by
    rw [Matrix.mulVec_smul, hAw0]
  have hfixed_s : s (e.symm (Multiplicative.ofAdd (c • w0))) =
      e.symm (Multiplicative.ofAdd (c • w0)) := by
    apply e.injective
    rw [hact]
    simp only [MulEquiv.apply_symm_apply]
    apply Multiplicative.ofAdd.injective
    change A *ᵥ (c • w0) = c • w0
    rw [Matrix.mulVec_smul, hAw0]
  have h2 : Multiplicative.ofAdd (F (c • w0)) =
      Multiplicative.ofAdd (c • w0) := by
    simpa [hFapply, hfixed_s] using congrArg e (hfix _ hfixed_s)
  exact Multiplicative.ofAdd.injective h2

private theorem exists_opposite_transvection {K : Type} [Field K]
    {w0 w1 : Fin 2 → K} {φ : (Fin 2 → K) →ₗ[K] K}
    (hw0 : w0 ≠ 0) (hφw0 : φ w0 = 0) (hφw1 : φ w1 = 1) :
    ∃ (ψ : (Fin 2 → K) →ₗ[K] K) (Bmat : Matrix (Fin 2) (Fin 2) K),
      Bmat.det = 1 ∧ ψ w1 = 0 ∧ ψ w0 = 1 ∧
        ∀ x, Bmat *ᵥ x = x + ψ x • w1 := by
  have hli : LinearIndependent K ![w1, w0] := by
    rw [linearIndependent_fin2]
    refine ⟨hw0, ?_⟩
    intro c hc
    have h1 : φ w1 = c * φ w0 := by
      rw [show w1 = c • w0 by simpa using hc.symm, map_smul, smul_eq_mul]
    rw [hφw1, hφw0, mul_zero] at h1
    exact one_ne_zero h1
  let b : Module.Basis (Fin 2) K (Fin 2 → K) :=
    basisOfLinearIndependentOfCardEqFinrank' ![w1, w0] hli (by simp)
  have hb0 : b 0 = w1 := by simp [b]
  have hb1 : b 1 = w0 := by simp [b]
  let ψ : (Fin 2 → K) →ₗ[K] K := b.coord 1
  have hψw1 : ψ w1 = 0 := by
    rw [show ψ = b.coord 1 from rfl, Module.Basis.coord_apply, ← hb0,
      Module.Basis.repr_self]
    simp
  have hψw0 : ψ w0 = 1 := by
    rw [show ψ = b.coord 1 from rfl, Module.Basis.coord_apply, ← hb1,
      Module.Basis.repr_self]
    simp
  obtain ⟨cvec, hcvec⟩ := (dotProductEquiv K (Fin 2)).surjective ψ
  have hψ : ∀ x, ψ x = cvec ⬝ᵥ x := fun x => by
    rw [← hcvec, dotProductEquiv_apply_apply]
  let Bmat : Matrix (Fin 2) (Fin 2) K := 1 + Matrix.vecMulVec w1 cvec
  have hBdet : Bmat.det = 1 := by
    refine det_one_add_vecMulVec_of_dotProduct_eq_zero ?_
    rw [← hψ w1, hψw1]
  have hB_mulVec : ∀ x, Bmat *ᵥ x = x + ψ x • w1 := by
    intro x
    simpa [Bmat, hψ] using add_vecMulVec_mulVec w1 cvec x
  exact ⟨ψ, Bmat, hBdet, hψw1, hψw0, hB_mulVec⟩

private theorem lamS_linear_of_action {K : Type} [Field K]
    {w0 w1 : Fin 2 → K} {φ : (Fin 2 → K) →ₗ[K] K}
    (hφw0 : φ w0 = 0) (hφw1 : φ w1 = 1)
    {lamS : K → K} {gmat : Matrix (Fin 2) (Fin 2) K}
    (hmain : ∀ c : K, gmat *ᵥ (c • w1) =
      (lamS (c - lamS c) - lamS c) • w0 + (c - lamS c) • w1) :
    ∀ c : K, lamS c = lamS 1 * c := by
  have hT : ∀ c : K, c - lamS c = c * (1 - lamS 1) := by
    intro c
    have hμ : φ (gmat *ᵥ w1) = 1 - lamS 1 := by
      have h := congrArg φ (hmain 1)
      rw [map_add, map_smul, map_smul, hφw0, hφw1] at h
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, mul_one, one_smul] at h
      exact h
    have h := congrArg φ (hmain c)
    rw [map_add, map_smul, map_smul, hφw0, hφw1] at h
    rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, mul_one] at h
    have hc : φ (gmat *ᵥ (c • w1)) = c * φ (gmat *ᵥ w1) := by
      rw [Matrix.mulVec_smul, map_smul, smul_eq_mul]
    rw [hc, hμ] at h
    exact h.symm
  intro c
  have h := hT c
  have h' : c - lamS c = c - c * lamS 1 := by
    simpa [mul_sub, mul_one] using h
  have h'' : -(lamS c) = -(c * lamS 1) := by
    apply add_left_cancel (a := c)
    simpa [sub_eq_add_neg] using h'
  rw [neg_inj.mp h'', mul_comm]

private theorem f_inv_on_w1 {K : Type} [Field K]
    {e : V ≃* Multiplicative (Fin 2 → K)} {f : MulAut V}
    {w0 w1 : Fin 2 → K} {φ : (Fin 2 → K) →ₗ[K] K}
    {F : (Fin 2 → K) →+ (Fin 2 → K)} {lamS : K → K}
    (hFapply : ∀ x, F x =
      Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x)))))
    (hF_vec : ∀ x, F x = x + lamS (φ x) • w0)
    (hφw1 : φ w1 = 1)
    (hfix_line : ∀ c : K, F (c • w0) = c • w0) (c : K) :
    f⁻¹ (e.symm (Multiplicative.ofAdd (c • w1))) =
      e.symm (Multiplicative.ofAdd (c • w1 - lamS c • w0)) := by
  have h1 : f (e.symm (Multiplicative.ofAdd (c • w1 - lamS c • w0))) =
      e.symm (Multiplicative.ofAdd (c • w1)) := by
    apply e.injective
    have h2 : e (f (e.symm (Multiplicative.ofAdd (c • w1 - lamS c • w0)))) =
        Multiplicative.ofAdd (F (c • w1 - lamS c • w0)) := by
      rw [hFapply]
      rfl
    rw [h2]
    have h3 : F (c • w1 - lamS c • w0) = c • w1 := by
      have hc : F (c • w1) = c • w1 + lamS c • w0 := by
        rw [hF_vec (c • w1), map_smul, hφw1, smul_eq_mul, mul_one]
      have hz : F (lamS c • w0) = lamS c • w0 := hfix_line (lamS c)
      rw [map_sub, hc, hz]
      abel
    rw [h3]
    simp
  have h4 := congrArg (fun y => f⁻¹ y) h1
  simpa using h4.symm

private theorem conjugate_transvection_mulVec {K : Type} [Field K]
    {H : Subgroup (MulAut V)}
    {e : V ≃* Multiplicative (Fin 2 → K)} {f g : MulAut V}
    {bH : H} {A : H → Matrix.SpecialLinearGroup (Fin 2) K}
    (B : Matrix.SpecialLinearGroup (Fin 2) K)
    {w0 w1 : Fin 2 → K} {ψ : (Fin 2 → K) →ₗ[K] K}
    {φ : (Fin 2 → K) →ₗ[K] K}
    {F : (Fin 2 → K) →+ (Fin 2 → K)} {lamS : K → K}
    (hact : ∀ (h : H) (w : V), e ((h : MulAut V) w) = Multiplicative.ofAdd
      ((A h : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd (e w)))
    (hbHmat : A bH = B)
    (hB_mulVec : ∀ x, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x + ψ x • w1)
    (hψw1 : ψ w1 = 0) (hψw0 : ψ w0 = 1)
    (hFapply : ∀ x, F x =
      Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x)))))
    (hF_vec : ∀ x, F x = x + lamS (φ x) • w0)
    (hφw0 : φ w0 = 0) (hφw1 : φ w1 = 1)
    (hfix_line : ∀ c : K, F (c • w0) = c • w0)
    (hgH : g ∈ H) (hg : g = f * (bH : MulAut V) * f⁻¹) :
    ∀ c : K, (A ⟨g, hgH⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ (c • w1) =
      (lamS (c - lamS c) - lamS c) • w0 + (c - lamS c) • w1 := by
  let gH : H := ⟨g, hgH⟩
  have hbHact : ∀ y : Fin 2 → K,
      (bH : MulAut V) (e.symm (Multiplicative.ofAdd y)) =
        e.symm (Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ y)) := by
    intro y
    apply e.injective
    have h := hact bH (e.symm (Multiplicative.ofAdd y))
    rw [hbHmat] at h
    simpa using h
  intro c
  have hfinv := f_inv_on_w1 hFapply hF_vec hφw1 hfix_line c
  have hB_compute : (B : Matrix (Fin 2) (Fin 2) K) *ᵥ (c • w1 - lamS c • w0) =
      (-(lamS c)) • w0 + (c - lamS c) • w1 := by
    rw [hB_mulVec]
    have hψc : ψ (c • w1 - lamS c • w0) = -(lamS c) := by
      rw [map_sub, map_smul, map_smul, hψw1, hψw0]
      simp
    rw [hψc]
    module
  have hF_B : F ((-(lamS c)) • w0 + (c - lamS c) • w1) =
      (lamS (c - lamS c) - lamS c) • w0 + (c - lamS c) • w1 := by
    rw [map_add]
    have h1 : F ((-(lamS c)) • w0) = (-(lamS c)) • w0 := hfix_line (-(lamS c))
    have h2 : F ((c - lamS c) • w1) =
        (c - lamS c) • w1 + lamS (c - lamS c) • w0 := by
      rw [hF_vec ((c - lamS c) • w1), map_smul, hφw1, smul_eq_mul, mul_one]
    rw [h1, h2]
    module
  have h1 : e ((gH : MulAut V) (e.symm (Multiplicative.ofAdd (c • w1)))) =
      Multiplicative.ofAdd ((A gH : Matrix (Fin 2) (Fin 2) K) *ᵥ (c • w1)) := by
    simpa [gH] using hact gH (e.symm (Multiplicative.ofAdd (c • w1)))
  have h2 : (gH : MulAut V) (e.symm (Multiplicative.ofAdd (c • w1))) =
      f ((bH : MulAut V) (f⁻¹ (e.symm (Multiplicative.ofAdd (c • w1))))) := by
    change g (e.symm (Multiplicative.ofAdd (c • w1))) =
      f ((bH : MulAut V) (f⁻¹ (e.symm (Multiplicative.ofAdd (c • w1)))))
    rw [hg]
    simp [MulAut.mul_apply]
  rw [h2, hfinv] at h1
  have h3 : e (f ((bH : MulAut V)
      (e.symm (Multiplicative.ofAdd (c • w1 - lamS c • w0))))) =
      Multiplicative.ofAdd
        (F ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ (c • w1 - lamS c • w0))) := by
    rw [hbHact (c • w1 - lamS c • w0)]
    rw [hFapply]
    rfl
  rw [h3, hB_compute, hF_B] at h1
  exact Multiplicative.ofAdd.injective h1.symm

private theorem exists_gamma_transvection {K : Type} [Field K]
    {w0 : Fin 2 → K} {φ : (Fin 2 → K) →ₗ[K] K}
    (hφw0 : φ w0 = 0)
    (F : (Fin 2 → K) →+ (Fin 2 → K)) {lamS : K → K}
    (hF_vec : ∀ x, F x = x + lamS (φ x) • w0)
    (hlam_lin : ∀ c : K, lamS c = lamS 1 * c) :
    ∃ γmat : Matrix (Fin 2) (Fin 2) K, γmat.det = 1 ∧ ∀ x, γmat *ᵥ x = F x := by
  obtain ⟨φvec, hφvec'⟩ := (dotProductEquiv K (Fin 2)).surjective φ
  have hφvec : ∀ x, φ x = φvec ⬝ᵥ x := fun x => by
    rw [← hφvec', dotProductEquiv_apply_apply]
  let γmat : Matrix (Fin 2) (Fin 2) K := 1 + Matrix.vecMulVec (lamS 1 • w0) φvec
  have hγdet : γmat.det = 1 := by
    refine det_one_add_vecMulVec_of_dotProduct_eq_zero ?_
    rw [← hφvec (lamS 1 • w0), map_smul, hφw0, smul_zero]
  refine ⟨γmat, hγdet, ?_⟩
  intro x
  have hγ_mulVec : γmat *ᵥ x = x + (φvec ⬝ᵥ x) • (lamS 1 • w0) := by
    simpa [γmat] using add_vecMulVec_mulVec (lamS 1 • w0) φvec x
  rw [hγ_mulVec, ← hφvec x, smul_smul, mul_comm (φ x) (lamS 1),
    ← hlam_lin (φ x), ← hF_vec x]

theorem BinaryNaturalSL.mem_of_normalizes {H : Subgroup (MulAut V)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 2 n) {s f : MulAut V}
    (hs : s ∈ H) (hs1 : s ≠ 1) {z : V} (hz : z ≠ 1) (hsz : s z = z)
    (hnorm : ∀ h ∈ H, f * h * f⁻¹ ∈ H)
    (hfix : ∀ v, s v = v → f v = v)
    (hmod : ∀ v, s (f v * v⁻¹) = f v * v⁻¹) : f ∈ H := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, e, A, hAdet, hAne, hact⟩ :=
    exists_coordinates hH
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hA_inj : Function.Injective A := by
    intro h1 h2 h
    apply Subtype.ext
    ext w
    apply e.injective
    rw [hact h1 w, hact h2 w, h]
  have hcardH : Nat.card H = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    obtain ⟨K', hK'field, hK'fin, hK'card, ⟨eH⟩⟩ :=
      BinaryNaturalSL.exists_equiv hH
    letI : Field K' := hK'field
    letI : Finite K' := hK'fin
    calc Nat.card H = Nat.card (StatedSL 2 K') := (Nat.card_congr eH.toEquiv).symm
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K') :=
        (Nat.card_congr (specialLinearGroupEquivStatedSL 2 K').toEquiv).symm
      _ = Nat.card K' * (Nat.card K' ^ 2 - 1) :=
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K'
      _ = Nat.card K * (Nat.card K ^ 2 - 1) := by rw [hK'card, hKcard]
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
        (CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K).symm
  have hA_surj : Function.Surjective A :=
    (Nat.bijective_iff_injective_and_card A).2 ⟨hA_inj, hcardH⟩ |>.2
  let sH : H := ⟨s, hs⟩
  have hsH1 : sH ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  let As : Matrix.SpecialLinearGroup (Fin 2) K := A sH
  have hAsdet : (As : Matrix (Fin 2) (Fin 2) K).det = 1 := hAdet sH
  have hAs1 : (As : Matrix (Fin 2) (Fin 2) K) ≠ 1 := hAne sH hsH1
  let w0 : Fin 2 → K := Multiplicative.toAdd (e z)
  have hw0 : w0 ≠ 0 := by
    intro h0
    apply hz
    have h1 : Multiplicative.ofAdd w0 = 1 := by rw [h0]; rfl
    simpa [w0] using h1
  have hAw0 : (As : Matrix (Fin 2) (Fin 2) K) *ᵥ w0 = w0 := by
    have h1 := hact sH z
    rw [show ((sH : H) : MulAut V) z = z from hsz] at h1
    have h2 : Multiplicative.ofAdd ((As : Matrix (Fin 2) (Fin 2) K) *ᵥ w0) =
        Multiplicative.ofAdd w0 := by
      simpa [As, w0] using h1.symm
    exact Multiplicative.ofAdd.injective h2
  obtain ⟨φ, a, b, ha, hb, hφw0, ⟨w1, hφw1⟩, hφker, hAact, -⟩ :=
    exists_common_functional_of_specialLinear_two hAsdet hAsdet hAs1 hAs1 hw0 hAw0 hAw0
  let F : (Fin 2 → K) →+ (Fin 2 → K) :=
    { toFun := fun x => Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x))))
      map_zero' := by simp
      map_add' := by
        intro x y
        have h : Multiplicative.ofAdd (x + y) =
            Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
        rw [h, map_mul, map_mul, map_mul]
        rfl }
  have hFapply : ∀ x, F x =
      Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x)))) := fun x => rfl
  have hFdiff : ∀ x : Fin 2 → K, F x - x ∈ Submodule.span K {w0} :=
    addCoord_sub_mem_span F hFapply ha hw0 (fun w => hact sH w) hmod hAact hφker
  have hfix_line : ∀ c : K, F (c • w0) = c • w0 :=
    addCoord_fix_line F hFapply (fun w => hact sH w) hfix hAw0
  obtain ⟨lamS, hF_vec⟩ :=
    exists_lamS_of_addCoord F hw0 hφw1 hφker hFdiff hfix_line
  obtain ⟨ψ, Bmat, hBdet, hψw1, hψw0, hB_mulVec⟩ :=
    exists_opposite_transvection hw0 hφw0 hφw1
  let B : Matrix.SpecialLinearGroup (Fin 2) K := ⟨Bmat, hBdet⟩
  obtain ⟨bH, hbHmat⟩ := hA_surj B
  let g : MulAut V := f * (bH : MulAut V) * f⁻¹
  have hgH : g ∈ H := hnorm _ bH.2
  have hmain := conjugate_transvection_mulVec (B := B) (g := g) hact hbHmat
    hB_mulVec hψw1 hψw0 hFapply hF_vec hφw0 hφw1 hfix_line hgH rfl
  have hlam_lin := lamS_linear_of_action hφw0 hφw1 hmain
  obtain ⟨γmat, hγdet, hγ_mulVec⟩ := exists_gamma_transvection hφw0 F hF_vec hlam_lin
  let γ : Matrix.SpecialLinearGroup (Fin 2) K := ⟨γmat, hγdet⟩
  obtain ⟨hfH, hhfA⟩ := hA_surj γ
  have hf_eq : (hfH : MulAut V) = f := by
    ext w
    apply e.injective
    rw [hact hfH w, hhfA]
    change Multiplicative.ofAdd (γmat *ᵥ Multiplicative.toAdd (e w)) =
      e (f w)
    rw [hγ_mulVec]
    simp [F]
  rw [← hf_eq]
  exact hfH.2

end CFSG.Quasithin
