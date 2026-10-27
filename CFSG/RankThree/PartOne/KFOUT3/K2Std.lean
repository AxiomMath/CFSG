module

public import CFSG.RankThree.PartOne.KFOUT3.StdAlg
public import CFSG.RankThree.PartOne.KFOUT3.Transport
public import CFSG.RankThree.PartOne.KFOUT3.Std
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.RankThree.PartOne.KFOUT3

variable {K : Type} [Field K]

theorem toGL_slConj (H : GL (Fin 3) K) (t : SL3 K) :
    Matrix.SpecialLinearGroup.toGL (slConj H t) =
      H * Matrix.SpecialLinearGroup.toGL t * H⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_slConj]

theorem toGL_map (σ : K ≃+* K) (t : SL3 K) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ.toRingHom t) =
      glMap σ (Matrix.SpecialLinearGroup.toGL t) := by
  apply Units.ext
  rw [coe_glMap, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

theorem toGL_stdHom (G : GL (Fin 3) K) (σ : K ≃+* K) (t : SL3 K) :
    Matrix.SpecialLinearGroup.toGL (stdHom G σ t) =
      G * glMap σ (Matrix.SpecialLinearGroup.toGL t) * G⁻¹ := by
  rw [stdHom, MonoidHom.comp_apply, toGL_slConj, toGL_map]

theorem slConj_mul (G₁ G₂ : GL (Fin 3) K) (t : SL3 K) :
    slConj (G₁ * G₂) t = slConj G₁ (slConj G₂ t) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slConj, toGL_slConj, toGL_slConj]
  group

theorem slConj_injective (G : GL (Fin 3) K) : Function.Injective (slConj G) := by
  intro s t hst
  apply Matrix.SpecialLinearGroup.toGL_injective
  have h := congrArg Matrix.SpecialLinearGroup.toGL hst
  rw [toGL_slConj, toGL_slConj] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem slConj_toGL (x : SL3 K) (t : SL3 K) :
    slConj (Matrix.SpecialLinearGroup.toGL x) t = x * t * x⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slConj, map_mul, map_mul, map_inv]

theorem slConj_stdHom (G₁ G₂ : GL (Fin 3) K) (σ : K ≃+* K) (t : SL3 K) :
    slConj G₁ (stdHom G₂ σ t) = stdHom (G₁ * G₂) σ t := by
  simp only [stdHom, MonoidHom.comp_apply, slConj_mul]

theorem stdHom_slConj_of_fixed {G H : GL (Fin 3) K} {σ : K ≃+* K} {d : Kˣ}
    (hH : G * glMap σ H = Matrix.GeneralLinearGroup.scalar (Fin 3) d * H) (t : SL3 K) :
    stdHom G σ (slConj H t) = slConj H (Matrix.SpecialLinearGroup.map σ.toRingHom t) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_stdHom, toGL_slConj, toGL_slConj, toGL_map, map_mul, map_mul, map_inv]
  have hG : G = Matrix.GeneralLinearGroup.scalar (Fin 3) d * H * (glMap σ H)⁻¹ := by
    rw [← hH]
    group
  have key : G * (glMap σ H * glMap σ (Matrix.SpecialLinearGroup.toGL t) * (glMap σ H)⁻¹) * G⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) d *
        (H * glMap σ (Matrix.SpecialLinearGroup.toGL t) * H⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) d)⁻¹ := by
    rw [hG]
    group
  rw [key, Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

theorem Tor_pow_eq_one {p : ℕ} {t : SL3 K} (ht : t ∈ Tor p K) : t ^ p = 1 := by
  obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 ht
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL, Matrix.diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, hv1 i, Units.val_one]

theorem Tor_mul_comm {p : ℕ} {s t : SL3 K} (hs : s ∈ Tor p K) (ht : t ∈ Tor p K) :
    s * t = t * s := by
  obtain ⟨v, -, hv, rfl⟩ := mem_Tor_iff.1 hs
  obtain ⟨w, -, hw, rfl⟩ := mem_Tor_iff.1 ht
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, coe_diagSL,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem map_eq_pow_of_mem_Tor {p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {σ : K ≃+* K}
    {k : ℕ}
    (hσ : σ (ζ : K) = (ζ : K) ^ k) {t : SL3 K} (ht : t ∈ Tor p K) :
    Matrix.SpecialLinearGroup.map σ.toRingHom t = t ^ k := by
  obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 ht
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_pow, coe_diagSL,
    Matrix.diagonal_pow]
  have hζ' : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.2 hζ
  have hmap : ((Matrix.diagonal fun i => (v i : K)).map σ.toRingHom : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun i => σ (v i : K) :=
    Matrix.diagonal_map (map_zero σ.toRingHom)
  rw [RingHom.mapMatrix_apply, hmap]
  congr 1
  funext i
  have h1 : ((v i : Kˣ) : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hv1 i, Units.val_one]
  obtain ⟨m, -, hm⟩ := hζ'.eq_pow_of_pow_eq_one h1
  rw [Pi.pow_apply, ← hm, map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_conj_fixed [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {G : GL (Fin 3) K} {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3) c = G * glMap σ G * glMap (σ * σ) G) {k : ℕ}
    (hσt : ∀ t ∈ Tor p K, Matrix.SpecialLinearGroup.map σ.toRingHom t = t ^ k) :
    ∃ g : SL3 K, ∀ t ∈ Tor p K, stdHom G σ (g⁻¹ * t * g) = (g⁻¹ * t * g) ^ k := by
  obtain ⟨H, d, hH⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_mul_map_eq_scalar_mul_of_orderOf_eq_three (n := 3)
      (by norm_num) hσ G hc
  let X : Subgroup (SL3 K) := (Tor p K).map (slConj H)
  have hXexp : ∀ x ∈ X, x ^ p = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, Tor_pow_eq_one ht, map_one]
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, Tor_mul_comm hs ht]
  obtain ⟨g, hg⟩ := exists_conj_Tor hp hζ X hXexp hXcomm
  let φ : Tor p K → Tor p K := fun t => ⟨g * slConj H t * g⁻¹, hg _ ⟨t, t.2, rfl⟩⟩
  have hφinj : Function.Injective φ := by
    intro s t hst
    have h1 : g * slConj H s * g⁻¹ = g * slConj H t * g⁻¹ := congrArg Subtype.val hst
    exact Subtype.ext (slConj_injective H (mul_left_cancel (mul_right_cancel h1)))
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.1 hφinj
  refine ⟨g, fun t ht => ?_⟩
  obtain ⟨s, hs⟩ := hφsurj ⟨t, ht⟩
  have hs' : g * slConj H s * g⁻¹ = t := congrArg Subtype.val hs
  have e : g⁻¹ * t * g = slConj H s := by
    rw [← hs']
    group
  rw [e, stdHom_slConj_of_fixed hH, hσt s s.2, map_pow]

theorem rho_comp (π π' : Equiv.Perm (Fin 3)) (ε ε' : Bool) (b : Blk) :
    rho π ε (rho π' ε' b) = rho (π * π') (xor ε ε') b := by
  apply Subtype.ext
  cases ε <;> cases ε' <;> rfl

theorem rho_true_iterate_three_ne : ∀ π : Equiv.Perm (Fin 3), ∃ b : Blk, (rho π true)^[3] b ≠ b := by
  decide

theorem eps_false_of_cube {π : Equiv.Perm (Fin 3)} {ε : Bool} (h : (rho π ε)^[3] = id) :
    ε = false := by
  by_contra hε
  have hε' : ε = true := by simpa using hε
  subst hε'
  obtain ⟨b, hb⟩ := rho_true_iterate_three_ne π
  exact hb (congrFun h b)

theorem permSL_one [CharP K 2] : (permSL 1 : SL3 K) = 1 := by
  apply Subtype.ext
  rw [coe_permSL, inv_one, Matrix.permMatrix_one]
  rfl

theorem cPerm_one [CharP K 2] (u : PSL3 K) : cPerm 1 u = u := by
  induction u using QuotientGroup.induction_on with
  | H x => rw [cPerm_mk, permSL_one, inv_one, one_mul, mul_one]

end CFSG.RankThree.PartOne.KFOUT3
