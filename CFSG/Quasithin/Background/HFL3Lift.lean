module

public import CFSG.Quasithin.Background.HFL3U3
public import CFSG.Quasithin.Background.HL3NineM

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag SU3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] in
theorem eq_one_of_pow_two_pow {x : K} {k : ℕ} (h : x ^ 2 ^ k = 1) : x = 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply eq_one_of_sq_eq_one
    rw [← sq, ← pow_mul, ← pow_succ]
    exact h

omit [Finite K] in
theorem det_eq_one_of_pow {B : GL (Fin 3) K} {k : ℕ} (h : B ^ 2 ^ k = 1) :
    (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  apply eq_one_of_pow_two_pow (k := k)
  rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, Matrix.det_one]

omit [Finite K] in
theorem eq_one_of_scalar_of_pow {B : GL (Fin 3) K} {d : K}
    (hB : (B : Matrix (Fin 3) (Fin 3) K) = d • 1) {k : ℕ} (h : B ^ 2 ^ k = 1) : B = 1 := by
  have hd : d ^ 2 ^ k = 1 := by
    have h1 := congrArg (fun C : GL (Fin 3) K => (C : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [Units.val_pow_eq_pow_val, hB, smul_pow, one_pow, Units.val_one] at h1
    simpa using h1
  apply Units.ext
  rw [hB, eq_one_of_pow_two_pow hd, one_smul, Units.val_one]

theorem exists_lift (hK : Nat.card K = (2 ^ n) ^ 2) {T : Subgroup (MulAut (HMod n K))}
    (hT : T ≤ linImg hK) (hT2 : IsPGroup 2 T) :
    ∃ P : Subgroup (SpecialLinearGroup (Fin 3) K), IsPGroup 2 P ∧ P.map (rho hK) = T ∧
      ∀ g ∈ P, rho hK g = 1 → g = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tt : Subgroup (GL (Fin 3) K) := T.comap (rhoT hK) with hTt
  let φ : ↥Tt →* ↥T :=
    { toFun := fun x => ⟨rhoT hK x.1, x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hφ : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨B, rfl⟩ := hT ht
    exact ⟨⟨B, ht⟩, rfl⟩
  obtain ⟨P₁⟩ : Nonempty (Sylow 2 ↥Tt) := inferInstance
  have htop : (P₁ : Subgroup ↥Tt).map φ = ⊤ := by
    rw [← Sylow.coe_mapSurjective hφ]
    exact ((P₁.mapSurjective hφ).is_maximal' (hT2.to_subgroup ⊤) le_top).symm
  set P₀ : Subgroup (GL (Fin 3) K) := (P₁ : Subgroup ↥Tt).map Tt.subtype with hP₀
  have hP₀2 : IsPGroup 2 P₀ := P₁.isPGroup'.map Tt.subtype
  have hpow : ∀ B ∈ P₀, ∃ k : ℕ, B ^ 2 ^ k = 1 := by
    intro B hB
    obtain ⟨k, hk⟩ := hP₀2 ⟨B, hB⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hmapP₀ : P₀.map (rhoT hK) = T := by
    ext t
    constructor
    · rintro ⟨B, ⟨x, -, rfl⟩, rfl⟩
      exact x.2
    · intro ht
      have hmem : (⟨t, ht⟩ : ↥T) ∈ (P₁ : Subgroup ↥Tt).map φ := htop ▸ Subgroup.mem_top _
      obtain ⟨x, hx, hxt⟩ := hmem
      exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxt⟩
  refine ⟨P₀.comap SpecialLinearGroup.toGL, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨k, hk⟩ := hpow _ g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, map_one]
    exact hk
  · ext t
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [← hmapP₀]
      exact ⟨_, hg, rfl⟩
    · intro ht
      rw [← hmapP₀] at ht
      obtain ⟨B, hB, rfl⟩ := ht
      obtain ⟨k, hk⟩ := hpow B hB
      set g : SpecialLinearGroup (Fin 3) K :=
        ⟨(B : Matrix (Fin 3) (Fin 3) K), det_eq_one_of_pow hk⟩ with hg
      have hgB : SpecialLinearGroup.toGL g = B := Units.ext rfl
      refine ⟨g, ?_, ?_⟩
      · show SpecialLinearGroup.toGL g ∈ P₀
        rw [hgB]
        exact hB
      · show rhoT hK (SpecialLinearGroup.toGL g) = rhoT hK B
        rw [hgB]
  · intro g hg h1
    obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h1
    obtain ⟨k, hk⟩ := hpow _ hg
    have h2 := eq_one_of_scalar_of_pow hd hk
    exact SpecialLinearGroup.toGL_injective (h2.trans (map_one _).symm)

theorem le_img_of_isPGroup (hK : Nat.card K = (2 ^ n) ^ 2) {T : Subgroup (MulAut (HMod n K))}
    (hT : T ≤ linImg hK) (hT2 : IsPGroup 2 T) : T ≤ img hK := by
  obtain ⟨P, -, hPT, -⟩ := exists_lift hK hT hT2
  rw [← hPT]
  exact Subgroup.map_le_range _ _

theorem exists_conj_uni3 (hK : Nat.card K = (2 ^ n) ^ 2) {T : Subgroup (MulAut (HMod n K))}
    (hT : T ≤ linImg hK) (hT2 : IsPGroup 2 T) :
    ∃ (g : SpecialLinearGroup (Fin 3) K) (P : Subgroup (SpecialLinearGroup (Fin 3) K)),
      P ≤ unitriangular 3 K ∧ IsPGroup 2 P ∧ (∀ x ∈ P, rho hK x = 1 → x = 1) ∧
        P.map (rho hK) = T.map (MulAut.conj (rho hK g)).toMonoidHom := by
  obtain ⟨P, hP2, hPT, hinj⟩ := exists_lift hK hT hT2
  obtain ⟨g, hg⟩ := exists_conj_le_uni3 hP2
  refine ⟨g, P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  · rintro _ ⟨x, hx, rfl⟩ h1
    have h2 : rho hK x = 1 := by
      have e : rho hK ((MulAut.conj g).toMonoidHom x) = rho hK g * rho hK x * (rho hK g)⁻¹ := by
        show rho hK (g * x * g⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      rw [e] at h1
      have := congrArg (fun y => (rho hK g)⁻¹ * y * rho hK g) h1
      simpa [mul_assoc] using this
    rw [hinj x hx h2, map_one]
  · rw [← hPT, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    show rho hK (g * x * g⁻¹) = rho hK g * rho hK x * (rho hK g)⁻¹
    rw [map_mul, map_mul, map_inv]

theorem card_map_rho_of_inj (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hinj : ∀ x ∈ P, rho hK x = 1 → x = 1) :
    Nat.card ↥(P.map (rho hK)) = Nat.card ↥P := by
  have hi : Function.Injective ((rho hK).comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x.1 x.2 hx)
  have e : P.map (rho hK) = ((rho hK).comp P.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e]
  exact (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm

theorem card_le_of_elemAb (hK : Nat.card K = (2 ^ n) ^ 2) {E : Subgroup (MulAut (HMod n K))}
    (hE : E ≤ linImg hK) (hEe : IsElemAbelian2 E) : Nat.card E ≤ Nat.card K ^ 2 := by
  have hE2 : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hEe.2 x x.2)⟩
  obtain ⟨P, -, hPE, hinj⟩ := exists_lift hK hE hE2
  have hmem : ∀ x ∈ P, rho hK x ∈ E := fun x hx => hPE ▸ ⟨x, hx, rfl⟩
  have hc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : rho hK (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hEe.1 _ (hmem x hx) _ (hmem y hy), mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj _ (P.mul_mem (P.mul_mem hx hy) (P.inv_mem (P.mul_mem hy hx)))
      h1)
  have hs : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    refine hinj _ (P.mul_mem hx hx) ?_
    rw [map_mul, ← sq]
    exact hEe.2 _ (hmem x hx)
  rw [← hPE, card_map_rho_of_inj hK hinj]
  exact card_le_sq_of_elemAb hc hs

end CFSG.Quasithin.H.L3Nine
