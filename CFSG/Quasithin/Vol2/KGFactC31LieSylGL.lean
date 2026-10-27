module

public import CFSG.Quasithin.Vol2.KGFactC31LieSylEig
public import CFSG.Quasithin.Vol2.KGFactC31LieSylGen

public section

open Matrix

namespace CFSG.Quasithin.KGC31

@[expose] def AutBdA {G : Type*} [Group G] (R : Subgroup G) (m : ℕ) : Prop :=
  (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧
    ∀ u ∈ Subgroup.normalizer (R : Set G), u ^ m ∈ Subgroup.centralizer (R : Set G)

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem autBdA_of_map_injective (f : G →* H) (hf : Function.Injective f) {R : Subgroup G} {m : ℕ}
    (h : AutBdA (R.map f) m) : AutBdA R m := by
  obtain ⟨hc, hn⟩ := h
  refine ⟨fun x hx y hy => hf ?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul]
    exact hc _ (Subgroup.mem_map_of_mem f hx) _ (Subgroup.mem_map_of_mem f hy)
  · have hu' : f u ∈ Subgroup.normalizer (((R.map f : Subgroup H)) : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_map.2 ⟨u * x * u⁻¹, conj_mem_of_mem_normalizer hu hx, by
          simp only [map_mul, map_inv]⟩
      · intro hz
        obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz
        refine Subgroup.mem_map.2 ⟨u⁻¹ * y * u, conj_inv_mem_of_mem_normalizer hu hy, ?_⟩
        simp only [map_mul, map_inv]
        rw [hyz]
        group
    have hc' := Subgroup.mem_centralizer_iff.1 (hn (f u) hu')
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply hf
    simp only [map_mul, map_pow]
    exact hc' (f x) (Subgroup.mem_map_of_mem f hx)

theorem conj_hom_injective (g : G) : Function.Injective (MulAut.conj g).toMonoidHom :=
  (MulAut.conj g).injective

end Transport

section DiagGL

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] noncomputable def rhoA (ι K : Type*) [Fintype ι] [DecidableEq ι] [Field K] :
    GL ι K →* Module.End K (ι → K) :=
  ((Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] (ι → K) →ₗ[K] ι → K).toAlgHom.toMonoidHom).comp
    (Units.coeHom (Matrix ι ι K))

theorem rhoA_apply (g : GL ι K) (v : ι → K) :
    rhoA ι K g v = (g : Matrix ι ι K) *ᵥ v :=
  rfl

theorem rhoA_injective : Function.Injective (rhoA ι K) := by
  intro g h hgh
  apply Units.ext
  apply Matrix.toLinAlgEquiv'.injective
  exact hgh

theorem rhoA_diag (g : GL ι K) (hg : ∀ i j, i ≠ j → (g : Matrix ι ι K) i j = 0) (i : ι) :
    rhoA ι K g (Pi.basisFun K ι i) = (g : Matrix ι ι K) i i • Pi.basisFun K ι i := by
  rw [rhoA_apply, Pi.basisFun_apply, Matrix.mulVec_single_one]
  ext k
  by_cases hki : k = i
  · subst hki
    simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, hg k i hki, hki]

@[expose] noncomputable def diagHomA (ι K : Type*) [Fintype ι] [DecidableEq ι] [Field K] :
    (ι → Kˣ) →* GL ι K :=
  (Units.map (Matrix.diagonalRingHom ι K).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : ι => K)).symm.toMonoidHom

theorem coe_diagHomA (a : ι → Kˣ) :
    ((diagHomA ι K a : GL ι K) : Matrix ι ι K) = Matrix.diagonal fun i => (a i : K) :=
  rfl

@[expose] noncomputable def diagTorusA (ι K : Type*) [Fintype ι] [DecidableEq ι] [Field K] :
    Subgroup (GL ι K) :=
  (diagHomA ι K).range

theorem diagTorusA_offdiag {g : GL ι K} (hg : g ∈ diagTorusA ι K) {i j : ι} (hij : i ≠ j) :
    (g : Matrix ι ι K) i j = 0 := by
  obtain ⟨a, rfl⟩ := hg
  rw [coe_diagHomA]
  exact Matrix.diagonal_apply_ne _ hij

theorem diagTorusA_comm {x y : GL ι K} (hx : x ∈ diagTorusA ι K) (hy : y ∈ diagTorusA ι K) :
    x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem diagHomA_injective : Function.Injective (diagHomA ι K) := by
  intro a b hab
  have h1 : Matrix.diagonal (fun i => (a i : K)) = Matrix.diagonal (fun i => (b i : K)) := by
    rw [← coe_diagHomA, ← coe_diagHomA, hab]
  funext i
  exact Units.ext (congrFun (Matrix.diagonal_injective h1) i)

theorem autBdA_of_le_diagTorusA {R : Subgroup (GL ι K)} (hR : R ≤ diagTorusA ι K) :
    AutBdA R (Fintype.card ι).factorial := by
  refine ⟨fun x hx y hy => diagTorusA_comm (hR hx) (hR hy), fun u hu => ?_⟩
  exact eigen_pow_mem_centralizer (b := Pi.basisFun K ι) (ρ := rhoA ι K) rhoA_injective
    (χ := fun i x => (x : Matrix ι ι K) i i)
    (fun x hx i => rhoA_diag x (fun i j hij => diagTorusA_offdiag (hR hx) hij) i) hu

end DiagGL

section Index

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem prod_range_sub_eq_factorial : ∀ n : ℕ, ∏ i ∈ Finset.range n, (n - i) = Nat.factorial n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have h : ∀ i ∈ Finset.range n, (n + 1 - (i + 1)) = n - i := fun i _ => by omega
    rw [Finset.prod_congr rfl h, prod_range_sub_eq_factorial n]
    simp [mul_comm]

theorem prod_fin_sub_eq_factorial (n : ℕ) :
    ∏ i : Fin n, (n - (i : ℕ)) = Nat.factorial n := by
  rw [Fin.prod_univ_eq_prod_range (fun i => n - i) n]
  exact prod_range_sub_eq_factorial n

theorem not_dvd_of_geom (r n ℓ I : ℕ) (hℓ : ℓ.Prime) (hn : n < ℓ) (hr : ℓ ∣ r) (hr1 : 1 ≤ r)
    (hI : r ^ n * I = ∏ i : Fin n, ((r + 1) ^ n - (r + 1) ^ (i : ℕ))) : ¬ ℓ ∣ I := by
  set S : ℕ → ℕ := fun k => ∑ j ∈ Finset.range k, (r + 1) ^ j with hSdef
  have hS : ∀ k, r * S k + 1 = (r + 1) ^ k := by
    intro k
    induction k with
    | zero => simp [hSdef]
    | succ k ih =>
      simp only [hSdef] at ih ⊢
      rw [Finset.sum_range_succ, pow_succ]
      calc r * (∑ j ∈ Finset.range k, (r + 1) ^ j + (r + 1) ^ k) + 1
          = (r * ∑ j ∈ Finset.range k, (r + 1) ^ j + 1) + r * (r + 1) ^ k := by ring
        _ = (r + 1) ^ k + r * (r + 1) ^ k := by rw [ih]
        _ = (r + 1) ^ k * (r + 1) := by ring
  have hfac : ∀ i : Fin n,
      (r + 1) ^ n - (r + 1) ^ (i : ℕ) = (r + 1) ^ (i : ℕ) * (r * S (n - i)) := by
    intro i
    have hi : (i : ℕ) ≤ n := le_of_lt i.2
    have h1 : (r + 1) ^ n = (r + 1) ^ (i : ℕ) * (r * S (n - i) + 1) := by
      rw [hS (n - i), ← pow_add, Nat.add_sub_of_le hi]
    apply Nat.sub_eq_of_eq_add
    rw [h1]
    ring
  have hprod : ∏ i : Fin n, ((r + 1) ^ n - (r + 1) ^ (i : ℕ)) =
      (∏ i : Fin n, (r + 1) ^ (i : ℕ)) * (r ^ n * ∏ i : Fin n, S (n - i)) := by
    rw [Finset.prod_congr rfl (fun i _ => hfac i)]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hI' : I = (∏ i : Fin n, (r + 1) ^ (i : ℕ)) * ∏ i : Fin n, S (n - i) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < r) n)
    rw [hI, hprod]
    ring
  intro hdvd
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hr0 : (r : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff r ℓ).2 hr
  have hQ : ∀ i : Fin n, (((r + 1) ^ (i : ℕ) : ℕ) : ZMod ℓ) = 1 := by
    intro i
    simp [hr0]
  have hS' : ∀ k, ((S k : ℕ) : ZMod ℓ) = (k : ZMod ℓ) := by
    intro k
    simp [hSdef, hr0]
  have hz : ((I : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff I ℓ).2 hdvd
  rw [hI', Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at hz
  have e1 : (∏ i : Fin n, (((r + 1) ^ (i : ℕ) : ℕ) : ZMod ℓ)) = 1 :=
    Finset.prod_eq_one (fun i _ => hQ i)
  have e2 : ∏ i : Fin n, ((S (n - i) : ℕ) : ZMod ℓ) =
      ((Nat.factorial n : ℕ) : ZMod ℓ) := by
    simp only [hS']
    rw [← Nat.cast_prod, prod_fin_sub_eq_factorial n]
  rw [e1, e2, one_mul] at hz
  have hdvd' : ℓ ∣ Nat.factorial n := (ZMod.natCast_eq_zero_iff _ _).1 hz
  have hle : ℓ ≤ n := (Nat.Prime.dvd_factorial hℓ).1 hdvd'
  omega

theorem card_GL_eq [Fintype K] :
    Nat.card (GL ι K) = ∏ i : Fin (Fintype.card ι),
      (Fintype.card K ^ Fintype.card ι - Fintype.card K ^ (i : ℕ)) := by
  rw [← Matrix.card_GL_field (Fintype.card ι)]
  exact Nat.card_congr (Units.mapEquiv
    (Matrix.reindexAlgEquiv K K (Fintype.equivFin ι)).toMulEquiv).toEquiv

theorem card_diagTorusA_eq [Fintype K] :
    Nat.card (diagTorusA ι K) = (Fintype.card K - 1) ^ Fintype.card ι := by
  rw [diagTorusA, ← Nat.card_congr (MonoidHom.ofInjective diagHomA_injective).toEquiv,
    Nat.card_fun, Nat.card_units, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

theorem not_dvd_index_diagTorusA [Fintype K] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hn : Fintype.card ι < ℓ) (hq : ℓ ∣ Fintype.card K - 1) :
    ¬ ℓ ∣ (diagTorusA ι K).index := by
  have hmul := (diagTorusA ι K).card_mul_index
  rw [card_diagTorusA_eq, card_GL_eq] at hmul
  have hK1 : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 1 := ⟨Fintype.card K - 1, by omega⟩
  rw [hr] at hmul hq
  simp only [Nat.add_sub_cancel] at hmul hq
  exact not_dvd_of_geom r (Fintype.card ι) ℓ _ hℓ hn hq (by omega) hmul

end Index

section Sylow

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem exists_sylow_le_diagTorusA [Fintype K] {ℓ : ℕ} [Fact ℓ.Prime]
    (hn : Fintype.card ι < ℓ) (hq : ℓ ∣ Fintype.card K - 1) :
    ∃ P₀ : Sylow ℓ (GL ι K), (P₀ : Subgroup (GL ι K)) ≤ diagTorusA ι K := by
  obtain ⟨S₀⟩ : Nonempty (Sylow ℓ (diagTorusA ι K)) := inferInstance
  have hSp : IsPGroup ℓ ((S₀ : Subgroup (diagTorusA ι K)).map (diagTorusA ι K).subtype) :=
    S₀.isPGroup'.map (diagTorusA ι K).subtype
  have hSi : ¬ ℓ ∣ ((S₀ : Subgroup (diagTorusA ι K)).map (diagTorusA ι K).subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).1 h with h1 | h2
    · exact S₀.not_dvd_index h1
    · exact not_dvd_index_diagTorusA (Fact.out : ℓ.Prime) hn hq h2
  refine ⟨hSp.toSylow hSi, ?_⟩
  exact Subgroup.map_subtype_le _

theorem exists_conj_le_diagTorusA [Fintype K] {ℓ : ℕ} [Fact ℓ.Prime]
    (hn : Fintype.card ι < ℓ) (hq : ℓ ∣ Fintype.card K - 1) {R : Subgroup (GL ι K)}
    (hR : IsPGroup ℓ R) :
    ∃ g : GL ι K, ∀ x ∈ R, g * x * g⁻¹ ∈ diagTorusA ι K := by
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := exists_sylow_le_diagTorusA hn hq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL ι K) Q P₀
  refine ⟨g, fun x hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ ((g • Q : Sylow ℓ (GL ι K)) : Subgroup (GL ι K)) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hRQ hx, rfl⟩
  rw [hg] at h1
  exact hP₀ h1

end Sylow

section Split

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem autBdA_split [Fintype K] {ℓ : ℕ} (hℓ : ℓ.Prime) (hn : Fintype.card ι < ℓ)
    (hq : ℓ ∣ Fintype.card K - 1) {R : Subgroup (GL ι K)} (hR : IsPGroup ℓ R) :
    AutBdA R (Fintype.card ι).factorial := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g, hg⟩ := exists_conj_le_diagTorusA hn hq hR
  refine autBdA_of_map_injective (MulAut.conj g).toMonoidHom (conj_hom_injective g) ?_
  refine autBdA_of_le_diagTorusA ?_
  rintro z hz
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
  exact hg x hx

end Split

section General

theorem autBdA_general {K ι : Type} [Field K] [Finite K] [Fintype ι] [DecidableEq ι]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hn : Fintype.card ι < ℓ) (hK : ¬ ℓ ∣ Nat.card K)
    {R : Subgroup (GL ι K)} (hR : IsPGroup ℓ R) :
    AutBdA R (Fintype.card ι).factorial := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hp, n, hpp, hcardK⟩ := FiniteField.card' K
  haveI : CharP K p := hp
  haveI : Fact p.Prime := ⟨hpp⟩
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  have hKf : p ^ Module.finrank (ZMod p) K = Nat.card K :=
    FiniteField.pow_finrank_eq_natCard p K
  have hf0 : Module.finrank (ZMod p) K ≠ 0 := Module.finrank_pos.ne'
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have hfm : Module.finrank (ZMod p) K * (ℓ - 1) ≠ 0 := Nat.mul_ne_zero hf0 (by omega)
  have hK'card : Nat.card (GaloisField p (Module.finrank (ZMod p) K * (ℓ - 1))) =
      (Nat.card K) ^ (ℓ - 1) := by
    rw [GaloisField.card p _ hfm, pow_mul, hKf]
  have hdvd : ℓ ∣ Nat.card (GaloisField p (Module.finrank (ZMod p) K * (ℓ - 1))) - 1 := by
    rw [hK'card]
    have hq0 : (Nat.card K : ZMod ℓ) ≠ 0 := fun h => hK ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have h1 : 1 ≤ (Nat.card K) ^ (ℓ - 1) := Nat.one_le_pow _ _ Nat.card_pos
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow,
      ZMod.pow_card_sub_one_eq_one hq0, Nat.cast_one, sub_self]
  obtain ⟨ιK⟩ : Nonempty (K →ₐ[ZMod p] GaloisField p (Module.finrank (ZMod p) K * (ℓ - 1))) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      rw [GaloisField.finrank p hfm]
      exact dvd_mul_right _ _)
  haveI : Fintype (GaloisField p (Module.finrank (ZMod p) K * (ℓ - 1))) :=
    Fintype.ofFinite _
  have hdvd' : ℓ ∣ Fintype.card (GaloisField p (Module.finrank (ZMod p) K * (ℓ - 1))) - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hdvd
  let ρ0 : K →+* GaloisField p (Module.finrank (ZMod p) K * (ℓ - 1)) := ιK.toRingHom
  let φ : GL ι K →* GL ι (GaloisField p (Module.finrank (ZMod p) K * (ℓ - 1))) :=
    Matrix.GeneralLinearGroup.map ρ0
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply Units.ext
    apply Matrix.map_injective ρ0.injective
    exact congrArg Units.val hgh
  exact autBdA_of_map_injective φ hφ (autBdA_split hℓ hn hdvd' (hR.map φ))

theorem sylowAutBoundAll_GL_of_fintype {K ι : Type} [Field K] [Finite K] [Fintype ι]
    [DecidableEq ι] {ℓ : ℕ} (hℓ : ℓ.Prime) (hn : Fintype.card ι < ℓ) (hK : ¬ ℓ ∣ Nat.card K) :
    SylowAutBoundAll ℓ (Fintype.card ι).factorial (GL ι K) := fun P =>
  autBdA_general hℓ hn hK P.isPGroup'

end General

end CFSG.Quasithin.KGC31

end
