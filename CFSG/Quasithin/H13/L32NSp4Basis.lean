module

public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.H13.A6Nu
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def sumFin4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 1] ![3, 2]
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]
  left_inv := by decide
  right_inv := by decide

theorem J_sumFin4 (i j : Fin 4) :
    Matrix.J (Fin 2) (ZMod 2) (sumFin4.symm i) (sumFin4.symm j) = antidiagGram i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem exists_antidiag_basis4 [FiniteDimensional (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} (halt : ∀ v, B v v = 0) (hnd : B.Nondegenerate)
    (hd : Module.finrank (ZMod 2) V = 4) :
    ∃ b : Module.Basis (Fin 4) (ZMod 2) V, ∀ i j, B (b i) (b j) = antidiagGram i j := by
  obtain ⟨m, b', hb'⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J (B := B) halt hnd
  have hm : m = 2 := by
    have := Module.finrank_eq_card_basis b'
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hm
  refine ⟨b'.reindex sumFin4, fun i j => ?_⟩
  have h := congrFun (congrFun hb' (sumFin4.symm i)) (sumFin4.symm j)
  rw [LinearMap.BilinForm.toMatrix_apply] at h
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, h, J_sumFin4]

@[expose] noncomputable def phi4 (b : Module.Basis (Fin 4) (ZMod 2) V) :
    (V ≃ₗ[ZMod 2] V) →* GL (Fin 4) (ZMod 2) where
  toFun γ := ⟨LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V),
    LinearMap.toMatrix b b (γ.symm : V →ₗ[ZMod 2] V), by
      rw [← LinearMap.toMatrix_mul]
      convert LinearMap.toMatrix_id b using 2
      ext v; simp, by
      rw [← LinearMap.toMatrix_mul]
      convert LinearMap.toMatrix_id b using 2
      ext v; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' γ δ := Units.ext (by
    simp only [Units.val_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul])

theorem coe_phi4 (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) :
    ((phi4 b γ : GL (Fin 4) (ZMod 2)) : Mat4) = LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V) :=
  rfl

theorem phi4_injective (b : Module.Basis (Fin 4) (ZMod 2) V) : Function.Injective (phi4 b) := by
  intro γ δ h
  have h1 := congrArg Units.val h
  rw [coe_phi4, coe_phi4] at h1
  exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h1)

theorem phi4_surjective (b : Module.Basis (Fin 4) (ZMod 2) V) :
    Function.Surjective (phi4 b) := by
  intro u
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofLinearMap (Matrix.toLin b b (u : Mat4))
    (Matrix.toLin b b ((u⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)) (by
      rw [← Matrix.toLin_mul, Units.mul_inv, Matrix.toLin_one]) (by
      rw [← Matrix.toLin_mul, Units.inv_mul, Matrix.toLin_one])
  refine ⟨e, Units.ext ?_⟩
  rw [coe_phi4]
  exact LinearMap.toMatrix_toLin b b (u : Mat4)

theorem phi4_map (b : Module.Basis (Fin 4) (ZMod 2) V) (e γ : V ≃ₗ[ZMod 2] V) :
    phi4 (b.map e) γ = phi4 b (e⁻¹ * γ * e) := by
  apply Units.ext
  rw [coe_phi4, coe_phi4]
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr,
    LinearEquiv.coe_coe]
  rfl

theorem form_eq_sum4 (b : Module.Basis (Fin 4) (ZMod 2) V) (B : LinearMap.BilinForm (ZMod 2) V)
    (x y : V) :
    B x y = ∑ k, ∑ l, b.repr x k * (b.repr y l * B (b k) (b l)) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem form_eq_formJ (b : Module.Basis (Fin 4) (ZMod 2) V) {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) (x y : V) :
    B x y = formJ (b.repr x) (b.repr y) := by
  rw [form_eq_sum4 b B]
  simp only [hgram, formJ, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem phi4_mem_sympFour_iff (b : Module.Basis (Fin 4) (ZMod 2) V)
    {B : LinearMap.BilinForm (ZMod 2) V} (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j)
    (γ : V ≃ₗ[ZMod 2] V) : phi4 b γ ∈ sympFour ↔ ∀ v w, B (γ v) (γ w) = B v w := by
  rw [mem_sympFour_iff, coe_phi4]
  have key : ∀ i j, ((LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V))ᵀ * antidiagGram *
      LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V)) i j = B (γ (b i)) (γ (b j)) := by
    intro i j
    rw [transpose_mul_mul_apply, form_eq_formJ b hgram]
    simp only [LinearMap.toMatrix_apply]
    rfl
  constructor
  · intro h v w
    have hγ : ∀ k l, B (γ (b k)) (γ (b l)) = B (b k) (b l) := fun k l => by
      rw [← key, h, hgram]
    have hB : B.compl₁₂ (γ : V →ₗ[ZMod 2] V) (γ : V →ₗ[ZMod 2] V) = B :=
      LinearMap.BilinForm.ext_basis b fun k l => by
        simpa [LinearMap.compl₁₂_apply] using hγ k l
    have := DFunLike.congr_fun (DFunLike.congr_fun hB v) w
    simpa [LinearMap.compl₁₂_apply] using this
  · intro h
    ext i j
    rw [key, h, hgram]

theorem card_sympFour4 : Nat.card ↥sympFour = 720 := by
  have e : ↥sympFour ≃ Equiv.Perm (Fin 6) :=
    Equiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩
  rw [Nat.card_congr e, Nat.card_perm]
  simp [Nat.factorial]

@[expose] def toGL4 (x y : List ℕ) (hx : x.length = 4) (hy : y.length = 4)
    (hxy : mulC x y = oneC4) (hyx : mulC y x = oneC4) : GL (Fin 4) (ZMod 2) :=
  ⟨decodeC4 x, decodeC4 y, by rw [← decodeC4_mulC hx hy, hxy, decodeC4_oneC4],
    by rw [← decodeC4_mulC hy hx, hyx, decodeC4_oneC4]⟩

@[expose] def toSp4 (x y : List ℕ) (hx : x.length = 4) (hy : y.length = 4)
    (hxy : mulC x y = oneC4) (hyx : mulC y x = oneC4) (hs : isSympC x = true) : ↥sympFour :=
  ⟨toGL4 x y hx hy hxy hyx, by rw [mem_sympFour_iff]; exact isSympC_iff.mp hs⟩

@[expose] def x5S : ↥sympFour :=
  toSp4 x5C (mulC x5C (mulC x5C (mulC x5C x5C))) rfl rfl (by decide) (by decide) (by decide)

@[expose] def a9S : ↥sympFour :=
  toSp4 a9C (mulC a9C a9C) rfl rfl (by decide) (by decide) (by decide)

@[expose] def b9S : ↥sympFour :=
  toSp4 b9C (mulC b9C b9C) rfl rfl (by decide) (by decide) (by decide)

theorem sp4_ext {g h : ↥sympFour}
    (e : ((g : GL (Fin 4) (ZMod 2)) : Mat4) = (h : GL (Fin 4) (ZMod 2))) : g = h :=
  Subtype.ext (Units.ext e)

theorem coe_sp4_mul (g h : ↥sympFour) :
    (((g * h : ↥sympFour) : GL (Fin 4) (ZMod 2)) : Mat4) =
      ((g : GL (Fin 4) (ZMod 2)) : Mat4) * ((h : GL (Fin 4) (ZMod 2)) : Mat4) := rfl

theorem orderOf_x5S : orderOf x5S = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply sp4_ext
    simp only [pow_succ, pow_zero, one_mul, coe_sp4_mul]
    show decodeC4 x5C * decodeC4 x5C * decodeC4 x5C * decodeC4 x5C * decodeC4 x5C = 1
    rw [← decodeC4_mulC rfl rfl, ← decodeC4_mulC rfl rfl, ← decodeC4_mulC rfl rfl,
      ← decodeC4_mulC rfl rfl, ← decodeC4_oneC4]
    rfl
  · intro h
    have h1 := congrArg (fun g : ↥sympFour => ((g : GL (Fin 4) (ZMod 2)) : Mat4)) h
    change decodeC4 x5C = 1 at h1
    rw [← decodeC4_oneC4] at h1
    exact absurd (decodeC4_injOn ⟨rfl, by decide⟩ validC4_oneC4 h1) (by decide)

theorem exists_conj_of_sylow {p : ℕ} [Fact p.Prime] {K P : Subgroup ↥sympFour} (hK : IsPGroup p K)
    (hP : IsPGroup p P) (hKi : ¬ p ∣ K.index) (hPi : ¬ p ∣ P.index) :
    ∃ c : ↥sympFour, ∀ x ∈ P, c⁻¹ * x * c ∈ K := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥sympFour (hK.toSylow hKi) (hP.toSylow hPi)
  refine ⟨c, fun x hx => ?_⟩
  have hx' : x ∈ ((c • hK.toSylow hKi : Sylow p ↥sympFour) : Subgroup ↥sympFour) := by
    rw [hc]
    exact (hP.mem_toSylow hPi).mpr hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
  have e : (MulAut.conj c)⁻¹ • x = c⁻¹ * x * c := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [e] at hx'
  exact (hK.mem_toSylow hKi).mp hx'

theorem index_of_card {K : Subgroup ↥sympFour} {n : ℕ} (hK : Nat.card K = n) (hn : 0 < n) :
    K.index = 720 / n := by
  have h := Subgroup.index_mul_card K
  rw [card_sympFour4, hK] at h
  rw [← h, Nat.mul_div_cancel _ hn]

theorem exists_basis_conj {B : LinearMap.BilinForm (ZMod 2) V} (b : Module.Basis (Fin 4) (ZMod 2) V)
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) (c : ↥sympFour) :
    ∃ b' : Module.Basis (Fin 4) (ZMod 2) V, (∀ i j, B (b' i) (b' j) = antidiagGram i j) ∧
      ∀ γ, phi4 b' γ = (c : GL (Fin 4) (ZMod 2)) * phi4 b γ * (c : GL (Fin 4) (ZMod 2))⁻¹ := by
  obtain ⟨e, he⟩ := phi4_surjective b (c : GL (Fin 4) (ZMod 2))
  have hiso : ∀ v w, B (e v) (e w) = B v w :=
    (phi4_mem_sympFour_iff b hgram e).mp (by rw [he]; exact c.2)
  have hiso' : ∀ v w, B (e⁻¹ v) (e⁻¹ w) = B v w := by
    intro v w
    have := hiso (e⁻¹ v) (e⁻¹ w)
    rwa [show e (e⁻¹ v) = v from e.apply_symm_apply v,
      show e (e⁻¹ w) = w from e.apply_symm_apply w, eq_comm] at this
  refine ⟨b.map e⁻¹, fun i j => ?_, fun γ => ?_⟩
  · simp only [Module.Basis.map_apply]
    exact (hiso' (b i) (b j)).trans (hgram i j)
  · rw [phi4_map, inv_inv, map_mul, map_mul, map_inv, he]

theorem map_phi4_le {B : LinearMap.BilinForm (ZMod 2) V} (b : Module.Basis (Fin 4) (ZMod 2) V)
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hΓ : Γ ≤ KGCert.spGroup B) : Γ.map (phi4 b) ≤ sympFour := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact (phi4_mem_sympFour_iff b hgram γ).mpr (hΓ hγ)

theorem exists_basis_of_sylow {B : LinearMap.BilinForm (ZMod 2) V}
    (b : Module.Basis (Fin 4) (ZMod 2) V) (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j)
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite Γ] (hΓ : Γ ≤ KGCert.spGroup B) {p n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card Γ) (hpn : ¬ p ∣ 720 / p ^ n) {P : Subgroup ↥sympFour}
    (hP : Nat.card P = p ^ n) :
    ∃ b' : Module.Basis (Fin 4) (ZMod 2) V, (∀ i j, B (b' i) (b' j) = antidiagGram i j) ∧
      ∀ x ∈ P, ∃ γ ∈ Γ, phi4 b' γ = (x : GL (Fin 4) (ZMod 2)) := by
  have hle := map_phi4_le b hgram hΓ
  set Δ := (Γ.map (phi4 b)).subgroupOf sympFour with hΔ
  have hcard : Nat.card Δ = Nat.card Γ := by
    rw [hΔ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact Subgroup.card_map_of_injective (phi4_injective b)
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime p (hcard ▸ hdvd : p ^ n ∣ Nat.card Δ)
  set K := K₀.map Δ.subtype with hK
  have hKc : Nat.card K = p ^ n := by
    rw [hK, Subgroup.card_map_of_injective Δ.subtype_injective, hK₀]
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  obtain ⟨c, hc⟩ := exists_conj_of_sylow (IsPGroup.of_card hKc) (IsPGroup.of_card hP)
    (by rw [index_of_card hKc hpos]; exact hpn) (by rw [index_of_card hP hpos]; exact hpn)
  obtain ⟨b', hb', hconj⟩ := exists_basis_conj b hgram c
  refine ⟨b', hb', fun x hx => ?_⟩
  have h1 := hc x hx
  rw [hK] at h1
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp h1
  have h2 : ((c⁻¹ * x * c : ↥sympFour) : GL (Fin 4) (ZMod 2)) ∈ Γ.map (phi4 b) := by
    rw [← hy]
    exact y.2
  obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.mp h2
  refine ⟨γ, hγ, ?_⟩
  rw [hconj, hγe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem orderOf_eq_three_of {g : ↥sympFour} {x : List ℕ} (hx : ValidC4 x)
    (hg : ((g : GL (Fin 4) (ZMod 2)) : Mat4) = decodeC4 x) (h3 : mulC x (mulC x x) = oneC4)
    (h1 : x ≠ oneC4) : orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply sp4_ext
    rw [pow_succ, pow_succ, pow_one, coe_sp4_mul, coe_sp4_mul, hg]
    show decodeC4 x * decodeC4 x * decodeC4 x = 1
    have hxx : (mulC x x).length = 4 := by rw [length_mulC]; exact hx.1
    rw [Matrix.mul_assoc, ← decodeC4_mulC hx.1 hx.1, ← decodeC4_mulC hx.1 hxx, h3,
      decodeC4_oneC4]
  · intro h
    have h' := congrArg (fun g : ↥sympFour => ((g : GL (Fin 4) (ZMod 2)) : Mat4)) h
    change ((g : GL (Fin 4) (ZMod 2)) : Mat4) = 1 at h'
    rw [hg, ← decodeC4_oneC4] at h'
    exact h1 (decodeC4_injOn hx validC4_oneC4 h')

theorem orderOf_a9S : orderOf a9S = 3 :=
  orderOf_eq_three_of ⟨rfl, by decide⟩ rfl (by decide) (by decide)

theorem orderOf_b9S : orderOf b9S = 3 :=
  orderOf_eq_three_of ⟨rfl, by decide⟩ rfl (by decide) (by decide)

@[expose] def P9S : Subgroup ↥sympFour := Subgroup.zpowers a9S ⊔ Subgroup.zpowers b9S

theorem mem_zpowers_three {g x : ↥sympFour} (hg : orderOf g = 3) (hx : x ∈ Subgroup.zpowers g) :
    x = 1 ∨ x = g ∨ x = g * g := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hg] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  interval_cases k <;> simp [pow_two]

theorem card_P9S : Nat.card P9S = 9 := by
  have hcomm : a9S * b9S = b9S * a9S := by
    apply sp4_ext
    rw [coe_sp4_mul, coe_sp4_mul]
    show decodeC4 a9C * decodeC4 b9C = decodeC4 b9C * decodeC4 a9C
    rw [← decodeC4_mulC rfl rfl, ← decodeC4_mulC rfl rfl]
    rfl
  have hle : Subgroup.zpowers a9S ≤ Subgroup.normalizer (Subgroup.zpowers b9S : Set ↥sympFour) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hc : ∀ n : ℤ, a9S * b9S ^ n * a9S⁻¹ = b9S ^ n := fun n => by
      rw [(Commute.zpow_right hcomm n).eq]
      group
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, (hc n).symm⟩
    · rintro ⟨n, hn⟩
      simp only at hn
      refine ⟨n, ?_⟩
      have h1 := hc n
      have h2 : a9S⁻¹ * b9S ^ n * a9S = b9S ^ n := by
        calc a9S⁻¹ * b9S ^ n * a9S = a9S⁻¹ * (a9S * b9S ^ n * a9S⁻¹) * a9S := by rw [h1]
          _ = b9S ^ n := by group
      show b9S ^ n = x
      calc b9S ^ n = a9S⁻¹ * b9S ^ n * a9S := h2.symm
        _ = a9S⁻¹ * (a9S * x * a9S⁻¹) * a9S := by rw [hn]
        _ = x := by group
  have hinf : Subgroup.zpowers a9S ⊓ Subgroup.zpowers b9S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have ha := mem_zpowers_three orderOf_a9S hx.1
    have hb := mem_zpowers_three orderOf_b9S hx.2
    have key : ∀ y : ↥sympFour, (y = a9S ∨ y = a9S * a9S) → (y = b9S ∨ y = b9S * b9S) →
        False := by
      intro y hya hyb
      have hcol : ∀ g : ↥sympFour, colsOf4 ((g : GL (Fin 4) (ZMod 2)) : Mat4) ∈
          [a9C, mulC a9C a9C] → colsOf4 ((g : GL (Fin 4) (ZMod 2)) : Mat4) ∈
          [b9C, mulC b9C b9C] → False := by
        intro g h1 h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1] at h2 <;>
          exact absurd h2 (by decide)
      have hA : colsOf4 ((a9S : GL (Fin 4) (ZMod 2)) : Mat4) = a9C :=
        colsOf4_decodeC4 ⟨rfl, by decide⟩
      have hA2 : colsOf4 (((a9S * a9S : ↥sympFour) : GL (Fin 4) (ZMod 2)) : Mat4) =
          mulC a9C a9C := by
        rw [coe_sp4_mul]
        show colsOf4 (decodeC4 a9C * decodeC4 a9C) = _
        rw [← decodeC4_mulC rfl rfl, colsOf4_decodeC4 ⟨rfl, by decide⟩]
      have hB : colsOf4 ((b9S : GL (Fin 4) (ZMod 2)) : Mat4) = b9C :=
        colsOf4_decodeC4 ⟨rfl, by decide⟩
      have hB2 : colsOf4 (((b9S * b9S : ↥sympFour) : GL (Fin 4) (ZMod 2)) : Mat4) =
          mulC b9C b9C := by
        rw [coe_sp4_mul]
        show colsOf4 (decodeC4 b9C * decodeC4 b9C) = _
        rw [← decodeC4_mulC rfl rfl, colsOf4_decodeC4 ⟨rfl, by decide⟩]
      apply hcol y
      · rcases hya with rfl | rfl
        · rw [hA]; simp
        · rw [hA2]; simp
      · rcases hyb with rfl | rfl
        · rw [hB]; simp
        · rw [hB2]; simp
    rcases ha with h | h | h
    · exact h
    · rcases hb with h' | h' | h'
      · exact h'
      · exact (key x (Or.inl h) (Or.inl h')).elim
      · exact (key x (Or.inl h) (Or.inr h')).elim
    · rcases hb with h' | h' | h'
      · exact h'
      · exact (key x (Or.inr h) (Or.inl h')).elim
      · exact (key x (Or.inr h) (Or.inr h')).elim
  have h := A6.card_sup_mul_card_inf' hle
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, orderOf_a9S,
    orderOf_b9S] at h
  exact h

theorem exists_basis_inD_5 {B : LinearMap.BilinForm (ZMod 2) V}
    (b : Module.Basis (Fin 4) (ZMod 2) V) (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j)
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite Γ] (hΓ : Γ ≤ KGCert.spGroup B)
    (h5 : 5 ∣ Nat.card Γ) :
    ∃ b' : Module.Basis (Fin 4) (ZMod 2) V, (∀ i j, B (b' i) (b' j) = antidiagGram i j) ∧
      InD (Γ.map (phi4 b')) x5C := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : Nat.card (Subgroup.zpowers x5S) = 5 ^ 1 := by
    rw [Nat.card_zpowers, orderOf_x5S, pow_one]
  obtain ⟨b', hb', h⟩ := exists_basis_of_sylow b hgram hΓ (n := 1) (by rwa [pow_one])
    (by norm_num) hP
  obtain ⟨γ, hγ, hγe⟩ := h x5S (Subgroup.mem_zpowers _)
  exact ⟨b', hb', ⟨rfl, by decide⟩, phi4 b' γ, ⟨γ, hγ, rfl⟩, by rw [hγe]; rfl⟩

theorem exists_basis_inD_9 {B : LinearMap.BilinForm (ZMod 2) V}
    (b : Module.Basis (Fin 4) (ZMod 2) V) (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j)
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite Γ] (hΓ : Γ ≤ KGCert.spGroup B)
    (h9 : 9 ∣ Nat.card Γ) :
    ∃ b' : Module.Basis (Fin 4) (ZMod 2) V, (∀ i j, B (b' i) (b' j) = antidiagGram i j) ∧
      InD (Γ.map (phi4 b')) a9C ∧ InD (Γ.map (phi4 b')) b9C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b', hb', h⟩ := exists_basis_of_sylow b hgram hΓ (p := 3) (n := 2) (by norm_num; exact h9)
    (by norm_num) (P := P9S) (by rw [card_P9S]; norm_num)
  obtain ⟨γ, hγ, hγe⟩ := h a9S (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  obtain ⟨δ, hδ, hδe⟩ := h b9S (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  exact ⟨b', hb', ⟨⟨rfl, by decide⟩, phi4 b' γ, ⟨γ, hγ, rfl⟩, by rw [hγe]; rfl⟩,
    ⟨⟨rfl, by decide⟩, phi4 b' δ, ⟨δ, hδ, rfl⟩, by rw [hδe]; rfl⟩⟩

end CFSG.Quasithin.H13.Sp4Cert
