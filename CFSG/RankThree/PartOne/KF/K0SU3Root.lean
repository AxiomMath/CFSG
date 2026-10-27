module

public import CFSG.RankThree.PartOne.KF.K0SU3Eig
public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder

public section

namespace CFSG.RankThree.PartOne.KFK0

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def Qset (σ : K ≃+* K) (v : Fin 3 → K) : Set ↥(SU σ 3) :=
  {x | ∀ y : Fin 3 → K, ∃ c : K, smat x *ᵥ y - y = c • v}

theorem conj_mem_Qset (g : ↥(SU σ 3)) {x : ↥(SU σ 3)} {v : Fin 3 → K} (hx : x ∈ Qset σ v) :
    g * x * g⁻¹ ∈ Qset σ (smat g *ᵥ v) := by
  intro y
  obtain ⟨c, hc⟩ := hx (smat g⁻¹ *ᵥ y)
  refine ⟨c, ?_⟩
  set z := smat g⁻¹ *ᵥ y with hz
  have h1 : smat g *ᵥ z = y := by
    rw [hz, Matrix.mulVec_mulVec, smat_mul_inv, Matrix.one_mulVec]
  have h2 : smat (g * x * g⁻¹) *ᵥ y = smat g *ᵥ (smat x *ᵥ z) := by
    rw [smat_mul, smat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc smat (g * x * g⁻¹) *ᵥ y - y = smat g *ᵥ (smat x *ᵥ z) - smat g *ᵥ z := by rw [h2, h1]
    _ = smat g *ᵥ (smat x *ᵥ z - z) := (Matrix.mulVec_sub _ _ _).symm
    _ = c • (smat g *ᵥ v) := by rw [hc, Matrix.mulVec_smul]

theorem conj_mem_Qset_iff (g : ↥(SU σ 3)) {x : ↥(SU σ 3)} {v : Fin 3 → K} :
    g * x * g⁻¹ ∈ Qset σ (smat g *ᵥ v) ↔ x ∈ Qset σ v := by
  refine ⟨fun h => ?_, conj_mem_Qset g⟩
  have h' := conj_mem_Qset g⁻¹ h
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group, Matrix.mulVec_mulVec, smat_inv_mul,
    Matrix.one_mulVec] at h'

theorem Qset_smul {c : K} (hc : c ≠ 0) (v : Fin 3 → K) : Qset σ (c • v) = Qset σ v := by
  ext x
  constructor
  · intro hx y
    obtain ⟨d, hd⟩ := hx y
    exact ⟨d * c, by rw [hd, smul_smul]⟩
  · intro hx y
    obtain ⟨d, hd⟩ := hx y
    exact ⟨d * c⁻¹, by rw [hd, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]⟩

@[expose] def e0 : Fin 3 → K := ![1, 0, 0]

@[expose] def Zmat (b : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, b; 0, 1, 0; 0, 0, 1]

theorem exists_Zmat_of_mem_Qset_e0 [CharP K 2] {x : ↥(SU σ 3)}
    (hx : x ∈ Qset σ e0) : ∃ b : K, σ b = b ∧ smat x = Zmat b := by
  obtain ⟨c0, hc0⟩ := hx ![1, 0, 0]
  obtain ⟨c1, hc1⟩ := hx ![0, 1, 0]
  obtain ⟨c2, hc2⟩ := hx ![0, 0, 1]
  have e10 : smat x 1 0 = 0 := by
    have := congrFun hc0 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0] using this
  have e20 : smat x 2 0 = 0 := by
    have := congrFun hc0 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0] using this
  have e11 : smat x 1 1 = 1 := by
    have := congrFun hc1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0, sub_eq_zero] using this
  have e21 : smat x 2 1 = 0 := by
    have := congrFun hc1 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0] using this
  have e12 : smat x 1 2 = 0 := by
    have := congrFun hc2 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0] using this
  have e22 : smat x 2 2 = 1 := by
    have := congrFun hc2 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0, sub_eq_zero] using this
  have h22 := hf_mulVec_SU x ![0, 0, 1] ![0, 0, 1]
  have h12 := hf_mulVec_SU x ![0, 1, 0] ![0, 0, 1]
  have h02 := hf_mulVec_SU x ![1, 0, 0] ![0, 0, 1]
  simp [hf, Matrix.mulVec, dotProduct, Fin.sum_univ_three, e10, e20, e11, e21, e12, e22] at h22 h12 h02
  have hb : smat x 0 1 = 0 := by
    have : σ (smat x 0 1) = 0 := by simpa using h12
    exact σ.injective (by rw [this, map_zero])
  have ha : smat x 0 0 = 1 := by
    have : σ (smat x 0 0) = 1 := by simpa using h02
    exact σ.injective (by rw [this, map_one])
  refine ⟨smat x 0 2, ?_, ?_⟩
  · have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h22 - (smat x 0 2) * h2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Zmat, ha, hb, e10, e20, e11, e21, e12, e22]

@[expose] def Z0 (σ : K ≃+* K) : Set ↥(SU σ 3) := {y | ∃ b : K, σ b = b ∧ smat y = Zmat b}

theorem Z0_subset_Qset : Z0 σ ⊆ Qset σ e0 := by
  rintro y ⟨b, -, hy⟩ z
  refine ⟨b * z 2, ?_⟩
  ext i
  fin_cases i <;> simp [hy, Zmat, e0, dotProduct, Fin.sum_univ_three]

theorem mem_Z0_of_mem_X0 [CharP K 2] (hσ : ∀ c, σ (σ c) = c) {x : ↥(SU σ 3)}
    (hx : x ∈ rootGroup σ hσ 3 (Pi.single 0 1)) (hx2 : x ^ 2 = 1) : x ∈ Z0 σ := by
  obtain ⟨a, b, hab, hm⟩ := (mem_rootGroup_three hσ).1 hx
  have hm' : smat x = !![1, a, b; 0, 1, -σ a; 0, 0, 1] := hm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : smat x ^ 2 = 1 := by rw [← smat_pow, hx2, smat_one]
  have hsq02 := congrFun (congrFun hsq 0) 2
  rw [hm', sq] at hsq02
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hsq02
  have ha : a = 0 := by
    have : a * σ a = 0 := by linear_combination -hsq02 + b * h2
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact σ.injective (by rw [h, map_zero])
  subst ha
  refine ⟨b, ?_, ?_⟩
  · have : b + σ b = 0 := by simpa using hab
    linear_combination this - b * h2
  · rw [hm']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Zmat]

theorem smat_mulVec_e0_ne_zero (g : ↥(SU σ 3)) : smat g *ᵥ e0 ≠ 0 := by
  intro h
  have h1 : e0 = (0 : Fin 3 → K) := by
    have := congrArg (fun z => smat g⁻¹ *ᵥ z) h
    simpa [Matrix.mulVec_mulVec, smat_inv_mul] using this
  have h2 := congrFun h1 0
  simp [e0] at h2

theorem hf_smat_mulVec_e0 (g : ↥(SU σ 3)) :
    hf σ (smat g *ᵥ e0) (smat g *ᵥ e0) = 0 := by
  rw [hf_mulVec_SU]
  simp [hf, e0]

omit [Field K] in
theorem pow_eq_one_of_pgroup_of_pow_three {H : Type*} [Group H] (hH : IsPGroup 2 H) {x : H}
    (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hH) x
  have h1 : x ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hc : Nat.Coprime (2 ^ k) 3 := (Nat.Coprime.pow_left _ (by norm_num))
  have := pow_gcd_eq_one.2 ⟨h1, h3⟩
  rwa [Nat.Coprime.gcd_eq_one hc, pow_one] at this

theorem sq_eq_one_of_mem_Z0 [CharP K 2] {x : ↥(SU σ 3)} (hx : x ∈ Z0 σ) : x ^ 2 = 1 := by
  obtain ⟨b, -, hb⟩ := hx
  apply Subtype.ext
  apply Units.ext
  show smat (x ^ 2) = 1
  rw [smat_pow, hb]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Zmat, sq, Matrix.mul_apply, Fin.sum_univ_three, ← two_mul, h2]

theorem sq_eq_one_of_mem_Qset [CharP K 2] (g : ↥(SU σ 3)) {x : ↥(SU σ 3)}
    (hx : x ∈ Qset σ (smat g *ᵥ e0)) : x ^ 2 = 1 := by
  have h := (conj_mem_Qset_iff g (x := g⁻¹ * x * g) (v := e0)).1
    (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
  obtain ⟨b, hb, hxb⟩ := exists_Zmat_of_mem_Qset_e0 h
  have h1 := sq_eq_one_of_mem_Z0 (σ := σ) (x := g⁻¹ * x * g) ⟨b, hb, hxb⟩
  have h2 : g⁻¹ * x ^ 2 * g = 1 := by
    have := conj_pow (a := g⁻¹) (b := x) (i := 2)
    rw [inv_inv] at this
    rw [← this]
    exact h1
  calc x ^ 2 = g * (g⁻¹ * x ^ 2 * g) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

section Sylow

variable [Finite K] [CharP K 2] {f : ℕ}

theorem odd_cofactor {f : ℕ} (hf : 1 ≤ f) :
    Odd (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
  have hq'ev : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  refine Odd.mul ?_ ?_
  · have h4 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have hev : Even ((2 ^ f) ^ 2) := (Nat.even_pow.2 ⟨hq'ev, by norm_num⟩)
    rcases hev with ⟨r, hr⟩
    exact ⟨r - 1, by omega⟩
  · have hev : Even ((2 ^ f) ^ 3) := (Nat.even_pow.2 ⟨hq'ev, by norm_num⟩)
    rcases hev with ⟨r, hr⟩
    exact ⟨r, by omega⟩

theorem exists_Rbar_eq_image_aux (hσ : ∀ c, σ (σ c) = c)
    (hcardX0 : Nat.card (rootGroup σ hσ 3 (Pi.single 0 1)) = (2 ^ f) ^ 3) {m : ℕ} (hm : Odd m)
    (hcardG : Nat.card (SU σ 3) = (2 ^ f) ^ 3 * m) (hZcard : (Z0 σ).ncard ≤ 2 ^ f)
    {M : Type} [Group M] (π : ↥(SU σ 3) →* M) (hπ : Function.Surjective π)
    (hker : ∀ z, π z = 1 → z ^ 3 = 1) {R : Subgroup M} (hRcard : Nat.card R = 2 ^ f)
    (hR2 : ∀ r ∈ R, r ^ 2 = 1) :
    ∃ g : ↥(SU σ 3), ∀ r : M, r ∈ R ↔ ∃ x ∈ Qset σ (smat g *ᵥ e0), π x = r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X0 := rootGroup σ hσ 3 (Pi.single 0 1) with hX0
  have hfac : (Nat.card (SU σ 3)).factorization 2 = 3 * f := by
    rw [hcardG, show (2 ^ f) ^ 3 = 2 ^ (3 * f) by ring,
      Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat, add_zero]
  have hS0 : Nat.card X0 = 2 ^ (Nat.card (SU σ 3)).factorization 2 := by
    rw [hcardX0, hfac, show 2 ^ (3 * f) = (2 ^ f) ^ 3 by ring]
  set S0 : Sylow 2 (SU σ 3) := Sylow.ofCard X0 hS0 with hS0def
  have hS0coe : (S0 : Subgroup (SU σ 3)) = X0 := rfl
  have hX0p : IsPGroup 2 ↥X0 := S0.isPGroup'
  set S1 : Sylow 2 M := Sylow.mapSurjective hπ S0 with hS1
  have hS1coe : (S1 : Subgroup M) = X0.map π := rfl
  have : Finite M := Finite.of_surjective π hπ
  have hRp : IsPGroup 2 ↥R := IsPGroup.of_card hRcard
  obtain ⟨T, hRT⟩ := hRp.exists_le_sylow
  obtain ⟨g1, hg1⟩ := MulAction.exists_smul_eq M T S1
  have hconj : ∀ r ∈ R, g1 * r * g1⁻¹ ∈ X0.map π := by
    intro r hr
    have h1 : g1 * r * g1⁻¹ ∈ ((g1 • T : Sylow 2 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨r, hRT hr, by simp [MulAut.conj_apply]⟩
    rw [hg1, hS1coe] at h1
    exact h1
  obtain ⟨g, rfl⟩ := hπ g1
  have hZ : ∀ r ∈ R, π g * r * (π g)⁻¹ ∈ π '' Z0 σ := by
    intro r hr
    obtain ⟨x, hxX, hx⟩ := hconj r hr
    refine ⟨x, mem_Z0_of_mem_X0 hσ hxX ?_, hx⟩
    have h2 : π (x ^ 2) = 1 := by
      rw [map_pow, hx, show (π g * r * (π g)⁻¹) ^ 2 = π g * r ^ 2 * (π g)⁻¹ by rw [conj_pow],
        hR2 r hr]
      group
    have h3 : (x ^ 2) ^ 3 = 1 := hker _ h2
    have h4 : x ^ 2 ∈ X0 := X0.pow_mem hxX 2
    exact pow_eq_one_of_pgroup_of_pow_three hX0p (x := ⟨x ^ 2, h4⟩) (Subtype.ext h3) |> fun h =>
      by simpa using congrArg Subtype.val h
  set Rimg : Set M := (fun r => π g * r * (π g)⁻¹) '' (R : Set M) with hRimg
  have hRimgcard : Rimg.ncard = 2 ^ f := by
    rw [hRimg, Set.ncard_image_of_injective _ (fun a b h => by simpa using h),
      ← Nat.card_coe_set_eq]
    exact hRcard
  have hRimgZ : Rimg ⊆ π '' Z0 σ := by
    rintro _ ⟨r, hr, rfl⟩
    exact hZ r hr
  have hEq : Rimg = π '' Z0 σ :=
    Set.eq_of_subset_of_ncard_le hRimgZ
      (by rw [hRimgcard]; exact (Set.ncard_image_le (Set.toFinite _)).trans hZcard) (Set.toFinite _)
  refine ⟨g⁻¹, fun r => ?_⟩
  constructor
  · intro hr
    have h1 : π g * r * (π g)⁻¹ ∈ π '' Z0 σ := hZ r hr
    obtain ⟨z, hz, hzr⟩ := h1
    refine ⟨g⁻¹ * z * g⁻¹⁻¹, conj_mem_Qset g⁻¹ (Z0_subset_Qset hz), ?_⟩
    simp only [map_mul, map_inv, inv_inv]
    rw [hzr]
    group
  · rintro ⟨x, hx, rfl⟩
    have h1 : g * x * g⁻¹ ∈ Qset σ e0 := by
      have := conj_mem_Qset_iff g⁻¹ (x := g * x * g⁻¹) (v := e0)
      rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
      exact this.1 hx
    obtain ⟨b, hb, hxb⟩ := exists_Zmat_of_mem_Qset_e0 h1
    have h2 : π (g * x * g⁻¹) ∈ Rimg := by
      rw [hEq]
      exact ⟨_, ⟨b, hb, hxb⟩, rfl⟩
    obtain ⟨r, hr, hrr⟩ := h2
    have hrr' : π g * r * (π g)⁻¹ = π (g * x * g⁻¹) := hrr
    have h3 : π g * r * (π g)⁻¹ = π g * π x * (π g)⁻¹ := by
      rw [hrr', map_mul, map_mul, map_inv]
    have : r = π x := by simpa using h3
    rwa [← this]

theorem exists_Rbar_eq_image (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) {M : Type} [Group M]
    (π : ↥(SU (unitaryInvolution K 2 f) 3) →* M) (hπ : Function.Surjective π)
    (hker : ∀ z, π z = 1 → z ^ 3 = 1) {R : Subgroup M} (hRcard : Nat.card R = 2 ^ f)
    (hR2 : ∀ r ∈ R, r ^ 2 = 1) :
    ∃ g : ↥(SU (unitaryInvolution K 2 f) 3), ∀ r : M,
      r ∈ R ↔ ∃ x ∈ Qset (unitaryInvolution K 2 f) (smat g *ᵥ e0), π x = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    unitaryInvolution_involutive hK
  refine exists_Rbar_eq_image_aux hσ (card_rootGroup_three hK) (odd_cofactor hf) ?_ ?_ π hπ hker
    hRcard hR2
  · rw [card_SU_three hK]
    ring
  · have hinj : Set.InjOn (fun y : ↥(SU (unitaryInvolution K 2 f) 3) => smat y 0 2)
        (Z0 (unitaryInvolution K 2 f)) := by
      rintro y ⟨b, -, hy⟩ y' ⟨b', -, hy'⟩ h
      apply Subtype.ext
      apply Units.ext
      show smat y = smat y'
      rw [hy, hy']
      have h1 : b = b' := by simpa [hy, hy', Zmat] using h
      rw [h1]
    have hmaps : ∀ y ∈ Z0 (unitaryInvolution K 2 f),
        (fun y : ↥(SU (unitaryInvolution K 2 f) 3) => smat y 0 2) y ∈
          ((fixedSubfield K 2 f : Subfield K) : Set K) := by
      rintro y ⟨b, hb, hy⟩
      show unitaryInvolution K 2 f (smat y 0 2) = smat y 0 2
      simpa [hy, Zmat] using hb
    calc (Z0 (unitaryInvolution K 2 f)).ncard ≤ ((fixedSubfield K 2 f : Subfield K) : Set K).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
      _ = 2 ^ f := by
        rw [← Nat.card_coe_set_eq]
        exact card_fixedSubfield hK

omit [Finite K] [CharP K 2] in
theorem eq_one_of_mulVec_eq (M : Matrix (Fin 3) (Fin 3) K) (h : ∀ z, M *ᵥ z = z) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

omit [Finite K] [CharP K 2] in
theorem exists_eigen_of_normalized {u x' : ↥(SU σ 3)} {y : Fin 3 → K} (hx'Q : x' ∈ Qset σ y)
    (hx'1 : x' ≠ 1) (hux : u * x' * u⁻¹ ∈ Qset σ y) : ∃ μ : K, smat u *ᵥ y = μ • y := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, smat x' *ᵥ z - z ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hx'1
    apply Subtype.ext
    apply Units.ext
    exact eq_one_of_mulVec_eq _ fun z => sub_eq_zero.1 (hno z)
  obtain ⟨c, hc⟩ := hx'Q z
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hz (by rw [hc, zero_smul])
  obtain ⟨c', hc'⟩ := hux (smat u *ᵥ z)
  refine ⟨c⁻¹ * c', ?_⟩
  have h1 : smat (u * x' * u⁻¹) *ᵥ (smat u *ᵥ z) = smat u *ᵥ (smat x' *ᵥ z) := by
    have hinv : smat u⁻¹ *ᵥ (smat u *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, smat_inv_mul, Matrix.one_mulVec]
    rw [smat_mul, smat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv]
  rw [h1, ← Matrix.mulVec_sub, hc, Matrix.mulVec_smul] at hc'
  calc smat u *ᵥ y = c⁻¹ • (c • (smat u *ᵥ y)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = (c⁻¹ * c') • y := by rw [hc', smul_smul]

theorem core_Qset (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ} (hp : 0 < p) (hpodd : Odd p) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpq : p ∣ 2 ^ f - 1)
    {u : ↥(SU (unitaryInvolution K 2 f) 3)} (hu : u ^ p = 1) (hu1 : u ≠ 1) :
    ∃ v w : Fin 3 → K, ∀ y : Fin 3 → K, y ≠ 0 → hf (unitaryInvolution K 2 f) y y = 0 →
      ∀ x' ∈ Qset (unitaryInvolution K 2 f) y, x' ≠ 1 →
        u * x' * u⁻¹ ∈ Qset (unitaryInvolution K 2 f) y →
          Qset (unitaryInvolution K 2 f) y = Qset (unitaryInvolution K 2 f) v ∨
            Qset (unitaryInvolution K 2 f) y = Qset (unitaryInvolution K 2 f) w := by
  classical
  have hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    unitaryInvolution_involutive hK
  have hfix : ∀ ν : K, ν ^ p = 1 → unitaryInvolution K 2 f ν = ν := by
    intro ν hν
    rw [unitaryInvolution_apply]
    obtain ⟨k, hk⟩ := hpq
    have h1 : ν ^ (2 ^ f - 1) = 1 := by rw [hk, pow_mul, hν, one_pow]
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    calc ν ^ 2 ^ f = ν ^ (2 ^ f - 1) * ν := by rw [← pow_succ, Nat.sub_add_cancel hq1]
      _ = ν := by rw [h1, one_mul]
  obtain ⟨l, v, w, x, hlp, hl1, hv, hw, hx, hvv, hww, hxx, hli⟩ :=
    exists_eigenbasis hσ hp hpodd hζ hfix hu hu1
  have hli1 : l⁻¹ ≠ 1 := fun h => hl1 (inv_eq_one.1 h)
  have hll : l ≠ l⁻¹ := by
    intro h
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hlp
      exact zero_ne_one hlp
    apply sq_ne_one_of_ne_one hpodd hlp hl1
    calc l ^ 2 = l * l⁻¹ := by rw [sq]; exact congrArg (l * ·) h
      _ = 1 := mul_inv_cancel₀ hl0
  refine ⟨v, w, fun y hy0 hyy x' hx'Q hx'1 hux => ?_⟩
  obtain ⟨μ, hμ⟩ := exists_eigen_of_normalized hx'Q hx'1 hux
  rcases eigen_isotropic_cases hli hl1 hli1 hll hxx hv hw hx hy0 hμ hyy with
    ⟨d, hd, hdy⟩ | ⟨d, hd, hdy⟩
  · left
    rw [hdy, Qset_smul hd]
  · right
    rw [hdy, Qset_smul hd]

end Sylow

end CFSG.RankThree.PartOne.KFK0
