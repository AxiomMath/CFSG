module

public import CFSG.RankThree.PartOne.U5K.Hyp.Para

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] def Gam1 : Subgroup (Gam hK) :=
  (SemidirectProduct.rightHom.comp (semilinearSimilitudes hK 2 1).subtype).ker

@[expose] def Dlin : Subgroup (MulAut (hypPSU hK 2 1)) := (Gam1 hK).map (Phi hK)

variable {hK}

theorem mem_Gam1 {x : Gam hK} : x ∈ Gam1 hK ↔ x.1.right = 1 := by
  rw [Gam1, MonoidHom.mem_ker]
  rfl

theorem Phi_eq_one_iff {x : Gam hK} :
    Phi hK x = 1 ↔ x.1.right = 1 ∧ ∃ c : Kˣ,
      x.1.left = GeneralLinearGroup.scalar (HypIndex 2 1) c :=
  semilinearAutHom_eq_one_iff hK (r := 2) (ε := 1) (by norm_num) le_rfl (by norm_num) x

theorem right_eq_of_Phi_eq {x y : Gam hK} (h : Phi hK x = Phi hK y) : x.1.right = y.1.right := by
  have h1 : Phi hK (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (Phi_eq_one_iff.1 h1).1
  have h3 : (x⁻¹ * y).1.right = x.1.right⁻¹ * y.1.right := by
    rw [Subgroup.coe_mul, SemidirectProduct.mul_right, Subgroup.coe_inv,
      SemidirectProduct.inv_right]
  rw [h3] at h2
  exact inv_mul_eq_one.1 h2

theorem mem_Dlin_iff {ρ : MulAut (hypPSU hK 2 1)} {x : Gam hK} (hx : Phi hK x = ρ) :
    ρ ∈ Dlin hK ↔ x.1.right = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [right_eq_of_Phi_eq hx]
    exact mem_Gam1.1 hy
  · intro h
    exact ⟨x, mem_Gam1.2 h, hx⟩

instance Dlin_normal : (Dlin hK).Normal where
  conj_mem n hn g := by
    obtain ⟨y, rfl⟩ := Phi_surjective hK g
    obtain ⟨z, hz, rfl⟩ := hn
    refine ⟨y * z * y⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hz' := mem_Gam1.1 hz
    refine mem_Gam1.2 ?_
    simp only [Subgroup.coe_mul, SemidirectProduct.mul_right, Subgroup.coe_inv,
      SemidirectProduct.inv_right, hz']
    simp

@[expose] def inlG (g : hypSU hK 2 1) : Gam hK :=
  ⟨SemidirectProduct.inl (g : GL (HypIndex 2 1) K), inl_mem_semilinearSimilitudes g⟩

theorem Phi_inlG (g : hypSU hK 2 1) : Phi hK (inlG g) = innM hK g := by
  ext z
  obtain ⟨h, rfl⟩ := hypProj_surjective hK 2 1 z
  rw [Phi_apply, innM_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem Pi_le_Dlin : Pi hK ≤ Dlin hK := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨g, rfl⟩ := hypProj_surjective hK 2 1 z
  refine ⟨inlG g, mem_Gam1.2 (by simp [inlG]), ?_⟩
  exact Phi_inlG g

section Unit

theorem left_pow_of_right_one {y : SemiGL (HypIndex 2 1) K} (hy : y.right = 1) (n : ℕ) :
    (y ^ n).left = y.left ^ n ∧ (y ^ n).right = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    refine ⟨?_, ?_⟩
    · rw [SemidirectProduct.mul_left, ih.2, map_one, MulAut.one_apply, ih.1]
    · rw [SemidirectProduct.mul_right, ih.2, hy, mul_one]

theorem norm_det_eq_one {A : GL (HypIndex 2 1) K} (hA : A ∈ hypUnitary hK 2 1) :
    hK.norm ((A : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det) = 1 := by
  have h1 := congrArg Matrix.det (mem_hypUnitary.1 hA)
  have e : ((A : Matrix (HypIndex 2 1) (HypIndex 2 1) K).map hK.bar).det =
      hK.bar (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det := by
    simpa using (RingHom.map_det hK.bar (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K)).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e] at h1
  have h2 := det_hypGram_ne_zero (K := K) (r := 2) (ε := 1)
  have h3 : hK.bar (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det *
      (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det = 1 := by
    apply mul_left_cancel₀ h2
    linear_combination h1
  unfold UnitaryFieldData.norm
  linear_combination h3

theorem Dlin_two_mem_Pi {ρ : MulAut (hypPSU hK 2 1)} (hρ : ρ ∈ Dlin hK) {k : ℕ}
    (hk : ρ ^ (2 ^ k) = 1) : ρ ∈ Pi hK := by
  classical
  obtain ⟨x₀, hx₀, hρx⟩ := hρ
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep hK (r := 2) (ε := 1) (by norm_num) le_rfl
    (by norm_num) x₀
  have hr1 : x.1.right = 1 := by rw [hxr]; exact mem_Gam1.1 hx₀
  set A : GL (HypIndex 2 1) K := x.1.left with hAdef
  have hxΦ' : Phi hK x = Phi hK x₀ := hxΦ
  have hker : Phi hK (x ^ (2 ^ k)) = 1 := by rw [map_pow, hxΦ', hρx, hk]
  obtain ⟨-, c, hc⟩ := Phi_eq_one_iff.1 hker
  have hleft : ((x ^ (2 ^ k) : Gam hK) : SemiGL (HypIndex 2 1) K).left = A ^ (2 ^ k) := by
    rw [Subgroup.coe_pow]
    exact (left_pow_of_right_one hr1 _).1
  rw [hleft] at hc
  have hcU : GeneralLinearGroup.scalar (HypIndex 2 1) c ∈ hypUnitary hK 2 1 := by
    rw [← hc]
    exact pow_mem hxU _
  have hnc' : hK.norm (c : K) = 1 := by
    have h1 := mem_hypUnitary.1 hcU
    rw [GeneralLinearGroup.coe_scalar, scalar_gram hK (c : K)] at h1
    have := congrFun (congrFun h1 (.inl 0)) (.inr (.inr 0))
    simpa using this
  have hnδ := norm_det_eq_one hxU
  set δ : K := (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det with hδ
  have hδc : δ ^ (2 ^ k) = (c : K) ^ 5 := by
    have h1 := congrArg (fun B : GL (HypIndex 2 1) K =>
      ((B : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det) hc
    simp only [Units.val_pow_eq_pow_val, Matrix.det_pow, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ] at h1
    simpa [hδ, Fintype.card_sum] using h1
  have hf1 : 1 ≤ f := hK.one_le
  set n : ℕ := 2 ^ f + 1 with hn
  have hcn : (c : K) ^ n = 1 := by rw [← hK.norm_eq_pow]; exact hnc'
  have hδn : δ ^ n = 1 := by rw [← hK.norm_eq_pow]; exact hnδ
  have hcop : Nat.Coprime (2 ^ k) n := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    have := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).1 h
    omega
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by
    have : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    omega)
  set γ : K := (c : K) with hγ
  set lam : K := γ ^ t with hlam
  have hlam0 : lam ≠ 0 := pow_ne_zero _ c.ne_zero
  have hlam5 : lam ^ 5 = δ := by
    calc lam ^ 5 = (γ ^ 5) ^ t := by rw [hlam]; ring
      _ = (δ ^ (2 ^ k)) ^ t := by rw [hδc]
      _ = δ ^ (2 ^ k * t) := by rw [← pow_mul]
      _ = δ ^ ((2 ^ k * t) % n) := pow_eq_pow_mod _ hδn
      _ = δ := by rw [ht, pow_one]
  have hNlam : hK.norm lam = 1 := by
    have : hK.norm lam = (hK.norm γ) ^ t := by
      simp only [UnitaryFieldData.norm, hlam, map_pow, ← mul_pow]
    rw [this, hnc', one_pow]
  set Amat : Matrix (HypIndex 2 1) (HypIndex 2 1) K := (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K)
    with hAmat
  set S : Matrix (HypIndex 2 1) (HypIndex 2 1) K := Matrix.scalar (HypIndex 2 1) lam⁻¹ with hS
  have hNinv : hK.norm lam⁻¹ = 1 := by
    have : hK.norm lam⁻¹ = (hK.norm lam)⁻¹ := by
      simp only [UnitaryFieldData.norm, map_inv₀, mul_inv]
    rw [this, hNlam, inv_one]
  have hgram : ((S * Amat).map hK.bar)ᵀ * hypGram 2 1 K * (S * Amat) = hypGram 2 1 K := by
    rw [conjTranspose_mul_mul hK (hypGram 2 1 K) S Amat, hS, scalar_gram hK, hNinv, one_smul]
    exact mem_hypUnitary.1 hxU
  have hδ0 : δ ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K)).1 A.isUnit
    exact this.ne_zero
  have hdet : (S * Amat).det = 1 := by
    rw [Matrix.det_mul, hS, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ]
    simp only [Fintype.card_sum, Fintype.card_fin]
    rw [inv_pow]
    norm_num
    rw [hlam5]
    exact inv_mul_cancel₀ hδ0
  set g' : hypSU hK 2 1 := mkHypSU hK (S * Amat) hgram hdet with hg'
  have hmatg' : mat g' = S * Amat := rfl
  set lu : Kˣ := Units.mk0 lam hlam0 with hlu
  let s : Gam hK := ⟨SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex 2 1) lu),
    scalarSim_mem hK lu⟩
  have hs1 : Phi hK s = 1 := Phi_eq_one_iff.2 ⟨by simp [s], lu, by simp [s]⟩
  have hx : x = inlG g' * s := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · have h1 : (g' : GL (HypIndex 2 1) K) * GeneralLinearGroup.scalar (HypIndex 2 1) lu = A := by
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
        change (S * Amat) * Matrix.scalar (HypIndex 2 1) (lu : K) = Amat
        have hc : Matrix.scalar (HypIndex 2 1) (lu : K) * Amat =
            Amat * Matrix.scalar (HypIndex 2 1) (lu : K) :=
          (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq
        rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hS, ← map_mul]
        have : lam⁻¹ * (lu : K) = 1 := by
          rw [hlu, Units.val_mk0]
          exact inv_mul_cancel₀ hlam0
        rw [this, map_one, Matrix.one_mul]
      simp only [inlG, Subgroup.coe_mul, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply, s]
      exact h1.symm
    · simp [inlG, s, hr1]
  have hρ' : ρ = innM hK g' := by
    rw [← hρx, ← hxΦ', hx, map_mul, hs1, mul_one, Phi_inlG]
  rw [hρ']
  exact ⟨hypProj hK 2 1 g', rfl⟩

end Unit

section Index

theorem right_sq_of_sq {ρ : MulAut (hypPSU hK 2 1)} (hρ : ρ * ρ = 1) {x : Gam hK}
    (hx : Phi hK x = ρ) : x.1.right = 1 ∨ ∀ c, x.1.right c = hK.bar c := by
  have h1 : Phi hK (x * x) = 1 := by rw [map_mul, hx, hρ]
  have h2 := (Phi_eq_one_iff.1 h1).1
  rw [Subgroup.coe_mul, SemidirectProduct.mul_right] at h2
  rcases ringEquiv_eq_refl_or_bar hK h2 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem card_le_two_mul_inf_Pi (F : Subgroup (MulAut (hypPSU hK 2 1)))
    (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hs : ∀ ρ ∈ F, ρ * ρ = 1) :
    Nat.card F ≤ 2 * Nat.card ↥(F ⊓ Pi hK) := by
  classical
  have := finite_mulAut_hyp hK
  have hsq : ∀ ρ, ρ * ρ = 1 → ρ ∈ Dlin hK → ρ ∈ Pi hK := fun ρ h hD =>
    Dlin_two_mem_Pi hD (k := 1) (by rw [pow_one, pow_two]; exact h)
  by_cases hall : ∀ ρ ∈ F, ρ ∈ Pi hK
  · calc Nat.card F ≤ Nat.card ↥(F ⊓ Pi hK) :=
          Nat.card_le_card_of_injective (fun ρ => ⟨ρ, ρ.2, hall ρ ρ.2⟩)
            (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
      _ ≤ 2 * Nat.card ↥(F ⊓ Pi hK) := Nat.le_mul_of_pos_left _ (by norm_num)
  · push Not at hall
    obtain ⟨ρ₀, hρ₀, hρ₀P⟩ := hall
    have hnotD : ρ₀ ∉ Dlin hK := fun hD => hρ₀P (hsq ρ₀ (hs ρ₀ hρ₀) hD)
    obtain ⟨x₀, hx₀⟩ := Phi_surjective hK ρ₀
    have hx₀r : x₀.1.right ≠ 1 := fun h => hnotD ((mem_Dlin_iff hx₀).2 h)
    have hx₀bar := (right_sq_of_sq (hs ρ₀ hρ₀) hx₀).resolve_left hx₀r
    have hmem : ∀ ρ ∈ F, ρ ∉ Pi hK → ρ₀ * ρ ∈ Pi hK := by
      intro ρ hρ hρP
      have hnD : ρ ∉ Dlin hK := fun hD => hρP (hsq ρ (hs ρ hρ) hD)
      obtain ⟨x, hx⟩ := Phi_surjective hK ρ
      have hxr : x.1.right ≠ 1 := fun h => hnD ((mem_Dlin_iff hx).2 h)
      have hxbar := (right_sq_of_sq (hs ρ hρ) hx).resolve_left hxr
      have hlift : Phi hK (x₀ * x) = ρ₀ * ρ := by rw [map_mul, hx₀, hx]
      have hr : (x₀ * x).1.right = 1 := by
        rw [Subgroup.coe_mul, SemidirectProduct.mul_right]
        ext c
        show x₀.1.right (x.1.right c) = c
        rw [hxbar c, hx₀bar (hK.bar c), hK.bar_bar]
      have hD : ρ₀ * ρ ∈ Dlin hK := (mem_Dlin_iff hlift).2 hr
      have hsq' : (ρ₀ * ρ) * (ρ₀ * ρ) = 1 := by
        calc ρ₀ * ρ * (ρ₀ * ρ) = ρ₀ * (ρ * ρ₀) * ρ := by group
          _ = ρ₀ * (ρ₀ * ρ) * ρ := by rw [hc ρ hρ ρ₀ hρ₀]
          _ = (ρ₀ * ρ₀) * (ρ * ρ) := by group
          _ = 1 := by rw [hs ρ₀ hρ₀, hs ρ hρ, one_mul]
      exact hsq _ hsq' hD
    let φ : F → ↥(F ⊓ Pi hK) × Bool := fun ρ =>
      if h : (ρ : MulAut (hypPSU hK 2 1)) ∈ Pi hK then (⟨ρ, ρ.2, h⟩, false)
      else (⟨ρ₀ * ρ, F.mul_mem hρ₀ ρ.2, hmem ρ ρ.2 h⟩, true)
    have hinj : Function.Injective φ := by
      intro a b hab
      by_cases ha : (a : MulAut (hypPSU hK 2 1)) ∈ Pi hK <;>
        by_cases hb : (b : MulAut (hypPSU hK 2 1)) ∈ Pi hK <;> simp only [φ, ha, hb, dite_true,
          dite_false] at hab
      · exact Subtype.ext (congrArg (fun p => (p.1 : MulAut (hypPSU hK 2 1))) hab)
      · exact absurd (congrArg Prod.snd hab) (by simp)
      · exact absurd (congrArg Prod.snd hab) (by simp)
      · have := congrArg (fun p => (p.1 : MulAut (hypPSU hK 2 1))) hab
        simp only at this
        exact Subtype.ext (mul_left_cancel this)
    calc Nat.card F ≤ Nat.card (↥(F ⊓ Pi hK) × Bool) := Nat.card_le_card_of_injective φ hinj
      _ = 2 * Nat.card ↥(F ⊓ Pi hK) := by rw [Nat.card_prod]; simp [mul_comm]

end Index

end CFSG.RankThree.PartOne.U5K.Hyp
