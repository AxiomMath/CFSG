module

public import CFSG.Quasithin.H13.L32NLem14324g
public import CFSG.Quasithin.EmptyFaithful.SzPS8Model
public import CFSG.Quasithin.EmptyFaithful.SzPS8AxA
public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Fact
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4SL2

public section

namespace CFSG.Quasithin.H13.L14324

open Matrix CFSG.Quasithin.SzPS8 CFSG.Quasithin.SzPS8.L28
open scoped MatrixGroups

@[expose] noncomputable def frobSL : SL(2, F4) →* SL(2, F4) :=
  Matrix.SpecialLinearGroup.map (frobenius F4 2)

theorem frobSL_up (t : F4) : frobSL (up t) = up (t ^ 2) := by
  apply Subtype.ext
  rw [frobSL, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [up, frobenius_def, RingHom.mapMatrix_apply]

theorem exists_sq_ne : ∃ t : F4, t ^ 2 ≠ t := by
  classical
  by_contra h
  push Not at h
  have hcard : Nat.card F4 = 4 := by rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have : Fintype F4 := Fintype.ofFinite F4
  have h2 : ∀ t : F4, t = 0 ∨ t = 1 := by
    intro t
    have := h t
    have h' : t * (t - 1) = 0 := by rw [mul_sub, mul_one, ← sq, this, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hle : Fintype.card F4 ≤ 2 := by
    have : (Finset.univ : Finset F4) ⊆ {0, 1} := fun t _ => by
      rcases h2 t with rfl | rfl <;> simp
    calc Fintype.card F4 = (Finset.univ : Finset F4).card := rfl
      _ ≤ ({0, 1} : Finset F4).card := Finset.card_le_card this
      _ ≤ 2 := Finset.card_le_two
  rw [← Nat.card_eq_fintype_card, hcard] at hle
  omega

theorem card_le_two_of_fixed (g : SL(2, F4)) (E : Subgroup SL(2, F4))
    (hE : ∀ e ∈ E, e * e = 1) (hfix : ∀ e ∈ E, g * frobSL e * g⁻¹ = e) : Nat.card E ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two]; exact hE _ x.2)⟩
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have hSL : Nat.card SL(2, F4) = 60 := by
    have : Fintype F4 := Fintype.ofFinite F4
    have hK : Fintype.card F4 = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    rw [Matrix.card_SL_field 2, hK, Fin.prod_univ_two]
    norm_num
  have hdvd : 2 ^ k ∣ 60 := hk ▸ hSL ▸ Subgroup.card_subgroup_dvd_card E
  have hk2 : k ≤ 2 := by
    have : 2 ^ k ∣ 2 ^ 2 * 15 := hdvd
    have hcop : Nat.Coprime (2 ^ k) 15 := Nat.Coprime.pow_left k (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right this)
  by_contra hgt
  push Not at hgt
  have h4 : 2 < 2 ^ k := by rw [← hk]; exact hgt
  have hk2' : k = 2 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> norm_num at h4
    · omega
  have hEidx : ¬ 2 ∣ E.index := by
    have h := E.card_mul_index
    rw [hk, hk2', hSL] at h
    have : E.index = 15 := by omega
    rw [this]; omega
  obtain ⟨c, hc⟩ := exists_conj_of_isPGroup hE2 hEidx isPGroup_U_gf
    (index_U_gf (n := 2) (by norm_num))
  set g' := c⁻¹ * g * frobSL c with hg'
  have hfixU : ∀ t : F4, g' * up (t ^ 2) * g'⁻¹ = up t := by
    intro t
    have hmem : c * up t * c⁻¹ ∈ E := by
      rw [hc]
      simpa [mul_assoc] using up_mem_U t
    have h1 := hfix _ hmem
    rw [map_mul, map_mul, map_inv, frobSL_up] at h1
    have : g' * up (t ^ 2) * g'⁻¹ =
        c⁻¹ * (g * (frobSL c * up (t ^ 2) * (frobSL c)⁻¹) * g⁻¹) * c := by
      rw [hg']; group
    rw [this, ← mul_assoc g, ← mul_assoc g, show g * frobSL c * up (t ^ 2) * (frobSL c)⁻¹ * g⁻¹ =
      g * (frobSL c * up (t ^ 2) * (frobSL c)⁻¹) * g⁻¹ by group] at *
    rw [h1]
    group
  have h10 : g' 1 0 = 0 := by
    have h1 := hfixU 1
    rw [one_pow] at h1
    have hcomm : g' * up 1 = up 1 * g' := by
      calc g' * up 1 = g' * up 1 * g'⁻¹ * g' := by group
        _ = up 1 * g' := by rw [h1]
    have := congrArg (fun A : SL(2, F4) => (A : Matrix (Fin 2) (Fin 2) F4) 0 0) hcomm
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    simp [up, Matrix.mul_apply, Fin.sum_univ_two] at this
    exact this
  have hconj := fun t => (conj_up h10 (t ^ 2)).symm.trans (hfixU t)
  have heq : ∀ t : F4, g' 0 0 ^ 2 * t ^ 2 = t := fun t => up_injective (hconj t)
  have h00 : g' 0 0 ^ 2 = 1 := by simpa using heq 1
  obtain ⟨t, ht⟩ := exists_sq_ne
  apply ht
  have := heq t
  rwa [h00, one_mul] at this

open Matrix CFSG.Quasithin.SzPS8 CFSG.Quasithin.SzPS8.L28 CFSG.Open
open scoped MatrixGroups

theorem exists_omega : ∃ ω : F4, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨t, ht⟩ := exists_sq_ne
  have : Fintype F4 := Fintype.ofFinite F4
  have hcard : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]; norm_num
  have h4 : t ^ 4 = t := by rw [← hcard]; exact FiniteField.pow_card t
  have ht0 : t ≠ 0 := by rintro rfl; exact ht (by ring)
  have ht1 : t ≠ 1 := by rintro rfl; exact ht (by ring)
  refine ⟨t, ?_⟩
  have h3 : t ^ 3 = 1 := by
    have : t * (t ^ 3 - 1) = 0 := by rw [mul_sub, mul_one, ← pow_succ', h4, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ht0
    · exact sub_eq_zero.mp h
  have : (t - 1) * (t ^ 2 + t + 1) = 0 := by
    have e : (t - 1) * (t ^ 2 + t + 1) = t ^ 3 - 1 := by ring
    rw [e, h3, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) ht1
  · exact h


theorem f4_cases {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) (a : F4) :
    a = 0 ∨ a = 1 ∨ a = ω ∨ a = ω + 1 := by
  classical
  have : Fintype F4 := Fintype.ofFinite F4
  have hcard : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]; norm_num
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  have hω0 : ω ≠ 0 := by rintro rfl; simp at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have : (1 : F4) ^ 2 + 1 + 1 = 1 := by
      rw [one_pow, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [this] at hω
    exact one_ne_zero hω
  have hω2 : ω + 1 ≠ 0 := fun h => hω1 (by
    have := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at this)
  have hω3 : ω + 1 ≠ 1 := fun h => hω0 (add_eq_right.mp h)
  have hω4 : ω + 1 ≠ ω := fun h => one_ne_zero (add_eq_left.mp h)
  set S : Finset F4 := {0, 1, ω, ω + 1} with hS
  have hScard : S.card = 4 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair hω4.symm]
    · simp [hω1.symm, hω3.symm]
    · simp [zero_ne_one, hω0.symm, hω2.symm]
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hScard, hcard])
  have ha : a ∈ S := by rw [hSuniv]; exact Finset.mem_univ a
  simpa [hS] using ha

theorem eq_omega_of_sq {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) {c : F4} (hc : c ^ 2 + c + 1 = 0) :
    c = ω ∨ c = ω + 1 := by
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  have : (c - ω) * (c - (ω + 1)) = 0 := by
    have e : (c - ω) * (c - (ω + 1)) = (c ^ 2 + c + 1) - (ω ^ 2 + ω + 1) - 2 * c * ω - 2 * c
        + 2 * ω ^ 2 + 2 * ω := by ring
    rw [e, hc, hω, h2]
    ring
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)



@[expose] noncomputable def frobM (X : Matrix (Fin 2) (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4 :=
  X.map (frobenius F4 2)

theorem frobM_add (X Y : Matrix (Fin 2) (Fin 2) F4) : frobM (X + Y) = frobM X + frobM Y := by
  unfold frobM
  exact Matrix.map_add _ (map_add _) X Y

theorem frobM_mul (X Y : Matrix (Fin 2) (Fin 2) F4) : frobM (X * Y) = frobM X * frobM Y := by
  unfold frobM
  exact Matrix.map_mul

theorem frobM_smul (c : F4) (X : Matrix (Fin 2) (Fin 2) F4) :
    frobM (c • X) = c ^ 2 • frobM X := by
  unfold frobM
  ext i j
  simp [frobenius_def, mul_pow]

theorem frobM_frobM (X : Matrix (Fin 2) (Fin 2) F4) : frobM (frobM X) = X := by
  have : Fintype F4 := Fintype.ofFinite F4
  have hcard : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]; norm_num
  unfold frobM
  ext i j
  simp only [Matrix.map_apply, frobenius_def]
  rw [← pow_mul]
  have := FiniteField.pow_card (X i j)
  rw [hcard] at this
  simpa using this

theorem frobM_sl (g : SL(2, F4)) : frobM (g : Matrix (Fin 2) (Fin 2) F4) =
    ((frobSL g : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) := rfl

@[expose] def trIf (δ : Bool) (X : Matrix (Fin 2) (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4 :=
  if δ then Xᵀ else X

@[expose] noncomputable def frobIf (ε : Bool) (X : Matrix (Fin 2) (Fin 2) F4) :
    Matrix (Fin 2) (Fin 2) F4 :=
  if ε then frobM X else X

theorem trIf_trIf (δ : Bool) (X : Matrix (Fin 2) (Fin 2) F4) : trIf δ (trIf δ X) = X := by
  cases δ <;> simp [trIf]

theorem frobIf_frobIf (ε : Bool) (X : Matrix (Fin 2) (Fin 2) F4) :
    frobIf ε (frobIf ε X) = X := by
  cases ε <;> simp [frobIf, frobM_frobM]

theorem trIf_add (δ : Bool) (X Y : Matrix (Fin 2) (Fin 2) F4) :
    trIf δ (X + Y) = trIf δ X + trIf δ Y := by
  cases δ <;> simp [trIf, Matrix.transpose_add]

theorem frobIf_add (ε : Bool) (X Y : Matrix (Fin 2) (Fin 2) F4) :
    frobIf ε (X + Y) = frobIf ε X + frobIf ε Y := by
  cases ε <;> simp [frobIf, frobM_add]

theorem trIf_smul (δ : Bool) (c : F4) (X : Matrix (Fin 2) (Fin 2) F4) :
    trIf δ (c • X) = c • trIf δ X := by
  cases δ <;> simp [trIf, Matrix.transpose_smul]

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def hatOf (e : V ≃+ Matrix (Fin 2) (Fin 2) F4) (γ : V ≃ₗ[ZMod 2] V) :
    Matrix (Fin 2) (Fin 2) F4 ≃+ Matrix (Fin 2) (Fin 2) F4 :=
  (e.symm.trans γ.toAddEquiv).trans e

theorem hatOf_apply (e : V ≃+ Matrix (Fin 2) (Fin 2) F4) (γ : V ≃ₗ[ZMod 2] V)
    (X : Matrix (Fin 2) (Fin 2) F4) : hatOf e γ X = e (γ (e.symm X)) := rfl

theorem hatOf_mul (e : V ≃+ Matrix (Fin 2) (Fin 2) F4) (γ δ : V ≃ₗ[ZMod 2] V)
    (X : Matrix (Fin 2) (Fin 2) F4) : hatOf e (γ * δ) X = hatOf e γ (hatOf e δ X) := by
  simp [hatOf_apply]

theorem hatOf_one (e : V ≃+ Matrix (Fin 2) (Fin 2) F4) (X : Matrix (Fin 2) (Fin 2) F4) :
    hatOf e 1 X = X := by
  simp [hatOf_apply]

theorem hatOf_inv_hatOf (e : V ≃+ Matrix (Fin 2) (Fin 2) F4) (γ : V ≃ₗ[ZMod 2] V)
    (X : Matrix (Fin 2) (Fin 2) F4) : hatOf e γ⁻¹ (hatOf e γ X) = X := by
  rw [← hatOf_mul, inv_mul_cancel, hatOf_one]

theorem hatOf_hatOf_inv (e : V ≃+ Matrix (Fin 2) (Fin 2) F4) (γ : V ≃ₗ[ZMod 2] V)
    (X : Matrix (Fin 2) (Fin 2) F4) : hatOf e γ (hatOf e γ⁻¹ X) = X := by
  rw [← hatOf_mul, mul_inv_cancel, hatOf_one]

theorem hatOf_injective (e : V ≃+ Matrix (Fin 2) (Fin 2) F4) {γ δ : V ≃ₗ[ZMod 2] V}
    (h : ∀ X, hatOf e γ X = hatOf e δ X) : γ = δ := by
  ext v
  have := h (e v)
  simp only [hatOf_apply, AddEquiv.symm_apply_apply] at this
  exact e.injective this

structure Model7 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) where
  e : V ≃+ Matrix (Fin 2) (Fin 2) F4
  θ : ↥(genFittingFStar ↥Γ) ≃* Pr
  hact : ∀ (f : ↥(genFittingFStar ↥Γ)) X,
    hatOf e ((f : ↥Γ) : V ≃ₗ[ZMod 2] V) X = act (θ f) X


namespace Model7

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (M : Model7 Γ)

theorem fstar_conj_mem (γ : ↥Γ) {f : ↥Γ} (hf : f ∈ genFittingFStar ↥Γ) :
    γ * f * γ⁻¹ ∈ genFittingFStar ↥Γ :=
  (A7Mod.genFittingFStar_normal' ↥Γ).conj_mem f hf γ

@[expose] noncomputable def alpha (γ : ↥Γ) (z : Pr) : Pr :=
  M.θ ⟨γ * (M.θ.symm z : ↥Γ) * γ⁻¹, fstar_conj_mem γ (M.θ.symm z).2⟩

theorem hat_act (γ : ↥Γ) (z : Pr) (X : Matrix (Fin 2) (Fin 2) F4) :
    hatOf M.e (γ : V ≃ₗ[ZMod 2] V) (act z X) =
      act (M.alpha γ z) (hatOf M.e (γ : V ≃ₗ[ZMod 2] V) X) := by
  have h1 := M.hact ⟨γ * (M.θ.symm z : ↥Γ) * γ⁻¹, fstar_conj_mem γ (M.θ.symm z).2⟩
    (hatOf M.e (γ : V ≃ₗ[ZMod 2] V) X)
  have h2 := M.hact (M.θ.symm z) X
  rw [MulEquiv.apply_symm_apply] at h2
  rw [alpha, ← h1]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hatOf_mul, hatOf_inv_hatOf]
  rw [h2]

theorem alpha_mul (γ : ↥Γ) (z w : Pr) : M.alpha γ (z * w) = M.alpha γ z * M.alpha γ w := by
  rw [alpha, alpha, alpha, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [map_mul, Subgroup.coe_mul]
  group

theorem alpha_spec (γ : ↥Γ) (z : Pr) :
    ((M.θ.symm (M.alpha γ z) : ↥(genFittingFStar ↥Γ)) : ↥Γ) = γ * (M.θ.symm z : ↥Γ) * γ⁻¹ := by
  rw [alpha, MulEquiv.symm_apply_apply]

theorem alpha_eq_iff (γ : ↥Γ) (z w : Pr) :
    M.alpha γ z = w ↔ γ * (M.θ.symm z : ↥Γ) * γ⁻¹ = (M.θ.symm w : ↥Γ) := by
  constructor
  · rintro rfl
    exact (M.alpha_spec γ z).symm
  · intro h
    apply M.θ.symm.injective
    apply Subtype.ext
    rw [M.alpha_spec, h]

theorem alpha_alpha_inv (γ : ↥Γ) (z : Pr) : M.alpha γ (M.alpha γ⁻¹ z) = z := by
  rw [M.alpha_eq_iff, M.alpha_spec]
  group

theorem act_injective {z w : Pr} (h : ∀ X, act z X = act w X) : z = w := by
  apply CFSG.Quasithin.G11.P3Ortho.Om4.rho'_injective (K := F4)
  ext X : 1
  rw [rho'_apply', rho'_apply']
  exact h X


theorem left_or_right (γ : ↥Γ) :
    (∀ g : SL(2, F4), (M.alpha γ (g, 1)).2 = 1) ∨ (∀ g : SL(2, F4), (M.alpha γ (g, 1)).1 = 1) := by
  have : IsSimpleGroup SL(2, F4) := CFSG.ComponentClassification.Asc75T4.isSimpleGroup_sl2 le_rfl
  have hnc : ¬ IsMulCommutative SL(2, F4) := not_isMulCommutative_sl2_gf (n := 2) (by norm_num)
  have hFn : ∀ (γ : ↥Γ), ∀ f ∈ genFittingFStar ↥Γ, γ * f * γ⁻¹ ∈ genFittingFStar ↥Γ :=
    fun γ f hf => fstar_conj_mem γ hf
  have key : ∀ (g : SL(2, F4)) (z : Pr),
      AxA.emb (genFittingFStar ↥Γ) M.θ z = γ * (M.θ.symm (g, 1) : ↥Γ) * γ⁻¹ →
        M.alpha γ (g, 1) = z := by
    intro g z hz
    rw [alpha]
    have : (⟨γ * (M.θ.symm (g, 1) : ↥Γ) * γ⁻¹, fstar_conj_mem γ (M.θ.symm (g, 1)).2⟩ :
        ↥(genFittingFStar ↥Γ)) = M.θ.symm z := Subtype.ext hz.symm
    rw [this, MulEquiv.apply_symm_apply]
  have hmem : ∀ g : SL(2, F4), γ * (M.θ.symm (g, 1) : ↥Γ) * γ⁻¹ ∈
      (AxA.sub1 (genFittingFStar ↥Γ) M.θ).map (MulAut.conj γ).toMonoidHom := fun g =>
    ⟨_, ⟨(g, 1), AxA.mem_fac1.mpr rfl, rfl⟩, rfl⟩
  rcases AxA.map_conj_sub1 hnc M.θ hFn γ with h | h
  · left
    intro g
    have h2 := hmem g
    rw [h] at h2
    obtain ⟨z, hz, hze⟩ := h2
    rw [key g z hze]
    exact AxA.mem_fac1.mp hz
  · right
    intro g
    have h2 := hmem g
    rw [h] at h2
    obtain ⟨z, hz, hze⟩ := h2
    rw [key g z hze]
    exact AxA.mem_fac2.mp hz


theorem act_smul (z : Pr) (c : F4) (X : Matrix (Fin 2) (Fin 2) F4) :
    act z (c • X) = c • act z X := by
  unfold act
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem exists_omega_conj {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) (γ : ↥Γ) :
    ∃ c : F4, (c = ω ∨ c = ω + 1) ∧ ∀ X, hatOf M.e (γ : V ≃ₗ[ZMod 2] V) (ω • X) =
      c • hatOf M.e (γ : V ≃ₗ[ZMod 2] V) X := by
  set gh := hatOf M.e (γ : V ≃ₗ[ZMod 2] V) with hgh
  set gi := hatOf M.e ((γ⁻¹ : ↥Γ) : V ≃ₗ[ZMod 2] V) with hgi
  have hgi_gh : ∀ X, gi (gh X) = X := fun X => by
    rw [hgi, hgh, Subgroup.coe_inv, hatOf_inv_hatOf]
  have hgh_gi : ∀ X, gh (gi X) = X := fun X => by
    rw [hgi, hgh, Subgroup.coe_inv, hatOf_hatOf_inv]
  let y : Matrix (Fin 2) (Fin 2) F4 →+ Matrix (Fin 2) (Fin 2) F4 :=
    { toFun := fun X => gh (ω • gi X)
      map_zero' := by simp
      map_add' := fun X Y => by simp [smul_add] }
  have hy : ∀ X, y X = gh (ω • gi X) := fun X => rfl
  have hyact : ∀ (z : Pr) X, y (act z X) = act z (y X) := by
    intro z X
    rw [hy, hy]
    have h1 : gi (act z X) = act (M.alpha γ⁻¹ z) (gi X) := M.hat_act γ⁻¹ z X
    rw [h1, ← act_smul, M.hat_act γ (M.alpha γ⁻¹ z), M.alpha_alpha_inv]
  have hl : ∀ (g : SL(2, F4)) X, y ((g : Matrix (Fin 2) (Fin 2) F4) * X) =
      (g : Matrix _ _ F4) * y X := by
    intro g X
    have := hyact (g, 1) X
    simpa [act] using this
  have hr : ∀ (g : SL(2, F4)) X, y (X * (g : Matrix (Fin 2) (Fin 2) F4)) =
      y X * (g : Matrix _ _ F4) := by
    intro g X
    have := hyact (1, g⁻¹) X
    simpa [act] using this
  have hsc := eq_smul_of_comm y hl hr
  set c := y 1 0 0 with hc
  have hc2 : c ^ 2 + c + 1 = 0 := by
    have h1 : ∀ X, y (y X) + y X + X = 0 := by
      intro X
      rw [hy, hy, hgi_gh]
      have : gh (ω • ω • gi X) + gh (ω • gi X) + gh (gi X) = gh ((ω ^ 2 + ω + 1) • gi X) := by
        rw [add_smul, add_smul, one_smul, sq, mul_smul, map_add, map_add]
      rw [hgh_gi] at this
      rw [this, hω, zero_smul, map_zero]
    have h2 := h1 1
    rw [hsc, hsc (1 : Matrix (Fin 2) (Fin 2) F4), smul_smul, ← add_smul] at h2
    have h3 := congrFun (congrFun h2 0) 0
    simp at h3
    linear_combination h3
  refine ⟨c, eq_omega_of_sq hω hc2, fun X => ?_⟩
  have := hsc (gh X)
  rw [hy, hgi_gh] at this
  exact this


theorem exists_shape {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) (γ : ↥Γ) :
    ∃ (P Q : Matrix (Fin 2) (Fin 2) F4) (δ ε : Bool), IsUnit P.det ∧ IsUnit Q.det ∧
      (ε = false ↔ ∀ X, hatOf M.e (γ : V ≃ₗ[ZMod 2] V) (ω • X) =
        ω • hatOf M.e (γ : V ≃ₗ[ZMod 2] V) X) ∧
      (δ = false ↔ ∀ g : SL(2, F4), (M.alpha γ (g, 1)).2 = 1) ∧
      ∀ X, hatOf M.e (γ : V ≃ₗ[ZMod 2] V) X = trIf δ (P * frobIf ε X * Q) := by
  classical
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  have hω2 : ω ^ 2 = ω + 1 := by
    have : ω ^ 2 = ω ^ 2 + ω + 1 + (ω + 1) := by
      rw [show ω ^ 2 + ω + 1 + (ω + 1) = ω ^ 2 + 2 * ω + 2 by ring, h2]; ring
    rw [this, hω, zero_add]
  obtain ⟨c, hc, hγω⟩ := M.exists_omega_conj hω γ
  set gh := hatOf M.e (γ : V ≃ₗ[ZMod 2] V) with hgh
  set gi := hatOf M.e ((γ⁻¹ : ↥Γ) : V ≃ₗ[ZMod 2] V) with hgi
  have hgi_gh : ∀ X, gi (gh X) = X := fun X => by
    rw [hgi, hgh, Subgroup.coe_inv, hatOf_inv_hatOf]
  have hgh_gi : ∀ X, gh (gi X) = X := fun X => by
    rw [hgi, hgh, Subgroup.coe_inv, hatOf_hatOf_inv]
  have hωne : ω ≠ ω + 1 := fun h => by simp at h
  set ε : Bool := decide (c = ω + 1) with hε
  set δ : Bool := decide ¬ (∀ g : SL(2, F4), (M.alpha γ (g, 1)).2 = 1) with hδ
  let w : Matrix (Fin 2) (Fin 2) F4 → Matrix (Fin 2) (Fin 2) F4 := fun X => trIf δ (gh (frobIf ε X))
  have hw_add : ∀ X Y, w (X + Y) = w X + w Y := fun X Y => by
    simp only [w, frobIf_add, map_add, trIf_add]
  have hw_ω : ∀ X, w (ω • X) = ω • w X := by
    intro X
    simp only [w]
    rw [← trIf_smul]
    congr 1
    rcases hc with rfl | rfl
    · have hε' : ε = false := by simp [hε, hωne]
      rw [hε']
      simpa [frobIf] using hγω X
    · have hε' : ε = true := by simp [hε]
      rw [hε']
      simp only [frobIf, ↓reduceIte]
      rw [frobM_smul, hω2, add_smul, one_smul, map_add, hγω, add_smul, one_smul, add_assoc,
        ← two_smul F4 (gh (frobM X)), h2, zero_smul, add_zero]
  have hw_smul : ∀ (a : F4) X, w (a • X) = a • w X := by
    intro a X
    rcases f4_cases hω a with rfl | rfl | rfl | rfl
    · have h0 : w 0 = 0 := by simpa using hw_add 0 0
      simp [h0]
    · simp
    · exact hw_ω X
    · rw [add_smul, one_smul, hw_add, hw_ω, add_smul, one_smul]
  let wl : Matrix (Fin 2) (Fin 2) F4 ≃ₗ[F4] Matrix (Fin 2) (Fin 2) F4 :=
    { toFun := w
      invFun := fun X => frobIf ε (gi (trIf δ X))
      map_add' := hw_add
      map_smul' := hw_smul
      left_inv := fun X => by simp only [w, trIf_trIf, hgi_gh, frobIf_frobIf]
      right_inv := fun X => by simp only [w, frobIf_frobIf, hgh_gi, trIf_trIf] }
  have hwl_apply : ∀ Y, wl Y = trIf δ (gh (frobIf ε Y)) := fun Y => rfl
  have hwl : ∀ g : SL(2, F4), ∃ g' : SL(2, F4), ∀ X,
      wl ((g : Matrix (Fin 2) (Fin 2) F4) * X) = (g' : Matrix _ _ F4) * wl X := by
    intro g
    set g₁ : SL(2, F4) := if ε then frobSL g else g with hg₁
    have hfg : ∀ X, frobIf ε ((g : Matrix (Fin 2) (Fin 2) F4) * X) =
        act (g₁, 1) (frobIf ε X) := by
      intro X
      simp only [act, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, hg₁]
      cases ε <;> simp [frobIf, frobM_mul, frobM_sl]
    by_cases hL : ∀ g : SL(2, F4), (M.alpha γ (g, 1)).2 = 1
    · have hδ' : δ = false := by simp [hδ, hL]
      refine ⟨(M.alpha γ (g₁, 1)).1, fun X => ?_⟩
      rw [hwl_apply, hwl_apply, hfg, hgh, M.hat_act, ← hgh, hδ']
      have hz : M.alpha γ (g₁, 1) = ((M.alpha γ (g₁, 1)).1, 1) := Prod.ext rfl (hL g₁)
      rw [hz]
      simp [trIf, act]
    · have hδ' : δ = true := by simp [hδ, hL]
      have hR := (M.left_or_right γ).resolve_left hL
      set h' := (M.alpha γ (g₁, 1)).2 with hh'
      refine ⟨⟨((h'⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4)ᵀ, by
        rw [Matrix.det_transpose]; exact (h'⁻¹).2⟩, fun X => ?_⟩
      rw [hwl_apply, hwl_apply, hfg, hgh, M.hat_act, ← hgh, hδ']
      have hz : M.alpha γ (g₁, 1) = (1, h') := Prod.ext (hR g₁) rfl
      rw [hz]
      simp [trIf, act, Matrix.transpose_mul]
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_eq_mul_mul wl hwl
  refine ⟨P, Q, δ, ε, hP, hQ, ?_, ?_, fun X => ?_⟩
  · constructor
    · intro hε0 X
      have : c = ω := by
        rcases hc with h | h
        · exact h
        · exfalso; simp [hε, h] at hε0
      rw [hγω, this]
    · intro hlin
      by_contra hε1
      have hεt : c = ω + 1 := by simpa [hε] using hε1
      have := hlin 1
      rw [hγω, hεt] at this
      have h3 : (1 : F4) • gh 1 = 0 := by
        have : (ω + 1) • gh 1 - ω • gh 1 = 0 := by rw [this, sub_self]
        rwa [← sub_smul, add_sub_cancel_left] at this
      rw [one_smul] at h3
      have : (1 : Matrix (Fin 2) (Fin 2) F4) = 0 := by
        rw [← hgi_gh 1, h3, map_zero]
      exact one_ne_zero this
  · simp [hδ]
  · have h1 := hPQ (frobIf ε X)
    have h2 : wl (frobIf ε X) = trIf δ (gh X) := by
      rw [hwl_apply, frobIf_frobIf]
    rw [h2] at h1
    rw [← trIf_trIf δ (gh X), h1]

end Model7

end Model

end CFSG.Quasithin.H13.L14324
