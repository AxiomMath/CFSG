module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF2
import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF1

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec19

section Plain

variable {F : Type} [Field F] [Finite F]

theorem sl2_lang_general (φ : F ≃+* F) (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1)
    (a : Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : a * Matrix.SpecialLinearGroup.map φ.toRingHom a *
      Matrix.SpecialLinearGroup.map φ.toRingHom (Matrix.SpecialLinearGroup.map φ.toRingHom a) = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      a = g * (Matrix.SpecialLinearGroup.map φ.toRingHom g)⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  set A : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hA
  have hA3 : CFSG.GH74.GLS.IVK.H90.Ai φ A 3 = 1 := by
    have h := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F)) ha
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h
    show A * (A * (A * (1 : Matrix (Fin 2) (Fin 2) F).map φ).map φ).map φ = 1
    have h1 : (1 : Matrix (Fin 2) (Fin 2) F).map φ = 1 := Matrix.map_one φ (map_zero φ) (map_one φ)
    rw [h1, mul_one, Matrix.map_mul, ← mul_assoc]
    exact h
  obtain ⟨B, hBdet, hAB⟩ := CFSG.GH74.GLS.IVK.H90.speiser φ A 3 hord (by norm_num) hA3
  have hAdet : A.det = 1 := a.2
  have hmapdet : ∀ M : Matrix (Fin 2) (Fin 2) F, (M.map φ).det = φ M.det := fun M => by
    have := RingHom.map_det φ.toRingHom M
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hδσ : φ B.det = B.det := by
    have h := congrArg Matrix.det hAB
    rw [Matrix.det_mul, hAdet, one_mul, hmapdet] at h
    exact h
  set δ := B.det with hδ
  set D : Matrix (Fin 2) (Fin 2) F := !![δ⁻¹, 0; 0, 1] with hDdef
  have hD : D.det = δ⁻¹ := by simp [hDdef, Matrix.det_fin_two_of]
  have hB'det : (B * D).det = 1 := by
    rw [Matrix.det_mul, hD]
    exact mul_inv_cancel₀ hBdet
  have hDσ : D.map φ = D := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hDdef, map_inv₀, hδσ]
  refine ⟨⟨B * D, hB'det⟩, ?_⟩
  have key : a * Matrix.SpecialLinearGroup.map φ.toRingHom (⟨B * D, hB'det⟩ :
      Matrix.SpecialLinearGroup (Fin 2) F) = ⟨B * D, hB'det⟩ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show A * (φ.toRingHom.mapMatrix (B * D)) = B * D
    rw [map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
    show A * (B.map φ * D.map φ) = B * D
    rw [hDσ, ← mul_assoc, hAB]
  exact eq_mul_inv_of_mul_eq key

theorem sl2_map_map (f g : F ≃+* F) (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup.map f.toRingHom (Matrix.SpecialLinearGroup.map g.toRingHom M) =
      Matrix.SpecialLinearGroup.map (f * g).toRingHom M := by
  apply Subtype.ext
  ext i j
  rfl

end Plain

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem tauPow_mem_A (hAB : TrialityABFacts σ) (e : ℕ) {a : C0 σ} (ha : a ∈ Asub σ) :
    (tauAut σ ^ e) a ∈ Asub σ := by
  induction e with
  | zero => simpa using ha
  | succ e ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact hAB.tau_A _ ih

theorem tauPow_apply_B (hAB : TrialityABFacts σ) (e : ℕ) {b : C0 σ} (hb : b ∈ Bsub σ) :
    (tauAut σ ^ e) b = b := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', MulAut.mul_apply, ih, hAB.tau_B b hb]

theorem conj_mul_pow_three (g : C0 σ) (φ : MulAut (C0 σ)) (hφ : φ ^ 3 = 1) :
    (MulAut.conj g * φ) ^ 3 = MulAut.conj (g * φ g * φ (φ g)) := by
  refine MulEquiv.ext fun k => ?_
  have h3 : ∀ x : C0 σ, φ (φ (φ x)) = x := fun x => by
    have := congrArg (fun ψ : MulAut (C0 σ) => ψ x) hφ
    simpa [pow_succ, MulAut.mul_apply] using this
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h3]

theorem outer_commute_B_comm (hAB : TrialityABFacts σ) (n : ℕ) (hn : 1 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {b : C0 σ}
    (hb : b ∈ Bsub σ) {g : C0 σ} {e : ℕ}
    (hcomm : Commute (MulAut.conj b) (MulAut.conj g * tauAut σ ^ e)) : b * g = g * b := by
  have hinj := conj_injective_C0 σ n hn hX hσ
  have hτb := tauPow_apply_B σ hAB e hb
  have key : ∀ k : C0 σ, (b * g) * (tauAut σ ^ e) k * (b * g)⁻¹ =
      (g * b) * (tauAut σ ^ e) k * (g * b)⁻¹ := by
    intro k
    have h1 := congrArg (fun φ : MulAut (C0 σ) => φ k) hcomm.eq
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
    rw [map_mul, map_mul, map_inv, hτb] at h1
    calc (b * g) * (tauAut σ ^ e) k * (b * g)⁻¹
        = b * (g * (tauAut σ ^ e) k * g⁻¹) * b⁻¹ := by group
      _ = g * (b * (tauAut σ ^ e) k * b⁻¹) * g⁻¹ := h1
      _ = (g * b) * (tauAut σ ^ e) k * (g * b)⁻¹ := by group
  have hconj : MulAut.conj (b * g) = MulAut.conj (g * b) := by
    refine MulEquiv.ext fun m => ?_
    have := key ((tauAut σ ^ e)⁻¹ m)
    rw [MulAut.apply_inv_self] at this
    simpa only [MulAut.conj_apply] using this
  exact hinj hconj

theorem outer_commute_mem_AB (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {b : C0 σ}
    (hb : b ∈ Bsub σ) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) {g : C0 σ} {e : ℕ}
    (hcomm : Commute (MulAut.conj b) (MulAut.conj g * tauAut σ ^ e)) : g ∈ Asub σ ⊔ Bsub σ :=
  centralizer_le_AB σ hAB n hn hX hσ hb hb3 hb1
    (Subgroup.mem_centralizer_singleton_iff.mpr
      (outer_commute_B_comm σ hAB n (by omega) hX hσ hb hcomm).symm)

theorem mul_three_comm {G : Type*} [Group G] (u₁ u₂ u₃ b : G) (h2 : b * u₂ = u₂ * b)
    (h3 : b * u₃ = u₃ * b) : (u₁ * b) * (u₂ * b) * (u₃ * b) = u₁ * u₂ * u₃ * b ^ 3 := by
  calc (u₁ * b) * (u₂ * b) * (u₃ * b) = u₁ * (b * u₂) * b * (u₃ * b) := by group
    _ = u₁ * (u₂ * b) * b * (u₃ * b) := by rw [h2]
    _ = u₁ * u₂ * (b * b * u₃) * b := by group
    _ = u₁ * u₂ * (b * (b * u₃)) * b := by group
    _ = u₁ * u₂ * (b * (u₃ * b)) * b := by rw [h3]
    _ = u₁ * u₂ * ((b * u₃) * b) * b := by group
    _ = u₁ * u₂ * ((u₃ * b) * b) * b := by rw [h3]
    _ = u₁ * u₂ * u₃ * b ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem outer_norm_split (hAB : TrialityABFacts σ) (n : ℕ) (hn : 1 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {a' b' : C0 σ}
    (ha' : a' ∈ Asub σ) (hb' : b' ∈ Bsub σ) {e : ℕ}
    (h3 : (MulAut.conj (a' * b') * tauAut σ ^ e) ^ 3 = 1) :
    a' * (tauAut σ ^ e) a' * (tauAut σ ^ e) ((tauAut σ ^ e) a') = 1 ∧ b' ^ 3 = 1 := by
  have hinj := conj_injective_C0 σ n hn hX hσ
  have hφ3 : (tauAut σ ^ e) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hAB.tau3, one_pow]
  rw [conj_mul_pow_three σ _ _ hφ3] at h3
  have hN : (a' * b') * (tauAut σ ^ e) (a' * b') * (tauAut σ ^ e) ((tauAut σ ^ e) (a' * b')) = 1 :=
    hinj (by rw [map_one]; exact h3)
  have hφb : (tauAut σ ^ e) b' = b' := tauPow_apply_B σ hAB e hb'
  have hφa : (tauAut σ ^ e) a' ∈ Asub σ := tauPow_mem_A σ hAB e ha'
  have hφφa : (tauAut σ ^ e) ((tauAut σ ^ e) a') ∈ Asub σ := tauPow_mem_A σ hAB e hφa
  simp only [map_mul, hφb] at hN
  have hc : ∀ x ∈ Asub σ, b' * x = x * b' := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hb' x hx).symm
  rw [mul_three_comm _ _ _ _ (hc _ hφa) (hc _ hφφa)] at hN
  have hmemA : a' * (tauAut σ ^ e) a' * (tauAut σ ^ e) ((tauAut σ ^ e) a') ∈ Asub σ :=
    (Asub σ).mul_mem ((Asub σ).mul_mem ha' hφa) hφφa
  have hb3A : b' ^ 3 ∈ Asub σ := by
    have : b' ^ 3 = (a' * (tauAut σ ^ e) a' * (tauAut σ ^ e) ((tauAut σ ^ e) a'))⁻¹ :=
      eq_inv_of_mul_eq_one_right hN
    rw [this]
    exact (Asub σ).inv_mem hmemA
  have hb3 : b' ^ 3 = 1 := by
    have : b' ^ 3 ∈ Asub σ ⊓ Bsub σ := Subgroup.mem_inf.mpr ⟨hb3A, (Bsub σ).pow_mem hb' 3⟩
    rw [hAB.inf_bot, Subgroup.mem_bot] at this
    exact this
  refine ⟨?_, hb3⟩
  rw [hb3, mul_one] at hN
  exact hN

theorem congr_conj_conj (k x : C0 σ) :
    (MulAut.congr (MulAut.conj k)).toMonoidHom (MulAut.conj x) = MulAut.conj (k * x * k⁻¹) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
    MulAut.conj_symm_apply, MulAut.conj_apply]
  group

theorem congr_conj_mul (k g : C0 σ) (φ : MulAut (C0 σ)) :
    (MulAut.congr (MulAut.conj k)).toMonoidHom (MulAut.conj g * φ) =
      MulAut.conj (k * g * (φ k)⁻¹) * φ := by
  refine MulEquiv.ext fun y => ?_
  have e1 : (MulAut.congr (MulAut.conj k)).toMonoidHom (MulAut.conj g * φ) y =
      k * (g * φ (k⁻¹ * y * k) * g⁻¹) * k⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulAut.conj_symm_apply, MulAut.conj_apply, MulAut.mul_apply]
  have e2 : (MulAut.conj (k * g * (φ k)⁻¹) * φ) y =
      (k * g * (φ k)⁻¹) * φ y * (k * g * (φ k)⁻¹)⁻¹ := by
    simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [e1, e2, map_mul, map_mul, map_inv]
  group

theorem congr_conj_pair (k x g : C0 σ) (φ : MulAut (C0 σ)) :
    (Subgroup.closure ({MulAut.conj x, MulAut.conj g * φ} : Set (MulAut (C0 σ)))).map
        (MulAut.congr (MulAut.conj k)).toMonoidHom =
      Subgroup.closure ({MulAut.conj (k * x * k⁻¹), MulAut.conj (k * g * (φ k)⁻¹) * φ} :
        Set (MulAut (C0 σ))) := by
  rw [MonoidHom.map_closure, Set.image_pair, congr_conj_conj, congr_conj_mul]

theorem sl2A_tauPow (hAB : TrialityABFacts σ) {ι : Asub σ ≃* Matrix.SpecialLinearGroup (Fin 2) X}
    (hι : ∀ (a : C0 σ) (ha : a ∈ Asub σ),
      ι ⟨tauAut σ a, hAB.tau_A a ha⟩ =
        Matrix.SpecialLinearGroup.map (σ : X →+* X) (ι ⟨a, ha⟩))
    (e : ℕ) {b : C0 σ} (hb : b ∈ Asub σ) :
    ι ⟨(tauAut σ ^ e) b, tauPow_mem_A σ hAB e hb⟩ =
      Matrix.SpecialLinearGroup.map (σ ^ e).toRingHom (ι ⟨b, hb⟩) := by
  induction e with
  | zero =>
    simp only [pow_zero]
    apply Subtype.ext
    ext i j
    rfl
  | succ e ih =>
    have h1 := hι ((tauAut σ ^ e) b) (tauPow_mem_A σ hAB e hb)
    have h2 : (⟨(tauAut σ ^ (e + 1)) b, tauPow_mem_A σ hAB (e + 1) hb⟩ : Asub σ) =
        ⟨tauAut σ ((tauAut σ ^ e) b), hAB.tau_A _ (tauPow_mem_A σ hAB e hb)⟩ := by
      apply Subtype.ext
      show (tauAut σ ^ (e + 1)) b = tauAut σ ((tauAut σ ^ e) b)
      rw [pow_succ', MulAut.mul_apply]
    rw [h2, h1, ih]
    refine (sl2_map_map σ (σ ^ e) _).trans ?_
    rw [pow_succ']

theorem exists_lang_Asub (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {e : ℕ}
    (he : e = 1 ∨ e = 2) {a : C0 σ} (ha : a ∈ Asub σ)
    (hN : a * (tauAut σ ^ e) a * (tauAut σ ^ e) ((tauAut σ ^ e) a) = 1) :
    ∃ h ∈ Asub σ, a = h * ((tauAut σ ^ e) h)⁻¹ := by
  obtain ⟨ι, hι⟩ := hAB.sl2A
  have hσ3 := sigma_pow_three σ n hX hσ
  have hσ1 : σ ≠ 1 := nf1_sigma_ne_one σ n (by omega) hX hσ
  have hφ3 : (σ ^ e) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
  have hφ1 : σ ^ e ≠ 1 := by
    rcases he with rfl | rfl
    · simpa using hσ1
    · intro h2
      apply hσ1
      have : σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      rw [this, hσ3, h2]
      simp
  have hb1 := tauPow_mem_A σ hAB e ha
  have hb2 := tauPow_mem_A σ hAB e hb1
  have hNs : ι ⟨a, ha⟩ * Matrix.SpecialLinearGroup.map (σ ^ e).toRingHom (ι ⟨a, ha⟩) *
      Matrix.SpecialLinearGroup.map (σ ^ e).toRingHom
        (Matrix.SpecialLinearGroup.map (σ ^ e).toRingHom (ι ⟨a, ha⟩)) = 1 := by
    have h1 := sl2A_tauPow σ hAB hι e ha
    have h2 := sl2A_tauPow σ hAB hι e hb1
    rw [← h1, ← h2]
    have h3 : (⟨a, ha⟩ : Asub σ) * ⟨(tauAut σ ^ e) a, hb1⟩ * ⟨(tauAut σ ^ e) ((tauAut σ ^ e) a), hb2⟩
        = 1 := Subtype.ext hN
    rw [← map_mul, ← map_mul, h3, map_one]
  obtain ⟨g, hg⟩ := sl2_lang_general (σ ^ e) hφ3 hφ1 (ι ⟨a, ha⟩) hNs
  refine ⟨((ι.symm g : Asub σ) : C0 σ), (ι.symm g).2, ?_⟩
  have hgt := sl2A_tauPow σ hAB hι e (ι.symm g).2
  have hfin : ι ⟨a, ha⟩ = ι ((ι.symm g) * ⟨(tauAut σ ^ e) ((ι.symm g : Asub σ) : C0 σ),
      tauPow_mem_A σ hAB e (ι.symm g).2⟩⁻¹) := by
    rw [map_mul, map_inv, hgt, hg]
    simp
  have := congrArg Subtype.val (ι.injective hfin)
  simpa using this

theorem outer_Y_case (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x g : C0 σ} {e : ℕ}
    (he : e = 1 ∨ e = 2) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hβ3 : (MulAut.conj g * tauAut σ ^ e) ^ 3 = 1)
    (hcomm : Commute (MulAut.conj x) (MulAut.conj g * tauAut σ ^ e))
    (hY : ∃ h : C0 σ, h * x * h⁻¹ ∈ Bsub σ) :
    ∃ (ψ : MulAut (C0 σ)) (b : C0 σ), b ∈ Bsub σ ∧ b ^ 3 = 1 ∧ b ≠ 1 ∧
      (Subgroup.closure ({MulAut.conj x, MulAut.conj g * tauAut σ ^ e} :
          Set (MulAut (C0 σ)))).map (MulAut.congr ψ).toMonoidHom =
        Subgroup.closure ({MulAut.conj b, tauAut σ} : Set (MulAut (C0 σ))) := by
  have hn1 : 1 ≤ n := by omega
  have h3 : (3 : X) ≠ 0 := three_ne_zero_of_cube n hn1 hX
  have h3k := three_ne_zero_fixSubfield σ h3
  obtain ⟨eB⟩ := hAB.sl2B
  obtain ⟨h₁, hb₀⟩ := hY
  set b₀ : C0 σ := h₁ * x * h₁⁻¹ with hb₀def
  have hb₀3 : b₀ ^ 3 = 1 := by rw [hb₀def, conj_pow, hx3]; group
  have hb₀1 : b₀ ≠ 1 := fun h => hx1 (by
    have : x = h₁⁻¹ * b₀ * h₁ := by rw [hb₀def]; group
    rw [this, h]; group)
  set φ : MulAut (C0 σ) := tauAut σ ^ e with hφ
  set g₁ : C0 σ := h₁ * g * (φ h₁)⁻¹ with hg₁
  have hcomm₁ : Commute (MulAut.conj b₀) (MulAut.conj g₁ * φ) := by
    have := hcomm.map (MulAut.congr (MulAut.conj h₁)).toMonoidHom
    rwa [congr_conj_conj, congr_conj_mul] at this
  have hβ₁3 : (MulAut.conj g₁ * φ) ^ 3 = 1 := by
    have := congrArg (MulAut.congr (MulAut.conj h₁)).toMonoidHom hβ3
    rwa [map_pow, congr_conj_mul, map_one] at this
  have hg₁AB := outer_commute_mem_AB σ hAB n hn hX hσ hb₀ hb₀3 hb₀1 hcomm₁
  obtain ⟨a', ha', b', hb', hg₁eq⟩ := mem_sup_AB_decomp σ hg₁AB
  obtain ⟨hN, hb'3⟩ := outer_norm_split σ hAB n hn1 hX hσ ha' hb'
    (by rw [← hg₁eq]; exact hβ₁3)
  obtain ⟨h, hh, hlang⟩ := exists_lang_Asub σ hAB n hn hX hσ he ha' hN
  have hb'b₀ : b₀ * b' = b' * b₀ := by
    have hg := outer_commute_B_comm σ hAB n hn1 hX hσ hb₀ hcomm₁
    rw [hg₁eq] at hg
    have hab : b₀ * a' = a' * b₀ :=
      (Subgroup.mem_centralizer_iff.mp hb₀ a' ha').symm
    have : a' * (b₀ * b') = a' * (b' * b₀) := by
      calc a' * (b₀ * b') = (a' * b₀) * b' := by group
        _ = (b₀ * a') * b' := by rw [hab]
        _ = b₀ * (a' * b') := by group
        _ = (a' * b') * b₀ := hg
        _ = a' * (b' * b₀) := by group
    exact mul_left_cancel this
  have hb'z : b' ∈ Subgroup.zpowers b₀ :=
    zpowers_of_commuting_cube_one_of_iso h3k (Bsub σ) eB hb₀ hb' hb₀3 hb₀1 hb'3 hb'b₀
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb'z
  refine ⟨MulAut.conj (h⁻¹ * h₁), b₀, hb₀, hb₀3, hb₀1, ?_⟩
  rw [congr_conj_pair σ (h⁻¹ * h₁) x g (tauAut σ ^ e)]
  have hhb₀ : h * b₀ = b₀ * h := Subgroup.mem_centralizer_iff.mp hb₀ h hh
  have e1 : (h⁻¹ * h₁) * x * (h⁻¹ * h₁)⁻¹ = b₀ := by
    calc (h⁻¹ * h₁) * x * (h⁻¹ * h₁)⁻¹ = h⁻¹ * (h₁ * x * h₁⁻¹) * h := by group
      _ = h⁻¹ * (b₀ * h) := by rw [← hb₀def]; group
      _ = h⁻¹ * (h * b₀) := by rw [hhb₀]
      _ = b₀ := by group
  have hφh : φ h ∈ Asub σ := tauPow_mem_A σ hAB e hh
  have hφb' : φ b' = b' := tauPow_apply_B σ hAB e hb'
  have hb'φh : b' * φ h = φ h * b' := (Subgroup.mem_centralizer_iff.mp hb' (φ h) hφh).symm
  have e2 : (h⁻¹ * h₁) * g * (φ (h⁻¹ * h₁))⁻¹ = b' := by
    have hφinv : φ (h⁻¹ * h₁) = (φ h)⁻¹ * φ h₁ := by rw [map_mul, map_inv]
    rw [hφinv]
    have h4 : (h⁻¹ * h₁) * g * ((φ h)⁻¹ * φ h₁)⁻¹ = h⁻¹ * (h₁ * g * (φ h₁)⁻¹) * φ h := by group
    rw [h4, ← hg₁, hg₁eq, hlang]
    calc h⁻¹ * (h * (φ h)⁻¹ * b') * φ h = (φ h)⁻¹ * (b' * φ h) := by group
      _ = (φ h)⁻¹ * (φ h * b') := by rw [hb'φh]
      _ = b' := by group
  rw [e1, e2]
  have hcb' : MulAut.conj b' = (MulAut.conj b₀) ^ m := by rw [← hm, map_zpow]
  have hτφ : tauAut σ ∈ Subgroup.zpowers φ := by
    rcases he with rfl | rfl
    · simp [hφ]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩
      have h4 : tauAut σ ^ 4 = tauAut σ := by
        rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hAB.tau3, one_mul]
      show (tauAut σ ^ 2) ^ (2 : ℤ) = tauAut σ
      rw [zpow_ofNat, ← pow_mul]
      exact h4
  have hφτ : φ ∈ Subgroup.zpowers (tauAut σ) := by
    rw [hφ]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) e
  rw [hcb']
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine mul_mem (zpow_mem (Subgroup.subset_closure (by simp)) m) ?_
      exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) hφτ
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      have hφL : φ ∈ Subgroup.closure ({MulAut.conj b₀, (MulAut.conj b₀) ^ m * φ} :
          Set (MulAut (C0 σ))) := by
        have h5 : φ = ((MulAut.conj b₀) ^ m)⁻¹ * ((MulAut.conj b₀) ^ m * φ) := by group
        rw [h5]
        refine mul_mem (inv_mem (zpow_mem (Subgroup.subset_closure (by simp)) m))
          (Subgroup.subset_closure (by simp))
      exact (Subgroup.zpowers_le.mpr hφL) hτφ

end Model

end CFSG.RankThree.PartTwo.Sec19
