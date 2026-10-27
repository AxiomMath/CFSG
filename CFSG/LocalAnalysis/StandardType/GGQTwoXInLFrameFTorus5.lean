module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus4
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.QTwoFrameTorus

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R]

private lemma frame_charP_two {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4) :
    CharP M 2 := by
  let _ : Fintype M := Fintype.ofFinite M
  have h : Fintype.card M = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hM]
    norm_num
  exact charP_of_card_eq_prime_pow h

private noncomputable def framePermGL {n : ℕ} {M : Type} [Field M]
    (σ : Equiv.Perm (Fin n)) : GL (Fin n) M :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (σ.permMatrix M) (by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])

private lemma framePermGL_val {n : ℕ} {M : Type} [Field M] (σ : Equiv.Perm (Fin n)) :
    ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = σ.permMatrix M :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma frame_permMatrix_apply {n : ℕ} {M : Type} [Field M]
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (σ.permMatrix M) i j = if j = σ i then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  by_cases h : j = σ i
  · simp [h]
  · have h' : σ i ≠ j := fun hh => h hh.symm
    simp [h, h']

private lemma framePermGL_mem_heldGU {n : ℕ} {M : Type} [Field M] [Finite M]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (σ : Equiv.Perm (Fin n)) : framePermGL σ ∈ heldGU n M τ hτ := by
  rw [mem_heldGU, framePermGL_val]
  have hmap : (σ.permMatrix M).map τ = σ.permMatrix M := by
    ext i j
    rw [Matrix.map_apply, frame_permMatrix_apply]
    by_cases h : j = σ i <;> simp [h]
  rw [hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

private lemma framePermGL_mem_heldSU {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (σ : Equiv.Perm (Fin n)) : framePermGL σ ∈ heldSU n M τ hτ := by
  have hchar : CharP M 2 := frame_charP_two hM
  refine Subgroup.mem_inf.mpr ⟨framePermGL_mem_heldGU σ, ?_⟩
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, framePermGL_val, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · rw [h]
    have hneg : (-1 : M) = 1 := @CharTwo.neg_eq M _ hchar 1
    simp [hneg]

private lemma framePermGL_conj_diag {n : ℕ} {M : Type} [Field M]
    (σ : Equiv.Perm (Fin n)) (a : Fin n → M) :
    ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        Matrix.diagonal a *
        (((framePermGL σ)⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (a ∘ σ) := by
  have hmul : ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
      Matrix.diagonal a =
      Matrix.diagonal (a ∘ σ) *
        ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
    rw [framePermGL_val]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, frame_permMatrix_apply]
    by_cases h : j = σ i <;> simp [h]
  have hPP : ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
      (((framePermGL σ)⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = 1 := by
    have h := congrArg (fun X : GL (Fin n) M => ((X : Matrix (Fin n) (Fin n) M)))
      (mul_inv_cancel (framePermGL σ))
    exact h
  calc
    ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        Matrix.diagonal a *
        (((framePermGL σ)⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)
        = (Matrix.diagonal (a ∘ σ) *
            ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) *
            (((framePermGL σ)⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
          rw [hmul]
    _ = Matrix.diagonal (a ∘ σ) *
          (((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
            (((framePermGL σ)⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) := by
          rw [mul_assoc]
    _ = Matrix.diagonal (a ∘ σ) := by rw [hPP, Matrix.mul_one]

private lemma framePermGL_inv {n : ℕ} {M : Type} [Field M] (σ : Equiv.Perm (Fin n)) :
    (framePermGL (M := M) σ)⁻¹ = framePermGL (M := M) σ⁻¹ := by
  apply Units.ext
  rw [Matrix.coe_units_inv, framePermGL_val (M := M), framePermGL_val (M := M)]
  exact Matrix.inv_eq_right_inv (by
    rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one])

private lemma framePermGL_conj_mem_diagSub {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (σ : Equiv.Perm (Fin n))
    (T : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
    (⟨framePermGL σ, framePermGL_mem_heldGU σ⟩ : ↥(heldGU n M τ hτ)) *
        (T : ↥(heldGU n M τ hτ)) *
        (⟨framePermGL σ, framePermGL_mem_heldGU σ⟩ : ↥(heldGU n M τ hτ))⁻¹ ∈
      frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2 := by
  have hTdiag : ∀ i j, i ≠ j →
      (((T : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) i j = 0 :=
    (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2
      (T : ↥(heldGU n M τ hτ))).mp T.2
  let d : Fin n → M := fun i =>
    (((T : ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i
  have hTmat : (((T : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hTdiag i j hij]
  have hconj := framePermGL_conj_diag σ d
  refine (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 _).mpr ?_
  intro i j hij
  rw [show ((((⟨framePermGL σ, framePermGL_mem_heldGU σ⟩ :
      ↥(heldGU n M τ hτ)) * (T : ↥(heldGU n M τ hτ)) *
      (⟨framePermGL σ, framePermGL_mem_heldGU σ⟩ :
        ↥(heldGU n M τ hτ))⁻¹ : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) =
      ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        (((T : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
          Matrix (Fin n) (Fin n) M) *
        (((framePermGL σ)⁻¹ : GL (Fin n) M) :
          Matrix (Fin n) (Fin n) M) from rfl]
  rw [hTmat]
  rw [show ((framePermGL σ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
      Matrix.diagonal d *
      (((framePermGL σ)⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (d ∘ σ) from hconj]
  exact Matrix.diagonal_apply_ne _ hij

private lemma framePermGL_mem_normalizer_E {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L)
    (σ : Equiv.Perm (Fin n)) :
    ρ (⟨framePermGL σ, framePermGL_mem_heldGU σ⟩ : ↥(heldGU n M τ hτ)) ∈
      Subgroup.normalizer (E : Set R) := by
  have hEeq := frame_E_eq_diagSub (n := n) (M := M) (τ := τ) (hτ := hτ) (ρ := ρ)
    (E := E) (x := x) (L := L) hM hτ2 hU
  let P : ↥(heldGU n M τ hτ) := ⟨framePermGL σ, framePermGL_mem_heldGU σ⟩
  let Pinv : ↥(heldGU n M τ hτ) := ⟨framePermGL σ⁻¹, framePermGL_mem_heldGU σ⁻¹⟩
  have hPinv : P⁻¹ = Pinv := by
    apply Subtype.ext
    exact framePermGL_inv (M := M) σ
  have hfwd : ∀ e ∈ E, ρ P * e * (ρ P)⁻¹ ∈ E := by
    intro e he
    obtain ⟨T, hTdiag, hTe⟩ := (hU.2.1 e).mp he
    let Tsub : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
      ⟨T, (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 T).mpr hTdiag⟩
    have hmem := framePermGL_conj_mem_diagSub hM hτ2 σ Tsub
    have hρmem : ρ (P * T * P⁻¹) ∈ E := by
      rw [hEeq]
      exact Subgroup.mem_map.mpr ⟨P * T * P⁻¹, hmem, rfl⟩
    have heq : ρ P * e * (ρ P)⁻¹ = ρ (P * T * P⁻¹) := by
      rw [← hTe, map_mul, map_inv, map_mul]
    rwa [heq]
  have hinv : ∀ e ∈ E, (ρ P)⁻¹ * e * ρ P ∈ E := by
    intro e he
    obtain ⟨T, hTdiag, hTe⟩ := (hU.2.1 e).mp he
    let Tsub : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
      ⟨T, (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 T).mpr hTdiag⟩
    have hmem := framePermGL_conj_mem_diagSub hM hτ2 σ⁻¹ Tsub
    have hρmem : ρ (Pinv * T * Pinv⁻¹) ∈ E := by
      rw [hEeq]
      exact Subgroup.mem_map.mpr ⟨Pinv * T * Pinv⁻¹, hmem, rfl⟩
    have heq : (ρ P)⁻¹ * e * ρ P = ρ (Pinv * T * Pinv⁻¹) := by
      rw [← hTe, show Pinv = P⁻¹ from hPinv.symm, map_mul, map_mul, map_inv, inv_inv]
    rwa [heq]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hfwd h
  · intro hh
    have hh' := hinv (ρ P * h * (ρ P)⁻¹) hh
    rwa [show (ρ P)⁻¹ * (ρ P * h * (ρ P)⁻¹) * ρ P = h by group] at hh'

private lemma frame_automizer_eq {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3)
    (hc1 : (c : M) ≠ 1) :
    (ggAutomizer L E).map (ggLin (p := 3) (frameCoordAdd hM hτ2 hU c hgen hn)) =
      Subgroup.closure {T : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) |
        ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
          T v i = v (σ i)} := by
  apply le_antisymm
  · rw [ggAutomizer, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨g, hgL, hgN, hφg⟩ := hφ
    have hgLmap : g ∈ ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ := by
      rw [← hU.2.2.2.1]
      exact hgL
    obtain ⟨B, hBSU, hBg⟩ := Subgroup.mem_map.mp hgLmap
    have hBN := frame_mem_normalizer_diagSub_of_mem_normalizer_E hM hτ2 hU hBg hgN
    obtain ⟨σ, hσ⟩ := frame_exists_perm_of_normalizes hM hτ2 B hBN c hc1
    have hsupp := frame_col_support hM hτ2 B c hc1 σ hσ
    have hlin := frame_ggLin_eq_perm hM hτ2 hU c hgen hn hBg φ hφg σ hsupp
    rw [hlin]
    exact Subgroup.subset_closure ⟨σ.symm, fun v i => frameLinPerm_apply σ.symm v i⟩
  · rw [Subgroup.closure_le]
    rintro T ⟨σ, hT⟩
    have hTeq : T = frameLinPerm σ := by
      apply LinearEquiv.ext
      intro v
      funext i
      rw [frameLinPerm_apply]
      exact hT v i
    rw [hTeq]
    let P : ↥(heldGU n M τ hτ) :=
      ⟨framePermGL σ, framePermGL_mem_heldGU σ⟩
    have hPSU : (P : GL (Fin n) M) ∈ heldSU n M τ hτ :=
      framePermGL_mem_heldSU hM σ
    let g : R := ρ P
    have hgL : g ∈ L := by
      have hgmap : g ∈ ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ :=
        Subgroup.mem_map.mpr ⟨P, hPSU, rfl⟩
      rw [hU.2.2.2.1]
      exact hgmap
    have hgN : g ∈ Subgroup.normalizer (E : Set R) :=
      framePermGL_mem_normalizer_E hM hτ2 hU σ
    let φ : MulAut ↥E := ggConjAut E hgN
    have hφmem : φ ∈ ggAutomizer L E := ggConjAut_mem_ggAutomizer hgL hgN
    have hφ : ∀ e : ↥E, ((φ e : E) : R) = g * e * g⁻¹ := fun e =>
      ggConjAut_apply E hgN e
    have hsupp : ∀ i k : Fin n, k ≠ (σ⁻¹) i →
        ((P : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i = 0 := by
      intro i k hk
      rw [show ((P : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
        σ.permMatrix M by rfl, frame_permMatrix_apply]
      have hik : ¬ i = σ k := by
        intro h
        apply hk
        calc
          k = σ⁻¹ (σ k) := (Equiv.symm_apply_apply σ k).symm
          _ = σ⁻¹ i := by rw [h]
      simp [hik]
    have hlin := frame_ggLin_eq_perm hM hτ2 hU c hgen hn (B := P) rfl φ hφ
      (σ⁻¹) hsupp
    have hsymm : frameLinPerm (σ⁻¹).symm = frameLinPerm σ := by
      congr 1
    rw [hsymm] at hlin
    exact Subgroup.mem_map.mpr ⟨φ, hφmem, hlin⟩

private lemma frame_scalar_generator {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L D J : Subgroup R}
    (hC : GGQTwoFRCfg E x L D J)
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L)
    (A0 : ↥(heldGU n M τ hτ)) (c0 : M) (hc0ne : c0 ≠ 1)
    (hA0mat : ((A0 : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun _ => c0)) (hA0x : ρ A0 = x) :
    ∃ cunit : Mˣ, c0 ^ 3 = 1 ∧ (cunit : M) = c0 ∧
      (∀ u : Mˣ, u ∈ Subgroup.zpowers cunit) ∧ Nat.card Mˣ = 3 := by
  have hxL : x ∈ L := hC.2.2.2.2.2.1
  have hA0L : (A0 : GL (Fin n) M) ∈ heldSU n M τ hτ := by
    have hxmap : ρ A0 ∈ ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ := by
      rw [hA0x, ← hU.2.2.2.1]
      exact hxL
    obtain ⟨B, hB, hBx⟩ := Subgroup.mem_map.mp hxmap
    have hBA : B = A0 := hU.1 hBx
    rw [← hBA]
    exact hB
  have hA0SL : (A0 : GL (Fin n) M) ∈ CFSG.Open.StatedSL n M :=
    (Subgroup.mem_inf.mp hA0L).2
  have hdet : ((A0 : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp hA0SL
  have hn4 : 4 ≤ n := frame_four_le_n hM hτ2 hC hU
  have hpow : c0 ^ n = 1 := by
    simpa [hA0mat, Matrix.det_diagonal] using hdet
  have hc0zero : c0 ≠ 0 := by
    intro hzero
    have hzero' : c0 ^ n = 0 := by
      rw [hzero]
      exact zero_pow (by omega : n ≠ 0)
    rw [hpow] at hzero'
    exact one_ne_zero hzero'
  have hc0pow : c0 ^ 3 = 1 := frame_pow_three_eq_one hM hc0zero
  let cunit : Mˣ := Units.mk0 c0 hc0zero
  have hcunitpow : cunit ^ 3 = 1 := by
    apply Units.ext
    simpa [cunit] using hc0pow
  have hcunitne : cunit ≠ 1 := by
    intro h
    apply hc0ne
    have := congrArg (fun u : Mˣ => (u : M)) h
    simpa [cunit] using this
  have horder : orderOf cunit = 3 :=
    orderOf_eq_prime (p := 3) hcunitpow hcunitne
  have hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers cunit := by
    have htop : Subgroup.zpowers cunit = ⊤ :=
      Subgroup.eq_top_of_card_eq _
        (by rw [Nat.card_zpowers, horder, frame_card_units hM])
    intro u
    rw [htop]
    exact Subgroup.mem_top u
  exact ⟨cunit, hc0pow, rfl, hgen, frame_card_units hM⟩

theorem frame_exists_frameIota {E : Subgroup R} {x : R} {L D J : Subgroup R}
    (hC : GGQTwoFRCfg E x L D J) {n : ℕ} {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4)
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) :
    6 ≤ n ∧ ∃ (hx : x ∈ E) (ι : Additive ↥E ≃+ (Fin n → ZMod 3)) (c : M), c ^ 3 = 1 ∧ c ≠ 1 ∧
      ι (Additive.ofMul ⟨x, hx⟩) = (fun _ => 1) ∧
      (ggAutomizer L E).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
          T v i = v (σ i)} ∧
      ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
        (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
        ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
          c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val := by
  classical
  have hn6 : 6 ≤ n := frame_six_le_n hM hτ2 hC hU
  obtain ⟨A0, c0, hc0ne, hA0mat, hA0x⟩ := hU.2.2.1
  obtain ⟨cunit, hc0pow, hcunitval, hgen, hnunits⟩ :=
    frame_scalar_generator hM hτ2 hC hU A0 c0 hc0ne hA0mat hA0x
  let ι : Additive ↥E ≃+ (Fin n → ZMod 3) := frameCoordAdd hM hτ2 hU cunit hgen hnunits
  have hx : x ∈ E := hC.2.2.2.1
  have hc0zero : c0 ≠ 0 := by
    intro h
    rw [h] at hc0pow
    norm_num at hc0pow
  have hdiagA0 : ∀ i j : Fin n, i ≠ j →
      ((A0 : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0 := by
    intro i j hij
    rw [hA0mat, Matrix.diagonal_apply_ne _ hij]
  have hneA0 : ∀ i : Fin n,
      ((A0 : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i ≠ 0 := by
    intro i
    rw [hA0mat, Matrix.diagonal_apply_eq]
    exact hc0zero
  have heA0 : ρ A0 ∈ E := hA0x ▸ hx
  have hιx : ι (Additive.ofMul ⟨x, hx⟩) = (fun _ => 1) := by
    funext i
    have hxA0 : (⟨x, hx⟩ : ↥E) = ⟨ρ A0, heA0⟩ := Subtype.ext hA0x.symm
    rw [show ι (Additive.ofMul ⟨x, hx⟩) =
      frameCoordAdd hM hτ2 hU cunit hgen hnunits (Additive.ofMul ⟨x, hx⟩) from rfl]
    rw [hxA0]
    rw [frameCoordAdd_diag hM hτ2 hU cunit hgen hnunits A0 hdiagA0 hneA0 heA0 i]
    have hunit : Units.mk0 (((A0 : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i)
        (hneA0 i) = cunit := by
      apply Units.ext
      rw [Units.val_mk0, hA0mat, Matrix.diagonal_apply_eq]
      exact hcunitval.symm
    rw [hunit, frameDlog_apply_gen]
    rfl
  have hdiag : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j : Fin n, i ≠ j →
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c0 ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val := by
    intro A he hd i
    have hne : ∀ j : Fin n,
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j ≠ 0 :=
      fun j => frame_diag_entry_ne_zero hd j
    have hcoord := frameCoordAdd_diag hM hτ2 hU cunit hgen hnunits A hd hne he i
    have hp := frameDlog_pow cunit hgen hnunits
      (Units.mk0 (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) (hne i))
    rw [show ι (Additive.ofMul ⟨ρ A, he⟩) i =
      frameCoordAdd hM hτ2 hU cunit hgen hnunits (Additive.ofMul ⟨ρ A, he⟩) i from rfl]
    rw [hcoord, ← hcunitval, hp, Units.val_mk0]
  have hc1 : (cunit : M) ≠ 1 := by
    rw [hcunitval]
    exact hc0ne
  have haut := frame_automizer_eq hM hτ2 hU cunit hgen hnunits hc1
  exact ⟨hn6, hx, ι, c0, hc0pow, hc0ne, hιx, by simpa [ι] using haut, hdiag⟩


end CFSG.StandardType.QTwoFrameTorus

end
