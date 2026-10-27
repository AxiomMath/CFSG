module

public import CFSG.Milestones.ASVolI.K1
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Quasithin.Background.SmithB45L2Main
public import CFSG.Quasithin.Vol2.Ch5ModulesOrth
public import CFSG.Quasithin.Background.C124YLA6Grp
public import CFSG.Quasithin.Background.SmithB42L2Alt5
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Background.C1PackClassG
public import CFSG.Quasithin.Background.C1PackSolvP
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import Certificates.Certificate7233Base

public section

namespace CFSG.ASVolI

open CFSG.Open

section Field

variable {F : Type} [Field F] [Finite F] [CharP F 2] {s : ℕ}

@[expose] def burnsideK312_sg (F : Type) [Field F] [CharP F 2] (s : ℕ) : F →+* F :=
  iterateFrobenius F 2 s

theorem burnsideK312_sg_apply (x : F) : burnsideK312_sg F s x = x ^ 2 ^ s := by
  show iterateFrobenius F 2 s x = _
  rw [iterateFrobenius_def]

theorem burnsideK312_sg_sg (hF : Nat.card F = 2 ^ (2 * s)) (x : F) :
    burnsideK312_sg F s (burnsideK312_sg F s x) = x := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ (2 * s) := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [burnsideK312_sg_apply, burnsideK312_sg_apply, ← pow_mul, ← pow_add, ← two_mul, ← hF',
    FiniteField.pow_card]

theorem burnsideK312_one_le (hF : Nat.card F = 2 ^ (2 * s)) : 1 ≤ s := by
  by_contra h0
  have hs0 : s = 0 := by omega
  subst hs0
  have h1 : Nat.card F = 1 := by simpa using hF
  have : Subsingleton F := (Nat.card_eq_one_iff_unique.mp h1).1
  exact absurd (Subsingleton.elim (0 : F) 1) zero_ne_one

@[expose] def burnsideK312_K (F : Type) [Field F] [CharP F 2] (s : ℕ) : Subfield F :=
  RingHom.eqLocusField (burnsideK312_sg F s) (RingHom.id F)

theorem burnsideK312_mem_K {x : F} : x ∈ burnsideK312_K F s ↔ x ^ 2 ^ s = x := by
  show burnsideK312_sg F s x = (RingHom.id F) x ↔ _
  rw [burnsideK312_sg_apply]
  rfl

theorem burnsideK312_card_K (hs : 1 ≤ s) (hF : Nat.card F = 2 ^ (2 * s)) :
    Nat.card ↥(burnsideK312_K F s) = 2 ^ s := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ (2 * s) := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [← CFSG.Quasithin.B45L2.card_frob_fixed hs hF']
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => burnsideK312_mem_K)

theorem burnsideK312_exists_notFixed (hs : 1 ≤ s) (hF : Nat.card F = 2 ^ (2 * s)) :
    ∃ ω : F, ω ^ 2 ^ s ≠ ω := by
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card ↥(burnsideK312_K F s) = Nat.card F :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun x => burnsideK312_mem_K.2 (hcon x))
  rw [burnsideK312_card_K hs hF, hF] at h1
  have : 2 ^ s < 2 ^ (2 * s) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem burnsideK312_exists_trace (hs : 1 ≤ s) (hF : Nat.card F = 2 ^ (2 * s)) {κ : F}
    (hκ : κ ^ 2 ^ s = κ) : ∃ z : F, z + z ^ 2 ^ s = κ := by
  obtain ⟨ω, hω⟩ := burnsideK312_exists_notFixed hs hF
  have hθ : ω + ω ^ 2 ^ s ≠ 0 := fun h => hω (CharTwo.add_eq_zero.mp h).symm
  have hθK : (ω + ω ^ 2 ^ s) ^ 2 ^ s = ω + ω ^ 2 ^ s := by
    have := burnsideK312_sg_sg (s := s) hF ω
    rw [burnsideK312_sg_apply, burnsideK312_sg_apply] at this
    rw [add_pow_char_pow, this, add_comm]
  refine ⟨κ / (ω + ω ^ 2 ^ s) * ω, ?_⟩
  have hdivK : (κ / (ω + ω ^ 2 ^ s)) ^ 2 ^ s = κ / (ω + ω ^ 2 ^ s) := by
    rw [div_pow, hκ, hθK]
  rw [mul_pow, hdivK]
  field_simp

theorem burnsideK312_exists_hilbert90 {a : F} (ha : a * a ^ 2 ^ s = 1) :
    ∃ y : F, y ≠ 0 ∧ y = a * y ^ 2 ^ s := by
  by_cases h1 : a = 1
  · exact ⟨1, one_ne_zero, by simp [h1]⟩
  · refine ⟨1 + a, ?_, ?_⟩
    · intro h
      exact h1 ((CharTwo.add_eq_zero.mp h).symm)
    · rw [add_pow_char_pow, one_pow]
      linear_combination -ha

end Field

section Coord

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem burnsideK312_frobPow_eq_map (M : Matrix (Fin 2) (Fin 2) F) :
    frobPow s M = M.map (burnsideK312_sg F s) := by
  ext i j
  simp [frobPow, burnsideK312_sg_apply]

@[expose] def burnsideK312_Herm (F : Type) [Field F] [CharP F 2] (s : ℕ)
    (M : Matrix (Fin 2) (Fin 2) F) : Prop :=
  (frobPow s M)ᵀ = M

theorem burnsideK312_herm_apply {M : Matrix (Fin 2) (Fin 2) F} (h : burnsideK312_Herm F s M)
    (i j : Fin 2) : M i j = (M j i) ^ 2 ^ s := by
  have := congrFun (congrFun h i) j
  simpa [frobPow] using this.symm

theorem burnsideK312_matrix_herm (c : OrthogonalFourCoordinates L s F) (v : V) :
    burnsideK312_Herm F s (c.matrix v) :=
  (c.module_equiv v).2

theorem burnsideK312_matrix_mul (c : OrthogonalFourCoordinates L s F) (v w : V) :
    c.matrix (v * w) = c.matrix v + c.matrix w := by
  unfold OrthogonalFourCoordinates.matrix
  rw [map_mul, Subgroup.coe_mul, toAdd_mul]

theorem burnsideK312_matrix_one (c : OrthogonalFourCoordinates L s F) :
    c.matrix 1 = 0 := by
  unfold OrthogonalFourCoordinates.matrix
  rw [map_one, Subgroup.coe_one, toAdd_one]

theorem burnsideK312_matrix_inv (c : OrthogonalFourCoordinates L s F) (v : V) :
    c.matrix v⁻¹ = - c.matrix v := by
  unfold OrthogonalFourCoordinates.matrix
  rw [map_inv, Subgroup.coe_inv, toAdd_inv]

theorem burnsideK312_matrix_injective (c : OrthogonalFourCoordinates L s F) :
    Function.Injective c.matrix := by
  intro v w h
  apply c.module_equiv.injective
  apply Subtype.ext
  exact Multiplicative.toAdd.injective h

theorem burnsideK312_exists_vec (c : OrthogonalFourCoordinates L s F)
    {M : Matrix (Fin 2) (Fin 2) F} (hM : burnsideK312_Herm F s M) : ∃ v, c.matrix v = M := by
  obtain ⟨v, hv⟩ := c.module_equiv.surjective ⟨Multiplicative.ofAdd M, hM⟩
  exact ⟨v, by unfold OrthogonalFourCoordinates.matrix; rw [hv]; rfl⟩

@[expose] noncomputable def burnsideK312_actHom (c : OrthogonalFourCoordinates L s F) : SL(2, F) →* MulAut V :=
  L.subtype.comp (c.group_equiv.toMonoidHom.comp
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toMonoidHom)

theorem burnsideK312_actHom_injective (c : OrthogonalFourCoordinates L s F) :
    Function.Injective (burnsideK312_actHom c) :=
  L.subtype_injective.comp (c.group_equiv.injective.comp
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).injective)

theorem burnsideK312_actHom_mem (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    burnsideK312_actHom c g ∈ L :=
  (c.group_equiv _).2

theorem burnsideK312_exists_actHom (c : OrthogonalFourCoordinates L s F) {l : MulAut V}
    (hl : l ∈ L) : ∃ g : SL(2, F), burnsideK312_actHom c g = l := by
  obtain ⟨γ, hγ⟩ := c.group_equiv.surjective ⟨l, hl⟩
  obtain ⟨g, rfl⟩ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).surjective γ
  exact ⟨g, congrArg Subtype.val hγ⟩

theorem burnsideK312_matrix_act (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) (v : V) :
    c.matrix (burnsideK312_actHom c g v) =
      (g : Matrix (Fin 2) (Fin 2) F) * c.matrix v * (frobPow s (g : Matrix (Fin 2) (Fin 2) F))ᵀ := by
  have h := c.intertwines (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F g) v
  have h2 := congrArg Multiplicative.toAdd h
  unfold OrthogonalFourCoordinates.matrix
  simp only [twistAct, toAdd_ofAdd, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
    at h2
  exact h2

theorem burnsideK312_herm_iff (hF : Nat.card F = 2 ^ (2 * s)) {M : Matrix (Fin 2) (Fin 2) F} :
    burnsideK312_Herm F s M ↔
      (M 0 0) ^ 2 ^ s = M 0 0 ∧ (M 1 1) ^ 2 ^ s = M 1 1 ∧ M 1 0 = (M 0 1) ^ 2 ^ s := by
  constructor
  · intro h
    refine ⟨(burnsideK312_herm_apply h 0 0).symm, (burnsideK312_herm_apply h 1 1).symm,
      burnsideK312_herm_apply h 1 0⟩
  · rintro ⟨h00, h11, h10⟩
    unfold burnsideK312_Herm
    ext i j
    have h01 : M 0 1 = (M 1 0) ^ 2 ^ s := by
      rw [h10]
      exact (burnsideK312_sg_sg hF (M 0 1)).symm.trans (by rw [burnsideK312_sg_apply,
        burnsideK312_sg_apply])
    simp only [frobPow, Matrix.transpose_apply, Matrix.map_apply]
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01.symm
    · exact h10.symm
    · exact h11

theorem burnsideK312_herm_mk (hF : Nat.card F = 2 ^ (2 * s)) {a b d : F} (ha : a ^ 2 ^ s = a)
    (hd : d ^ 2 ^ s = d) : burnsideK312_Herm F s !![a, b; b ^ 2 ^ s, d] := by
  rw [burnsideK312_herm_iff hF]
  simpa using ⟨ha, hd⟩

@[expose] noncomputable def burnsideK312_pre (c : OrthogonalFourCoordinates L s F)
    (f : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F)
    (hf : ∀ M, burnsideK312_Herm F s M → burnsideK312_Herm F s (f M)) (v : V) : V :=
  Classical.choose (burnsideK312_exists_vec c (hf _ (burnsideK312_matrix_herm c v)))

theorem burnsideK312_matrix_pre (c : OrthogonalFourCoordinates L s F)
    (f : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F)
    (hf : ∀ M, burnsideK312_Herm F s M → burnsideK312_Herm F s (f M)) (v : V) :
    c.matrix (burnsideK312_pre c f hf v) = f (c.matrix v) :=
  Classical.choose_spec (burnsideK312_exists_vec c (hf _ (burnsideK312_matrix_herm c v)))

@[expose] noncomputable def burnsideK312_lift (c : OrthogonalFourCoordinates L s F)
    (f f' : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F)
    (hf : ∀ M, burnsideK312_Herm F s M → burnsideK312_Herm F s (f M))
    (hf' : ∀ M, burnsideK312_Herm F s M → burnsideK312_Herm F s (f' M))
    (hadd : ∀ M N, f (M + N) = f M + f N)
    (h1 : ∀ M, burnsideK312_Herm F s M → f' (f M) = M)
    (h2 : ∀ M, burnsideK312_Herm F s M → f (f' M) = M) : MulAut V where
  toFun := burnsideK312_pre c f hf
  invFun := burnsideK312_pre c f' hf'
  left_inv v := by
    apply burnsideK312_matrix_injective c
    rw [burnsideK312_matrix_pre, burnsideK312_matrix_pre, h1 _ (burnsideK312_matrix_herm c v)]
  right_inv v := by
    apply burnsideK312_matrix_injective c
    rw [burnsideK312_matrix_pre, burnsideK312_matrix_pre, h2 _ (burnsideK312_matrix_herm c v)]
  map_mul' v w := by
    apply burnsideK312_matrix_injective c
    rw [burnsideK312_matrix_mul, burnsideK312_matrix_pre, burnsideK312_matrix_pre,
      burnsideK312_matrix_pre, burnsideK312_matrix_mul, hadd]

theorem burnsideK312_matrix_lift (c : OrthogonalFourCoordinates L s F)
    (f f' : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F)
    (hf : ∀ M, burnsideK312_Herm F s M → burnsideK312_Herm F s (f M))
    (hf' : ∀ M, burnsideK312_Herm F s M → burnsideK312_Herm F s (f' M))
    (hadd : ∀ M N, f (M + N) = f M + f N)
    (h1 : ∀ M, burnsideK312_Herm F s M → f' (f M) = M)
    (h2 : ∀ M, burnsideK312_Herm F s M → f (f' M) = M) (v : V) :
    c.matrix (burnsideK312_lift c f f' hf hf' hadd h1 h2 v) = f (c.matrix v) :=
  burnsideK312_matrix_pre c f hf v

@[expose] def burnsideK312_sgE (hF : Nat.card F = 2 ^ (2 * s)) : F ≃+* F :=
  { burnsideK312_sg F s with
    invFun := burnsideK312_sg F s
    left_inv := burnsideK312_sg_sg hF
    right_inv := burnsideK312_sg_sg hF }

theorem burnsideK312_sgE_apply (hF : Nat.card F = 2 ^ (2 * s)) (x : F) :
    burnsideK312_sgE hF x = x ^ 2 ^ s :=
  burnsideK312_sg_apply x

theorem burnsideK312_herm_transpose {M : Matrix (Fin 2) (Fin 2) F} (h : burnsideK312_Herm F s M) :
    Mᵀ = frobPow s M := by
  have := congrArg Matrix.transpose h
  rw [Matrix.transpose_transpose] at this
  exact this.symm

theorem burnsideK312_herm_map {M : Matrix (Fin 2) (Fin 2) F} (h : burnsideK312_Herm F s M)
    (ρ : F ≃+* F) (hρ : ∀ x, burnsideK312_sg F s (ρ x) = ρ (burnsideK312_sg F s x)) :
    burnsideK312_Herm F s (M.map ρ) := by
  unfold burnsideK312_Herm at h ⊢
  have e : frobPow s (M.map ρ) = (frobPow s M).map ρ := by
    ext i j
    have := hρ (M i j)
    simp only [burnsideK312_sg_apply] at this
    simpa [frobPow] using this
  rw [e, ← Matrix.transpose_map, h]

@[expose] noncomputable def burnsideK312_fieldTwist (c : OrthogonalFourCoordinates L s F) (ρ : F ≃+* F)
    (hρ : ∀ x, burnsideK312_sg F s (ρ x) = ρ (burnsideK312_sg F s x)) : MulAut V :=
  burnsideK312_lift c (fun M => M.map ρ) (fun M => M.map ρ.symm)
    (fun M hM => burnsideK312_herm_map hM ρ hρ)
    (fun M hM => burnsideK312_herm_map hM ρ.symm (fun x => by
      apply ρ.injective
      rw [← hρ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]))
    (fun M N => by ext i j; simp)
    (fun M _ => by ext i j; simp)
    (fun M _ => by ext i j; simp)

theorem burnsideK312_matrix_fieldTwist (c : OrthogonalFourCoordinates L s F) (ρ : F ≃+* F)
    (hρ : ∀ x, burnsideK312_sg F s (ρ x) = ρ (burnsideK312_sg F s x)) (v : V) :
    c.matrix (burnsideK312_fieldTwist c ρ hρ v) = (c.matrix v).map ρ :=
  burnsideK312_matrix_lift c _ _ _ _ _ _ _ v

theorem burnsideK312_sgE_comm (hF : Nat.card F = 2 ^ (2 * s)) (x : F) :
    burnsideK312_sg F s (burnsideK312_sgE hF x) = burnsideK312_sgE hF (burnsideK312_sg F s x) :=
  rfl

@[expose] noncomputable def burnsideK312_sh (c : OrthogonalFourCoordinates L s F) : MulAut V :=
  burnsideK312_fieldTwist c (burnsideK312_sgE c.field_card) (burnsideK312_sgE_comm c.field_card)

theorem burnsideK312_matrix_sh (c : OrthogonalFourCoordinates L s F) (v : V) :
    c.matrix (burnsideK312_sh c v) = (c.matrix v)ᵀ := by
  refine (burnsideK312_matrix_fieldTwist c (burnsideK312_sgE c.field_card)
    (burnsideK312_sgE_comm c.field_card) v).trans ?_
  rw [burnsideK312_herm_transpose (burnsideK312_matrix_herm c v), burnsideK312_frobPow_eq_map]
  rfl

theorem burnsideK312_herm_E11 {F : Type} [Field F] [CharP F 2] {s : ℕ} :
    burnsideK312_Herm F s !![(1 : F), 0; 0, 0] := by
  unfold burnsideK312_Herm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow]

theorem burnsideK312_herm_E22 {F : Type} [Field F] [CharP F 2] {s : ℕ} :
    burnsideK312_Herm F s !![(0 : F), 0; 0, 1] := by
  unfold burnsideK312_Herm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow]

theorem burnsideK312_herm_J {F : Type} [Field F] [CharP F 2] {s : ℕ} :
    burnsideK312_Herm F s !![(0 : F), 1; 1, 0] := by
  unfold burnsideK312_Herm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow]

theorem burnsideK312_triv_of_fix3 {F : Type} [Field F] [CharP F 2] {s : ℕ}
    (γ : Matrix (Fin 2) (Fin 2) F) (hγ : γ.det = 1)
    (h1 : γ * !![(1 : F), 0; 0, 0] * (frobPow s γ)ᵀ = !![(1 : F), 0; 0, 0])
    (h3 : γ * !![(0 : F), 0; 0, 1] * (frobPow s γ)ᵀ = !![(0 : F), 0; 0, 1])
    (h4 : γ * !![(0 : F), 1; 1, 0] * (frobPow s γ)ᵀ = !![(0 : F), 1; 1, 0]) : γ = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have a1 := congrFun (congrFun h1 1) 1
  have a2 := congrFun (congrFun h3 0) 0
  have a3 := congrFun (congrFun h1 0) 0
  have a4 := congrFun (congrFun h3 1) 1
  have a5 := congrFun (congrFun h4 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow] at a1 a2 a3 a4 a5
  rw [Matrix.det_fin_two] at hγ
  rw [a1, a2] at hγ
  rw [a2] at a5
  simp at hγ a5
  have hw0 : γ 1 1 ^ 2 ^ s ≠ 0 := fun h0 => by rw [h0, mul_zero] at a4; exact zero_ne_one a4
  have hpw : γ 0 0 = γ 1 1 := by
    have : (γ 0 0 - γ 1 1) * γ 1 1 ^ 2 ^ s = 0 := by linear_combination a5 - a4
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have hpp : γ 0 0 * γ 0 0 = 1 := by
    calc γ 0 0 * γ 0 0 = γ 0 0 * γ 1 1 := by rw [← hpw]
      _ = 1 := hγ
  have hp1 : γ 0 0 = 1 := by
    have h0 : (γ 0 0 - 1) ^ 2 = 0 := by linear_combination hpp + (1 - γ 0 0) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp1, a1, a2, ← hpw]

theorem burnsideK312_triv_of_fix {F : Type} [Field F] [CharP F 2] {s : ℕ}
    (γ : Matrix (Fin 2) (Fin 2) F) (hγ : γ.det = 1)
    (h : ∀ M : Matrix (Fin 2) (Fin 2) F, burnsideK312_Herm F s M →
      γ * M * (frobPow s γ)ᵀ = M) : γ = 1 :=
  burnsideK312_triv_of_fix3 γ hγ (h _ burnsideK312_herm_E11) (h _ burnsideK312_herm_E22)
    (h _ burnsideK312_herm_J)

theorem burnsideK312_fieldTwist_actHom (c : OrthogonalFourCoordinates L s F) (ρ : F ≃+* F)
    (hρ : ∀ x, burnsideK312_sg F s (ρ x) = ρ (burnsideK312_sg F s x)) (g : SL(2, F)) :
    burnsideK312_fieldTwist c ρ hρ * burnsideK312_actHom c g =
      burnsideK312_actHom c (Matrix.SpecialLinearGroup.map ρ.toRingHom g) *
        burnsideK312_fieldTwist c ρ hρ := by
  ext v
  apply burnsideK312_matrix_injective c
  simp only [MulAut.mul_apply]
  rw [burnsideK312_matrix_fieldTwist, burnsideK312_matrix_act, burnsideK312_matrix_act,
    burnsideK312_matrix_fieldTwist, Matrix.SpecialLinearGroup.map_apply_coe]
  have e : (frobPow s (g : Matrix (Fin 2) (Fin 2) F)).map ρ =
      frobPow s ((g : Matrix (Fin 2) (Fin 2) F).map ρ) := by
    ext i j
    have := hρ ((g : Matrix (Fin 2) (Fin 2) F) i j)
    simp only [burnsideK312_sg_apply] at this
    simpa [frobPow] using this.symm
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, e]
  rfl

theorem burnsideK312_sh_sq (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_sh c * burnsideK312_sh c = 1 := by
  ext v
  apply burnsideK312_matrix_injective c
  simp only [MulAut.mul_apply, MulAut.one_apply]
  rw [burnsideK312_matrix_sh, burnsideK312_matrix_sh, Matrix.transpose_transpose]

theorem burnsideK312_sh_inv (c : OrthogonalFourCoordinates L s F) :
    (burnsideK312_sh c)⁻¹ = burnsideK312_sh c :=
  inv_eq_of_mul_eq_one_right (burnsideK312_sh_sq c)

theorem burnsideK312_sh_actHom (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    burnsideK312_sh c * burnsideK312_actHom c g * burnsideK312_sh c =
      burnsideK312_actHom c
        (Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g) := by
  have h := burnsideK312_fieldTwist_actHom c (burnsideK312_sgE c.field_card)
    (burnsideK312_sgE_comm c.field_card) g
  have h2 : burnsideK312_sh c * burnsideK312_actHom c g =
      burnsideK312_actHom c (Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g) *
        burnsideK312_sh c := h
  rw [h2, mul_assoc, burnsideK312_sh_sq, mul_one]

theorem burnsideK312_sh_normalizer (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_sh c ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ l ∈ L, burnsideK312_sh c * l * (burnsideK312_sh c)⁻¹ ∈ L := by
    intro l hl
    obtain ⟨g, rfl⟩ := burnsideK312_exists_actHom c hl
    rw [burnsideK312_sh_inv, burnsideK312_sh_actHom]
    exact burnsideK312_actHom_mem c _
  intro h
  refine ⟨key h, fun hh => ?_⟩
  have := key _ hh
  rwa [burnsideK312_sh_inv, ← mul_assoc, ← mul_assoc, burnsideK312_sh_sq, one_mul, mul_assoc,
    burnsideK312_sh_sq, mul_one] at this

theorem burnsideK312_sh_notMem (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_sh c ∉ L := by
  intro hL
  obtain ⟨g, hg⟩ := burnsideK312_exists_actHom c hL
  have hE : ∀ M : Matrix (Fin 2) (Fin 2) F, burnsideK312_Herm F s M → Mᵀ = M →
      (g : Matrix (Fin 2) (Fin 2) F) * M * (frobPow s (g : Matrix (Fin 2) (Fin 2) F))ᵀ = M := by
    intro M hM hMt
    obtain ⟨v, hv⟩ := burnsideK312_exists_vec c hM
    have h1 := burnsideK312_matrix_act c g v
    rw [hg, burnsideK312_matrix_sh, hv, hMt] at h1
    exact h1.symm
  have hg1 : (g : Matrix (Fin 2) (Fin 2) F) = 1 :=
    burnsideK312_triv_of_fix3 _ g.2
      (hE _ burnsideK312_herm_E11 (by ext i j; fin_cases i <;> fin_cases j <;> simp))
      (hE _ burnsideK312_herm_E22 (by ext i j; fin_cases i <;> fin_cases j <;> simp))
      (hE _ burnsideK312_herm_J (by ext i j; fin_cases i <;> fin_cases j <;> simp))
  have hg2 : g = 1 := Subtype.ext hg1
  rw [hg2, map_one] at hg
  obtain ⟨ω, hω⟩ := burnsideK312_exists_notFixed (burnsideK312_one_le c.field_card) c.field_card
  obtain ⟨v, hv⟩ := burnsideK312_exists_vec c (burnsideK312_herm_mk c.field_card
    (a := 0) (d := 0) (b := ω) (by simp) (by simp))
  have h1 := burnsideK312_matrix_sh c v
  rw [← hg, MulAut.one_apply, hv] at h1
  have h2 := congrFun (congrFun h1 0) 1
  simp at h2
  exact hω h2.symm

theorem burnsideK312_twAct_mul (γ δ M : Matrix (Fin 2) (Fin 2) F) :
    CFSG.Quasithin.B45L2.twAct s (γ * δ) M =
      CFSG.Quasithin.B45L2.twAct s γ (CFSG.Quasithin.B45L2.twAct s δ M) := by
  unfold CFSG.Quasithin.B45L2.twAct
  rw [burnsideK312_frobPow_eq_map, burnsideK312_frobPow_eq_map, burnsideK312_frobPow_eq_map,
    Matrix.map_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem burnsideK312_twAct_one (M : Matrix (Fin 2) (Fin 2) F) :
    CFSG.Quasithin.B45L2.twAct s 1 M = M := by
  unfold CFSG.Quasithin.B45L2.twAct
  rw [burnsideK312_frobPow_eq_map]
  simp

theorem burnsideK312_det_twAct (g : SL(2, F)) (M : Matrix (Fin 2) (Fin 2) F) :
    (CFSG.Quasithin.B45L2.twAct s (g : Matrix (Fin 2) (Fin 2) F) M).det = M.det := by
  unfold CFSG.Quasithin.B45L2.twAct
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, burnsideK312_frobPow_eq_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, g.2, map_one]
  simp

theorem burnsideK312_actHom_one (c : OrthogonalFourCoordinates L s F) : burnsideK312_actHom c 1 = 1 :=
  map_one _

@[expose] noncomputable def burnsideK312_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    OrthogonalFourCoordinates L s F where
  field_card := c.field_card
  group_equiv := c.group_equiv.trans
    (MulAut.conj (⟨burnsideK312_actHom c g, burnsideK312_actHom_mem c g⟩ : ↥L))
  module_equiv := MulEquiv.trans (burnsideK312_actHom c g)⁻¹ c.module_equiv
  intertwines γ v := by
    have h := c.intertwines γ ((burnsideK312_actHom c g)⁻¹ v)
    refine Eq.trans ?_ (h.trans ?_)
    · show (c.module_equiv (((burnsideK312_actHom c g)⁻¹ : MulAut V)
        ((burnsideK312_actHom c g * ((c.group_equiv γ : ↥L) : MulAut V) *
          (burnsideK312_actHom c g)⁻¹) v)) : Multiplicative (Matrix (Fin 2) (Fin 2) F)) = _
      simp
    · rfl

theorem burnsideK312_matrix_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) (v : V) :
    (burnsideK312_conj c g).matrix v = c.matrix ((burnsideK312_actHom c g)⁻¹ v) := rfl

theorem burnsideK312_actHom_conj (c : OrthogonalFourCoordinates L s F) (g h : SL(2, F)) :
    burnsideK312_actHom (burnsideK312_conj c g) h =
      burnsideK312_actHom c g * burnsideK312_actHom c h * (burnsideK312_actHom c g)⁻¹ := rfl

@[expose] noncomputable def burnsideK312_Uc (c : OrthogonalFourCoordinates L s F) :
    Subgroup (MulAut V) :=
  (CFSG.Quasithin.B45L2.rootSub (⊤ : AddSubgroup F)).map (burnsideK312_actHom c)

@[expose] noncomputable def burnsideK312_Rc (c : OrthogonalFourCoordinates L s F) :
    Subgroup (MulAut V) :=
  (CFSG.Quasithin.B45L2.rootSub (CFSG.Quasithin.B45L2.frobFixSub (F := F) s)).map
    (burnsideK312_actHom c)

@[expose] noncomputable def burnsideK312_Xc (c : OrthogonalFourCoordinates L s F) :
    Subgroup (MulAut V) :=
  burnsideK312_Rc c ⊔ Subgroup.zpowers (burnsideK312_sh c)

theorem burnsideK312_Rc_le_Uc (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_Rc c ≤ burnsideK312_Uc c :=
  Subgroup.map_mono (fun g ⟨t, _, e⟩ => ⟨t, trivial, e⟩)

theorem burnsideK312_Uc_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    burnsideK312_Uc (burnsideK312_conj c g) =
      (burnsideK312_Uc c).map (MulAut.conj (burnsideK312_actHom c g)).toMonoidHom := by
  unfold burnsideK312_Uc
  rw [Subgroup.map_map]
  congr 1

theorem burnsideK312_Rc_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    burnsideK312_Rc (burnsideK312_conj c g) =
      (burnsideK312_Rc c).map (MulAut.conj (burnsideK312_actHom c g)).toMonoidHom := by
  unfold burnsideK312_Rc
  rw [Subgroup.map_map]
  congr 1

theorem burnsideK312_sh_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    burnsideK312_sh (burnsideK312_conj c g) =
      burnsideK312_actHom c g * burnsideK312_sh c * (burnsideK312_actHom c g)⁻¹ := by
  ext v
  apply burnsideK312_matrix_injective (burnsideK312_conj c g)
  rw [burnsideK312_matrix_sh, burnsideK312_matrix_conj, burnsideK312_matrix_conj]
  simp only [MulAut.mul_apply, MulAut.inv_apply]
  have := burnsideK312_matrix_sh c ((burnsideK312_actHom c g).symm v)
  simp [this]

theorem burnsideK312_matrix_uMat (c : OrthogonalFourCoordinates L s F) (x : F) (v : V) :
    c.matrix (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) v) =
      !![c.matrix v 0 0 + x * c.matrix v 1 0 +
          (c.matrix v 0 1 + x * c.matrix v 1 1) * x ^ 2 ^ s,
        c.matrix v 0 1 + x * c.matrix v 1 1;
        c.matrix v 1 0 + c.matrix v 1 1 * x ^ 2 ^ s, c.matrix v 1 1] := by
  rw [burnsideK312_matrix_act, CFSG.Quasithin.JonesParshall.uMat_coe]
  exact CFSG.Quasithin.B45L2.twAct_u s x (c.matrix v)

theorem burnsideK312_map_sg_uMat (x : F) :
    Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) (CFSG.Quasithin.JonesParshall.uMat x) =
      CFSG.Quasithin.JonesParshall.uMat (x ^ 2 ^ s) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, CFSG.Quasithin.JonesParshall.uMat_coe,
    CFSG.Quasithin.JonesParshall.uMat_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, burnsideK312_sg_apply]

theorem burnsideK312_sh_uMat (c : OrthogonalFourCoordinates L s F) (x : F) :
    burnsideK312_sh c * burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) *
        burnsideK312_sh c =
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (x ^ 2 ^ s)) := by
  rw [burnsideK312_sh_actHom, burnsideK312_map_sg_uMat]

theorem burnsideK312_centralizer_sh (c : OrthogonalFourCoordinates L s F) :
    Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓ burnsideK312_Uc c =
      burnsideK312_Rc c := by
  ext z
  constructor
  · rintro ⟨hz, g, ⟨x, -, rfl⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hz _ (Set.mem_singleton _)
    have h2 : burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (x ^ 2 ^ s)) =
        burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) := by
      rw [← burnsideK312_sh_uMat, h1, mul_assoc, burnsideK312_sh_sq, mul_one]
    have h3 := CFSG.Quasithin.B45L2.uMat_injective
      (burnsideK312_actHom_injective c h2)
    refine ⟨CFSG.Quasithin.JonesParshall.uMat x, ⟨x, ?_, rfl⟩, rfl⟩
    exact h3
  · intro hz
    refine ⟨?_, burnsideK312_Rc_le_Uc c hz⟩
    obtain ⟨g, ⟨x, hx, rfl⟩, rfl⟩ := hz
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have hx' : x ^ 2 ^ s = x := hx
    have := burnsideK312_sh_uMat c x
    rw [hx'] at this
    have e := congrArg (fun y => y * burnsideK312_sh c) this
    simp only [mul_assoc, burnsideK312_sh_sq, mul_one] at e
    exact e

end Coord

section TConj

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

@[expose] def burnsideK312_TConj (c : OrthogonalFourCoordinates L s F) (t : MulAut V) : Prop :=
  (∀ vector, (c.matrix (t vector)).det = (c.matrix vector).det) ∧
  (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
    ∀ first second : V, c.matrix second = scalar • c.matrix first →
      c.matrix (t second) = scalar • c.matrix (t first)) ∧
  (∃ point : V, point ≠ 1 ∧ (c.matrix point).det ≠ 0 ∧
    ∀ vector : V, c.matrix (t vector) = c.matrix vector +
      (c.polar vector point / (c.matrix point).det) • c.matrix point) ∧
  c.IsPoint (commV (Subgroup.zpowers t)) ∧
  (∀ vector ∈ commV (Subgroup.zpowers t), vector ≠ 1 → (c.matrix vector).det ≠ 0) ∧
  (∀ groupElement ∈ L,
    groupElement ∈ Subgroup.centralizer ({t} : Set (MulAut V)) ↔
      ∀ vector : V, vector ∈ commV (Subgroup.zpowers t) ↔
        groupElement vector ∈ commV (Subgroup.zpowers t)) ∧
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (field_embedding : K →+* F),
      Nat.card K = 2 ^ s ∧ Function.Injective field_embedding ∧
      (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar ↔
        ∃ baseScalar : K, field_embedding baseScalar = scalar) ∧
      Nonempty (↥(L ⊓ Subgroup.centralizer ({t} : Set (MulAut V))) ≃* ↥(StatedSL 2 K))) ∧
  (∃ perpendicular : Subgroup V,
    (∀ vector : V, vector ∈ perpendicular ↔
      ∀ point ∈ commV (Subgroup.zpowers t), c.polar vector point = 0) ∧
    (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
      ∀ vector ∈ perpendicular, ∀ scalarVector : V,
        c.matrix scalarVector = scalar • c.matrix vector → scalarVector ∈ perpendicular) ∧
    Nat.card perpendicular = 2 ^ (3 * s) ∧
    (∀ groupElement ∈ L ⊓ Subgroup.centralizer ({t} : Set (MulAut V)),
      ∀ vector ∈ perpendicular, groupElement vector ∈ perpendicular ∧
        (c.matrix (groupElement vector)).det = (c.matrix vector).det) ∧
    (∀ groupElement ∈ L ⊓ Subgroup.centralizer ({t} : Set (MulAut V)),
      (∀ vector ∈ perpendicular, groupElement vector = vector) → groupElement = 1) ∧
    (∀ isometry : MulAut ↥perpendicular,
      (∀ vector : ↥perpendicular,
        (c.matrix (isometry vector : V)).det = (c.matrix (vector : V)).det) →
      (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
        ∀ first second : ↥perpendicular,
          c.matrix (second : V) = scalar • c.matrix (first : V) →
            c.matrix (isometry second : V) = scalar • c.matrix (isometry first : V)) →
      ∃ groupElement ∈ L ⊓ Subgroup.centralizer ({t} : Set (MulAut V)),
        ∀ vector : ↥perpendicular, groupElement (vector : V) = (isometry vector : V)))

end TConj

section Syl

open scoped MatrixGroups Matrix
open CFSG.Quasithin.B45L2 (rootSub card_rootSub rootSub_sq rootSub_comm)

variable {E : Type} [Field E] [Finite E] [CharP E 2]

theorem burnsideK312_card_rootSub : Nat.card (rootSub (⊤ : AddSubgroup E)) = Nat.card E := by
  rw [card_rootSub]
  exact Nat.card_congr (AddSubgroup.topEquiv (G := E)).toEquiv

theorem burnsideK312_even_card : Even (Nat.card E) := by
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨n, -, hn⟩ := FiniteField.card E 2
  rw [Nat.card_eq_fintype_card, hn]
  exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)

theorem burnsideK312_card_SL2 :
    Nat.card SL(2, E) = Nat.card E * (Nat.card E ^ 2 - 1) := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have h := Matrix.card_SL_field (𝔽 := E) 2
  rw [Fin.prod_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h, Nat.card_eq_fintype_card (α := E)]
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have e1 : Fintype.card E ^ 2 - Fintype.card E = Fintype.card E * (Fintype.card E - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [e1]
  ring

theorem burnsideK312_isPGroup_rootSub : IsPGroup 2 (rootSub (⊤ : AddSubgroup E)) := fun g =>
  ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using rootSub_sq (⊤ : AddSubgroup E) g.1 g.2)⟩

theorem burnsideK312_sylow_conj {Y : Subgroup SL(2, E)} (hY : IsPGroup 2 Y) :
    ∃ x : SL(2, E), Y ≤ (rootSub (⊤ : AddSubgroup E)).map (MulAut.conj x).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := rootSub (⊤ : AddSubgroup E) with hP
  have hPc : Nat.card P = Nat.card E := burnsideK312_card_rootSub
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hidx : P.index = Nat.card E ^ 2 - 1 := by
    have h := Subgroup.index_mul_card P
    rw [hPc, burnsideK312_card_SL2] at h
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm _ _))
  have hodd : ¬ 2 ∣ P.index := by
    rw [hidx]
    obtain ⟨k, hk⟩ := burnsideK312_even_card (E := E)
    have h2 : 2 ≤ Nat.card E := by
      have : Fintype E := Fintype.ofFinite E
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hk1 : 1 ≤ k := by omega
    have e : Nat.card E ^ 2 = 4 * (k * k) := by rw [hk]; ring
    have hkk : 1 ≤ k * k := Nat.mul_pos hk1 hk1
    rw [e]
    omega
  let Pu : Sylow 2 SL(2, E) := burnsideK312_isPGroup_rootSub.toSylow hodd
  obtain ⟨Q, hYQ⟩ := hY.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, E) Pu Q
  refine ⟨g, hYQ.trans ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact le_rfl

theorem burnsideK312_card_le_of_isPGroup {Y : Subgroup SL(2, E)} (hY : IsPGroup 2 Y) :
    Nat.card Y ≤ Nat.card E := by
  obtain ⟨x, hx⟩ := burnsideK312_sylow_conj hY
  calc Nat.card Y ≤ Nat.card ((rootSub (⊤ : AddSubgroup E)).map (MulAut.conj x).toMonoidHom) :=
        Subgroup.card_le_of_le hx
    _ = Nat.card (rootSub (⊤ : AddSubgroup E)) :=
        Subgroup.card_map_of_injective (MulAut.conj x).injective
    _ = Nat.card E := burnsideK312_card_rootSub

end Syl


section Extract

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

theorem burnsideK312_statedSL_det {F : Type} [Field F] (γ : ↥(StatedSL 2 F)) :
    ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  obtain ⟨g, rfl⟩ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).surjective γ
  rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  exact g.2

theorem burnsideK312_coords {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {s : ℕ}
    (h : BinaryOrthogonalFour L ⊤ ⊥ s) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nonempty (OrthogonalFourCoordinates L s F) := by
  obtain ⟨K, _, _, _, hK, π, hπs, -, -, -, -, hsecinv, -, β, hβs, hβk, hβe⟩ := h
  refine ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩
  classical
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  let q : ↥(hermSub s (Fin 2) K) ⧸ (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K))).subgroupOf
      (hermSub s (Fin 2) K) ≃* ↥(hermSub s (Fin 2) K) :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans QuotientGroup.quotientBot
  let e : V ≃* ↥(hermSub s (Fin 2) K) :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans q)
  have hqs : ∀ x, x = (QuotientGroup.mk (q x) : ↥(hermSub s (Fin 2) K) ⧸
      (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K))).subgroupOf
        (hermSub s (Fin 2) K)) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have hint : ∀ (γ : ↥(StatedSL 2 K)) (v : V),
      ((e (((π γ : ↥L) : MulAut V) v) : ↥(hermSub s (Fin 2) K)) :
          Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
        twistAct s (StatedSL 2 K) γ ((e v : ↥(hermSub s (Fin 2) K)) :
          Multiplicative (Matrix (Fin 2) (Fin 2) K)) := by
    intro γ v
    have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk (e v) := hqs _
    have h2 := hβe γ ⟨v, trivial⟩ (e v) trivial (hsecinv γ _ (e v).2) h1
    have h3 := congrArg q h2
    exact congrArg Subtype.val h3
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro (γ : ↥(StatedSL 2 K)) hγ
    have hmat := burnsideK312_triv_of_fix (s := s) ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      (burnsideK312_statedSL_det γ) (fun M hM => ?_)
    · exact Subtype.ext (Units.ext hmat)
    · obtain ⟨v, hv⟩ := e.surjective ⟨Multiplicative.ofAdd M, hM⟩
      have h1 := hint γ v
      rw [hγ, Subgroup.coe_one, MulAut.one_apply, hv] at h1
      have h2 := congrArg Multiplicative.toAdd h1
      simpa [twistAct] using h2.symm
  exact ⟨⟨hK, MulEquiv.ofBijective π ⟨hinj, hπs⟩, e, hint⟩⟩

end Extract


section Cl

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_Cl_u_fix_E (c : OrthogonalFourCoordinates L s F) (E : V)
    (hE : c.matrix E = !![(1 : F), 0; 0, 0]) (x : F) :
    burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) E = E := by
  apply burnsideK312_matrix_injective c
  rw [burnsideK312_matrix_uMat, hE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideK312_commutant (c : OrthogonalFourCoordinates L s F)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (φ : MulAut V)
    (hφ : ∀ g : SL(2, F), φ * burnsideK312_actHom c g = burnsideK312_actHom c g * φ) :
    ∃ κ : F, κ ^ 2 ^ s = κ ∧ ∀ v, c.matrix (φ v) = κ • c.matrix v := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨E, hE⟩ := burnsideK312_exists_vec c (burnsideK312_herm_E11 (F := F) (s := s))
  have hφv : ∀ (g : SL(2, F)) (v : V),
      φ (burnsideK312_actHom c g v) = burnsideK312_actHom c g (φ v) := fun g v => by
    have := congrArg (fun m : MulAut V => m v) (hφ g)
    simpa [MulAut.mul_apply] using this
  have hfixφE : ∀ x : F, burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) (φ E) = φ E :=
    fun x => by
      rw [← hφv, burnsideK312_Cl_u_fix_E c E hE]
  set M := c.matrix (φ E) with hM
  have hMh := burnsideK312_matrix_herm c (φ E)
  have hF := c.field_card
  obtain ⟨ω, hω⟩ := burnsideK312_exists_notFixed (burnsideK312_one_le hF) hF
  have e1 := fun x => congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 1)
    (congrArg c.matrix (hfixφE x))
  have e2 := fun x => congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0)
    (congrArg c.matrix (hfixφE x))
  simp only [burnsideK312_matrix_uMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e2
  rw [← hM] at e1 e2
  have hM11 : M 1 1 = 0 := by
    have := e1 1
    have h3 : 1 * M 1 1 = 0 := by linear_combination this
    simpa using h3
  have hM10 : M 1 0 = M 0 1 := by
    have h4 := e2 1
    rw [hM11] at h4
    have : M 1 0 + M 0 1 = 0 := by simpa using (by linear_combination h4 : M 1 0 + M 0 1 = 0)
    exact (CharTwo.add_eq_zero.mp this)
  have hM01 : M 0 1 = 0 := by
    have h4 := e2 ω
    rw [hM11, hM10] at h4
    have h5 : M 0 1 * (ω + ω ^ 2 ^ s) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h5 with h | h
    · exact h
    · exact absurd (CharTwo.add_eq_zero.mp h).symm hω
  have hκ : M 0 0 ^ 2 ^ s = M 0 0 := (burnsideK312_herm_apply hMh 0 0).symm
  refine ⟨M 0 0, hκ, ?_⟩
  let J : Subgroup V :=
    { carrier := {v | c.matrix (φ v) = M 0 0 • c.matrix v}
      one_mem' := by simp [burnsideK312_matrix_one]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, burnsideK312_matrix_mul, smul_add] at ha hb ⊢
        rw [ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_inv, burnsideK312_matrix_inv, smul_neg] at ha ⊢
        rw [ha] }
  have hJL : ∀ l ∈ L, ∀ v ∈ J, l v ∈ J := by
    intro l hl v hv
    obtain ⟨g, rfl⟩ := burnsideK312_exists_actHom c hl
    show c.matrix (φ (burnsideK312_actHom c g v)) = M 0 0 • c.matrix (burnsideK312_actHom c g v)
    have hv' : c.matrix (φ v) = M 0 0 • c.matrix v := hv
    rw [hφv, burnsideK312_matrix_act, burnsideK312_matrix_act, hv']
    simp [Matrix.mul_smul, Matrix.smul_mul]
  have hEJ : E ∈ J := by
    show M = M 0 0 • c.matrix E
    rw [hE]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM11, hM10, hM01]
  have hE1 : E ≠ 1 := by
    intro h1
    have := burnsideK312_matrix_one c
    rw [← h1, hE] at this
    have h00 := congrFun (congrFun this 0) 0
    simp at h00
  rcases hirr J hJL with h | h
  · exact absurd (Subgroup.mem_bot.mp (h ▸ hEJ)) hE1
  · intro v
    have : v ∈ J := h ▸ Subgroup.mem_top v
    exact this

theorem burnsideK312_Cl_conj_mem (c : OrthogonalFourCoordinates L s F) {t : MulAut V}
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (g : SL(2, F)) :
    t * burnsideK312_actHom c g * t⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp hN _).mp (burnsideK312_actHom_mem c g)

theorem burnsideK312_Cl_conj_mem' (c : OrthogonalFourCoordinates L s F) {t : MulAut V}
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (g : SL(2, F)) :
    t⁻¹ * burnsideK312_actHom c g * t ∈ L := by
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hN) _).mp (burnsideK312_actHom_mem c g)
  simpa using this

@[expose] noncomputable def burnsideK312_Cl_aF (c : OrthogonalFourCoordinates L s F)
    {t : MulAut V} (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (g : SL(2, F)) :
    SL(2, F) :=
  Classical.choose (burnsideK312_exists_actHom c (burnsideK312_Cl_conj_mem c hN g))

theorem burnsideK312_Cl_aF_spec (c : OrthogonalFourCoordinates L s F) {t : MulAut V}
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (g : SL(2, F)) :
    burnsideK312_actHom c (burnsideK312_Cl_aF c hN g) = t * burnsideK312_actHom c g * t⁻¹ :=
  Classical.choose_spec (burnsideK312_exists_actHom c (burnsideK312_Cl_conj_mem c hN g))

@[expose] noncomputable def burnsideK312_Cl_alpha (c : OrthogonalFourCoordinates L s F)
    {t : MulAut V} (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) : MulAut SL(2, F) where
  toFun := burnsideK312_Cl_aF c hN
  invFun := burnsideK312_Cl_aF c (inv_mem hN)
  left_inv g := by
    apply burnsideK312_actHom_injective c
    rw [burnsideK312_Cl_aF_spec, burnsideK312_Cl_aF_spec]
    group
  right_inv g := by
    apply burnsideK312_actHom_injective c
    rw [burnsideK312_Cl_aF_spec, burnsideK312_Cl_aF_spec]
    group
  map_mul' g h := by
    apply burnsideK312_actHom_injective c
    rw [map_mul, burnsideK312_Cl_aF_spec, burnsideK312_Cl_aF_spec, burnsideK312_Cl_aF_spec,
      map_mul]
    group

theorem burnsideK312_Cl_actHom_alpha (c : OrthogonalFourCoordinates L s F) {t : MulAut V}
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (g : SL(2, F)) :
    burnsideK312_actHom c (burnsideK312_Cl_alpha c hN g) =
      t * burnsideK312_actHom c g * t⁻¹ :=
  burnsideK312_Cl_aF_spec c hN g

theorem burnsideK312_Cl_ringAut_comm (hF : Nat.card F = 2 ^ (2 * s)) (ρ τ : RingAut F) :
    ρ * τ = τ * ρ := by
  haveI : IsCyclic (RingAut F) :=
    (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.ringAut_card_and_cyclic hF).2
  exact (IsCyclic.commGroup (α := RingAut F)).mul_comm ρ τ

theorem burnsideK312_Cl_sg_comm (hF : Nat.card F = 2 ^ (2 * s)) (ρ : RingAut F) (x : F) :
    burnsideK312_sg F s (ρ x) = ρ (burnsideK312_sg F s x) := by
  have h := burnsideK312_Cl_ringAut_comm hF (burnsideK312_sgE hF) ρ
  have := congrArg (fun r : RingAut F => r x) h
  exact this

theorem burnsideK312_Cl_map_map (ρ τ : F ≃+* F) (g : SL(2, F)) :
    Matrix.SpecialLinearGroup.map ρ.toRingHom (Matrix.SpecialLinearGroup.map τ.toRingHom g) =
      Matrix.SpecialLinearGroup.map (ρ * τ).toRingHom g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  simp

theorem burnsideK312_Cl_data (c : OrthogonalFourCoordinates L s F) {t : MulAut V}
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (hsq : t * t = 1) :
    ∃ (h : SL(2, F)) (ρ : RingAut F),
      (∀ g, burnsideK312_Cl_alpha c hN g =
        h * Matrix.SpecialLinearGroup.map ρ.toRingHom g * h⁻¹) ∧
      h * Matrix.SpecialLinearGroup.map ρ.toRingHom h = 1 ∧ ρ * ρ = 1 := by
  have hn : 1 ≤ 2 * s := by
    have := burnsideK312_one_le c.field_card
    omega
  have key := (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.even_SL2_full_automorphism_semilinear_model
    hn c.field_card).2.2.2.2
  obtain ⟨⟨h, ρ⟩, hp, -⟩ := key (burnsideK312_Cl_alpha c hN)
  refine ⟨h, ρ, hp, ?_⟩
  have hαα : ∀ g, burnsideK312_Cl_alpha c hN (burnsideK312_Cl_alpha c hN g) = g := by
    intro g
    apply burnsideK312_actHom_injective c
    rw [burnsideK312_Cl_actHom_alpha, burnsideK312_Cl_actHom_alpha,
      inv_eq_of_mul_eq_one_right hsq]
    have e : t * (t * burnsideK312_actHom c g * t) * t = (t * t) * burnsideK312_actHom c g * (t * t) := by
      group
    rw [e, hsq, one_mul, mul_one]
  have hp' : ∀ g, burnsideK312_Cl_alpha c hN g =
      h * Matrix.SpecialLinearGroup.map ρ.toRingHom g * h⁻¹ := hp
  obtain ⟨p1, -, huniq1⟩ := key (1 : MulAut SL(2, F))
  have hone : ∀ g : SL(2, F), (1 : MulAut SL(2, F)) g =
      (1 : SL(2, F)) * Matrix.SpecialLinearGroup.map (1 : RingAut F).toRingHom g *
        (1 : SL(2, F))⁻¹ := by
    intro g
    rw [MulAut.one_apply, inv_one, one_mul, mul_one]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    simp
  have hq : ∀ g : SL(2, F), (1 : MulAut SL(2, F)) g =
      (h * Matrix.SpecialLinearGroup.map ρ.toRingHom h) *
        Matrix.SpecialLinearGroup.map (ρ * ρ).toRingHom g *
        (h * Matrix.SpecialLinearGroup.map ρ.toRingHom h)⁻¹ := by
    intro g
    have h1 := hαα g
    rw [hp' (burnsideK312_Cl_alpha c hN g), hp' g, map_mul, map_mul, map_inv,
      burnsideK312_Cl_map_map] at h1
    calc (1 : MulAut SL(2, F)) g = g := rfl
      _ = h * (Matrix.SpecialLinearGroup.map ρ.toRingHom h *
            Matrix.SpecialLinearGroup.map (ρ * ρ).toRingHom g *
            (Matrix.SpecialLinearGroup.map ρ.toRingHom h)⁻¹) * h⁻¹ := h1.symm
      _ = _ := by group
  have e1 := huniq1 (1, 1) (fun g => hone g)
  have e2 := huniq1 (h * Matrix.SpecialLinearGroup.map ρ.toRingHom h, ρ * ρ) (fun g => hq g)
  exact Prod.mk.inj (e2.trans e1.symm)

theorem burnsideK312_Cl_sq_eq_one (hF : Nat.card F = 2 ^ (2 * s)) {ρ : RingAut F}
    (h : ρ * ρ = 1) : ρ = 1 ∨ ρ = burnsideK312_sgE hF := by
  classical
  have hs := burnsideK312_one_le hF
  have hcc := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.ringAut_card_and_cyclic hF
  haveI hcyc : IsCyclic (RingAut F) := hcc.2
  haveI : Finite (RingAut F) := Nat.finite_of_card_ne_zero (by rw [hcc.1]; omega)
  haveI : Fintype (RingAut F) := Fintype.ofFinite _
  have hσ2 : burnsideK312_sgE hF * burnsideK312_sgE hF = 1 := by
    ext x
    exact burnsideK312_sg_sg hF x
  have hσ1 : burnsideK312_sgE hF ≠ 1 := by
    intro h1
    obtain ⟨ω, hω⟩ := burnsideK312_exists_notFixed hs hF
    apply hω
    have := congrArg (fun r : RingAut F => r ω) h1
    simpa [burnsideK312_sgE_apply] using this
  by_contra hcon
  push Not at hcon
  have hcard := IsCyclic.card_pow_eq_one_le (α := RingAut F) (n := 2) (by norm_num)
  have hsub : ({1, burnsideK312_sgE hF, ρ} : Finset (RingAut F)) ⊆
      Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · simpa [pow_two] using hσ2
    · simpa [pow_two] using h
  have h3 : ({1, burnsideK312_sgE hF, ρ} : Finset (RingAut F)).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, burnsideK312_sgE hF, ρ, hσ1.symm, hcon.1.symm, hcon.2.symm, rfl⟩
  have := Finset.card_le_card hsub
  omega

@[expose] def burnsideK312_Cl_Tm (s : ℕ) (h : Matrix (Fin 2) (Fin 2) F) (ρ : F ≃+* F)
    (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  h * M.map ρ * (frobPow s h)ᵀ

theorem burnsideK312_Cl_Tm_smul (h : Matrix (Fin 2) (Fin 2) F) (ρ : F ≃+* F)
    (a : F) (M : Matrix (Fin 2) (Fin 2) F) :
    burnsideK312_Cl_Tm s h ρ (a • M) = ρ a • burnsideK312_Cl_Tm s h ρ M := by
  unfold burnsideK312_Cl_Tm
  have : (a • M).map ρ = ρ a • M.map ρ := by
    ext i j
    simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem burnsideK312_Cl_Tm_Tm (ρ : F ≃+* F) (hρ2 : ∀ x, ρ (ρ x) = x)
    (hσρ : ∀ x, burnsideK312_sg F s (ρ x) = ρ (burnsideK312_sg F s x))
    {h : Matrix (Fin 2) (Fin 2) F} (hh : h * h.map ρ = 1) (M : Matrix (Fin 2) (Fin 2) F) :
    burnsideK312_Cl_Tm s h ρ (burnsideK312_Cl_Tm s h ρ M) = M := by
  unfold burnsideK312_Cl_Tm
  have hmm : ∀ N : Matrix (Fin 2) (Fin 2) F, (N.map ρ).map ρ = N := fun N => by
    ext i j
    simp [hρ2]
  have hs1 : frobPow s h * (frobPow s h).map ρ = 1 := by
    have h1 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N.map (burnsideK312_sg F s)) hh
    simp only [Matrix.map_mul] at h1
    have h2 : (h.map ρ).map (burnsideK312_sg F s) = (h.map (burnsideK312_sg F s)).map ρ := by
      ext i j
      simp [hσρ]
    rw [h2] at h1
    rw [burnsideK312_frobPow_eq_map]
    refine h1.trans ?_
    ext i j
    simp [Matrix.one_apply]
  calc h * (h * M.map ρ * (frobPow s h)ᵀ).map ρ * (frobPow s h)ᵀ
      = h * (h.map ρ * (M.map ρ).map ρ * ((frobPow s h)ᵀ).map ρ) * (frobPow s h)ᵀ := by
        rw [Matrix.map_mul, Matrix.map_mul]
    _ = h * (h.map ρ * M * ((frobPow s h).map ρ)ᵀ) * (frobPow s h)ᵀ := by
        rw [hmm, Matrix.transpose_map]
    _ = (h * h.map ρ) * M * (((frobPow s h).map ρ)ᵀ * (frobPow s h)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = M := by
        rw [hh, ← Matrix.transpose_mul, hs1, Matrix.transpose_one]
        simp

theorem burnsideK312_outer_involution (c : OrthogonalFourCoordinates L s F)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {t : MulAut V} (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (hsq : t ^ 2 = 1)
    (ht : t ∉ L) :
    ∃ h : SL(2, F), h * Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) h = 1 ∧
      t = burnsideK312_actHom c h * burnsideK312_sh c := by
  have hsq' : t * t = 1 := by rw [← pow_two]; exact hsq
  obtain ⟨h, ρ, hα, hhρ, hρρ⟩ := burnsideK312_Cl_data c hN hsq'
  have hF := c.field_card
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hρσ := burnsideK312_Cl_sg_comm hF ρ
  have hρ2 : ∀ x, ρ (ρ x) = x := fun x => by
    have := congrArg (fun r : RingAut F => r x) hρρ
    simpa using this
  have hΦπ : ∀ g : SL(2, F), burnsideK312_fieldTwist c ρ hρσ * burnsideK312_actHom c g =
      burnsideK312_actHom c (Matrix.SpecialLinearGroup.map ρ.toRingHom g) *
        burnsideK312_fieldTwist c ρ hρσ :=
    burnsideK312_fieldTwist_actHom c ρ hρσ
  obtain ⟨T, hT⟩ : ∃ T : MulAut V, T = burnsideK312_actHom c h * burnsideK312_fieldTwist c ρ hρσ :=
    ⟨_, rfl⟩
  have hTπ : ∀ g : SL(2, F), T * burnsideK312_actHom c g =
      burnsideK312_actHom c (burnsideK312_Cl_alpha c hN g) * T := by
    intro g
    rw [hα g, map_mul, map_mul, map_inv, hT, mul_assoc, hΦπ g]
    group
  have htπ : ∀ g : SL(2, F), t * burnsideK312_actHom c g =
      burnsideK312_actHom c (burnsideK312_Cl_alpha c hN g) * t := by
    intro g
    rw [burnsideK312_Cl_actHom_alpha]
    group
  have hφ0 : ∀ g : SL(2, F), (T⁻¹ * t) * burnsideK312_actHom c g =
      burnsideK312_actHom c g * (T⁻¹ * t) := by
    intro g
    have e1 : burnsideK312_actHom c (burnsideK312_Cl_alpha c hN g) =
        T * burnsideK312_actHom c g * T⁻¹ := eq_mul_inv_of_mul_eq (hTπ g).symm
    calc T⁻¹ * t * burnsideK312_actHom c g = T⁻¹ * (t * burnsideK312_actHom c g) := by
          rw [mul_assoc]
      _ = T⁻¹ * (burnsideK312_actHom c (burnsideK312_Cl_alpha c hN g) * t) := by rw [htπ g]
      _ = T⁻¹ * (T * burnsideK312_actHom c g * T⁻¹ * t) := by rw [e1]
      _ = burnsideK312_actHom c g * (T⁻¹ * t) := by group
  obtain ⟨κ, hκ, hκv⟩ := burnsideK312_commutant c hirr (T⁻¹ * t) hφ0
  have hmT : ∀ w, c.matrix (T w) = burnsideK312_Cl_Tm s (h : Matrix (Fin 2) (Fin 2) F) ρ
      (c.matrix w) := by
    intro w
    rw [hT, MulAut.mul_apply, burnsideK312_matrix_act, burnsideK312_matrix_fieldTwist]
    rfl
  have hmt : ∀ v, c.matrix (t v) = ρ κ • burnsideK312_Cl_Tm s (h : Matrix (Fin 2) (Fin 2) F) ρ
      (c.matrix v) := by
    intro v
    have e : t v = T ((T⁻¹ * t) v) := by simp [MulAut.mul_apply]
    rw [e, hmT, hκv, burnsideK312_Cl_Tm_smul]
  have hhρ' : (h : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F).map ρ = 1 := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hhρ
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply] using this
  have hTT : ∀ v, c.matrix (t (t v)) = (ρ κ * κ) • c.matrix v := by
    intro v
    rw [hmt (t v), hmt v, burnsideK312_Cl_Tm_smul, burnsideK312_Cl_Tm_Tm ρ hρ2 hρσ hhρ', hρ2,
      smul_smul]
  obtain ⟨E, hE⟩ := burnsideK312_exists_vec c (burnsideK312_herm_E11 (F := F) (s := s))
  have hρκκ : ρ κ * κ = 1 := by
    have h1 : t (t E) = E := by
      simpa [MulAut.mul_apply] using congrArg (fun m : MulAut V => m E) hsq'
    have h3 := hTT E
    rw [h1, hE] at h3
    have h4 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) h3
    simpa using h4.symm
  have hρκ : ρ κ = κ := by
    rcases burnsideK312_Cl_sq_eq_one hF hρρ with hρ1 | hρs
    · rw [hρ1]; rfl
    · rw [hρs, burnsideK312_sgE_apply]; exact hκ
  have hκ1 : κ = 1 := by
    rw [hρκ] at hρκκ
    have h0 : (κ - 1) ^ 2 = 0 := by linear_combination hρκκ + (1 - κ) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  rcases burnsideK312_Cl_sq_eq_one hF hρρ with hρ1 | hρs
  · exfalso
    apply ht
    have : t = burnsideK312_actHom c h := by
      ext v
      apply burnsideK312_matrix_injective c
      rw [hmt v, hκ1, burnsideK312_matrix_act, hρ1]
      simp only [map_one, one_smul, burnsideK312_Cl_Tm]
      congr 2
    rw [this]
    exact burnsideK312_actHom_mem c h
  · subst hρs
    have e : (burnsideK312_sgE hF).toRingHom = burnsideK312_sg F s := RingHom.ext fun x => rfl
    rw [e] at hhρ
    refine ⟨h, hhρ, ?_⟩
    ext v
    apply burnsideK312_matrix_injective c
    rw [hmt v, hκ1, MulAut.mul_apply, burnsideK312_matrix_act, burnsideK312_matrix_sh,
      burnsideK312_herm_transpose (burnsideK312_matrix_herm c v), burnsideK312_frobPow_eq_map,
      map_one, one_smul]
    rfl

theorem burnsideK312_Cl_range (c : OrthogonalFourCoordinates L s F) :
    (burnsideK312_actHom c).range = L := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact burnsideK312_actHom_mem c g
  · intro hx
    obtain ⟨g, hg⟩ := burnsideK312_exists_actHom c hx
    exact ⟨g, hg⟩

theorem burnsideK312_Cl_card_L (c : OrthogonalFourCoordinates L s F) :
    Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← burnsideK312_card_SL2 (E := F)]
  exact (Nat.card_congr ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans
    c.group_equiv).toEquiv).symm

theorem burnsideK312_Cl_card_Uc (c : OrthogonalFourCoordinates L s F) :
    Nat.card (burnsideK312_Uc c) = Nat.card F := by
  unfold burnsideK312_Uc
  rw [Subgroup.card_map_of_injective (burnsideK312_actHom_injective c)]
  exact burnsideK312_card_rootSub

theorem burnsideK312_Cl_conj_hom (c : OrthogonalFourCoordinates L s F) (x : SL(2, F)) :
    (burnsideK312_actHom c).comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (burnsideK312_actHom c x)).toMonoidHom.comp (burnsideK312_actHom c) := by
  ext g
  simp [MulAut.conj_apply]

theorem burnsideK312_sylow_of_isSylow (c : OrthogonalFourCoordinates L s F)
    {S : Subgroup (MulAut V)} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S L) :
    ∃ g : SL(2, F), S = (burnsideK312_Uc c).map
      (MulAut.conj (burnsideK312_actHom c g)).toMonoidHom := by
  obtain ⟨hSL, hSp, hSidx⟩ := hS
  have hS'p : IsPGroup 2 ↥(S.comap (burnsideK312_actHom c)) :=
    hSp.comap_of_injective _ (burnsideK312_actHom_injective c)
  obtain ⟨x, hx⟩ := burnsideK312_sylow_conj hS'p
  refine ⟨x, ?_⟩
  have hmapS : (S.comap (burnsideK312_actHom c)).map (burnsideK312_actHom c) = S := by
    rw [Subgroup.map_comap_eq, burnsideK312_Cl_range]
    exact inf_eq_right.mpr hSL
  have hUc : (burnsideK312_Uc c).map (MulAut.conj (burnsideK312_actHom c x)).toMonoidHom =
      ((CFSG.Quasithin.B45L2.rootSub (⊤ : AddSubgroup F)).map (MulAut.conj x).toMonoidHom).map
        (burnsideK312_actHom c) := by
    unfold burnsideK312_Uc
    rw [Subgroup.map_map, Subgroup.map_map, burnsideK312_Cl_conj_hom]
  have hle : S ≤ (burnsideK312_Uc c).map (MulAut.conj (burnsideK312_actHom c x)).toMonoidHom := by
    rw [hUc, ← hmapS]
    exact Subgroup.map_mono hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hcardUc : Nat.card ((burnsideK312_Uc c).map
      (MulAut.conj (burnsideK312_actHom c x)).toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (burnsideK312_actHom c x)).injective,
      burnsideK312_Cl_card_Uc]
  rw [hcardUc]
  have h1 := Subgroup.index_mul_card (S.subgroupOf L)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv,
    burnsideK312_Cl_card_L c] at h1
  obtain ⟨k, hk⟩ : ∃ k, Nat.card S = 2 ^ k := ⟨_, card_eq_two_pow_of_isPGroup hSp⟩
  obtain ⟨e, he⟩ : ∃ e, Nat.card F = 2 ^ e := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hqodd : ¬ 2 ∣ Nat.card F ^ 2 - 1 := by
    have h2 : 2 ≤ Nat.card F := by
      have : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    obtain ⟨k', hk'⟩ := burnsideK312_even_card (E := F)
    have hk1 : 1 ≤ k' := by omega
    have e4 : Nat.card F ^ 2 = 4 * (k' * k') := by rw [hk']; ring
    have hkk : 1 ≤ k' * k' := Nat.mul_pos hk1 hk1
    rw [e4]
    omega
  have hqv : padicValNat 2 (Nat.card F) = e := by
    rw [he]
    exact padicValNat.prime_pow e
  have hkv : padicValNat 2 (Nat.card S) = k := by
    rw [hk]
    exact padicValNat.prime_pow k
  have hq2 : 2 ≤ Nat.card F := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hq1 : Nat.card F ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ Nat.card F ^ 2 := by nlinarith
    omega
  have hv := congrArg (padicValNat 2) h1
  rw [padicValNat.mul (Subgroup.index_ne_zero_of_finite) Nat.card_pos.ne',
    padicValNat.mul Nat.card_pos.ne' hq1, padicValNat.eq_zero_of_not_dvd hSidx, hkv, hqv,
    padicValNat.eq_zero_of_not_dvd hqodd] at hv
  have hke : k = e := by omega
  rw [hk, he, hke]

theorem burnsideK312_Cl_borel (c : OrthogonalFourCoordinates L s F) {h0 : SL(2, F)}
    (h : burnsideK312_actHom c (h0 * CFSG.Quasithin.JonesParshall.uMat 1 * h0⁻¹) ∈
      burnsideK312_Uc c) : (h0 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨g, ⟨y, -, rfl⟩, hg⟩ := h
  have e := burnsideK312_actHom_injective c hg
  have e2 := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) 1 0) e
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    CFSG.Quasithin.JonesParshall.uMat_coe, Matrix.adjugate_fin_two] at e2
  rw [Matrix.eta_fin_two (h0 : Matrix (Fin 2) (Fin 2) F)] at e2
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e2
  have h3 : (h0 : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 = 0 := by linear_combination e2
  exact pow_eq_zero_iff two_ne_zero |>.mp h3

theorem burnsideK312_Cl_cocycle_borel (hF : Nat.card F = 2 ^ (2 * s)) {h0 : SL(2, F)}
    (h10 : (h0 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hcoc : h0 * Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) h0 = 1) :
    ∃ b : SL(2, F), (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      h0 * Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) b = b := by
  classical
  have hs := burnsideK312_one_le hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet : (h0 : Matrix (Fin 2) (Fin 2) F) 0 0 * (h0 : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := h0.2
    rw [Matrix.det_fin_two, h10] at this
    simpa using this
  have hcoc' := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hcoc
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.SpecialLinearGroup.coe_one] at hcoc'
  have e00 := congrFun (congrFun hcoc' 0) 0
  have e01 := congrFun (congrFun hcoc' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, burnsideK312_sg_apply, h10] at e00 e01
  obtain ⟨a, ha⟩ : ∃ a, (h0 : Matrix (Fin 2) (Fin 2) F) 0 0 = a := ⟨_, rfl⟩
  obtain ⟨x', hx⟩ : ∃ x', (h0 : Matrix (Fin 2) (Fin 2) F) 0 1 = x' := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, (h0 : Matrix (Fin 2) (Fin 2) F) 1 1 = w := ⟨_, rfl⟩
  rw [ha, hw] at hdet
  rw [ha] at e00
  rw [ha, hx, hw] at e01
  have hh0 : (h0 : Matrix (Fin 2) (Fin 2) F) = !![a, x'; 0, w] := by
    rw [Matrix.eta_fin_two (h0 : Matrix (Fin 2) (Fin 2) F), ha, hx, hw, h10]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hwσ : w = a ^ 2 ^ s := by
    have : a * w = a * a ^ 2 ^ s := by rw [hdet, e00]
    exact mul_left_cancel₀ ha0 this
  have hσw : w ^ 2 ^ s = a := by
    rw [hwσ]
    have := burnsideK312_sg_sg hF a
    simpa [burnsideK312_sg_apply] using this
  have hx'σ : x' ^ 2 ^ s = x' := by
    have h5 : a * (x' ^ 2 ^ s + x') = 0 := by
      rw [hσw] at e01
      linear_combination e01
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h ha0
    · exact CharTwo.add_eq_zero.mp h
  obtain ⟨y, hy0, hy⟩ := burnsideK312_exists_hilbert90 e00
  obtain ⟨w', hw'⟩ := burnsideK312_exists_trace hs hF hx'σ
  have hYY : (y ^ 2 ^ s) ^ 2 ^ s = y := by
    have := burnsideK312_sg_sg hF y
    simpa [burnsideK312_sg_apply] using this
  have hY0 : y ^ 2 ^ s ≠ 0 := pow_ne_zero _ hy0
  obtain ⟨b, hb⟩ : ∃ b : SL(2, F), (b : Matrix (Fin 2) (Fin 2) F) = !![y, w' / y ^ 2 ^ s; 0, y⁻¹] :=
    ⟨⟨_, by simp [Matrix.det_fin_two, hy0]⟩, rfl⟩
  refine ⟨b, by rw [hb]; simp, ?_⟩
  have haw : w = a⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have key : (h0 : Matrix (Fin 2) (Fin 2) F) *
      (b : Matrix (Fin 2) (Fin 2) F).map (burnsideK312_sg F s) = (b : Matrix (Fin 2) (Fin 2) F) := by
    rw [hh0, hb]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, burnsideK312_sg_apply, map_inv₀, map_div₀,
        div_pow, hYY]
    · exact hy.symm
    · have hY0' : y ^ 2 ^ s ≠ 0 := hY0
      have e1 : a * (w' ^ 2 ^ s / y) = w' ^ 2 ^ s / y ^ 2 ^ s := by
        rw [mul_div_assoc', div_eq_div_iff hy0 hY0']
        calc a * w' ^ 2 ^ s * y ^ 2 ^ s = w' ^ 2 ^ s * (a * y ^ 2 ^ s) := by ring
          _ = w' ^ 2 ^ s * y := by rw [← hy]
      rw [e1, ← hw']
      field_simp
      linear_combination (w' ^ 2 ^ s) * h2
    · rw [haw]
      conv_rhs => rw [hy]
      rw [mul_inv]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, key]

theorem burnsideK312_Cl_conj_uMat {b : SL(2, F)}
    (hb : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ∃ p : F, p ≠ 0 ∧ ∀ x : F,
      b * CFSG.Quasithin.JonesParshall.uMat x * b⁻¹ =
        CFSG.Quasithin.JonesParshall.uMat (p ^ 2 * x) := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) F) 0 0 * (b : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := b.2
    rw [Matrix.det_fin_two, hb] at this
    simpa using this
  refine ⟨(b : Matrix (Fin 2) (Fin 2) F) 0 0, left_ne_zero_of_mul_eq_one hdet, fun x => ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, CFSG.Quasithin.JonesParshall.uMat_coe,
    CFSG.Quasithin.JonesParshall.uMat_coe, Matrix.adjugate_fin_two]
  rw [Matrix.eta_fin_two (b : Matrix (Fin 2) (Fin 2) F)]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb]
  all_goals first
    | linear_combination hdet
    | linear_combination (b : Matrix (Fin 2) (Fin 2) F) 0 0 * hdet
    | ring

theorem burnsideK312_Cl_rootSub_conj {b : SL(2, F)}
    (hb : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (CFSG.Quasithin.B45L2.rootSub (⊤ : AddSubgroup F)).map (MulAut.conj b).toMonoidHom =
      CFSG.Quasithin.B45L2.rootSub (⊤ : AddSubgroup F) := by
  ext g
  constructor
  · rintro ⟨u, ⟨x, -, rfl⟩, rfl⟩
    obtain ⟨p, hp0, hp⟩ := burnsideK312_Cl_conj_uMat hb
    exact ⟨p ^ 2 * x, trivial, by simpa [MulAut.conj_apply] using hp x⟩
  · rintro ⟨y, -, rfl⟩
    obtain ⟨p, hp0, hp⟩ := burnsideK312_Cl_conj_uMat hb
    refine ⟨CFSG.Quasithin.JonesParshall.uMat (y / p ^ 2), ⟨y / p ^ 2, trivial, rfl⟩, ?_⟩
    have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp0
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hp, mul_div_cancel₀ _ hp2]

theorem burnsideK312_Cl_Uc_conj_upper (c : OrthogonalFourCoordinates L s F) {b : SL(2, F)}
    (hb : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (burnsideK312_Uc c).map (MulAut.conj (burnsideK312_actHom c b)).toMonoidHom =
      burnsideK312_Uc c := by
  unfold burnsideK312_Uc
  rw [Subgroup.map_map, ← burnsideK312_Cl_conj_hom c b, ← Subgroup.map_map,
    burnsideK312_Cl_rootSub_conj hb]

theorem burnsideK312_Cl_sgmap_sgmap (hF : Nat.card F = 2 ^ (2 * s)) (g : SL(2, F)) :
    Matrix.SpecialLinearGroup.map (burnsideK312_sg F s)
      (Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    burnsideK312_sg_sg hF]

theorem burnsideK312_pair (c : OrthogonalFourCoordinates L s F)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {S : Subgroup (MulAut V)} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S L) {t : MulAut V}
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (hsq : t ^ 2 = 1) (ht : t ∉ L)
    (htS : t ∈ Subgroup.normalizer (S : Set (MulAut V))) :
    ∃ g : SL(2, F), S = (burnsideK312_Uc c).map
        (MulAut.conj (burnsideK312_actHom c g)).toMonoidHom ∧
      t = burnsideK312_actHom c g * burnsideK312_sh c * (burnsideK312_actHom c g)⁻¹ := by
  have hF := c.field_card
  obtain ⟨g0, hSg0⟩ := burnsideK312_sylow_of_isSylow c hS
  obtain ⟨h, hhσ, hth⟩ := burnsideK312_outer_involution c hirr hN hsq ht
  set σ : SL(2, F) →* SL(2, F) := Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) with hσdef
  have hσσ : ∀ g, σ (σ g) = g := burnsideK312_Cl_sgmap_sgmap hF
  set π := burnsideK312_actHom c with hπ
  set sh := burnsideK312_sh c with hsh
  set h0 : SL(2, F) := g0⁻¹ * h * σ g0 with hh0
  have hcoc0 : h0 * σ h0 = 1 := by
    have : h0 * σ h0 = g0⁻¹ * (h * σ h) * g0 := by
      rw [hh0, map_mul, map_mul, map_inv, hσσ]
      group
    rw [this, hhσ]
    group
  have ht0 : (π g0)⁻¹ * t * π g0 = π h0 * sh := by
    have e1 := burnsideK312_sh_actHom c g0
    calc (π g0)⁻¹ * t * π g0 = (π g0)⁻¹ * (π h * sh) * π g0 := by rw [← hth]
      _ = (π g0)⁻¹ * π h * (sh * π g0 * sh) * sh⁻¹ := by group
      _ = π h0 * sh := by
        rw [e1, hsh, burnsideK312_sh_inv, hh0, map_mul, map_mul, map_inv]
  have hu1 : π (CFSG.Quasithin.JonesParshall.uMat 1) ∈ burnsideK312_Uc c :=
    ⟨CFSG.Quasithin.JonesParshall.uMat 1, ⟨1, trivial, rfl⟩, rfl⟩
  have hxS : π g0 * π (CFSG.Quasithin.JonesParshall.uMat 1) * (π g0)⁻¹ ∈ S := by
    rw [hSg0]
    exact ⟨_, hu1, by simp [MulAut.conj_apply]⟩
  have hxS' := (Subgroup.mem_normalizer_iff.mp htS _).mp hxS
  rw [hSg0] at hxS'
  obtain ⟨u, hu, hu_eq⟩ := hxS'
  have hu_val : u = π (h0 * CFSG.Quasithin.JonesParshall.uMat 1 * h0⁻¹) := by
    have e0 : u = (π g0)⁻¹ * (t * (π g0 * π (CFSG.Quasithin.JonesParshall.uMat 1) * (π g0)⁻¹) *
        t⁻¹) * π g0 := by
      rw [← hu_eq]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have e2 : (π g0)⁻¹ * (t * (π g0 * π (CFSG.Quasithin.JonesParshall.uMat 1) * (π g0)⁻¹) *
        t⁻¹) * π g0 = ((π g0)⁻¹ * t * π g0) * π (CFSG.Quasithin.JonesParshall.uMat 1) *
          ((π g0)⁻¹ * t * π g0)⁻¹ := by group
    rw [e0, e2, ht0]
    have e3 : (π h0 * sh) * π (CFSG.Quasithin.JonesParshall.uMat 1) * (π h0 * sh)⁻¹ =
        π h0 * (sh * π (CFSG.Quasithin.JonesParshall.uMat 1) * sh⁻¹) * (π h0)⁻¹ := by group
    rw [e3, hsh, burnsideK312_sh_inv, burnsideK312_sh_uMat, one_pow]
    simp only [map_mul, map_inv]
    rfl
  have hborel : (h0 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    burnsideK312_Cl_borel c (hu_val ▸ hu)
  obtain ⟨b, hb10, hb⟩ := burnsideK312_Cl_cocycle_borel hF hborel hcoc0
  refine ⟨g0 * b, ?_, ?_⟩
  · have e5 : (burnsideK312_Uc c).map (MulAut.conj (π (g0 * b))).toMonoidHom =
        ((burnsideK312_Uc c).map (MulAut.conj (π b)).toMonoidHom).map
          (MulAut.conj (π g0)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e5, burnsideK312_Cl_Uc_conj_upper c hb10, hSg0]
  · have hh0b : h0 = b * (σ b)⁻¹ := eq_mul_inv_of_mul_eq hb
    have e4 : π h0 * sh = π b * sh * (π b)⁻¹ := by
      rw [hh0b, map_mul, map_inv, ← burnsideK312_sh_actHom c b]
      calc π b * (sh * π b * burnsideK312_sh c)⁻¹ * sh = π b * sh⁻¹ * (π b)⁻¹ := by
            rw [← hsh]
            group
        _ = π b * sh * (π b)⁻¹ := by rw [hsh, burnsideK312_sh_inv]
    have e6 : t = π g0 * ((π g0)⁻¹ * t * π g0) * (π g0)⁻¹ := by group
    rw [e6, ht0, e4, map_mul]
    group

end Cl


section Geo

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def burnsideK312_Geo_mk (c : OrthogonalFourCoordinates L s F) (a b d : F)
    (ha : a ^ 2 ^ s = a) (hd : d ^ 2 ^ s = d) : V :=
  Classical.choose (burnsideK312_exists_vec c (burnsideK312_herm_mk c.field_card (b := b) ha hd))

theorem burnsideK312_Geo_matrix_mk (c : OrthogonalFourCoordinates L s F) (a b d : F)
    (ha : a ^ 2 ^ s = a) (hd : d ^ 2 ^ s = d) :
    c.matrix (burnsideK312_Geo_mk c a b d ha hd) = !![a, b; b ^ 2 ^ s, d] :=
  Classical.choose_spec
    (burnsideK312_exists_vec c (burnsideK312_herm_mk c.field_card (b := b) ha hd))

theorem burnsideK312_Geo_pol (M N : Matrix (Fin 2) (Fin 2) F) :
    (M + N).det - M.det - N.det =
      M 0 0 * N 1 1 + N 0 0 * M 1 1 - M 0 1 * N 1 0 - N 0 1 * M 1 0 := by
  simp only [Matrix.det_fin_two, Matrix.add_apply]
  ring

theorem burnsideK312_Geo_zpowers (c : OrthogonalFourCoordinates L s F) :
    ∀ x ∈ Subgroup.zpowers (burnsideK312_sh c), x = 1 ∨ x = burnsideK312_sh c := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hsq : burnsideK312_sh c ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact burnsideK312_sh_sq c
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hsq, one_zpow]
  · right
    rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

@[expose] noncomputable def burnsideK312_Geo_Jv (c : OrthogonalFourCoordinates L s F) : V :=
  Classical.choose (burnsideK312_exists_vec c (burnsideK312_herm_J (F := F) (s := s)))

theorem burnsideK312_Geo_matrix_Jv (c : OrthogonalFourCoordinates L s F) :
    c.matrix (burnsideK312_Geo_Jv c) = !![(0 : F), 1; 1, 0] :=
  Classical.choose_spec (burnsideK312_exists_vec c (burnsideK312_herm_J (F := F) (s := s)))

@[expose] noncomputable def burnsideK312_Geo_line (c : OrthogonalFourCoordinates L s F) :
    Subgroup V where
  carrier := {v | ∃ κ : F, κ ^ 2 ^ s = κ ∧ c.matrix v = κ • !![(0 : F), 1; 1, 0]}
  one_mem' := ⟨0, by simp, by rw [burnsideK312_matrix_one, zero_smul]⟩
  mul_mem' := fun {a b} ⟨κ, hκ, ha⟩ ⟨κ', hκ', hb⟩ =>
    ⟨κ + κ', by rw [add_pow_char_pow, hκ, hκ'], by
      rw [burnsideK312_matrix_mul, ha, hb, add_smul]⟩
  inv_mem' := fun {a} ⟨κ, hκ, ha⟩ =>
    ⟨κ, hκ, by
      rw [burnsideK312_matrix_inv, ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]⟩

theorem burnsideK312_Geo_mem_line (c : OrthogonalFourCoordinates L s F) (v : V) :
    v ∈ burnsideK312_Geo_line c ↔
      ∃ κ : F, κ ^ 2 ^ s = κ ∧ c.matrix v = κ • !![(0 : F), 1; 1, 0] := Iff.rfl

theorem burnsideK312_Geo_commV (c : OrthogonalFourCoordinates L s F) :
    commV (Subgroup.zpowers (burnsideK312_sh c)) = burnsideK312_Geo_line c := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply le_antisymm
  · unfold commV
    rw [Subgroup.closure_le]
    rintro w ⟨x, hx, v, rfl⟩
    rcases burnsideK312_Geo_zpowers c x hx with rfl | rfl
    · simp only [MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have hM := burnsideK312_matrix_herm c v
      have h10 := burnsideK312_herm_apply hM 1 0
      have h01 := burnsideK312_herm_apply hM 0 1
      refine ⟨c.matrix v 0 1 + c.matrix v 1 0, ?_, ?_⟩
      · rw [add_pow_char_pow, ← h10, ← h01, add_comm]
      · rw [burnsideK312_matrix_mul, burnsideK312_matrix_inv, burnsideK312_matrix_sh]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq, h2]
        all_goals first
          | ring1
          | linear_combination (c.matrix v 0 0) * h2
          | linear_combination (c.matrix v 1 1) * h2
          | linear_combination (c.matrix v 0 1) * h2
          | linear_combination (c.matrix v 1 0) * h2
  · rintro v ⟨κ, hκ, hv⟩
    obtain ⟨z, hz⟩ := burnsideK312_exists_trace hs hF hκ
    apply Subgroup.subset_closure
    refine ⟨burnsideK312_sh c, Subgroup.mem_zpowers _,
      burnsideK312_Geo_mk c 0 z 0 (by simp) (by simp), ?_⟩
    apply burnsideK312_matrix_injective c
    rw [burnsideK312_matrix_mul, burnsideK312_matrix_inv, burnsideK312_matrix_sh, hv,
      burnsideK312_Geo_matrix_mk, ← hz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq, h2, add_comm]

theorem burnsideK312_Geo_fix (c : OrthogonalFourCoordinates L s F) (v : V) :
    v ∈ fixV (Subgroup.zpowers (burnsideK312_sh c)) ↔ (c.matrix v)ᵀ = c.matrix v := by
  constructor
  · intro h
    have h1 := h (burnsideK312_sh c) (Subgroup.mem_zpowers _)
    have h2 := congrArg c.matrix h1
    rwa [burnsideK312_matrix_sh] at h2
  · intro h x hx
    rcases burnsideK312_Geo_zpowers c x hx with rfl | rfl
    · rfl
    · apply burnsideK312_matrix_injective c
      rw [burnsideK312_matrix_sh]
      exact h

theorem burnsideK312_Geo_reflection (c : OrthogonalFourCoordinates L s F) (v : V) :
    c.matrix (burnsideK312_sh c v) = c.matrix v +
      (c.polar v (burnsideK312_Geo_Jv c) / (c.matrix (burnsideK312_Geo_Jv c)).det) •
        c.matrix (burnsideK312_Geo_Jv c) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  unfold OrthogonalFourCoordinates.polar
  rw [burnsideK312_Geo_pol, burnsideK312_Geo_matrix_Jv, burnsideK312_matrix_sh]
  have hd : (!![(0 : F), 1; 1, 0]).det = -1 := by simp [Matrix.det_fin_two]
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals first
    | ring1
    | linear_combination (c.matrix v 0 1) * h2
    | linear_combination (c.matrix v 1 0) * h2
    | linear_combination (-(c.matrix v 0 1)) * h2
    | linear_combination (-(c.matrix v 1 0)) * h2

theorem burnsideK312_Geo_Jv_ne (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_Geo_Jv c ≠ 1 := by
  intro h
  have h1 := burnsideK312_Geo_matrix_Jv c
  rw [h, burnsideK312_matrix_one] at h1
  have := congrFun (congrFun h1 0) 1
  simp at this

theorem burnsideK312_Geo_det_Jv (c : OrthogonalFourCoordinates L s F) :
    (c.matrix (burnsideK312_Geo_Jv c)).det ≠ 0 := by
  rw [burnsideK312_Geo_matrix_Jv]
  simp [Matrix.det_fin_two]

theorem burnsideK312_Geo_isPoint (c : OrthogonalFourCoordinates L s F) :
    c.IsPoint (commV (Subgroup.zpowers (burnsideK312_sh c))) := by
  refine ⟨burnsideK312_Geo_Jv c, burnsideK312_Geo_Jv_ne c, fun v => ?_⟩
  rw [burnsideK312_Geo_commV, burnsideK312_Geo_mem_line, burnsideK312_Geo_matrix_Jv]
  exact Iff.rfl

theorem burnsideK312_Geo_nonsingular (c : OrthogonalFourCoordinates L s F) :
    ∀ vector ∈ commV (Subgroup.zpowers (burnsideK312_sh c)), vector ≠ 1 →
      (c.matrix vector).det ≠ 0 := by
  intro v hv hv1
  rw [burnsideK312_Geo_commV, burnsideK312_Geo_mem_line] at hv
  obtain ⟨κ, hκ, hM⟩ := hv
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    apply hv1
    apply burnsideK312_matrix_injective c
    rw [hM, zero_smul, burnsideK312_matrix_one]
  rw [hM, Matrix.det_smul]
  simp [Matrix.det_fin_two, hκ0]

theorem burnsideK312_Geo_mem_centralizer (c : OrthogonalFourCoordinates L s F) (x : MulAut V) :
    x ∈ L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ↔
      ∃ g : SL(2, F), Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g = g ∧
        x = burnsideK312_actHom c g := by
  constructor
  · rintro ⟨hxL, hxC⟩
    obtain ⟨g, rfl⟩ := burnsideK312_exists_actHom c hxL
    refine ⟨g, ?_, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hxC _ (Set.mem_singleton _)
    have h2 := burnsideK312_sh_actHom c g
    rw [h1, mul_assoc, burnsideK312_sh_sq, mul_one] at h2
    exact (burnsideK312_actHom_injective c h2).symm
  · rintro ⟨g, hg, rfl⟩
    refine ⟨burnsideK312_actHom_mem c g, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    have h2 := burnsideK312_sh_actHom c g
    rw [hg] at h2
    have h3 := congrArg (fun m => m * burnsideK312_sh c) h2
    simpa [mul_assoc, burnsideK312_sh_sq] using h3

theorem burnsideK312_Geo_starJ (g : SL(2, F)) :
    (g : Matrix (Fin 2) (Fin 2) F) * !![(0 : F), 1; 1, 0] *
        (frobPow s (g : Matrix (Fin 2) (Fin 2) F))ᵀ = !![(0 : F), 1; 1, 0] ↔
      Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g = g := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨p, hp⟩ : ∃ p, (g : Matrix (Fin 2) (Fin 2) F) 0 0 = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, (g : Matrix (Fin 2) (Fin 2) F) 0 1 = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, (g : Matrix (Fin 2) (Fin 2) F) 1 0 = r := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, (g : Matrix (Fin 2) (Fin 2) F) 1 1 = w := ⟨_, rfl⟩
  have hdet : p * w + q * r = 1 := by
    have := g.2
    rw [Matrix.det_fin_two, hp, hq, hr, hw] at this
    linear_combination this + (q * r) * h2
  have hgm : (g : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, w] := by
    rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) F), hp, hq, hr, hw]
  constructor
  · intro h
    rw [hgm] at h
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    have e11 := congrFun (congrFun h 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow] at e00 e01 e10 e11
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hgm]
    fin_cases i <;> fin_cases j <;> simp [burnsideK312_sg_apply]
    · linear_combination (-(p ^ 2 ^ s)) * hdet + r * e00 + p * e10 + (-(p * r * q ^ 2 ^ s)) * h2
    · linear_combination (-(q ^ 2 ^ s)) * hdet + w * e00 + q * e10 + (-(w * q * p ^ 2 ^ s)) * h2
    · linear_combination (-(r ^ 2 ^ s)) * hdet + r * e01 + p * e11 + (-(p * r * w ^ 2 ^ s)) * h2
    · linear_combination (-(w ^ 2 ^ s)) * hdet + w * e01 + q * e11 + (-(w * q * r ^ 2 ^ s)) * h2
  · intro h
    have h' := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F)) h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hgm] at h'
    have e00 := congrFun (congrFun h' 0) 0
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    have e11 := congrFun (congrFun h' 1) 1
    simp [burnsideK312_sg_apply] at e00 e01 e10 e11
    rw [hgm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow, e00, e01, e10, e11]
    all_goals first
      | linear_combination hdet
      | linear_combination (q * p) * h2
      | linear_combination (w * r) * h2

theorem burnsideK312_Geo_line_mapsto (c : OrthogonalFourCoordinates L s F) {g : SL(2, F)}
    (hg : Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g = g) {v : V}
    (hv : v ∈ burnsideK312_Geo_line c) :
    burnsideK312_actHom c g v ∈ burnsideK312_Geo_line c := by
  obtain ⟨κ, hκ, hM⟩ := hv
  refine ⟨κ, hκ, ?_⟩
  rw [burnsideK312_matrix_act, hM]
  have := (burnsideK312_Geo_starJ g).mpr hg
  rw [Matrix.mul_smul, Matrix.smul_mul, this]

theorem burnsideK312_Geo_stab (c : OrthogonalFourCoordinates L s F) :
    ∀ x ∈ L, x ∈ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ↔
      ∀ v : V, v ∈ commV (Subgroup.zpowers (burnsideK312_sh c)) ↔
        x v ∈ commV (Subgroup.zpowers (burnsideK312_sh c)) := by
  intro x hx
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [burnsideK312_Geo_commV]
  obtain ⟨g, rfl⟩ := burnsideK312_exists_actHom c hx
  constructor
  · intro hC
    have hσg : Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g = g := by
      obtain ⟨g', hg', hxg'⟩ := (burnsideK312_Geo_mem_centralizer c _).mp ⟨hx, hC⟩
      have e := burnsideK312_actHom_injective c hxg'
      rw [e]
      exact hg'
    intro v
    refine ⟨burnsideK312_Geo_line_mapsto c hσg, fun hv => ?_⟩
    have hσg' : Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g⁻¹ = g⁻¹ := by
      rw [map_inv, hσg]
    have := burnsideK312_Geo_line_mapsto c hσg' hv
    simpa [map_inv] using this
  · intro h
    have hJ : burnsideK312_Geo_Jv c ∈ burnsideK312_Geo_line c :=
      ⟨1, by simp, by rw [burnsideK312_Geo_matrix_Jv, one_smul]⟩
    obtain ⟨κ, hκ, hM⟩ := (h _).mp hJ
    rw [burnsideK312_matrix_act, burnsideK312_Geo_matrix_Jv] at hM
    have hdet := congrArg Matrix.det hM
    have hd2 : ((g : Matrix (Fin 2) (Fin 2) F) * !![(0 : F), 1; 1, 0] *
        (frobPow s (g : Matrix (Fin 2) (Fin 2) F))ᵀ).det = (!![(0 : F), 1; 1, 0]).det :=
      burnsideK312_det_twAct g _
    rw [hd2, Matrix.det_smul] at hdet
    simp [Matrix.det_fin_two] at hdet
    have hκ2 : κ * κ = 1 := by
      have : κ ^ 2 = 1 := hdet.symm
      linear_combination this
    have hκ1 : κ = 1 := by
      have h0 : (κ - 1) ^ 2 = 0 := by linear_combination hκ2 + (1 - κ) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
    rw [hκ1, one_smul] at hM
    exact (burnsideK312_Geo_mem_centralizer c _).mpr
      ⟨g, (burnsideK312_Geo_starJ g).mp hM, rfl⟩ |>.2

@[expose] noncomputable def burnsideK312_Geo_incl :
    SL(2, ↥(burnsideK312_K F s)) →* SL(2, F) :=
  Matrix.SpecialLinearGroup.map (burnsideK312_K F s).subtype

theorem burnsideK312_Geo_incl_coe (g : SL(2, ↥(burnsideK312_K F s))) (i j : Fin 2) :
    ((burnsideK312_Geo_incl g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
      ((g : Matrix (Fin 2) (Fin 2) ↥(burnsideK312_K F s)) i j : F) := by
  unfold burnsideK312_Geo_incl
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

theorem burnsideK312_Geo_incl_injective :
    Function.Injective (burnsideK312_Geo_incl (F := F) (s := s)) := by
  intro g g' h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply Subtype.val_injective
  have := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) i j) h
  simpa [burnsideK312_Geo_incl_coe] using this

theorem burnsideK312_Geo_incl_fixed (g : SL(2, ↥(burnsideK312_K F s))) :
    Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) (burnsideK312_Geo_incl g) =
      burnsideK312_Geo_incl g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    burnsideK312_Geo_incl_coe, burnsideK312_sg_apply]
  exact burnsideK312_mem_K.mp (g i j).2

theorem burnsideK312_Geo_exists_incl {g' : SL(2, F)}
    (hg : Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g' = g') :
    ∃ g : SL(2, ↥(burnsideK312_K F s)), burnsideK312_Geo_incl g = g' := by
  have hent : ∀ i j, ((g' : Matrix (Fin 2) (Fin 2) F) i j) ^ 2 ^ s =
      (g' : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) i j) hg
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      burnsideK312_sg_apply] using this
  let M : Matrix (Fin 2) (Fin 2) ↥(burnsideK312_K F s) :=
    Matrix.of fun i j => ⟨(g' : Matrix (Fin 2) (Fin 2) F) i j, burnsideK312_mem_K.mpr (hent i j)⟩
  have hMg : (burnsideK312_K F s).subtype.mapMatrix M = (g' : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    apply Subtype.val_injective
    have h1 : (burnsideK312_K F s).subtype M.det =
        ((burnsideK312_K F s).subtype.mapMatrix M).det := RingHom.map_det _ _
    rw [hMg, g'.2] at h1
    exact h1
  obtain ⟨g, hg0⟩ : ∃ g : SL(2, ↥(burnsideK312_K F s)),
      (g : Matrix (Fin 2) (Fin 2) ↥(burnsideK312_K F s)) = M := ⟨⟨M, hdet⟩, rfl⟩
  refine ⟨g, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [burnsideK312_Geo_incl_coe, hg0]
  rfl

theorem burnsideK312_Geo_viii (c : OrthogonalFourCoordinates L s F) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (field_embedding : K →+* F),
      Nat.card K = 2 ^ s ∧ Function.Injective field_embedding ∧
      (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar ↔
        ∃ baseScalar : K, field_embedding baseScalar = scalar) ∧
      Nonempty (↥(L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V))) ≃*
        ↥(StatedSL 2 K)) := by
  have hF := c.field_card
  refine ⟨↥(burnsideK312_K F s), inferInstance, inferInstance, (burnsideK312_K F s).subtype,
    burnsideK312_card_K (burnsideK312_one_le hF) hF, Subtype.val_injective, ?_, ?_⟩
  · intro scalar
    constructor
    · intro h
      exact ⟨⟨scalar, burnsideK312_mem_K.mpr h⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact burnsideK312_mem_K.mp b.2
  · let ψ : SL(2, ↥(burnsideK312_K F s)) →*
        ↥(L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V))) :=
      ((burnsideK312_actHom c).comp burnsideK312_Geo_incl).codRestrict _ (fun g =>
        (burnsideK312_Geo_mem_centralizer c _).mpr
          ⟨burnsideK312_Geo_incl g, burnsideK312_Geo_incl_fixed g, rfl⟩)
    have hinj : Function.Injective ψ := by
      intro g g' h
      apply burnsideK312_Geo_incl_injective
      have e : ∀ g, ((ψ g : ↥(L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)))) :
          MulAut V) = burnsideK312_actHom c (burnsideK312_Geo_incl g) := fun g => rfl
      have h' : ((ψ g : ↥(L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)))) :
          MulAut V) = ((ψ g' : ↥(L ⊓ Subgroup.centralizer ({burnsideK312_sh c} :
            Set (MulAut V)))) : MulAut V) := by rw [h]
      rw [e, e] at h'
      exact burnsideK312_actHom_injective c h'
    have hsurj : Function.Surjective ψ := by
      rintro ⟨x, hx⟩
      obtain ⟨g', hg', rfl⟩ := (burnsideK312_Geo_mem_centralizer c x).mp hx
      obtain ⟨g, rfl⟩ := burnsideK312_Geo_exists_incl hg'
      exact ⟨g, rfl⟩
    exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 ↥(burnsideK312_K F s))⟩

theorem burnsideK312_Geo_perp_char (c : OrthogonalFourCoordinates L s F) (v : V) :
    v ∈ fixV (Subgroup.zpowers (burnsideK312_sh c)) ↔
      ∀ point ∈ commV (Subgroup.zpowers (burnsideK312_sh c)), c.polar v point = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [burnsideK312_Geo_fix, burnsideK312_Geo_commV]
  constructor
  · intro h point hp
    obtain ⟨κ, hκ, hpM⟩ := hp
    have hsym := congrFun (congrFun h 0) 1
    simp only [Matrix.transpose_apply] at hsym
    unfold OrthogonalFourCoordinates.polar
    rw [burnsideK312_Geo_pol, hpM]
    simp
    linear_combination (-(κ * c.matrix v 0 1)) * h2 + (-κ) * hsym
  · intro h
    have hJ : burnsideK312_Geo_Jv c ∈ burnsideK312_Geo_line c :=
      ⟨1, by simp, by rw [burnsideK312_Geo_matrix_Jv, one_smul]⟩
    have h0 := h _ hJ
    unfold OrthogonalFourCoordinates.polar at h0
    rw [burnsideK312_Geo_pol, burnsideK312_Geo_matrix_Jv] at h0
    simp at h0
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (-1 : F) * h0 + (-(c.matrix v 0 1)) * h2
    · linear_combination h0 + (c.matrix v 0 1) * h2

theorem burnsideK312_Geo_sq_inj {x y : F} (h : x ^ 2 = y ^ 2) : x = y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h0 : (x - y) ^ 2 = 0 := by linear_combination h + (y * (y - x)) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)

theorem burnsideK312_Geo_exists_sqrt (a : F) : ∃ y : F, y ^ 2 = a := by
  have : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two this a
  exact ⟨r, by rw [hr]; ring⟩

theorem burnsideK312_Geo_iso_matrix (_hF : Nat.card F = 2 ^ (2 * s))
    {a1 b1 c1 a3 b3 c3 : F}
    (ha1 : a1 ^ 2 ^ s = a1) (hc1 : c1 ^ 2 ^ s = c1) (ha3 : a3 ^ 2 ^ s = a3)
    (hc3 : c3 ^ 2 ^ s = c3)
    (hd1 : a1 * c1 = b1 ^ 2) (hd3 : a3 * c3 = b3 ^ 2) (hp : a1 * c3 + a3 * c1 = 1) :
    ∃ g : SL(2, F), Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g = g ∧
      (g : Matrix (Fin 2) (Fin 2) F) * !![(1 : F), 0; 0, 0] *
          (frobPow s (g : Matrix (Fin 2) (Fin 2) F))ᵀ = !![a1, b1; b1, c1] ∧
      (g : Matrix (Fin 2) (Fin 2) F) * !![(0 : F), 0; 0, 1] *
          (frobPow s (g : Matrix (Fin 2) (Fin 2) F))ᵀ = !![a3, b3; b3, c3] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨x1, hx1⟩ := burnsideK312_Geo_exists_sqrt a1
  obtain ⟨z1, hz1⟩ := burnsideK312_Geo_exists_sqrt c1
  obtain ⟨x3, hx3⟩ := burnsideK312_Geo_exists_sqrt a3
  obtain ⟨z3, hz3⟩ := burnsideK312_Geo_exists_sqrt c3
  have hfix : ∀ x a : F, x ^ 2 = a → a ^ 2 ^ s = a → x ^ 2 ^ s = x := by
    intro x a hx ha
    apply burnsideK312_Geo_sq_inj
    calc (x ^ 2 ^ s) ^ 2 = (x ^ 2) ^ 2 ^ s := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = a ^ 2 ^ s := by rw [hx]
      _ = a := ha
      _ = x ^ 2 := hx.symm
  have hx1f := hfix x1 a1 hx1 ha1
  have hz1f := hfix z1 c1 hz1 hc1
  have hx3f := hfix x3 a3 hx3 ha3
  have hz3f := hfix z3 c3 hz3 hc3
  have hb1 : b1 = x1 * z1 := by
    apply burnsideK312_Geo_sq_inj
    rw [mul_pow, hx1, hz1, ← hd1]
  have hb3 : b3 = x3 * z3 := by
    apply burnsideK312_Geo_sq_inj
    rw [mul_pow, hx3, hz3, ← hd3]
  have hdet : x1 * z3 + x3 * z1 = 1 := by
    apply burnsideK312_Geo_sq_inj
    have : (x1 * z3 + x3 * z1) ^ 2 = x1 ^ 2 * z3 ^ 2 + x3 ^ 2 * z1 ^ 2 := by
      linear_combination (x1 * z3 * x3 * z1) * h2
    rw [this, hx1, hz3, hx3, hz1, hp]
    ring
  obtain ⟨g, hg⟩ : ∃ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) = !![x1, x3; z1, z3] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]; linear_combination hdet + (-(x3 * z1)) * h2⟩, rfl⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hg]
    fin_cases i <;> fin_cases j <;> simp [burnsideK312_sg_apply, hx1f, hz1f, hx3f, hz3f]
  · rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow, hx1f, hz1f, hx3f, hz3f, hb1]
    all_goals first
      | ring1
      | linear_combination hx1
      | linear_combination hz1
      | linear_combination (-1 : F) * hx1
      | linear_combination (-1 : F) * hz1
  · rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow, hx1f, hz1f, hx3f, hz3f, hb3]
    all_goals first
      | ring1
      | linear_combination hx3
      | linear_combination hz3
      | linear_combination (-1 : F) * hx3
      | linear_combination (-1 : F) * hz3

theorem burnsideK312_Geo_perp_sym (c : OrthogonalFourCoordinates L s F) {v : V}
    (hv : v ∈ fixV (Subgroup.zpowers (burnsideK312_sh c))) :
    c.matrix v 1 0 = c.matrix v 0 1 := by
  have := (burnsideK312_Geo_fix c v).mp hv
  have h := congrFun (congrFun this 0) 1
  simpa using h

theorem burnsideK312_Geo_perp_K01 (c : OrthogonalFourCoordinates L s F) {v : V}
    (hv : v ∈ fixV (Subgroup.zpowers (burnsideK312_sh c))) :
    (c.matrix v 0 1) ^ 2 ^ s = c.matrix v 0 1 := by
  have h1 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0
  rw [← h1]
  exact burnsideK312_Geo_perp_sym c hv

theorem burnsideK312_Geo_mk_mem (c : OrthogonalFourCoordinates L s F) (a b d : F)
    (ha : a ^ 2 ^ s = a) (hb : b ^ 2 ^ s = b) (hd : d ^ 2 ^ s = d) :
    burnsideK312_Geo_mk c a b d ha hd ∈ fixV (Subgroup.zpowers (burnsideK312_sh c)) := by
  rw [burnsideK312_Geo_fix, burnsideK312_Geo_matrix_mk, hb]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideK312_Geo_matrix_mk' (c : OrthogonalFourCoordinates L s F) (a b d : F)
    (ha : a ^ 2 ^ s = a) (hb : b ^ 2 ^ s = b) (hd : d ^ 2 ^ s = d) :
    c.matrix (burnsideK312_Geo_mk c a b d ha hd) = !![a, b; b, d] := by
  rw [burnsideK312_Geo_matrix_mk, hb]

theorem burnsideK312_Geo_card_perp (c : OrthogonalFourCoordinates L s F) :
    Nat.card ↥(fixV (Subgroup.zpowers (burnsideK312_sh c))) = 2 ^ (3 * s) := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  let e : ↥(fixV (Subgroup.zpowers (burnsideK312_sh c))) ≃
      ↥(burnsideK312_K F s) × ↥(burnsideK312_K F s) × ↥(burnsideK312_K F s) :=
    { toFun := fun v =>
        (⟨c.matrix v.1 0 0, burnsideK312_mem_K.mpr
          (burnsideK312_herm_apply (burnsideK312_matrix_herm c v.1) 0 0).symm⟩,
         ⟨c.matrix v.1 0 1, burnsideK312_mem_K.mpr (burnsideK312_Geo_perp_K01 c v.2)⟩,
         ⟨c.matrix v.1 1 1, burnsideK312_mem_K.mpr
          (burnsideK312_herm_apply (burnsideK312_matrix_herm c v.1) 1 1).symm⟩)
      invFun := fun t =>
        ⟨burnsideK312_Geo_mk c t.1.1 t.2.1.1 t.2.2.1 (burnsideK312_mem_K.mp t.1.2)
          (burnsideK312_mem_K.mp t.2.2.2),
         burnsideK312_Geo_mk_mem c _ _ _ _ (burnsideK312_mem_K.mp t.2.1.2) _⟩
      left_inv := fun v => by
        apply Subtype.ext
        apply burnsideK312_matrix_injective c
        rw [burnsideK312_Geo_matrix_mk' c _ _ _ _ (burnsideK312_Geo_perp_K01 c v.2)]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [burnsideK312_Geo_perp_sym c v.2]
      right_inv := fun t => by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨d, hd⟩⟩ := t
        simp only [Prod.mk.injEq]
        refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
        · simp only
          rw [burnsideK312_Geo_matrix_mk' c _ _ _ _ (burnsideK312_mem_K.mp hb)]
          rfl
        · simp only
          rw [burnsideK312_Geo_matrix_mk' c _ _ _ _ (burnsideK312_mem_K.mp hb)]
          rfl
        · simp only
          rw [burnsideK312_Geo_matrix_mk' c _ _ _ _ (burnsideK312_mem_K.mp hb)]
          rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, burnsideK312_card_K hs hF]
  ring

theorem burnsideK312_Geo_perp_stable (c : OrthogonalFourCoordinates L s F) {x : MulAut V}
    (hx : x ∈ L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V))) :
    ∀ v ∈ fixV (Subgroup.zpowers (burnsideK312_sh c)),
      x v ∈ fixV (Subgroup.zpowers (burnsideK312_sh c)) ∧
        (c.matrix (x v)).det = (c.matrix v).det := by
  intro v hv
  refine ⟨?_, ?_⟩
  · have hsh : burnsideK312_sh c * x = x * burnsideK312_sh c :=
      Subgroup.mem_centralizer_iff.mp hx.2 _ (Set.mem_singleton _)
    have hv' : burnsideK312_sh c v = v := by
      have h1 := (burnsideK312_Geo_fix c v).mp hv
      apply burnsideK312_matrix_injective c
      rw [burnsideK312_matrix_sh]
      exact h1
    rw [burnsideK312_Geo_fix]
    have h2 : burnsideK312_sh c (x v) = x v := by
      have := congrArg (fun m : MulAut V => m v) hsh
      simp only [MulAut.mul_apply] at this
      rw [this, hv']
    have h3 := congrArg c.matrix h2
    rwa [burnsideK312_matrix_sh] at h3
  · obtain ⟨g, -, rfl⟩ := (burnsideK312_Geo_mem_centralizer c x).mp hx
    rw [burnsideK312_matrix_act]
    exact burnsideK312_det_twAct g _

theorem burnsideK312_Geo_perp_faithful (c : OrthogonalFourCoordinates L s F) {x : MulAut V}
    (hx : x ∈ L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)))
    (h : ∀ v ∈ fixV (Subgroup.zpowers (burnsideK312_sh c)), x v = v) : x = 1 := by
  obtain ⟨g, -, rfl⟩ := (burnsideK312_Geo_mem_centralizer c x).mp hx
  have key : ∀ M : Matrix (Fin 2) (Fin 2) F, burnsideK312_Herm F s M → Mᵀ = M →
      (g : Matrix (Fin 2) (Fin 2) F) * M * (frobPow s (g : Matrix (Fin 2) (Fin 2) F))ᵀ = M := by
    intro M hM hMt
    obtain ⟨v, hv⟩ := burnsideK312_exists_vec c hM
    have hvP : v ∈ fixV (Subgroup.zpowers (burnsideK312_sh c)) :=
      (burnsideK312_Geo_fix c v).mpr (by rw [hv]; exact hMt)
    have h1 := congrArg c.matrix (h v hvP)
    rw [burnsideK312_matrix_act, hv] at h1
    exact h1
  have hg1 : (g : Matrix (Fin 2) (Fin 2) F) = 1 :=
    burnsideK312_triv_of_fix3 _ g.2
      (key _ burnsideK312_herm_E11 (by ext i j; fin_cases i <;> fin_cases j <;> simp))
      (key _ burnsideK312_herm_E22 (by ext i j; fin_cases i <;> fin_cases j <;> simp))
      (key _ burnsideK312_herm_J (by ext i j; fin_cases i <;> fin_cases j <;> simp))
  have hg2 : g = 1 := Subtype.ext hg1
  rw [hg2, map_one]

theorem burnsideK312_Geo_perp_iso (c : OrthogonalFourCoordinates L s F) {P : Subgroup V}
    (hP : P = fixV (Subgroup.zpowers (burnsideK312_sh c))) (ι : MulAut ↥P)
    (hdet : ∀ vector : ↥P, (c.matrix (ι vector : V)).det = (c.matrix (vector : V)).det)
    (hK : ∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
      ∀ first second : ↥P, c.matrix (second : V) = scalar • c.matrix (first : V) →
        c.matrix (ι second : V) = scalar • c.matrix (ι first : V)) :
    ∃ groupElement ∈ L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)),
      ∀ vector : ↥P, groupElement (vector : V) = (ι vector : V) := by
  classical
  have hF := c.field_card
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hmem : ∀ v : V, v ∈ P ↔ (c.matrix v)ᵀ = c.matrix v := fun v => by
    rw [hP]; exact burnsideK312_Geo_fix c v
  have hsy : ∀ v : ↥P, c.matrix (v : V) 1 0 = c.matrix (v : V) 0 1 := fun v => by
    have := (hmem v).mp v.2
    have h := congrFun (congrFun this 0) 1
    simpa using h
  have hmulι : ∀ x y : ↥P, c.matrix (ι (x * y) : V) =
      c.matrix (ι x : V) + c.matrix (ι y : V) := by
    intro x y
    rw [map_mul]
    exact burnsideK312_matrix_mul c _ _
  have hmul : ∀ x y : ↥P, c.matrix ((x * y : ↥P) : V) = c.matrix (x : V) + c.matrix (y : V) :=
    fun x y => burnsideK312_matrix_mul c _ _
  have hpol : ∀ x y : ↥P, (c.matrix (ι x : V) + c.matrix (ι y : V)).det -
      (c.matrix (ι x : V)).det - (c.matrix (ι y : V)).det =
      (c.matrix (x : V) + c.matrix (y : V)).det - (c.matrix (x : V)).det -
        (c.matrix (y : V)).det := by
    intro x y
    rw [← hmulι x y, hdet (x * y), hdet x, hdet y, hmul x y]
  obtain ⟨v1, hv1⟩ := burnsideK312_exists_vec c (burnsideK312_herm_E11 (F := F) (s := s))
  obtain ⟨v2, hv2⟩ := burnsideK312_exists_vec c (burnsideK312_herm_J (F := F) (s := s))
  obtain ⟨v3, hv3⟩ := burnsideK312_exists_vec c (burnsideK312_herm_E22 (F := F) (s := s))
  have hP1 : v1 ∈ P := (hmem v1).mpr
    (by rw [hv1]; ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hP2 : v2 ∈ P := (hmem v2).mpr
    (by rw [hv2]; ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hP3 : v3 ∈ P := (hmem v3).mpr
    (by rw [hv3]; ext i j; fin_cases i <;> fin_cases j <;> simp)
  let e1 : ↥P := ⟨v1, hP1⟩
  let e2 : ↥P := ⟨v2, hP2⟩
  let e3 : ↥P := ⟨v3, hP3⟩
  have hm1 : c.matrix (e1 : V) = !![(1 : F), 0; 0, 0] := hv1
  have hm2 : c.matrix (e2 : V) = !![(0 : F), 1; 1, 0] := hv2
  have hm3 : c.matrix (e3 : V) = !![(0 : F), 0; 0, 1] := hv3
  have hrad : ∀ z : ↥P, (c.matrix (ι e2 : V) + c.matrix (z : V)).det -
      (c.matrix (ι e2 : V)).det - (c.matrix (z : V)).det = 0 := by
    intro z
    obtain ⟨w, rfl⟩ := ι.surjective z
    rw [hpol e2 w, hm2, burnsideK312_Geo_pol, hsy w]
    simp
    linear_combination (-(c.matrix (w : V) 0 1)) * h2
  have hX11 : c.matrix (ι e2 : V) 1 1 = 0 := by
    have h := hrad e1
    rw [burnsideK312_Geo_pol, hm1] at h
    simpa using h
  have hX00 : c.matrix (ι e2 : V) 0 0 = 0 := by
    have h := hrad e3
    rw [burnsideK312_Geo_pol, hm3] at h
    simpa using h
  have hι2 : ι e2 = e2 := by
    apply Subtype.ext
    apply burnsideK312_matrix_injective c
    show c.matrix (ι e2 : V) = c.matrix (e2 : V)
    have hd := hdet e2
    rw [hm2, Matrix.det_fin_two, Matrix.det_fin_two] at hd
    rw [hsy (ι e2), hX00, hX11] at hd
    simp at hd
    have hb : c.matrix (ι e2 : V) 0 1 = 1 := by
      have h0 : (c.matrix (ι e2 : V) 0 1 - 1) ^ 2 = 0 := by
        linear_combination hd + (1 - c.matrix (ι e2 : V) 0 1) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
    rw [hm2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hX00, hX11, hb, hsy (ι e2)]
  have hS1 := hsy (ι e1)
  have hS3 := hsy (ι e3)
  have ha1 : (c.matrix (ι e1 : V) 0 0) ^ 2 ^ s = c.matrix (ι e1 : V) 0 0 :=
    (burnsideK312_herm_apply (burnsideK312_matrix_herm c _) 0 0).symm
  have hc1 : (c.matrix (ι e1 : V) 1 1) ^ 2 ^ s = c.matrix (ι e1 : V) 1 1 :=
    (burnsideK312_herm_apply (burnsideK312_matrix_herm c _) 1 1).symm
  have ha3 : (c.matrix (ι e3 : V) 0 0) ^ 2 ^ s = c.matrix (ι e3 : V) 0 0 :=
    (burnsideK312_herm_apply (burnsideK312_matrix_herm c _) 0 0).symm
  have hc3 : (c.matrix (ι e3 : V) 1 1) ^ 2 ^ s = c.matrix (ι e3 : V) 1 1 :=
    (burnsideK312_herm_apply (burnsideK312_matrix_herm c _) 1 1).symm
  have hd1 : c.matrix (ι e1 : V) 0 0 * c.matrix (ι e1 : V) 1 1 = (c.matrix (ι e1 : V) 0 1) ^ 2 := by
    have h := hdet e1
    rw [hm1, Matrix.det_fin_two, Matrix.det_fin_two, hS1] at h
    simp at h
    linear_combination h
  have hd3 : c.matrix (ι e3 : V) 0 0 * c.matrix (ι e3 : V) 1 1 = (c.matrix (ι e3 : V) 0 1) ^ 2 := by
    have h := hdet e3
    rw [hm3, Matrix.det_fin_two, Matrix.det_fin_two, hS3] at h
    simp at h
    linear_combination h
  have hp : c.matrix (ι e1 : V) 0 0 * c.matrix (ι e3 : V) 1 1 +
      c.matrix (ι e3 : V) 0 0 * c.matrix (ι e1 : V) 1 1 = 1 := by
    have h := hpol e1 e3
    rw [burnsideK312_Geo_pol, burnsideK312_Geo_pol, hm1, hm3, hS1, hS3] at h
    simp at h
    linear_combination h + (c.matrix (ι e1 : V) 0 1 * c.matrix (ι e3 : V) 0 1) * h2
  obtain ⟨g, hσg, hg1, hg3⟩ := burnsideK312_Geo_iso_matrix hF ha1 hc1 ha3 hc3 hd1 hd3 hp
  have hX1m : c.matrix (ι e1 : V) = !![c.matrix (ι e1 : V) 0 0, c.matrix (ι e1 : V) 0 1;
      c.matrix (ι e1 : V) 0 1, c.matrix (ι e1 : V) 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS1]
  have hX3m : c.matrix (ι e3 : V) = !![c.matrix (ι e3 : V) 0 0, c.matrix (ι e3 : V) 0 1;
      c.matrix (ι e3 : V) 0 1, c.matrix (ι e3 : V) 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS3]
  rw [← hX1m] at hg1
  rw [← hX3m] at hg3
  have hgJ := (burnsideK312_Geo_starJ g).mpr hσg
  refine ⟨burnsideK312_actHom c g,
    (burnsideK312_Geo_mem_centralizer c _).mpr ⟨g, hσg, rfl⟩, fun v => ?_⟩
  apply burnsideK312_matrix_injective c
  rw [burnsideK312_matrix_act]
  have hvf : ∀ w : ↥P, (w : V) ∈ fixV (Subgroup.zpowers (burnsideK312_sh c)) := fun w => hP ▸ w.2
  have hz : (0 : F) ^ 2 ^ s = 0 := by simp
  have hα : (c.matrix (v : V) 0 0) ^ 2 ^ s = c.matrix (v : V) 0 0 :=
    (burnsideK312_herm_apply (burnsideK312_matrix_herm c _) 0 0).symm
  have hδ : (c.matrix (v : V) 1 1) ^ 2 ^ s = c.matrix (v : V) 1 1 :=
    (burnsideK312_herm_apply (burnsideK312_matrix_herm c _) 1 1).symm
  have hβ : (c.matrix (v : V) 0 1) ^ 2 ^ s = c.matrix (v : V) 0 1 :=
    burnsideK312_Geo_perp_K01 c (hvf v)
  have hmk : ∀ (a b d : F) (ha : a ^ 2 ^ s = a) (hb : b ^ 2 ^ s = b) (hd : d ^ 2 ^ s = d),
      burnsideK312_Geo_mk c a b d ha hd ∈ P := fun a b d ha hb hd => by
    rw [hP]
    exact burnsideK312_Geo_mk_mem c a b d ha hb hd
  obtain ⟨w1, hw1m⟩ : ∃ w : ↥P, c.matrix (w : V) =
      c.matrix (v : V) 0 0 • !![(1 : F), 0; 0, 0] :=
    ⟨⟨burnsideK312_Geo_mk c _ 0 0 hα hz, hmk _ _ _ hα hz hz⟩, by
      show c.matrix (burnsideK312_Geo_mk c _ 0 0 hα hz) = _
      rw [burnsideK312_Geo_matrix_mk' c _ _ _ hα hz hz]
      ext i j
      fin_cases i <;> fin_cases j <;> simp⟩
  obtain ⟨w2, hw2m⟩ : ∃ w : ↥P, c.matrix (w : V) =
      c.matrix (v : V) 0 1 • !![(0 : F), 1; 1, 0] :=
    ⟨⟨burnsideK312_Geo_mk c 0 _ 0 hz hz, hmk _ _ _ hz hβ hz⟩, by
      show c.matrix (burnsideK312_Geo_mk c 0 _ 0 hz hz) = _
      rw [burnsideK312_Geo_matrix_mk' c _ _ _ hz hβ hz]
      ext i j
      fin_cases i <;> fin_cases j <;> simp⟩
  obtain ⟨w3, hw3m⟩ : ∃ w : ↥P, c.matrix (w : V) =
      c.matrix (v : V) 1 1 • !![(0 : F), 0; 0, 1] :=
    ⟨⟨burnsideK312_Geo_mk c 0 0 _ hz hδ, hmk _ _ _ hz hz hδ⟩, by
      show c.matrix (burnsideK312_Geo_mk c 0 0 _ hz hδ) = _
      rw [burnsideK312_Geo_matrix_mk' c _ _ _ hz hz hδ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp⟩
  have hw1 : c.matrix (w1 : V) = c.matrix (v : V) 0 0 • c.matrix (e1 : V) := by rw [hw1m, hm1]
  have hw2 : c.matrix (w2 : V) = c.matrix (v : V) 0 1 • c.matrix (e2 : V) := by rw [hw2m, hm2]
  have hw3 : c.matrix (w3 : V) = c.matrix (v : V) 1 1 • c.matrix (e3 : V) := by rw [hw3m, hm3]
  have hv : v = w1 * w2 * w3 := by
    apply Subtype.ext
    apply burnsideK312_matrix_injective c
    show c.matrix (v : V) = c.matrix ((w1 * w2 * w3 : ↥P) : V)
    rw [hmul, hmul, hw1m, hw2m, hw3m]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsy v]
  have hιv : c.matrix (ι v : V) = c.matrix (v : V) 0 0 • c.matrix (ι e1 : V) +
      c.matrix (v : V) 0 1 • c.matrix (e2 : V) + c.matrix (v : V) 1 1 • c.matrix (ι e3 : V) := by
    have h1 := hK _ hα e1 w1 hw1
    have h2' := hK _ hβ e2 w2 hw2
    have h3 := hK _ hδ e3 w3 hw3
    rw [hι2] at h2'
    have hιmul : c.matrix (ι v : V) = c.matrix (ι w1 : V) + c.matrix (ι w2 : V) +
        c.matrix (ι w3 : V) := by
      conv_lhs => rw [hv]
      rw [map_mul, map_mul, hmul, hmul]
    rw [hιmul, h1, h2', h3]
  have hMdec : c.matrix (v : V) = c.matrix (v : V) 0 0 • !![(1 : F), 0; 0, 0] +
      c.matrix (v : V) 0 1 • !![(0 : F), 1; 1, 0] + c.matrix (v : V) 1 1 • !![(0 : F), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsy v]
  rw [hιv]
  conv_lhs => rw [hMdec]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hg1, hg3, hgJ, hm2]

theorem burnsideK312_Geo_card_V (c : OrthogonalFourCoordinates L s F) :
    Nat.card V = 2 ^ (4 * s) := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  let e : V ≃ ↥(burnsideK312_K F s) × F × ↥(burnsideK312_K F s) :=
    { toFun := fun v =>
        (⟨c.matrix v 0 0, burnsideK312_mem_K.mpr
          (burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 0 0).symm⟩,
         c.matrix v 0 1,
         ⟨c.matrix v 1 1, burnsideK312_mem_K.mpr
          (burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 1).symm⟩)
      invFun := fun t => burnsideK312_Geo_mk c t.1.1 t.2.1 t.2.2.1 (burnsideK312_mem_K.mp t.1.2)
          (burnsideK312_mem_K.mp t.2.2.2)
      left_inv := fun v => by
        apply burnsideK312_matrix_injective c
        rw [burnsideK312_Geo_matrix_mk]
        have h10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h10]
      right_inv := fun t => by
        obtain ⟨⟨a, ha⟩, b, ⟨d, hd⟩⟩ := t
        have ha' := burnsideK312_mem_K.mp ha
        have hd' := burnsideK312_mem_K.mp hd
        refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ (Subtype.ext ?_))
        · show c.matrix (burnsideK312_Geo_mk c a b d ha' hd') 0 0 = a
          rw [burnsideK312_Geo_matrix_mk]
          rfl
        · show c.matrix (burnsideK312_Geo_mk c a b d ha' hd') 0 1 = b
          rw [burnsideK312_Geo_matrix_mk]
          rfl
        · show c.matrix (burnsideK312_Geo_mk c a b d ha' hd') 1 1 = d
          rw [burnsideK312_Geo_matrix_mk]
          rfl }
  have hcard : Nat.card F = 2 ^ (2 * s) := hF
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, burnsideK312_card_K hs hF, hcard]
  ring

theorem burnsideK312_TConj_sh (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_TConj c (burnsideK312_sh c) := by
  refine ⟨?_, ?_,
    ⟨burnsideK312_Geo_Jv c, burnsideK312_Geo_Jv_ne c, burnsideK312_Geo_det_Jv c,
      fun v => burnsideK312_Geo_reflection c v⟩,
    burnsideK312_Geo_isPoint c, burnsideK312_Geo_nonsingular c, burnsideK312_Geo_stab c,
    burnsideK312_Geo_viii c, ?_⟩
  · intro v
    rw [burnsideK312_matrix_sh, Matrix.det_transpose]
  · intro scalar _ first second h
    rw [burnsideK312_matrix_sh, burnsideK312_matrix_sh, h, Matrix.transpose_smul]
  · refine ⟨fixV (Subgroup.zpowers (burnsideK312_sh c)), burnsideK312_Geo_perp_char c, ?_,
      burnsideK312_Geo_card_perp c, ?_, ?_, ?_⟩
    · intro scalar _ vector hv scalarVector hsv
      rw [burnsideK312_Geo_fix] at hv ⊢
      rw [hsv, Matrix.transpose_smul, hv]
    · intro x hx v hv
      exact burnsideK312_Geo_perp_stable c hx v hv
    · intro x hx h
      exact burnsideK312_Geo_perp_faithful c hx h
    · intro ι hdet hK
      exact burnsideK312_Geo_perp_iso c rfl ι hdet hK

end Geo


section RU

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_RU_sq (c : OrthogonalFourCoordinates L s F) (v : V) : v ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply burnsideK312_matrix_injective c
  rw [pow_two, burnsideK312_matrix_mul, burnsideK312_matrix_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  linear_combination (c.matrix v i j) * h2

theorem burnsideK312_RU_hV (c : OrthogonalFourCoordinates L s F) : ∀ v : V, v ^ 2 = 1 :=
  burnsideK312_RU_sq c

theorem burnsideK312_RU_card_pow (c : OrthogonalFourCoordinates L s F) (H : Subgroup V) :
    Nat.card H = 2 ^ rk H :=
  card_eq_two_pow (burnsideK312_RU_hV c) H

theorem burnsideK312_RU_rk_of_card {W : Type*} [Group W] {m : ℕ} (h : Nat.card W = 2 ^ m) :
    rk W = m := by
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem burnsideK312_RU_rk_le (c : OrthogonalFourCoordinates L s F) {H : Subgroup V} {m : ℕ}
    (h : Nat.card H ≤ 2 ^ m) : rk H ≤ m := by
  rw [burnsideK312_RU_card_pow c H] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem burnsideK312_RU_le_rk (c : OrthogonalFourCoordinates L s F) {H : Subgroup V} {m : ℕ}
    (h : 2 ^ m ≤ Nat.card H) : m ≤ rk H := by
  rw [burnsideK312_RU_card_pow c H] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem burnsideK312_RU_rkIdx (c : OrthogonalFourCoordinates L s F) (A : Subgroup (MulAut V)) :
    rkIdx (fixV A) = 4 * s - rk (fixV A) := by
  have h := rk_add_rkIdx (fixV A)
  have hV : rk V = 4 * s := burnsideK312_RU_rk_of_card (burnsideK312_Geo_card_V c)
  omega

theorem burnsideK312_RU_rk_fix_le (c : OrthogonalFourCoordinates L s F) (A : Subgroup (MulAut V)) :
    rk (fixV A) ≤ 4 * s := by
  have h := rk_add_rkIdx (fixV A)
  have hV : rk V = 4 * s := burnsideK312_RU_rk_of_card (burnsideK312_Geo_card_V c)
  omega

theorem burnsideK312_RU_rAV_ge {A : Subgroup (MulAut V)} {p q : ℕ}
    (hp : p ≤ rkIdx (fixV A)) (hq : rk A ≤ q) (hA : 0 < rk A) :
    (p : ℚ) / q ≤ rAV A := by
  unfold rAV
  have hA' : (0 : ℚ) < rk A := by exact_mod_cast hA
  have hq' : (rk A : ℚ) ≤ q := by exact_mod_cast hq
  have hp' : (p : ℚ) ≤ rkIdx (fixV A) := by exact_mod_cast hp
  calc (p : ℚ) / q ≤ p / rk A := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hA' hq'
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right hp' hA'.le

@[expose] noncomputable def burnsideK312_RU_S (c : OrthogonalFourCoordinates L s F)
    (A : Subgroup (MulAut V)) : AddSubgroup F where
  carrier := {x | burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) ∈ A}
  add_mem' := fun {x y} hx hy => by
    show burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (x + y)) ∈ A
    rw [← CFSG.Quasithin.JonesParshall.uMat_mul, map_mul]
    exact A.mul_mem hx hy
  zero_mem' := by
    show burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat 0) ∈ A
    rw [CFSG.Quasithin.JonesParshall.uMat_zero, map_one]
    exact A.one_mem
  neg_mem' := fun {x} hx => by
    show burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (-x)) ∈ A
    have : CFSG.Quasithin.JonesParshall.uMat (-x) =
        (CFSG.Quasithin.JonesParshall.uMat x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, CFSG.Quasithin.JonesParshall.uMat_mul, neg_add_cancel,
        CFSG.Quasithin.JonesParshall.uMat_zero]
    rw [this, map_inv]
    exact A.inv_mem hx

theorem burnsideK312_RU_mem_S (c : OrthogonalFourCoordinates L s F) (A : Subgroup (MulAut V))
    (x : F) : x ∈ burnsideK312_RU_S c A ↔
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) ∈ A := Iff.rfl

theorem burnsideK312_RU_eq_map (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) :
    A = (CFSG.Quasithin.B45L2.rootSub (burnsideK312_RU_S c A)).map (burnsideK312_actHom c) := by
  ext z
  constructor
  · intro hz
    obtain ⟨g, ⟨x, -, rfl⟩, rfl⟩ := hA hz
    exact ⟨_, ⟨x, hz, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨x, hx, rfl⟩, rfl⟩
    exact hx

theorem burnsideK312_RU_card_A (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) : Nat.card A = Nat.card (burnsideK312_RU_S c A) := by
  conv_lhs => rw [burnsideK312_RU_eq_map c hA]
  rw [Subgroup.card_map_of_injective (burnsideK312_actHom_injective c),
    CFSG.Quasithin.B45L2.card_rootSub]

theorem burnsideK312_RU_exists_ne (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) (hA1 : A ≠ ⊥) : ∃ x ∈ burnsideK312_RU_S c A, x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hA1
  rw [burnsideK312_RU_eq_map c hA, eq_bot_iff]
  rintro z ⟨g, ⟨x, hx, rfl⟩, rfl⟩
  rw [hcon x hx, CFSG.Quasithin.JonesParshall.uMat_zero, map_one]
  exact Subgroup.one_mem _

theorem burnsideK312_RU_mem_fixV (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) (v : V) :
    v ∈ fixV A ↔ ∀ x ∈ burnsideK312_RU_S c A,
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) v = v := by
  constructor
  · intro h x hx
    exact h _ hx
  · intro h a ha
    obtain ⟨g, ⟨x, -, rfl⟩, rfl⟩ := hA ha
    exact h x ha

theorem burnsideK312_RU_fix_uMat (c : OrthogonalFourCoordinates L s F) {x : F} (hx : x ≠ 0)
    (v : V) :
    burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) v = v ↔
      c.matrix v 1 1 = 0 ∧ x * c.matrix v 1 0 + c.matrix v 0 1 * x ^ 2 ^ s = 0 := by
  constructor
  · intro h
    have h' := congrArg c.matrix h
    rw [burnsideK312_matrix_uMat] at h'
    have e01 := congrFun (congrFun h' 0) 1
    have e00 := congrFun (congrFun h' 0) 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e01 e00
    have h11 : c.matrix v 1 1 = 0 := by
      have : x * c.matrix v 1 1 = 0 := by linear_combination e01
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hx
      · exact h0
    refine ⟨h11, ?_⟩
    rw [h11] at e00
    linear_combination e00
  · rintro ⟨h11, h⟩
    apply burnsideK312_matrix_injective c
    rw [burnsideK312_matrix_uMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11]
    linear_combination h

theorem burnsideK312_RU_ratio_K {x B : F} (hx : x ≠ 0)
    (h : x * B ^ 2 ^ s + B * x ^ 2 ^ s = 0) : (B / x) ^ 2 ^ s = B / x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [div_pow, div_eq_div_iff (pow_ne_zero _ hx) hx]
  linear_combination h + (-(B * x ^ 2 ^ s)) * h2

@[expose] def burnsideK312_RU_Iso (c : OrthogonalFourCoordinates L s F) (A : Subgroup (MulAut V)) :
    Prop :=
  ∀ y ∈ burnsideK312_RU_S c A, ∀ t ∈ burnsideK312_RU_S c A, y * t ^ 2 ^ s + t * y ^ 2 ^ s = 0

theorem burnsideK312_RU_fix_iff (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) {x : F} (hxS : x ∈ burnsideK312_RU_S c A) (hx : x ≠ 0) (v : V)
    (hv : v ∈ fixV A) :
    c.matrix v 1 1 = 0 ∧ x * (c.matrix v 0 1) ^ 2 ^ s + c.matrix v 0 1 * x ^ 2 ^ s = 0 := by
  have h := (burnsideK312_RU_mem_fixV c hA v).mp hv x hxS
  obtain ⟨h11, h2⟩ := (burnsideK312_RU_fix_uMat c hx v).mp h
  refine ⟨h11, ?_⟩
  rw [burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0] at h2
  exact h2

theorem burnsideK312_RU_noniso (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) {x1 x2 : F} (h1 : x1 ∈ burnsideK312_RU_S c A)
    (h2 : x2 ∈ burnsideK312_RU_S c A) (hp : x1 * x2 ^ 2 ^ s + x2 * x1 ^ 2 ^ s ≠ 0) :
    ∀ v ∈ fixV A, c.matrix v 0 1 = 0 ∧ c.matrix v 1 1 = 0 := by
  have hc2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hx1 : x1 ≠ 0 := by
    rintro rfl
    apply hp
    simp
  have hx2 : x2 ≠ 0 := by
    rintro rfl
    apply hp
    simp
  intro v hv
  obtain ⟨h11, e1⟩ := burnsideK312_RU_fix_iff c hA h1 hx1 v hv
  obtain ⟨-, e2⟩ := burnsideK312_RU_fix_iff c hA h2 hx2 v hv
  refine ⟨?_, h11⟩
  by_contra hB
  have r1 := burnsideK312_RU_ratio_K hx1 e1
  have r2 := burnsideK312_RU_ratio_K hx2 e2
  set B := c.matrix v 0 1 with hBdef
  obtain ⟨t, htdef⟩ : ∃ t, t = x1 / x2 := ⟨_, rfl⟩
  have ht : t ^ 2 ^ s = t := by
    have : x1 / x2 = (B / x2) / (B / x1) := by field_simp
    rw [htdef, this, div_pow, r1, r2]
  have hx1e : x1 = t * x2 := by rw [htdef]; field_simp
  have hx1s : x1 ^ 2 ^ s = t * x2 ^ 2 ^ s := by
    rw [hx1e, mul_pow, ht]
  apply hp
  rw [hx1s]
  conv_lhs => rw [hx1e]
  linear_combination (t * x2 * x2 ^ 2 ^ s) * hc2

end RU


section RU2

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_RU2_zero_pow : (0 : F) ^ 2 ^ s = 0 :=
  zero_pow (pow_ne_zero _ two_ne_zero)

theorem burnsideK312_RU_mem_fixV_iff (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c) {x0 : F}
    (hx0S : x0 ∈ burnsideK312_RU_S c A) (hx0 : x0 ≠ 0) (v : V) :
    v ∈ fixV A ↔ c.matrix v 1 1 = 0 ∧ ∀ x ∈ burnsideK312_RU_S c A,
      x * (c.matrix v 0 1) ^ 2 ^ s + c.matrix v 0 1 * x ^ 2 ^ s = 0 := by
  constructor
  · intro hv
    refine ⟨(burnsideK312_RU_fix_iff c hA hx0S hx0 v hv).1, fun x hx => ?_⟩
    by_cases hx0' : x = 0
    · subst hx0'
      rw [burnsideK312_RU2_zero_pow]
      ring
    · exact (burnsideK312_RU_fix_iff c hA hx hx0' v hv).2
  · rintro ⟨h11, h⟩
    rw [burnsideK312_RU_mem_fixV c hA]
    intro x hx
    by_cases hx0' : x = 0
    · subst hx0'
      rw [CFSG.Quasithin.JonesParshall.uMat_zero, map_one]
      rfl
    · rw [burnsideK312_RU_fix_uMat c hx0' v]
      refine ⟨h11, ?_⟩
      rw [burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0]
      exact h x hx

theorem burnsideK312_RU_card_fix_noniso (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c) {x1 x2 : F}
    (h1 : x1 ∈ burnsideK312_RU_S c A) (h2 : x2 ∈ burnsideK312_RU_S c A)
    (hp : x1 * x2 ^ 2 ^ s + x2 * x1 ^ 2 ^ s ≠ 0) : Nat.card (fixV A) ≤ 2 ^ s := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  have hmain := burnsideK312_RU_noniso c hA h1 h2 hp
  let f : ↥(fixV A) → ↥(burnsideK312_K F s) := fun v =>
    ⟨c.matrix v.1 0 0, burnsideK312_mem_K.mpr
      (burnsideK312_herm_apply (burnsideK312_matrix_herm c v.1) 0 0).symm⟩
  have hinj : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    apply burnsideK312_matrix_injective c
    have e : c.matrix v.1 0 0 = c.matrix w.1 0 0 := congrArg Subtype.val hvw
    obtain ⟨hv01, hv11⟩ := hmain v.1 v.2
    obtain ⟨hw01, hw11⟩ := hmain w.1 w.2
    have hv10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v.1) 1 0
    have hw10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c w.1) 1 0
    rw [hv01, burnsideK312_RU2_zero_pow] at hv10
    rw [hw01, burnsideK312_RU2_zero_pow] at hw10
    ext i j
    fin_cases i <;> fin_cases j
    · exact e
    · show c.matrix v.1 0 1 = c.matrix w.1 0 1
      rw [hv01, hw01]
    · show c.matrix v.1 1 0 = c.matrix w.1 1 0
      rw [hv10, hw10]
    · show c.matrix v.1 1 1 = c.matrix w.1 1 1
      rw [hv11, hw11]
  calc Nat.card (fixV A) ≤ Nat.card ↥(burnsideK312_K F s) := Nat.card_le_card_of_injective f hinj
    _ = 2 ^ s := burnsideK312_card_K hs hF

theorem burnsideK312_RU_card_fix_iso (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c) {x0 : F}
    (hx0S : x0 ∈ burnsideK312_RU_S c A) (hx0 : x0 ≠ 0) (hiso : burnsideK312_RU_Iso c A) :
    Nat.card (fixV A) = 2 ^ (2 * s) := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  have hcK := burnsideK312_card_K hs hF
  apply le_antisymm
  · have hr : ∀ v : ↥(fixV A), (c.matrix v.1 0 1 / x0) ^ 2 ^ s = c.matrix v.1 0 1 / x0 := by
      intro v
      have h := ((burnsideK312_RU_mem_fixV_iff c hA hx0S hx0 v.1).mp v.2).2 x0 hx0S
      exact burnsideK312_RU_ratio_K hx0 h
    let f : ↥(fixV A) → ↥(burnsideK312_K F s) × ↥(burnsideK312_K F s) := fun v =>
      (⟨c.matrix v.1 0 0, burnsideK312_mem_K.mpr
        (burnsideK312_herm_apply (burnsideK312_matrix_herm c v.1) 0 0).symm⟩,
       ⟨c.matrix v.1 0 1 / x0, burnsideK312_mem_K.mpr (hr v)⟩)
    have hinj : Function.Injective f := by
      intro v w hvw
      have e1 : c.matrix v.1 0 0 = c.matrix w.1 0 0 := congrArg (fun p => p.1.1) hvw
      have e2 : c.matrix v.1 0 1 / x0 = c.matrix w.1 0 1 / x0 := congrArg (fun p => p.2.1) hvw
      have e2' : c.matrix v.1 0 1 = c.matrix w.1 0 1 := (div_left_inj' hx0).mp e2
      have hv11 := ((burnsideK312_RU_mem_fixV_iff c hA hx0S hx0 v.1).mp v.2).1
      have hw11 := ((burnsideK312_RU_mem_fixV_iff c hA hx0S hx0 w.1).mp w.2).1
      have hv10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v.1) 1 0
      have hw10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c w.1) 1 0
      apply Subtype.ext
      apply burnsideK312_matrix_injective c
      ext i j
      fin_cases i <;> fin_cases j
      · exact e1
      · exact e2'
      · show c.matrix v.1 1 0 = c.matrix w.1 1 0
        rw [hv10, hw10, e2']
      · show c.matrix v.1 1 1 = c.matrix w.1 1 1
        rw [hv11, hw11]
    calc Nat.card (fixV A) ≤ Nat.card (↥(burnsideK312_K F s) × ↥(burnsideK312_K F s)) :=
          Nat.card_le_card_of_injective f hinj
      _ = 2 ^ (2 * s) := by
          rw [Nat.card_prod, hcK]
          ring
  · have hmem : ∀ p : ↥(burnsideK312_K F s) × ↥(burnsideK312_K F s),
        burnsideK312_Geo_mk c p.1.1 (x0 * p.2.1) 0 (burnsideK312_mem_K.mp p.1.2)
          (burnsideK312_RU2_zero_pow) ∈ fixV A := by
      intro p
      rw [burnsideK312_RU_mem_fixV_iff c hA hx0S hx0]
      rw [burnsideK312_Geo_matrix_mk]
      refine ⟨rfl, fun x hx => ?_⟩
      have hb := burnsideK312_mem_K.mp p.2.2
      have h := hiso x hx x0 hx0S
      show x * (x0 * p.2.1) ^ 2 ^ s + (x0 * p.2.1) * x ^ 2 ^ s = 0
      rw [mul_pow, hb]
      linear_combination p.2.1 * h
    let g : ↥(burnsideK312_K F s) × ↥(burnsideK312_K F s) → ↥(fixV A) := fun p =>
      ⟨burnsideK312_Geo_mk c p.1.1 (x0 * p.2.1) 0 (burnsideK312_mem_K.mp p.1.2)
          (burnsideK312_RU2_zero_pow), hmem p⟩
    have hinj : Function.Injective g := by
      intro p q hpq
      have h := congrArg (fun v : ↥(fixV A) => c.matrix v.1) hpq
      simp only [g, burnsideK312_Geo_matrix_mk] at h
      have e1 := congrFun (congrFun h 0) 0
      have e2 := congrFun (congrFun h 0) 1
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e2
      have e2' : p.2.1 = q.2.1 := mul_left_cancel₀ hx0 e2
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2')
    calc 2 ^ (2 * s) = Nat.card (↥(burnsideK312_K F s) × ↥(burnsideK312_K F s)) := by
          rw [Nat.card_prod, hcK]
          ring
      _ ≤ Nat.card (fixV A) := Nat.card_le_card_of_injective g hinj

theorem burnsideK312_RU_S_ratio (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    {x0 : F} (hx0S : x0 ∈ burnsideK312_RU_S c A) (hx0 : x0 ≠ 0) (hiso : burnsideK312_RU_Iso c A)
    {y : F} (hy : y ∈ burnsideK312_RU_S c A) : (y / x0) ^ 2 ^ s = y / x0 :=
  burnsideK312_RU_ratio_K hx0 (hiso x0 hx0S y hy)

@[expose] noncomputable def burnsideK312_RU_toK (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} {x0 : F} (hx0S : x0 ∈ burnsideK312_RU_S c A) (hx0 : x0 ≠ 0)
    (hiso : burnsideK312_RU_Iso c A) : ↥(burnsideK312_RU_S c A) → ↥(burnsideK312_K F s) :=
  fun y => ⟨y.1 / x0, burnsideK312_mem_K.mpr (burnsideK312_RU_S_ratio c hx0S hx0 hiso y.2)⟩

theorem burnsideK312_RU_toK_injective (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} {x0 : F} (hx0S : x0 ∈ burnsideK312_RU_S c A) (hx0 : x0 ≠ 0)
    (hiso : burnsideK312_RU_Iso c A) :
    Function.Injective (burnsideK312_RU_toK c hx0S hx0 hiso) := by
  intro y z h
  have h' : y.1 / x0 = z.1 / x0 := congrArg Subtype.val h
  exact Subtype.ext ((div_left_inj' hx0).mp h')

theorem burnsideK312_RU_card_S_iso_le (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} {x0 : F} (hx0S : x0 ∈ burnsideK312_RU_S c A) (hx0 : x0 ≠ 0)
    (hiso : burnsideK312_RU_Iso c A) : Nat.card (burnsideK312_RU_S c A) ≤ 2 ^ s := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  calc Nat.card (burnsideK312_RU_S c A) ≤ Nat.card ↥(burnsideK312_K F s) :=
        Nat.card_le_card_of_injective _ (burnsideK312_RU_toK_injective c hx0S hx0 hiso)
    _ = 2 ^ s := burnsideK312_card_K hs hF

theorem burnsideK312_RU_S_eq_of_card (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} {x0 : F} (hx0S : x0 ∈ burnsideK312_RU_S c A) (hx0 : x0 ≠ 0)
    (hiso : burnsideK312_RU_Iso c A) (hcard : 2 ^ s ≤ Nat.card (burnsideK312_RU_S c A))
    (k : F) (hk : k ^ 2 ^ s = k) : x0 * k ∈ burnsideK312_RU_S c A := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  have hbij := (burnsideK312_RU_toK_injective c hx0S hx0 hiso).bijective_of_nat_card_le
    (by rw [burnsideK312_card_K hs hF]; exact hcard)
  obtain ⟨y, hy⟩ := hbij.2 ⟨k, burnsideK312_mem_K.mpr hk⟩
  have h' : y.1 / x0 = k := congrArg Subtype.val hy
  have : y.1 = x0 * k := by
    rw [← h']
    field_simp
  rw [← this]
  exact y.2

theorem burnsideK312_RU_quad_iso (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hq : IsQuadratic A) : burnsideK312_RU_Iso c A := by
  have hF := c.field_card
  intro y hy x hx
  by_cases hy0 : y = 0
  · subst hy0
    rw [burnsideK312_RU2_zero_pow]
    ring
  let v : V := burnsideK312_Geo_mk c 0 0 1 burnsideK312_RU2_zero_pow (one_pow _)
  have hv : c.matrix v = !![0, 0; 0, 1] := by
    rw [burnsideK312_Geo_matrix_mk, burnsideK312_RU2_zero_pow]
  let w : V := burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) v * v⁻¹
  have hw : w ∈ fixV A := hq (Subgroup.subset_closure ⟨_, hx, v, rfl⟩)
  have hfix := hw _ hy
  have hfix' := (burnsideK312_RU_fix_uMat c hy0 w).mp hfix
  have e10 : c.matrix w 1 0 = x ^ 2 ^ s := by
    simp only [w, burnsideK312_matrix_mul, burnsideK312_matrix_inv,
      burnsideK312_matrix_uMat, hv, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    ring
  have e01 : c.matrix w 0 1 = x := by
    simp only [w, burnsideK312_matrix_mul, burnsideK312_matrix_inv,
      burnsideK312_matrix_uMat, hv, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    ring
  rw [e10, e01] at hfix'
  linear_combination hfix'.2

@[expose] def burnsideK312_RU_W1 (c : OrthogonalFourCoordinates L s F) : Subgroup V where
  carrier := {v | c.matrix v 1 1 = 0}
  one_mem' := by simp [burnsideK312_matrix_one]
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [burnsideK312_matrix_mul, ha, hb]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [burnsideK312_matrix_inv, ha]

@[expose] def burnsideK312_RU_W2 (c : OrthogonalFourCoordinates L s F) : Subgroup V where
  carrier := {v | c.matrix v 0 1 = 0 ∧ c.matrix v 1 1 = 0}
  one_mem' := by simp [burnsideK312_matrix_one]
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [burnsideK312_matrix_mul, ha.1, ha.2, hb.1, hb.2]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [burnsideK312_matrix_inv, ha.1, ha.2]

theorem burnsideK312_RU_mem_Uc (c : OrthogonalFourCoordinates L s F) {a : MulAut V}
    (ha : a ∈ burnsideK312_Uc c) :
    ∃ x : F, a = burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x) := by
  obtain ⟨g, ⟨x, -, rfl⟩, rfl⟩ := ha
  exact ⟨x, rfl⟩

theorem burnsideK312_RU_cubic (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) : commSeries A 3 = ⊥ := by
  have ha : commSub (⊤ : Subgroup V) A ≤ burnsideK312_RU_W1 c := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨a, haA, w, -, rfl⟩
    obtain ⟨x, rfl⟩ := burnsideK312_RU_mem_Uc c (hA haA)
    show c.matrix _ 1 1 = 0
    simp only [burnsideK312_matrix_mul, burnsideK312_matrix_inv, burnsideK312_matrix_uMat,
      Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have hb : commSub (burnsideK312_RU_W1 c) A ≤ burnsideK312_RU_W2 c := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨a, haA, w, hw, rfl⟩
    obtain ⟨x, rfl⟩ := burnsideK312_RU_mem_Uc c (hA haA)
    have hw' : c.matrix w 1 1 = 0 := hw
    show c.matrix _ 0 1 = 0 ∧ c.matrix _ 1 1 = 0
    simp only [burnsideK312_matrix_mul, burnsideK312_matrix_inv, burnsideK312_matrix_uMat,
      Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hw']
    constructor <;> ring
  have hc : commSub (burnsideK312_RU_W2 c) A = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro w hw a haA
    obtain ⟨x, rfl⟩ := burnsideK312_RU_mem_Uc c (hA haA)
    obtain ⟨hw01, hw11⟩ := hw
    have hw10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c w) 1 0
    rw [hw01, burnsideK312_RU2_zero_pow] at hw10
    apply burnsideK312_matrix_injective c
    rw [burnsideK312_matrix_uMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hw01, hw11, hw10]
  show commSub (commSub (commSub ⊤ A) A) A = ⊥
  exact eq_bot_iff.mpr ((commSub_mono (commSub_mono ha le_rfl) le_rfl).trans
    ((commSub_mono hb le_rfl).trans hc.le))

theorem burnsideK312_RU_Uc_elem (c : OrthogonalFourCoordinates L s F) :
    IsElemAbelian2 (burnsideK312_Uc c) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨x, rfl⟩ := burnsideK312_RU_mem_Uc c ha
    obtain ⟨y, rfl⟩ := burnsideK312_RU_mem_Uc c hb
    rw [← map_mul, ← map_mul, CFSG.Quasithin.JonesParshall.uMat_mul,
      CFSG.Quasithin.JonesParshall.uMat_mul, add_comm]
  · obtain ⟨x, rfl⟩ := burnsideK312_RU_mem_Uc c ha
    rw [sq, ← map_mul, CFSG.Quasithin.JonesParshall.uMat_mul, CharTwo.add_self_eq_zero,
      CFSG.Quasithin.JonesParshall.uMat_zero, map_one]

theorem burnsideK312_RU_isPGroup (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) : IsPGroup 2 A := by
  intro a
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := (burnsideK312_RU_Uc_elem c).2 a.1 (hA a.2)
  simpa using this

theorem burnsideK312_RU_card_A_pow (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c) : Nat.card A = 2 ^ rk A :=
  card_eq_two_pow_of_isPGroup (burnsideK312_RU_isPGroup c hA)

theorem burnsideK312_RU_rk_pos (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) (hA1 : A ≠ ⊥) : 0 < rk A := by
  rcases Nat.eq_zero_or_pos (rk A) with h | h
  · exact absurd ((rk_eq_zero_iff_of_isPGroup (burnsideK312_RU_isPGroup c hA)).mp h) hA1
  · exact h

theorem burnsideK312_RU_rk_le_two_s (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c) : rk A ≤ 2 * s := by
  have h1 : Nat.card A ≤ 2 ^ (2 * s) := by
    rw [burnsideK312_RU_card_A c hA, ← c.field_card]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [burnsideK312_RU_card_A_pow c hA] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

theorem burnsideK312_RU_iso_num (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) (hA1 : A ≠ ⊥) (hiso : burnsideK312_RU_Iso c A) :
    rkIdx (fixV A) = 2 * s ∧ rk A ≤ s := by
  obtain ⟨x0, hx0S, hx0⟩ := burnsideK312_RU_exists_ne c hA hA1
  have h1 := burnsideK312_RU_card_fix_iso c hA hx0S hx0 hiso
  have h2 := burnsideK312_RU_card_S_iso_le c hx0S hx0 hiso
  have h3 := (burnsideK312_RU_card_A c hA).symm.trans (burnsideK312_RU_card_A_pow c hA)
  have hV := burnsideK312_RU_rk_fix_le c A
  refine ⟨?_, ?_⟩
  · rw [burnsideK312_RU_rkIdx c, burnsideK312_RU_rk_of_card h1]
    omega
  · rw [h3] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

theorem burnsideK312_RU_noniso_num (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c)
    (hni : ¬ burnsideK312_RU_Iso c A) : 3 * s ≤ rkIdx (fixV A) ∧ rk A ≤ 2 * s := by
  unfold burnsideK312_RU_Iso at hni
  push Not at hni
  obtain ⟨y, hy, t, ht, hyt⟩ := hni
  have h1 := burnsideK312_RU_card_fix_noniso c hA hy ht hyt
  have h2 := burnsideK312_RU_rk_le c h1
  refine ⟨?_, burnsideK312_RU_rk_le_two_s c hA⟩
  rw [burnsideK312_RU_rkIdx c]
  have := burnsideK312_RU_rk_fix_le c A
  omega

theorem burnsideK312_RU_iso_rAV (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) (hA1 : A ≠ ⊥) (hiso : burnsideK312_RU_Iso c A) :
    2 ≤ rAV A ∧ (rAV A ≤ 2 → rk A = s) := by
  have hs := burnsideK312_one_le c.field_card
  obtain ⟨hr, hm⟩ := burnsideK312_RU_iso_num c hA hA1 hiso
  have hpos := burnsideK312_RU_rk_pos c hA hA1
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have hm' : (0 : ℚ) < rk A := by exact_mod_cast hpos
  refine ⟨?_, fun h => ?_⟩
  · have := burnsideK312_RU_rAV_ge (A := A) (p := 2 * s) (q := s) hr.ge hm hpos
    have e : ((2 * s : ℕ) : ℚ) / (s : ℕ) = 2 := by
      push_cast
      field_simp
    rw [e] at this
    exact this
  · unfold rAV at h
    rw [hr, div_le_iff₀ hm'] at h
    have h' : (s : ℚ) ≤ rk A := by
      push_cast at h
      linarith
    have : s ≤ rk A := by exact_mod_cast h'
    omega

theorem burnsideK312_RU_noniso_rAV (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c) (hA1 : A ≠ ⊥)
    (hni : ¬ burnsideK312_RU_Iso c A) : 3 / 2 ≤ rAV A ∧ (rAV A = 3 / 2 → rk A = 2 * s) := by
  have hs := burnsideK312_one_le c.field_card
  obtain ⟨hr, hm⟩ := burnsideK312_RU_noniso_num c hA hni
  have hpos := burnsideK312_RU_rk_pos c hA hA1
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have hm' : (0 : ℚ) < rk A := by exact_mod_cast hpos
  refine ⟨?_, fun h => ?_⟩
  · have := burnsideK312_RU_rAV_ge (A := A) (p := 3 * s) (q := 2 * s) hr hm hpos
    have e : ((3 * s : ℕ) : ℚ) / ((2 * s : ℕ) : ℚ) = 3 / 2 := by
      push_cast
      field_simp
    rw [e] at this
    exact this
  · unfold rAV at h
    rw [div_eq_iff hm'.ne'] at h
    have h2 : (2 * rkIdx (fixV A) : ℚ) = 3 * rk A := by linarith
    have h3 : 2 * rkIdx (fixV A) = 3 * rk A := by exact_mod_cast h2
    omega

theorem burnsideK312_RU_eq_Uc_of_rk (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c) (hrk : rk A = 2 * s) :
    A = burnsideK312_Uc c := by
  have h1 := (burnsideK312_RU_card_A c hA).symm.trans (burnsideK312_RU_card_A_pow c hA)
  have h2 : Nat.card (burnsideK312_RU_S c A) = Nat.card F := by
    rw [h1, hrk, c.field_card]
  have hS : burnsideK312_RU_S c A = ⊤ := AddSubgroup.eq_top_of_card_eq _ h2
  have := burnsideK312_RU_eq_map c hA
  rw [hS] at this
  rw [this]
  rfl

theorem burnsideK312_RU_conj_tMat (c : OrthogonalFourCoordinates L s F) (a : F) (ha : a ≠ 0)
    (x : F) :
    MulAut.conj (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.tMat a ha))
        (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat x)) =
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (a ^ 2 * x)) := by
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
    CFSG.Quasithin.JonesParshall.tMat_conj]

theorem burnsideK312_RU_mem_Rc (c : OrthogonalFourCoordinates L s F) (k : F)
    (hk : k ^ 2 ^ s = k) :
    burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k) ∈ burnsideK312_Rc c :=
  ⟨_, ⟨k, hk, rfl⟩, rfl⟩

theorem burnsideK312_RU_iso_le_conj (c : OrthogonalFourCoordinates L s F)
    {A : Subgroup (MulAut V)} (hA : A ≤ burnsideK312_Uc c) (hA1 : A ≠ ⊥)
    (hiso : burnsideK312_RU_Iso c A) :
    ∃ (a : F) (ha : a ≠ 0), A ≤ (burnsideK312_Rc c).map
      (MulAut.conj (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.tMat a ha))).toMonoidHom := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨x0, hx0S, hx0⟩ := burnsideK312_RU_exists_ne c hA hA1
  have ha0 : CFSG.Quasithin.JonesParshall.sqrtF x0 ≠ 0 := by
    intro h
    apply hx0
    rw [← CFSG.Quasithin.JonesParshall.sqrtF_sq x0, h]
    ring
  refine ⟨CFSG.Quasithin.JonesParshall.sqrtF x0, ha0, fun z hz => ?_⟩
  obtain ⟨y, rfl⟩ := burnsideK312_RU_mem_Uc c (hA hz)
  have hyS : y ∈ burnsideK312_RU_S c A := hz
  have hk := burnsideK312_RU_S_ratio c hx0S hx0 hiso hyS
  refine ⟨_, burnsideK312_RU_mem_Rc c (y / x0) hk, ?_⟩
  show MulAut.conj _ _ = _
  rw [burnsideK312_RU_conj_tMat, CFSG.Quasithin.JonesParshall.sqrtF_sq]
  congr 3
  field_simp

theorem burnsideK312_RU_S_Uc (c : OrthogonalFourCoordinates L s F) (x : F) :
    x ∈ burnsideK312_RU_S c (burnsideK312_Uc c) :=
  ⟨_, ⟨x, AddSubgroup.mem_top x, rfl⟩, rfl⟩

theorem burnsideK312_RU_Uc_le_L (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_Uc c ≤ L := by
  intro z hz
  obtain ⟨g, -, rfl⟩ := hz
  exact burnsideK312_actHom_mem c g

theorem burnsideK312_RU_card_Uc (c : OrthogonalFourCoordinates L s F) :
    Nat.card (burnsideK312_Uc c) = 2 ^ (2 * s) := by
  unfold burnsideK312_Uc
  rw [Subgroup.card_map_of_injective (burnsideK312_actHom_injective c), burnsideK312_card_rootSub,
    c.field_card]

theorem burnsideK312_RU_Uc_noniso (c : OrthogonalFourCoordinates L s F) :
    ¬ burnsideK312_RU_Iso c (burnsideK312_Uc c) := by
  intro h
  obtain ⟨ω, hω⟩ := burnsideK312_exists_notFixed (burnsideK312_one_le c.field_card) c.field_card
  have := h 1 (burnsideK312_RU_S_Uc c 1) ω (burnsideK312_RU_S_Uc c ω)
  have h2 : ω ^ 2 ^ s + ω = 0 := by simpa using this
  exact hω (CharTwo.add_eq_zero.mp h2)

theorem burnsideK312_RU_card_fix_Uc (c : OrthogonalFourCoordinates L s F) :
    Nat.card (fixV (burnsideK312_Uc c)) = 2 ^ s := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  obtain ⟨ω, hω⟩ := burnsideK312_exists_notFixed hs hF
  apply le_antisymm
  · refine burnsideK312_RU_card_fix_noniso c le_rfl (burnsideK312_RU_S_Uc c 1)
      (burnsideK312_RU_S_Uc c ω) ?_
    intro h
    have h2 : ω ^ 2 ^ s + ω = 0 := by simpa using h
    exact hω (CharTwo.add_eq_zero.mp h2)
  · have hmem : ∀ k : ↥(burnsideK312_K F s),
        burnsideK312_Geo_mk c k.1 0 0 (burnsideK312_mem_K.mp k.2)
          burnsideK312_RU2_zero_pow ∈ fixV (burnsideK312_Uc c) := by
      intro k
      rw [burnsideK312_RU_mem_fixV_iff c le_rfl (burnsideK312_RU_S_Uc c 1) one_ne_zero,
        burnsideK312_Geo_matrix_mk]
      refine ⟨rfl, fun x _ => ?_⟩
      show x * (0 : F) ^ 2 ^ s + 0 * x ^ 2 ^ s = 0
      rw [burnsideK312_RU2_zero_pow]
      ring
    let g : ↥(burnsideK312_K F s) → ↥(fixV (burnsideK312_Uc c)) := fun k =>
      ⟨_, hmem k⟩
    have hinj : Function.Injective g := by
      intro k k' h
      have h' := congrArg (fun v : ↥(fixV (burnsideK312_Uc c)) => c.matrix v.1) h
      simp only [g, burnsideK312_Geo_matrix_mk] at h'
      have e := congrFun (congrFun h' 0) 0
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at e
      exact Subtype.ext e
    calc 2 ^ s = Nat.card ↥(burnsideK312_K F s) := (burnsideK312_card_K hs hF).symm
      _ ≤ _ := Nat.card_le_card_of_injective g hinj

theorem burnsideK312_RU_rAV_Uc (c : OrthogonalFourCoordinates L s F) :
    rAV (burnsideK312_Uc c) = 3 / 2 := by
  have hs := burnsideK312_one_le c.field_card
  unfold rAV
  rw [burnsideK312_RU_rkIdx c, burnsideK312_RU_rk_of_card (burnsideK312_RU_card_fix_Uc c),
    burnsideK312_RU_rk_of_card (burnsideK312_RU_card_Uc c)]
  have e : 4 * s - s = 3 * s := by omega
  rw [e]
  have hs' : (s : ℚ) ≠ 0 := by
    have : s ≠ 0 := by omega
    exact_mod_cast this
  push_cast
  field_simp

theorem burnsideK312_RU_S_Rc (c : OrthogonalFourCoordinates L s F) (x : F) :
    x ∈ burnsideK312_RU_S c (burnsideK312_Rc c) ↔ x ^ 2 ^ s = x := by
  constructor
  · intro h
    obtain ⟨g, ⟨t, ht, rfl⟩, hg⟩ := h
    have := CFSG.Quasithin.B45L2.uMat_injective (burnsideK312_actHom_injective c hg)
    rw [← this]
    exact ht
  · intro hx
    exact burnsideK312_RU_mem_Rc c x hx

theorem burnsideK312_RU_card_Rc (c : OrthogonalFourCoordinates L s F) :
    Nat.card (burnsideK312_Rc c) = 2 ^ s := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  unfold burnsideK312_Rc
  rw [Subgroup.card_map_of_injective (burnsideK312_actHom_injective c),
    CFSG.Quasithin.B45L2.card_rootSub, ← burnsideK312_card_K hs hF]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    rw [burnsideK312_mem_K]
    exact Iff.rfl)

theorem burnsideK312_RU_Rc_iso (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_RU_Iso c (burnsideK312_Rc c) := by
  intro y hy t ht
  have hy' := (burnsideK312_RU_S_Rc c y).mp hy
  have ht' := (burnsideK312_RU_S_Rc c t).mp ht
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [ht', hy']
  linear_combination (y * t) * h2

theorem burnsideK312_RU_fix_Rc (c : OrthogonalFourCoordinates L s F) :
    Nat.card (fixV (burnsideK312_Rc c)) = 2 ^ (2 * s) :=
  burnsideK312_RU_card_fix_iso c (burnsideK312_Rc_le_Uc c) (x0 := 1)
    ((burnsideK312_RU_S_Rc c 1).mpr (one_pow _)) one_ne_zero (burnsideK312_RU_Rc_iso c)

theorem burnsideK312_RU_rAV_Rc (c : OrthogonalFourCoordinates L s F) :
    rAV (burnsideK312_Rc c) = 2 := by
  have hs := burnsideK312_one_le c.field_card
  unfold rAV
  rw [burnsideK312_RU_rkIdx c, burnsideK312_RU_rk_of_card (burnsideK312_RU_fix_Rc c),
    burnsideK312_RU_rk_of_card (burnsideK312_RU_card_Rc c)]
  have e : 4 * s - 2 * s = 2 * s := by omega
  rw [e]
  have hs' : (s : ℚ) ≠ 0 := by
    have : s ≠ 0 := by omega
    exact_mod_cast this
  push_cast
  field_simp

theorem burnsideK312_RU_Rc_ne_bot (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_Rc c ≠ ⊥ := by
  have hs := burnsideK312_one_le c.field_card
  intro h
  have h1 := burnsideK312_RU_card_Rc c
  rw [h, Subgroup.card_bot] at h1
  have : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  omega

theorem burnsideK312_RU_Rc_elem (c : OrthogonalFourCoordinates L s F) :
    IsElemAbelian2 (burnsideK312_Rc c) :=
  ⟨fun a ha b hb => (burnsideK312_RU_Uc_elem c).1 a (burnsideK312_Rc_le_Uc c ha) b
      (burnsideK312_Rc_le_Uc c hb),
    fun a ha => (burnsideK312_RU_Uc_elem c).2 a (burnsideK312_Rc_le_Uc c ha)⟩

end RU2


section RU3

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_RU_fixV_sup (A B : Subgroup (MulAut V)) (v : V) :
    v ∈ fixV (A ⊔ B) ↔ v ∈ fixV A ∧ v ∈ fixV B := by
  constructor
  · intro h
    exact ⟨fun a ha => h a ((le_sup_left : A ≤ A ⊔ B) ha),
      fun b hb => h b ((le_sup_right : B ≤ A ⊔ B) hb)⟩
  · rintro ⟨hA, hB⟩ x hx
    have hle : A ⊔ B ≤ MulAction.stabilizer (MulAut V) v := sup_le
      (fun a ha => (MulAction.mem_stabilizer_iff).mpr (by rw [MulAut.smul_def]; exact hA a ha))
      (fun b hb => (MulAction.mem_stabilizer_iff).mpr (by rw [MulAut.smul_def]; exact hB b hb))
    have := (MulAction.mem_stabilizer_iff).mp (hle hx)
    rwa [MulAut.smul_def] at this

theorem burnsideK312_RU_Rc_commute (c : OrthogonalFourCoordinates L s F) {r : MulAut V}
    (hr : r ∈ burnsideK312_Rc c) : Commute r (burnsideK312_sh c) := by
  have hr' : r ∈ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓
      burnsideK312_Uc c := by
    rw [burnsideK312_centralizer_sh]
    exact hr
  exact (Subgroup.mem_centralizer_iff.mp hr'.1 (burnsideK312_sh c) (Set.mem_singleton _)).symm

theorem burnsideK312_RU_Y_commute (c : OrthogonalFourCoordinates L s F) {x : MulAut V}
    (hx : x ∈ burnsideK312_Rc c ∨ x * burnsideK312_sh c ∈ burnsideK312_Rc c) :
    Commute x (burnsideK312_sh c) := by
  rcases hx with hx | hx
  · exact burnsideK312_RU_Rc_commute c hx
  · have h := burnsideK312_RU_Rc_commute c hx
    have e : x = (x * burnsideK312_sh c) * burnsideK312_sh c := by
      rw [mul_assoc, burnsideK312_sh_sq, mul_one]
    rw [e]
    exact h.mul_left (Commute.refl _)

@[expose] def burnsideK312_RU_Y (c : OrthogonalFourCoordinates L s F) : Subgroup (MulAut V) where
  carrier := {x | x ∈ burnsideK312_Rc c ∨ x * burnsideK312_sh c ∈ burnsideK312_Rc c}
  one_mem' := Or.inl (Subgroup.one_mem _)
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (Subgroup.mul_mem _ hx hy)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact Subgroup.mul_mem _ hx hy
    · refine Or.inr ?_
      have hc : Commute y (burnsideK312_sh c) := burnsideK312_RU_Rc_commute c hy
      rw [mul_assoc, hc.eq, ← mul_assoc]
      exact Subgroup.mul_mem _ hx hy
    · refine Or.inl ?_
      have hc : Commute y (burnsideK312_sh c) := burnsideK312_RU_Y_commute c (Or.inr hy)
      have e : x * y = (x * burnsideK312_sh c) * (y * burnsideK312_sh c) := by
        have h1 : burnsideK312_sh c * y = y * burnsideK312_sh c := hc.eq.symm
        calc x * y = x * (burnsideK312_sh c * burnsideK312_sh c) * y := by
              rw [burnsideK312_sh_sq, mul_one]
          _ = x * burnsideK312_sh c * (burnsideK312_sh c * y) := by simp only [mul_assoc]
          _ = x * burnsideK312_sh c * (y * burnsideK312_sh c) := by rw [h1]
      rw [e]
      exact Subgroup.mul_mem _ hx hy
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (Subgroup.inv_mem _ hx)
    · refine Or.inr ?_
      have hc : Commute x (burnsideK312_sh c) := burnsideK312_RU_Y_commute c (Or.inr hx)
      have e : x⁻¹ * burnsideK312_sh c = (x * burnsideK312_sh c)⁻¹ := by
        rw [mul_inv_rev, burnsideK312_sh_inv]
        exact hc.inv_left.eq
      rw [e]
      exact Subgroup.inv_mem _ hx

theorem burnsideK312_RU3_ss (hF : Nat.card F = 2 ^ (2 * s)) (y : F) :
    (y ^ 2 ^ s) ^ 2 ^ s = y := by
  have := burnsideK312_sg_sg (s := s) hF y
  rw [burnsideK312_sg_apply, burnsideK312_sg_apply] at this
  exact this

theorem burnsideK312_RU_Xc_mem (c : OrthogonalFourCoordinates L s F) {x : MulAut V} :
    x ∈ burnsideK312_Xc c ↔
      x ∈ burnsideK312_Rc c ∨ x * burnsideK312_sh c ∈ burnsideK312_Rc c := by
  have hX : burnsideK312_Xc c = burnsideK312_Rc c ⊔ Subgroup.zpowers (burnsideK312_sh c) := rfl
  constructor
  · intro hx
    have hle : burnsideK312_Xc c ≤ burnsideK312_RU_Y c := by
      rw [hX]
      refine sup_le (fun r hr => Or.inl hr) ?_
      rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [burnsideK312_sh_sq]; exact Subgroup.one_mem _)
    exact hle hx
  · rintro (h | h)
    · rw [hX]
      exact (le_sup_left : burnsideK312_Rc c ≤ burnsideK312_Rc c ⊔
        Subgroup.zpowers (burnsideK312_sh c)) h
    · have e : x = (x * burnsideK312_sh c) * burnsideK312_sh c := by
        rw [mul_assoc, burnsideK312_sh_sq, mul_one]
      rw [e, hX]
      exact Subgroup.mul_mem _ ((le_sup_left : burnsideK312_Rc c ≤ burnsideK312_Rc c ⊔
        Subgroup.zpowers (burnsideK312_sh c)) h)
        ((le_sup_right : Subgroup.zpowers (burnsideK312_sh c) ≤ burnsideK312_Rc c ⊔
          Subgroup.zpowers (burnsideK312_sh c)) (Subgroup.mem_zpowers _))

theorem burnsideK312_RU_Xc_exists (c : OrthogonalFourCoordinates L s F) {x : MulAut V}
    (hx : x ∈ burnsideK312_Xc c) :
    ∃ r ∈ burnsideK312_Rc c, x = r ∨ x = r * burnsideK312_sh c := by
  rcases (burnsideK312_RU_Xc_mem c).mp hx with h | h
  · exact ⟨x, h, Or.inl rfl⟩
  · refine ⟨x * burnsideK312_sh c, h, Or.inr ?_⟩
    rw [mul_assoc, burnsideK312_sh_sq, mul_one]

theorem burnsideK312_RU_Xc_elem (c : OrthogonalFourCoordinates L s F) :
    IsElemAbelian2 (burnsideK312_Xc c) := by
  have hR := burnsideK312_RU_Rc_elem c
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨r, hr, h1⟩ := burnsideK312_RU_Xc_exists c ha
    obtain ⟨r', hr', h2⟩ := burnsideK312_RU_Xc_exists c hb
    have c1 : Commute r r' := hR.1 r hr r' hr'
    have c2 : Commute r (burnsideK312_sh c) := burnsideK312_RU_Rc_commute c hr
    have c3 : Commute r' (burnsideK312_sh c) := burnsideK312_RU_Rc_commute c hr'
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact c1.eq
    · exact (c1.mul_right c2).eq
    · exact (c1.mul_left c3.symm).eq
    · exact ((c1.mul_right c2).mul_left (c3.symm.mul_right (Commute.refl _))).eq
  · obtain ⟨r, hr, h1⟩ := burnsideK312_RU_Xc_exists c ha
    have c2 : Commute r (burnsideK312_sh c) := burnsideK312_RU_Rc_commute c hr
    rcases h1 with rfl | rfl
    · exact hR.2 a hr
    · rw [c2.mul_pow, hR.2 r hr, sq, burnsideK312_sh_sq, one_mul]

theorem burnsideK312_RU_Xc_fix (c : OrthogonalFourCoordinates L s F) (v : V) :
    v ∈ fixV (burnsideK312_Xc c) ↔
      c.matrix v 1 1 = 0 ∧ (c.matrix v 0 1) ^ 2 ^ s = c.matrix v 0 1 := by
  have hX : burnsideK312_Xc c = burnsideK312_Rc c ⊔ Subgroup.zpowers (burnsideK312_sh c) := rfl
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0
  rw [hX, burnsideK312_RU_fixV_sup, burnsideK312_Geo_fix]
  constructor
  · rintro ⟨hR, hT⟩
    have hsym := congrFun (congrFun hT 0) 1
    simp only [Matrix.transpose_apply] at hsym
    refine ⟨?_, ?_⟩
    · have := hR _ (burnsideK312_RU_mem_Rc c 1 (one_pow _))
      exact ((burnsideK312_RU_fix_uMat c one_ne_zero v).mp this).1
    · rw [hsym] at h10
      exact h10.symm
  · rintro ⟨h11, hK⟩
    refine ⟨?_, ?_⟩
    · rw [burnsideK312_RU_mem_fixV c (burnsideK312_Rc_le_Uc c)]
      intro x hx
      have hxK := (burnsideK312_RU_S_Rc c x).mp hx
      by_cases hx0 : x = 0
      · subst hx0
        rw [CFSG.Quasithin.JonesParshall.uMat_zero, map_one]
        rfl
      · rw [burnsideK312_RU_fix_uMat c hx0 v]
        refine ⟨h11, ?_⟩
        rw [h10, hK, hxK]
        linear_combination (x * c.matrix v 0 1) * h2
    · have hsym : c.matrix v 1 0 = c.matrix v 0 1 := by rw [h10, hK]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, hsym]

theorem burnsideK312_RU_Xc_quad (c : OrthogonalFourCoordinates L s F) :
    IsQuadratic (burnsideK312_Xc c) := by
  have hF := c.field_card
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  show commV (burnsideK312_Xc c) ≤ fixV (burnsideK312_Xc c)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  rw [SetLike.mem_coe, burnsideK312_RU_Xc_fix]
  obtain ⟨r, hr, h1⟩ := burnsideK312_RU_Xc_exists c hx
  obtain ⟨k, rfl⟩ := burnsideK312_RU_mem_Uc c (burnsideK312_Rc_le_Uc c hr)
  have hkS : k ∈ burnsideK312_RU_S c (burnsideK312_Rc c) := hr
  have hk := (burnsideK312_RU_S_Rc c k).mp hkS
  have hM11 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 1
  have hM10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0
  rcases h1 with rfl | rfl
  · have e11 : c.matrix (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k) v * v⁻¹)
        1 1 = 0 := by
      simp only [burnsideK312_matrix_mul, burnsideK312_matrix_inv, burnsideK312_matrix_uMat,
        Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      ring
    have e01 : c.matrix (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k) v * v⁻¹)
        0 1 = k * c.matrix v 1 1 := by
      simp only [burnsideK312_matrix_mul, burnsideK312_matrix_inv, burnsideK312_matrix_uMat,
        Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      ring
    rw [e11, e01]
    refine ⟨rfl, ?_⟩
    rw [mul_pow, hk, ← hM11]
  · have e11 : c.matrix ((burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k) *
        burnsideK312_sh c) v * v⁻¹) 1 1 = 0 := by
      simp only [MulAut.mul_apply, burnsideK312_matrix_mul, burnsideK312_matrix_inv,
        burnsideK312_matrix_uMat, burnsideK312_matrix_sh, Matrix.add_apply, Matrix.neg_apply,
        Matrix.of_apply, Matrix.transpose_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      ring
    have e01 : c.matrix ((burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k) *
        burnsideK312_sh c) v * v⁻¹) 0 1 =
        (c.matrix v 0 1) ^ 2 ^ s + k * c.matrix v 1 1 + c.matrix v 0 1 := by
      simp only [MulAut.mul_apply, burnsideK312_matrix_mul, burnsideK312_matrix_inv,
        burnsideK312_matrix_uMat, burnsideK312_matrix_sh, Matrix.add_apply, Matrix.neg_apply,
        Matrix.of_apply, Matrix.transpose_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [hM10]
      linear_combination (-c.matrix v 0 1) * h2
    rw [e11, e01]
    refine ⟨rfl, ?_⟩
    rw [add_pow_char_pow, add_pow_char_pow, mul_pow, hk, burnsideK312_RU3_ss hF, ← hM11]
    ring

theorem burnsideK312_RU_card_fix_Xc (c : OrthogonalFourCoordinates L s F) :
    Nat.card (fixV (burnsideK312_Xc c)) = 2 ^ (2 * s) := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  have hcK := burnsideK312_card_K hs hF
  apply le_antisymm
  · let f : ↥(fixV (burnsideK312_Xc c)) → ↥(burnsideK312_K F s) × ↥(burnsideK312_K F s) :=
      fun v => (⟨c.matrix v.1 0 0, burnsideK312_mem_K.mpr
          (burnsideK312_herm_apply (burnsideK312_matrix_herm c v.1) 0 0).symm⟩,
        ⟨c.matrix v.1 0 1, burnsideK312_mem_K.mpr
          ((burnsideK312_RU_Xc_fix c v.1).mp v.2).2⟩)
    have hinj : Function.Injective f := by
      intro v w hvw
      have e1 : c.matrix v.1 0 0 = c.matrix w.1 0 0 := congrArg (fun p => p.1.1) hvw
      have e2 : c.matrix v.1 0 1 = c.matrix w.1 0 1 := congrArg (fun p => p.2.1) hvw
      have hv11 := ((burnsideK312_RU_Xc_fix c v.1).mp v.2).1
      have hw11 := ((burnsideK312_RU_Xc_fix c w.1).mp w.2).1
      have hv10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v.1) 1 0
      have hw10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c w.1) 1 0
      apply Subtype.ext
      apply burnsideK312_matrix_injective c
      ext i j
      fin_cases i <;> fin_cases j
      · exact e1
      · exact e2
      · show c.matrix v.1 1 0 = c.matrix w.1 1 0
        rw [hv10, hw10, e2]
      · show c.matrix v.1 1 1 = c.matrix w.1 1 1
        rw [hv11, hw11]
    calc Nat.card (fixV (burnsideK312_Xc c))
        ≤ Nat.card (↥(burnsideK312_K F s) × ↥(burnsideK312_K F s)) :=
          Nat.card_le_card_of_injective f hinj
      _ = 2 ^ (2 * s) := by
          rw [Nat.card_prod, hcK]
          ring
  · have hmem : ∀ p : ↥(burnsideK312_K F s) × ↥(burnsideK312_K F s),
        burnsideK312_Geo_mk c p.1.1 p.2.1 0 (burnsideK312_mem_K.mp p.1.2)
          burnsideK312_RU2_zero_pow ∈ fixV (burnsideK312_Xc c) := by
      intro p
      rw [burnsideK312_RU_Xc_fix, burnsideK312_Geo_matrix_mk]
      exact ⟨rfl, burnsideK312_mem_K.mp p.2.2⟩
    let g : ↥(burnsideK312_K F s) × ↥(burnsideK312_K F s) → ↥(fixV (burnsideK312_Xc c)) :=
      fun p => ⟨_, hmem p⟩
    have hinj : Function.Injective g := by
      intro p q hpq
      have h := congrArg (fun v : ↥(fixV (burnsideK312_Xc c)) => c.matrix v.1) hpq
      simp only [g, burnsideK312_Geo_matrix_mk] at h
      have e1 := congrFun (congrFun h 0) 0
      have e2 := congrFun (congrFun h 0) 1
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e2
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
    calc 2 ^ (2 * s) = Nat.card (↥(burnsideK312_K F s) × ↥(burnsideK312_K F s)) := by
          rw [Nat.card_prod, hcK]
          ring
      _ ≤ Nat.card (fixV (burnsideK312_Xc c)) := Nat.card_le_card_of_injective g hinj

theorem burnsideK312_RU_card_Xc (c : OrthogonalFourCoordinates L s F) :
    Nat.card (burnsideK312_Xc c) = 2 ^ (s + 1) := by
  have hX : burnsideK312_Xc c = burnsideK312_Rc c ⊔ Subgroup.zpowers (burnsideK312_sh c) := rfl
  have hRX : burnsideK312_Rc c ≤ burnsideK312_Xc c := by
    rw [hX]
    exact le_sup_left
  have hσX : burnsideK312_sh c ∈ burnsideK312_Xc c := by
    rw [hX]
    exact (le_sup_right : Subgroup.zpowers (burnsideK312_sh c) ≤ burnsideK312_Rc c ⊔
      Subgroup.zpowers (burnsideK312_sh c)) (Subgroup.mem_zpowers _)
  have hnot : burnsideK312_sh c ∉ burnsideK312_Rc c := fun h =>
    burnsideK312_sh_notMem c (burnsideK312_RU_Uc_le_L c (burnsideK312_Rc_le_Uc c h))
  have hidx : (burnsideK312_Rc c).relIndex (burnsideK312_Xc c) = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨burnsideK312_sh c, hσX⟩, fun b => ?_⟩
    have hmem := (burnsideK312_RU_Xc_mem c).mp b.2
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : MulAut V) ∈ burnsideK312_Rc c
    · refine Or.inr ⟨hb, fun h => hnot ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h
      simpa using this
    · exact Or.inl ⟨hmem.resolve_left hb, hb⟩
  have h := Subgroup.relIndex_mul_card (burnsideK312_Rc c) (burnsideK312_Xc c)
  rw [hidx, inf_eq_left.mpr hRX, burnsideK312_RU_card_Rc] at h
  rw [← h]
  ring

theorem burnsideK312_RU_rAV_Xc (c : OrthogonalFourCoordinates L s F) :
    rAV (burnsideK312_Xc c) = ((2 * s : ℕ) : ℚ) / ((s : ℚ) + 1) := by
  unfold rAV
  rw [burnsideK312_RU_rkIdx c, burnsideK312_RU_rk_of_card (burnsideK312_RU_card_fix_Xc c),
    burnsideK312_RU_rk_of_card (burnsideK312_RU_card_Xc c)]
  have e : 4 * s - 2 * s = 2 * s := by omega
  rw [e]
  push_cast
  ring

theorem burnsideK312_X_facts (c : OrthogonalFourCoordinates L s F) :
    IsQuadratic (burnsideK312_Xc c) ∧ IsElemAbelian2 (burnsideK312_Xc c) ∧
    burnsideK312_Rc c ≠ ⊥ ∧ IsElemAbelian2 (burnsideK312_Rc c) ∧
    burnsideK312_Rc c ≤ burnsideK312_Uc c ∧ burnsideK312_Uc c ≤ L ∧
    Nat.card (fixV (burnsideK312_Xc c)) = 2 ^ (2 * s) ∧
    rAV (burnsideK312_Xc c) = ((2 * s : ℕ) : ℚ) / ((s : ℚ) + 1) ∧
    rAV (burnsideK312_Rc c) = 2 :=
  ⟨burnsideK312_RU_Xc_quad c, burnsideK312_RU_Xc_elem c, burnsideK312_RU_Rc_ne_bot c,
    burnsideK312_RU_Rc_elem c, burnsideK312_Rc_le_Uc c, burnsideK312_RU_Uc_le_L c,
    burnsideK312_RU_card_fix_Xc c, burnsideK312_RU_rAV_Xc c, burnsideK312_RU_rAV_Rc c⟩

theorem burnsideK312_RU_Uc_ne_bot (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_Uc c ≠ ⊥ := by
  have hs := burnsideK312_one_le c.field_card
  intro h
  have h1 := burnsideK312_RU_card_Uc c
  rw [h, Subgroup.card_bot] at h1
  have : 2 ≤ 2 ^ (2 * s) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem burnsideK312_Uc_facts (c : OrthogonalFourCoordinates L s F) :
    IsElemAbelian2 (burnsideK312_Uc c) ∧ burnsideK312_Uc c ≠ ⊥ ∧
    rAV (burnsideK312_Uc c) = 3 / 2 ∧ commSeries (burnsideK312_Uc c) 3 = ⊥ :=
  ⟨burnsideK312_RU_Uc_elem c, burnsideK312_RU_Uc_ne_bot c, burnsideK312_RU_rAV_Uc c,
    burnsideK312_RU_cubic c le_rfl⟩

theorem burnsideK312_tMat_mem (c : OrthogonalFourCoordinates L s F) (a : F) (ha : a ≠ 0) :
    burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.tMat a ha) ∈
      L ⊓ Subgroup.normalizer (burnsideK312_Uc c : Set (MulAut V)) := by
  rw [Subgroup.mem_inf]
  refine ⟨burnsideK312_actHom_mem c _, ?_⟩
  have hinv : (CFSG.Quasithin.JonesParshall.tMat a ha)⁻¹ =
      CFSG.Quasithin.JonesParshall.tMat a⁻¹ (inv_ne_zero ha) := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.Quasithin.JonesParshall.tMat_coe,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨x, rfl⟩ := burnsideK312_RU_mem_Uc c hh
    have := burnsideK312_RU_conj_tMat c a ha x
    rw [MulAut.conj_apply] at this
    rw [this]
    exact ⟨_, ⟨_, AddSubgroup.mem_top _, rfl⟩, rfl⟩
  · intro hh
    obtain ⟨y, hy⟩ := burnsideK312_RU_mem_Uc c hh
    have e := burnsideK312_RU_conj_tMat c a⁻¹ (inv_ne_zero ha) y
    have hg : burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.tMat a⁻¹ (inv_ne_zero ha)) =
        (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.tMat a ha))⁻¹ := by
      rw [← map_inv, hinv]
    have : h = burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (a⁻¹ ^ 2 * y)) := by
      rw [← e, hg, MulAut.conj_apply, inv_inv, ← hy]
      group
    rw [this]
    exact ⟨_, ⟨_, AddSubgroup.mem_top _, rfl⟩, rfl⟩

theorem burnsideK312_Uc_sub (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hA : A ≤ burnsideK312_Uc c) (_hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥) :
    3 / 2 ≤ rAV A ∧ (IsQuadratic A → 2 ≤ rAV A) ∧ commSeries A 3 = ⊥ ∧
    (IsQuadratic A → rAV A ≤ 2 →
      ∃ (a : F) (ha : a ≠ 0), A = (burnsideK312_Rc c).map
        (MulAut.conj (burnsideK312_actHom c
          (CFSG.Quasithin.JonesParshall.tMat a ha))).toMonoidHom) ∧
    ((∀ (a : F) (ha : a ≠ 0), ¬ A ≤ (burnsideK312_Rc c).map
        (MulAut.conj (burnsideK312_actHom c
          (CFSG.Quasithin.JonesParshall.tMat a ha))).toMonoidHom) →
      ((rAV A = 3 / 2 ↔ A = burnsideK312_Uc c) ∧ ¬ IsQuadratic A)) := by
  by_cases hiso : burnsideK312_RU_Iso c A
  · obtain ⟨h2, h2'⟩ := burnsideK312_RU_iso_rAV c hA hA1 hiso
    refine ⟨by linarith, fun _ => h2, burnsideK312_RU_cubic c hA, ?_, ?_⟩
    · intro _ hle
      obtain ⟨a, ha, hle'⟩ := burnsideK312_RU_iso_le_conj c hA hA1 hiso
      refine ⟨a, ha, ?_⟩
      have hrk := h2' hle
      apply Subgroup.eq_of_le_of_card_ge hle'
      rw [Subgroup.card_map_of_injective (fun x y h => (MulAut.conj _).injective h),
        burnsideK312_RU_card_Rc, burnsideK312_RU_card_A_pow c hA, hrk]
    · intro hall
      exfalso
      obtain ⟨a, ha, hle'⟩ := burnsideK312_RU_iso_le_conj c hA hA1 hiso
      exact hall a ha hle'
  · obtain ⟨h3, h3'⟩ := burnsideK312_RU_noniso_rAV c hA hA1 hiso
    refine ⟨h3, fun hq => absurd (burnsideK312_RU_quad_iso c hq) hiso,
      burnsideK312_RU_cubic c hA, fun hq => absurd (burnsideK312_RU_quad_iso c hq) hiso,
      fun _ => ⟨⟨fun h => burnsideK312_RU_eq_Uc_of_rk c hA (h3' h),
        fun h => h ▸ burnsideK312_RU_rAV_Uc c⟩,
        fun hq => hiso (burnsideK312_RU_quad_iso c hq)⟩⟩

end RU3


section W

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_W_exists_smul (c : OrthogonalFourCoordinates L s F) {κ : F}
    (hκ : κ ^ 2 ^ s = κ) (v : V) : ∃ u : V, c.matrix u = κ • c.matrix v := by
  apply burnsideK312_exists_vec c
  rw [burnsideK312_herm_iff c.field_card]
  obtain ⟨h00, h11, h10⟩ := (burnsideK312_herm_iff c.field_card).mp (burnsideK312_matrix_herm c v)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_pow, hκ, h00]
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_pow, hκ, h11]
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [h10, mul_pow, hκ]

theorem burnsideK312_W_det (c : OrthogonalFourCoordinates L s F) (v : V) :
    (c.matrix v).det = c.matrix v 0 0 * c.matrix v 1 1 -
      c.matrix v 0 1 * (c.matrix v 0 1) ^ 2 ^ s := by
  rw [Matrix.det_fin_two, burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0]

theorem burnsideK312_W_norm (c : OrthogonalFourCoordinates L s F) {v : V}
    (hv : (c.matrix v).det = 0) (h0 : c.matrix v 0 0 = 0) : c.matrix v 0 1 = 0 := by
  rw [burnsideK312_W_det, h0] at hv
  have h' : c.matrix v 0 1 * (c.matrix v 0 1) ^ 2 ^ s = 0 := by linear_combination -hv
  rcases mul_eq_zero.mp h' with h | h
  · exact h
  · exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h

theorem burnsideK312_W_bound (c : OrthogonalFourCoordinates L s F) (W : Subgroup V)
    (hsing : ∀ v ∈ W, (c.matrix v).det = 0)
    (hK : ∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
      ∀ vector ∈ W, ∀ scalarVector : V,
        c.matrix scalarVector = scalar • c.matrix vector → scalarVector ∈ W) :
    Nat.card W ≤ 2 ^ s := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  have hcK := burnsideK312_card_K hs hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases hA : ∃ w ∈ W, c.matrix w 0 0 ≠ 0
  · obtain ⟨w, hw, ha⟩ := hA
    have haK : (c.matrix w 0 0) ^ 2 ^ s = c.matrix w 0 0 :=
      (burnsideK312_herm_apply (burnsideK312_matrix_herm c w) 0 0).symm
    have hainvK : (c.matrix w 0 0)⁻¹ ^ 2 ^ s = (c.matrix w 0 0)⁻¹ := by
      rw [inv_pow, haK]
    obtain ⟨w0, hw0⟩ := burnsideK312_W_exists_smul c hainvK w
    have hw0W : w0 ∈ W := hK _ hainvK w hw w0 hw0
    have hw0_00 : c.matrix w0 0 0 = 1 := by
      rw [hw0]
      simp [ha]
    have key : ∀ w' ∈ W, c.matrix w' = c.matrix w' 0 0 • c.matrix w0 := by
      intro w' hw'
      have ha'K : (c.matrix w' 0 0) ^ 2 ^ s = c.matrix w' 0 0 :=
        (burnsideK312_herm_apply (burnsideK312_matrix_herm c w') 0 0).symm
      obtain ⟨u, hu⟩ := burnsideK312_W_exists_smul c ha'K w0
      have huW : u ∈ W := hK _ ha'K w0 hw0W u hu
      have hz : w' * u ∈ W := W.mul_mem hw' huW
      have hz00 : c.matrix (w' * u) 0 0 = 0 := by
        rw [burnsideK312_matrix_mul, hu]
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hw0_00]
        linear_combination (c.matrix w' 0 0) * h2
      have hz01 : c.matrix (w' * u) 0 1 = 0 := burnsideK312_W_norm c (hsing _ hz) hz00
      have hz11 : c.matrix (w' * u) 1 1 = 0 := by
        have hm : w0 * (w' * u) ∈ W := W.mul_mem hw0W hz
        have hdet0 := hsing _ hm
        have hdet1 := hsing w0 hw0W
        rw [burnsideK312_W_det, burnsideK312_matrix_mul c w0 (w' * u)] at hdet0
        rw [burnsideK312_W_det] at hdet1
        simp only [Matrix.add_apply, hz00, hz01, hw0_00, add_zero] at hdet0
        simp only [hw0_00] at hdet1
        linear_combination hdet0 - hdet1
      have hz10 : c.matrix (w' * u) 1 0 = 0 := by
        rw [burnsideK312_herm_apply (burnsideK312_matrix_herm c _) 1 0, hz01,
          burnsideK312_RU2_zero_pow]
      have hzero : c.matrix (w' * u) = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hz00, hz01, hz10, hz11]
      rw [burnsideK312_matrix_mul, hu] at hzero
      ext i j
      have := congrFun (congrFun hzero i) j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this ⊢
      linear_combination this - (c.matrix w' 0 0 * c.matrix w0 i j) * h2
    let f : ↥W → ↥(burnsideK312_K F s) := fun w' =>
      ⟨c.matrix w'.1 0 0, burnsideK312_mem_K.mpr
        (burnsideK312_herm_apply (burnsideK312_matrix_herm c w'.1) 0 0).symm⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      have e : c.matrix x.1 0 0 = c.matrix y.1 0 0 := congrArg Subtype.val hxy
      apply Subtype.ext
      apply burnsideK312_matrix_injective c
      rw [key x.1 x.2, key y.1 y.2, e]
    calc Nat.card W ≤ Nat.card ↥(burnsideK312_K F s) := Nat.card_le_card_of_injective f hinj
      _ = 2 ^ s := hcK
  · push Not at hA
    let f : ↥W → ↥(burnsideK312_K F s) := fun w' =>
      ⟨c.matrix w'.1 1 1, burnsideK312_mem_K.mpr
        (burnsideK312_herm_apply (burnsideK312_matrix_herm c w'.1) 1 1).symm⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      have e : c.matrix x.1 1 1 = c.matrix y.1 1 1 := congrArg Subtype.val hxy
      have hx00 := hA x.1 x.2
      have hy00 := hA y.1 y.2
      have hx01 := burnsideK312_W_norm c (hsing _ x.2) hx00
      have hy01 := burnsideK312_W_norm c (hsing _ y.2) hy00
      have hx10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c x.1) 1 0
      have hy10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c y.1) 1 0
      rw [hx01, burnsideK312_RU2_zero_pow] at hx10
      rw [hy01, burnsideK312_RU2_zero_pow] at hy10
      apply Subtype.ext
      apply burnsideK312_matrix_injective c
      ext i j
      fin_cases i <;> fin_cases j
      · exact hx00.trans hy00.symm
      · exact hx01.trans hy01.symm
      · exact hx10.trans hy10.symm
      · exact e
    calc Nat.card W ≤ Nat.card ↥(burnsideK312_K F s) := Nat.card_le_card_of_injective f hinj
      _ = 2 ^ s := hcK

@[expose] def burnsideK312_W_line (c : OrthogonalFourCoordinates L s F) (p : V) : Subgroup V where
  carrier := {v | ∃ κ : F, κ ^ 2 ^ s = κ ∧ c.matrix v = κ • c.matrix p}
  one_mem' := ⟨0, burnsideK312_RU2_zero_pow, by rw [burnsideK312_matrix_one, zero_smul]⟩
  mul_mem' := fun {a b} ⟨κ, hκ, ha⟩ ⟨κ', hκ', hb⟩ =>
    ⟨κ + κ', by rw [add_pow_char_pow, hκ, hκ'], by
      rw [burnsideK312_matrix_mul, ha, hb, add_smul]⟩
  inv_mem' := fun {a} ⟨κ, hκ, ha⟩ =>
    ⟨κ, hκ, by
      rw [burnsideK312_matrix_inv, ha]
      ext i j
      simp [CharTwo.neg_eq]⟩

theorem burnsideK312_witt (c : OrthogonalFourCoordinates L s F) :
    0 < s ∧ Nat.card V = 2 ^ (4 * s) ∧
    (∃ singularPoint : Subgroup V, c.IsPoint singularPoint ∧
      ∀ vector ∈ singularPoint, (c.matrix vector).det = 0) ∧
    (∀ singularSpace : Subgroup V,
      (∀ vector ∈ singularSpace, (c.matrix vector).det = 0) →
      (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
        ∀ vector ∈ singularSpace, ∀ scalarVector : V,
          c.matrix scalarVector = scalar • c.matrix vector → scalarVector ∈ singularSpace) →
      Nat.card singularSpace ≤ 2 ^ s) := by
  refine ⟨burnsideK312_one_le c.field_card, burnsideK312_Geo_card_V c, ?_,
    fun W hsing hK => burnsideK312_W_bound c W hsing hK⟩
  let p : V := burnsideK312_Geo_mk c 1 0 0 (one_pow _) burnsideK312_RU2_zero_pow
  have hp : c.matrix p = !![1, 0; 0 ^ 2 ^ s, 0] := burnsideK312_Geo_matrix_mk c _ _ _ _ _
  refine ⟨burnsideK312_W_line c p, ⟨p, ?_, fun v => Iff.rfl⟩, ?_⟩
  · intro h
    have := congrArg (fun v => c.matrix v 0 0) h
    simp [hp, burnsideK312_matrix_one] at this
  · rintro v ⟨κ, hκ, hv⟩
    rw [Matrix.det_fin_two, hv, hp]
    simp

theorem burnsideK312_W_fixV_zpowers (g : MulAut V) (v : V) :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v := by
  constructor
  · intro h
    exact h g (Subgroup.mem_zpowers g)
  · intro h x hx
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut V) v := by
      rw [Subgroup.zpowers_le]
      exact (MulAction.mem_stabilizer_iff).mpr (by rw [MulAut.smul_def]; exact h)
    have := (MulAction.mem_stabilizer_iff).mp (hle hx)
    rwa [MulAut.smul_def] at this

theorem burnsideK312_W_Rc_fix (c : OrthogonalFourCoordinates L s F) (v : V) :
    v ∈ fixV (burnsideK312_Rc c) ↔
      c.matrix v 1 1 = 0 ∧ (c.matrix v 0 1) ^ 2 ^ s = c.matrix v 0 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0
  constructor
  · intro hR
    have := hR _ (burnsideK312_RU_mem_Rc c 1 (one_pow _))
    obtain ⟨h11, h⟩ := (burnsideK312_RU_fix_uMat c one_ne_zero v).mp this
    refine ⟨h11, ?_⟩
    rw [one_pow] at h
    rw [h10] at h
    linear_combination h - (c.matrix v 0 1) * h2
  · rintro ⟨h11, hK⟩
    rw [burnsideK312_RU_mem_fixV c (burnsideK312_Rc_le_Uc c)]
    intro x hx
    have hxK := (burnsideK312_RU_S_Rc c x).mp hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [CFSG.Quasithin.JonesParshall.uMat_zero, map_one]
      rfl
    · rw [burnsideK312_RU_fix_uMat c hx0 v]
      refine ⟨h11, ?_⟩
      rw [h10, hK, hxK]
      linear_combination (x * c.matrix v 0 1) * h2

theorem burnsideK312_W_point (c : OrthogonalFourCoordinates L s F) {y : F}
    (hy : y ^ 2 ^ s ≠ y) :
    c.IsPoint (fixV (burnsideK312_Rc c ⊔ Subgroup.zpowers
      (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat y)))) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy burnsideK312_RU2_zero_pow
  let p : V := burnsideK312_Geo_mk c 1 0 0 (one_pow _) burnsideK312_RU2_zero_pow
  have hp : c.matrix p = !![1, 0; 0 ^ 2 ^ s, 0] := burnsideK312_Geo_matrix_mk c _ _ _ _ _
  refine ⟨p, ?_, fun v => ?_⟩
  · intro h
    have := congrArg (fun v => c.matrix v 0 0) h
    simp [hp, burnsideK312_matrix_one] at this
  · rw [burnsideK312_RU_fixV_sup, burnsideK312_W_Rc_fix, burnsideK312_W_fixV_zpowers,
      burnsideK312_RU_fix_uMat c hy0]
    have h10 := burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0
    constructor
    · rintro ⟨⟨h11, hK⟩, -, h⟩
      have h01 : c.matrix v 0 1 = 0 := by
        rw [h10, hK] at h
        have h' : c.matrix v 0 1 * (y + y ^ 2 ^ s) = 0 := by linear_combination h
        rcases mul_eq_zero.mp h' with h0 | h0
        · exact h0
        · exact absurd (CharTwo.add_eq_zero.mp h0).symm hy
      have hK0 : (c.matrix v 0 0) ^ 2 ^ s = c.matrix v 0 0 :=
        (burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 0 0).symm
      refine ⟨c.matrix v 0 0, hK0, ?_⟩
      rw [hp]
      have h10' : c.matrix v 1 0 = 0 := by
        rw [h10, h01, burnsideK312_RU2_zero_pow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10', h11, burnsideK312_RU2_zero_pow]
    · rintro ⟨κ, hκ, hv⟩
      rw [hp] at hv
      have e11 : c.matrix v 1 1 = 0 := by
        have := congrFun (congrFun hv 1) 1
        simpa using this
      have e01 : c.matrix v 0 1 = 0 := by
        have := congrFun (congrFun hv 0) 1
        simpa using this
      have e10 : c.matrix v 1 0 = 0 := by
        rw [h10, e01, burnsideK312_RU2_zero_pow]
      refine ⟨⟨e11, by rw [e01, burnsideK312_RU2_zero_pow]⟩, e11, ?_⟩
      rw [e10, e01]
      ring

theorem burnsideK312_W_normalizer (c : OrthogonalFourCoordinates L s F) {n : MulAut V}
    (hn : n ∈ L ⊓ Subgroup.normalizer (burnsideK312_Uc c : Set (MulAut V))) :
    ∃ p : F, p ≠ 0 ∧ ∀ k : F, MulAut.conj n
        (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k)) =
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (p ^ 2 * k)) := by
  obtain ⟨hnL, hnN⟩ := Subgroup.mem_inf.mp hn
  obtain ⟨g, rfl⟩ := burnsideK312_exists_actHom c hnL
  have hu1 : burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat 1) ∈
      burnsideK312_Uc c := ⟨_, ⟨1, AddSubgroup.mem_top _, rfl⟩, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hnN _).mp hu1
  obtain ⟨x, hx⟩ := burnsideK312_RU_mem_Uc c h1
  have h2 : g * CFSG.Quasithin.JonesParshall.uMat 1 * g⁻¹ =
      CFSG.Quasithin.JonesParshall.uMat x :=
    burnsideK312_actHom_injective c (by rw [map_mul, map_mul, map_inv]; exact hx)
  have h3 : g * CFSG.Quasithin.JonesParshall.uMat 1 = CFSG.Quasithin.JonesParshall.uMat x * g := by
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hmat := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F)) h3
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.Quasithin.JonesParshall.uMat_coe] at hmat
  have e11 := congrFun (congrFun hmat 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e11
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have hr : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := e11
  rw [hr] at hdet
  have hpt : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    linear_combination hdet
  refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 0, left_ne_zero_of_mul_eq_one hpt, fun k => ?_⟩
  have key : g * CFSG.Quasithin.JonesParshall.uMat k =
      CFSG.Quasithin.JonesParshall.uMat ((g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * k) * g := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.Quasithin.JonesParshall.uMat_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hr]
    linear_combination (-((g : Matrix (Fin 2) (Fin 2) F) 0 0 * k)) * hpt
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← mul_inv_eq_iff_eq_mul.mpr key]

theorem burnsideK312_W_map_le (c : OrthogonalFourCoordinates L s F) {n1 n2 : MulAut V}
    {p1 p2 ρ : F}
    (h1 : ∀ k : F, MulAut.conj n1
        (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k)) =
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (p1 ^ 2 * k)))
    (h2 : ∀ k : F, MulAut.conj n2
        (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k)) =
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (p2 ^ 2 * k)))
    (hρ : ρ ^ 2 ^ s = ρ) (hp : p1 ^ 2 = p2 ^ 2 * ρ) :
    (burnsideK312_Rc c).map (MulAut.conj n1).toMonoidHom ≤
      (burnsideK312_Rc c).map (MulAut.conj n2).toMonoidHom := by
  rintro z ⟨r, hr, rfl⟩
  obtain ⟨k, rfl⟩ := burnsideK312_RU_mem_Uc c (burnsideK312_Rc_le_Uc c hr)
  have hk := (burnsideK312_RU_S_Rc c k).mp hr
  refine ⟨burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (ρ * k)),
    burnsideK312_RU_mem_Rc c _ (by rw [mul_pow, hρ, hk]), ?_⟩
  show MulAut.conj n2 _ = MulAut.conj n1 _
  rw [h2, h1, hp, mul_assoc]

theorem burnsideK312_W_map_disjoint (c : OrthogonalFourCoordinates L s F) {n1 n2 : MulAut V}
    {p1 p2 : F} (hp2 : p2 ≠ 0)
    (h1 : ∀ k : F, MulAut.conj n1
        (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k)) =
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (p1 ^ 2 * k)))
    (h2 : ∀ k : F, MulAut.conj n2
        (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k)) =
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (p2 ^ 2 * k)))
    (hρ : ¬ ((p1 ^ 2 / p2 ^ 2) ^ 2 ^ s = p1 ^ 2 / p2 ^ 2)) :
    Disjoint ((burnsideK312_Rc c).map (MulAut.conj n1).toMonoidHom)
      ((burnsideK312_Rc c).map (MulAut.conj n2).toMonoidHom) := by
  rw [Subgroup.disjoint_def]
  rintro z ⟨r1, hr1, rfl⟩ ⟨r2, hr2, hz⟩
  obtain ⟨k1, rfl⟩ := burnsideK312_RU_mem_Uc c (burnsideK312_Rc_le_Uc c hr1)
  obtain ⟨k2, rfl⟩ := burnsideK312_RU_mem_Uc c (burnsideK312_Rc_le_Uc c hr2)
  have hk1 := (burnsideK312_RU_S_Rc c k1).mp hr1
  have hk2 := (burnsideK312_RU_S_Rc c k2).mp hr2
  have hz' : MulAut.conj n2 (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k2)) =
      MulAut.conj n1 (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat k1)) := hz
  rw [h1, h2] at hz'
  have hz'' : p2 ^ 2 * k2 = p1 ^ 2 * k1 :=
    CFSG.Quasithin.B45L2.uMat_injective (burnsideK312_actHom_injective c hz')
  by_cases hk1z : k1 = 0
  · subst hk1z
    show MulAut.conj n1 (burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat 0)) = 1
    rw [CFSG.Quasithin.JonesParshall.uMat_zero, map_one, map_one]
  · exfalso
    apply hρ
    have e : p1 ^ 2 / p2 ^ 2 = k2 / k1 := by
      rw [div_eq_div_iff (pow_ne_zero 2 hp2) hk1z]
      linear_combination (-1 : F) * hz''
    rw [e, div_pow, hk1, hk2]

theorem burnsideK312_std_x (c : OrthogonalFourCoordinates L s F) :
    (∀ element ∈ burnsideK312_Uc c, element ≠ 1 →
      ∃ normalizerElement ∈ L ⊓ Subgroup.normalizer (burnsideK312_Uc c : Set (MulAut V)),
        element ∈ (Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓
          burnsideK312_Uc c).map (MulAut.conj normalizerElement).toMonoidHom) ∧
    (∀ first ∈ L ⊓ Subgroup.normalizer (burnsideK312_Uc c : Set (MulAut V)),
      ∀ second ∈ L ⊓ Subgroup.normalizer (burnsideK312_Uc c : Set (MulAut V)),
      (Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓
          burnsideK312_Uc c).map (MulAut.conj first).toMonoidHom =
        (Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓
          burnsideK312_Uc c).map (MulAut.conj second).toMonoidHom ∨
      Disjoint ((Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓
          burnsideK312_Uc c).map (MulAut.conj first).toMonoidHom)
        ((Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓
          burnsideK312_Uc c).map (MulAut.conj second).toMonoidHom)) ∧
    (∀ element ∈ burnsideK312_Uc c,
      element ∉ (Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓
        burnsideK312_Uc c) →
      c.IsPoint (fixV ((Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) ⊓
        burnsideK312_Uc c) ⊔ Subgroup.zpowers element))) := by
  rw [burnsideK312_centralizer_sh]
  refine ⟨?_, ?_, ?_⟩
  · intro element hU hne
    obtain ⟨y, rfl⟩ := burnsideK312_RU_mem_Uc c hU
    letI : Fintype F := Fintype.ofFinite F
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hne
      rw [CFSG.Quasithin.JonesParshall.uMat_zero, map_one]
    have ha0 : CFSG.Quasithin.JonesParshall.sqrtF y ≠ 0 := by
      intro h
      apply hy0
      rw [← CFSG.Quasithin.JonesParshall.sqrtF_sq y, h]
      ring
    refine ⟨burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.tMat
      (CFSG.Quasithin.JonesParshall.sqrtF y) ha0), burnsideK312_tMat_mem c _ ha0,
      burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat 1),
      burnsideK312_RU_mem_Rc c 1 (one_pow _), ?_⟩
    show MulAut.conj _ _ = _
    rw [burnsideK312_RU_conj_tMat, CFSG.Quasithin.JonesParshall.sqrtF_sq, mul_one]
  · intro first hfirst second hsecond
    obtain ⟨p1, hp1, h1⟩ := burnsideK312_W_normalizer c hfirst
    obtain ⟨p2, hp2, h2⟩ := burnsideK312_W_normalizer c hsecond
    by_cases hρ : (p1 ^ 2 / p2 ^ 2) ^ 2 ^ s = p1 ^ 2 / p2 ^ 2
    · left
      apply le_antisymm
      · exact burnsideK312_W_map_le c h1 h2 hρ (by field_simp)
      · exact burnsideK312_W_map_le c h2 h1 (ρ := (p1 ^ 2 / p2 ^ 2)⁻¹)
          (by rw [inv_pow, hρ]) (by field_simp)
    · right
      exact burnsideK312_W_map_disjoint c hp2 h1 h2 hρ
  · intro element hU hnot
    obtain ⟨y, rfl⟩ := burnsideK312_RU_mem_Uc c hU
    apply burnsideK312_W_point c
    intro hy
    exact hnot (burnsideK312_RU_mem_Rc c y hy)

end W


section RO

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_RO_Xc_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    burnsideK312_Xc (burnsideK312_conj c g) =
      (burnsideK312_Xc c).map (MulAut.conj (burnsideK312_actHom c g)).toMonoidHom := by
  unfold burnsideK312_Xc
  rw [burnsideK312_Rc_conj, burnsideK312_sh_conj, Subgroup.map_sup, MonoidHom.map_zpowers]
  rfl

theorem burnsideK312_RO_incl_uMat (κ : ↥(burnsideK312_K F s)) :
    burnsideK312_Geo_incl (CFSG.Quasithin.JonesParshall.uMat κ) =
      CFSG.Quasithin.JonesParshall.uMat (κ : F) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [burnsideK312_Geo_incl_coe]
  fin_cases i <;> fin_cases j <;> simp [CFSG.Quasithin.JonesParshall.uMat_coe]

theorem burnsideK312_RO_sylow (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hAe : IsElemAbelian2 A) (hsh : burnsideK312_sh c ∈ A) :
    ∃ x : SL(2, ↥(burnsideK312_K F s)), ∀ a ∈ A, a ∈ L →
      a ∈ (burnsideK312_Rc c).map
        (MulAut.conj (burnsideK312_actHom c (burnsideK312_Geo_incl x))).toMonoidHom := by
  classical
  let Y' : Subgroup SL(2, ↥(burnsideK312_K F s)) :=
    (A.comap (burnsideK312_actHom c)).comap burnsideK312_Geo_incl
  have hY'p : IsPGroup 2 Y' := by
    intro y
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hy : burnsideK312_actHom c (burnsideK312_Geo_incl y.1) ∈ A := y.2
    have hsq := hAe.2 _ hy
    have h1 : burnsideK312_Geo_incl (F := F) (s := s) (y.1 ^ 2) =
        burnsideK312_Geo_incl (F := F) (s := s) 1 := by
      apply burnsideK312_actHom_injective c
      rw [map_pow, map_pow, map_one, map_one]
      exact hsq
    have h2 := burnsideK312_Geo_incl_injective h1
    simpa using h2
  obtain ⟨x, hx⟩ := burnsideK312_sylow_conj hY'p
  refine ⟨x, fun a haA haL => ?_⟩
  obtain ⟨g, rfl⟩ := burnsideK312_exists_actHom c haL
  have hcomm := hAe.1 _ hsh _ haA
  have hfix : Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g = g := by
    apply burnsideK312_actHom_injective c
    rw [← burnsideK312_sh_actHom, hcomm, mul_assoc, burnsideK312_sh_sq, mul_one]
  obtain ⟨g', rfl⟩ := burnsideK312_Geo_exists_incl hfix
  have hg' : g' ∈ Y' := haA
  obtain ⟨r, ⟨κ, -, rfl⟩, hr⟩ := hx hg'
  refine ⟨burnsideK312_actHom c (CFSG.Quasithin.JonesParshall.uMat (κ : F)),
    burnsideK312_RU_mem_Rc c _ (burnsideK312_mem_K.mp κ.2), ?_⟩
  show MulAut.conj _ _ = _
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← burnsideK312_RO_incl_uMat,
    ← map_inv, ← map_mul, ← map_mul]
  congr 2

theorem burnsideK312_RO_X_sub (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hAe : IsElemAbelian2 A) (hAX : A ≤ burnsideK312_Xc c) (hsh : burnsideK312_sh c ∈ A) :
    ((2 * s : ℕ) : ℚ) / ((s : ℚ) + 1) ≤ rAV A := by
  have hF := c.field_card
  have hs := burnsideK312_one_le hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hAp : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a.1 a.2)⟩
  have hcardA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hAp
  have hrk_le : rk A ≤ s + 1 := by
    have h1 : Nat.card A ≤ Nat.card (burnsideK312_Xc c) := Subgroup.card_le_of_le hAX
    rw [hcardA, burnsideK312_RU_card_Xc] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hsh1 : burnsideK312_sh c ≠ 1 := fun h => burnsideK312_sh_notMem c (h ▸ L.one_mem)
  have hne : A ≠ ⊥ := fun h => hsh1 (by
    have := h ▸ hsh
    simpa using this)
  have hrk_pos : 0 < rk A := by
    rcases Nat.eq_zero_or_pos (rk A) with h | h
    · exact absurd ((rk_eq_zero_iff_of_isPGroup hAp).mp h) hne
    · exact h
  by_cases hR : ∃ r ∈ A, r ∈ burnsideK312_Rc c ∧ r ≠ 1
  · obtain ⟨r, hrA, hrR, hr1⟩ := hR
    obtain ⟨k, rfl⟩ := burnsideK312_RU_mem_Uc c (burnsideK312_Rc_le_Uc c hrR)
    have hkK := (burnsideK312_RU_S_Rc c k).mp hrR
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hr1
      rw [CFSG.Quasithin.JonesParshall.uMat_zero, map_one]
    have hle : fixV A ≤ fixV (burnsideK312_Xc c) := by
      intro v hv
      rw [burnsideK312_RU_Xc_fix]
      obtain ⟨h11, h⟩ := (burnsideK312_RU_fix_uMat c hk0 v).mp (hv _ hrA)
      refine ⟨h11, ?_⟩
      rw [hkK, burnsideK312_herm_apply (burnsideK312_matrix_herm c v) 1 0] at h
      have h' : k * ((c.matrix v 0 1) ^ 2 ^ s + c.matrix v 0 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h0 | h0
      · exact absurd h0 hk0
      · exact CharTwo.add_eq_zero.mp h0
    have hcard : Nat.card (fixV A) ≤ 2 ^ (2 * s) := by
      calc Nat.card (fixV A) ≤ Nat.card (fixV (burnsideK312_Xc c)) := Subgroup.card_le_of_le hle
        _ = 2 ^ (2 * s) := burnsideK312_RU_card_fix_Xc c
    have hrk2 := burnsideK312_RU_rk_le c hcard
    have hidx : 2 * s ≤ rkIdx (fixV A) := by
      rw [burnsideK312_RU_rkIdx c]
      omega
    have := burnsideK312_RU_rAV_ge (A := A) (p := 2 * s) (q := s + 1) hidx hrk_le hrk_pos
    simpa using this
  · push Not at hR
    have hA_le : A ≤ Subgroup.zpowers (burnsideK312_sh c) := by
      intro a ha
      rcases (burnsideK312_RU_Xc_mem c).mp (hAX ha) with h | h
      · rw [hR a ha h]
        exact Subgroup.one_mem _
      · have h1 := hR (a * burnsideK312_sh c) (A.mul_mem ha hsh) h
        have e : a = burnsideK312_sh c := by
          have := mul_eq_one_iff_eq_inv.mp h1
          rw [this, burnsideK312_sh_inv]
        rw [e]
        exact Subgroup.mem_zpowers _
    have hA_eq : A = Subgroup.zpowers (burnsideK312_sh c) :=
      le_antisymm hA_le (Subgroup.zpowers_le.mpr hsh)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (burnsideK312_sh c) = 2 :=
      orderOf_eq_prime (by rw [sq, burnsideK312_sh_sq]) hsh1
    have hcard2 : Nat.card A = 2 := by
      rw [hA_eq, Nat.card_zpowers, hord]
    have hrk1 : rk A = 1 := by
      rw [hcardA] at hcard2
      exact (Nat.pow_right_injective (le_refl 2) (hcard2.trans (pow_one 2).symm))
    have hfix : Nat.card (fixV A) = 2 ^ (3 * s) := by
      rw [hA_eq]
      exact burnsideK312_Geo_card_perp c
    have hidx : rkIdx (fixV A) = s := by
      rw [burnsideK312_RU_rkIdx c, burnsideK312_RU_rk_of_card hfix]
      omega
    unfold rAV
    rw [hidx, hrk1]
    have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
    push_cast
    rw [div_one, div_le_iff₀ (by positivity)]
    nlinarith

theorem burnsideK312_outer_sub (c : OrthogonalFourCoordinates L s F) {A : Subgroup (MulAut V)}
    (hAe : IsElemAbelian2 A) (hsh : burnsideK312_sh c ∈ A)
    (hA : ∀ a ∈ A, a ∈ L ∨ a * burnsideK312_sh c ∈ L) :
    ((2 * s : ℕ) : ℚ) / ((s : ℚ) + 1) ≤ rAV A ∧
    ∃ x ∈ L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)),
      A ≤ (burnsideK312_Xc c).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x, hx⟩ := burnsideK312_RO_sylow c hAe hsh
  have hx0 : burnsideK312_actHom c (burnsideK312_Geo_incl x) ∈
      L ⊓ Subgroup.centralizer ({burnsideK312_sh c} : Set (MulAut V)) :=
    (burnsideK312_Geo_mem_centralizer c _).mpr
      ⟨burnsideK312_Geo_incl x, burnsideK312_Geo_incl_fixed x, rfl⟩
  have hcomm : burnsideK312_sh c * burnsideK312_actHom c (burnsideK312_Geo_incl x) =
      burnsideK312_actHom c (burnsideK312_Geo_incl x) * burnsideK312_sh c :=
    Subgroup.mem_centralizer_iff.mp hx0.2 _ (Set.mem_singleton _)
  have hconj_sh : (MulAut.conj (burnsideK312_actHom c (burnsideK312_Geo_incl x))).toMonoidHom
      (burnsideK312_sh c) = burnsideK312_sh c := by
    show burnsideK312_actHom c (burnsideK312_Geo_incl x) * burnsideK312_sh c *
      (burnsideK312_actHom c (burnsideK312_Geo_incl x))⁻¹ = burnsideK312_sh c
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hRX : burnsideK312_Rc c ≤ burnsideK312_Xc c := le_sup_left
  have hshX : burnsideK312_sh c ∈ burnsideK312_Xc c :=
    (le_sup_right : Subgroup.zpowers (burnsideK312_sh c) ≤ burnsideK312_Xc c)
      (Subgroup.mem_zpowers _)
  have hAX : A ≤ (burnsideK312_Xc c).map
      (MulAut.conj (burnsideK312_actHom c (burnsideK312_Geo_incl x))).toMonoidHom := by
    intro a ha
    rcases hA a ha with haL | haL
    · exact Subgroup.map_mono hRX (hx a ha haL)
    · have h1 := hx (a * burnsideK312_sh c) (A.mul_mem ha hsh) haL
      have e : a = (a * burnsideK312_sh c) * burnsideK312_sh c := by
        rw [mul_assoc, burnsideK312_sh_sq, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.map_mono hRX h1) ⟨_, hshX, hconj_sh⟩
  refine ⟨?_, _, hx0, hAX⟩
  have hX' : A ≤ burnsideK312_Xc (burnsideK312_conj c (burnsideK312_Geo_incl x)) := by
    rw [burnsideK312_RO_Xc_conj]
    exact hAX
  have hsh'' : burnsideK312_sh (burnsideK312_conj c (burnsideK312_Geo_incl x)) ∈ A := by
    rw [burnsideK312_sh_conj, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hsh
  exact burnsideK312_RO_X_sub _ hAe hX' hsh''

end RO


section AS1

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_AS_irr (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) :
    ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ := by
  intro J hJ
  have hinv : XMod.IsInv ↥L J := by
    intro l v hv
    have h2 : l • v = (l : MulAut V) v := by simp [Subgroup.smul_def, MulAut.smul_def]
    rw [h2]
    exact hJ l l.2 v hv
  exact hirr.2 J hinv bot_le le_top

theorem burnsideK312_AS_sylow_inf (hLG : L ≤ G) (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G) : IsSylowTwoOf (T ⊓ L) L := by
  have hnorm : (L.subgroupOf G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : MulAut V) ∈ L := hx
    show ((g * x * g⁻¹ : ↥G) : MulAut V) ∈ L
    simpa using hLn g g.2 x hx'
  exact CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hLG hnorm.isSubnormal

theorem burnsideK312_AS_mem_normalizer (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    {g : MulAut V} (hg : g ∈ G) : g ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hLn g hg h, fun hh => ?_⟩
  have := hLn g⁻¹ (G.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem burnsideK312_AS_mem_normalizer_inf (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    {T : Subgroup (MulAut V)} (hT : T ≤ G) {t : MulAut V} (ht : t ∈ T) :
    t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ t ∈ T, ∀ h ∈ T ⊓ L, t * h * t⁻¹ ∈ T ⊓ L := fun t ht h hh =>
    ⟨T.mul_mem (T.mul_mem ht hh.1) (T.inv_mem ht), hLn t (hT ht) h hh.2⟩
  refine ⟨key t ht h, fun hh => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hh
  simpa [mul_assoc] using this

theorem burnsideK312_AS_pair (c : OrthogonalFourCoordinates L s F)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L) {t : MulAut V}
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (hsq : t ^ 2 = 1) (ht : t ∉ L)
    (htS : t ∈ Subgroup.normalizer (S : Set (MulAut V))) :
    ∃ g : SL(2, F), S = burnsideK312_Uc (burnsideK312_conj c g) ∧
      t = burnsideK312_sh (burnsideK312_conj c g) := by
  obtain ⟨g, hg1, hg2⟩ := burnsideK312_pair c hirr hS hN hsq ht htS
  exact ⟨g, by rw [burnsideK312_Uc_conj]; exact hg1, by rw [burnsideK312_sh_conj]; exact hg2⟩

theorem burnsideK312_AS_sylow (c : OrthogonalFourCoordinates L s F) {S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) :
    ∃ g : SL(2, F), S = burnsideK312_Uc (burnsideK312_conj c g) := by
  obtain ⟨g, hg⟩ := burnsideK312_sylow_of_isSylow c hS
  exact ⟨g, by rw [burnsideK312_Uc_conj]; exact hg⟩

theorem burnsideK312_AS_MA (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hAe : IsElemAbelian2 A) :
    (A ≤ L ∧ ∃ g : SL(2, F), A ≤ burnsideK312_Uc (burnsideK312_conj c g)) ∨
    (¬ A ≤ L ∧ ∃ g : SL(2, F), burnsideK312_sh (burnsideK312_conj c g) ∈ A ∧
      ∀ a ∈ A, a ∈ L ∨ a * burnsideK312_sh (burnsideK312_conj c g) ∈ L) := by
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  have hirr := burnsideK312_AS_irr hHyp.2.2.2
  have hAp : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a.1 a.2)⟩
  obtain ⟨T, hAT, hT⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf_of_le hAG hAp
  have hS := burnsideK312_AS_sylow_inf hLG hLn hT
  by_cases hAL : A ≤ L
  · left
    refine ⟨hAL, ?_⟩
    obtain ⟨g, hg⟩ := burnsideK312_AS_sylow c hS
    exact ⟨g, hg ▸ fun a ha => ⟨hAT ha, hAL ha⟩⟩
  · right
    refine ⟨hAL, ?_⟩
    obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
    have ha2 : a ^ 2 = 1 := hAe.2 a haA
    obtain ⟨g, hg1, hg2⟩ := burnsideK312_AS_pair c hirr hS
      (burnsideK312_AS_mem_normalizer hLn (hAG haA)) ha2 haL
      (burnsideK312_AS_mem_normalizer_inf hLn hT.1 (hAT haA))
    refine ⟨g, hg2 ▸ haA, fun b hb => ?_⟩
    by_cases hbL : b ∈ L
    · exact Or.inl hbL
    · right
      obtain ⟨h, -, hh⟩ := burnsideK312_outer_involution (burnsideK312_conj c g) hirr
        (burnsideK312_AS_mem_normalizer hLn (hAG hb)) (hAe.2 b hb) hbL
      rw [hh, mul_assoc, burnsideK312_sh_sq, mul_one]
      exact burnsideK312_actHom_mem _ h

end AS1


section AS2

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_AS_rel (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) (x : V) :
    c.matrix x = (g : Matrix (Fin 2) (Fin 2) F) * (burnsideK312_conj c g).matrix x *
      (frobPow s (g : Matrix (Fin 2) (Fin 2) F))ᵀ := by
  have := burnsideK312_matrix_act c g ((burnsideK312_actHom c g)⁻¹ x)
  rw [MulAut.apply_inv_self] at this
  rw [burnsideK312_matrix_conj]
  exact this

theorem burnsideK312_AS_rel_inv (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) (x : V) :
    (burnsideK312_conj c g).matrix x = ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      c.matrix x * (frobPow s ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))ᵀ := by
  rw [burnsideK312_matrix_conj, ← map_inv, burnsideK312_matrix_act]

theorem burnsideK312_AS_det_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) (x : V) :
    ((burnsideK312_conj c g).matrix x).det = (c.matrix x).det := by
  rw [burnsideK312_AS_rel_inv]
  exact burnsideK312_det_twAct g⁻¹ _

theorem burnsideK312_AS_smul_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F))
    (x y : V) (κ : F) :
    (burnsideK312_conj c g).matrix x = κ • (burnsideK312_conj c g).matrix y ↔
      c.matrix x = κ • c.matrix y := by
  constructor
  · intro h
    rw [burnsideK312_AS_rel c g x, burnsideK312_AS_rel c g y, h]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  · intro h
    rw [burnsideK312_AS_rel_inv c g x, burnsideK312_AS_rel_inv c g y, h]
    simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem burnsideK312_AS_polar_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F))
    (x y : V) : (burnsideK312_conj c g).polar x y = c.polar x y := by
  unfold OrthogonalFourCoordinates.polar
  rw [← burnsideK312_matrix_mul (burnsideK312_conj c g) x y, ← burnsideK312_matrix_mul c x y,
    burnsideK312_AS_det_conj c g (x * y), burnsideK312_AS_det_conj c g x,
    burnsideK312_AS_det_conj c g y]

theorem burnsideK312_AS_TConj_transfer (c : OrthogonalFourCoordinates L s F) (g : SL(2, F))
    {t : MulAut V} (h : burnsideK312_TConj (burnsideK312_conj c g) t) :
    burnsideK312_TConj c t := by
  obtain ⟨h1, h2, ⟨p, hp1, hp2, hp3⟩, h4, h5, h6, h7, P, hP1, hP2, hP3, hP4, hP5, hP6⟩ := h
  have hdet := burnsideK312_AS_det_conj c g
  have hsm := burnsideK312_AS_smul_conj c g
  have hpol := burnsideK312_AS_polar_conj c g
  refine ⟨?_, ?_, ⟨p, hp1, ?_, ?_⟩, ?_, ?_, h6, h7, ⟨P, ?_, ?_, hP3, ?_, hP5, ?_⟩⟩
  · intro v
    rw [← hdet (t v), ← hdet v]
    exact h1 v
  · intro κ hκ first second hs
    exact (hsm _ _ κ).mp (h2 κ hκ first second ((hsm _ _ κ).mpr hs))
  · rw [← hdet p]
    exact hp2
  · intro v
    have e : (burnsideK312_conj c g).polar v p / ((burnsideK312_conj c g).matrix p).det =
        c.polar v p / (c.matrix p).det := by rw [hpol, hdet]
    have h3 := hp3 v
    rw [e] at h3
    generalize c.polar v p / (c.matrix p).det = lam at h3 ⊢
    rw [burnsideK312_AS_rel c g (t v), burnsideK312_AS_rel c g v, burnsideK312_AS_rel c g p, h3]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  · obtain ⟨q, hq1, hq2⟩ := h4
    exact ⟨q, hq1, fun v => (hq2 v).trans
      (exists_congr (fun κ => and_congr_right (fun _ => hsm v q κ)))⟩
  · intro v hv hv1
    rw [← hdet v]
    exact h5 v hv hv1
  · intro v
    rw [hP1 v]
    simp only [hpol]
  · intro κ hκ v hv sv hsv
    exact hP2 κ hκ v hv sv ((hsm sv v κ).mpr hsv)
  · intro x hx v hv
    refine ⟨(hP4 x hx v hv).1, ?_⟩
    rw [← hdet, ← hdet v]
    exact (hP4 x hx v hv).2
  · intro ι hdι hκι
    refine hP6 ι (fun v => ?_) (fun κ hκ first second hs => ?_)
    · rw [hdet, hdet]
      exact hdι v
    · exact (hsm _ _ κ).mpr (hκι κ hκ first second ((hsm _ _ κ).mp hs))

theorem burnsideK312_AS_TConj_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    burnsideK312_TConj c (burnsideK312_sh (burnsideK312_conj c g)) :=
  burnsideK312_AS_TConj_transfer c g (burnsideK312_TConj_sh (burnsideK312_conj c g))

theorem burnsideK312_AS_sh_conj_eq (c : OrthogonalFourCoordinates L s F) (g : SL(2, F)) :
    burnsideK312_sh (burnsideK312_conj c g) = burnsideK312_actHom c (g *
      (Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g)⁻¹) * burnsideK312_sh c := by
  have hs := burnsideK312_sh_sq c
  have h := burnsideK312_sh_actHom c g
  have e : (burnsideK312_actHom c (Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g))⁻¹ =
      burnsideK312_sh c * (burnsideK312_actHom c g)⁻¹ * burnsideK312_sh c := by
    rw [← h]
    simp only [mul_inv_rev, burnsideK312_sh_inv, mul_assoc, inv_inv]
  rw [burnsideK312_sh_conj, map_mul, map_inv, e]
  simp only [mul_assoc, hs, mul_one]

theorem burnsideK312_AS_fieldMatrix (c : OrthogonalFourCoordinates L s F) (h : SL(2, F)) :
    ∃ fieldMatrix : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ groupElement : ↥(StatedSL 2 F), ∃ imageElement : ↥(StatedSL 2 F),
        ((imageElement : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (fieldMatrix : Matrix (Fin 2) (Fin 2) F) *
            frobPow s ((groupElement : Matrix.GeneralLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) *
            (fieldMatrix⁻¹ : Matrix (Fin 2) (Fin 2) F) ∧
        ((c.group_equiv imageElement : ↥L) : MulAut V) =
          (burnsideK312_actHom c h * burnsideK312_sh c) *
            ((c.group_equiv groupElement : ↥L) : MulAut V) *
            (burnsideK312_actHom c h * burnsideK312_sh c)⁻¹) ∧
      ∀ vector : V, c.matrix ((burnsideK312_actHom c h * burnsideK312_sh c) vector) =
        (fieldMatrix : Matrix (Fin 2) (Fin 2) F) * frobPow s (c.matrix vector) *
          Matrix.transpose (frobPow s (fieldMatrix : Matrix (Fin 2) (Fin 2) F)) := by
  have hs := burnsideK312_sh_sq c
  refine ⟨((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F h :
    ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F), ?_, ?_⟩
  · intro γ
    obtain ⟨γ', rfl⟩ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).surjective γ
    refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
      (h * Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) γ' * h⁻¹), ?_, ?_⟩
    · show ((h * Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) γ' * h⁻¹ : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) = (h : Matrix (Fin 2) (Fin 2) F) *
          frobPow s (γ' : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F)⁻¹
      have hinv : (h : Matrix (Fin 2) (Fin 2) F)⁻¹ = ((h⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) :=
        Matrix.inv_eq_right_inv (by
          rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.SpecialLinearGroup.coe_one])
      rw [hinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.map_apply_coe, burnsideK312_frobPow_eq_map]
      rfl
    · show burnsideK312_actHom c (h * Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) γ' * h⁻¹) =
        (burnsideK312_actHom c h * burnsideK312_sh c) * burnsideK312_actHom c γ' *
          (burnsideK312_actHom c h * burnsideK312_sh c)⁻¹
      rw [map_mul, map_mul, map_inv, ← burnsideK312_sh_actHom, mul_inv_rev,
        burnsideK312_sh_inv]
      simp only [mul_assoc]
  · intro v
    rw [MulAut.mul_apply, burnsideK312_matrix_act, burnsideK312_matrix_sh,
      burnsideK312_herm_transpose (burnsideK312_matrix_herm c v)]
    rfl

end AS2


section AS3

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_AS_rAV_le_one (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (h : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) : rAV A ≤ 1 := by
  have hAp : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a.1 a.2)⟩
  have hcA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hAp
  have hcC : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hV (fixV A)
  have hcV : Nat.card V = 2 ^ rk V := by
    have := card_eq_two_pow hV ⊤
    simpa [rk_top] using this
  rw [hcV, hcA, hcC, ← pow_add] at h
  have h1 : rk V ≤ rk A + rk (fixV A) := (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have h2 := rk_add_rkIdx (fixV A)
  have hpos : 0 < rk A := by
    rcases Nat.eq_zero_or_pos (rk A) with h0 | h0
    · exact absurd ((rk_eq_zero_iff_of_isPGroup hAp).mp h0) hA1
    · exact h0
  have hpos' : (0 : ℚ) < rk A := by exact_mod_cast hpos
  unfold rAV
  rw [div_le_one hpos']
  have : rkIdx (fixV A) ≤ rk A := by omega
  exact_mod_cast this

theorem burnsideK312_AS_rAV_gt_one (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    (hs : 1 < s) {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hAe : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) : 1 < rAV A := by
  rcases burnsideK312_AS_MA c hHyp hAG hAe with ⟨-, g, hg⟩ | ⟨-, g, hsh, hA⟩
  · have := (burnsideK312_Uc_sub (burnsideK312_conj c g) hg hAe hA1).1
    linarith
  · have h := (burnsideK312_outer_sub (burnsideK312_conj c g) hAe hsh hA).1
    have hs' : (1 : ℚ) < s := by exact_mod_cast hs
    refine lt_of_lt_of_le ?_ h
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    linarith

theorem burnsideK312_AS_le_of_odd (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hodd : Odd (L.relIndex G)) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hAe : IsElemAbelian2 A) : A ≤ L := by
  have hnorm : (L.subgroupOf G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : MulAut V) ∈ L := hx
    show ((g * x * g⁻¹ : ↥G) : MulAut V) ∈ L
    simpa using hLn g g.2 x hx'
  intro a ha
  let x : ↥G := ⟨a, hAG ha⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 a ha)
  have hy2 : ((x : ↥G ⧸ L.subgroupOf G)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hx2]
    rfl
  have hyn : ((x : ↥G ⧸ L.subgroupOf G)) ^ (L.relIndex G) = 1 := by
    have := pow_card_eq_one' (G := ↥G ⧸ L.subgroupOf G) (x := (x : ↥G ⧸ L.subgroupOf G))
    exact this
  obtain ⟨m, hm⟩ := hodd
  have hy1 : ((x : ↥G ⧸ L.subgroupOf G)) = 1 := by
    calc ((x : ↥G ⧸ L.subgroupOf G)) = ((x : ↥G ⧸ L.subgroupOf G)) ^ (2 * m + 1) := by
          rw [pow_succ, pow_mul, hy2, one_pow, one_mul]
      _ = 1 := by rw [← hm]; exact hyn
  exact (QuotientGroup.eq_one_iff x).mp hy1

theorem burnsideK312_AS_Rc_le_G (c : OrthogonalFourCoordinates L s F) (hLG : L ≤ G) :
    burnsideK312_Rc c ≤ G :=
  (burnsideK312_Rc_le_Uc c).trans ((burnsideK312_RU_Uc_le_L c).trans hLG)

theorem burnsideK312_AS_Uc_le_G (c : OrthogonalFourCoordinates L s F) (hLG : L ≤ G) :
    burnsideK312_Uc c ≤ G :=
  (burnsideK312_RU_Uc_le_L c).trans hLG

theorem burnsideK312_AS_Rc_quad (c : OrthogonalFourCoordinates L s F) :
    commSeries (burnsideK312_Rc c) 2 = ⊥ := by
  have h := (isQuadratic_iff_commSeries_two _).mp (burnsideK312_RU_Xc_quad c)
  have hle : burnsideK312_Rc c ≤ burnsideK312_Xc c := le_sup_left
  exact eq_bot_iff.mpr ((commSeries_mono hle 2).trans h.le)

theorem burnsideK312_AS_Rc_A2 (c : OrthogonalFourCoordinates L s F) (hLG : L ≤ G) :
    IsA2 G (burnsideK312_Rc c) :=
  ⟨burnsideK312_AS_Rc_le_G c hLG, burnsideK312_RU_Rc_ne_bot c, burnsideK312_RU_Rc_elem c⟩

theorem burnsideK312_AS_Uc_A2 (c : OrthogonalFourCoordinates L s F) (hLG : L ≤ G) :
    IsA2 G (burnsideK312_Uc c) :=
  ⟨burnsideK312_AS_Uc_le_G c hLG, burnsideK312_RU_Uc_ne_bot c, burnsideK312_RU_Uc_elem c⟩

theorem burnsideK312_AS_q_le (c : OrthogonalFourCoordinates L s F) (hLG : L ≤ G) :
    qOf G ≤ ((2 : ℚ) : WithTop ℚ) ∧ qhatOf G ≤ (((3 / 2 : ℚ)) : WithTop ℚ) := by
  refine ⟨qOf_le_iff.mpr ⟨burnsideK312_Rc c, burnsideK312_AS_Rc_A2 c hLG,
    (isQuadratic_iff_commSeries_two _).mpr (burnsideK312_AS_Rc_quad c),
    (burnsideK312_RU_rAV_Rc c).le⟩, ?_⟩
  exact kq_le_iff.mpr ⟨burnsideK312_Uc c, burnsideK312_AS_Uc_A2 c hLG,
    burnsideK312_RU_cubic c le_rfl, (burnsideK312_RU_rAV_Uc c).le⟩

theorem burnsideK312_AS_q_odd (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    (hodd : Odd (L.relIndex G)) :
    qOf G = ((2 : ℚ) : WithTop ℚ) ∧ qhatOf G = (((3 / 2 : ℚ)) : WithTop ℚ) := by
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  have hA : ∀ A, IsA2 G A → ∃ g : SL(2, F), A ≤ burnsideK312_Uc (burnsideK312_conj c g) := by
    intro A hA
    have hAL := burnsideK312_AS_le_of_odd hLn hodd hA.1 hA.2.2
    rcases burnsideK312_AS_MA c hHyp hA.1 hA.2.2 with ⟨-, g, hg⟩ | ⟨hn, -⟩
    · exact ⟨g, hg⟩
    · exact absurd hAL hn
  refine ⟨?_, ?_⟩
  · unfold qOf
    refine kq_eq_coe_iff.mpr ⟨⟨burnsideK312_Rc c, burnsideK312_AS_Rc_A2 c hLG,
      burnsideK312_AS_Rc_quad c, burnsideK312_RU_rAV_Rc c⟩, fun A hA2 hAk => ?_⟩
    obtain ⟨g, hg⟩ := hA A hA2
    exact ((burnsideK312_Uc_sub (burnsideK312_conj c g) hg hA2.2.2 hA2.2.1).2.1
      ((isQuadratic_iff_commSeries_two _).mpr hAk))
  · unfold qhatOf
    refine kq_eq_coe_iff.mpr ⟨⟨burnsideK312_Uc c, burnsideK312_AS_Uc_A2 c hLG,
      burnsideK312_RU_cubic c le_rfl, burnsideK312_RU_rAV_Uc c⟩, fun A hA2 hAk => ?_⟩
    obtain ⟨g, hg⟩ := hA A hA2
    exact (burnsideK312_Uc_sub (burnsideK312_conj c g) hg hA2.2.2 hA2.2.1).1

theorem burnsideK312_AS_map_conj_mul (X : Subgroup (MulAut V)) (a b : MulAut V) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj b).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (b * a)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [h]

theorem burnsideK312_AS_zpowers_elem {t : MulAut V} (hsq : t ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers t) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self t m n).eq
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq, one_zpow]

theorem burnsideK312_AS_A_le_XZ (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hq : IsQuadratic A) (hr : rAV A ≤ 2) :
    ∃ z ∈ L, A ≤ (burnsideK312_Xc c).map (MulAut.conj z).toMonoidHom := by
  rcases burnsideK312_AS_MA c hHyp hAG hAe with ⟨-, g, hg⟩ | ⟨-, g, hsh, hA⟩
  · obtain ⟨-, -, -, h4, -⟩ := burnsideK312_Uc_sub (burnsideK312_conj c g) hg hAe hA1
    obtain ⟨a, ha, hAeq⟩ := h4 hq hr
    refine ⟨burnsideK312_actHom (burnsideK312_conj c g)
        (CFSG.Quasithin.JonesParshall.tMat a ha) * burnsideK312_actHom c g,
      L.mul_mem (burnsideK312_actHom_mem _ _) (burnsideK312_actHom_mem c g), ?_⟩
    rw [hAeq, burnsideK312_Rc_conj, burnsideK312_AS_map_conj_mul]
    exact Subgroup.map_mono le_sup_left
  · obtain ⟨-, x, hx, hAx⟩ := burnsideK312_outer_sub (burnsideK312_conj c g) hAe hsh hA
    refine ⟨x * burnsideK312_actHom c g, L.mul_mem hx.1 (burnsideK312_actHom_mem c g), ?_⟩
    rw [← burnsideK312_AS_map_conj_mul, ← burnsideK312_RO_Xc_conj]
    exact hAx

theorem burnsideK312_AS_exists_X (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    {t : MulAut V} (htG : t ∈ G) (htL : t ∉ L) (hsq : t ^ 2 = 1) :
    ∃ g : SL(2, F), burnsideK312_Xc (burnsideK312_conj c g) ≤ G ∧
      t = burnsideK312_sh (burnsideK312_conj c g) := by
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  have hirr := burnsideK312_AS_irr hHyp.2.2.2
  have hel := burnsideK312_AS_zpowers_elem hsq
  have hAp : IsPGroup 2 (Subgroup.zpowers t) :=
    fun a => ⟨1, Subtype.ext (by simpa using hel.2 a.1 a.2)⟩
  obtain ⟨T, hT0, hT⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf_of_le
    (Subgroup.zpowers_le.mpr htG) hAp
  have htT : t ∈ T := hT0 (Subgroup.mem_zpowers _)
  obtain ⟨g, hS, ht⟩ := burnsideK312_AS_pair c hirr (burnsideK312_AS_sylow_inf hLG hLn hT)
    (burnsideK312_AS_mem_normalizer hLn htG) hsq htL
    (burnsideK312_AS_mem_normalizer_inf hLn hT.1 htT)
  refine ⟨g, ?_, ht⟩
  show burnsideK312_Rc (burnsideK312_conj c g) ⊔
    Subgroup.zpowers (burnsideK312_sh (burnsideK312_conj c g)) ≤ G
  refine sup_le ?_ ?_
  · have hUT : burnsideK312_Uc (burnsideK312_conj c g) ≤ T := by
      rw [← hS]
      exact inf_le_left
    exact (burnsideK312_Rc_le_Uc _).trans (hUT.trans hT.1)
  · rw [← ht]
    exact Subgroup.zpowers_le.mpr htG

theorem burnsideK312_AS_q_outer (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    {t : MulAut V} (htG : t ∈ G) (htL : t ∉ L) (hsq : t ^ 2 = 1) :
    qOf G = ((((2 * s : ℕ) : ℚ) / ((s : ℚ) + 1) : ℚ) : WithTop ℚ) := by
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  obtain ⟨g, hXG, -⟩ := burnsideK312_AS_exists_X c hHyp htG htL hsq
  have hs := burnsideK312_one_le c.field_card
  unfold qOf
  refine kq_eq_coe_iff.mpr ⟨⟨burnsideK312_Xc (burnsideK312_conj c g), ⟨hXG, ?_,
    burnsideK312_RU_Xc_elem _⟩, (isQuadratic_iff_commSeries_two _).mp
      (burnsideK312_RU_Xc_quad _), burnsideK312_RU_rAV_Xc _⟩, fun A hA2 hAk => ?_⟩
  · intro h
    apply burnsideK312_RU_Rc_ne_bot (burnsideK312_conj c g)
    have hle : burnsideK312_Rc (burnsideK312_conj c g) ≤
        burnsideK312_Xc (burnsideK312_conj c g) := le_sup_left
    exact eq_bot_iff.mpr (hle.trans h.le)
  · rcases burnsideK312_AS_MA c hHyp hA2.1 hA2.2.2 with ⟨-, g', hg'⟩ | ⟨-, g', hsh, hA⟩
    · have := (burnsideK312_Uc_sub (burnsideK312_conj c g') hg' hA2.2.2 hA2.2.1).2.1
        ((isQuadratic_iff_commSeries_two _).mpr hAk)
      refine le_trans ?_ this
      have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
      rw [div_le_iff₀ (by positivity)]
      push_cast
      linarith
    · exact (burnsideK312_outer_sub (burnsideK312_conj c g') hA2.2.2 hsh hA).1

theorem burnsideK312_AS_Qset (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G) {t : MulAut V} (htT : t ∈ T)
    (htL : t ∉ L) (hsq : t ^ 2 = 1) :
    (∀ A ∈ Qset G, ∃ g ∈ G, A ≤ (Xt T L t).map (MulAut.conj g).toMonoidHom) ∧
    (∀ A ∈ Qset G, (∀ B ∈ Qset G, A ≤ B → B = A) →
      ∃ g ∈ G, A = (Xt T L t).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  have hirr := burnsideK312_AS_irr hHyp.2.2.2
  obtain ⟨g₀, hS, rfl⟩ := burnsideK312_AS_pair c hirr (burnsideK312_AS_sylow_inf hLG hLn hT)
    (burnsideK312_AS_mem_normalizer hLn (hT.1 htT)) hsq htL
    (burnsideK312_AS_mem_normalizer_inf hLn hT.1 htT)
  have hXt : Xt T L (burnsideK312_sh (burnsideK312_conj c g₀)) =
      (burnsideK312_Xc c).map (MulAut.conj (burnsideK312_actHom c g₀)).toMonoidHom := by
    unfold Xt Rt
    rw [hS, burnsideK312_centralizer_sh]
    exact burnsideK312_RO_Xc_conj c g₀
  have hXtG : Xt T L (burnsideK312_sh (burnsideK312_conj c g₀)) ≤ G := by
    unfold Xt Rt
    refine sup_le ?_ ?_
    · exact inf_le_right.trans (inf_le_left.trans hT.1)
    · exact Subgroup.zpowers_le.mpr (hT.1 htT)
  have hπg₀ : burnsideK312_actHom c g₀ ∈ L := burnsideK312_actHom_mem c g₀
  have key : ∀ A ∈ Qset G, ∃ g ∈ L,
      A ≤ (Xt T L (burnsideK312_sh (burnsideK312_conj c g₀))).map
        (MulAut.conj g).toMonoidHom := by
    intro A hA
    obtain ⟨⟨hA2, hr⟩, hk⟩ := hA
    obtain ⟨z, hz, hle⟩ := burnsideK312_AS_A_le_XZ c hHyp hA2.1 hA2.2.2 hA2.2.1
      ((isQuadratic_iff_commSeries_two _).mpr hk) hr
    refine ⟨z * (burnsideK312_actHom c g₀)⁻¹, L.mul_mem hz (L.inv_mem hπg₀), ?_⟩
    rw [hXt, burnsideK312_AS_map_conj_mul, inv_mul_cancel_right]
    exact hle
  refine ⟨fun A hA => ?_, fun A hA hmax => ?_⟩
  · obtain ⟨g, hg, hle⟩ := key A hA
    exact ⟨g, hLG hg, hle⟩
  · obtain ⟨g, hg, hle⟩ := key A hA
    obtain ⟨h, hh⟩ := burnsideK312_exists_actHom c (L.mul_mem hg hπg₀)
    have hB : (Xt T L (burnsideK312_sh (burnsideK312_conj c g₀))).map
        (MulAut.conj g).toMonoidHom = burnsideK312_Xc (burnsideK312_conj c h) := by
      rw [hXt, burnsideK312_AS_map_conj_mul, burnsideK312_RO_Xc_conj, hh]
    have hBG : (Xt T L (burnsideK312_sh (burnsideK312_conj c g₀))).map
        (MulAut.conj g).toMonoidHom ≤ G := by
      rintro _ ⟨x, hx, rfl⟩
      exact G.mul_mem (G.mul_mem (hLG hg) (hXtG hx)) (G.inv_mem (hLG hg))
    obtain ⟨hq, he, hRne, -, -, -, -, hr, -⟩ := burnsideK312_X_facts (burnsideK312_conj c h)
    have hs := burnsideK312_one_le c.field_card
    have hBmem : (Xt T L (burnsideK312_sh (burnsideK312_conj c g₀))).map
        (MulAut.conj g).toMonoidHom ∈ Qset G := by
      rw [hB] at hBG ⊢
      refine ⟨⟨⟨hBG, ?_, he⟩, ?_⟩, (isQuadratic_iff_commSeries_two _).mp hq⟩
      · intro hbot
        apply hRne
        have hle' : burnsideK312_Rc (burnsideK312_conj c h) ≤
            burnsideK312_Xc (burnsideK312_conj c h) := le_sup_left
        exact eq_bot_iff.mpr (hle'.trans hbot.le)
      · rw [hr]
        have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
        rw [div_le_iff₀ (by positivity)]
        push_cast
        linarith
    exact ⟨g, hLG hg, (hmax _ hBmem hle).symm⟩

theorem burnsideK312_AS_not_FF (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    (hV : ∀ v : V, v ^ 2 = 1) (hs : 1 < s) : ¬ IsFFModule G := by
  rintro ⟨A, hAG, hA1, hAe, hcard⟩
  have h1 := burnsideK312_AS_rAV_le_one hV hAe hA1 hcard
  have h2 := burnsideK312_AS_rAV_gt_one c hHyp hs hAG hAe hA1
  linarith

theorem burnsideK312_AS_C2 (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G) {t : MulAut V}
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut V)))
    (hNT : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)))
    (htL : t ∉ L) (hsq : t ^ 2 = 1) :
    (IsQuadratic (Xt T L t) ∧ Nat.card (fixV (Xt T L t)) = 2 ^ (2 * s) ∧
      rAV (Xt T L t) = ((2 * s : ℕ) : ℚ) / ((s : ℚ) + 1) ∧ rAV (Rt T L t) = 2) ∧
    ∀ A, IsA2 L A → A ≤ T ⊓ L →
      (∀ n ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
        ¬ A ≤ (Rt T L t).map (MulAut.conj n).toMonoidHom) →
      (3 / 2 : ℚ) ≤ rAV A ∧ (rAV A = 3 / 2 ↔ A = T ⊓ L) ∧ commSeries A 3 = ⊥ ∧
        ¬ IsQuadratic A := by
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  have hirr := burnsideK312_AS_irr hHyp.2.2.2
  obtain ⟨g, hS, rfl⟩ := burnsideK312_AS_pair c hirr (burnsideK312_AS_sylow_inf hLG hLn hT) hN hsq
    htL hNT
  have hRt : Rt T L (burnsideK312_sh (burnsideK312_conj c g)) =
      burnsideK312_Rc (burnsideK312_conj c g) := by
    unfold Rt
    rw [hS, burnsideK312_centralizer_sh]
  have hXt : Xt T L (burnsideK312_sh (burnsideK312_conj c g)) =
      burnsideK312_Xc (burnsideK312_conj c g) := by
    unfold Xt
    rw [hRt]
    rfl
  rw [hRt, hXt]
  obtain ⟨hq, -, -, -, -, -, hfix, hX, hR⟩ := burnsideK312_X_facts (burnsideK312_conj c g)
  rw [hS]
  refine ⟨⟨hq, hfix, hX, hR⟩, fun A hA hAU hall => ?_⟩
  obtain ⟨h1, -, h3, -, h5⟩ := burnsideK312_Uc_sub (burnsideK312_conj c g) hAU hA.2.2 hA.2.1
  have hall' : ∀ (a : F) (ha : a ≠ 0), ¬ A ≤ (burnsideK312_Rc (burnsideK312_conj c g)).map
      (MulAut.conj (burnsideK312_actHom (burnsideK312_conj c g)
        (CFSG.Quasithin.JonesParshall.tMat a ha))).toMonoidHom := fun a ha =>
    hall _ (burnsideK312_tMat_mem (burnsideK312_conj c g) a ha)
  obtain ⟨h5a, h5b⟩ := h5 hall'
  exact ⟨h1, h5a, h3, h5b⟩

theorem burnsideK312_AS_sh_normalizes_Uc (c : OrthogonalFourCoordinates L s F) :
    burnsideK312_sh c ∈ Subgroup.normalizer (burnsideK312_Uc c : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ x ∈ burnsideK312_Uc c, burnsideK312_sh c * x * (burnsideK312_sh c)⁻¹ ∈
      burnsideK312_Uc c := by
    intro x hx
    obtain ⟨y, rfl⟩ := burnsideK312_RU_mem_Uc c hx
    rw [burnsideK312_sh_inv, burnsideK312_sh_uMat]
    exact ⟨_, ⟨_, AddSubgroup.mem_top _, rfl⟩, rfl⟩
  refine ⟨key h, fun hh => ?_⟩
  have := key _ hh
  have e : burnsideK312_sh c * (burnsideK312_sh c * h * (burnsideK312_sh c)⁻¹) *
      (burnsideK312_sh c)⁻¹ = h := by
    rw [burnsideK312_sh_inv]
    calc burnsideK312_sh c * (burnsideK312_sh c * h * burnsideK312_sh c) * burnsideK312_sh c
        = (burnsideK312_sh c * burnsideK312_sh c) * h *
          (burnsideK312_sh c * burnsideK312_sh c) := by simp only [mul_assoc]
      _ = h := by rw [burnsideK312_sh_sq]; simp
  rw [e] at this
  exact this

theorem burnsideK312_AS_isPoint_conj (c : OrthogonalFourCoordinates L s F) (g : SL(2, F))
    {W : Subgroup V} (h : (burnsideK312_conj c g).IsPoint W) : c.IsPoint W := by
  obtain ⟨q, hq1, hq2⟩ := h
  exact ⟨q, hq1, fun v => (hq2 v).trans
    (exists_congr (fun κ => and_congr_right (fun _ => burnsideK312_AS_smul_conj c g v q κ)))⟩

theorem burnsideK312_AS_xblock (c : OrthogonalFourCoordinates L s F) (g : SL(2, F))
    {T : Subgroup (MulAut V)} (hS : T ⊓ L = burnsideK312_Uc (burnsideK312_conj c g)) :
    (∀ element ∈ T ⊓ L, element ≠ 1 →
      ∃ normalizerElement ∈ L ⊓
          Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
        element ∈ (Rt T L (burnsideK312_sh (burnsideK312_conj c g))).map
          (MulAut.conj normalizerElement).toMonoidHom) ∧
    (∀ first ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
      ∀ second ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
      (Rt T L (burnsideK312_sh (burnsideK312_conj c g))).map (MulAut.conj first).toMonoidHom =
          (Rt T L (burnsideK312_sh (burnsideK312_conj c g))).map
            (MulAut.conj second).toMonoidHom ∨
        Disjoint ((Rt T L (burnsideK312_sh (burnsideK312_conj c g))).map
            (MulAut.conj first).toMonoidHom)
          ((Rt T L (burnsideK312_sh (burnsideK312_conj c g))).map
            (MulAut.conj second).toMonoidHom)) ∧
    (∀ element ∈ T ⊓ L, element ∉ Rt T L (burnsideK312_sh (burnsideK312_conj c g)) →
      c.IsPoint (fixV (Rt T L (burnsideK312_sh (burnsideK312_conj c g)) ⊔
        Subgroup.zpowers element))) := by
  have hRt : Rt T L (burnsideK312_sh (burnsideK312_conj c g)) =
      Subgroup.centralizer ({burnsideK312_sh (burnsideK312_conj c g)} : Set (MulAut V)) ⊓
        burnsideK312_Uc (burnsideK312_conj c g) := by
    unfold Rt
    rw [hS]
  rw [hRt, hS]
  obtain ⟨x1, x2, x3⟩ := burnsideK312_std_x (burnsideK312_conj c g)
  exact ⟨x1, x2, fun e he hn => burnsideK312_AS_isPoint_conj c g (x3 e he hn)⟩

end AS3


section S1

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem burnsideK312_S1_center {s : ℕ} (c : OrthogonalFourCoordinates L s F) :
    Subgroup.center ↥L = ⊥ := by
  let θL : ↥L ≃* SL(2, F) :=
    c.group_equiv.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h1 : θL x ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := θL.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y']
  rw [B42L2.center_sl2_eq_bot, Subgroup.mem_bot] at h1
  exact θL.injective (h1.trans (map_one θL).symm)

theorem burnsideK312_S1_cent (c : OrthogonalFourCoordinates L 1 F)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {g : MulAut V} (hcomm : ∀ l ∈ L, g * l = l * g) : g = 1 := by
  obtain ⟨κ, hκ, hκv⟩ := burnsideK312_commutant c hirr g (fun h => hcomm _ (burnsideK312_actHom_mem c h))
  have hκ' : κ * κ = κ := by
    have : κ ^ 2 ^ 1 = κ := hκ
    simpa [sq] using this
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    obtain ⟨E, hE⟩ := burnsideK312_exists_vec c (burnsideK312_herm_E11 (F := F) (s := 1))
    have h1 : g E = g 1 := by
      apply burnsideK312_matrix_injective c
      rw [hκv, map_one, zero_smul, burnsideK312_matrix_one]
    have h2 : E = 1 := g.injective h1
    rw [h2, burnsideK312_matrix_one] at hE
    have := congrFun (congrFun hE 0) 0
    simp at this
  have hκ1 : κ = 1 := by
    have := mul_right_cancel₀ hκ0 (hκ'.trans (one_mul κ).symm)
    exact this
  ext v
  apply burnsideK312_matrix_injective c
  rw [hκv, hκ1, one_smul]
  rfl

@[expose] noncomputable def burnsideK312_S1_eL (c : OrthogonalFourCoordinates L 1 F) :
    ↥L ≃* ↥(alternatingGroup (Fin 5)) :=
  (c.group_equiv.symm.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans
    (Classical.choice (CFSG.Quasithin.C124.YL.A6.sl2_equiv_alt_five
      (by rw [c.field_card]; norm_num)))

theorem burnsideK312_S1_haut (c : OrthogonalFourCoordinates L 1 F) :
    Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L := by
  rw [Nat.card_congr (MulAut.congr (burnsideK312_S1_eL c)).toEquiv,
    Nat.card_congr (burnsideK312_S1_eL c).toEquiv]
  exact FFC.card_mulAut_alternating_le (Or.inl rfl)

theorem burnsideK312_S1_not_le {s : ℕ} (c : OrthogonalFourCoordinates L s F) (hHyp : B4Hyp G L)
    (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)} (hQ : IsFFStarOffender G Q) :
    ¬ Q ≤ L := by
  intro hQL
  have h1 := burnsideK312_AS_rAV_le_one hV hQ.2.2.1 hQ.2.1 (B42L2.card_le_of_offender hQ)
  rcases burnsideK312_AS_MA c hHyp hQ.1 hQ.2.2.1 with ⟨-, g, hg⟩ | ⟨hn, -⟩
  · have := (burnsideK312_Uc_sub (burnsideK312_conj c g) hg hQ.2.2.1 hQ.2.1).1
    linarith
  · exact hn hQL

theorem burnsideK312_S1_deleted
    (hK : KSetup V G L) (c : OrthogonalFourCoordinates L 1 F)
    {Q : Subgroup (MulAut V)} (hQ : IsFFStarOffender G Q) (hQq : IsQuadratic Q) :
    ¬ Q ≤ L ∧ ∃ (σ : ↥(L ⊔ Q) ≃* Equiv.Perm (Fin 5)) (e : V ≃* ↥(G6.coreMod 5)),
      (∀ (y : ↥(L ⊔ Q)) (v : V), e ((y : MulAut V) v) = G6.coreAct 5 (σ y) (e v)) ∧
      ∀ y : ↥(L ⊔ Q), (y : MulAut V) ∈ L ↔ σ y ∈ alternatingGroup (Fin 5) := by
  have hQL := burnsideK312_S1_not_le c hK.hyp hK.elem2 hQ
  refine ⟨hQL, ?_⟩
  letI : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, c.field_card]
  let θL : ↥L ≃* SL(2, F) :=
    c.group_equiv.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  rcases (B42L2.sl2_alt hK.elem2 hK.hyp (burnsideK312_S1_center c) (n := 2) le_rfl hFc θL hQ
    hQq).2 with ⟨hQL', -⟩ | ⟨-, -, σ, e, he, hL⟩
  · exact absurd hQL' hQL
  · exact ⟨σ, e, he, hL⟩

theorem burnsideK312_S1_normalizer (hHyp : B4Hyp G L) (c : OrthogonalFourCoordinates L 1 F)
    (hGL : G ≠ L) : Subgroup.normalizer (L : Set (MulAut V)) = G := by
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  have hirr := burnsideK312_AS_irr hHyp.2.2.2
  exact FFC.eq_of_card_mulAut_le (G := Subgroup.normalizer (L : Set (MulAut V))) hLG
    (fun g hg => burnsideK312_AS_mem_normalizer hLn hg) hGL
    (fun g hg l hl => (Subgroup.mem_normalizer_iff.mp hg l).mp hl)
    (fun g _ hc => burnsideK312_S1_cent c hirr hc) (burnsideK312_S1_haut c)

theorem burnsideK312_S1_Q (c : OrthogonalFourCoordinates L 1 F)
    (hshG : burnsideK312_sh c ∈ G) :
    IsFFStarOffender G (Subgroup.zpowers (burnsideK312_sh c)) ∧
      IsQuadratic (Subgroup.zpowers (burnsideK312_sh c)) := by
  have hsq : burnsideK312_sh c ^ 2 = 1 := by rw [sq]; exact burnsideK312_sh_sq c
  have hel := burnsideK312_AS_zpowers_elem hsq
  have hsh1 : burnsideK312_sh c ≠ 1 := fun h => burnsideK312_sh_notMem c (h ▸ L.one_mem)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (burnsideK312_sh c) = 2 := orderOf_eq_prime hsq hsh1
  have hQc : Nat.card (Subgroup.zpowers (burnsideK312_sh c)) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hfix : Nat.card (fixV (Subgroup.zpowers (burnsideK312_sh c))) = 2 ^ (3 * 1) :=
    burnsideK312_Geo_card_perp c
  have hV16 : Nat.card V = 2 ^ (4 * 1) := burnsideK312_Geo_card_V c
  refine ⟨⟨Subgroup.zpowers_le.mpr hshG, ?_, hel, fun B hB => ?_⟩, ?_⟩
  · intro h
    apply hsh1
    have : burnsideK312_sh c ∈ Subgroup.zpowers (burnsideK312_sh c) := Subgroup.mem_zpowers _
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  · by_cases hB1 : B = ⊥
    · subst hB1
      rw [B1.card_bot_mul_card_fixV, hV16, hQc, hfix]
      norm_num
    · obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
      have hbz := hB hb
      have hbs : b = burnsideK312_sh c := by
        rcases burnsideK312_Geo_zpowers c b hbz with h | h
        · exact absurd (Subtype.ext h) hb1
        · exact h
      have hle : Subgroup.zpowers (burnsideK312_sh c) ≤ B := by
        rw [Subgroup.zpowers_le, ← hbs]
        exact hb
      rw [le_antisymm hB hle]
  · intro v hv
    rw [burnsideK312_Geo_commV] at hv
    obtain ⟨κ, hκ, hvm⟩ := hv
    rw [burnsideK312_Geo_fix, hvm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem burnsideK312_S1
    (hK : KSetup V G L) (c : OrthogonalFourCoordinates L 1 F)
    (hB : BinaryOrthogonalFour L ⊤ ⊥ 1) :
    (IsAlt 5 ↥G ∨ Nonempty (↥G ≃* Equiv.Perm (Fin 5))) ∧ AlternatingNatural L ⊤ ⊥ 5 ∧
    (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) → ∀ A, IsFFStarOffender G A → B42Case5 G A) ∧
    (IsAlt 5 ↥G → qOf G ≤ qc 2 ∧ qhatOf G ≤ qc (3 / 2)) := by
  have hHyp := hK.hyp
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  refine ⟨?_, CFSG.Quasithin.H13.OrthFour.alternatingNatural_five_of_binaryOrthogonalFour_one hB,
    ?_, fun _ => burnsideK312_AS_q_le c hLG⟩
  · by_cases hGL : G = L
    · exact Or.inl ⟨(MulEquiv.subgroupCongr hGL).trans (burnsideK312_S1_eL c)⟩
    · right
      have hirr := burnsideK312_AS_irr hHyp.2.2.2
      have hN1 := burnsideK312_S1_normalizer hHyp c hGL
      have hshG : burnsideK312_sh c ∈ G := by
        rw [← hN1]
        exact burnsideK312_sh_normalizer c
      obtain ⟨hQ, hQq⟩ := burnsideK312_S1_Q c hshG
      obtain ⟨hQL, σ, e, he, hL⟩ := burnsideK312_S1_deleted hK c hQ hQq
      have hN2 : Subgroup.normalizer (L : Set (MulAut V)) =
          L ⊔ Subgroup.zpowers (burnsideK312_sh c) :=
        FFC.eq_of_card_mulAut_le (G := Subgroup.normalizer (L : Set (MulAut V)))
          (le_sup_left : L ≤ L ⊔ Subgroup.zpowers (burnsideK312_sh c))
          (sup_le Subgroup.le_normalizer
            (Subgroup.zpowers_le.mpr (burnsideK312_sh_normalizer c)))
          (fun h => hQL (le_of_le_of_eq (le_sup_right : Subgroup.zpowers (burnsideK312_sh c) ≤
            L ⊔ Subgroup.zpowers (burnsideK312_sh c)) h))
          (fun g hg l hl => (Subgroup.mem_normalizer_iff.mp hg l).mp hl)
          (fun g _ hc => burnsideK312_S1_cent c hirr hc) (burnsideK312_S1_haut c)
      exact ⟨(MulEquiv.subgroupCongr (hN1.symm.trans hN2)).trans σ⟩
  · intro _ A hA
    letI : Fintype F := Fintype.ofFinite F
    have hFc : Fintype.card F = 2 ^ 2 := by
      rw [← Nat.card_eq_fintype_card, c.field_card]
    let θL : ↥L ≃* SL(2, F) :=
      c.group_equiv.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
    have hZ := burnsideK312_S1_center c
    obtain ⟨Q, hQA, hQ, hQq, -⟩ := exists_quadratic_offender_le hK.elem2 hA
    obtain ⟨hQL, σ, e, he, hL⟩ := burnsideK312_S1_deleted hK c hQ hQq
    have hw : ∀ B, IsFFStarOffender G B → Nat.card B * Nat.card (fixV B) = Nat.card V :=
      fun B hB => B42L2.weight_eq_sl2 hK.elem2 hHyp hZ (n := 2) le_rfl hFc θL hB
    exact B42L2.case5_of_deleted hK.elem2 hHyp hZ (burnsideK312_S1_haut c) hw hQ hA hQA hQL σ e
      he hL

end S1


section AS4

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique

section


theorem as_K_3_1_2 : K_3_1_2 := by
  intro V _ _ G L hK s hPSL hB
  obtain ⟨F, _, _, _, ⟨c⟩⟩ := burnsideK312_coords hB
  have hHyp : B4Hyp G L := hK.hyp
  obtain ⟨hLG, hLn, -, -⟩ := FFC.b4hyp_data hHyp
  have hirr := burnsideK312_AS_irr hHyp.2.2.2
  obtain ⟨w1, w2, w3, w4⟩ := burnsideK312_witt c
  refine ⟨⟨F, inferInstance, inferInstance, inferInstance, c, w1, w2, w3, w4, ?_⟩, ?_, ?_, ?_⟩
  · intro T hT
    have hS := burnsideK312_AS_sylow_inf hLG hLn hT
    refine ⟨?_, fun t hN hNT htL hsq => ?_⟩
    · obtain ⟨g, hg⟩ := burnsideK312_AS_sylow c hS
      refine ⟨burnsideK312_sh (burnsideK312_conj c g), burnsideK312_sh_normalizer _, ?_,
        burnsideK312_sh_notMem _, by rw [sq]; exact burnsideK312_sh_sq _⟩
      rw [hg]
      exact burnsideK312_AS_sh_normalizes_Uc _
    · obtain ⟨g, hS', rfl⟩ := burnsideK312_AS_pair c hirr hS hN hsq htL hNT
      obtain ⟨a1, a2, a4, a5, a6, a7, a8, a9⟩ := burnsideK312_AS_TConj_conj c g
      refine ⟨a1, a2, ?_, a4, a5, a6, a7, a8, a9, fun _ => ?_⟩
      · have := burnsideK312_AS_fieldMatrix c
          (g * (Matrix.SpecialLinearGroup.map (burnsideK312_sg F s) g)⁻¹)
        rw [← burnsideK312_AS_sh_conj_eq] at this
        exact this
      · exact burnsideK312_AS_xblock c g hS'
  · intro hs1
    subst hs1
    exact burnsideK312_S1 hK c hB
  · intro hs1
    refine ⟨burnsideK312_AS_not_FF c hHyp hK.elem2 hs1, ?_, ?_, ?_⟩
    · intro T hT t hN hNT htL hsq
      exact burnsideK312_AS_C2 c hHyp hT hN hNT htL hsq
    · intro hodd
      exact burnsideK312_AS_q_odd c hHyp hodd
    · rintro ⟨t₀, ht₀G, ht₀L, hsq⟩
      exact ⟨burnsideK312_AS_q_outer c hHyp ht₀G ht₀L hsq, (burnsideK312_AS_q_le c hLG).2,
        fun T hT t htT htL hsq' => burnsideK312_AS_Qset c hHyp hT htT htL hsq'⟩
  · exact burnsideK312_AS_q_le c hLG

end

end AS4

end CFSG.ASVolI
