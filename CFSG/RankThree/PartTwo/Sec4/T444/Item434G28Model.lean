module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Quasithin.Background.SmithB42G2TenQ
public import CFSG.Quasithin.Background.SmithB42G2TenMat

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten CFSG.Quasithin.B42G2Id
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Open CFSG.Quasithin.Explicit CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.Timmesfeld.RankTwo

@[expose] def ix6 : Fin 6 → Ix3 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inr 2]

theorem ix6_bijective : Function.Bijective ix6 := by decide

@[expose] noncomputable def ixEquiv : Fin 6 ≃ Ix3 := Equiv.ofBijective ix6 ix6_bijective

theorem ixEquiv_apply (i : Fin 6) : ixEquiv i = ix6 i := rfl

section Cayley

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def cmat (τ : K ≃+* GF8) (g : ↥(cayleyGroup K)) :
    Matrix (Fin 6) (Fin 6) GF8 :=
  Matrix.of fun i j => τ (repQ g (ix6 i) (ix6 j))

theorem cmat_mul (τ : K ≃+* GF8) (g h : ↥(cayleyGroup K)) :
    cmat τ (g * h) = cmat τ g * cmat τ h := by
  ext i j
  simp only [cmat, Matrix.of_apply, map_mul, Matrix.mul_apply]
  rw [map_sum, ← ixEquiv.sum_comp]
  simp only [ixEquiv_apply, map_mul]

theorem cmat_one (τ : K ≃+* GF8) : cmat τ 1 = 1 := by
  ext i j
  simp only [cmat, Matrix.of_apply, map_one, Matrix.one_apply]
  have hinj : ix6 i = ix6 j ↔ i = j := ix6_bijective.1.eq_iff
  by_cases h : i = j
  · simp [h]
  · simp [h, hinj]

theorem cmat_injective (τ : K ≃+* GF8) : Function.Injective (cmat τ) := by
  intro g h hgh
  apply cayley_ext_Q
  intro w
  rw [← repQ_mulVec, ← repQ_mulVec]
  have : repQ g = repQ h := by
    ext a b
    obtain ⟨i, rfl⟩ := ix6_bijective.2 a
    obtain ⟨j, rfl⟩ := ix6_bijective.2 b
    have := congrFun (congrFun hgh i) j
    simp only [cmat, Matrix.of_apply] at this
    exact τ.injective this
  rw [this]

@[expose] noncomputable def cmatHom (τ : K ≃+* GF8) :
    ↥(cayleyGroup K) →* Matrix (Fin 6) (Fin 6) GF8 where
  toFun := cmat τ
  map_one' := cmat_one τ
  map_mul' := cmat_mul τ

omit [CharP K 2] in
theorem single_ix (j : Fin 6) : (Pi.single (ix6 j) (1 : K) : Ix3 → K) =
    q6 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0) (if j = 2 then 1 else 0)
      (if j = 3 then 1 else 0) (if j = 4 then 1 else 0) (if j = 5 then 1 else 0) := by
  funext k
  rcases k with k | k <;> fin_cases k <;> fin_cases j <;> simp [ix6, q6]

theorem cmat_zPos0 (τ : K ≃+* GF8) (c : K) : cmat τ (zPos 0 c) = rootMatrix 0 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zPos]
  rw [repQ_apply, single_ix j, g2Act_x0q]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zPos1 (τ : K ≃+* GF8) (c : K) : cmat τ (zPos 1 c) = rootMatrix 1 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zPos]
  rw [repQ_apply, single_ix j, g2Act_tv02]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zPos2 (τ : K ≃+* GF8) (c : K) : cmat τ (zPos 2 c) = rootMatrix 2 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zPos]
  rw [repQ_apply, single_ix j, g2Act_y2q]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zPos3 (τ : K ≃+* GF8) (c : K) : cmat τ (zPos 3 c) = rootMatrix 3 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zPos]
  rw [repQ_apply, single_ix j, g2Act_tv12]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zPos4 (τ : K ≃+* GF8) (c : K) : cmat τ (zPos 4 c) = rootMatrix 4 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zPos]
  rw [repQ_apply, single_ix j, g2Act_x1q]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zPos5 (τ : K ≃+* GF8) (c : K) : cmat τ (zPos 5 c) = rootMatrix 5 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zPos]
  rw [repQ_apply, single_ix j, g2Act_tv10]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zNeg0 (τ : K ≃+* GF8) (c : K) : cmat τ (zNeg 0 c) = rootMatrix 6 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zNeg]
  rw [repQ_apply, single_ix j, g2Act_y0q]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zNeg1 (τ : K ≃+* GF8) (c : K) : cmat τ (zNeg 1 c) = rootMatrix 7 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zNeg]
  rw [repQ_apply, single_ix j, g2Act_tv20]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zNeg2 (τ : K ≃+* GF8) (c : K) : cmat τ (zNeg 2 c) = rootMatrix 8 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zNeg]
  rw [repQ_apply, single_ix j, g2Act_x2q]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zNeg3 (τ : K ≃+* GF8) (c : K) : cmat τ (zNeg 3 c) = rootMatrix 9 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zNeg]
  rw [repQ_apply, single_ix j, g2Act_tv21]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zNeg4 (τ : K ≃+* GF8) (c : K) : cmat τ (zNeg 4 c) = rootMatrix 10 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zNeg]
  rw [repQ_apply, single_ix j, g2Act_y1q]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zNeg5 (τ : K ≃+* GF8) (c : K) : cmat τ (zNeg 5 c) = rootMatrix 11 (τ c) := by
  ext i j
  simp only [cmat, Matrix.of_apply, rootMatrix, rootEntry, zNeg]
  rw [repQ_apply, single_ix j, g2Act_tv01]
  fin_cases i <;> fin_cases j <;> simp [ix6, q6, rootEntries]

theorem cmat_zPos (τ : K ≃+* GF8) (j : Fin 6) (c : K) :
    cmat τ (zPos j c) = rootMatrix j.val (τ c) := by
  fin_cases j
  · exact cmat_zPos0 τ c
  · exact cmat_zPos1 τ c
  · exact cmat_zPos2 τ c
  · exact cmat_zPos3 τ c
  · exact cmat_zPos4 τ c
  · exact cmat_zPos5 τ c

theorem cmat_zNeg (τ : K ≃+* GF8) (j : Fin 6) (c : K) :
    cmat τ (zNeg j c) = rootMatrix (j.val + 6) (τ c) := by
  fin_cases j
  · exact cmat_zNeg0 τ c
  · exact cmat_zNeg1 τ c
  · exact cmat_zNeg2 τ c
  · exact cmat_zNeg3 τ c
  · exact cmat_zNeg4 τ c
  · exact cmat_zNeg5 τ c

@[expose] def rootVec (r : ℕ) : Fin 2 → ℤ :=
  if h : r % 12 < 6 then hexRoot ⟨r % 12, h⟩ else -hexRoot ⟨r % 12 - 6, by omega⟩

theorem cmat_zPsi_rootVec (τ : K ≃+* GF8) (r : ℕ) (c : K) :
    cmat τ (zPsi (rootVec r) c) = rootMatrix (r % 12) (τ c) := by
  unfold rootVec
  by_cases h : r % 12 < 6
  · simp only [h, dite_true]
    rw [zPsi_pos, cmat_zPos]
  · simp only [h, dite_false]
    rw [zPsi_neg, cmat_zNeg]
    have : r % 12 - 6 + 6 = r % 12 := by omega
    simp only [this]

end Cayley

structure G28Model (K : Type) [Field K] [Finite K] [CharP K 2] where
  τ : K ≃+* GF8
  ψ : ↥(adjointGroup .G2 K) →* ↥(cayleyGroup K)
  hψ : ∀ γ, IsRoot .G2 γ → ∀ c, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c
  hinj : Function.Injective ψ

namespace G28Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

@[expose] noncomputable def rho : ↥(adjointGroup .G2 K) →* Matrix (Fin 6) (Fin 6) GF8 :=
  (cmatHom M.τ).comp M.ψ

theorem rho_apply (g : ↥(adjointGroup .G2 K)) : M.rho g = cmat M.τ (M.ψ g) := rfl

theorem rho_injective : Function.Injective M.rho :=
  (cmat_injective M.τ).comp M.hinj

theorem isRoot_rootVec (r : ℕ) : IsRoot .G2 (rootVec r) := by
  unfold rootVec
  split_ifs with h
  · exact isRoot_hexRoot _
  · exact CFSG.LieType.Chevalley.IsRoot.neg (isRoot_hexRoot _)

@[expose] noncomputable def letterElt (n : ℕ) : ↥(adjointGroup .G2 K) :=
  xPar (rootOperatorFamily .G2) (rootVec (n / 8)) (M.τ.symm (GF8.ofNat' (n % 8)))

theorem rho_letterElt (n : ℕ) : M.rho (M.letterElt n) = decode (letterCode n) := by
  have hlt : (n / 8) % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hn8 : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hτ : M.τ (M.τ.symm (GF8.ofNat' (n % 8))) = GF8.ofNat' (n % 8) := M.τ.apply_symm_apply _
  rw [letterCode, decode_rootCode _ _ hlt hn8, rho_apply, letterElt,
    M.hψ _ (isRoot_rootVec _), cmat_zPsi_rootVec, hτ]

@[expose] noncomputable def wordElt (w : List ℕ) : ↥(adjointGroup .G2 K) :=
  (w.map M.letterElt).prod

theorem rho_mul_prod (w : List ℕ) : ∀ (g : ↥(adjointGroup .G2 K)) (A : Array ℕ), Valid A →
    M.rho g = decode A →
    M.rho (g * (w.map M.letterElt).prod) =
      decode (w.foldl (fun A n => mulCode A (letterCode n)) A) := by
  induction w with
  | nil =>
    intro g A _ hg
    simpa using hg
  | cons n w ih =>
    intro g A hA hg
    rw [List.map_cons, List.prod_cons, ← mul_assoc, List.foldl_cons]
    refine ih (g * M.letterElt n) (mulCode A (letterCode n))
      (valid_mulCode hA (valid_letterCode n)) ?_
    rw [map_mul, hg, rho_letterElt, decode_mulCode hA (valid_letterCode n)]

theorem rho_wordElt (w : List ℕ) : M.rho (M.wordElt w) = decode (wordCode w) := by
  have := M.rho_mul_prod w 1 idCode valid_idCode (by rw [map_one, decode_idCode])
  simpa [wordElt, wordCode] using this

theorem rho_pow (g : ↥(adjointGroup .G2 K)) {A : Array ℕ} (hA : Valid A)
    (hg : M.rho g = decode A) (k : ℕ) :
    Valid (powCode A k) ∧ M.rho (g ^ k) = decode (powCode A k) := by
  induction k with
  | zero => exact ⟨valid_idCode, by simp [powCode, decode_idCode]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨valid_mulCode h1 hA, ?_⟩
    rw [pow_succ, map_mul, h2, hg, powCode, decode_mulCode h1 hA]

end G28Model

theorem exists_model {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 8) :
    Nonempty (G28Model K) := by
  obtain ⟨ψ, hψ, -, hker⟩ := exists_adjointGroup_hom_cayleyGroup (K := K) (f := 3)
    (by rw [hK]; norm_num) (by norm_num)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker]
    exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card GF8 := by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl
  exact ⟨⟨FiniteField.ringEquivOfCardEq hcard, ψ, hψ, hinj⟩⟩

end CFSG.RankThree.PartTwo.Sec4.Item434G28