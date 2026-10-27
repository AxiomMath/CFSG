module

public import CFSG.Quasithin.EmptyFaithful.LRed5Twist
public import CFSG.Quasithin.Background.FFC4Pair

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

namespace SL2Twist

section Schur

variable {F : Type*} [Field F]

@[expose] def e12 (a : F) : Matrix (Fin 2) (Fin 2) F := !![1, a; 0, 1]

@[expose] def e21 (a : F) : Matrix (Fin 2) (Fin 2) F := !![1, 0; a, 1]

theorem e12_mulVec (a : F) (x : Fin 2 → F) : e12 a *ᵥ x = ![x 0 + a * x 1, x 1] := by
  funext i
  fin_cases i <;> simp [e12, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem e21_mulVec (a : F) (x : Fin 2 → F) : e21 a *ᵥ x = ![x 0, a * x 0 + x 1] := by
  funext i
  fin_cases i <;> simp [e21, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det_e12 (a : F) : (e12 a).det = 1 := by simp [e12, Matrix.det_fin_two]

theorem det_e21 (a : F) : (e21 a).det = 1 := by simp [e21, Matrix.det_fin_two]

theorem exists_scalar_of_commute (φ : (Fin 2 → F) →+ (Fin 2 → F))
    (h12 : ∀ a x, φ (e12 a *ᵥ x) = e12 a *ᵥ φ x)
    (h21 : ∀ a x, φ (e21 a *ᵥ x) = e21 a *ᵥ φ x) :
    ∃ c : F, ∀ x, φ x = c • x := by
  have hA : ∀ t : F, φ ![t, 0] 1 = 0 := by
    intro t
    have h := congrFun (h12 1 ![t, 0]) 0
    rw [e12_mulVec, e12_mulVec] at h
    simpa using h
  have hB : ∀ t : F, φ ![0, t] 0 = 0 := by
    intro t
    have h := congrFun (h21 1 ![0, t]) 1
    rw [e21_mulVec, e21_mulVec] at h
    simpa using h
  have hC : ∀ a y : F, φ ![a * y, 0] 0 = a * φ ![0, y] 1 := by
    intro a y
    have h := congrFun (h12 a ![0, y]) 0
    rw [e12_mulVec, e12_mulVec] at h
    have e : (![(![0, y] : Fin 2 → F) 0 + a * (![0, y] : Fin 2 → F) 1, (![0, y] : Fin 2 → F) 1] :
        Fin 2 → F) = ![a * y, 0] + ![0, y] := by
      funext i
      fin_cases i <;> simp
    rw [e, map_add] at h
    simpa [hA, hB] using h
  refine ⟨φ ![0, 1] 1, fun x => ?_⟩
  have hx : x = ![x 0, 0] + ![0, x 1] := by
    funext i
    fin_cases i <;> simp
  have h0 : φ ![x 0, 0] 0 = φ ![0, 1] 1 * x 0 := by
    have := hC (x 0) 1
    rw [mul_one] at this
    rw [this, mul_comm]
  have h1 : φ ![0, x 1] 1 = φ ![0, 1] 1 * x 1 := by
    have h1' := hC 1 (x 1)
    have h2' := hC (x 1) 1
    simp only [one_mul] at h1'
    simp only [mul_one] at h2'
    rw [← h1', h2', mul_comm]
  funext i
  conv_lhs => rw [hx]
  rw [map_add]
  fin_cases i
  · simp [hB, h0]
  · simp [hA, h1]

end Schur

section Twist

variable {V : Type} [CommGroup V]

theorem inner_of_natural_sl2_four {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) {π : ↥(StatedSL 2 F) →* ↥L}
    (hπ : (FFModel.nat (StatedSL 2 F)).RealizesVia L U Z π) {ω s : MulAut V}
    (hωU : ∀ u ∈ U, ω u ∈ U) (hωU' : ∀ u ∈ U, ω⁻¹ u ∈ U) (hωZ : ∀ z ∈ Z, ω z ∈ Z)
    (hωZ' : ∀ z ∈ Z, ω⁻¹ z ∈ Z) (hωL : ∀ l ∈ L, ω * l = l * ω)
    (hωf : ∀ u ∈ U, ω u * u⁻¹ ∈ Z → u ∈ Z)
    (hsU : ∀ u ∈ U, s u ∈ U) (hsU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hsZ : ∀ z ∈ Z, s z ∈ Z)
    (hsZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z) (hsω : ω * s = s * ω) (hsL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) :
    ∃ l ∈ L, ∀ x ∈ L, s * x * s⁻¹ = l * x * l⁻¹ := by
  classical
  have hc2 : CharP F 2 := FFC.charP_two_of_card_pow (n := 2) (by rw [hF]; norm_num)
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  obtain ⟨Ω, hΩ⟩ := LRed5.exists_equiv_of_section hfs hfk hωU hωU' hωZ hωZ'
  obtain ⟨Θ, hΘ⟩ := LRed5.exists_equiv_of_section hfs hfk hsU hsU' hsZ hsZ'
  set eSL := specialLinearGroupEquivStatedSL 2 F with heSL
  let addOf : Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → F) →
      (Fin 2 → F) →+ (Fin 2 → F) := fun Φ =>
    { toFun := fun x => Multiplicative.toAdd (Φ (Multiplicative.ofAdd x))
      map_zero' := by simp
      map_add' := fun x y => by simp [ofAdd_add] }
  have haddOf : ∀ Φ x, addOf Φ x = Multiplicative.toAdd (Φ (Multiplicative.ofAdd x)) :=
    fun _ _ => rfl
  have hact : ∀ (γ : ↥(StatedSL 2 F)) (u : ↥U),
      natAct (StatedSL 2 F) γ (f u) = f ⟨((π γ : ↥L) : MulAut V) u, hπ.2.2.2.1 (π γ) u u.2⟩ :=
    fun γ u => (hfe γ u _).symm
  have hint : ∀ (Φ : Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → F)) (t : MulAut V)
      (htU : ∀ u ∈ U, t u ∈ U), (∀ u : ↥U, Φ (f u) = f ⟨t u, htU u u.2⟩) →
      ∀ (γ γ' : ↥(StatedSL 2 F)),
        ((π γ' : ↥L) : MulAut V) = t * (π γ : ↥L) * t⁻¹ →
        ∀ m, Φ (natAct (StatedSL 2 F) γ m) = natAct (StatedSL 2 F) γ' (Φ m) := by
    intro Φ t htU hΦt γ γ' hγ m
    obtain ⟨u, rfl⟩ := hfs m
    rw [hact, hΦt, hΦt, hact]
    congr 1
    apply Subtype.ext
    show t (((π γ : ↥L) : MulAut V) (u : V)) = ((π γ' : ↥L) : MulAut V) (t (u : V))
    rw [hγ]
    simp [MulAut.mul_apply]
  have hnatAct : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (x : Fin 2 → F),
      Multiplicative.toAdd (natAct (StatedSL 2 F) (eSL A) (Multiplicative.ofAdd x)) =
        (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x := by
    intro A x
    simp only [natAct, toAdd_ofAdd]
    rw [heSL, specialLinearGroupEquivStatedSL_coe]
  have hΩc : ∀ γ m, Ω (natAct (StatedSL 2 F) γ m) = natAct (StatedSL 2 F) γ (Ω m) := by
    intro γ m
    refine hint Ω ω hωU hΩ γ γ ?_ m
    rw [hωL _ (π γ).2, mul_inv_cancel_right]
  have hcomm_mat : ∀ (Φ : Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → F)),
      (∀ γ m, Φ (natAct (StatedSL 2 F) γ m) = natAct (StatedSL 2 F) γ (Φ m)) →
      ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) x,
        addOf Φ ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ
          addOf Φ x := by
    intro Φ hΦ A x
    rw [haddOf, haddOf, ← hnatAct, ← hnatAct, ofAdd_toAdd, hΦ, ofAdd_toAdd]
  obtain ⟨c, hc⟩ := exists_scalar_of_commute (addOf Ω)
    (fun a x => hcomm_mat Ω hΩc ⟨e12 a, det_e12 a⟩ x)
    (fun a x => hcomm_mat Ω hΩc ⟨e21 a, det_e21 a⟩ x)
  obtain ⟨u₀, hu₀⟩ := hfs (Multiplicative.ofAdd ![1, 0])
  have hu₀Z : (u₀ : V) ∉ Z := by
    intro h
    have h1 := (hfk u₀).2 h
    rw [hu₀] at h1
    have h2 := congrArg (fun m : Multiplicative (Fin 2 → F) => Multiplicative.toAdd m 0) h1
    simp at h2
  have hc1 : c ≠ 1 := by
    intro h1
    apply hu₀Z
    refine hωf _ u₀.2 ?_
    have h2 : f ⟨ω u₀, hωU _ u₀.2⟩ = f u₀ := by
      rw [← hΩ]
      apply Multiplicative.toAdd.injective
      have := hc (Multiplicative.toAdd (f u₀))
      rw [h1, one_smul] at this
      simpa [haddOf] using this
    have h3 : f (⟨ω u₀, hωU _ u₀.2⟩ * u₀⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact (hfk _).1 h3
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu₀Z
    have h2 : Ω (f u₀) = 1 := by
      apply Multiplicative.toAdd.injective
      have := hc (Multiplicative.toAdd (f u₀))
      rw [h0, zero_smul] at this
      simpa [haddOf] using this
    have h3 := Ω.injective (h2.trans (map_one Ω).symm)
    exact (hfk u₀).1 h3
  have hF4 : ∀ μ : F, μ = 0 ∨ μ = 1 ∨ μ = c ∨ μ = c + 1 := by
    have : Fintype F := Fintype.ofFinite F
    have hne1 : (c + 1 : F) ≠ 0 := by
      intro h
      apply hc1
      have : c = -1 := eq_neg_of_add_eq_zero_left h
      rw [this, CharTwo.neg_eq]
    have hne2 : (c + 1 : F) ≠ 1 := fun h => hc0 (add_eq_right.mp h)
    have hne3 : (c + 1 : F) ≠ c := fun h => (one_ne_zero : (1 : F) ≠ 0) (add_eq_left.mp h)
    have hcard : ({0, 1, c, c + 1} : Finset F).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne3.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hc1.symm, hne2.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨zero_ne_one, hc0.symm, hne1.symm⟩
    have hu : ({0, 1, c, c + 1} : Finset F) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard, ← Nat.card_eq_fintype_card, hF])
    intro μ
    have hμ : μ ∈ ({0, 1, c, c + 1} : Finset F) := by rw [hu]; exact Finset.mem_univ μ
    simpa using hμ
  have hΘΩ : ∀ x, addOf Θ (c • x) = c • addOf Θ x := by
    intro x
    obtain ⟨u, hu⟩ := hfs (Multiplicative.ofAdd x)
    have e1 : c • x = addOf Ω x := (hc x).symm
    rw [e1, (hc (addOf Θ x)).symm]
    simp only [haddOf, ofAdd_toAdd]
    rw [← hu, hΩ, hΘ, hΘ, hΩ]
    congr 2
    apply Subtype.ext
    show s (ω u) = ω (s u)
    have := congrArg (fun φ : MulAut V => φ (u : V)) hsω
    simpa [MulAut.mul_apply] using this.symm
  have hlin : ∀ (μ : F) x, addOf Θ (μ • x) = μ • addOf Θ x := by
    intro μ x
    rcases hF4 μ with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact hΘΩ x
    · rw [add_smul, one_smul, map_add, hΘΩ, add_smul, one_smul]
  set M : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => addOf Θ (Pi.single j 1) i with hM
  have hMx : ∀ x, addOf Θ x = M *ᵥ x := by
    intro x
    have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → F) + x 1 • (Pi.single 1 1 : Fin 2 → F) := by
      funext i
      fin_cases i <;> simp
    conv_lhs => rw [hx]
    rw [map_add, hlin, hlin]
    funext i
    simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hΘc : ∀ (γ γ' : ↥(StatedSL 2 F)),
      ((π γ' : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹ →
      M * (((γ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) =
        (((γ' : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * M := by
    intro γ γ' hγ
    apply Matrix.ext_of_mulVec_single
    intro j
    have h1 := congrArg Multiplicative.toAdd
      (hint Θ s hsU hΘ γ γ' hγ (Multiplicative.ofAdd (Pi.single j 1)))
    simp only [natAct, toAdd_ofAdd] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hMx, ← hMx]
    simpa [haddOf, natAct] using h1
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hx0
    have h1 : addOf Θ x = 0 := by rw [hMx, hx]
    have h2 : Θ (Multiplicative.ofAdd x) = 1 := by
      apply Multiplicative.toAdd.injective
      simpa [haddOf] using h1
    have h3 := Θ.injective (h2.trans (map_one Θ).symm)
    simpa using congrArg Multiplicative.toAdd h3
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' M.det
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [hμ, zero_mul])
  have hdet0 : (μ⁻¹ • M).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hμ]
    field_simp
  set M₀ : Matrix.SpecialLinearGroup (Fin 2) F := ⟨μ⁻¹ • M, hdet0⟩ with hM₀
  refine ⟨π (eSL M₀), (π (eSL M₀)).2, fun x hx => ?_⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 2 F), π γ = ⟨x, hx⟩ := hπ.1 ⟨x, hx⟩
  obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(StatedSL 2 F), π γ' = ⟨s * x * s⁻¹, hsL x hx⟩ :=
    hπ.1 ⟨s * x * s⁻¹, hsL x hx⟩
  have hxγ : x = ((π γ : ↥L) : MulAut V) := (congrArg Subtype.val hγ).symm
  have hsxγ' : s * x * s⁻¹ = ((π γ' : ↥L) : MulAut V) := (congrArg Subtype.val hγ').symm
  have hrel := hΘc γ γ' (by rw [← hsxγ', hxγ])
  have hγeq : γ' = eSL M₀ * γ * (eSL M₀)⁻¹ := by
    obtain ⟨A, rfl⟩ := eSL.surjective γ
    obtain ⟨A', rfl⟩ := eSL.surjective γ'
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    have hrel' : (M₀ : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
        (A' : Matrix (Fin 2) (Fin 2) F) * (M₀ : Matrix (Fin 2) (Fin 2) F) := by
      have e1 := hrel
      rw [heSL, specialLinearGroupEquivStatedSL_coe, specialLinearGroupEquivStatedSL_coe] at e1
      show (μ⁻¹ • M) * (A : Matrix (Fin 2) (Fin 2) F) = (A' : Matrix (Fin 2) (Fin 2) F) * (μ⁻¹ • M)
      rw [Matrix.smul_mul, e1, Matrix.mul_smul]
    have h2 : A' * M₀ = M₀ * A := Subtype.ext hrel'.symm
    calc A' = A' * M₀ * M₀⁻¹ := by group
      _ = M₀ * A * M₀⁻¹ := by rw [h2]
  rw [hsxγ', hxγ, hγeq, map_mul, map_mul, map_inv]
  rfl

end Twist

end SL2Twist

end CFSG.Quasithin
