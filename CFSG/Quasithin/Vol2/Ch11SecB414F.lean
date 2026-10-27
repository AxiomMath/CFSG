module

public import CFSG.Quasithin.Vol2.Ch11SecB414E
public import CFSG.Quasithin.Background.SmithB45SL3Label

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open CFSG.QuasithinUnique.Setup.X7a CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {U : Type} [AddCommGroup U]
  [Module (ZMod 2) U]

theorem label_cases (a b : Fin 2 → Bool) (hne : a ≠ zeros 2 ∨ b ≠ zeros 2)
    (h3 : 3 ∣ mBits a + 2 * mBits b) :
    (a = ![true, false] ∧ b = ![true, false]) ∨ (a = ![false, true] ∧ b = ![false, true]) ∨
      (a = ![true, true] ∧ b = ![false, false]) ∨ (a = ![false, false] ∧ b = ![true, true]) ∨
      (a = ![true, true] ∧ b = ![true, true]) := by
  obtain ⟨a0, a1, rfl⟩ : ∃ a0 a1, a = ![a0, a1] := ⟨a 0, a 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨b0, b1, rfl⟩ : ∃ b0 b1, b = ![b0, b1] := ⟨b 0, b 1, by funext i; fin_cases i <;> rfl⟩
  revert hne h3
  revert a0 a1 b0 b1
  decide

omit [Fintype F] in
theorem nonempty_equiv_adj :
    Nonempty ((matRep (tensorRep (F := F) F ![true, false] ![true, false])).Equiv
      (matRep (adjRep (F := F) F 0))) :=
  B42SL3.nonempty_equiv_locRep (F := F) (fun i : Fin 2 => (![true, false] i, ![true, false] i))
    (fun i => (i : ℕ)) (i₀ := 0) (fun p hp => by
      fin_cases p
      · exact absurd rfl hp
      · rfl)

theorem const_two (x y : Bool) (h : x = y) : (![x, y] : Fin 2 → Bool) = fun _ => x := by
  subst h
  funext i
  fin_cases i <;> rfl

omit [Fintype F] in
theorem card_eig_one_A [DecidableEq F] {ω : Fˣ} (hω : orderOf ω = 3) :
    Fintype.card {x : TIdx 2 ![true, false] ![true, false] //
      ∏ i : Fin 2, locD (![true, false] i) (![true, false] i) (i : ℕ) 1 ω (x i) = 1} = 2 := by
  have hω3 : (ω : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have key : ∀ x : TIdx 2 ![true, false] ![true, false],
      ∏ i : Fin 2, locD (![true, false] i) (![true, false] i) (i : ℕ) 1 ω (x i) =
        (ω : F) ^ locE true true (x 0) := by
    intro x
    rw [Fin.prod_univ_two]
    show locD true true 0 1 ω (x 0) * locD false false 1 1 ω (x 1) = _
    rw [show locD false false 1 1 ω (x 1) = 1 from rfl, mul_one]
    exact locD_zero_one true true hω3 (x 0)
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun x => 3 ∣ locE true true (x 0))
    fun x => by rw [key x, ← hω, orderOf_dvd_iff_pow_eq_one, ← Units.val_pow_eq_pow_val,
      Units.val_eq_one])]
  decide

theorem injective_of_label_A (hF : Fintype.card F = 4) [Finite U]
    {ρ : Representation (ZMod 2) SL(3, F) U} (hirr : ρ.IsIrreducible)
    {H : (TIdx 2 ![true, false] ![true, false] → F) →+ U}
    (hH : ∀ g v, H (tensorRep (F := F) F ![true, false] ![true, false] g *ᵥ v) = ρ g (H v))
    (hsurj : Function.Surjective H) {ω : Fˣ} (hω : orderOf ω = 3)
    (hdiv : ∃ m, Nat.card U = Nat.card {u // ρ (dT 1 ω) u = u} * 16 ^ m) :
    Function.Injective H := by
  by_contra hinj
  let _ : DecidableEq F := Classical.decEq F
  have : Nontrivial U := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
  have hF' : Fintype.card F = 2 ^ 2 := by
    rw [hF]
    norm_num
  have hR := ((tensorRep_absolutely_irreducible_and_distinct F hF' (by norm_num)).1
    ![true, false] ![true, false]).1
  obtain ⟨hU, hC⟩ := card_of_not_injective hF hR hH hsurj hinj (dT 1 ω)
  rw [tensorRep_dT, card_fixed_diagonal, card_eig_one_A hω, hF] at hC
  have h8 : Fintype.card (TIdx 2 ![true, false] ![true, false]) = 8 := by decide
  rw [h8] at hU
  have hCU : Nat.card {u // ρ (dT 1 ω) u = u} = 2 ^ 2 := by
    apply Nat.pow_left_injective two_ne_zero
    simp only
    rw [hC]
    norm_num
  obtain ⟨m, hm⟩ := hdiv
  rw [hU, hCU, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add] at hm
  have := Nat.pow_right_injective (le_refl 2) hm
  omega

theorem exists_adjEquiv_of_sub (hF : Fintype.card F = 4) [Finite U] {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (hirr : ρ.IsIrreducible) (W₀ : Subrepresentation (matRep (PFrep ρ bas)))
    (e₀ : W₀.toRepresentation.Equiv (matRep (tensorRep (F := F) F ![true, false] ![true, false])))
    {ω : Fˣ} (hω : orderOf ω = 3)
    (hdiv : ∃ m, Nat.card U = Nat.card {u // ρ (dT 1 ω) u = u} * 16 ^ m) :
    ∃ H : (Fin 8 → F) ≃+ U, ∀ g v, H (adjRep F 0 g *ᵥ v) = ρ g (H v) := by
  have hF' : Fintype.card F = 2 ^ 2 := by
    rw [hF]
    norm_num
  have : Nonempty (TIdx 2 ![true, false] ![true, false]) :=
    ⟨fun _ => ⟨0, B42SL3.locDim_pos _ _⟩⟩
  obtain ⟨H, hH, hH0⟩ := exists_traceHom hF' ρ bas W₀ e₀
  have hsurj := traceHom_surjective hirr hH hH0
  have hinj := injective_of_label_A hF hirr hH hsurj hω hdiv
  obtain ⟨e₁⟩ := nonempty_equiv_adj (F := F)
  refine ⟨e₁.symm.toLinearEquiv.toAddEquiv.trans (AddEquiv.ofBijective H ⟨hinj, hsurj⟩),
    fun g v => ?_⟩
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e₁.symm.toIntertwiningMap g v
  show H (e₁.symm (adjRep F 0 g *ᵥ v)) = ρ g (H (e₁.symm v))
  rw [← hH]
  exact congrArg H h1

theorem exists_adjEquiv (hF : Fintype.card F = 4) [Finite U]
    (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible) (hnt : ∃ x, ρ x ≠ 1)
    {ω : Fˣ} (hω : orderOf ω = 3) (hcen : ρ (dT ω ω) = 1)
    (hdiv : ∃ m, Nat.card U = Nat.card {u // ρ (dT 1 ω) u = u} * 16 ^ m) :
    ∃ H : (Fin 8 → F) ≃+ U, ∀ g v, H (adjRep F 0 g *ᵥ v) = ρ g (H v) := by
  have hF' : Fintype.card F = 2 ^ 2 := by
    rw [hF]
    norm_num
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨a, b, Wj, hne, -, heq, -, -, -⟩ :=
    B45SL3.exists_label_pkg hF' (by norm_num) ρ (Module.finBasis (ZMod 2) U) hirr hnt
  have h3 : 3 ∣ mBits a + 2 * mBits b := by
    obtain ⟨e⟩ := heq 0
    exact three_dvd_of_center a b hω (eq_one_of_sub ρ _ (Wj 0) e hcen)
  have hbad : ∀ α β : Bool, a = (fun _ => α) → b = (fun _ => β) →
      (∀ m, Fintype.card (TIdx 2 (fun _ => α) (fun _ => β)) ≠
        Fintype.card {x : TIdx 2 (fun _ => α) (fun _ => β) //
          3 ∣ locE α β (x 0) + 2 * locE α β (x 1)} + 4 * m) → False := by
    rintro α β rfl rfl hc
    obtain ⟨e⟩ := heq 0
    have e' : (Wj 0).toRepresentation.Equiv
        (matRep (tensorRep (F := F) F (fun _ => α) (fun _ => β))) := e
    have : Nonempty (TIdx 2 (fun _ => α) (fun _ => β)) :=
      ⟨fun _ => ⟨0, B42SL3.locDim_pos α β⟩⟩
    obtain ⟨H, hH, hH0⟩ := exists_traceHom hF' ρ _ (Wj 0) e'
    exact false_of_stable_label α β hF hirr hH (traceHom_surjective hirr hH hH0) hω hdiv hc
  rcases label_cases a b hne h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · obtain ⟨e⟩ := heq 0
    exact exists_adjEquiv_of_sub hF ρ _ hirr (Wj 0) e hω hdiv
  · obtain ⟨e⟩ := heq 1
    have hs : (shiftBits 2)^[1] ![false, true] = ![true, false] := by
      funext i
      fin_cases i <;> rfl
    rw [hs] at e
    exact exists_adjEquiv_of_sub hF ρ _ hirr (Wj 1) e hω hdiv
  · refine (hbad true false (const_two _ _ rfl) (const_two _ _ rfl) fun m => ?_).elim
    have h1 : Fintype.card (TIdx 2 (fun _ => true) (fun _ => false)) = 9 := by decide
    have h2 : Fintype.card {x : TIdx 2 (fun _ => true) (fun _ => false) //
        3 ∣ locE true false (x 0) + 2 * locE true false (x 1)} = 3 := by decide
    omega
  · refine (hbad false true (const_two _ _ rfl) (const_two _ _ rfl) fun m => ?_).elim
    have h1 : Fintype.card (TIdx 2 (fun _ => false) (fun _ => true)) = 9 := by decide
    have h2 : Fintype.card {x : TIdx 2 (fun _ => false) (fun _ => true) //
        3 ∣ locE false true (x 0) + 2 * locE false true (x 1)} = 3 := by decide
    omega
  · refine (hbad true true (const_two _ _ rfl) (const_two _ _ rfl) fun m => ?_).elim
    have h1 : Fintype.card (TIdx 2 (fun _ => true) (fun _ => true)) = 64 := by decide
    have h2 : Fintype.card {x : TIdx 2 (fun _ => true) (fun _ => true) //
        3 ∣ locE true true (x 0) + 2 * locE true true (x 1)} = 22 := by decide
    omega

end CFSG.Quasithin.H13.Ch4.B414
