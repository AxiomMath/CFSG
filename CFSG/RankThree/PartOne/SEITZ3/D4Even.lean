module

public import CFSG.RankThree.PartOne.SEITZ3.NatArith
public import CFSG.RankThree.PartOne.SEITZ3.PlanePair
public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.RankThree.PartOne.CTP.SeitzFineD4

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.K1214
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Arith

theorem d4_index_arith {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ q + 1) :
    ¬ p ∣ q ^ 8 * (q ^ 8 + q ^ 4 + 1) ∧ ¬ q ^ 8 * (q ^ 8 + q ^ 4 + 1) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : (q : ZMod p) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (q + 1) p).2 hpq
    push_cast at this
    exact this
  have h3 : ((q ^ 8 * (q ^ 8 + q ^ 4 + 1) : ℕ) : ZMod p) = ((3 : ℕ) : ZMod p) := by
    push_cast
    linear_combination ((q : ZMod p) ^ 15 - (q : ZMod p) ^ 14 + (q : ZMod p) ^ 13 -
      (q : ZMod p) ^ 12 + 2 * (q : ZMod p) ^ 11 - 2 * (q : ZMod p) ^ 10 +
      2 * (q : ZMod p) ^ 9 - 2 * (q : ZMod p) ^ 8 + 3 * (q : ZMod p) ^ 7 -
      3 * (q : ZMod p) ^ 6 + 3 * (q : ZMod p) ^ 5 - 3 * (q : ZMod p) ^ 4 +
      3 * (q : ZMod p) ^ 3 - 3 * (q : ZMod p) ^ 2 + 3 * (q : ZMod p) - 3) * h0
  constructor
  · intro h
    have h' : ((q ^ 8 * (q ^ 8 + q ^ 4 + 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [h3] at h'
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 3 p).1 h')
    omega
  · intro h
    have h' := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    rw [h3] at h'
    have h'' : 3 ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff 3 1 p).1 h'
    have := Nat.le_of_dvd (by norm_num) ((Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 3)).1 h''.symm)
    omega

end Arith

section Max

@[expose] def Max3D4A1A1Big : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → 4 ≤ q.card →
    ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], IsoLie K (.trialityD4 q) →
    ∃ (A B : Subgroup K) (F₃ F₁ : Type) (_ : Field F₃) (_ : Field F₁),
      Nat.card F₃ = q.card ^ 3 ∧ Nat.card F₁ = q.card ∧
      Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 2) F₃) ∧
      Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) F₁) ∧
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ A ⊓ B = ⊥ ∧
      ∀ N : Subgroup K, A ⊔ B ≤ N → N = A ⊔ B ∨ N = ⊤

end Max

section Reduction

theorem card_isoLie_trialityD4
    {q : TauCeti.PrimePower} (hq : q.p = 2) {K : Type} [Group K]
    (hiso : IsoLie K (.trialityD4 q)) :
    Nat.card K = q.card ^ 12 * (q.card ^ 2 - 1) * (q.card ^ 6 - 1) *
      (q.card ^ 8 + q.card ^ 4 + 1) := by
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := CTP.exists_trialityD4_model hq hiso
  have hQ : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq]
  have h := (triality_both_orientations_exact_finite_order 2 q.exponent Nat.prime_two
    q.exponent_pos X hX 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  rw [Nat.card_congr e.toEquiv, h, hQ]

theorem closure_cenGen_trialityD4_eq_top
    (hmax : Max3D4A1A1Big) {q : TauCeti.PrimePower}
    (hq : q.p = 2) {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hiso : IsoLie K (.trialityD4 q)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q.card + 1) (E₁ : Subgroup K) (hE₁p : ∀ x ∈ E₁, x ^ p = 1)
    (hE₁c : Nat.card E₁ = p ^ 2) : Subgroup.closure (cenGen E₁) = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h4 : 4 ≤ q.card := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    omega
  obtain ⟨A, B, F₃, F₁, _, _, hF₃f, hF₁f, ⟨eA⟩, ⟨eB⟩, hcomm, hAB, hmaxAB⟩ :=
    hmax q hq h4 K hiso
  have hQ : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq]
  have hQ2 : 2 ≤ q.card := by
    rw [hQ]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
  obtain ⟨X, _, _, σ, hX, hσ, hσ3, ⟨e⟩⟩ := CTP.exists_trialityD4_model hq hiso
  have hpq' : p ∣ 2 ^ q.exponent + 1 := by rwa [hQ] at hpq
  have hshape : SylowShape p 2 ((2 ^ q.exponent + 1).factorization p) K :=
    (CFSG.RankThree.PartOne.K128.sylowShape_D4_qplus (ℓ := 2) q.exponent_pos X hX σ hσ hp hp5
      hpq').of_mulEquiv e
  have hKcard := card_isoLie_trialityD4 hq hiso
  have : Finite F₃ := Nat.finite_of_card_ne_zero (by rw [hF₃f]; positivity)
  have : Finite F₁ := Nat.finite_of_card_ne_zero (by rw [hF₁f]; positivity)
  have hcardA : Nat.card A = q.card ^ 3 * ((q.card ^ 3) ^ 2 - 1) := by
    rw [Nat.card_congr eA.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF₃f]
  have hcardB : Nat.card B = q.card * (q.card ^ 2 - 1) := by
    rw [Nat.card_congr eB.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF₁f]
  have hcardM : Nat.card ↥(A ⊔ B) = (q.card ^ 3 * ((q.card ^ 3) ^ 2 - 1)) *
      (q.card * (q.card ^ 2 - 1)) := by
    rw [card_sup_pair hAB hcomm, hcardA, hcardB]
  have hidx : (A ⊔ B).index = q.card ^ 8 * (q.card ^ 8 + q.card ^ 4 + 1) := by
    have h1 := Subgroup.index_mul_card (A ⊔ B)
    rw [hcardM, hKcard] at h1
    have hpos : 0 < (q.card ^ 3 * ((q.card ^ 3) ^ 2 - 1)) * (q.card * (q.card ^ 2 - 1)) := by
      have h4 : 4 ≤ q.card ^ 2 := by nlinarith
      have h64 : 4 ≤ (q.card ^ 3) ^ 2 := by
        have : 4 ≤ q.card ^ 3 := by nlinarith [pow_pos (by omega : 0 < q.card) 3]
        nlinarith
      have h5 : 0 < q.card ^ 2 - 1 := by omega
      have h6 : 0 < (q.card ^ 3) ^ 2 - 1 := by omega
      positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    have e6 : (q.card ^ 3) ^ 2 = q.card ^ 6 := by rw [← pow_mul]
    rw [e6]
    ring
  obtain ⟨hnd, hmod⟩ := d4_index_arith hp hp5 hpq
  rw [← hidx] at hnd hmod
  have hQpq : p ∣ q.card ^ 2 - 1 := by
    rw [sq_sub_one_eq_mul (by omega)]
    exact Dvd.dvd.mul_right hpq _
  have hQ3 : p ∣ q.card ^ 3 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow q.card 1 (by decide : Odd 3)
    simpa using hpq.trans h
  have hpA : p ∣ Nat.card A := by
    rw [hcardA, sq_sub_one_eq_mul (Nat.one_le_pow _ _ (by omega))]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hQ3 _) _
  have hpB : p ∣ Nat.card B := by
    rw [hcardB]
    exact Dvd.dvd.mul_left hQpq _
  exact closure_cenGen_eq_top_of_pair A B hAB hcomm hpA hpB hshape hmaxAB hnd hmod E₁ hE₁p hE₁c

section Assembly

theorem extSeitzAtInnerFor_trialityD4_qplus
    (hmax : Max3D4A1A1Big)
    {q : TauCeti.PrimePower}
    (hq : q.p = 2) : CTP.ExtSeitzAtInnerFor (.trialityD4 q) fun p => p ∣ q.card + 1 := by
  intro K _ _ _ hnab hiso p hp hp5 _ hpq E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  refine CTP.closure_fixUnion_eq_top_of_inner_equiv hnab (MulEquiv.refl K) (p := p) ?_ E hcard
    hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  exact closure_cenGen_trialityD4_eq_top hmax hq hiso hp hp5 hpq E₁
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx) hcard₁

end Assembly

end Reduction

end CFSG.RankThree.PartOne.SEITZ3
