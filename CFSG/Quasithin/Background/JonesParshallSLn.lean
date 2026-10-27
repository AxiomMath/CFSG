module

public import CFSG.Quasithin.Background.JonesParshallSmallSL
public import CFSG.Quasithin.Background.JonesParshallSL3

public section

namespace CFSG.Quasithin.JonesParshall

open Matrix

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

section RingEquiv

variable {d : ℕ} {F F' : Type} [Field F] [Field F']

@[expose] def slRingEquiv (d : ℕ) (e : F ≃+* F') :
    SpecialLinearGroup (Fin d) F ≃* SpecialLinearGroup (Fin d) F' where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    change e.symm (e ((g : Matrix (Fin d) (Fin d) F) i j)) = _
    rw [RingEquiv.symm_apply_apply]
  right_inv g := by
    ext i j
    change e (e.symm ((g : Matrix (Fin d) (Fin d) F') i j)) = _
    rw [RingEquiv.apply_symm_apply]
  map_mul' := map_mul _

@[expose] def vecRingEquiv (d : ℕ) (e : F ≃+* F') : (Fin d → F) ≃+ (Fin d → F') where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp

theorem intertwiner_ringEquiv {ρ : Representation (ZMod 2) Γ W}
    {θ : Γ ≃* SpecialLinearGroup (Fin d) F} {β : W ≃+ (Fin d → F)}
    (h : ∀ γ w, β (ρ γ w) = θ γ • β w) (e : F ≃+* F') :
    ∀ γ w, (β.trans (vecRingEquiv d e)) (ρ γ w) =
      (θ.trans (slRingEquiv d e)) γ • (β.trans (vecRingEquiv d e)) w := by
  intro γ w
  change (fun i => e (β (ρ γ w) i)) =
    ((SpecialLinearGroup.map e.toRingHom (θ γ) : SpecialLinearGroup (Fin d) F') :
      Matrix (Fin d) (Fin d) F') *ᵥ (fun i => e (β w i))
  rw [h, SpecialLinearGroup.map_apply_coe]
  funext i
  change e ((((θ γ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ β w) i) = _
  exact RingHom.map_mulVec e.toRingHom _ _ i

theorem intertwiner_zmod {ρ : Representation (ZMod 2) Γ W} [Fintype F]
    (hF : Fintype.card F = 2) {ε : Explicit.NatDual} (h : Explicit.BinaryNaturalSL ρ d F ε) :
    ∃ (θ : Γ ≃* SpecialLinearGroup (Fin d) (ZMod 2)) (β : W ≃+ (Fin d → ZMod 2)),
      ∀ γ w, β (ρ γ w) = θ γ • β w := by
  obtain ⟨θ, β, hβ⟩ := BinaryNaturalSL.intertwiner h
  exact ⟨_, _, intertwiner_ringEquiv hβ (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm⟩

end RingEquiv

theorem rels_constraint {n : ℕ} {gens : Fin 2 → SpecialLinearGroup (Fin n) (ZMod 2)}
    {rels : List (List (Fin 2))}
    (hrels : ∀ r ∈ rels, wordEvalM (fun k => (gens k : Matrix (Fin n) (Fin n) (ZMod 2))) r = 1)
    {f : SpecialLinearGroup (Fin n) (ZMod 2) → (Fin n → ZMod 2)} (hf : f ∈ Z1A (muF2 n)) :
    ∀ r ∈ rels, foxEvalM (fun k => (gens k : Matrix (Fin n) (Fin n) (ZMod 2)))
      ![f (gens 0), f (gens 1)] r = 0 := fun r hr => by
  have h := (foxEval_SL gens (fun i => f (gens i)) r).symm.trans (Z1A_wordEval hf gens r).symm
  rw [wordEval_eq_one (hrels r hr), Z1A_one hf] at h
  have hv : (![f (gens 0), f (gens 1)] : Fin 2 → Fin n → ZMod 2) = fun i => f (gens i) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact h

theorem closure_gens3 : Subgroup.closure (Set.range gens3) = ⊤ :=
  closure_range_eq_top (tw := tw3) (by rw [gens3_coe]; exact tw3_spec)

theorem cocycle3_mem : cocycle3 ∈ Z1A (muF2 3) := by
  refine mem_Z1A_of_gens closure_gens3 cocycle3_one ?_
  rintro _ ⟨i, rfl⟩ g
  fin_cases i
  · exact cocycle3_gen0 g
  · exact cocycle3_gen1 g

theorem cocycle3_not_mem : cocycle3 ∉ B1A (muF2 3) := by
  rintro ⟨v, hv⟩
  apply cocycle3_not
  refine ⟨v, ?_, ?_⟩
  · rw [← hv]
    rfl
  · rw [← hv]
    rfl

theorem eq_of_agree {n : ℕ} {gens : Fin 2 → SpecialLinearGroup (Fin n) (ZMod 2)}
    (hS : Subgroup.closure (Set.range gens) = ⊤) {f f' : SpecialLinearGroup (Fin n) (ZMod 2) →
      (Fin n → ZMod 2)} (hf : f ∈ Z1A (muF2 n)) (hf' : f' ∈ Z1A (muF2 n))
    (h0 : f (gens 0) = f' (gens 0)) (h1 : f (gens 1) = f' (gens 1)) : f = f' := by
  have h := eq_zero_of_vanish_closure (sub_mem hf hf') hS (by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact sub_eq_zero.mpr h0
    · exact sub_eq_zero.mpr h1)
  exact sub_eq_zero.mp h

theorem card_Z1A_three
    : Nat.card (Z1A (muF2 3)) = 2 * Nat.card (B1A (muF2 3)) := by
  let Φ : ZMod 2 × B1A (muF2 3) → Z1A (muF2 3) := fun p =>
    ⟨p.1.val • cocycle3 + p.2.1,
      add_mem (AddSubgroup.nsmul_mem _ cocycle3_mem _) (B1A_le_Z1A _ p.2.2)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨c, b⟩ ⟨c', b'⟩ h
      have h' : c.val • cocycle3 + b.1 = c'.val • cocycle3 + b'.1 := by
        simpa [Φ] using congrArg Subtype.val h
      have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      have key : c = c' := by
        rcases hc c with rfl | rfl <;> rcases hc c' with rfl | rfl
        · rfl
        · exfalso
          apply cocycle3_not_mem
          have : cocycle3 = b.1 - b'.1 := by
            simp only [ZMod.val_zero, zero_smul, zero_add, ZMod.val_one, one_smul] at h'
            rw [h']
            abel
          rw [this]
          exact sub_mem b.2 b'.2
        · exfalso
          apply cocycle3_not_mem
          have : cocycle3 = b'.1 - b.1 := by
            simp only [ZMod.val_zero, zero_smul, zero_add, ZMod.val_one, one_smul] at h'
            rw [← h']
            abel
          rw [this]
          exact sub_mem b'.2 b.2
        · rfl
      subst key
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h'))
    · rintro ⟨f, hf⟩
      have hrel := rels_constraint (gens := gens3) (rels := rels3)
        (by rw [gens3_coe]; exact rels3_spec) hf
      rw [gens3_coe] at hrel
      rcases sol3 _ _ hrel with ⟨v, hv₀, hv₁⟩ | ⟨v, hv₀, hv₁⟩
      · refine ⟨(0, ⟨coboundaryA (muF2 3) v, ⟨v, rfl⟩⟩), Subtype.ext ?_⟩
        simp only [Φ, ZMod.val_zero, zero_smul, zero_add]
        exact (eq_of_agree closure_gens3 hf (B1A_le_Z1A _ ⟨v, rfl⟩) hv₀ hv₁).symm
      · refine ⟨(1, ⟨coboundaryA (muF2 3) v, ⟨v, rfl⟩⟩), Subtype.ext ?_⟩
        simp only [Φ, ZMod.val_one, one_smul]
        refine (eq_of_agree closure_gens3 hf
          (add_mem cocycle3_mem (B1A_le_Z1A _ ⟨v, rfl⟩)) ?_ ?_).symm
        · rw [hv₀, Pi.add_apply, add_comm]
          rfl
        · rw [hv₁, Pi.add_apply, add_comm]
          rfl
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_zmod]

theorem finrank_H1_SL3 {F : Type} [Field F] [Fintype F] [CharP F 2]
    {ρ : Representation (ZMod 2) Γ W} {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 0 < a)
    {ε : Explicit.NatDual} (h : Explicit.BinaryNaturalSL ρ 3 F ε) :
    Module.finrank (ZMod 2) (H1 ρ) = if a = 1 then 1 else 0 := by
  split_ifs with h1
  · subst h1
    obtain ⟨θ, β, hβ⟩ := intertwiner_zmod (by rw [hF, pow_one]) h
    have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
    have : Finite W := Finite.of_equiv _ β.toEquiv.symm
    have hβ' : ∀ γ w, β (ρ γ w) = muF2 3 (θ γ) (β w) := hβ
    apply finrank_H1_of_card
    rw [card_H1_eq_of_card ρ hβ' card_Z1A_three, pow_one]
  · exact finrank_H1_SL3_of_one_lt hF (by omega) h

theorem finrank_H1_SL45
    {F : Type} [Field F] [Fintype F] {ρ : Representation (ZMod 2) Γ W}
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hF : Fintype.card F = 2) {ε : Explicit.NatDual}
    (h : Explicit.BinaryNaturalSL ρ d F ε) : Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  obtain ⟨θ, β, hβ⟩ := intertwiner_zmod hF h
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have hβ' : ∀ γ w, β (ρ γ w) = muF2 d (θ γ) (β w) := hβ
  have hZ : Z1A (muF2 d) = B1A (muF2 d) := by
    rcases hd with rfl | rfl
    · exact Z1A_eq_B1A_four
    · exact Z1A_eq_B1A_five
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' (k := 1) (by rw [hZ, one_mul]), pow_zero]

end CFSG.Quasithin.JonesParshall
