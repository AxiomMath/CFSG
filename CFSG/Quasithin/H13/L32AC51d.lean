module

public import CFSG.Quasithin.H13.L32AC51a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Matrix

namespace Lin

@[expose] def c60 : SLn 6 :=
  SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) 1 *
    SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 0 by decide) 1

@[expose] def c61 : SLn 6 :=
  SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 3 by decide) 1 *
    SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 2 by decide) 1

@[expose] def c62 : SLn 6 :=
  SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) 1 *
    SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) 1

theorem c6_facts : c60 ^ 3 = 1 ∧ c61 ^ 3 = 1 ∧ c62 ^ 3 = 1 ∧ c60 * c61 = c61 * c60 ∧
    c60 * c62 = c62 * c60 ∧ c61 * c62 = c62 * c61 := by
  decide +kernel

theorem c6_indep : ∀ a b c : ZMod 3, c60 ^ a.val * (c61 ^ b.val * c62 ^ c.val) = 1 →
    a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel

theorem pow_val_add3 {M : Type*} [Monoid M] {ζ : M} (hζ : ζ ^ 3 = 1) (a b : ZMod 3) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  have h : ζ ^ (a.val + b.val) = ζ ^ ((a.val + b.val) % 3) := by
    conv_lhs => rw [← Nat.mod_add_div (a.val + b.val) 3, pow_add, pow_mul, hζ, one_pow, mul_one]
  rw [ZMod.val_add, ← h, pow_add]

theorem mul_mul_three {M : Type*} [Monoid M] {P Q R : M} (hPQ : Commute P Q) (hPR : Commute P R)
    (hQR : Commute Q R) (a b c a' b' c' : ℕ) :
    P ^ a * P ^ a' * (Q ^ b * Q ^ b' * (R ^ c * R ^ c')) =
      P ^ a * (Q ^ b * R ^ c) * (P ^ a' * (Q ^ b' * R ^ c')) := by
  have h1 : Commute (P ^ a') (Q ^ b * R ^ c) := (hPQ.pow_pow a' b).mul_right (hPR.pow_pow a' c)
  have h2 : Commute (Q ^ b') (R ^ c) := hQR.pow_pow b' c
  calc P ^ a * P ^ a' * (Q ^ b * Q ^ b' * (R ^ c * R ^ c'))
      = P ^ a * (P ^ a' * (Q ^ b * (Q ^ b' * R ^ c * R ^ c'))) := by simp only [mul_assoc]
    _ = P ^ a * (P ^ a' * (Q ^ b * R ^ c * (Q ^ b' * R ^ c'))) := by
        rw [h2.eq]; simp only [mul_assoc]
    _ = P ^ a * (Q ^ b * R ^ c * (P ^ a' * (Q ^ b' * R ^ c'))) := by
        rw [← mul_assoc (P ^ a'), h1.eq, mul_assoc]
    _ = _ := by simp only [mul_assoc]

@[expose] def e27 : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* SLn 6 where
  toFun x := c60 ^ (Multiplicative.toAdd x).1.val *
    (c61 ^ (Multiplicative.toAdd x).2.1.val * c62 ^ (Multiplicative.toAdd x).2.2.val)
  map_one' := by simp
  map_mul' x y := by
    obtain ⟨h0, h1, h2, h01, h02, h12⟩ := c6_facts
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    rw [pow_val_add3 h0, pow_val_add3 h1, pow_val_add3 h2]
    exact mul_mul_three h01 h02 h12 _ _ _ _ _ _

theorem e27_injective : Function.Injective e27 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨ha, hb, hc⟩ := c6_indep _ _ _ (MonoidHom.mem_ker.mp hx)
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  ext
  · exact ha
  · exact hb
  · exact hc

variable {m r : ℕ}

@[expose] def embMat (m r : ℕ) (A : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (m + r)) (Fin (m + r)) (ZMod 2) :=
  Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finSumFinEquiv (Matrix.fromBlocks A 0 0 1)

theorem embMat_mul (A B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    embMat m r (A * B) = embMat m r A * embMat m r B := by
  rw [embMat, embMat, embMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem embMat_one : embMat m r (1 : Matrix (Fin m) (Fin m) (ZMod 2)) = 1 := by
  rw [embMat, Matrix.fromBlocks_one, map_one]

theorem det_embMat (A : Matrix (Fin m) (Fin m) (ZMod 2)) : (embMat m r A).det = A.det := by
  rw [embMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem embMat_injective : Function.Injective (embMat m r) := fun A B h => by
  have h' := (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finSumFinEquiv).injective h
  exact (Matrix.fromBlocks_inj.1 h').1

@[expose] noncomputable def emb (m r : ℕ) : SLn m →* SLn (m + r) where
  toFun A := ⟨embMat m r (A : Matrix (Fin m) (Fin m) (ZMod 2)), by rw [det_embMat]; exact A.2⟩
  map_one' := Subtype.ext (embMat_one (m := m) (r := r))
  map_mul' A B := Subtype.ext (embMat_mul (m := m) (r := r) (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (B : Matrix (Fin m) (Fin m) (ZMod 2)))

theorem emb_injective : Function.Injective (emb m r) := fun _ _ h =>
  Subtype.ext (embMat_injective (congrArg Subtype.val h))

theorem card_e27 : Nat.card (Multiplicative (ZMod 3 × ZMod 3 × ZMod 3)) = 3 ^ 3 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  norm_num

theorem e27_cube (a : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  obtain ⟨x, y, z⟩ := Multiplicative.toAdd a
  ext <;> simp only [Prod.smul_mk, Prod.fst_zero, Prod.snd_zero] <;> revert x y z <;> decide

theorem three_le_pRank {X : Type*} [Group X] [Finite X] (r : ℕ) (f : SLn (6 + r) →* X)
    (hf : Function.Injective f) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b) e27_cube card_e27
    (f.comp ((emb 6 r).comp e27)) (hf.comp (emb_injective.comp e27_injective)) le_top

end Lin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem false_of_six_le (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ}
    (hn : 6 ≤ n) (hP : IsPSL n 2 1 (cStar K)) : False := by
  obtain ⟨r, rfl⟩ : ∃ r, n = 6 + r := ⟨n - 6, by omega⟩
  obtain ⟨φ⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL hP
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  have h3 := Lin.three_le_pRank r ((modO2Image H K).subtype.comp
    (((cStarEquiv K).trans e).toMonoidHom.comp φ.symm.toMonoidHom))
    ((modO2Image H K).subtype_injective.comp (((cStarEquiv K).trans e).injective.comp
      φ.symm.injective))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥H) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥H) hN
  have hsq : CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 :=
    stronglyQuasithin_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hz.1.2 3 Nat.prime_three (by norm_num)
  omega

end CFSG.Quasithin.H13.L32A.C
