module

public import CFSG.Quasithin.H13.L32AC51d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm

namespace Alt9

@[expose] def p0 : Perm (Fin 9) := swap 0 1 * swap 1 2

@[expose] def p1 : Perm (Fin 9) := swap 3 4 * swap 4 5

@[expose] def p2 : Perm (Fin 9) := swap 6 7 * swap 7 8

theorem p_facts : p0 ^ 3 = 1 ∧ p1 ^ 3 = 1 ∧ p2 ^ 3 = 1 ∧ p0 * p1 = p1 * p0 ∧
    p0 * p2 = p2 * p0 ∧ p1 * p2 = p2 * p1 := by
  decide +kernel

theorem p_indep : ∀ a b c : ZMod 3, p0 ^ a.val * (p1 ^ b.val * p2 ^ c.val) = 1 →
    a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel

theorem p_sign : sign p0 = 1 ∧ sign p1 = 1 ∧ sign p2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [p0, p1, p2, Perm.sign_mul, Perm.sign_swap']

@[expose] def e27 : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* Perm (Fin 9) where
  toFun x := p0 ^ (Multiplicative.toAdd x).1.val *
    (p1 ^ (Multiplicative.toAdd x).2.1.val * p2 ^ (Multiplicative.toAdd x).2.2.val)
  map_one' := by simp
  map_mul' x y := by
    obtain ⟨h0, h1, h2, h01, h02, h12⟩ := p_facts
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    rw [Lin.pow_val_add3 h0, Lin.pow_val_add3 h1, Lin.pow_val_add3 h2]
    exact Lin.mul_mul_three h01 h02 h12 _ _ _ _ _ _

theorem e27_injective : Function.Injective e27 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨ha, hb, hc⟩ := p_indep _ _ _ (MonoidHom.mem_ker.mp hx)
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  ext
  · exact ha
  · exact hb
  · exact hc

theorem sign_e27 (x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3)) : sign (e27 x) = 1 := by
  obtain ⟨s0, s1, s2⟩ := p_sign
  show sign (p0 ^ _ * (p1 ^ _ * p2 ^ _)) = 1
  rw [Perm.sign_mul, Perm.sign_mul, map_pow, map_pow, map_pow, s0, s1, s2]
  simp

@[expose] noncomputable def e27A {n : ℕ} (hn : 9 ≤ n) :
    Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* ↥(alternatingGroup (Fin n)) :=
  ((viaEmbeddingHom (Fin.castLEEmb hn)).comp e27).codRestrict _ fun x => by
    rw [mem_alternatingGroup, MonoidHom.comp_apply, viaEmbeddingHom_apply, viaEmbedding,
      sign_extendDomain, sign_e27]

theorem e27A_injective {n : ℕ} (hn : 9 ≤ n) : Function.Injective (e27A hn) := fun _ _ h =>
  e27_injective (viaEmbeddingHom_injective (Fin.castLEEmb hn) (congrArg Subtype.val h))

theorem three_le_pRank {X : Type*} [Group X] [Finite X] {n : ℕ} (hn : 9 ≤ n)
    (f : ↥(alternatingGroup (Fin n)) →* X) (hf : Function.Injective f) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b) Lin.e27_cube
    Lin.card_e27 (f.comp (e27A hn)) (hf.comp (e27A_injective hn)) le_top

end Alt9

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem pRank_quot_le_two (S : Setting147 G T L V H) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 := by
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

theorem false_of_alt_nine_le (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    {n : ℕ} (hn : 9 ≤ n) (hA : IsAlt n (cStar K)) : False := by
  obtain ⟨φ⟩ := hA
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  have h3 := Alt9.three_le_pRank hn ((modO2Image H K).subtype.comp
    (((cStarEquiv K).trans e).toMonoidHom.comp φ.symm.toMonoidHom))
    ((modO2Image H K).subtype_injective.comp (((cStarEquiv K).trans e).injective.comp
      φ.symm.injective))
  have h2 := pRank_quot_le_two S
  omega

end CFSG.Quasithin.H13.L32A.C
