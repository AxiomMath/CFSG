module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Four

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr equivStatedSU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open Matrix CFSG.RankThree.PartTwo.KFacts.KS21.DFT

section Split

variable {F : Type} [Field F]

@[expose] def vec4 : Fˣ × Fˣ →* (Fin 4 → Fˣ) where
  toFun x := ![x.1, x.2, x.2⁻¹, x.1⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i <;> simp [mul_comm]

theorem vec4_injective : Function.Injective (vec4 (F := F)) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

theorem diagGL_vec4_mem (σ : F ≃+* F) {x : Fˣ × Fˣ} (h1 : σ (x.1 : F) = x.1)
    (h2 : σ (x.2 : F) = x.2) : TauCeti.diagGL (vec4 x) ∈ SU σ 4 := by
  rw [CFSG.LieType.Universal.Unitary.mem_SU]
  refine ⟨?_, ?_⟩
  · rw [TauCeti.diagGL_coe, det_diagonal, Fin.prod_univ_four]
    simp [vec4]
  · rw [TauCeti.diagGL_coe, conjTr, diagonal_map (map_zero σ), diagonal_transpose]
    ext i j
    rw [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [antidiag, vec4, h1, h2, Fin.rev]

variable {N : ℕ} [NeZero N] {ζ : Fˣ} (hζ : ζ ^ N = 1)

@[expose] noncomputable def splitHom :
    Multiplicative (ZMod N) × Multiplicative (ZMod N) →* GL (Fin 4) F :=
  TauCeti.diagGL.comp (vec4.comp (MonoidHom.prodMap (expHom ζ hζ) (expHom ζ hζ)))

theorem splitHom_injective (hζo : orderOf ζ = N) : Function.Injective (splitHom hζ) :=
  TauCeti.diagGL_injective.comp (vec4_injective.comp
    (Function.Injective.prodMap (expHom_injective hζ hζo) (expHom_injective hζ hζo)))

end Split

section SU

variable {p : ℕ} [Fact p.Prime]

theorem card_SU4_eq_mod_one {a m : ℕ} (hm : ¬ 3 ∣ m) (hpm : p - 1 = 3 ^ (a + 1) * m) :
    ∃ k, ¬ 3 ∣ k ∧ Nat.card (SU4 p) = 3 ^ (2 * (a + 1)) * k := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨B, hB⟩ : ∃ B, B = 3 ^ a * m := ⟨_, rfl⟩
  have hpB : p = 3 * B + 1 := by
    have : p - 1 = 3 * B := by rw [hpm, hB, pow_succ]; ring
    omega
  have hp3 : p % 3 = 1 := by omega
  refine ⟨m ^ 2 * (p ^ 6 * (p + 1) ^ 2 * (p ^ 3 + 1) * (p ^ 2 + 1)), ?_, ?_⟩
  · refine not_three_dvd_mul (not_three_dvd_pow 2 hm) (not_three_dvd_mul
      (not_three_dvd_mul (not_three_dvd_mul (not_three_dvd_pow 6 (by omega))
        (not_three_dvd_pow 2 (by omega))) ?_) ?_)
    · intro h
      have : (p ^ 3 + 1) % 3 = 2 := by
        rw [Nat.add_mod, Nat.pow_mod, hp3]
      omega
    · intro h
      have : (p ^ 2 + 1) % 3 = 2 := by
        rw [Nat.add_mod, Nat.pow_mod, hp3]
      omega
  · have h9 : 3 ^ (2 * (a + 1)) * m ^ 2 = 9 * B ^ 2 := by rw [hB]; ring
    rw [← mul_assoc, h9]
    have h := card_SU4_int (p := p)
    have hZ : (p : ℤ) = 3 * (B : ℤ) + 1 := by rw [hpB]; push_cast; ring
    have key : (Nat.card (SU4 p) : ℤ) = ((9 * B ^ 2 * (p ^ 6 * (p + 1) ^ 2 * (p ^ 3 + 1) *
        (p ^ 2 + 1)) : ℕ) : ℤ) := by
      rw [h]
      push_cast
      rw [hZ]
      ring
    exact_mod_cast key

theorem comm_of_isPGroup_SU4_mod_one (hp : p % 3 = 1) (P : Subgroup (SU4 p))
    (hP : IsPGroup 3 P) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨a, m, hm, hpm⟩ := exists_three_pow_succ (n := p - 1) (by omega) (by omega)
  obtain ⟨ζ, hζo⟩ := exists_orderOf_eq_of_dvd (F := FU p) (d := 3 ^ (a + 1)) (by
    rw [card_FU, show p ^ 2 - 1 = (p - 1) * (p + 1) by
      zify [(by omega : 1 ≤ p), Nat.one_le_pow 2 p (by omega)]
      ring, hpm]
    exact Dvd.dvd.mul_right (Dvd.intro m rfl) _)
  have hζ : ζ ^ (3 ^ (a + 1)) = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hζp : ζ ^ p = ζ := by
    have h1 : ζ ^ (p - 1) = 1 := by rw [hpm, pow_mul, hζ, one_pow]
    calc ζ ^ p = ζ ^ (p - 1) * ζ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      _ = ζ := by rw [h1, one_mul]
  have hσ : ∀ x : Multiplicative (ZMod (3 ^ (a + 1))),
      unitaryInvolution (FU p) p 1 ((expHom ζ hζ x : (FU p)ˣ) : FU p) = expHom ζ hζ x := by
    intro x
    obtain ⟨u, rfl⟩ := Multiplicative.ofAdd.surjective x
    rw [unitaryInvolution_apply, expHom_apply, ← Units.val_pow_eq_pow_val, ← pow_mul,
      Nat.mul_comm u.val (p ^ 1), pow_mul, pow_one, hζp]
  have hmem : ∀ x, splitHom hζ x ∈ SU (unitaryInvolution (FU p) p 1) 4 := fun x =>
    diagGL_vec4_mem _ (hσ x.1) (hσ x.2)
  have hF : Nat.card (FU p) = (p ^ 1) ^ 2 := by rw [card_FU, pow_one]
  let Ψ : Multiplicative (ZMod (3 ^ (a + 1))) × Multiplicative (ZMod (3 ^ (a + 1))) →* SU4 p :=
    (equivStatedSU hF 4).toMonoidHom.comp ((splitHom hζ).codRestrict _ hmem)
  have hΨ : Function.Injective Ψ := (equivStatedSU hF 4).injective.comp fun x y h =>
    splitHom_injective hζ hζo (congrArg Subtype.val h)
  set T := Ψ.range with hT
  haveI : IsMulCommutative T := ⟨⟨by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    apply Subtype.ext
    change Ψ x * Ψ y = Ψ y * Ψ x
    rw [← map_mul, ← map_mul, mul_comm x y]⟩⟩
  have hTcard : Nat.card T = 3 ^ (2 * (a + 1)) := by
    rw [hT, ← Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (3 ^ (a + 1))) ≃ _),
      Nat.card_zmod]
    ring
  obtain ⟨k, hk, hcard⟩ := card_SU4_eq_mod_one hm hpm
  have hindex : ¬ 3 ∣ T.index := by
    have hmul := Subgroup.card_mul_index T
    rw [hTcard, hcard] at hmul
    rwa [Nat.eq_of_mul_eq_mul_left (by positivity) hmul]
  have hc := CFSG.AGLEmbeddingD2.AbelianSylowGL.isMulCommutative_of_isPGroup_of_not_dvd_index
    T hindex hP
  intro x hx y hy
  exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

section Rows


omit [Fact p.Prime] in
theorem kT2_four_SU_mod_one (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    RowOf425 (projSU 4 p 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine rowOf425_of_noCQ' (noCC425_of_abelian_sylow ?_)
  rw [← CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 4 p 1]
  exact comm_sylow_projImage fun P hP => comm_of_isPGroup_SU4_mod_one hp P hP

omit [Fact p.Prime] in
theorem kT2_four_SU (p : ℕ) [Fact p.Prime] (hp : 3 < p) : RowOf425 (projSU 4 p 1) := by
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
  · have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h3 with h' | h' <;> omega
  · exact kT2_four_SU_mod_one p h
  · exact kT2_four_SU_mod_two p hp h

end Rows

end SU

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
