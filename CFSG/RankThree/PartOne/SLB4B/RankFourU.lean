module

public import CFSG.RankThree.PartOne.SLB4B.ModelU
public import CFSG.RankThree.PartOne.SLB4B.WitnessU
public import CFSG.RankThree.PartOne.SRC.CentralizerGen
public import CFSG.RankThree.PartOne.SRC.ModelU4
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.SRC

section Cover

variable {K : Type} [Field K]

theorem eq_one_of_scalar_pow_eq_one {p : ℕ} [Fact p.Prime] [CharP K p] {g : GL (Fin 4) K}
    (hg : g ∈ StatedScalars (Fin 4) K) (hgp : g ^ p = 1) : g = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 4) (u ^ p) = 1 := by rw [map_pow, hgp]
  have h2 : ((u ^ p : Kˣ) : K) = 1 := by
    have := congrArg (fun g : GL (Fin 4) K => Units.val g 0 0) h1
    rwa [scalar_entry, Units.val_one, Matrix.one_apply_eq] at this
  have hu : u = 1 := Units.ext (frobenius_inj K p (by
    rw [frobenius_def, frobenius_def, Units.val_one, one_pow, ← Units.val_pow_eq_pow_val]
    exact h2))
  rw [hu, map_one]

theorem negDiagSU4_sq {q : ℕ} (hq : Odd q) : negDiagSU4 (K := K) hq ^ 2 = 1 := by
  apply Subtype.ext
  change negDiag4 K ^ 2 = 1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_negDiag4, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Matrix.diagonal]

variable [Finite K]

theorem su4_block_data {p e : ℕ} [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ e) ^ 2)
    (hp2 : p ≠ 2) :
    CFSG.IsQuasisimple (StatedSU 4 (p ^ e) K) ∧
      Nat.Coprime p (Nat.card (center (StatedSU 4 (p ^ e) K))) ∧
      ∃ g : StatedSU 4 (p ^ e) K, g ∉ center (StatedSU 4 (p ^ e) K) ∧
        Nat.Coprime (orderOf g) p := by
  have hp : p.Prime := Fact.out
  have hodd : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  obtain ⟨hQ, hcen⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK
    (n := 4) (by norm_num) (fun h => absurd (congrArg Prod.fst h) (by norm_num))
  refine ⟨hQ, ?_, negDiagSU4 (K := K) hodd, ?_, ?_⟩
  · rw [hp.coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center (StatedSU 4 (p ^ e) K)) p hdvd
    have hxs : ((x : StatedSU 4 (p ^ e) K) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K :=
      Subgroup.mem_subgroupOf.mp ((SetLike.ext_iff.mp hcen _).mp x.2)
    have hxp1 : x ^ p = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have hxp : ((x : StatedSU 4 (p ^ e) K) : GL (Fin 4) K) ^ p = 1 := by
      have := congrArg (fun y : center (StatedSU 4 (p ^ e) K) =>
        ((y : StatedSU 4 (p ^ e) K) : GL (Fin 4) K)) hxp1
      simpa using this
    have hx1 : x = 1 := Subtype.ext (Subtype.ext (eq_one_of_scalar_pow_eq_one hxs hxp))
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  · rw [hcen, Subgroup.mem_subgroupOf]
    exact negDiag4_not_scalar h2
  · have hdvd : orderOf (negDiagSU4 (K := K) hodd) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (negDiagSU4_sq hodd)
    exact Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

theorem cover_su4 {p e : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ e) ^ 2)
    (hp2 : p ≠ 2) (hq : 4 ≤ p ^ e) (W : Type) [Group W] [Finite W]
    (ρ : W →* StatedSU 4 (p ^ e) K) (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, pow_zero] at hq
      omega
    · exact h0
  obtain ⟨hQ, hZ, h, hhc, hho⟩ := su4_block_data hK hp2
  have hclosed : ∀ (W : Type) [Group W] [Finite W] (π : W →* StatedSU 4 (p ^ e) K),
      Function.Surjective π → π.ker ≤ center W → IsPGroup p π.ker →
        ∃ s : StatedSU 4 (p ^ e) K →* W, ∀ g, π (s g) = g :=
    fun W _ _ π hπ hcen' _ =>
      CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central hK
        (by decide) le_rfl hq hπ hcen'
  have hK' : Nat.card K = p ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨E₀, hE₀, hcard⟩ := exists_elementaryAbelian_statedSU_four hp2 he1 hK'
  exact rank_four_of_cover_quasisimple hp2 hQ hZ h hhc hho hclosed hE₀ (k := 4 * e)
    (by omega) hcard ρ hρ hker

end Cover

theorem rankFourCover_psu {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hq : 4 ≤ p ^ e) {n : ℕ} (hn : 5 ≤ n) :
    RankFourCover p (StatedProj (StatedSU n (p ^ e) (GaloisField p (2 * e)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  have hm : 1 ≤ m := by omega
  have hp : p.Prime := Fact.out
  set K := GaloisField p (2 * e) with hKdef
  have hK : Nat.card K = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hneg : (-1 : K) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq K p]; exact hp2)
  exact rankFourCover_of_cover_ker hp hp2
    (fun W _ _ ρ hρ hker => cover_su4 hK hp2 hq W ρ hρ hker)
    (psuEmb (m := m) hodd.pos)
    (fun A hA => by rw [psuEmb_injective hodd.pos hm (hA.trans (map_one _).symm), one_pow])
    (orderOf_psuSign hodd hm hneg) (psuEmb_comm hodd.pos hodd)

end CFSG.RankThree.PartOne.SLB4B
