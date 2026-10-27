module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Assembly.LowTwoRank Matrix CFSG.Open

private theorem torusDiag_det {F : Type} [Field F] (a b : Fˣ) :
    (Matrix.diagonal ![(a : F), (b : F), ((a : F) * b)⁻¹]).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simpa using mul_inv_cancel₀ (mul_ne_zero a.ne_zero b.ne_zero)

private theorem torusDiag_mul {F : Type} [Field F] (a b a' b' : Fˣ) :
    Matrix.diagonal ![((a * a' : Fˣ) : F), ((b * b' : Fˣ) : F),
        (((a * a' : Fˣ) : F) * ((b * b' : Fˣ) : F))⁻¹] =
      Matrix.diagonal ![(a : F), (b : F), ((a : F) * b)⁻¹] *
        Matrix.diagonal ![(a' : F), (b' : F), ((a' : F) * b')⁻¹] := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

private noncomputable def torusDiagHom (F : Type) [Field F] :
    Fˣ × Fˣ →* Matrix.SpecialLinearGroup (Fin 3) F :=
  MonoidHom.mk'
    (fun m => ⟨Matrix.diagonal ![(m.1 : F), (m.2 : F), ((m.1 : F) * m.2)⁻¹],
      torusDiag_det m.1 m.2⟩)
    (fun m m' => Subtype.ext (torusDiag_mul m.1 m.2 m'.1 m'.2))

private theorem torusDiagHom_injective (F : Type) [Field F] :
    Function.Injective (torusDiagHom F) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  have h0 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F => A 0 0) hm
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F => A 1 1) hm
  simp [torusDiagHom] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

private theorem card_units_eq_sub_one (F : Type) [Field F] [Fintype F] :
    Nat.card Fˣ = Fintype.card F - 1 := by
  have h1 := Nat.card_eq_card_units_add_one (α := F)
  rw [Nat.card_eq_fintype_card (α := F)] at h1
  omega

theorem exists_torus_elemAbelian {F : Type} [Field F] [Fintype F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Fintype.card F - 1) :
    ∃ E : Subgroup ↥(StatedSL 3 F), IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p
    (by rw [card_units_eq_sub_one F]; exact hpF)
  have hμcard : Nat.card (Subgroup.zpowers ζ) = p := by
    rw [Nat.card_zpowers, hζ]
  have hμpow : ∀ a ∈ Subgroup.zpowers ζ, a ^ p = 1 := fun a ha =>
    orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ orderOf_dvd_of_mem_zpowers ha)
  have hMcard : Nat.card ((Subgroup.zpowers ζ).prod (Subgroup.zpowers ζ)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers ζ) (Subgroup.zpowers ζ)).toEquiv,
      Nat.card_prod, hμcard, sq]
  have he : Function.Injective
      (specialLinearGroupEquivStatedSL 3 F : Matrix.SpecialLinearGroup (Fin 3) F →* StatedSL 3 F) :=
    (specialLinearGroupEquivStatedSL 3 F).injective
  refine ⟨(((Subgroup.zpowers ζ).prod (Subgroup.zpowers ζ)).map (torusDiagHom F)).map
    (specialLinearGroupEquivStatedSL 3 F : Matrix.SpecialLinearGroup (Fin 3) F →* StatedSL 3 F),
    ⟨inferInstance, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    have hz' : z ^ p = 1 := by
      have h1 : z.1 ∈ Subgroup.zpowers ζ := (Subgroup.mem_prod.1 hz).1
      have h2 : z.2 ∈ Subgroup.zpowers ζ := (Subgroup.mem_prod.1 hz).2
      exact Prod.ext (by simpa using hμpow _ h1) (by simpa using hμpow _ h2)
    rw [← map_pow, ← map_pow, hz', map_one, map_one]
  · rw [Subgroup.card_map_of_injective he,
      Subgroup.card_map_of_injective (torusDiagHom_injective F), hMcard]

theorem exists_prime_dvd_two_pow_sub_one {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧ (p = 3 → n = 2) := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    exact ⟨3, Nat.prime_three, by norm_num, by norm_num, fun _ => rfl⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have hpow : 2 ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; norm_num; ring
    have hN8 : (2 ^ (m + 3) - 1) % 8 = 7 := by
      rw [hpow]
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    by_cases hex : ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ (m + 3) - 1 ∧ p ≠ 3
    · obtain ⟨p, hp, hpd, hp3⟩ := hex
      refine ⟨p, hp, ?_, hpd, fun h => absurd h hp3⟩
      rintro rfl
      have h2 : 2 ∣ 2 ^ (m + 3) := dvd_pow_self 2 (by omega)
      omega
    · exfalso
      push Not at hex
      have hN0 : 2 ^ (m + 3) - 1 ≠ 0 := by omega
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 ^ (m + 3) - 1 = 3 ^ k :=
        ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hN0 (fun {d} hd hdvd => hex d hd hdvd)⟩
      have hmod : ∀ j : ℕ, 3 ^ j % 8 = 1 ∨ 3 ^ j % 8 = 3 := by
        intro j
        induction j with
        | zero => norm_num
        | succ j ih => rw [pow_succ]; omega
      have := hmod k
      omega

end CFSG.Quasithin.H13.Ch4.CentK
