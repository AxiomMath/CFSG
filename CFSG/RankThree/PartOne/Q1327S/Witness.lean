module

public import CFSG.RankThree.PartOne.Q1327S.Weyl

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne

variable {Q : Type} [Group Q]

theorem not_perm3_of_conj {E E₀ : Subgroup Q} {g h : Q}
    (hconj : ∀ z : Q, z ∈ E ↔ g⁻¹ * z * g ∈ E₀) (hh : h ∈ Subgroup.normalizer (E₀ : Set Q))
    {z₀ : Q} (hz₀ : z₀ ∈ E₀) (hne : h ^ 6 * z₀ * (h ^ 6)⁻¹ ≠ z₀) :
    ¬ Nonempty (torusImage E ⊤ ≃* Equiv.Perm (Fin 3)) := by
  have hz : g * z₀ * g⁻¹ ∈ E := by
    rw [hconj]
    simpa [mul_assoc] using hz₀
  have hn : g * h * g⁻¹ ∈ Subgroup.normalizer (E : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hconj, hconj]
    have h1 := (Subgroup.mem_normalizer_iff.1 hh) (g⁻¹ * z * g)
    have h2 : h * (g⁻¹ * z * g) * h⁻¹ = g⁻¹ * (g * h * g⁻¹ * z * (g * h * g⁻¹)⁻¹) * g := by
      group
    rw [h2] at h1
    exact h1
  refine not_nonempty_perm3_of_pow_six hn hz ?_
  intro h3
  apply hne
  have h4 : (g * h * g⁻¹) ^ 6 * (g * z₀ * g⁻¹) * ((g * h * g⁻¹) ^ 6)⁻¹ =
      g * (h ^ 6 * z₀ * (h ^ 6)⁻¹) * g⁻¹ := by
    rw [conj_pow]
    group
  rw [h4] at h3
  have := mul_left_cancel (mul_right_cancel h3)
  exact this

theorem exists_conj_of_card {p : ℕ} [Fact p.Prime] [Finite Q] {E E₀ : Subgroup Q}
    (hE : Nat.card E = p ^ (Nat.card Q).factorization p)
    (hE₀ : Nat.card E₀ = p ^ (Nat.card Q).factorization p) :
    ∃ g : Q, ∀ z : Q, z ∈ E ↔ g⁻¹ * z * g ∈ E₀ := by
  let S : Sylow p Q := Sylow.ofCard E hE
  let S₀ : Sylow p Q := Sylow.ofCard E₀ hE₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q S₀ S
  refine ⟨g, fun z => ?_⟩
  have h1 : ((g • S₀ : Sylow p Q) : Subgroup Q) = E := by rw [hg]; rfl
  rw [Sylow.coe_subgroup_smul] at h1
  rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]
  rfl

theorem not_perm3_of_witness {p : ℕ} [Fact p.Prime] [Finite Q] {Ē : Subgroup Q}
    (hEcard : Nat.card Ē = p ^ 2) (hQ : ¬ p ^ 3 ∣ Nat.card Q) {x y h : Q}
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set Q)) = p ^ 2)
    (hh : h ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set Q) : Set Q))
    (hne : h ^ 6 * x * (h ^ 6)⁻¹ ≠ x) :
    ¬ Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) := by
  have hX0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hdvd : p ^ 2 ∣ Nat.card Q := hEcard ▸ Subgroup.card_subgroup_dvd_card Ē
  have hfac : (Nat.card Q).factorization p = 2 :=
    factorization_eq_two (Fact.out : p.Prime) hX0 hdvd hQ
  obtain ⟨g, hg⟩ := exists_conj_of_card (p := p) (E := Ē)
    (E₀ := Subgroup.closure ({x, y} : Set Q)) (by rw [hfac, hEcard]) (by rw [hfac, hcard])
  exact not_perm3_of_conj hg hh (Subgroup.subset_closure (by simp)) hne

section Pair

variable [Finite Q]

theorem mem_normalizer_of_conj_le {P : Subgroup Q} {h : Q} (hh : ∀ z ∈ P, h * z * h⁻¹ ∈ P) :
    h ∈ Subgroup.normalizer (P : Set Q) := by
  have hle : P.map (MulAut.conj h).toMonoidHom ≤ P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hh z hz
  have hcard : Nat.card P ≤ Nat.card (P.map (MulAut.conj h).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
  have heq : P.map (MulAut.conj h).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hh z
  · intro hz
    rw [← heq] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = z := (MulAut.conj h).injective hwz
    rw [← this]
    simpa using hw

omit [Finite Q] in
theorem conj_closure_le {x y h : Q} (hx : h * x * h⁻¹ ∈ Subgroup.closure ({x, y} : Set Q))
    (hy : h * y * h⁻¹ ∈ Subgroup.closure ({x, y} : Set Q)) :
    ∀ z ∈ Subgroup.closure ({x, y} : Set Q),
      h * z * h⁻¹ ∈ Subgroup.closure ({x, y} : Set Q) := by
  have : Subgroup.closure ({x, y} : Set Q) ≤
      (Subgroup.closure ({x, y} : Set Q)).comap (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hx
    · exact hy
  exact fun z hz => this hz

end Pair

section Iter

variable {x y h : Q} {p : ℕ}

@[expose] def stPair (a b c d : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => (a * (stPair a b c d n).1 + c * (stPair a b c d n).2,
      b * (stPair a b c d n).1 + d * (stPair a b c d n).2)

theorem conj_mul_pow (hxy : x * y = y * x) {a b c d : ℕ} (hhx : h * x * h⁻¹ = x ^ a * y ^ b)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d) (i j : ℕ) :
    h * (x ^ i * y ^ j) * h⁻¹ = x ^ (a * i + c * j) * y ^ (b * i + d * j) := by
  have hc : Commute x y := hxy
  have h1 : h * (x ^ i * y ^ j) * h⁻¹ = (h * x * h⁻¹) ^ i * (h * y * h⁻¹) ^ j := by
    rw [conj_pow, conj_pow]
    group
  rw [h1, hhx, hhy, (hc.pow_pow a b).mul_pow i, (hc.pow_pow c d).mul_pow j, ← pow_mul,
    ← pow_mul, ← pow_mul, ← pow_mul]
  have hcomm : y ^ (b * i) * x ^ (c * j) = x ^ (c * j) * y ^ (b * i) :=
    (hc.pow_pow (c * j) (b * i)).eq.symm
  calc x ^ (a * i) * y ^ (b * i) * (x ^ (c * j) * y ^ (d * j))
      = x ^ (a * i) * (y ^ (b * i) * x ^ (c * j)) * y ^ (d * j) := by simp only [mul_assoc]
    _ = x ^ (a * i) * (x ^ (c * j) * y ^ (b * i)) * y ^ (d * j) := by rw [hcomm]
    _ = x ^ (a * i) * x ^ (c * j) * (y ^ (b * i) * y ^ (d * j)) := by simp only [mul_assoc]
    _ = x ^ (a * i + c * j) * y ^ (b * i + d * j) := by rw [← pow_add, ← pow_add]

theorem conj_iter (hxy : x * y = y * x) {a b c d : ℕ} (hhx : h * x * h⁻¹ = x ^ a * y ^ b)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d) (n : ℕ) :
    h ^ n * x * (h ^ n)⁻¹ = x ^ (stPair a b c d n).1 * y ^ (stPair a b c d n).2 := by
  induction n with
  | zero => simp [stPair]
  | succ n ih =>
    have h1 : h ^ (n + 1) * x * (h ^ (n + 1))⁻¹ = h * (h ^ n * x * (h ^ n)⁻¹) * h⁻¹ := by
      rw [pow_succ']
      group
    rw [h1, ih, conj_mul_pow hxy hhx hhy]
    simp [stPair]

end Iter

end CFSG.RankThree.PartOne.Q1327S
