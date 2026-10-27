module

public import CFSG.RankThree.PartTwo.KFacts.KS12ClassSL

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix

section SL3

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem cube_root_cases {τ ζ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hζ : ζ ^ 3 = 1) :
    ζ = 1 ∨ ζ = τ ∨ ζ = τ ^ 2 := by
  have hs : 1 + τ + τ ^ 2 = 0 := by
    have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hτ1
    · exact h
  have h : (ζ - 1) * ((ζ - τ) * (ζ - τ ^ 2)) = 0 := by
    linear_combination hζ + (ζ - ζ ^ 2) * hs + (ζ - 1) * hτ
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))


theorem exists_conj_to_diagTau (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {d : slPi π 3 (p ^ f) K} (hd3 : d ^ 3 = 1)
    (hdz : d ∉ Subgroup.center (slPi π 3 (p ^ f) K)) :
    ∃ g : slPi π 3 (p ^ f) K,
      ((g * d * g⁻¹ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = diagTau hτ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hds : (d : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := by
    intro hs
    apply hdz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_statedScalars hs (g : GL (Fin 3) K))
  have hd3' : (d : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hd3, Subgroup.coe_one]
  obtain ⟨ζ, hζ3, g, hgS, hg⟩ := exists_conj_diagTau_slPi hK hq hτ hτ1 d.2 hd3' hds
  set ε : Kˣ := Units.mk0 τ hτ0 with hε
  have hε3 : ε ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hε, Units.val_mk0, hτ,
    Units.val_one])
  have hc : (cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (ε ^ 2) * diagTau hτ := by
    apply Units.ext
    rw [cycThree_conj_diagTau hτ, Units.val_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Units.val_pow_eq_pow_val, hε, Units.val_mk0]
  have hcpow : ∀ i : ℕ, (cycThree : GL (Fin 3) K) ^ i * diagTau hτ *
      ((cycThree : GL (Fin 3) K) ^ i)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (ε ^ (2 * i)) * diagTau hτ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc (cycThree : GL (Fin 3) K) ^ (i + 1) * diagTau hτ *
            ((cycThree : GL (Fin 3) K) ^ (i + 1))⁻¹
          = (cycThree : GL (Fin 3) K) ^ i *
              ((cycThree : GL (Fin 3) K) * diagTau hτ * (cycThree : GL (Fin 3) K)⁻¹) *
              ((cycThree : GL (Fin 3) K) ^ i)⁻¹ := by group
        _ = (cycThree : GL (Fin 3) K) ^ i * (GeneralLinearGroup.scalar (Fin 3) (ε ^ 2) *
              diagTau hτ) * ((cycThree : GL (Fin 3) K) ^ i)⁻¹ := by rw [hc]
        _ = GeneralLinearGroup.scalar (Fin 3) (ε ^ 2) *
              ((cycThree : GL (Fin 3) K) ^ i * diagTau hτ * ((cycThree : GL (Fin 3) K) ^ i)⁻¹) := by
          have hcp : ∀ (u : Kˣ) (n : ℕ), (cycThree : GL (Fin 3) K) ^ n *
              GeneralLinearGroup.scalar (Fin 3) u =
              GeneralLinearGroup.scalar (Fin 3) u * (cycThree : GL (Fin 3) K) ^ n := fun u n =>
            (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u ((cycThree : GL (Fin 3) K) ^ n)).eq
          rw [← mul_assoc, hcp, mul_assoc, mul_assoc]
          simp only [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin 3) (ε ^ (2 * (i + 1))) * diagTau hτ := by
          rw [ih, ← mul_assoc, ← map_mul, ← pow_add]
          congr 3
          ring
  have hcS : (cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := cycThree_mem_slPi hπ
  have hg' : g⁻¹ * (d : GL (Fin 3) K) * g = diagTau hτ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by
    have hcs : (GeneralLinearGroup.scalar (Fin 3) ζ) * g =
        g * GeneralLinearGroup.scalar (Fin 3) ζ :=
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g).eq.symm
    have h1 : g⁻¹ * (d : GL (Fin 3) K) * g * GeneralLinearGroup.scalar (Fin 3) ζ = diagTau hτ := by
      rw [← hg]
      calc g⁻¹ * (d : GL (Fin 3) K) * g * GeneralLinearGroup.scalar (Fin 3) ζ
          = g⁻¹ * (d : GL (Fin 3) K) * (g * GeneralLinearGroup.scalar (Fin 3) ζ) := by
            rw [mul_assoc]
        _ = g⁻¹ * (d : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) ζ * g) := by rw [hcs]
        _ = g⁻¹ * ((d : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ζ) * g := by
            simp only [mul_assoc]
    rw [map_inv]
    exact eq_mul_inv_of_mul_eq h1
  have finish : ∀ i : ℕ, g⁻¹ * (d : GL (Fin 3) K) * g =
      (cycThree : GL (Fin 3) K) ^ i * diagTau hτ * ((cycThree : GL (Fin 3) K) ^ i)⁻¹ →
      ∃ g' : slPi π 3 (p ^ f) K, ((g' * d * g'⁻¹ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        diagTau hτ := by
    intro i hi
    refine ⟨(⟨g, hgS⟩ * (⟨cycThree, hcS⟩ : slPi π 3 (p ^ f) K) ^ i)⁻¹, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, inv_inv]
    calc ((g * cycThree ^ i)⁻¹ * (d : GL (Fin 3) K) * (g * cycThree ^ i) : GL (Fin 3) K)
        = (cycThree ^ i)⁻¹ * (g⁻¹ * (d : GL (Fin 3) K) * g) * cycThree ^ i := by group
      _ = diagTau hτ := by rw [hi]; group
  have hεζ : ζ = 1 ∨ ζ = ε ∨ ζ = ε ^ 2 := by
    rcases cube_root_cases hτ hτ1 (ζ := (ζ : K)) (by
      rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]) with h | h | h
    · exact Or.inl (Units.ext (by simpa using h))
    · exact Or.inr (Or.inl (Units.ext (by rw [hε, Units.val_mk0]; exact h)))
    · exact Or.inr (Or.inr (Units.ext (by
        rw [Units.val_pow_eq_pow_val, hε, Units.val_mk0]; exact h)))
  have hinvcase : ∀ i : ℕ, ζ = ε ^ i →
      g⁻¹ * (d : GL (Fin 3) K) * g =
        (cycThree : GL (Fin 3) K) ^ i * diagTau hτ * ((cycThree : GL (Fin 3) K) ^ i)⁻¹ := by
    intro i hi
    rw [hg', hcpow i, hi]
    have hεi : (ε ^ i)⁻¹ = ε ^ (2 * i) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hε3, one_pow]
    rw [hεi]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (ε ^ (2 * i)) (diagTau hτ)).eq
  rcases hεζ with h | h | h
  · exact finish 0 (by simpa using hinvcase 0 (by rw [h]; simp))
  · exact finish 1 (hinvcase 1 (by rw [h, pow_one]))
  · exact finish 2 (hinvcase 2 h)


theorem exists_conj_of_pow_three_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {a b : slPi π 3 (p ^ f) K} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (ha' : a ∉ Subgroup.center (slPi π 3 (p ^ f) K))
    (hb' : b ∉ Subgroup.center (slPi π 3 (p ^ f) K)) :
    ∃ g : slPi π 3 (p ^ f) K, g * a * g⁻¹ = b := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨g₁, h₁⟩ := exists_conj_to_diagTau hK hq hτ hτ1 ha ha'
  obtain ⟨g₂, h₂⟩ := exists_conj_to_diagTau hK hq hτ hτ1 hb hb'
  have h12 : g₁ * a * g₁⁻¹ = g₂ * b * g₂⁻¹ := Subtype.ext (h₁.trans h₂.symm)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  calc g₂⁻¹ * g₁ * a * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * a * g₁⁻¹) * g₂ := by group
    _ = b := by rw [h12]; group

end SL3

section Transfer

theorem exists_conj_of_isSLThreePiAt {Q : Type} [Group Q] {r : TauCeti.PrimePower}
    (hQ : Sec4.IsSLThreePiAt Q r.card) {a b : Q} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (ha' : a ∉ Subgroup.center Q) (hb' : b ∉ Subgroup.center Q) :
    ∃ g : Q, g * a * g⁻¹ = b := by
  have key : ∀ {π : Bool} {K : Type} [Field K] (hK : PiField π r.p r.exponent K)
      (hq : ModThree π (r.p ^ r.exponent)) (e : Q ≃* slPi π 3 (r.p ^ r.exponent) K),
      ∃ g : Q, g * a * g⁻¹ = b := by
    intro π K _ hK hq e
    obtain ⟨g, hg⟩ := exists_conj_of_pow_three_slPi hK hq (a := e a) (b := e b)
      (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
      (fun h => ha' (by simpa using mem_center_of_mulEquiv e.symm h))
      (fun h => hb' (by simpa using mem_center_of_mulEquiv e.symm h))
    refine ⟨e.symm g, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
  have hc : r.card = r.p ^ r.exponent := TauCeti.PrimePower.card_def r
  obtain ⟨K, _, _, ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩⟩ := hQ
  · exact key (π := true) ⟨r.prime_p, r.exponent_pos, by rw [piCard, Bool.cond_true, ← hc, hK]⟩
      (by change r.p ^ r.exponent % 3 = 1; rw [← hc]; exact hq) e
  · exact key (π := false) ⟨r.prime_p, r.exponent_pos, by
      rw [piCard, Bool.cond_false, ← hc, hK]⟩
      (by change r.p ^ r.exponent % 3 = 2; rw [← hc]; exact hq)
      (by rw [← hc]; exact e)

end Transfer

end CFSG.RankThree.PartTwo.Sec12.Hering129L
