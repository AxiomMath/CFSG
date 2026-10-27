module

public import CFSG.Quasithin.MS93.MSPBT

public section

namespace CFSG.Quasithin.MS93.S512N

open Matrix CFSG.Assembly.LowTwoRank MSP

variable {F : Type} [Field F]

theorem eq_one_of_pow_two_pow [CharP F 2] {c : F} {n : ℕ} (h : c ^ 2 ^ n = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (c - 1) ^ 2 ^ n = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by positivity)).mp h1)

theorem mulVec_pow_of_eigen {g : Sp4 F} {v : V4 F} {c : F} (hv : mat g *ᵥ v = c • v) (m : ℕ) :
    mat (g ^ m) *ᵥ v = c ^ m • v := by
  induction m with
  | zero => simp [mat_one]
  | succ m ih =>
    rw [pow_succ, mat_mul_mulVec, hv, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem mulVec_eq_of_mem_stab_point [CharP F 2] {g : Sp4 F} {n : ℕ} (hg : g ^ 2 ^ n = 1)
    {p : Submodule F (V4 F)} (hp : IsPoint p) (hgp : g ∈ stab p) {v : V4 F} (hv : v ∈ p) :
    mat g *ᵥ v = v := by
  obtain ⟨x, hx, rfl⟩ := exists_eq_span_of_isPoint hp
  have hgx : mat g *ᵥ x ∈ F ∙ x :=
    mulVec_mem_of_mem_stab hgp (Submodule.mem_span_singleton_self x)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hgx
  have h1 := mulVec_pow_of_eigen hc.symm (2 ^ n)
  rw [hg, mat_one, one_mulVec] at h1
  have hc1 : c ^ 2 ^ n = 1 := by
    have h2 : (c ^ 2 ^ n - 1) • x = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hx)
  have hc' := eq_one_of_pow_two_pow hc1
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [mulVec_smul, ← hc, hc', one_smul]

theorem commute_of_le_normalizer [CharP F 2] {A : Subgroup (Sp4 F)} {p : Submodule F (V4 F)}
    (hp : IsPoint p) (hA : fixSp A = perp p) {g : Sp4 F} {n : ℕ} (hg : g ^ 2 ^ n = 1)
    (hgA : g ∈ Subgroup.normalizer (A : Set (Sp4 F))) {t : Sp4 F} (ht : t ∈ A) :
    g * t = t * g := by
  have hgs : g ∈ stab p := by
    have := normalizer_le_stab_fixSp A hgA
    rwa [hA, stab_perp] at this
  have htx : t ∈ xPoint p := fun v hv => by
    rw [← hA] at hv
    exact hv t ht
  obtain ⟨x, hx, rfl⟩ := exists_eq_span_of_isPoint hp
  obtain ⟨c, rfl⟩ := (mem_xPoint_span hx).1 htx
  have hgx := mulVec_eq_of_mem_stab_point hg hp hgs (Submodule.mem_span_singleton_self x)
  have he := transv_conj g x c
  rw [hgx] at he
  calc g * transv x c = g * transv x c * g⁻¹ * g := by group
    _ = transv x c * g := by rw [he]

end CFSG.Quasithin.MS93.S512N
