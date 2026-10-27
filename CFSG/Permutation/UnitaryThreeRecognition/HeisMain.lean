module

public import CFSG.Permutation.UnitaryThreeRecognition.HeisTrace

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

open scoped commutatorElement

namespace Hyp

variable {G : Type*} [Group G] [Finite G] {Q T Z W : Subgroup G} {p f d : ℕ} [Fact p.Prime]
  (S : Hyp Q T Z W p f d)
include S

@[expose] noncomputable def aA (x : Q) : S.A := S.coordA (Baer.toB S.isBaer x)

@[expose] noncomputable def cA (x : Q) : S.A := 2 * S.Linv (S.piZ (Baer.toB S.isBaer x))

theorem coordA_add (u v : S.V) : S.coordA (u + v) = S.coordA u + S.coordA v := by
  rw [coordA, coordA, coordA, map_add, map_add]

theorem coordA_of_mem_Zs {z : S.V} (hz : z ∈ S.Zs) : S.coordA z = 0 := by
  rw [coordA, S.piV_eq_zero_iff.mpr hz, map_zero]

omit [Finite G] in
theorem toB_mul_eq (x y : Q) :
    Baer.toB S.isBaer (x * y) = Baer.toB S.isBaer x + Baer.toB S.isBaer y +
      ((p + 1) / 2) • Baer.bracket (Baer.toB S.isBaer x) (Baer.toB S.isBaer y) := by
  rw [Baer.toB_mul, Baer.toB_pow]
  rfl

theorem aA_mul (x y : Q) : S.aA (x * y) = S.aA x + S.aA y := by
  rw [aA, S.toB_mul_eq, S.coordA_add, S.coordA_add,
    S.coordA_of_mem_Zs (S.Zs.nsmul_mem (S.bracket_mem_Zs _ _) _), add_zero]
  rfl

theorem two_mul_half_cast : (2 : S.A) * (((p + 1) / 2 : ℕ) : S.A) = 1 := by
  have := S.charP_A
  have h : (2 * ((p + 1) / 2) : ℕ) = p + 1 := by
    have := two_mul_baerExp S.isBaer
    omega
  have h' := congrArg (fun n : ℕ => (n : S.A)) h
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, CharP.cast_eq_zero, zero_add,
    Nat.cast_one] at h'
  exact h'

theorem cA_mul (x y : Q) :
    S.cA (x * y) = S.cA x + S.cA y +
      (S.aA y * S.aA x ^ p ^ f - S.aA x * S.aA y ^ p ^ f) / 2 := by
  have hpi : S.piZ (Baer.toB S.isBaer (x * y)) = S.piZ (Baer.toB S.isBaer x) +
      S.piZ (Baer.toB S.isBaer y) +
      ((p + 1) / 2) • (⟨Baer.bracket (Baer.toB S.isBaer x) (Baer.toB S.isBaer y),
        S.bracket_mem_Zs _ _⟩ : S.Zs) := by
    rw [S.toB_mul_eq, map_add, map_add, map_nsmul, S.piZ_of_mem (S.bracket_mem_Zs _ _)]
  rw [cA, cA, cA, hpi, map_add, map_add, map_nsmul, S.Linv_bracket, nsmul_eq_mul, mul_add,
    mul_add, ← mul_assoc, S.two_mul_half_cast, one_mul]
  rw [aA, aA]
  ring

theorem frob_two : (2 : S.A) ^ p ^ f = 2 := by
  have := S.charP_A
  rw [← iterateFrobenius_def (p := p), map_ofNat]

theorem cA_frob (x : Q) : S.cA x ^ p ^ f = -S.cA x := by
  rw [cA, mul_pow, S.frob_two, S.Linv_frob, mul_neg]

theorem eq_one_of_aA_cA (x : Q) (ha : S.aA x = 0) (hc : S.cA x = 0) : x = 1 := by
  have h1 : S.piV (Baer.toB S.isBaer x) = 0 := by
    have : S.iota.symm (S.piV (Baer.toB S.isBaer x)) = 0 := ha
    rwa [AddEquiv.map_eq_zero_iff] at this
  have h2 : S.piZ (Baer.toB S.isBaer x) = 0 := by
    have h3 : S.Linv (S.piZ (Baer.toB S.isBaer x)) = 0 :=
      (mul_eq_zero.mp hc).resolve_left S.two_ne_zero_A
    exact S.Linv_injective (h3.trans (map_zero S.Linv).symm)
  have h4 := S.piV_add_piZ (Baer.toB S.isBaer x)
  rw [h1, h2, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, add_zero] at h4
  exact Baer.toB_eq_zero.mp h4.symm

theorem exists_aA_cA (a₀ c₀ : S.A) (hc₀ : c₀ ^ p ^ f = -c₀) :
    ∃ x : Q, S.aA x = a₀ ∧ S.cA x = c₀ := by
  have hhalf : (c₀ / 2) ^ p ^ f = -(c₀ / 2) := by
    rw [div_pow, S.frob_two, hc₀, neg_div]
  set z : S.Zs := S.L ⟨c₀ / 2, hhalf⟩ with hz
  refine ⟨Baer.ofB ((S.iota a₀ : S.V) + (z : S.V)), ?_, ?_⟩
  · rw [aA, Baer.toB_ofB, S.coordA_add, S.coordA_of_mem_Zs z.2, add_zero, coordA,
      S.piV_of_mem (S.iota a₀).2]
    exact S.iota.symm_apply_apply a₀
  · rw [cA, Baer.toB_ofB, map_add, S.piZ_eq_zero_iff.mpr (S.iota a₀).2, zero_add,
      S.piZ_of_mem z.2, S.Linv_eq hhalf rfl]
    field_simp [S.two_ne_zero_A]

omit [Finite G] in
theorem toB_conjQ (t : T) (x : Q) :
    Baer.toB S.isBaer (S.conjQ t x) = S.rho t (Baer.toB S.isBaer x) := rfl

theorem mem_Z_iff (x : Q) : (x : G) ∈ Z ↔ S.aA x = 0 := by
  rw [aA, coordA, AddEquiv.map_eq_zero_iff, S.piV_eq_zero_iff]
  rfl

theorem aA_conjQ (t : T) (x : Q) : S.aA (S.conjQ t x) = (S.tau t : S.A) * S.aA x := by
  rw [aA, aA, S.toB_conjQ, coordA, S.piV_rho, coordA]
  apply S.iota.injective
  rw [AddEquiv.apply_symm_apply, S.iota_tau_mul, AddEquiv.apply_symm_apply]

theorem cA_conjQ (t : T) (x : Q) :
    S.cA (S.conjQ t x) = (S.tau t : S.A) ^ p ^ f * (S.tau t : S.A) * S.cA x := by
  have h : S.piZ (S.rho t (Baer.toB S.isBaer x)) =
      ⟨S.rho t (S.piZ (Baer.toB S.isBaer x)), S.rho_mem_Zs t (S.piZ _).2⟩ :=
    Subtype.ext (S.piZ_rho t _)
  rw [cA, cA, S.toB_conjQ, h, S.Linv_rho]
  ring

end Hyp

end CFSG.UnitaryThreeRecognition.Heisenberg
