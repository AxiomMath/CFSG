module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.AutItems
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Aut
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Structure
import CFSG.SignalizerFunctorTheorem.McBride.Models.Conj
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Arithmetic
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Dickson
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Setup

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Three

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {p : ℕ}

theorem eq_fixed_of_overgroup (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) :
    ∀ H : Subgroup PSL(2, GaloisField 3 p), signalizerFixedSubgroup f ≤ H → H ≠ ⊤ →
      H = signalizerFixedSubgroup f := fun _ hCH hH =>
  let h := isA4_fixed hp hcop f hf
  eq_of_overgroup hp (odd_of_coprime hp hcop) h.card h.nonabelian hCH hH

theorem fixedNormalizer_eq_fixed (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) :
    fixedNormalizer f = signalizerFixedSubgroup f :=
  (isA4_fixed hp hcop f hf).fixedNormalizer_eq (isSimpleGroup_of_prime hp)
    (eq_fixed_of_overgroup hp hcop f hf)

theorem itemC_of_transvecs (hp : p.Prime) {f : MulAut PSL(2, GaloisField 3 p)}
    (h1 : f (QuotientGroup.mk (transvecUp (GaloisField 3 p))) =
      QuotientGroup.mk (transvecUp (GaloisField 3 p)))
    (h2 : f (QuotientGroup.mk (transvecLow (GaloisField 3 p))) =
      QuotientGroup.mk (transvecLow (GaloisField 3 p))) : ItemC p f := by
  refine isPGroup_of_forall_coprime_orderOf_eq_one hp fun g hgcop => ?_
  have hfix : ∀ y ∈ signalizerFixedSubgroup f, (g : MulAut PSL(2, GaloisField 3 p)) y = y :=
    fun y hy => (mem_fixingSubgroup_iff _).mp g.2 y hy
  have hgcop' : Nat.Coprime p (orderOf (g : MulAut PSL(2, GaloisField 3 p))) := by
    rwa [Subgroup.orderOf_coe]
  obtain ⟨y, hy⟩ := exists_pglAction_of_coprime_orderOf hp _ hgcop'
  have hy1 : y = 1 := eq_one_of_pglAction_fixes
    (by rw [← hy]; exact hfix _ h1) (by rw [← hy]; exact hfix _ h2)
  apply Subtype.ext
  rw [hy, hy1, map_one]
  rfl

theorem itemG_of_transvecs (hp : p.Prime) {f : MulAut PSL(2, GaloisField 3 p)}
    (h : IsA4Subgroup (signalizerFixedSubgroup f))
    (hM : fixedNormalizer f = signalizerFixedSubgroup f)
    (h1 : f (QuotientGroup.mk (transvecUp (GaloisField 3 p))) =
      QuotientGroup.mk (transvecUp (GaloisField 3 p)))
    (h2 : f (QuotientGroup.mk (transvecLow (GaloisField 3 p))) =
      QuotientGroup.mk (transvecLow (GaloisField 3 p))) : ItemG p f := by
  intro g hg hgM hgF
  have hgC : ∀ x ∈ signalizerFixedSubgroup f, g x ∈ signalizerFixedSubgroup f := by
    intro x hx
    rw [← hM] at hx ⊢
    exact hgM x hx
  have hg2 : ∀ x ∈ signalizerFixedSubgroup f, (x⁻¹ * g x) ^ 2 = 1 := by
    intro x hx
    have hxM : x ∈ fixedNormalizer f := hM ▸ hx
    have h3 : x⁻¹ * g x ∈ fixedFitting f := by
      have := hgF x hxM
      rw [hM] at this
      exact this
    rw [h.fixedFitting_eq] at h3
    exact h3.2
  obtain ⟨c, hcC, hc⟩ := h.aut_inner g hgC hg2
  obtain ⟨y, rfl⟩ := exists_pglAction_of_coprime_orderOf hp g hg
  have hyc : y = Matrix.ProjectiveSpecialLinearGroup.toPGL c :=
    eq_toPGL_of_pglAction (hc _ h1) (hc _ h2)
  refine ⟨c, hM ▸ hcC, ?_⟩
  rw [hyc, pglAction_toPGL]

theorem itemO_of_card_normalizer (hp : p.Prime) (hodd : Odd p)
    {f : MulAut PSL(2, GaloisField 3 p)} (hM : Nat.card (fixedNormalizer f) = 12) : ItemO f := by
  have hp3 : 3 ≤ p := three_le_of_odd hp hodd
  have hodd1 := odd_three_pow_sub_one_div_two hodd
  have hne1 : (3 ^ p - 1) / 2 ≠ 1 := by
    have := le_three_pow hp3
    omega
  have hr12 : ∀ r : ℕ, r.Prime → (¬ r ∣ 12 ↔ r ≠ 2 ∧ r ≠ 3) := by
    intro r hr
    constructor
    · intro h
      exact ⟨fun h2 => h (h2 ▸ by norm_num), fun h3 => h (h3 ▸ by norm_num)⟩
    · rintro ⟨h2, h3⟩ hdvd
      have : r ∣ 2 ^ 2 * 3 := by simpa using hdvd
      rcases (Nat.Prime.dvd_mul hr).mp this with h | h
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne1
    refine ⟨r, hr, ?_, ?_⟩
    · rw [card_psl2 hp, card_formula_eq]
      exact (hrd.mul_left _).mul_right _
    · rw [hM, hr12 r hr]
      refine ⟨fun h2 => ?_, fun h3 => ?_⟩
      · subst h2
        exact (Nat.not_even_iff_odd.mpr hodd1) (even_iff_two_dvd.mpr hrd)
      · subst h3
        exact not_three_dvd_three_pow_sub_one hp.pos
          (hrd.trans (Nat.div_dvd_of_dvd (by
            have := three_pow_mod_four hodd
            omega)))
  · intro r hr _ hrM R
    rw [hM, hr12 r hr] at hrM
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
    refine isMulCommutative_of_coprime_six hp hodd (R : Subgroup PSL(2, GaloisField 3 p)) ?_
    rw [hk]
    refine Nat.Coprime.pow_left k ?_
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hr Nat.prime_two).mpr hrM.1)
      ((Nat.coprime_primes hr Nat.prime_three).mpr hrM.2)

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Three
