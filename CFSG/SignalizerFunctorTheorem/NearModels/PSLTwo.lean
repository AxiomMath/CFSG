module

public import CFSG.Open.SignalizerFunctorDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.SignalizerFunctorTheorem.NearModels.Conjugacy
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic
import CFSG.Walter.PSL2Facts.FieldAut

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.NearModels

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  PSLTwo

theorem psl2_card_pSubgroup_dvd (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p
      (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ℓ p))))
    (P : Subgroup (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ℓ p))))
    (hP : IsPGroup p P) : Nat.card P ∣ p := by
  classical
  let e := semilinearEquivAut (GaloisField ℓ p)
  let π : MulAut (PSL2 (GaloisField ℓ p)) →* (GaloisField ℓ p ≃+* GaloisField ℓ p) :=
    SemidirectProduct.rightHom.comp e.symm.toMonoidHom
  have hcop' := coprime_natCard_pgl2 (GaloisField ℓ p) hp hcop
  have hinj : Function.Injective (π.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hxP⟩ hx
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
    have hxk : x ^ p ^ k = 1 := congrArg Subtype.val hk
    have hx' : (e.symm x).right = 1 := hx
    have hy : e.symm x = SemidirectProduct.inl (e.symm x).left :=
      SemidirectProduct.ext rfl (by simpa using hx')
    have hxN : x ^ Nat.card (PGL2 (GaloisField ℓ p)) = 1 := by
      apply e.symm.injective
      rw [map_pow, hy, ← map_pow, pow_card_eq_one', map_one, map_one]
    have h1 : x ^ (p ^ k).gcd (Nat.card (PGL2 (GaloisField ℓ p))) = 1 :=
      pow_gcd_eq_one.mpr ⟨hxk, hxN⟩
    rw [Nat.Coprime.gcd_eq_one (hcop'.pow_left k), pow_one] at h1
    exact Subtype.ext h1
  have := Subgroup.card_dvd_of_injective _ hinj
  rwa [natCard_ringEquiv_galoisField ℓ hp.ne_zero] at this

theorem psl2_fixedSubgroup_mulEquiv (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p
      (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ℓ p))))
    (f : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ℓ p)))
    (hf : orderOf f = p) :
    Nonempty
      (signalizerFixedSubgroup f ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod ℓ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := odd_of_coprime_natCard_psl2 (GaloisField ℓ p) hp hcop
  have hGal : Nat.card (GaloisField ℓ p ≃+* GaloisField ℓ p) = p :=
    natCard_ringEquiv_galoisField ℓ hp.ne_zero
  have : Finite (GaloisField ℓ p ≃+* GaloisField ℓ p) :=
    Nat.finite_of_card_ne_zero (by rw [hGal]; exact hp.ne_zero)
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' p (by rw [hGal])
  set φ : MulAut (PSL2 (GaloisField ℓ p)) := psl2FieldAut (GaloisField ℓ p) σ with hφdef
  have hφ : orderOf φ = p := by
    rw [hφdef, orderOf_injective (psl2FieldAut (GaloisField ℓ p))
      (psl2FieldAut_injective (GaloisField ℓ p)) σ, hσ]
  set F0 := FixedPoints.subfield (Subgroup.zpowers σ) (GaloisField ℓ p) with hF0
  have hφfix : signalizerFixedSubgroup φ = (CFSG.Walter.psl2Map F0.subtype).range := by
    ext y
    change φ y = y ↔ _
    rw [hφdef, CFSG.Walter.psl2FieldAut_eq_psl2Map]
    exact CFSG.Walter.psl2Map_eq_self_iff σ (by rw [hσ]; exact hodd) y
  obtain ⟨e1⟩ := signalizerFixedSubgroup_mulEquiv_of_orderOf_eq
    (psl2_card_pSubgroup_dvd ℓ hp hcop) hf hφ
  let e2 : signalizerFixedSubgroup φ ≃* (CFSG.Walter.psl2Map F0.subtype).range :=
    MulEquiv.subgroupCongr hφfix
  let e3 : (CFSG.Walter.psl2Map F0.subtype).range ≃* PSL2 F0 :=
    (MonoidHom.ofInjective (CFSG.Walter.psl2Map_injective _)).symm
  obtain ⟨-, hF0card⟩ := CFSG.Walter.card_fixedSubfield_galoisField (p := ℓ) hp.ne_zero σ
  rw [hσ, Nat.div_self hp.pos, pow_one] at hF0card
  have : Fintype F0 := Fintype.ofFinite F0
  have e4 : F0 ≃+* ZMod ℓ := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, hF0card, ZMod.card])
  exact ⟨e1.trans (e2.trans (e3.trans (psl2RingEquiv e4)))⟩

end CFSG.SignalizerFunctorTheorem.NearModels
