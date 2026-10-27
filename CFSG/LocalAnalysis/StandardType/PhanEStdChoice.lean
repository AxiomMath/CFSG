module

public import CFSG.LocalAnalysis.StandardType.PhanEStdGeom
public import CFSG.LocalAnalysis.StandardType.PhanEStdTransport
public import CFSG.LocalAnalysis.StandardType.PhanEFiniteField
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LocalAnalysis.StandardType.PhanEStdE6Input
public import CFSG.LocalAnalysis.StandardType.PhanEStdE7Input
public import CFSG.LocalAnalysis.StandardType.PhanEStdE8Input
public import CFSG.LocalAnalysis.StandardType.PhanEStdE7Fix
public import CFSG.LocalAnalysis.StandardType.PhanEStdE8Fix

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary

section Transport

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {G : Type} [Group G]

@[expose] def PhanEConfig.ofEq {n : ℕ} {M M' : CoxeterMatrix (Fin n)} (h : M = M')
    (c : PhanEConfig K f M G) : PhanEConfig K f M' G :=
  h ▸ c

theorem PhanEConfig.iota_ofEq {n : ℕ} {M M' : CoxeterMatrix (Fin n)}
    (c : PhanEConfig K f M G) (h : M = M') (i : Fin n) :
    (c.ofEq h).S.ι i = c.S.ι i := by
  cases h
  rfl

theorem PhanEConfig.bridge_ofEq {n : ℕ} {M M' : CoxeterMatrix (Fin n)} (h : M = M')
    (c : PhanEConfig K f M G) : (c.ofEq h).Bridge ↔ c.Bridge := by
  subst h
  rfl

end Transport

section Field

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem one_le_of_four_le_two_pow (hq : 4 ≤ 2 ^ f) : 1 ≤ f := by
  refine Nat.one_le_iff_ne_zero.2 ?_
  rintro rfl
  norm_num at hq

theorem exists_mul_unitaryInvolution_eq (hK : Nat.card K = (2 ^ f) ^ 2) (s : K) (hs : s ≠ 0)
    (hθs : unitaryInvolution K 2 f s = s) : ∃ a : K, a * unitaryInvolution K 2 f a = s := by
  obtain ⟨a, ha⟩ := exists_norm_eq_of_fixed hK hθs hs
  exact ⟨a, by rw [mul_comm]; exact ha⟩

@[expose] noncomputable def fqEmbed (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    GaloisField 2 f →+* K :=
  (exists_fixed_embedding hK hf).choose

theorem unitaryInvolution_fqEmbed (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (c : GaloisField 2 f) : unitaryInvolution K 2 f (fqEmbed hK hf c) = fqEmbed hK hf c :=
  (exists_fixed_embedding hK hf).choose_spec.1 c

theorem exists_fqEmbed_eq (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (c : K)
    (hc : unitaryInvolution K 2 f c = c) : ∃ c', fqEmbed hK hf c' = c :=
  (exists_fixed_embedding hK hf).choose_spec.2 c hc

theorem frobQ_eq_unitaryInvolution (c : GaloisField 2 (2 * f)) :
    Exceptional.frobQ 2 f c = unitaryInvolution (GaloisField 2 (2 * f)) 2 f c := by
  rw [unitaryInvolution_apply]
  exact iterateFrobenius_def 2 f c

@[expose] noncomputable def e6Kappa (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    K ≃+* GaloisField 2 (2 * f) :=
  (exists_equiv_unitaryInvolution hK (card_galoisField_two_mul' hf)).choose

theorem e6Kappa_spec (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (c : K) :
    e6Kappa hK hf (unitaryInvolution K 2 f c) = Exceptional.frobQ 2 f (e6Kappa hK hf c) := by
  rw [frobQ_eq_unitaryInvolution]
  exact (exists_equiv_unitaryInvolution hK (card_galoisField_two_mul' hf)).choose_spec c

end Field

section FieldE6

variable {f : ℕ}

theorem exists_frobQ_ne (hf : 1 ≤ f) :
    ∃ c : GaloisField 2 (2 * f), Exceptional.frobQ 2 f c ≠ c := by
  obtain ⟨c, hc⟩ := unitaryInvolution_ne (card_galoisField_two_mul' hf) hf
  exact ⟨c, by rw [frobQ_eq_unitaryInvolution]; exact hc⟩

theorem exists_mul_frobQ_eq (hf : 1 ≤ f) (s : GaloisField 2 (2 * f)) (hs : s ≠ 0)
    (hθs : Exceptional.frobQ 2 f s = s) : ∃ a, a * Exceptional.frobQ 2 f a = s := by
  rw [frobQ_eq_unitaryInvolution] at hθs
  obtain ⟨a, ha⟩ := exists_mul_unitaryInvolution_eq (card_galoisField_two_mul' hf) s hs hθs
  exact ⟨a, by rw [frobQ_eq_unitaryInvolution]; exact ha⟩

end FieldE6

section E6

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def e6StdConfig (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    PhanEConfig K f CoxeterMatrix.E₆ (lieUniversal .twistedE6 0 2 f Nat.prime_two).K :=
  ((e6StdInput (Exceptional.frobQ 2 f) (Exceptional.frobQ_frobQ 2 f hf) (exists_frobQ_ne hf)
      (exists_mul_frobQ_eq hf)).config
    (e6FrobFixEquiv (Exceptional.frobQ 2 f) (Exceptional.frobQ_frobQ 2 f hf))
    (e6Kappa hK hf) (e6Kappa_spec hK hf)).ofEq (coxeterMatrix_e6Datum (GaloisField 2 (2 * f)))

theorem e6StdConfig_bridge (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e6StdConfig K f hK (one_le_of_four_le_two_pow hq)).Bridge :=
  (PhanEConfig.bridge_ofEq _ _).2 (StdInput.config_bridge _ _ _ _ hK hq)

end E6

section E7

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def e7StdConfig (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    PhanEConfig K f CoxeterMatrix.E₇ (lieUniversal .E7 0 2 f Nat.prime_two).K :=
  ((e7StdInput (unitaryInvolution K 2 f : K →+* K) (unitaryInvolution_involutive hK)
      (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)).config
    (e7FrobFixEquiv (unitaryInvolution K 2 f : K →+* K) (unitaryInvolution_involutive hK)
      (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf) (unitaryInvolution_fqEmbed hK hf)
      (exists_fqEmbed_eq hK hf))
    (RingEquiv.refl K) (fun _ => rfl)).ofEq (coxeterMatrix_e7Datum K)

theorem e7StdConfig_bridge (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e7StdConfig K f hK (one_le_of_four_le_two_pow hq)).Bridge :=
  (PhanEConfig.bridge_ofEq _ _).2 (StdInput.config_bridge _ _ _ _ hK hq)

end E7

section E8

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def e8StdConfig (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    PhanEConfig K f CoxeterMatrix.E₈ (lieUniversal .E8 0 2 f Nat.prime_two).K :=
  ((e8StdInput (unitaryInvolution K 2 f : K →+* K) (unitaryInvolution_involutive hK)
      (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)).config
    (e8FrobFixEquiv (unitaryInvolution K 2 f : K →+* K) (unitaryInvolution_involutive hK)
      (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf) (unitaryInvolution_fqEmbed hK hf)
      (exists_fqEmbed_eq hK hf))
    (RingEquiv.refl K) (fun _ => rfl)).ofEq (coxeterMatrix_e8Datum K)

theorem e8StdConfig_bridge (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e8StdConfig K f hK (one_le_of_four_le_two_pow hq)).Bridge :=
  (PhanEConfig.bridge_ofEq _ _).2 (StdInput.config_bridge _ _ _ _ hK hq)

end E8

section Choice

@[expose] noncomputable def stdChoice : PhanEConfigChoice :=
  fun K _ _ f _ hK hq =>
    { e6 := e6StdConfig K f hK (one_le_of_four_le_two_pow hq)
      e7 := e7StdConfig K f hK (one_le_of_four_le_two_pow hq)
      e8 := e8StdConfig K f hK (one_le_of_four_le_two_pow hq) }

theorem phanEBridge_stdChoice : PhanEBridge stdChoice := fun K _ _ f _ hK hq =>
  ⟨e6StdConfig_bridge K f hK hq, e7StdConfig_bridge K f hK hq, e8StdConfig_bridge K f hK hq⟩

end Choice

end CFSG.ClassicalInvolution.Phan.PhanE

end
