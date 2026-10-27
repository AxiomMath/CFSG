module

public import CFSG.Permutation.UnitaryThreeRecognition.HeisSetup
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

namespace Hyp

variable {G : Type*} [Group G] [Finite G] {Q T Z W : Subgroup G} {p f d : ℕ} [Fact p.Prime]
  (S : Hyp Q T Z W p f d)
include S

theorem nontrivial_Vp : Nontrivial S.Vp := by
  rw [← Finite.one_lt_card_iff_nontrivial, S.card_Vp]
  exact one_lt_pow' (Fact.out : p.Prime).one_lt (by have := S.hf; omega)

abbrev A : Type _ := SchurField (Set.range S.rhoV) S.isIrred_Vp S.nontrivial_Vp

omit [Finite G] in
theorem rhoV_comm (s t : T) : S.rhoV s * S.rhoV t = S.rhoV t * S.rhoV s := by
  ext v
  change S.rho s (S.rho t v) = S.rho t (S.rho s v)
  rw [← Module.End.mul_apply, S.rho_comm, Module.End.mul_apply]

@[expose] noncomputable def tauA (t : T) : S.A :=
  SchurField.mk _ _ (S.rhoV t) (by rintro _ ⟨s, rfl⟩; exact S.rhoV_comm s t)

theorem toEnd_tauA (t : T) : SchurField.toEnd _ _ (S.tauA t) = S.rhoV t := rfl

theorem tauA_mul (s t : T) : S.tauA (s * t) = S.tauA s * S.tauA t := by
  apply SchurField.toEnd_injective
  rw [map_mul, toEnd_tauA, toEnd_tauA, toEnd_tauA]
  ext v
  change S.rho (s * t) v = S.rho s (S.rho t v)
  rw [S.rho_mul, Module.End.mul_apply]

theorem tauA_one : S.tauA 1 = 1 := by
  apply SchurField.toEnd_injective
  rw [map_one, toEnd_tauA]
  ext v
  change S.rho 1 v = v
  rw [S.rho_one, Module.End.one_apply]

@[expose] noncomputable def tau : T →* S.Aˣ :=
  MonoidHom.toHomUnits
    { toFun := S.tauA
      map_one' := S.tauA_one
      map_mul' := S.tauA_mul }

theorem coe_tau (t : T) : ((S.tau t : S.Aˣ) : S.A) = S.tauA t := rfl

theorem tau_smul (t : T) (v : S.Vp) : ((S.tau t : S.Aˣ) : S.A) • v = S.rhoV t v := rfl

theorem tau_injective : Function.Injective S.tau := by
  rw [injective_iff_map_eq_one]
  intro t ht
  by_contra hne
  have ht' : (t : G) ≠ 1 := fun h => hne (Subtype.ext h)
  have := S.nontrivial_Vp
  obtain ⟨v, hv⟩ := exists_ne (0 : S.Vp)
  have h1 : S.rhoV t v = v := by
    rw [← S.tau_smul, ht, Units.val_one, one_smul]
  have h2 : S.rho t (v : S.V) = v := congrArg Subtype.val h1
  have hZ : (v : S.V) ∈ S.Zs := by
    apply S.hfree t t.2 ht' _ (Baer.ofB (v : S.V)).2
    have h3 := congrArg (fun u : S.V => ((Baer.ofB u : Q) : G)) h2
    simp only [coe_ofB_rho] at h3
    calc (t : G) * (Baer.ofB (v : S.V) : Q)
        = ((t : G) * (Baer.ofB (v : S.V) : Q) * (t : G)⁻¹) * t := by group
      _ = (Baer.ofB (v : S.V) : Q) * t := by rw [h3]
  have := Submodule.disjoint_def.mp S.isCompl_Zs_Vp.disjoint _ hZ v.2
  exact hv (Subtype.ext this)

theorem card_A : Nat.card S.A = (p ^ f) ^ 2 := by
  have : Fintype S.A := Fintype.ofFinite _
  have : Fintype S.Vp := Fintype.ofFinite _
  have hn : Nat.card S.A ^ Module.finrank S.A S.Vp = (p ^ f) ^ 2 := by
    rw [Nat.card_eq_fintype_card, ← Module.card_eq_pow_finrank (K := S.A) (V := S.Vp),
      ← Nat.card_eq_fintype_card, S.card_Vp, pow_mul']
  have hT : Nat.card T ∣ Nat.card S.A - 1 := by
    have h1 := Subgroup.card_subgroup_dvd_card S.tau.range
    rwa [Nat.card_congr (MonoidHom.ofInjective S.tau_injective).toEquiv.symm,
      Nat.card_units] at h1
  have ht : Nat.card T * d = (p ^ f) ^ 2 - 1 := by rw [S.hTcard, pow_mul']
  have h1 := eq_one_of_pow_eq_sq S.three_le_q S.d_le_three hn ht hT
  rw [h1, pow_one] at hn
  exact hn

theorem charP_A : CharP S.A p := by
  have h : ((p : ℕ) : S.A) = 0 := by
    apply SchurField.toEnd_injective
    rw [map_natCast, map_zero]
    ext v
    rw [Module.End.natCast_apply, LinearMap.zero_apply, ← Nat.cast_smul_eq_nsmul (ZMod p),
      ZMod.natCast_self, zero_smul]
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h

@[expose] noncomputable def v0 : S.Vp := Classical.choose (@exists_ne _ S.nontrivial_Vp 0)

theorem v0_ne_zero : S.v0 ≠ 0 := Classical.choose_spec (@exists_ne _ S.nontrivial_Vp 0)

@[expose] noncomputable def iotaAdd : S.A →+ S.Vp where
  toFun c := c • S.v0
  map_zero' := zero_smul _ _
  map_add' c c' := add_smul c c' S.v0

theorem iotaAdd_bijective : Function.Bijective S.iotaAdd := by
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, by rw [S.card_A, S.card_Vp, pow_mul']⟩
  rw [injective_iff_map_eq_zero]
  intro c hc
  exact (smul_eq_zero.mp hc).resolve_right S.v0_ne_zero

@[expose] noncomputable def iota : S.A ≃+ S.Vp := AddEquiv.ofBijective S.iotaAdd S.iotaAdd_bijective

theorem iota_apply (c : S.A) : S.iota c = c • S.v0 := rfl

theorem iota_mul (c c' : S.A) : S.iota (c * c') = c • S.iota c' := by
  rw [iota_apply, iota_apply, mul_smul]

theorem iota_tau_mul (t : T) (c : S.A) :
    S.iota ((S.tau t : S.A) * c) = S.rhoV t (S.iota c) := by
  rw [iota_mul, tau_smul]

end Hyp

end CFSG.UnitaryThreeRecognition.Heisenberg
