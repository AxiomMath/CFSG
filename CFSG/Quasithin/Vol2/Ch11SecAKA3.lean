module

public import CFSG.Quasithin.Vol2.Ch11SecAKA1
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4K
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15c

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (torus_mem_stabW act_diag_sp mem_gammaW_one_of_fix
  odd_card_units)

namespace KA

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}

theorem torus_pow (π : ↥(StatedSp 2 K) →* ↥H) (g : StatedSp 2 K) (a : Kˣ) (k : ℕ) :
    ((π (g * lSp K (dGL (a, 1)) * g⁻¹) : ↥H) : MulAut W) ^ k =
      ((π (g * lSp K (dGL (a ^ k, 1)) * g⁻¹) : ↥H) : MulAut W) := by
  rw [← psiSp_apply, ← psiSp_apply, ← map_pow, ← map_pow, ← map_pow, Prod.pow_mk, one_pow]

end KA

theorem factPointTorusSp4_holds : Ch11.SecA.FactPointTorusSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  obtain ⟨f, hf, g, -, rfl⟩ := KA.exists_point_coords hn hK hW hπ hP hU
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  set U := hf.pre (gmapSp g (spLine K)).toAddSubgroup with hUdef
  set d := ((π (g * lSp K (dGL (a, 1)) * g⁻¹) : ↥H) : MulAut W) with hd
  have hpow : ∀ c : K, c ≠ 0 → ∃ k : ℕ, (a : K) ^ k = c := by
    intro c hc
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (ha (Units.mk0 c hc)) :
      Units.mk0 c hc ∈ Submonoid.powers a)
    exact ⟨k, by rw [← Units.val_pow_eq_pow_val, show a ^ k = Units.mk0 c hc from hk,
      Units.val_mk0]⟩
  have hdk : ∀ k : ℕ, ∀ u, f u ∈ gmapSp g (spLine K) →
      f ((d ^ k) u) = ((a : K) ^ k) • f u := by
    intro k u hu
    rw [hd, KA.torus_pow, act_diag_sp hf g (a ^ k) hu, Units.val_pow_eq_pow_val]
  have hdS : d ∈ Ch11.SecA.stabW U := torus_mem_stabW hf g a
  refine ⟨d, ⟨(π _).2, hdS⟩, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨M, hM⟩ : ∃ M, π M = ⟨h, hh.1⟩ := hf.onto ⟨h, hh.1⟩
    have hhM : h = ((π M : ↥H) : MulAut W) := by rw [hM]
    obtain ⟨c, hc⟩ := exists_scalar_of_stab_sp hf (g := g) (γ := M) fun w hw => by
      rw [← hhM]
      exact (Ch11.SecA.mem_stabW.mp hh.2 w).mp hw
    obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
    have hu₀U : f u₀ ∈ gmapSp g (spLine K) :=
      mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 := hc u₀ hu₀U
      rw [zero_smul, hf.act4, hu₀] at h1
      apply v0_ne_zero g
      have h2 := congrArg (fun v => mat 2 K M⁻¹ *ᵥ v) h1
      simpa only [mat_inv_mulVec, Matrix.mulVec_zero] using h2
    obtain ⟨k, hk⟩ := hpow c hc0
    refine ⟨k, ?_⟩
    have hdkH : (d ^ k)⁻¹ ∈ H := H.inv_mem (H.pow_mem (π _).2 k)
    have hdkS : (d ^ k)⁻¹ ∈ Ch11.SecA.stabW U :=
      (Ch11.SecA.stabW U).inv_mem ((Ch11.SecA.stabW U).pow_mem hdS k)
    refine mem_gammaW_one_of_fix hK4 hf g (H.mul_mem hh.1 hdkH)
      ((Ch11.SecA.stabW U).mul_mem hh.2 hdkS) fun u hu => ?_
    have hv : (d ^ k)⁻¹ u ∈ U := (Ch11.SecA.mem_stabW.mp hdkS u).mp hu
    rw [MulAut.mul_apply, hhM, hc _ hv, ← hk, ← hdk k _ hv, MulAut.apply_inv_self]
  · refine ⟨Nat.card Kˣ, odd_card_units, ?_⟩
    rw [hd, KA.torus_pow, pow_card_eq_one', show ((1 : Kˣ), (1 : Kˣ)) = 1 from rfl, map_one,
      map_one, mul_one, mul_inv_cancel, map_one]
    exact one_mem _
  · intro u hu w hw huZ hwZ
    have hu' : f u ∈ gmapSp g (spLine K) := hu
    have hw' : f w ∈ gmapSp g (spLine K) := hw
    obtain ⟨s, hs⟩ := mem_gmapSp_spLine_iff.mp hu'
    obtain ⟨t, ht⟩ := mem_gmapSp_spLine_iff.mp hw'
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hs
      exact huZ ((hf.ker u).mp hs)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ht
      exact hwZ ((hf.ker w).mp ht)
    obtain ⟨k, hk⟩ := hpow (t / s) (div_ne_zero ht0 hs0)
    refine ⟨k, (hf.eq_iff _ _).mp ?_⟩
    rw [hdk k u hu', hs, ht, hk, smul_smul, div_mul_cancel₀ _ hs0]

end CFSG.Quasithin.Vol2.KGNat
