module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenX

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem exists_k (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) (hcard : Nat.card ↥X = p ^ 3) :
    ∃ k : ℕ, 2 ≤ k ∧ Nat.card ↥(iHull15 V₀ U H) = 2 ^ (p * k) ∧
      Nat.card ↥(v1Sub15 V₀ U) = 2 ^ ((p - 1) * k / 2) := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  obtain ⟨x, z, g, hH, hCz, hCx⟩ := hX.heis hcard
  have hI : IsElemAbelian 2 (iHull15 V₀ U H) :=
    B2F.isElemAbelian_mono (Hyp1510.iHull15_le_zSub15 V₀ U H)
      (c.hyp.fam.isElemAbelian_zSub15 c.cex)
  have hIN := Hyp1510.le_normalizer_iHull15 V₀ U H
  have hxN : x ∈ Subgroup.normalizer (iHull15 V₀ U H : Set G) := hIN (hX.le_H c hH.x_mem)
  have hzN : z ∈ Subgroup.normalizer (iHull15 V₀ U H : Set G) := hIN (hX.le_H c hH.z_mem)
  have hgN : g ∈ Subgroup.normalizer (iHull15 V₀ U H : Set G) := hIN (hX.le_H c hH.g_mem)
  have hvN : v ∈ Subgroup.normalizer (iHull15 V₀ U H : Set G) := hIN (c.hyp.V₀_le_H hX.mem)
  have hx : x ^ p = 1 := hH.x_pow
  have hz : z ^ p = 1 := hH.z_pow
  have hxz : x * z = z * x := hH.z_central x hH.x_mem
  have hgx : g * x * g⁻¹ = x * z := hH.g_conj_x
  have hgz : g * z = z * g := hH.z_central g hH.g_mem
  have hvx : v * x * v⁻¹ = x⁻¹ := hH.v_conj_x
  have hvz : v * z = z * v := hH.v_comm_z
  have hv : v * v = 1 := hX.mul_self c
  obtain ⟨k, hk1, -, hk3⟩ :=
    exists_card_eq_pow_of_inverting_involution c.p_ne_two hI hxN hzN hgN hvN hx hz hxz hgx hgz
      hvx hvz hv hCz hCx
  rw [hX.commutator_eq] at hk3
  refine ⟨k, ?_, hk1, hk3⟩
  have hZp : IsPGroup p ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card_dvd_pow (n := 1)
      (by simpa [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hz)
  have hZnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (iHull15 V₀ U H : Set G) :=
    Subgroup.zpowers_le.mpr hzN
  letI : MulAction ↥(Subgroup.zpowers z) ↥(iHull15 V₀ U H) :=
    MulAction.compHom _ (Subgroup.inclusion hZnorm)
  have hsmul : ∀ (a : ↥(Subgroup.zpowers z)) (i : ↥(iHull15 V₀ U H)),
      ((a • i : ↥(iHull15 V₀ U H)) : G) = (a : G) * (i : G) * (a : G)⁻¹ := by
    intro a i
    rfl
  have hfixed : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers z)
      ↥(iHull15 V₀ U H)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨?_, ?_⟩
    · refine ⟨fun u w => ?_⟩
      have key : ∀ t : ↥(MulAction.fixedPoints ↥(Subgroup.zpowers z) ↥(iHull15 V₀ U H)),
          ((t.1 : ↥(iHull15 V₀ U H)) : G) = 1 := by
        intro t
        have ht := (MulAction.mem_fixedPoints.mp t.2) ⟨z, Subgroup.mem_zpowers z⟩
        have hconj : z * ((t.1 : ↥(iHull15 V₀ U H)) : G) * z⁻¹ =
            ((t.1 : ↥(iHull15 V₀ U H)) : G) := by
          have := congrArg (fun s : ↥(iHull15 V₀ U H) => (s : G)) ht
          simpa [hsmul] using this
        have hcent : ((t.1 : ↥(iHull15 V₀ U H)) : G) ∈
            Subgroup.centralizer ({z} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact ((mul_inv_eq_iff_eq_mul).mp hconj).symm
        have hmem : ((t.1 : ↥(iHull15 V₀ U H)) : G) ∈
            iHull15 V₀ U H ⊓ Subgroup.centralizer ({z} : Set G) :=
          ⟨(t.1).2, hcent⟩
        rw [hCz] at hmem
        exact Subgroup.mem_bot.mp hmem
      apply Subtype.ext
      apply Subtype.ext
      rw [key u, key w]
    · exact ⟨1, by
        rw [MulAction.mem_fixedPoints]
        intro a
        apply Subtype.ext
        rw [hsmul, Subgroup.coe_one]
        group⟩
  have hmodI : Nat.card ↥(iHull15 V₀ U H) ≡ 1 [MOD p] := by
    have h := hZp.card_modEq_card_fixedPoints ↥(iHull15 V₀ U H)
    rwa [hfixed] at h
  rw [hk1] at hmodI
  rw [pow_mul] at hmodI
  have hfermat : 2 ^ p ≡ 2 [MOD p] := by
    have h : ((2 ^ p : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) := by
      push_cast
      exact ZMod.pow_card 2
    exact (ZMod.natCast_eq_natCast_iff (2 ^ p) 2 p).mp h
  have hmodk : 2 ^ k ≡ 1 [MOD p] := (hfermat.pow k).symm.trans hmodI
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero, pow_zero] at hk1
    have hne : v1Sub15 V₀ U ≠ ⊥ := c.cex.v1Sub15_ne_bot c.std
    have hgt : 1 < Nat.card ↥(v1Sub15 V₀ U) :=
      (Subgroup.one_lt_card_iff_ne_bot (v1Sub15 V₀ U)).mpr hne
    have hle : Nat.card ↥(v1Sub15 V₀ U) ≤ Nat.card ↥(iHull15 V₀ U H) :=
      Subgroup.card_le_of_le (Hyp1510.v1Sub15_le_iHull15 V₀ U H)
    omega
  have hk1ne : k ≠ 1 := by
    intro hk1eq
    rw [hk1eq, pow_one] at hmodk
    have hdvd : p ∣ 1 := by
      have := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmodk.symm
      simpa using this
    exact c.prime.not_dvd_one hdvd
  omega

theorem four_le_card_v1Sub15 (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) (hcard : Nat.card ↥X = p ^ 3) :
    4 ≤ Nat.card ↥(v1Sub15 V₀ U) := by
  obtain ⟨k, hk, -, h1⟩ := c.exists_k hX hcard
  have hp3 : 3 ≤ p := by
    have h2 := c.prime.two_le
    have h3 := c.p_ne_two
    omega
  rw [h1]
  have h4 : 2 ≤ (p - 1) * k / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    have : 2 * 2 ≤ (p - 1) * k := Nat.mul_le_mul (by omega) hk
    omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ ((p - 1) * k / 2) := Nat.pow_le_pow_right (by norm_num) h4

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
