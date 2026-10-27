module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreOdd
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeOddFrame

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}
  {ρ : ↥K →* Equiv.Perm (ZMod p)}

theorem nine3_comm_ne_one (hc : Nine3Choice V T A K S X p g x) (hρ : Nine3FibreAct K S p x ρ)
    {U U' : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) (hU' : U' ∈ omegaIn V K (nineE V K))
    {c c' : ZMod p} (h : Nine3Fib K p ρ U c) (h' : Nine3Fib K p ρ U' c') (hne : c ≠ c')
    {i : G} (hi : i ∈ U) (hi1 : i ≠ 1) {w : G} (hw : w ∈ U') (hwR : w ∉ pCoreOf 2 K) :
    i * w ≠ w * i := by
  intro hcomm
  have hp : p.Prime := hc.core.hyp.base.prime
  have hp2 : p ≠ 2 := hc.core.hyp.base.odd
  obtain ⟨g₁, hUg₁, -, -⟩ := mem_omegaSet.mp hU.1
  obtain ⟨g₂, hU'g₂, -, -⟩ := mem_omegaSet.mp hU'.1
  have hiV : i ∈ conjSubgroup V g₁ := by rwa [← hUg₁]
  have hwcent : w ∈ Subgroup.centralizer ({i} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm
  have hwN : w ∈ normalizer (conjSubgroup V g₁ : Set G) :=
    centralizer_le_normalizer_conj hc.core.hyp7.2.2 g₁ hiV hi1 hwcent
  obtain ⟨-, -, -, hnleU⟩ := mem_omegaSet.mp hU.1
  obtain ⟨u, huU, huR⟩ := SetLike.not_le_iff_exists.mp hnleU
  have huV : u ∈ conjSubgroup V g₁ := by rwa [← hUg₁]
  have hwV : w ∈ conjSubgroup V g₂ := by rwa [← hU'g₂]
  have hP : IsPGroup 2 (Subgroup.closure ({w, u} : Set G)) :=
    isPGroup_closure_pair_of_mem_normalizer hc.core.hyp7.1 (d := w) (e := u) hwV huV hwN
  have hpow : (w * u) ^ p = 1 :=
    nine3_fib_pow hc hρ hU' hU h' h hne.symm w hw hwR u huU huR
  have hwumem : w * u ∈ Subgroup.closure ({w, u} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  obtain ⟨k, hk⟩ := hP.exists_orderOf_dvd_pow
    (⟨w * u, hwumem⟩ : Subgroup.closure ({w, u} : Set G))
  have hk' : orderOf (w * u) ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_coe
      (⟨w * u, hwumem⟩ : Subgroup.closure ({w, u} : Set G))] at hk
    exact hk
  have hord_dvd_p : orderOf (w * u) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hcop2 : Nat.Coprime p 2 :=
    hp.coprime_iff_not_dvd.mpr (by
      intro h2
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
      · exact hp.ne_one h1
      · exact hp2 h1)
  have hcop : Nat.Coprime p (2 ^ k) := hcop2.pow_right k
  have hwueq : w * u = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord_dvd_p hk')
  have hu2 : u * u = 1 := by
    have hel : IsElemAbelian 2 (conjSubgroup V g₁) :=
      E3.isElemAbelian_conjSubgroup hc.core.hyp7.1 g₁
    have hh := hel.2 u huV
    rwa [pow_two] at hh
  have hw_eq_u : w = u := by
    have h1 : w⁻¹ = u := inv_eq_of_mul_eq_one_right hwueq
    have h2 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    calc w = (w⁻¹)⁻¹ := (inv_inv w).symm
      _ = u⁻¹ := by rw [h1]
      _ = u := h2
  have hku : (⟨u, hU.2 huU⟩ : ↥K) = ⟨w, hU'.2 hw⟩ := Subtype.ext hw_eq_u.symm
  have hρeq : zmodRefl p c = zmodRefl p c' := by
    rw [← h ⟨u, hU.2 huU⟩ huU huR, ← h' ⟨w, hU'.2 hw⟩ hw hwR, hku]
  exact hne (zmodRefl_inj hp hp2 hρeq)

end CFSG.LocalAnalysis.WeakClosure81
