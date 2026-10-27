module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# p-element extraction for the weak semilinear endpoint

From a finite normal nilpotent subgroup `N ◁ A` of odd order whose field
projection is nontrivial, extract an odd prime `p`, a field automorphism
`σ` of order `p`, and a normal `p`-subgroup `P` of `F(A)` containing an
element `a₀` with `rightHom a₀ = σ` and `p`-power order.

The proof:  the projection image of `N' = N.map A.subtype` is nontrivial,
so by Cauchy's theorem some element `a` of the nilpotent group `N'` has
`p`-power order with `orderOf (rightHom a) = p` (the arithmetic uses the
`padicValNat`/`divMaxPow` decomposition of orders); the `p`-Sylow of the
nilpotent `F(A)` containing `a` is normal in `F(A)`.
-/

set_option linter.unusedVariables false in

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- The Fitting subgroup of a subgroup is nilpotent (as an ambient
subgroup). -/
private theorem fittingSubgroupOf_isNilpotent_local
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Group.IsNilpotent (↥(fittingSubgroupOf H)) := by
  change Group.IsNilpotent (↥((fittingSubgroup (↥H)).map H.subtype))
  have : Group.IsNilpotent (fittingSubgroup (↥H)) := by infer_instance
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective (fittingSubgroup (↥H)) H.subtype H.subtype_injective)

/-- A number prime to `p` dividing `n` divides the `p`-free part of `n`. -/
private theorem divMaxPow_dvd_of_coprime_dvd
    (p m n : ℕ) (hcop : Nat.Coprime p m) (h : m ∣ n) :
    m ∣ n.divMaxPow p := by
  have hdecomp := Nat.pow_padicValNat_mul_divMaxPow p n
  rw [← hdecomp] at h
  have hcop' : Nat.Coprime m (p ^ padicValNat p n) :=
    hcop.symm.pow_right (padicValNat p n)
  rw [mul_comm] at h
  exact hcop'.dvd_of_dvd_mul_right h

/-- In a finite nilpotent group of odd order, if the image of a
homomorphism is nontrivial, then some element of prime order `p` in the
image comes from a `p`-element of the domain. -/
private theorem exists_p_element_prime_order_image_of_nontrivial
    {N C : Type u} [Group N] [Finite N] [Group C] [Finite C]
    (hNnil : Group.IsNilpotent N) (hNodd : Odd (Nat.card N))
    (f : N →* C)
    (hker : ∃ n : N, f n ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      ∃ a : N, IsPGroup p (Subgroup.zpowers a) ∧ orderOf (f a) = p := by
  classical
  obtain ⟨n₀, hn₀⟩ := hker
  have hord1 : orderOf (f n₀) ≠ 1 := by
    intro h
    apply hn₀
    exact (orderOf_eq_one_iff).mp h
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    have hdvdN : orderOf (f n₀) ∣ Nat.card N := by
      have h₁ : orderOf (f n₀) ∣ orderOf n₀ := orderOf_map_dvd f n₀
      have h₂ : orderOf n₀ ∣ Nat.card N := by
        simpa using (Subgroup.orderOf_dvd_natCard (⊤ : Subgroup N) (by trivial))
      exact h₁.trans h₂
    have hodd : Odd (orderOf (f n₀)) := Odd.of_dvd_nat hNodd hdvdN
    exact (Nat.Prime.odd_of_ne_two hp) (fun h2 => hodd.not_two_dvd_nat (by
      rw [← h2]
      exact hpdvd))
  let m₁ := orderOf (f n₀)
  let m := orderOf n₀
  have hm_ne0 : m ≠ 0 := by
    exact ne_of_gt (orderOf_pos n₀)
  have hord1' : m₁ ≠ 0 := by
    intro h
    have hdvd : m₁ ∣ m := by
      simpa [m₁, m] using orderOf_map_dvd f n₀
    rw [h] at hdvd
    exact hm_ne0 (Nat.eq_zero_of_zero_dvd hdvd)
  let m₁' := m₁.divMaxPow p
  let e₁ := padicValNat p m₁
  have hdec1 : m₁ = p ^ e₁ * m₁' := by
    rw [show p ^ e₁ * m₁' = m₁' * p ^ e₁ by rw [mul_comm]]
    simpa [e₁, m₁'] using (Nat.pow_padicValNat_mul_divMaxPow p m₁)
  have he1pos : 0 < e₁ := by
    have hdiv : p ∣ p ^ e₁ := by
      change p ∣ m₁ at hpdvd
      rw [hdec1] at hpdvd
      exact (hp.dvd_mul.mp hpdvd).resolve_right (by
        exact Nat.not_dvd_divMaxPow hp.one_lt hord1')
    rcases hdiv with ⟨k, hk⟩
    by_contra h0
    have he0 : e₁ = 0 := by omega
    rw [he0, pow_zero] at hk
    exact hp.ne_one (Nat.dvd_one.mp ⟨k, hk⟩)
  let m₀ := m.divMaxPow p
  have hp_not_dvd_m0 : ¬ p ∣ m₀ := by
    exact Nat.not_dvd_divMaxPow hp.one_lt hm_ne0
  have hdec : m = p ^ padicValNat p m * m₀ := by
    rw [show p ^ padicValNat p m * m₀ = m₀ * p ^ padicValNat p m by rw [mul_comm]]
    simpa [m₀] using (Nat.pow_padicValNat_mul_divMaxPow p m)
  -- m₁' divides m₀
  have hm1p_dvd_m0 : m₁' ∣ m₀ := by
    have hm1dvd_m : m₁ ∣ m := by
      simpa [m₁, m] using orderOf_map_dvd f n₀
    have hm1p_dvd_m : m₁' ∣ m := by
      have h : m₁' ∣ m₁ := by
        rw [hdec1]
        simpa [mul_comm] using (dvd_mul_right m₁' (p ^ e₁))
      exact h.trans hm1dvd_m
    exact divMaxPow_dvd_of_coprime_dvd p m₁' m
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (by
        exact Nat.not_dvd_divMaxPow hp.one_lt hord1'))
      hm1p_dvd_m
  have hm₀pos : 0 < m₀ := Nat.pos_of_ne_zero (by
    intro hm₀₀
    exact hm_ne0 (by
      rw [hdec, hm₀₀]
      simp))
  have hm₁'pos : 0 < m₁' := Nat.pos_of_dvd_of_pos hm1p_dvd_m0 hm₀pos
  rcases hm1p_dvd_m0 with ⟨c, hc⟩
  have hc_pfree : ¬ p ∣ c := by
    intro hpc
    apply hp_not_dvd_m0
    rw [hc]
    rw [mul_comm]
    exact dvd_mul_of_dvd_left hpc m₁'
  -- a := (n₀^m₀)^(p^(e₁-1))
  let a : N := (n₀ ^ m₀) ^ (p ^ (e₁ - 1))
  have ha0ord : orderOf (n₀ ^ m₀) = p ^ padicValNat p m := by
    have hgcd : Nat.gcd m m₀ = m₀ := by
      apply Nat.gcd_eq_right_iff_dvd.mpr
      use p ^ padicValNat p m
      rw [mul_comm]
      exact hdec
    have hpow := orderOf_pow (n := m₀) n₀
    rw [hgcd] at hpow
    rw [hpow]
    let e : ℕ := padicValNat p m
    change m / m₀ = p ^ e
    rw [hdec]
    rw [mul_comm]
    rw [Nat.mul_div_right _ (Nat.pos_of_ne_zero (by
      intro hm₀
      exact hm_ne0 (by
        calc
          m = p ^ padicValNat p m * m₀ := hdec
          _ = p ^ padicValNat p m * 0 := by rw [hm₀]
          _ = 0 := by simp)))]
  have hord_a : ∃ k : ℕ, orderOf a = p ^ k := by
    have hdvd : orderOf a ∣ p ^ padicValNat p m := by
      have h₁ : orderOf a ∣ orderOf (n₀ ^ m₀) := by
        simpa [a] using orderOf_pow_dvd (p ^ (e₁ - 1))
      rwa [ha0ord] at h₁
    rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨k, _hk, hk⟩
    exact ⟨k, hk⟩
  have hord_fa : orderOf (f a) = p := by
    have hfa : f a = (f n₀) ^ (m₀ * p ^ (e₁ - 1)) := by
      change f ((n₀ ^ m₀) ^ (p ^ (e₁ - 1))) = (f n₀) ^ (m₀ * p ^ (e₁ - 1))
      rw [map_pow]
      rw [map_pow]
      rw [← pow_mul]
    rw [hfa]
    have hpow := orderOf_pow (n := m₀ * p ^ (e₁ - 1)) (f n₀)
    rw [hpow]
    -- gcd(m₁, m₀·p^{e₁-1}) = m₁'·p^{e₁-1}
    have hgcd : Nat.gcd m₁ (m₀ * p ^ (e₁ - 1)) = m₁' * p ^ (e₁ - 1) := by
      rw [hdec1, hc]
      rw [mul_assoc]
      rw [show p ^ e₁ * m₁' = m₁' * p ^ e₁ by rw [mul_comm]]
      rw [Nat.gcd_mul_left]
      congr 1
      rw [show p ^ e₁ = p ^ (e₁ - 1) * p by
        rw [← pow_succ]
        congr 1
        omega]
      rw [mul_comm c (p ^ (e₁ - 1))]
      rw [Nat.gcd_mul_left]
      rw [show p.gcd c = 1 by
        exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hc_pfree).gcd_eq_one]
      rw [mul_one]
    rw [hgcd]
    change m₁ / (m₁' * p ^ (e₁ - 1)) = p
    rw [hdec1]
    rw [show p ^ e₁ = p ^ (e₁ - 1) * p by
      rw [← pow_succ]
      congr 1
      omega]
    rw [mul_assoc]
    rw [mul_comm p m₁']
    rw [← mul_assoc]
    rw [show m₁' * p ^ (e₁ - 1) = p ^ (e₁ - 1) * m₁' by rw [mul_comm]]
    rw [Nat.mul_div_right _ (Nat.pos_of_ne_zero (by
      exact mul_ne_zero (pow_ne_zero (e₁ - 1) hp.ne_zero) (ne_of_gt hm₁'pos)))]
  refine ⟨p, hp, hpodd, a, ?_, hord_fa⟩
  rcases hord_a with ⟨K, hK⟩
  exact IsPGroup.of_card (n := K) (by
    rw [Nat.card_zpowers a]
    exact hK)

/-- From a finite normal nilpotent subgroup `N ◁ A` of odd order with
nontrivial field projection, extract the odd prime `p`, the order-`p`
field automorphism `σ`, and a normal `p`-subgroup `P` of `F(A)` containing
a preimage `a₀` of `σ` of `p`-power order. -/
public theorem secondCase_fitting_fieldProjection_pElement
    {K : Type u} [Field K] [Finite K]
    (A : Subgroup (PGammaL2 K))
    (N : Subgroup A) [N.Normal]
    (hNodd : Odd (Nat.card N)) (hNnil : Group.IsNilpotent N)
    (hproj : ∃ n : N, SemidirectProduct.rightHom (n : PGammaL2 K) ≠ 1) :
    ∃ (p : ℕ), p.Prime ∧ Odd p ∧
      ∃ (σ : K ≃+* K), orderOf σ = p ∧
      ∃ (P : Subgroup (PGammaL2 K)),
        P ≤ fittingSubgroupOf A ∧ IsNormalIn P (fittingSubgroupOf A) ∧
        IsPGroup p P ∧
        ∃ a₀ : PGammaL2 K, a₀ ∈ P ∧ SemidirectProduct.rightHom a₀ = σ ∧
          ∃ k : ℕ, a₀ ^ p ^ k = 1 := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let N' : Subgroup (PGammaL2 K) := N.map A.subtype
  let F : Subgroup (PGammaL2 K) := fittingSubgroupOf A
  have hN'nil : Group.IsNilpotent (↥N') := by
    let e : N ≃* N' := Subgroup.equivMapOfInjective N A.subtype A.subtype_injective
    have : Group.IsNilpotent N := hNnil
    exact Group.nilpotent_of_mulEquiv (G := N) (G' := N') e
  have hN'odd : Odd (Nat.card N') := by
    have hcard : Nat.card N' = Nat.card N :=
      (Nat.card_congr (Subgroup.equivMapOfInjective N A.subtype A.subtype_injective).toEquiv).symm
    rwa [hcard]
  let f : ↥N' →* (K ≃+* K) := SemidirectProduct.rightHom.comp N'.subtype
  have hker : ∃ x : ↥N', f x ≠ 1 := by
    rcases hproj with ⟨n, hn⟩
    refine ⟨⟨(n : PGammaL2 K), ?_⟩, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(n : ↥A), n.2, rfl⟩
    · simpa [f] using hn
  obtain ⟨p, hp, hpodd, a, hPa, hordf⟩ := exists_p_element_prime_order_image_of_nontrivial
    (N := ↥N') (C := K ≃+* K) hN'nil hN'odd f hker
  have : Fact p.Prime := ⟨hp⟩
  let a₀ : PGammaL2 K := (a : PGammaL2 K)
  let σ : K ≃+* K := SemidirectProduct.rightHom a₀
  have hσord : orderOf σ = p := by
    simpa [σ, a₀, f] using hordf
  have ha₀N' : a₀ ∈ N' := a.2
  have hN'leF : N' ≤ F := by
    have hNleFit : N ≤ fittingSubgroup (↥A) := by
      change N ≤ sSup {K : Subgroup (↥A) | K.Normal ∧ Group.IsNilpotent K}
      exact le_sSup ⟨inferInstance, hNnil⟩
    simpa [F, N', fittingSubgroupOf] using Subgroup.map_mono (f := A.subtype) hNleFit
  have ha₀F : a₀ ∈ F := hN'leF ha₀N'
  have hFnil : Group.IsNilpotent (↥F) := fittingSubgroupOf_isNilpotent_local A
  have hord_a₀F : ∃ k : ℕ, orderOf (⟨a₀, ha₀F⟩ : ↥F) = p ^ k := by
    have horda : ∃ k : ℕ, orderOf (a : ↥N') = p ^ k := by
      have hsub := (IsPGroup.iff_orderOf (G := Subgroup.zpowers a) (p := p)).mp hPa
        ⟨a, Subgroup.mem_zpowers a⟩
      rcases hsub with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      exact (orderOf_injective (Subgroup.zpowers a).subtype
        (Subgroup.zpowers a).subtype_injective ⟨a, Subgroup.mem_zpowers a⟩).trans hk
    rcases horda with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      orderOf (⟨a₀, ha₀F⟩ : ↥F) = orderOf a₀ :=
        (orderOf_injective F.subtype F.subtype_injective (⟨a₀, ha₀F⟩ : ↥F)).symm
      _ = orderOf a := by
        simpa [a₀] using (orderOf_injective N'.subtype N'.subtype_injective a)
      _ = p ^ k := hk
  have hPa₀ : IsPGroup p (Subgroup.zpowers (⟨a₀, ha₀F⟩ : ↥F)) := by
    rcases hord_a₀F with ⟨k, hk⟩
    exact IsPGroup.of_card (n := k) (by
      rw [Nat.card_zpowers]
      exact hk)
  obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow hPa₀
  let P : Subgroup (PGammaL2 K) := (Q : Subgroup (↥F)).map F.subtype
  have hPleF : P ≤ F := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨q, hq, rfl⟩
    exact q.2
  have hQnorm : (Q : Subgroup (↥F)).Normal := Group.IsNilpotent.sylow_normal hFnil p Q
  have hPnormF : IsNormalIn P F := by
    refine ⟨hPleF, ?_⟩
    intro f hf x hx
    rcases Subgroup.mem_map.mp hx with ⟨q, hq, hxq⟩
    rw [← hxq]
    refine Subgroup.mem_map.mpr ⟨⟨f * (q : PGammaL2 K) * f⁻¹, ?_⟩, ?_, rfl⟩
    · exact F.mul_mem (F.mul_mem hf q.2) (F.inv_mem hf)
    · have hconj := hQnorm.conj_mem q hq ⟨f, hf⟩
      have hFmem : f * (q : PGammaL2 K) * f⁻¹ ∈ F :=
        F.mul_mem (F.mul_mem hf q.2) (F.inv_mem hf)
      have hcq : (⟨f, hf⟩ : ↥F) * q * (⟨f, hf⟩ : ↥F)⁻¹ =
          ⟨f * (q : PGammaL2 K) * f⁻¹, hFmem⟩ := by
        apply Subtype.ext
        simp [mul_assoc]
      rw [← hcq]
      simpa [mul_assoc] using hconj
  have hPp : IsPGroup p P := by
    simpa [P] using (Q.isPGroup'.map F.subtype : IsPGroup p ((Q : Subgroup (↥F)).map F.subtype))
  have ha₀P : a₀ ∈ P := by
    refine Subgroup.mem_map.mpr ⟨⟨a₀, ha₀F⟩, ?_, rfl⟩
    exact hQle (Subgroup.mem_zpowers (⟨a₀, ha₀F⟩ : ↥F))
  have hpow1 : ∃ k : ℕ, a₀ ^ p ^ k = 1 := by
    rcases hord_a₀F with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 : (⟨a₀, ha₀F⟩ : ↥F) ^ (p ^ k) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hk])
    simpa using congrArg (fun z : ↥F => (z : PGammaL2 K)) h1
  refine ⟨p, hp, hpodd, σ, hσord, P, hPleF, hPnormF, hPp, a₀, ha₀P, rfl, hpow1⟩

end CFSG.GorensteinWalter
