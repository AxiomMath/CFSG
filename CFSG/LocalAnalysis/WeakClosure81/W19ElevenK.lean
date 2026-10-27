module

public import CFSG.LocalAnalysis.WeakClosure81.W19SixFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def pairSub (A : Subgroup G) (k : G) : Subgroup G := A ⊔ conjSubgroup A k

theorem le_pairSub_left (A : Subgroup G) (k : G) : A ≤ pairSub A k := le_sup_left

theorem le_pairSub_right (A : Subgroup G) (k : G) : conjSubgroup A k ≤ pairSub A k := le_sup_right

theorem pairSub_le {A K : Subgroup G} (hA : A ≤ K) {k : G} (hk : k ∈ K) : pairSub A k ≤ K := by
  refine sup_le hA fun x hx => ?_
  rw [mem_conjSubgroup_iff] at hx
  have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
  rw [e]
  exact K.mul_mem (K.mul_mem (K.inv_mem hk) (hA hx)) hk

namespace Hyp193

variable {D : Data G} {V₀ : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem exists_orderOf_of_not_isPGroup (h : Hyp193 D V₀ p X) {L : Subgroup G}
    (hLH : L ≤ X ⊔ D.T) (hL : ¬ IsPGroup 2 L) : ∃ x ∈ L, orderOf x = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 h.isPGroup
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 D.sylowM.isPGroup
  have hdvd : Nat.card ↥L ∣ 2 ^ b * p ^ a := by
    have h1 := Subgroup.card_dvd_of_le hLH
    rwa [h.card_sup, ha, hb, mul_comm] at h1
  by_cases hp : p ∣ Nat.card ↥L
  · obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) p hp
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  · exfalso
    apply hL
    have hcop : Nat.Coprime (Nat.card ↥L) (p ^ a) :=
      Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd h.prime).2 hp).symm
    have h2 : Nat.card ↥L ∣ 2 ^ b := hcop.dvd_of_dvd_mul_right hdvd
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact IsPGroup.of_card hn

end Hyp193

namespace Conf196

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G} {g : G} {K : Subgroup G}

theorem pairSub_le_K (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) {k : G} (hk : k ∈ K) :
    pairSub (conjSubgroup V g) k ≤ K :=
  pairSub_le (hc.A_le_K c) hk

theorem exists_k (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    ∃ k ∈ K, ¬ IsPGroup 2 ↥(pairSub (conjSubgroup V g) k) := by
  by_contra hcon
  have hall : ∀ k ∈ K, IsPGroup 2 ↥(pairSub (conjSubgroup V g) k) := fun k hk => by
    by_contra h
    exact hcon ⟨k, hk, h⟩
  obtain ⟨p', hp', hp'2, R, hRK, hKR, hOR, hRp, -, hRne, hcomm, -⟩ := hc.eOneAmb c
  have hcommle : ⁅R, conjSubgroup V g⁆ ≤ pCoreOf 2 K := by
    refine Subgroup.commutator_le.2 fun r hr a ha => ?_
    have hrK : r⁻¹ ∈ K := K.inv_mem (hRK hr)
    have hP := hall r⁻¹ hrK
    have h1 : r * a * r⁻¹ ∈ conjSubgroup (conjSubgroup V g) r⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have e : r⁻¹ * (r * a * r⁻¹) * r⁻¹⁻¹ = a := by group
      rw [e]
      exact ha
    have h2 : ⁅r, a⁆ ∈ pairSub (conjSubgroup V g) r⁻¹ := by
      have e : ⁅r, a⁆ = (r * a * r⁻¹) * a⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact Subgroup.mul_mem _ (le_pairSub_right _ _ h1)
        (Subgroup.inv_mem _ (le_pairSub_left _ _ ha))
    obtain ⟨j, hj⟩ := hP ⟨_, h2⟩
    have hj' : ⁅r, a⁆ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hRmem : ⁅r, a⁆ ∈ R := by
      have e : ⁅r, a⁆ = r * (a * r⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      refine R.mul_mem hr ?_
      have := (Subgroup.mem_normalizer_iff.1 (hKR (hc.A_le_K c ha)) r⁻¹).1 (R.inv_mem hr)
      simpa using this
    obtain ⟨k, hk⟩ := hRp _ hRmem
    exact E1.mem_of_pow_mem_two_p hp' hp'2 hk (by rw [hj']; exact Subgroup.one_mem _)
  exact hRne (le_antisymm (fun x hx => sup_le hcommle le_rfl (hcomm hx)) hOR)

theorem inf_J193_eq_inf_K (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    (hc : Conf196 D V X g K) : X ⊓ J193 D X (conjSubgroup V g) K = X ⊓ K := by
  have hle : X ⊓ K ≤ X ⊓ J193 D X (conjSubgroup V g) K := inf_le_inf_left X hc.K_le_J193
  have hcard := c.card_inf_J193 h162 h763 hc
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  have hpK : p ≤ Nat.card ↥(X ⊓ K) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (c.hyp.isPGroup.to_le (inf_le_left : X ⊓ K ≤ X))
    rw [hn]
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact c.inf_K_ne_bot hc (Subgroup.card_eq_one.1 (by simpa using hn))
    exact Nat.le_self_pow hn0 p
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hpK)).symm

theorem card_inf_K (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    (hc : Conf196 D V X g K) : Nat.card ↥(X ⊓ K) = p := by
  rw [← hc.inf_J193_eq_inf_K c h162 h763]
  exact c.card_inf_J193 h162 h763 hc

theorem mem_sup_pCoreOf_of_mem_K (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) {x : G}
    (hxK : x ∈ K) (hx : x ^ p = 1) :
    x ∈ (X ⊓ J193 D X (conjSubgroup V g) K) ⊔ pCoreOf 2 (X ⊔ D.T) := by
  set Q := pCoreOf 2 (X ⊔ D.T) with hQ
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  have hXQ : X ≤ normalizer (Q : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hPp : IsPGroup p (Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one (show x ^ p ^ 1 = 1 by rw [pow_one]; exact hx))
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hPH : Subgroup.zpowers x ≤ X ⊔ D.T := Subgroup.zpowers_le.2 (hc.le_H hxK)
  obtain ⟨y, hyH, hxy⟩ := c.hyp.exists_conj_le hPH hPp
  have hyx : y * x * y⁻¹ ∈ X := mem_conjSubgroup_iff.1 (hxy (Subgroup.mem_zpowers x))
  have hxN : x ∈ X ⊔ Q := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (c.le_normalizer_sup_pCoreOf (Subgroup.inv_mem _ hyH))
      (y * x * y⁻¹)).1 (Subgroup.mem_sup_left hyx)
    have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
    rwa [e] at h1
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X Q hXQ] at hxN
  obtain ⟨a, ha, q, hq, rfl⟩ := hxN
  have hqJ : q ∈ J193 D X (conjSubgroup V g) K := hc.pCoreOf_le_J193 c hq
  have haJ : a ∈ J193 D X (conjSubgroup V g) K := by
    have := Subgroup.mul_mem _ (hc.K_le_J193 hxK) (Subgroup.inv_mem _ hqJ)
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha, haJ⟩) (Subgroup.mem_sup_right hq)

theorem mem_inf_K_sup_pCoreOf (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    (hc : Conf196 D V X g K) {x : G} (hxK : x ∈ K) (hx : orderOf x = p) :
    x ∈ (X ⊓ K) ⊔ pCoreOf 2 (X ⊔ D.T) := by
  have h := hc.mem_sup_pCoreOf_of_mem_K c hxK (by rw [← hx]; exact pow_orderOf_eq_one x)
  rwa [hc.inf_J193_eq_inf_K c h162 h763] at h

end Conf196

end CFSG.LocalAnalysis.WeakClosure81

end
