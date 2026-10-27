module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporExc
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.HardMathSupport.Dickson.I271 (PlaneKill CentGen)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (OPrimeCoreTrivialAt NoOuterFixesCentralizer)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Spor

variable {K : Type*} [Group K] [Finite K]

theorem mem_range_conj_of_card_outer_le_two (hO : Nat.card (Outer K) ≤ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ε : MulAut K) (hε : ε ^ p = 1) : ε ∈ (MulAut.conj : K →* MulAut K).range :=
  CFSG.HardMathSupport.Dickson.I271.mem_inner_of_pow_eq_one hp hp2 hO hε

theorem eq_bot_of_closure_planeFix_eq_top [IsSimpleGroup K] (hZ : Subgroup.center K = ⊥)
    {Ē R : Subgroup (MulAut K)} (hR2 : IsPGroup 2 R)
    (hfix : ∀ k ∈ planeFix Ē, MulAut.conj k ∈ normalizer (R : Set (MulAut K)))
    (hgen : Subgroup.closure (planeFix Ē) = ⊤) : R = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinn : ∀ k : K, MulAut.conj k ∈ normalizer (R : Set (MulAut K)) := fun k =>
    conj_mem_normalizer_of_mem_closure hfix (hgen ▸ Subgroup.mem_top k)
  set N : Subgroup K := R.comap MulAut.conj
  have hN2 : IsPGroup 2 N := hR2.comap_of_injective _ (conj_injective hZ)
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    change MulAut.conj (g * n * g⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hinn g) _).1 hn
  have hNbot : N = ⊥ := by
    rcases hNn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hK2 : IsPGroup 2 K := by
        intro g
        obtain ⟨n, hn⟩ := hN2 ⟨g, h ▸ Subgroup.mem_top g⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
      haveI : Nontrivial K := IsSimpleGroup.toNontrivial
      have hlt := hK2.bot_lt_center
      rw [hZ] at hlt
      exact lt_irrefl _ hlt
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  ext k
  have hc : k * r k⁻¹ ∈ N := conj_comm_mem (hinn k) hr
  rw [hNbot, Subgroup.mem_bot] at hc
  exact apply_eq_of_mul_apply_inv_eq_one hc

theorem not_sporPlaneConf_of_planeKill [IsSimpleGroup K] (hZ : Subgroup.center K = ⊥) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : PlaneKill p K) {Ē R : Subgroup (MulAut K)} :
    ¬ SporPlaneConf K p Ē R := by
  haveI : Finite (MulAut K) := MulEquiv.finite_left
  rintro ⟨hE, hEc, hR2, hR1, hER, hfix⟩
  apply hR1
  rcases hK Ē hE hEc with ⟨T, hT, hTfix⟩ | hns
  · refine eq_bot_of_closure_planeFix_eq_top hZ hR2 hfix ?_
    rw [eq_top_iff, ← hT]
    exact Subgroup.closure_mono fun σ hσ => (hTfix σ hσ).2
  · exact hns R ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_of_isPGroup_two hp hp2 hR2)) hER

theorem planeGenOrExc_of_centGen (hZ : Subgroup.center K = ⊥) (hO : Nat.card (Outer K) ≤ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : CentGen p K) : PlaneGenOrExc K p := by
  refine planeGenOrExc_of_planeOK hZ (mem_range_conj_of_card_outer_le_two hO hp hp2) fun A hA hAc => ?_
  refine planeOK_of_gens (fun σ hσ => ?_) (hK A hA hAc)
  obtain ⟨e, he, he1, hσe⟩ := hσ
  exact ⟨e, he, he1, hσe.symm⟩

theorem planeOK_of_onePair (hZ : Subgroup.center K = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO' : OPrimeCoreTrivialAt p K) (hN : NoOuterFixesCentralizer p K) {A : Subgroup K}
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) : PlaneOK A := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut K) := MulEquiv.finite_left
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hmemC : ∀ b k : K, k ∈ Subgroup.centralizer ({b} : Set K) ↔ b * k = k * b := fun b k => by
    rw [Subgroup.mem_centralizer_iff]
    simp
  have hCH : ∀ a ∈ A, a ≠ 1 → ∀ k : K, a * k = k * a → k ∈ Subgroup.closure (centSet A) :=
    fun a ha ha1 k hk => Subgroup.subset_closure ⟨a, ha, ha1, hk⟩
  have hcore : ∀ a ∈ A, a ≠ 1 → ∀ S : Subgroup K, IsPGroup 2 S →
      S ≤ Subgroup.centralizer ({a} : Set K) →
      (∀ g ∈ Subgroup.centralizer ({a} : Set K), ∀ x ∈ S, g * x * g⁻¹ ∈ S) → S = ⊥ := by
    intro a ha ha1 S hS2 hSC hSn
    have hle := CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal hSC hSn
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_of_isPGroup_two hp hp2 hS2))
    rw [hO' a (orderOf_eq_prime (hA.2 a ha) ha1)] at hle
    exact eq_bot_iff.2 hle
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    rcases A.bot_or_exists_ne_one with h | h
    · exfalso
      rw [h, Subgroup.card_bot] at hAc
      have h4 : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
      rw [← hAc] at h4
      norm_num at h4
    · exact h
  right
  refine ⟨fun N _ hN2 hHN => ?_, fun α hα => ?_⟩
  ·
    refine eq_bot_of_forall_commute_eq_one hA hAc (not_dvd_card_of_isPGroup_two hp hp2 hN2)
      ((le_closure_centSet hcomm).trans hHN) fun b hb hb1 x hxN hbx => ?_
    have hS : N ⊓ Subgroup.centralizer ({b} : Set K) = ⊥ := by
      refine hcore b hb hb1 _ (hN2.to_le inf_le_left) inf_le_right fun g hg y hy => ?_
      obtain ⟨hyN, hyC⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hHN (hCH b hb hb1 g ((hmemC b g).1 hg))) y).1 hyN
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hyC) (Subgroup.inv_mem _ hg)
    have hx : x ∈ N ⊓ Subgroup.centralizer ({b} : Set K) := Subgroup.mem_inf.2 ⟨hxN, (hmemC b x).2 hbx⟩
    rw [hS] at hx
    exact Subgroup.mem_bot.1 hx
  ·
    by_contra hodd
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hodd
    have hm0 : m ≠ 0 := by
      have := orderOf_pos α
      omega
    have hpowfix : ∀ j : ℕ, ∀ k ∈ Subgroup.closure (centSet A), (α ^ j) k = k := by
      intro j
      induction j with
      | zero => intro k _; simp
      | succ j ih => intro k hk; rw [pow_succ, MulAut.mul_apply, hα k hk, ih k hk]
    have hβord : orderOf (α ^ m) = 2 := by
      rw [orderOf_pow_of_dvd hm0 ⟨2, by omega⟩, hm, show m + m = m * 2 by ring,
        Nat.mul_div_cancel_left 2 (Nat.pos_of_ne_zero hm0)]
    have hβ2 : (α ^ m) ^ 2 = 1 := by
      rw [← hβord]
      exact pow_orderOf_eq_one _
    have hβ1 : α ^ m ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hβord
      omega
    by_cases hin : α ^ m ∈ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut K
    ·
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.1
        (show α ^ m ∈ (MulAut.conj : K →* MulAut K).range from hin)
      have hk1 : k ≠ 1 := by
        rintro rfl
        exact hβ1 (by rw [← hk, map_one])
      have hksq : k ^ 2 = 1 := by
        apply conj_injective hZ
        rw [map_pow, hk, hβ2, map_one]
      have hkcomm : ∀ h ∈ Subgroup.closure (centSet A), k * h = h * k := by
        intro h hh
        have h1 : MulAut.conj k h = h := by
          rw [hk]
          exact hpowfix m h hh
        rw [MulAut.conj_apply] at h1
        calc k * h = k * h * k⁻¹ * k := by group
          _ = h * k := by rw [h1]
      have hkC : k ∈ Subgroup.centralizer ({a} : Set K) :=
        (hmemC a k).2 (hkcomm a (Subgroup.subset_closure ⟨a, ha, ha1, rfl⟩)).symm
      have hkn : ∀ g ∈ Subgroup.centralizer ({a} : Set K), ∀ x ∈ Subgroup.zpowers k,
          g * x * g⁻¹ ∈ Subgroup.zpowers k := by
        intro g hg x hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        have hc : Commute g (k ^ j) :=
          Commute.zpow_right (show Commute g k from (hkcomm g (hCH a ha ha1 g ((hmemC a g).1 hg))).symm) j
        rw [hc.eq, mul_inv_cancel_right]
        exact Subgroup.zpow_mem_zpowers k j
      have hbot : Subgroup.zpowers k = ⊥ :=
        hcore a ha ha1 (Subgroup.zpowers k) (IsPGroup.of_card (n := 1)
          (by rw [Nat.card_zpowers, orderOf_eq_prime hksq hk1, pow_one]))
          (Subgroup.zpowers_le.2 hkC) hkn
      have hkbot : k ∈ (⊥ : Subgroup K) := by
        rw [← hbot]
        exact Subgroup.mem_zpowers k
      exact hk1 (Subgroup.mem_bot.1 hkbot)
    ·
      obtain ⟨t, hat, ht⟩ := hN (α ^ m) hβ2 hin a (orderOf_eq_prime (hA.2 a ha) ha1)
      exact ht (hpowfix m t (hCH a ha ha1 t hat))

theorem planeGenOrExc_of_onePair (hZ : Subgroup.center K = ⊥) (hO : Nat.card (Outer K) ≤ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hO' : OPrimeCoreTrivialAt p K) (hN : NoOuterFixesCentralizer p K) :
    PlaneGenOrExc K p :=
  planeGenOrExc_of_planeOK hZ (mem_range_conj_of_card_outer_le_two hO hp hp2) fun _ hA hAc =>
    planeOK_of_onePair hZ hp hp2 hO' hN hA hAc

end Spor

end CFSG.LocalAnalysis.UniquenessCase.UCK
