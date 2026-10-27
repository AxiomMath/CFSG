module

public import CFSG.Foundations.Basic
public import CFSG.Assembly.Defs
import CFSG.RankThree.Literature.SemiExtraspecialRank
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.RankThree.GroupTheory.SteinbergBKSmallSylowTwoCommutatorOdd
import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG
open scoped commutatorElement IsMulCommutative

theorem special_two_irreducible_odd_action_extraspecial_central_quotients {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {P A : Type*} [Group P] [Finite P] [Group A]
    [MulDistribMulAction A P] (hP2 : IsPGroup 2 P) (hPnab : ∃ x y : P, x * y ≠ y * x)
    (hcomm : commutator P = center P) (hfr : frattini P = center P)
    (hZel : ∀ z ∈ center P, z ^ 2 = 1) (hAcyc : IsCyclic A) (hAcard : Nat.card A = p)
    (hAZ : ∀ a : A, ∀ z ∈ center P, a • z = z)
    (hnontriv : ∃ a : A, ∃ x : P, x⁻¹ * (a • x) ∉ center P)
    (hirr : ∀ W : Subgroup P, center P ≤ W → (∀ a : A, ∀ w ∈ W, a • w ∈ W) →
      W = center P ∨ W = ⊤) :
    ∃ n : ℕ, 2 ≤ n ∧ (center P).index = 2 ^ (2 * n) ∧
      (∀ (Z₀ : Subgroup P) [Z₀.Normal], Z₀ ≤ center P →
        Nat.card (center P) = 2 * Nat.card Z₀ →
        IsExtraspecialPGroup 2 (P ⧸ Z₀) ∧ Nat.card (P ⧸ Z₀) = 2 ^ (1 + 2 * n)) ∧
      ∃ E : Subgroup P, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hc : commutator P ≤ center P := hcomm.le
  have hsmul_comm : ∀ (a : A) (u v : P), a • ⁅u, v⁆ = ⁅a • u, a • v⁆ := by
    intro a u v
    simp only [commutatorElement_def, smul_mul', smul_inv']
  have hcz : ∀ u v : P, ⁅u, v⁆ ∈ center P := fun u v =>
    hc (CFSG.RankThree.Literature.Beisiegel.commutatorElement_mem u v)
  have hgen : ∀ x : P, x ∉ center P → Subgroup.closure (Set.range fun y => ⁅x, y⁆) = center P := by
    intro x hx
    by_contra hne
    have hle : Subgroup.closure (Set.range fun y => ⁅x, y⁆) ≤ center P :=
      (Subgroup.closure_le _).mpr (by rintro _ ⟨y, rfl⟩; exact hcz x y)
    obtain ⟨N, hMN, hNZ, -⟩ :=
      CFSG.RankThree.Literature.Beisiegel.exists_maximal_between (lt_of_le_of_ne hle hne)
    let W : Subgroup P := ⨅ y : P,
      (N.subgroupOf (center P)).comap (CFSG.Monster.B.Short.commHom hc y)
    have hmemW : ∀ w : P, w ∈ W ↔ ∀ y : P, ⁅y, w⁆ ∈ N := by
      intro w
      simp only [W, mem_iInf, mem_comap, mem_subgroupOf, CFSG.Monster.B.Short.commHom_apply]
    have hZW : center P ≤ W := fun z hz => (hmemW z).mpr fun y => by
      rw [commutatorElement_def, mem_center_iff.mp hz y, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem N
    have hxW : x ∈ W := (hmemW x).mpr fun y => by
      rw [← commutatorElement_inv]
      exact inv_mem (hMN (subset_closure ⟨y, rfl⟩))
    have hWinv : ∀ a : A, ∀ w ∈ W, a • w ∈ W := by
      intro a w hw
      refine (hmemW _).mpr fun y => ?_
      have h1 : ⁅y, a • w⁆ = a • ⁅a⁻¹ • y, w⁆ := by rw [hsmul_comm, smul_inv_smul]
      rw [h1, hAZ a _ (hcz _ _)]
      exact (hmemW w).mp hw _
    rcases hirr W hZW hWinv with h | h
    · exact hx (h ▸ hxW)
    · have hcN : commutator P ≤ N := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro g₁ _ g₂ _
        exact (hmemW g₂).mp (h ▸ mem_top g₂) g₁
      exact hNZ.not_ge (hcomm ▸ hcN)
  have hS := CFSG.RankThree.Literature.isSemiExtraspecial_of_special Nat.prime_two hP2 hcomm hfr
    hgen
  have : Nontrivial P := by
    obtain ⟨x, y, hxy⟩ := hPnab
    exact ⟨⟨x * y, y * x, hxy⟩⟩
  obtain ⟨n, m, hn1, hidx, hZcard, hm1, -, -⟩ := hS.rank_data Nat.prime_two hP2
  have hsq : ∀ x : P, x ^ 2 ∈ center P := by
    intro x
    obtain ⟨-, -, hpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP2
    have h := hpow (x : P ⧸ frattini P)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hfr] at h
    exact h
  have hZinv : ∀ a : A, ∀ z ∈ center P, MulDistribMulAction.toMulAut A P a z ∈ center P :=
    fun a z hz => by
      change a • z ∈ center P
      rw [hAZ a z hz]
      exact hz
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    obtain ⟨a, x, hax⟩ := hnontriv
    have : Finite A := Nat.finite_of_card_ne_zero (by rw [hAcard]; exact hp.ne_zero)
    let β := CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
      (MulDistribMulAction.toMulAut A P) (center P) hZinv
    let : MulDistribMulAction A (P ⧸ center P) := MulDistribMulAction.compHom _ β
    have hA : IsPGroup p A := IsPGroup.of_card (n := 1) (by rw [hAcard, pow_one])
    have hV : Nat.card (⊤ : Subgroup (P ⧸ center P)) ≤ p := by
      rw [card_top]
      change (center P).index ≤ p
      rw [hidx, hn]
      omega
    have hfix := CFSG.RankThree.GroupTheory.SteinbergBK.smul_eq_self_of_card_le_prime hp hA
      (⊤ : Subgroup (P ⧸ center P)) (fun _ _ _ => mem_top _) hV a (x : P ⧸ center P) (mem_top _)
    change ((a • x : P) : P ⧸ center P) = (x : P ⧸ center P) at hfix
    apply hax
    have h := QuotientGroup.eq.mp hfix.symm
    exact h
  refine ⟨n, hn2, hidx, fun Z₀ _ hZ₀ hZ₀card => ?_, ?_⟩
  ·
    have hZ₀pos : 0 < Nat.card Z₀ := Nat.card_pos
    have hlt : Z₀ < center P := lt_of_le_of_ne hZ₀ fun h => by
      have h1 : Nat.card Z₀ = Nat.card (center P) := by rw [h]
      omega
    have hmax : ∀ K : Subgroup P, Z₀ < K → K ≤ center P → K = center P := by
      intro K hZK hK
      obtain ⟨c, hc'⟩ := card_dvd_of_le hZK.le
      obtain ⟨d, hd⟩ := card_dvd_of_le hK
      have h3 : Nat.card Z₀ < Nat.card K := card_lt_of_lt hZK
      refine eq_of_le_of_card_ge hK ?_
      rw [hZ₀card, hc'] at hd ⊢
      rw [hc'] at h3
      have hc2 : 2 ≤ c := by
        by_contra h
        interval_cases c <;> simp at h3
      have : c * d = 2 := by
        apply Nat.eq_of_mul_eq_mul_left hZ₀pos
        rw [← mul_assoc, ← hd]
        ring
      have hd1 : d = 1 := by
        rcases Nat.lt_or_ge d 1 with h | h
        · interval_cases d
          simp at this
        · nlinarith
      rw [hd1, mul_one] at this
      rw [this, mul_comm]
    refine ⟨hS Z₀ hlt hmax, ?_⟩
    have e1 := card_mul_index Z₀
    have e2 := card_mul_index (center P)
    rw [hidx, hZ₀card] at e2
    rw [← e1] at e2
    have : (Z₀.index) = 2 ^ (1 + 2 * n) := by
      apply Nat.eq_of_mul_eq_mul_left hZ₀pos
      rw [e2.symm.trans (by ring : 2 * Nat.card Z₀ * 2 ^ (2 * n) = Nat.card Z₀ * (2 * 2 ^ (2 * n))),
        pow_add, pow_one]
    exact this
  ·
    have hZnt : ∃ z ∈ center P, z ≠ 1 := by
      by_contra h
      push Not at h
      have : center P = ⊥ := eq_bot_iff.mpr fun z hz => (mem_bot).mpr (h z hz)
      rw [this, card_bot] at hZcard
      have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
      omega
    by_cases hinv : ∃ t : P, t ∉ center P ∧ t ^ 2 = 1
    · obtain ⟨t, htZ, ht2⟩ := hinv
      obtain ⟨z, hzZ, hz1⟩ := hZnt
      have hz2 : orderOf z = 2 := orderOf_eq_prime (hZel z hzZ) hz1
      have htz : t ∉ zpowers z := fun h => htZ (zpowers_le.mpr hzZ h)
      obtain ⟨hEc, hEcard⟩ := CFSG.RankThree.PartTwo.sup_zpowers_card
        (inferInstance : IsMulCommutative (zpowers z)) htz ht2 fun a ha =>
          (mem_center_iff.mp (zpowers_le.mpr hzZ ha) t).symm
      refine ⟨zpowers z ⊔ zpowers t, ⟨hEc, ?_⟩, by rw [hEcard, Nat.card_zpowers, hz2]⟩
      set E := zpowers z ⊔ zpowers t with hE
      have := hEc
      let ψ : E →* E := powMonoidHom 2
      have hK : E ≤ ψ.ker.map E.subtype := by
        refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
        · refine ⟨⟨z, mem_sup_left (mem_zpowers z)⟩, ?_, rfl⟩
          exact Subtype.ext (hZel z hzZ)
        · refine ⟨⟨t, mem_sup_right (mem_zpowers t)⟩, ?_, rfl⟩
          exact Subtype.ext ht2
      intro e he
      obtain ⟨e', he', rfl⟩ := hK he
      exact congrArg Subtype.val he'
    · push Not at hinv
      by_cases hm : m = 1
      ·
        exfalso
        rw [hm, pow_one] at hZcard
        obtain ⟨x, y, hxy⟩ := hPnab
        have hxZ : x ∉ center P := fun h => hxy (mem_center_iff.mp h y).symm
        have huniq : ∀ u ∈ center P, ∀ v ∈ center P, u ≠ 1 → v ≠ 1 → u = v := by
          intro u hu v hv hu1 hv1
          have hu2 : orderOf u = 2 := orderOf_eq_prime (hZel u hu) hu1
          have hzu : zpowers u = center P := eq_of_le_of_card_ge (zpowers_le.mpr hu)
            (by rw [hZcard, Nat.card_zpowers, hu2])
          have hvu : v ∈ zpowers u := hzu ▸ hv
          rw [mem_zpowers_iff_mem_range_orderOf, hu2] at hvu
          simp only [Finset.mem_image, Finset.mem_range] at hvu
          obtain ⟨k, hk, rfl⟩ := hvu
          interval_cases k
          · exact absurd (pow_zero u) hv1
          · exact (pow_one u).symm
        have hx2 : x ^ 2 ≠ 1 := hinv x hxZ
        have hZx : center P ≤ zpowers x := by
          intro u hu
          by_cases hu1 : u = 1
          · rw [hu1]
            exact one_mem _
          · rw [huniq u hu (x ^ 2) (hsq x) hu1 hx2]
            exact pow_mem (mem_zpowers x) 2
        have hxord : Nat.card (zpowers x) ≤ 4 := by
          rw [Nat.card_zpowers]
          refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
          rw [show 4 = 2 * 2 from rfl, pow_mul]
          exact hZel _ (hsq x)
        obtain ⟨-, -, -, hidxC⟩ := hS.commutator_map Nat.prime_two hP2 hxZ
        have hCcard : 16 ≤ Nat.card (centralizer {x}) := by
          have e1 := card_mul_index (centralizer {x})
          have e2 := card_mul_index (center P)
          rw [hidxC, hZcard] at e1
          rw [hidx, hZcard, ← e1] at e2
          have h4 : 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have : Nat.card (centralizer {x}) = 2 ^ (2 * n) := by omega
          omega
        obtain ⟨y', hy'C, hy'x⟩ : ∃ y' ∈ centralizer {x}, y' ∉ zpowers x := by
          by_contra h
          push Not at h
          have := card_le_of_le (show centralizer {x} ≤ zpowers x from h)
          omega
        have hy'Z : y' ∉ center P := fun h => hy'x (hZx h)
        have hxy'Z : x * y' ∉ center P := fun h => hy'x (by
          have : y' = x⁻¹ * (x * y') := by group
          rw [this]
          exact mul_mem (inv_mem (mem_zpowers x)) (hZx h))
        have hcomm' : x * y' = y' * x := (mem_centralizer_singleton_iff.mp hy'C).symm
        have heq : y' ^ 2 = x ^ 2 := huniq _ (hsq y') _ (hsq x) (hinv y' hy'Z) hx2
        apply hinv _ hxy'Z
        rw [Commute.mul_pow hcomm' 2, heq, ← sq]
        exact hZel _ (hsq x)
      ·
        obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := center P) 2 (n := 2)
          (by rw [hZcard]; exact pow_dvd_pow 2 (by omega))
        refine ⟨E'.map (center P).subtype, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
        · obtain ⟨_, ⟨wa, -, rfl⟩⟩ := a
          obtain ⟨_, ⟨wb, -, rfl⟩⟩ := b
          apply Subtype.ext
          change (wa : P) * wb = wb * wa
          exact mem_center_iff.mp wb.2 wa
        · rintro _ ⟨w, -, rfl⟩
          exact hZel w w.2
        · rw [card_map_of_injective (center P).subtype_injective, hE']
          rfl

end CFSG.RankThree.GroupTheory.SteinbergBK
