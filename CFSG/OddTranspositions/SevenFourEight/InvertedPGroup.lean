module

public import Mathlib.GroupTheory.PGroup
import CFSG.GH74.Uniqueness.Section171Group
import CFSG.GroupTheory.CentralExtensionPGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.OddTranspositions

open Subgroup in
private theorem isPGroup_of_forall_inverted_aux {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → ∀ (O : Subgroup X) [O.Normal],
      Odd (Nat.card O) → ∀ x : X, x * x = 1 → O ⊔ zpowers x = ⊤ →
      closure {y | IsConj x y} = ⊤ →
      (∀ o ∈ O, x * o * x⁻¹ = o⁻¹ → o = 1 ∨ orderOf o = p) → IsPGroup p O := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn O hOn hO x hx2 hOx hgen hinv
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hconj : ∀ c : X, x * (c * x * c⁻¹ * x⁻¹) * x⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by
    intro c
    rw [hxinv]
    calc x * (c * x * c⁻¹ * x) * x = x * c * x * c⁻¹ * (x * x) := by group
      _ = x * c * x * c⁻¹ := by rw [hx2, mul_one]
      _ = x⁻¹ * c * x⁻¹ * c⁻¹ := by rw [hxinv]
      _ = (c * x * c⁻¹ * x)⁻¹ := by group
  have hcomm : ∀ g : X, g * x * g⁻¹ * x⁻¹ ∈ O := by
    intro g
    have hg : g ∈ ((O ⊔ zpowers x : Subgroup X) : Set X) := by
      rw [hOx]
      exact Set.mem_univ g
    rw [normal_mul] at hg
    obtain ⟨o, ho, z, hz, rfl⟩ := Set.mem_mul.mp hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have h : o * x ^ k * x * (o * x ^ k)⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by group
    rw [h]
    exact O.mul_mem ho (hOn.conj_mem _ (O.inv_mem ho) x)
  have hzpow : ∀ z ∈ O, z ∈ zpowers x → z = 1 := by
    intro z hzO hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have h2 : (x ^ k) ^ 2 = 1 := by
      rw [sq, ← (Commute.refl x).mul_zpow, hx2, one_zpow]
    have hne : orderOf (x ^ k) ≠ 2 := hO.ne_two_of_dvd_nat (O.orderOf_dvd_natCard hzO)
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd h hne
  rcases eq_or_ne O ⊥ with hbot | hne
  · exact hbot ▸ IsPGroup.of_bot
  have : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hO
  obtain ⟨N, hNn, hNO, hNbot, hNmin⟩ := CFSG.exists_minimal_normal_le O hOn hne
  have : CFSG.IsMinimalNormal N :=
    ⟨fun K hK hKN => (eq_or_ne K ⊥).imp_right (hNmin K hK hKN)⟩
  have : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNO)
  obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
  have hNr : IsPGroup r N := CFSG.IsElementaryAbelian.isPGroup r N
  obtain ⟨π, hπ, hker⟩ : ∃ π : X →* X ⧸ N, Function.Surjective π ∧ π.ker = N :=
    ⟨_, QuotientGroup.mk'_surjective N, QuotientGroup.ker_mk' N⟩
  have hπx : π x * π x = 1 := by rw [← map_mul, hx2, map_one]
  have hO' : IsPGroup p (O.map π) := by
    have hlt : Nat.card (X ⧸ N) < n := by
      rw [← hn, card_eq_card_quotient_mul_card_subgroup N]
      exact lt_mul_of_one_lt_right Nat.card_pos ((one_lt_card_iff_ne_bot N).mpr hNbot)
    have : (O.map π).Normal := hOn.map π hπ
    refine ih _ hlt (X ⧸ N) rfl (O.map π) (hO.of_dvd_nat (O.card_map_dvd π)) (π x) hπx ?_ ?_ ?_
    · rw [← MonoidHom.map_zpowers π x, ← Subgroup.map_sup, hOx, map_top_of_surjective π hπ]
    · rw [eq_top_iff, ← map_top_of_surjective π hπ, ← hgen, MonoidHom.map_closure]
      apply closure_mono
      rintro _ ⟨y, hy, rfl⟩
      exact π.map_isConj hy
    · rintro _ ⟨o, ho, rfl⟩ hinv'
      have hodd : Odd (orderOf (π o)) :=
        hO.of_dvd_nat ((orderOf_map_dvd π o).trans (O.orderOf_dvd_natCard ho))
      obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.exists_pow_conj_of_inverted hodd hinv' hπx
      have hπc : π (o ^ k * x * (o ^ k)⁻¹ * x⁻¹) = π o := by
        simp only [map_mul, map_inv, map_pow]
        rw [← hk, mul_inv_cancel_right]
      rcases hinv _ (hcomm (o ^ k)) (hconj (o ^ k)) with h1 | h2
      · left
        rw [← hπc, h1, map_one]
      · have hdvd : orderOf (π o) ∣ p := by
          rw [← hπc, ← h2]
          exact orderOf_map_dvd π _
        rcases (Nat.dvd_prime hp).mp hdvd with h | h
        · exact Or.inl (orderOf_eq_one_iff.mp h)
        · exact Or.inr h
  by_cases hrp : r = p
  ·
    have hNp : IsPGroup p π.ker := by
      rw [hker, ← hrp]
      exact hNr
    exact (hO'.comap_of_ker_isPGroup π hNp).to_le (le_comap_map π O)
  have hxN : ∀ m ∈ N, m * x = x * m := by
    intro m hm
    have hcN : m * x * m⁻¹ * x⁻¹ ∈ N := by
      have h : m * x * m⁻¹ * x⁻¹ = m * (x * m⁻¹ * x⁻¹) := by group
      rw [h]
      exact N.mul_mem hm (hNn.conj_mem _ (N.inv_mem hm) x)
    rcases hinv _ (hNO hcN) (hconj m) with h1 | h2
    · calc m * x = m * x * m⁻¹ * x⁻¹ * (x * m) := by group
        _ = x * m := by rw [h1, one_mul]
    · exfalso
      obtain ⟨k, hk⟩ := hNr ⟨_, hcN⟩
      have hk' : (m * x * m⁻¹ * x⁻¹) ^ r ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      have hdvd : p ∣ r ^ k := h2 ▸ orderOf_dvd_of_pow_eq_one hk'
      exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hdvd)).symm
  have hNZ : N ≤ center X := by
    have hC : (⊤ : Subgroup X) ≤ centralizer (N : Set X) := by
      rw [← hgen, closure_le]
      intro y hy
      obtain ⟨c, rfl⟩ := isConj_iff.mp hy
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro m hm
      have hm' : c⁻¹ * m * c ∈ N := by simpa using hNn.conj_mem m hm c⁻¹
      have h := hxN _ hm'
      calc m * (c * x * c⁻¹) = c * ((c⁻¹ * m * c) * x) * c⁻¹ := by group
        _ = c * (x * (c⁻¹ * m * c)) * c⁻¹ := by rw [h]
        _ = c * x * c⁻¹ * m := by group
    intro m hm
    rw [mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (hC (mem_top g)) m hm).symm
  have : Fact p.Prime := ⟨hp⟩
  set S : Set X := {s | s ∈ O ∧ s ^ p = 1}
  set K : Subgroup X := normalClosure S
  have : K.Normal := normalClosure_normal
  have hKO : K ≤ O := normalClosure_le_normal fun s hs => hs.1
  have hOK : O ≤ K := by
    have hD : (⊤ : Subgroup X) ≤ K ⊔ zpowers x := by
      rw [← hgen, closure_le]
      intro y hy
      obtain ⟨c, rfl⟩ := isConj_iff.mp hy
      have hmem : c * x * c⁻¹ * x⁻¹ ∈ K := by
        apply subset_normalClosure
        refine ⟨hcomm c, ?_⟩
        rcases hinv _ (hcomm c) (hconj c) with h1 | h2
        · rw [h1, one_pow]
        · rw [← h2, pow_orderOf_eq_one]
      have h : c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x := by group
      rw [SetLike.mem_coe, h]
      exact mul_mem (mem_sup_left hmem) (mem_sup_right (mem_zpowers x))
    intro o ho
    have hmem : o ∈ ((K ⊔ zpowers x : Subgroup X) : Set X) := hD (mem_top o)
    rw [normal_mul] at hmem
    obtain ⟨k, hk, z, hz, rfl⟩ := Set.mem_mul.mp hmem
    have hzO : z ∈ O := by
      have h : z = k⁻¹ * (k * z) := by group
      rw [h]
      exact O.mul_mem (O.inv_mem (hKO hk)) ho
    rw [hzpow z hzO hz, mul_one]
    exact hk
  have hSp : ∀ s ∈ Group.conjugatesOfSet S, ∃ k : ℕ, s ^ p ^ k = 1 := by
    intro s hs
    obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hs
    obtain ⟨c, rfl⟩ := isConj_iff.mp hac
    exact ⟨1, by rw [pow_one, conj_pow, ha.2, mul_one, mul_inv_cancel]⟩
  have hmapO : IsPGroup p (O.map (QuotientGroup.mk' (center X))) := by
    rintro ⟨_, o, ho, rfl⟩
    obtain ⟨k, hk⟩ := hO' ⟨π o, o, ho, rfl⟩
    have h1 : π (o ^ p ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    have h2 : o ^ p ^ k ∈ center X := hNZ (hker ▸ (MonoidHom.mem_ker.mpr h1))
    refine ⟨k, Subtype.ext ?_⟩
    change QuotientGroup.mk' (center X) o ^ p ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h2
  have hKp : IsPGroup p K :=
    CFSG.GroupTheory.isPGroup_closure_of_map_center hSp (hmapO.to_le (map_mono hKO))
  exact hKp.to_le hOK

theorem isPGroup_of_forall_inverted {X : Type} [Group X] [Finite X] {O : Subgroup X} [O.Normal]
    (hO : Odd (Nat.card O)) {x : X} (hx2 : x * x = 1) (hOx : O ⊔ Subgroup.zpowers x = ⊤)
    (hgen : Subgroup.closure {y | IsConj x y} = ⊤) {p : ℕ} (hp : p.Prime)
    (hinv : ∀ o ∈ O, x * o * x⁻¹ = o⁻¹ → o = 1 ∨ orderOf o = p) :
    IsPGroup p O :=
  isPGroup_of_forall_inverted_aux hp _ X rfl O hO x hx2 hOx hgen hinv

end CFSG.OddTranspositions

end
