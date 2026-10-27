module

import CFSG.Walter.W67.Section4.Lemma42B
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.Section4.Prop43ab
import CFSG.Walter.W67.W1GW
import CFSG.Walter.W67.W2Cor32A
public import CFSG.Walter.JRFacts
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

theorem le_centralizer_of_isKleinFour' {M : Type*} [Group M] [Finite M] {S N : Subgroup M}
    [N.Normal] (hS : IsKleinFour S) (hN : Odd (Nat.card N))
    (hC : ∀ s ∈ S, s ≠ 1 → Subgroup.centralizer ({s} : Set M) ≤
      Subgroup.centralizer (S : Set M)) :
    S ≤ Subgroup.centralizer (N : Set M) := by
  have hSab : ∀ a b : S, a * b = b * a := mul_comm_of_exponent_two hS.exponent_two
  have : CFSG.IsElementaryAbelian 2 S :=
    { toIsMulCommutative := ⟨⟨hSab⟩⟩
      exponent_dvd_p := by rw [hS.exponent_two] }
  let : MulDistribMulAction S N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp S.subtype)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := S) (H := N)
    (by rw [hS.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h))
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hle : ⨆ (a : S) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) N ≤
      (Subgroup.centralizer ({s} : Set M)).comap N.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hya : (y : M) * a = a * y := by
      have h := congrArg Subtype.val hy
      change ((MulAut.conjNormal (a : M)) y : M) = y at h
      rw [MulAut.conjNormal_apply] at h
      calc (y : M) * a = (a * y * (a : M)⁻¹) * a := by rw [h]
        _ = a * y := by group
    have ha1 : (a : M) ≠ 1 := fun h => ha (Subtype.ext h)
    have hyC : (y : M) ∈ Subgroup.centralizer ({(a : M)} : Set M) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hya
    have h1 := Subgroup.mem_centralizer_iff.mp (hC a a.2 ha1 hyC) s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm
  have hmem := hle (hgen.symm ▸ Subgroup.mem_top (⟨x, hx⟩ : N))
  exact (Subgroup.mem_centralizer_singleton_iff.mp hmem)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_conj_iff {Y : Subgroup G} {c x : G} :
    x ∈ Y.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨c⁻¹ * x * c, h, by simp [mul_assoc]⟩

theorem factorization_two_of_le {V Y X : Subgroup G} (hVY : V ≤ Y) (hYX : Y ≤ X)
    (hV : Nat.card V = 4) (hX : (Nat.card X).factorization 2 = 2) :
    (Nat.card Y).factorization 2 = 2 := by
  apply le_antisymm
  · have h1 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hYX) 2
    rw [hX] at h1
    exact h1
  · have h4 : 2 ^ 2 ∣ Nat.card Y := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV]
      exact Subgroup.card_dvd_of_le hVY
    exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h4

namespace Std

variable (s : Std G) {T₂ : G}

theorem le_centralizer_of_le_H
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {X : Subgroup G} (hXH : X ≤ s.H) (hJX : s.J ∈ X) (hT₂X : T₂ ∈ X)
    (hX2 : (Nat.card X).factorization 2 = 2) {B : Subgroup G} (hBX : B ≤ X)
    (hBA : B ≤ s.fr.A T₂) (hB : B ≠ ⊥) : X ≤ Subgroup.centralizer ({T₂} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : s.fr.E ≤ Subgroup.normalizer (s.K : Set G) := s.fr.E_le_H.trans s.H_le_normalizer
  have hKEH : s.K ⊔ s.fr.E ≤ s.H := sup_le s.K_le_H s.fr.E_le_H
  have hJKE : Subgroup.zpowers s.J ⊓ (s.K ⊔ s.fr.E) = ⊥ :=
    disjoint_iff.mp s.fr.isInternalDirectProduct_H.2.1
  set X₀ := X ⊓ (s.K ⊔ s.fr.E) with hX₀
  have hJc : ∀ x ∈ Subgroup.zpowers s.J, ∀ y ∈ X₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (Commute.symm (s.commute_J (hXH hy.1))) m).eq
  have hXdec : X = Subgroup.zpowers s.J ⊔ X₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨j, hj, k, hk, e, he, rfl⟩ := s.fr.exists_decomp_H (hXH hx)
      have hjX : j ∈ X := (Subgroup.zpowers_le.mpr hJX) hj
      have hke : k * e ∈ X₀ := by
        refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right he)⟩
        have := X.mul_mem (X.inv_mem hjX) hx
        rwa [show j⁻¹ * (j * k * e) = k * e by group] at this
      rw [mul_assoc]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hke)
    · exact sup_le (Subgroup.zpowers_le.mpr hJX) inf_le_left
  obtain ⟨hc, -⟩ := card_sup_mul_card_inf_of_commute _ _ hJc
  have hinf : Subgroup.zpowers s.J ⊓ X₀ = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans hJKE.le)
  rw [← hXdec, hinf, Subgroup.card_bot, mul_one, s.card_zpowers_J] at hc
  have hX₀2 : (Nat.card X₀).factorization 2 = 1 := by
    rw [hc, Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two] at hX2
    omega
  have hT₂X₀ : T₂ ∈ X₀ := ⟨hT₂X, Subgroup.mem_sup_left hT₂.2⟩
  set t₀ : X₀ := ⟨T₂, hT₂X₀⟩ with ht₀def
  have ht₀ : orderOf t₀ = 2 := by rw [ht₀def, Subgroup.orderOf_mk]; exact h2
  have hP₀card : Nat.card (Subgroup.zpowers t₀) = 2 ^ (Nat.card X₀).factorization 2 := by
    rw [Nat.card_zpowers, ht₀, hX₀2, pow_one]
  set P : Sylow 2 X₀ := Sylow.ofCard (Subgroup.zpowers t₀) hP₀card
  have hPc : (P : Subgroup X₀) = Subgroup.zpowers t₀ := Sylow.coe_ofCard _ _
  have hNC : Subgroup.normalizer ((P : Subgroup X₀) : Set X₀) ≤
      Subgroup.centralizer ((P : Subgroup X₀) : Set X₀) := by
    intro n hn
    rw [hPc] at hn ⊢
    have h1 : n * t₀ * n⁻¹ ∈ Subgroup.zpowers t₀ :=
      (Subgroup.mem_normalizer_iff.mp hn t₀).mp (Subgroup.mem_zpowers t₀)
    have hcomm : Commute t₀ n := by
      rcases eq_one_or_eq_of_mem_zpowers ht₀ h1 with h | h
      · exfalso
        have : t₀ = 1 := by
          have := congrArg (fun z => n⁻¹ * z * n) h
          simpa [mul_assoc] using this
        rw [this, orderOf_one] at ht₀
        exact absurd ht₀ (by norm_num)
      · exact (show t₀ * n = n * t₀ by
          calc t₀ * n = (n * t₀ * n⁻¹) * n := by rw [h]
            _ = n * t₀ := by group)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left hcomm k).eq
  set Dk := (MonoidHom.transferSylow P hNC).ker with hDk
  have hcomp : Subgroup.IsComplement' Dk P := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hDkcard : Nat.card Dk * 2 = Nat.card X₀ := by
    rw [← hcomp.card_mul_card, hPc, Nat.card_zpowers, ht₀]
  have hDkidx : Dk.index = 2 := by
    have h1 := Dk.card_mul_index
    rw [← hDkcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hDkodd : Odd (Nat.card Dk) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    have h4 : 2 ^ 2 ∣ Nat.card X₀ := ⟨m, by rw [← hDkcard, hm]; ring⟩
    have := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h4
    omega
  set D := Dk.map X₀.subtype with hD
  have hDodd : Odd (Nat.card D) := by
    rw [Subgroup.card_map_of_injective X₀.subtype_injective]
    exact hDkodd
  have hDX₀ : D ≤ X₀ := Subgroup.map_subtype_le _
  have hoddD : ∀ x ∈ X₀, Odd (orderOf x) → x ∈ D := fun x hx hodd =>
    ⟨⟨x, hx⟩, mem_of_index_two_of_odd hDkidx (by rw [Subgroup.orderOf_mk]; exact hodd), rfl⟩
  have hBK : B ≤ s.K := fun b hb => (s.fr.A_le T₂ (hBA hb)).1
  have hBD : B ≤ D := fun b hb => hoddD b ⟨hBX hb, Subgroup.mem_sup_left (hBK hb)⟩
    (odd_orderOf_of_mem_oddPart (hBA hb))
  set D₁ := D ⊓ s.K with hD₁
  have hD₁A : D₁ ≤ s.fr.A T₂ := s.le_A_of_odd hp hT₂ h2 hBA hB (le_inf hBD hBK) inf_le_right
    (Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le inf_le_left))
  have hD₁ne : D₁ ≠ ⊥ := fun h => hB (eq_bot_iff.mpr (h ▸ le_inf hBD hBK))
  obtain ⟨U₀, w, hU, -, -, hAU, hC⟩ := s.exists_torus hp hT₂ h2
  have hcycA := s.isCyclic_A hp hT₂ h2
  have hEA : s.fr.E ≤ Subgroup.normalizer (s.fr.A T₂ : Set G) := fun e he =>
    JT.mem_normalizer_of_conj_mem fun x hx => s.fr.E_conj_mem_A he hx hT₂
  have hAEodd : Odd (Nat.card (s.fr.A T₂ ⊔ s.fr.E : Subgroup G)) := by
    have hc' := card_sup_mul_card_inf_of_le_normalizer hEA
    exact Odd.of_dvd_nat ((s.fr.odd_card_A T₂).mul s.fr.odd_card_E) (Dvd.intro _ hc')
  have hTN : s.fr.T ≤ Subgroup.normalizer ((s.fr.A T₂ ⊔ s.fr.E : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup (JT.mem_normalizer_of_conj_mem fun x hx =>
      s.fr.S_conj_mem_A (s.fr.T_le_S ht) hx hT₂) (JT.mem_normalizer_of_conj_mem fun e he => ?_)
    rw [Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) t (s.fr.T_le_S ht),
      mul_inv_cancel_right]
    exact he
  have hDAE : D ≤ s.fr.A T₂ ⊔ s.fr.E := by
    intro d hd
    have hdKE : d ∈ s.K ⊔ s.fr.E := (hDX₀ hd).2
    have hdN : d ∈ Subgroup.normalizer (D₁ : Set G) :=
      normalizer_inf_normalizer_le D s.K ⟨Subgroup.le_normalizer hd,
        s.H_le_normalizer (hKEH hdKE)⟩
    obtain ⟨k, hk, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hdKE
    have heN : e ∈ Subgroup.normalizer (D₁ : Set G) :=
      mem_normalizer_of_le_cyclic hcycA hD₁A (hEA he)
    have hkN : k ∈ s.K ⊓ Subgroup.normalizer (D₁ : Set G) := by
      refine ⟨hk, ?_⟩
      have := Subgroup.mul_mem _ hdN (Subgroup.inv_mem _ heN)
      rwa [mul_inv_cancel_right] at this
    rw [hU.normalizer D₁ (hD₁A.trans hAU) hD₁ne, ← hC, s.fr.K_inf_centralizer_eq hT₂ h2] at hkN
    have hmem : k * e ∈ (s.fr.A T₂ ⊔ s.fr.E) ⊔ s.fr.T := by
      have hk' : k ∈ (s.fr.A T₂ ⊔ s.fr.E) ⊔ s.fr.T :=
        (sup_le le_sup_right (le_sup_left.trans le_sup_left) :
          s.fr.T ⊔ s.fr.A T₂ ≤ (s.fr.A T₂ ⊔ s.fr.E) ⊔ s.fr.T) hkN
      exact Subgroup.mul_mem _ hk' (Subgroup.mem_sup_left (Subgroup.mem_sup_right he))
    exact mem_of_odd_of_mem_sup s.fr.isPGroup_T hAEodd hTN hmem
      (Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd))
  have hAEC : s.fr.A T₂ ⊔ s.fr.E ≤ Subgroup.centralizer ({T₂} : Set G) := by
    refine sup_le (fun x hx => (s.fr.A_le T₂ hx).2) (fun e he => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) T₂ (s.fr.T_le_S hT₂)).symm
  have hX₀C : X₀ ≤ Subgroup.centralizer ({T₂} : Set G) := by
    intro x hx
    have hsup : Dk ⊔ (P : Subgroup X₀) = ⊤ := hcomp.sup_eq_top
    have hx' : x ∈ (Dk ⊔ (P : Subgroup X₀)).map X₀.subtype :=
      ⟨⟨x, hx⟩, hsup ▸ Subgroup.mem_top _, rfl⟩
    rw [Subgroup.map_sup] at hx'
    refine (sup_le (hDAE.trans hAEC) ?_) hx'
    rw [hPc, MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  rw [hXdec]
  refine sup_le (Subgroup.zpowers_le.mpr ?_) hX₀C
  exact Subgroup.mem_centralizer_singleton_iff.mpr (s.commute_J (s.K_le_H hT₂.2)).symm

end Std

end CFSG.Walter.W67
