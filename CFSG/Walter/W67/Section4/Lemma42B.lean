module

import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Walter.JRFacts
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_odd_of_mem_sup {P O : Subgroup G} (hP : IsPGroup 2 P) (hO : Odd (Nat.card O))
    (hPN : P ≤ Subgroup.normalizer (O : Set G)) {x : G} (hx : x ∈ O ⊔ P)
    (hodd : Odd (orderOf x)) : x ∈ O := by
  obtain ⟨o, ho, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer hPN).mp hx
  have key : ∀ n : ℕ, ∃ o' ∈ O, (o * p) ^ n = o' * p ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, O.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨o', ho', h⟩ := ih
      refine ⟨o' * (p ^ n * o * (p ^ n)⁻¹), O.mul_mem ho'
        ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hPN hp) n) o).mp ho), ?_⟩
      rw [pow_succ, h, pow_succ]
      group
  obtain ⟨o', ho', h⟩ := key (orderOf (o * p))
  rw [pow_orderOf_eq_one] at h
  have hpm : p ^ orderOf (o * p) = o'⁻¹ := eq_inv_of_mul_eq_one_right h.symm
  have hpmO : p ^ orderOf (o * p) ∈ O := hpm ▸ O.inv_mem ho'
  have hpm1 : p ^ orderOf (o * p) = 1 := eq_one_of_odd_of_isPGroup hP (P.pow_mem hp _)
    (Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hpmO))
  have hp1 : p = 1 := eq_one_of_odd_of_isPGroup hP hp
    (Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hpm1))
  rw [hp1, mul_one]
  exact ho

omit [Finite G] in
theorem le_oddPart {Y B : Subgroup G} (hBY : B ≤ Y) (hodd : Odd (Nat.card B))
    (hN : Y ≤ Subgroup.normalizer (B : Set G)) : B ≤ oddPart Y := by
  have hB'n : (B.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hN
  have hB'odd : Nat.Coprime 2 (Nat.card (B.subgroupOf Y)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  have hle : B.subgroupOf Y ≤ CFSG.pPrimeCore 2 Y := le_sSup ⟨hB'n, hB'odd⟩
  intro b hb
  exact ⟨⟨b, hBY hb⟩, hle (show (⟨b, hBY hb⟩ : Y) ∈ B.subgroupOf Y from hb), rfl⟩

namespace Std

variable (s : Std G) {T₂ : G}

theorem q_mod_eight (hp : s.p = 3) : s.q % 8 = 3 := by
  have h8 := s.mod_eight
  rw [Hyp.q, hp] at h8 ⊢
  have : (3 : ℕ) ^ s.f % 8 = 1 ∨ (3 : ℕ) ^ s.f % 8 = 3 := by
    rcases Nat.even_or_odd s.f with ⟨k, hk⟩ | ⟨k, hk⟩
    · left; rw [hk, ← two_mul, pow_mul, Nat.pow_mod]; norm_num
    · right; rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  omega

theorem exists_torus
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    ∃ U₀ : Subgroup G, ∃ w : G, JT.TorusData s.K U₀ w ∧ T₂ ∈ U₀ ∧
      2 * Nat.card U₀ = s.q + 1 ∧ s.fr.A T₂ ≤ U₀ ∧
      s.K ⊓ Subgroup.centralizer ({T₂} : Set G) = U₀ ⊔ Subgroup.zpowers w := by
  have hF := JT.psl2Facts s.K s.iso s.p_ne_two (s.five_lt_q hp)
  obtain ⟨U₀, w, hU, hT₂U, hcard⟩ := hF.even_torus T₂ hT₂.2 h2
  have hC := hU.centralizer_eq hT₂U h2
  have hq4 : s.q % 4 = 3 := by have := s.q_mod_eight hp; omega
  have hcard' : 2 * Nat.card U₀ = s.q + 1 := by
    rcases hcard with ⟨-, h⟩ | ⟨h4, -⟩
    · exact h
    · exfalso
      rw [Hyp.q] at hq4
      omega
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (U₀ : Set G) := by
    rw [Subgroup.zpowers_le]
    exact JT.mem_normalizer_of_conj_mem fun x hx => by rw [hU.inv x hx]; exact U₀.inv_mem hx
  refine ⟨U₀, w, hU, hT₂U, hcard', fun x hx => ?_, hC⟩
  have hxC : x ∈ U₀ ⊔ Subgroup.zpowers w := hC ▸ (oddPart_le _ hx)
  obtain ⟨u, hu, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer hwN).mp hxC
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hU.w_mul_self)
    (fun h1 => hU.w_not_mem (h1 ▸ U₀.one_mem))
  rcases eq_one_or_eq_of_mem_zpowers hw2 hy with hy1 | hy1
  · rwa [hy1, mul_one]
  · rw [hy1] at hx
    exfalso
    have hsq : (u * w) * (u * w) = 1 := by
      calc (u * w) * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
        _ = 1 := by rw [hU.inv u hu, hU.w_mul_self]; group
    have h1 : u * w = 1 := by
      have hodd := odd_orderOf_of_mem_oddPart hx
      have hdvd : orderOf (u * w) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have := Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hodd) (dvd_refl _) hdvd
      exact orderOf_eq_one_iff.mp this
    apply hU.w_not_mem
    rw [eq_inv_of_mul_eq_one_right h1]
    exact U₀.inv_mem hu

theorem A_ne_bot
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    s.fr.A T₂ ≠ ⊥ := by
  obtain ⟨U₀, w, hU, hT₂U, hcard, -, hC⟩ := s.exists_torus hp hT₂ h2
  have hq8 := s.q_mod_eight hp
  have hq27 : 27 ≤ s.q := by
    have h5 := s.five_lt_q hp
    have hq : s.q = 3 ^ s.f := by rw [Hyp.q, hp]
    rcases Nat.lt_or_ge s.f 3 with hf | hf
    · interval_cases hf' : s.f
      · exact absurd s.f_pos (by omega)
      · rw [hq] at h5; norm_num at h5
      · rw [hq] at hq8; norm_num at hq8
    · rw [hq]
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ s.f := Nat.pow_le_pow_right (by norm_num) hf
  have hcyc := hU.cyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := U₀)
  have hgo : orderOf (g : G) = Nat.card U₀ := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have h2U : 2 ∣ orderOf (g : G) := by rw [hgo]; omega
  set u := (g : G) ^ 2 with hu
  have huo : orderOf u = Nat.card U₀ / 2 := by
    rw [hu, orderOf_pow_of_dvd two_ne_zero h2U, hgo]
  have huU : u ∈ U₀ := U₀.pow_mem g.2 2
  have hUodd : Odd (Nat.card U₀ / 2) := by
    refine Nat.odd_iff.mpr ?_
    omega
  have huodd : Odd (Nat.card (Subgroup.zpowers u)) := by
    rw [Nat.card_zpowers, huo]
    exact hUodd
  have hUC : U₀ ≤ s.K ⊓ Subgroup.centralizer ({T₂} : Set G) := by
    rw [hC]
    exact le_sup_left
  have hle : Subgroup.zpowers u ≤ s.fr.A T₂ := by
    refine le_oddPart (Subgroup.zpowers_le.mpr (hUC huU)) huodd ?_
    rw [hC]
    refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
    · refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
      have hab : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val ((IsCyclic.isMulCommutative (α := U₀)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      have hxU : x ∈ U₀ := (Subgroup.zpowers_le.mpr huU) hx
      rw [hab y hy x hxU, mul_inv_cancel_right]
      exact hx
    · refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
      have hxU : x ∈ U₀ := (Subgroup.zpowers_le.mpr huU) hx
      rw [hU.inv x hxU]
      exact Subgroup.inv_mem _ hx
  intro hbot
  have h1 : Nat.card (Subgroup.zpowers u) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff, ← hbot]
    exact hle
  rw [Nat.card_zpowers, huo] at h1
  omega

theorem isCyclic_of_odd_of_le_K
    {D : Subgroup G} (hDK : D ≤ s.K) (hD : Odd (Nat.card D))
    {b : ℕ} (hb1 : 1 < b) (hbD : b ∣ Nat.card D) (hbp : Nat.Coprime b s.p)
    (hbq : Nat.Coprime b (s.q - 1)) : IsCyclic D := by
  classical
  set H' : Subgroup PSL(2, GaloisField s.p s.f) := (D.subgroupOf s.K).map s.iso.toMonoidHom
  have hH'card : Nat.card H' = Nat.card D := by
    rw [Subgroup.card_map_of_injective s.iso.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]
  let eH : D ≃* H' := (Subgroup.subgroupOfEquivOfLe hDK).symm.trans
    ((D.subgroupOf s.K).equivMapOfInjective _ s.iso.injective)
  have hFcard : Nat.card (GaloisField s.p s.f) = s.p ^ s.f := GaloisField.card _ _ s.f_pos.ne'
  have heven : ∀ n : ℕ, Nat.card H' = 2 * n → False := fun n h => by
    rw [hH'card] at h
    rw [h] at hD
    exact (Nat.not_even_iff_odd.mpr hD) (even_two_mul n)
  have hbH : b ∣ Nat.card H' := hH'card ▸ hbD
  have hp : (s.p).Prime := Fact.out
  have hGF : ∀ m : ℕ, m ≠ 0 → IsOddPrimePower (Nat.card (GaloisField s.p m)) := fun m hm =>
    ⟨s.p, m, hp, s.odd_p, Nat.pos_of_ne_zero hm, GaloisField.card _ m hm⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFcard
      H' with
    helem | ⟨z, -, -, hcyc⟩ | ⟨z, -, hcard2, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, ht, N, C, hNn, -, hNcard, -, hCcard, hdisj, hsup⟩ | ⟨m, hm, -, ⟨e⟩⟩ |
      ⟨m, hm, -, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup s.p H').exists_card_eq
    rw [hk] at hbH
    exact hb1.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hbp) hbH)
  · exact isCyclic_of_surjective eH.symm.toMonoidHom eH.symm.surjective
  · exact (heven z hcard2).elim
  · refine (heven 6 ?_).elim
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · refine (heven 12 ?_).elim
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · refine (heven 30 ?_).elim
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  ·
    exfalso
    have hNC : N.IsComplement' C := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hcardH : Nat.card N * Nat.card C = Nat.card H' := hNC.card_mul_card
    rw [hNcard, hCcard] at hcardH
    rw [← hcardH] at hbH
    have hbt : b ∣ t := (Nat.Coprime.pow_right m hbp).dvd_of_dvd_mul_left hbH
    have htq : t ∣ s.q - 1 := ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    exact hb1.ne' (Nat.Coprime.eq_one_of_dvd hbq (hbt.trans htq))
  · refine (heven (Nat.card PSL(2, GaloisField s.p m) / 2) ?_).elim
    rw [Nat.card_congr e.toEquiv]
    exact (Nat.mul_div_cancel' (Suzuki.two_dvd_card_psl2 _ (hGF m hm))).symm
  · refine (heven (Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField s.p m)) / 2) ?_).elim
    rw [Nat.card_congr e.toEquiv]
    refine (Nat.mul_div_cancel' ?_).symm
    have hinj := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2)
      (R := GaloisField s.p m)
    exact (Suzuki.two_dvd_card_psl2 _ (hGF m (by omega))).trans
      (Subgroup.card_dvd_of_injective _ hinj)

theorem le_A_of_odd
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) {B D : Subgroup G}
    (hBA : B ≤ s.fr.A T₂) (hB : B ≠ ⊥) (hBD : B ≤ D) (hDK : D ≤ s.K) (hD : Odd (Nat.card D)) :
    D ≤ s.fr.A T₂ := by
  obtain ⟨U₀, w, hU, hT₂U, hcard, hAU, hC⟩ := s.exists_torus hp hT₂ h2
  have hBU : Nat.card B ∣ Nat.card U₀ := Subgroup.card_dvd_of_le (hBA.trans hAU)
  have hBq : Nat.card B ∣ s.q + 1 := hBU.trans (Dvd.intro_left _ hcard)
  have hBodd : Odd (Nat.card B) := Odd.of_dvd_nat (s.fr.odd_card_A T₂)
    (Subgroup.card_dvd_of_le hBA)
  have hB1 : 1 < Nat.card B := (Subgroup.one_lt_card_iff_ne_bot B).mpr hB
  have hp' : (s.p).Prime := Fact.out
  have hqp : s.p ∣ s.q := by rw [Hyp.q]; exact dvd_pow_self _ s.f_pos.ne'
  have hbp : Nat.Coprime (Nat.card B) s.p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp']
    intro h
    have h1 : s.p ∣ 1 := (Nat.dvd_add_right hqp).mp (h.trans hBq)
    exact hp'.one_lt.ne' (Nat.dvd_one.mp h1)
  have hbq : Nat.Coprime (Nat.card B) (s.q - 1) := by
    have hq1 : 1 ≤ s.q := by have := s.five_lt_q hp; omega
    set d := Nat.gcd (Nat.card B) (s.q - 1)
    have hd2 : d ∣ 2 := by
      have h1 : d ∣ s.q + 1 := (Nat.gcd_dvd_left _ _).trans hBq
      have h2' : d ∣ s.q - 1 := Nat.gcd_dvd_right _ _
      have := Nat.dvd_sub h1 h2'
      rwa [show s.q + 1 - (s.q - 1) = 2 by omega] at this
    have hdodd : Odd d := Odd.of_dvd_nat hBodd (Nat.gcd_dvd_left _ _)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact h
    · rw [h] at hdodd; exact absurd hdodd (by decide)
  have hcyc : IsCyclic D := s.isCyclic_of_odd_of_le_K hDK hD hB1 (Subgroup.card_dvd_of_le hBD)
    hbp hbq
  have hDN : D ≤ s.K ⊓ Subgroup.normalizer (B : Set G) := by
    intro d hd
    refine ⟨hDK hd, Subgroup.centralizer_le_normalizer _ ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := D)).is_comm.comm ⟨b, hBD hb⟩ ⟨d, hd⟩)
  rw [hU.normalizer B (hBA.trans hAU) hB, ← hC, s.fr.K_inf_centralizer_eq hT₂ h2] at hDN
  intro d hd
  have hTN : s.fr.T ≤ Subgroup.normalizer (s.fr.A T₂ : Set G) := fun t ht =>
    JT.mem_normalizer_of_conj_mem fun x hx => s.fr.S_conj_mem_A (s.fr.T_le_S ht) hx hT₂
  refine mem_of_odd_of_mem_sup s.fr.isPGroup_T (s.fr.odd_card_A T₂) hTN ?_
    (Odd.of_dvd_nat hD (Subgroup.orderOf_dvd_natCard D hd))
  rw [sup_comm]
  exact hDN hd

end Std

end CFSG.Walter.W67
