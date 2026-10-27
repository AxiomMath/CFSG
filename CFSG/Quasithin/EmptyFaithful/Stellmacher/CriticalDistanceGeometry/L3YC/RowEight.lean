module

public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Quasithin.Background.A4Defs
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Stellmacher.CD.L3YC

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

section Eight

variable {Hb : Type} [Group Hb] [Finite Hb]

theorem card_psl_two_seven {X : Type} [Group X] (h : IsPSL 2 7 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven h

theorem card_psl_two_forty_nine {X : Type} [Group X] (h : IsPSL 2 7 2 X) : Nat.card X = 58800 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_forty_nine h

theorem card_centralizer_involution_psl49 {X : Type} [Group X] (h : IsPSL 2 7 2 X) (t : X)
    (ht : orderOf t = 2) : Nat.card (Subgroup.centralizer ({t} : Set X)) = 48 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let e2 : X ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have ht2 : orderOf (e2 t) = 2 := (MulEquiv.orderOf_eq e2 t).trans ht
  have hW := (CFSG.Walter.psl2_centralizer_involution K hK (p := 7) (f := 2) (by decide)
    (by norm_num) ht2).1 (by norm_num)
  have hcard : Nat.card (Subgroup.centralizer ({t} : Set X)) =
      Nat.card (Subgroup.centralizer ({e2 t} : Set PSL(2, K))) := by
    refine Nat.card_congr ?_
    exact (e2.subgroupMap (Subgroup.centralizer ({t} : Set X))).toEquiv.trans
      (MulEquiv.subgroupCongr (by
        ext y
        simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
          MulEquiv.coe_toMonoidHom]
        constructor
        · rintro ⟨z, hz, rfl⟩
          have := congrArg e2 hz
          simpa using this
        · intro hy
          refine ⟨e2.symm y, ?_, by simp⟩
          have := congrArg e2.symm hy
          simpa using this)).toEquiv
  rw [hcard, hW.1]
  norm_num

theorem card_sylow_of_card {N X : Subgroup Hb} (hX : IsSylowTwoOf X N) {m : ℕ} (hm : Odd m)
    (hN : Nat.card ↥N = 16 * m) : Nat.card ↥X = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hX.2.1
  have hidx : ¬ 2 ∣ (X.subgroupOf N).index := hX.2.2
  have h1 : Nat.card ↥(X.subgroupOf N) * (X.subgroupOf N).index = Nat.card ↥N :=
    Subgroup.card_mul_index _
  have hXc : Nat.card ↥(X.subgroupOf N) = 2 ^ a := by
    rw [← ha]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX.1).toEquiv
  rw [hXc, hN] at h1
  rw [ha]
  have hodd : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)
  rcases Nat.lt_or_ge a 4 with hlt | hge
  · exfalso
    interval_cases a <;> omega
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · rw [← heq]; norm_num
    · exfalso
      have h5 : 2 ^ 5 ∣ 2 ^ a := pow_dvd_pow 2 hgt
      have h6 : 2 ^ 5 ∣ 16 * m := h1 ▸ Dvd.dvd.mul_right h5 _
      omega

theorem false_psl7_psl49 {S Lb L1b : Subgroup Hb} (hS : IsSylowTwoOf S ⊤) (hN : L1b.Normal)
    (hLL : Lb ≤ L1b) (hL : IsPSL 2 7 1 ↥Lb) (hL1 : IsPSL 2 7 2 ↥L1b)
    (hsplit : ∀ s ∈ S, ∃ p ∈ S ⊓ Lb, ∃ c ∈ S, (∀ x ∈ Lb, c * x * c⁻¹ = x) ∧ s = p * c) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc := card_psl_two_seven hL
  have hL1c := card_psl_two_forty_nine hL1
  have hnorm : (⊤ : Subgroup Hb) ≤ Subgroup.normalizer (L1b : Set Hb) :=
    le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hN).symm
  have hX : IsSylowTwoOf (S ⊓ L1b) L1b := A4.isSylowTwoOf_inf_normal hS le_top hnorm
  have hXc : Nat.card ↥(S ⊓ L1b) = 16 :=
    card_sylow_of_card hX (m := 3675) (by decide) (by rw [hL1c])
  have hPc : Nat.card ↥(S ⊓ Lb) ≤ 8 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hS.2.1.to_inf_left (K := Lb))
    have hdvd : Nat.card ↥(S ⊓ Lb) ∣ Nat.card ↥Lb := Subgroup.card_dvd_of_le inf_le_right
    rw [ha, hLc] at hdvd
    rw [ha]
    have : a ≤ 3 := by
      by_contra hlt
      have h5 : 2 ^ 4 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
      have := h5.trans hdvd
      omega
    calc 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
      _ = 8 := by norm_num
  obtain ⟨x, hx, hxn⟩ : ∃ x ∈ S ⊓ L1b, x ∉ S ⊓ Lb := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun y hy => hcon y hy)
    omega
  obtain ⟨p, hp, c, hc, hcent, rfl⟩ := hsplit x hx.1
  have hcL1 : c ∈ L1b := by
    have h1 : p⁻¹ * (p * c) ∈ L1b := L1b.mul_mem (L1b.inv_mem (hLL hp.2)) hx.2
    simpa using h1
  have hcnL : c ∉ Lb := fun hcL => hxn ⟨hx.1, Lb.mul_mem hp.2 hcL⟩
  have hc1 : c ≠ 1 := fun h => hcnL (h ▸ Lb.one_mem)
  obtain ⟨n, hn⟩ := hS.2.1 ⟨c, hc⟩
  have hcn : c ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hcn)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hc1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have hdvd : 2 ^ (k - 1) ∣ orderOf c := by
    rw [hk]; exact pow_dvd_pow 2 (by omega)
  have hord : orderOf (c ^ (2 ^ (k - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hk]
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
    exact Nat.mul_div_cancel _ (by positivity)
  set t := c ^ (2 ^ (k - 1)) with ht
  have htL1 : t ∈ L1b := L1b.pow_mem hcL1 _
  have htcent : ∀ x ∈ Lb, t * x * t⁻¹ = x := by
    intro y hy
    have hcomm : Commute c y := by
      have h := hcent y hy
      show c * y = y * c
      calc c * y = (c * y * c⁻¹) * c := by group
        _ = y * c := by rw [h]
    have h2 : t * y = y * t := (hcomm.pow_left (2 ^ (k - 1))).eq
    calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [h2]
      _ = y := by group
  let t' : ↥L1b := ⟨t, htL1⟩
  have ht'ord : orderOf t' = 2 := by
    rw [← hord]; exact (Subgroup.orderOf_mk t htL1)
  have hC := card_centralizer_involution_psl49 hL1 t' ht'ord
  have hle : Lb.subgroupOf L1b ≤ Subgroup.centralizer ({t'} : Set ↥L1b) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hyL : (y : Hb) ∈ Lb := hy
    apply Subtype.ext
    show t * (y : Hb) = (y : Hb) * t
    have := htcent y hyL
    calc t * (y : Hb) = (t * y * t⁻¹) * t := by group
      _ = y * t := by rw [this]
  have hcard := Subgroup.card_le_of_le hle
  rw [hC] at hcard
  have hsub : Nat.card ↥(Lb.subgroupOf L1b) = 168 := by
    rw [← hLc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLL).toEquiv
  omega

end Eight

end CFSG.Quasithin.Stellmacher.CD.L3YC
