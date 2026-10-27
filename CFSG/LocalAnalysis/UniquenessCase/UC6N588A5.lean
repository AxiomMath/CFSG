module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A4
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.N588A

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

theorem pow_dvd_sub_one_of_pow_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {e m a : ℕ} (he : 1 ≤ e) (hpe : p ∣ e - 1) (hm : ¬ p ∣ m) (h : p ^ a ∣ e ^ m - 1) :
    p ^ a ∣ e - 1 := by
  have hpe' : ¬ p ∣ e := by
    intro hdvd
    have h1 : p ∣ e - (e - 1) := Nat.dvd_sub hdvd hpe
    rw [Nat.sub_sub_self he] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hmul := Nat.emultiplicity_pow_sub_pow hp hodd (x := e) (y := 1) (by simpa using hpe) hpe' m
  rw [one_pow, emultiplicity_eq_zero.mpr hm, add_zero] at hmul
  rw [pow_dvd_iff_le_emultiplicity] at h ⊢
  rwa [hmul] at h

theorem mem_centralizer_of_isCyclic {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) {T : Subgroup X} (hTc : IsCyclic T) (hTp : IsPGroup p T) {n : X}
    (hn : n ∈ Subgroup.normalizer (T : Set X)) {m : ℕ} (hm : ¬ p ∣ m)
    (hnm : n ^ m ∈ Subgroup.centralizer (T : Set X)) {t : X} (ht : t ∈ T) (hto : orderOf t = p)
    (hnt : n * t = t * n) : n ∈ Subgroup.centralizer (T : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := hTc.exists_generator
  have hnu : n * (u : X) * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn _).mp u.2
  obtain ⟨e, he⟩ : ∃ e : ℕ, (u : X) ^ e = n * u * n⁻¹ := by
    obtain ⟨e, he⟩ := (mem_powers_iff_mem_zpowers (x := u)).mpr (hu ⟨_, hnu⟩)
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hpow : ∀ x ∈ T, ∃ i : ℕ, x = (u : X) ^ i := by
    intro x hx
    obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers (x := u)).mpr (hu ⟨x, hx⟩)
    exact ⟨i, by simpa using (congrArg Subtype.val hi).symm⟩
  have hconj : ∀ x ∈ T, n * x * n⁻¹ = x ^ e := by
    intro x hx
    obtain ⟨i, rfl⟩ := hpow x hx
    rw [← conj_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]
  have hiter : ∀ j : ℕ, ∀ x ∈ T, n ^ j * x * (n ^ j)⁻¹ = x ^ (e ^ j) := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      rw [pow_succ, mul_inv_rev]
      calc n ^ j * n * x * (n⁻¹ * (n ^ j)⁻¹) = n ^ j * (n * x * n⁻¹) * (n ^ j)⁻¹ := by group
        _ = n ^ j * x ^ e * (n ^ j)⁻¹ := by rw [hconj x hx]
        _ = (x ^ e) ^ (e ^ j) := ih _ (T.pow_mem hx e)
        _ = x ^ (e ^ (j + 1)) := by rw [← pow_mul, pow_succ, mul_comm]
  have hfix : ∀ x ∈ T, x ^ (e ^ m) = x := by
    intro x hx
    rw [← hiter m x hx, ← Subgroup.mem_centralizer_iff.mp hnm x hx, mul_inv_cancel_right]
  have hu1 : (u : X) ≠ 1 := by
    intro hu1
    obtain ⟨i, hi⟩ := hpow t ht
    rw [hi, hu1, one_pow, orderOf_one] at hto
    exact hp.one_lt.ne hto
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · exfalso
      apply hu1
      rw [h0, pow_zero] at he
      have e1 : (u : X) = n⁻¹ * (n * u * n⁻¹) * n := by group
      rw [e1, ← he]
      group
    · exact h0
  have hcardT : orderOf (u : X) = Nat.card T := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hu
  obtain ⟨a, ha⟩ := hTp.exists_card_eq
  have h1 : p ^ a ∣ e ^ m - 1 := by
    rw [← ha, ← hcardT]
    apply orderOf_dvd_of_pow_eq_one
    have hem : 1 ≤ e ^ m := Nat.one_le_pow _ _ he1
    calc (u : X) ^ (e ^ m - 1) = (u : X) ^ (e ^ m - 1) * u * (u : X)⁻¹ := by group
      _ = (u : X) ^ (e ^ m) * (u : X)⁻¹ := by rw [← pow_succ, Nat.sub_add_cancel hem]
      _ = 1 := by rw [hfix _ u.2, mul_inv_cancel]
  have h2 : p ∣ e - 1 := by
    rw [← hto]
    apply orderOf_dvd_of_pow_eq_one
    have htt : t ^ e = t := by rw [← hconj t ht, hnt, mul_inv_cancel_right]
    calc t ^ (e - 1) = t ^ (e - 1) * t * t⁻¹ := by group
      _ = t ^ e * t⁻¹ := by rw [← pow_succ, Nat.sub_add_cancel he1]
      _ = 1 := by rw [htt, mul_inv_cancel]
  have h3 := pow_dvd_sub_one_of_pow_dvd_pow_sub_one hp hodd he1 h2 hm h1
  have hue : (u : X) ^ e = u := by
    have h4 : (u : X) ^ (e - 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hcardT, ha]
      exact h3
    calc (u : X) ^ e = (u : X) ^ (e - 1) * u := by rw [← pow_succ, Nat.sub_add_cancel he1]
      _ = u := by rw [h4, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨i, rfl⟩ := hpow x hx
  have hnu' : n * (u : X) * n⁻¹ = u := by rw [← he, hue]
  have hni : n * (u : X) ^ i * n⁻¹ = (u : X) ^ i := by rw [← conj_pow, hnu']
  calc (u : X) ^ i * n = n * (u : X) ^ i * n⁻¹ * n := by rw [hni]
    _ = n * (u : X) ^ i := by group

namespace Hyp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {S Z : Subgroup G}

theorem eq_zpowers (h : Hyp G p S Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) : Z = zpowers z := by
  have hle : zpowers z ≤ Z := (Subgroup.zpowers_le).mpr hz
  have hdvd : orderOf z ∣ p := h.card ▸ Subgroup.orderOf_dvd_natCard Z hz
  have ho : orderOf z = p := by
    rcases (Nat.dvd_prime h.prime).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, ho, h.card])).symm

theorem exists_decomp (h : Hyp G p S Z) {J : Subgroup G}
    (hJC : J ⊓ Subgroup.centralizer (J : Set G) = ⊥) (hY : Z ⊔ J = ⊤)
    (hZJ : ¬ Z ≤ Subgroup.centralizer (J : Set G)) (hZnJ : ¬ Z ≤ J) {z t : G}
    (hZz : Z = zpowers z) (htJ : t ∈ J) (hjx : ∀ x ∈ J, t * x * t⁻¹ = z * x * z⁻¹) :
    ∃ c : G, z = t * c ∧ c ∈ Subgroup.center G ∧ c ∈ Subgroup.centralizer (J : Set G) ∧
      c ∈ S ∧ t ∈ S ∧ orderOf c = p ∧ orderOf t = p := by
  haveI := h.fact
  have hzZ : z ∈ Z := hZz ▸ Subgroup.mem_zpowers z
  set c : G := t⁻¹ * z with hc
  have hzeq : z = t * c := by rw [hc, mul_inv_cancel_left]
  have hcJ : c ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have e := hjx x hx
    calc x * c = t⁻¹ * (t * x * t⁻¹) * z := by rw [hc]; group
      _ = t⁻¹ * (z * x * z⁻¹) * z := by rw [e]
      _ = c * x := by rw [hc]; group
  have htz : t * z = z * t := by
    have e := hjx t htJ
    calc t * z = t * t * t⁻¹ * z := by group
      _ = z * t * z⁻¹ * z := by rw [e]
      _ = z * t := by group
  have hcz : c * z = z * c := by
    have e : z * t⁻¹ = t⁻¹ * z := by
      calc z * t⁻¹ = t⁻¹ * (t * z) * t⁻¹ := by group
        _ = t⁻¹ * (z * t) * t⁻¹ := by rw [htz]
        _ = t⁻¹ * z := by group
    rw [hc, mul_assoc, ← mul_assoc z t⁻¹ z, e, mul_assoc]
  have hcC : c ∈ Subgroup.center G := by
    have hle : Z ⊔ J ≤ Subgroup.centralizer ({c} : Set G) := by
      refine sup_le ?_ ?_
      · rw [hZz, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hcz.symm
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hcJ x hx
    rw [hY] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  have hcomm : Commute t c := Subgroup.mem_center_iff.mp hcC t
  have htp : t ^ p = 1 := by
    have hz := h.pow_eq_one hzZ
    rw [hzeq, hcomm.mul_pow] at hz
    have htp' : t ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hz
    have hmem : t ^ p ∈ J ⊓ Subgroup.centralizer (J : Set G) :=
      ⟨J.pow_mem htJ p, htp' ▸ Subgroup.inv_mem _ (Subgroup.pow_mem _ hcJ p)⟩
    rwa [hJC, Subgroup.mem_bot] at hmem
  have hcp : c ^ p = 1 := by
    have hz := h.pow_eq_one hzZ
    rwa [hzeq, hcomm.mul_pow, htp, one_mul] at hz
  have hc1 : c ≠ 1 := by
    intro hc1
    apply hZnJ
    rw [hZz, Subgroup.zpowers_le, hzeq, hc1, mul_one]
    exact htJ
  have ht1 : t ≠ 1 := by
    intro ht1
    apply hZJ
    rw [hZz, Subgroup.zpowers_le, hzeq, ht1, one_mul]
    exact hcJ
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  have hto : orderOf t = p := orderOf_eq_prime htp ht1
  have hcS : c ∈ S := by
    have hzc : zpowers c ≤ Subgroup.center G := (Subgroup.zpowers_le).mpr hcC
    haveI hN : (zpowers c).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_center_iff.mp (hzc hx) g, mul_inv_cancel_right]
      exact hx⟩
    have hP : IsPGroup p (zpowers c) :=
      IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers, hco])
    obtain ⟨Q, hQS⟩ := exists_sylow_of_isSylowOf_top h.sylow
    exact (hQS ▸ hP.le_sylow_of_normal Q) (Subgroup.mem_zpowers c)
  have htS : t ∈ S := by
    have e : t = z * c⁻¹ := by rw [hzeq, mul_inv_cancel_right]
    rw [e]
    exact S.mul_mem (h.le hzZ) (S.inv_mem hcS)
  exact ⟨c, hzeq, hcC, hcJ, hcS, htS, hco, hto⟩

theorem conj_eq_of_conj_mem (h : Hyp G p S Z) {J : Subgroup G}
    (hJC : J ⊓ Subgroup.centralizer (J : Set G) = ⊥) {z t c : G} (hZz : Z = zpowers z)
    (hzeq : z = t * c) (htJ : t ∈ J) (hcC : c ∈ Subgroup.center G)
    (hcJ : c ∈ Subgroup.centralizer (J : Set G)) (hcS : c ∈ S) (hco : orderOf c = p)
    (hto : orderOf t = p) {k : G} (hkJ : k ∈ J) (hk : k⁻¹ * t * k ∈ S) : k⁻¹ * t * k = t := by
  have hck : k⁻¹ * c * k = c := by
    rw [mul_assoc, (Subgroup.mem_center_iff.mp hcC k).symm, inv_mul_cancel_left]
  have hzk : k⁻¹ * z * k = (k⁻¹ * t * k) * c := by
    calc k⁻¹ * z * k = (k⁻¹ * t * k) * (k⁻¹ * c * k) := by rw [hzeq]; group
      _ = (k⁻¹ * t * k) * c := by rw [hck]
  have hzkS : k⁻¹ * z * k ∈ S := by
    rw [hzk]
    exact S.mul_mem hk hcS
  have hZk : CFSG.conjugate Z k ≤ S := by
    intro x hx
    rw [mem_conjugate_iff, hZz] at hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : x = (k⁻¹ * z * k) ^ i := by
      rw [show k⁻¹ * z * k = k⁻¹ * z * k⁻¹⁻¹ by rw [inv_inv], conj_zpow, hi]
      group
    rw [e]
    exact S.zpow_mem hzkS i
  have hZk' := h.wc k hZk
  have hzkZ : k⁻¹ * z * k ∈ Z := by
    rw [← hZk', mem_conjugate_iff]
    have hzZ : z ∈ Z := hZz ▸ Subgroup.mem_zpowers z
    simpa [mul_assoc] using hzZ
  rw [hZz] at hzkZ
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hzkZ
  have hcomm : Commute t c := Subgroup.mem_center_iff.mp hcC t
  rw [hzk, hzeq, hcomm.mul_zpow] at hi
  have hcC' : ∀ y : G, y * c ^ (i - 1) = c ^ (i - 1) * y := fun y =>
    Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hcC _) y
  have hkey : (t ^ i)⁻¹ * (k⁻¹ * t * k) = c ^ (i - 1) := by
    have e1 : k⁻¹ * t * k = t ^ i * c ^ i * c⁻¹ := by rw [hi, mul_inv_cancel_right]
    rw [e1, zpow_sub_one]
    group
  have hmem : c ^ (i - 1) ∈ J ⊓ Subgroup.centralizer (J : Set G) := by
    refine ⟨?_, Subgroup.zpow_mem _ hcJ _⟩
    rw [← hkey]
    exact J.mul_mem (J.inv_mem (J.zpow_mem htJ i))
      (J.mul_mem (J.mul_mem (J.inv_mem hkJ) htJ) hkJ)
  rw [hJC, Subgroup.mem_bot] at hmem
  have hdvd : (p : ℤ) ∣ i - 1 := by
    rw [← hco]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hmem
  have hti : t ^ (i - 1) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hto]
    exact hdvd
  rw [hmem] at hkey
  have e2 : k⁻¹ * t * k = t ^ i := by
    rw [← mul_one (t ^ i), ← hkey, mul_inv_cancel_left]
  rw [e2]
  calc t ^ i = t ^ (i - 1) * t := by rw [← zpow_add_one, sub_add_cancel]
    _ = t := by rw [hti, one_mul]

end Hyp

end CFSG.LocalAnalysis.UniquenessCase.UCK.N588A
