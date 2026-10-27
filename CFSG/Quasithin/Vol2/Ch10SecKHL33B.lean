module

public import CFSG.Quasithin.Vol2.Ch10SecKHL33A
public import CFSG.Quasithin.Vol2.Ch10SecKHNine
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRad

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {Q : Type} [Group Q] [Finite Q]

theorem card_dvd_sixteen (hD : Fin253.RadData Q) {R : Subgroup Q} (hR : IsPGroup 2 R) :
    Nat.card R ∣ 16 := by
  obtain ⟨m, hm, -, hcard⟩ := hD.card
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
  have h1 : Nat.card R ∣ 16 * m := hcard ▸ Subgroup.card_subgroup_dvd_card R
  rw [hk] at h1 ⊢
  exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)).dvd_of_dvd_mul_right h1

theorem mul_self_eq_one_of_comm (hD : Fin253.RadData Q) {x : Q} (hx : x ≠ 1)
    (hxo : Odd (orderOf x)) {R : Subgroup Q} (hR : IsPGroup 2 R) {t : Q} (ht : t ∈ R)
    (htx : t * x = x * t) : t * t = 1 := by
  have h16 : t ^ 16 = 1 := by
    have h1 : (⟨t, ht⟩ : R) ^ Nat.card R = 1 := pow_card_eq_one'
    have h2 : t ^ Nat.card R = 1 := by
      have h3 := congrArg (fun y : R => (y : Q)) h1
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
      exact h3
    obtain ⟨c, hc⟩ := card_dvd_sixteen hD hR
    rw [hc, pow_mul, h2, one_pow]
  have hcomm : ∀ n : ℕ, t ^ n * x = x * t ^ n := fun n => (Commute.pow_left htx n).eq
  have e4 : ∀ u : Q, u * u * (u * u) = u ^ 4 := fun u => by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e2 : ∀ u : Q, u * u = u ^ 2 := fun u => (sq u).symm
  have h8 : t ^ 8 = 1 := by
    have h := hD.odd_no4 x hx hxo (t ^ 4) (hcomm 4) (by rw [e4, ← pow_mul]; exact h16)
    rwa [e2, ← pow_mul] at h
  have h4 : t ^ 4 = 1 := by
    have h := hD.odd_no4 x hx hxo (t ^ 2) (hcomm 2) (by rw [e4, ← pow_mul]; exact h8)
    rwa [e2, ← pow_mul] at h
  exact hD.odd_no4 x hx hxo t htx (by rw [e4]; exact h4)

theorem eq_of_comm (hD : Fin253.RadData Q) {x : Q} (hx : x ≠ 1) (hxo : Odd (orderOf x))
    {R : Subgroup Q} (hR : IsPGroup 2 R) {t s : Q} (ht : t ∈ R) (hs : s ∈ R) (ht1 : t ≠ 1)
    (hs1 : s ≠ 1) (htx : t * x = x * t) (hsx : s * x = x * s) : t = s := by
  by_contra hts
  have htt := mul_self_eq_one_of_comm hD hx hxo hR ht htx
  have hss := mul_self_eq_one_of_comm hD hx hxo hR hs hsx
  have htsx : (t * s) * x = x * (t * s) := by
    rw [mul_assoc, hsx, ← mul_assoc, htx, mul_assoc]
  have hts2 := mul_self_eq_one_of_comm hD hx hxo hR (R.mul_mem ht hs) htsx
  have hcomm : t * s = s * t := by
    have h1 : t * s = (t * s)⁻¹ := eq_inv_of_mul_eq_one_left hts2
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_left hss, inv_eq_of_mul_eq_one_left htt]
  exact hD.odd_noV x hx hxo t s ht1 hs1 hts htt hss hcomm htx hsx

omit [Finite Q] in
theorem le_normalizer_of_conj_mem {E R : Subgroup Q} (h : ∀ e ∈ E, ∀ w ∈ R, e * w * e⁻¹ ∈ R) :
    E ≤ Subgroup.normalizer (R : Set Q) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h e he w, fun hw => ?_⟩
  have h' := h e⁻¹ (E.inv_mem he) _ hw
  simpa [mul_assoc] using h'

theorem exists_not_mem_of_radData (hD : Fin253.RadData Q) {Y : Subgroup Q} {z : Q}
    (hz1 : z ≠ 1) (hzz : z * z = 1) (hzY : z ∈ Subgroup.normalizer (Y : Set Q))
    (h3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) (h9 : (pCoreOf 2 Y).relIndex Y = 9) :
    ∃ y ∈ Y, z * y * z⁻¹ * y⁻¹ ∉ pCoreOf 2 Y := by
  classical
  by_contra hall
  push Not at hall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEY, hE9⟩ := exists_le_card_nine h9
  have hEP : E ⊓ pCoreOf 2 Y = ⊥ := inf_pCoreOf_eq_bot hE9
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := E)
      (by rw [hE9]; norm_num)
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    have hmem : e ^ 3 ∈ E ⊓ pCoreOf 2 Y := ⟨E.pow_mem he 3, h3 e (hEY he)⟩
    rwa [hEP, Subgroup.mem_bot] at hmem
  have hodd : ∀ e ∈ E, e ≠ 1 → Odd (orderOf e) := by
    intro e he he1
    rw [orderOf_eq_prime (hE3 e he) he1]
    decide
  have hkey : ∀ R : Subgroup Q, IsPGroup 2 R → E ≤ Subgroup.normalizer (R : Set Q) →
      Nat.card R ≤ 2 := fun R hR hER =>
    card_le_two_of_conj hE9 hEc hER (card_dvd_sixteen hD hR)
      fun e he he1 t ht s hs ht1 hs1 het hes =>
        eq_of_comm hD he1 (hodd e he he1) hR ht hs ht1 hs1 het.symm hes.symm
  have hzP : z ∈ Subgroup.normalizer (pCoreOf 2 Y : Set Q) :=
    normalizer_le_normalizer_pCoreOf 2 Y hzY
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hZp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  set R₁ := pCoreOf 2 Y ⊔ Subgroup.zpowers z with hR₁def
  have hR₁ : IsPGroup 2 R₁ := IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 Y) hZp
    ((Subgroup.zpowers_le).2 hzP)
  have hYP : Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set Q) := le_normalizer_pCoreOf 2 Y
  have hzR : z ∈ R₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hconjR₁ : ∀ e ∈ E, ∀ w ∈ R₁, e * w * e⁻¹ ∈ R₁ := by
    intro e he
    suffices h : R₁ ≤ R₁.comap (MulAut.conj e).toMonoidHom from fun w hw => h hw
    refine sup_le (fun p hp => ?_) ((Subgroup.zpowers_le).2 ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hYP (hEY he)) p).1 hp)
    · have h1 := hall e (hEY he)
      have he' : (MulAut.conj e).toMonoidHom z = (z * e * z⁻¹ * e⁻¹)⁻¹ * z := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      show (MulAut.conj e).toMonoidHom z ∈ R₁
      rw [he']
      exact R₁.mul_mem (Subgroup.mem_sup_left (Subgroup.inv_mem _ h1)) hzR
  have hR₁2 := hkey R₁ hR₁ (le_normalizer_of_conj_mem hconjR₁)
  have hcent : ∀ e ∈ E, e * z * e⁻¹ = z := by
    intro e he
    by_contra hne
    have hw := hconjR₁ e he z hzR
    have hw1 : e * z * e⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have hz' : z = e⁻¹ * (e * z * e⁻¹) * e := by group
      rw [hz', h]
      group
    have : Fintype R₁ := Fintype.ofFinite _
    have h3' : 2 < Fintype.card R₁ := Fintype.two_lt_card_iff.2 ⟨⟨1, R₁.one_mem⟩, ⟨z, hzR⟩,
      ⟨_, hw⟩, fun h => hz1 (congrArg Subtype.val h).symm,
      fun h => hw1 (congrArg Subtype.val h).symm, fun h => hne (congrArg Subtype.val h).symm⟩
    rw [← Nat.card_eq_fintype_card] at h3'
    omega
  set Q8 := Fin253.quatSubgroup ⊤ z hzz
    (fun y _ y' _ hy hy' => hD.quat_mul z hzo y y' hy hy') with hQ8def
  have e4 : ∀ u : Q, u ^ 2 ^ 2 = (u * u) * (u * u) := fun u => by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hQ8p : IsPGroup 2 Q8 := by
    intro y
    refine ⟨2, Subtype.ext ?_⟩
    obtain ⟨-, hy⟩ := y.2
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [e4]
    rcases hy with h | h | h
    · rw [h]
      group
    · rw [h, hzz, one_mul]
    · rw [h, hzz]
  have hQ8n : E ≤ Subgroup.normalizer (Q8 : Set Q) := by
    refine le_normalizer_of_conj_mem fun e he w hw => ⟨Subgroup.mem_top _, ?_⟩
    obtain ⟨-, hw⟩ := hw
    rcases hw with h | h | h
    · left
      rw [h]
      group
    · right; left
      rw [h]
      exact hcent e he
    · right; right
      calc e * w * e⁻¹ * (e * w * e⁻¹) = e * (w * w) * e⁻¹ := by group
        _ = z := by rw [h]; exact hcent e he
  have hQ8 := hkey Q8 hQ8p hQ8n
  have h5 := hD.quat_card z hzo
  have hcardQ8 : Nat.card Q8 = Nat.card {y : Q // y = 1 ∨ y = z ∨ y * y = z} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y =>
      ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top _, h⟩⟩)
  omega

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
