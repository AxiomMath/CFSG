module

public import CFSG.Quasithin.EmptyFaithful.S153IRed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_commute_of_pRank {H : Subgroup G} (hH : CFSG.Open.pRank 3 H ≤ 1) {a b : G}
    (haH : a ∈ H) (hbH : b ∈ H) (ha1 : a ≠ 1) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) : b ∈ Subgroup.zpowers a := by
  by_contra hb'
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hao : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hb1 : b ≠ 1 := fun h => hb' (h ▸ Subgroup.one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hE : IsElemAbelian 3 (Subgroup.zpowers a) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have hcomm : ∀ e ∈ Subgroup.zpowers a, Commute e b := by
    intro e he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute a b from hab) n)
  obtain ⟨hE2, hc2⟩ := exists_elemAbelian_sup_zpowers hE hbo hcomm hb'
  have hcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr haH) (Subgroup.zpowers_le.mpr hbH)
  have h2 := CFSG.Quasithin.le_pRank Nat.prime_three hle hE2 (k := 2)
    (by rw [hc2, hcard]; norm_num)
  omega

theorem le_of_le_normalizer_isSylowTwoOf {S I Q : Subgroup G} (hS : IsSylowTwoOf S I) (hQI : Q ≤ I)
    (hQ : IsPGroup 2 Q) (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) : Q ≤ S := by
  have hS' : IsSylowTwoOf S (S ⊔ Q) := A4.isSylowTwoOf_mono hS le_sup_left (sup_le hS.1 hQI)
  have hnorm : (Q.subgroupOf (S ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hSQ Subgroup.le_normalizer)
  exact A4.le_of_normal_of_isSylowTwoOf hS' le_sup_right hnorm hQ

omit [Finite G] in
private theorem le_normalizer_of_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ≤ Subgroup.normalizer (B : Set G) := fun a ha => by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have key : ∀ b' ∈ B, a * b' * a⁻¹ = b' := fun b' hb' => by rw [hAB a ha b' hb']; group
  constructor
  · intro hb
    rw [key b hb]
    exact hb
  · intro hb
    have h1 : a⁻¹ * (a * b * a⁻¹) = (a * b * a⁻¹) * a⁻¹ := hAB a⁻¹ (A.inv_mem ha) _ hb
    have e : b = a * b * a⁻¹ := by
      calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
        _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [h1]
        _ = a * b * a⁻¹ := by group
    rw [e]
    exact hb

omit [Finite G] in
theorem exists_mul_eq_of_mem_sup_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B
    (le_normalizer_of_commute hAB)] at hx
  exact hx

theorem exists_mul_of_mem_sylow_inf {S L C : Subgroup G} (hSL : IsSylowTwoOf (S ⊓ L) L)
    (hS : IsPGroup 2 S) (hLC : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) {q : G} (hqS : q ∈ S)
    (hqLC : q ∈ L ⊔ C) : ∃ p ∈ S ⊓ L, ∃ d ∈ S ⊓ C, p * d = q := by
  have hq : q ∈ (S ⊓ L) ⊔ C :=
    A312.inf_sup_le_of_sylow hSL hS (le_normalizer_of_commute hLC) ⟨hqS, hqLC⟩
  obtain ⟨p, hp, d, hd, rfl⟩ :=
    exists_mul_eq_of_mem_sup_commute (A := S ⊓ L) (B := C) (fun a ha b hb => hLC a ha.2 b hb) hq
  refine ⟨p, hp, d, ⟨?_, hd⟩, rfl⟩
  have e : d = p⁻¹ * (p * d) := by group
  rw [e]
  exact S.mul_mem (S.inv_mem hp.1) hqS

private theorem eq_one_of_pow_two_pow_of_card_three {X : Type*} [Group X] (hX : Nat.card X = 3)
    (x : X) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h3 : x ^ 3 = 1 := by
    have := pow_card_eq_one' (G := X) (x := x)
    rwa [hX] at this
  have hd1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hd2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have hd : orderOf x ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd hd1 hd2
  rw [hcop.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem mem_normalizer_of_projection {Yp S I L : Subgroup G} (hS : IsSylowTwoOf S I) (hYpI : Yp ≤ I)
    (hSN : S ≤ Subgroup.normalizer (Yp : Set G)) (hin : Yp ≤ L ⊔ Subgroup.centralizer (L : Set G))
    (hSL : IsSylowTwoOf (S ⊓ L) L) (hcard : Nat.card (OTwoQuot Yp) = 3) {y l c : G} (hyY : y ∈ Yp)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hl : l ∈ L) (hc : c ∈ Subgroup.centralizer (L : Set G))
    (hlc : l * c = y) : c ∈ Subgroup.normalizer (Yp : Set G) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer (L : Set G) with hC
  set Q : Subgroup G := pCoreOf 2 Yp with hQdef
  have hLC : ∀ a ∈ L, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb a ha
  have hQY : Q ≤ Yp := pCoreOf_le 2 Yp
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 Yp
  have hSQ : S ≤ Subgroup.normalizer (Q : Set G) :=
    hSN.trans (normalizer_le_normalizer_pCoreOf 2 Yp)
  have hQS : Q ≤ S := le_of_le_normalizer_isSylowTwoOf hS (hQY.trans hYpI) hQ2 hSQ
  have hmemQ' : ∀ g : ↥Yp, g ∈ CFSG.Open.pCore 2 ↥Yp ↔ (g : G) ∈ Q := fun g =>
    (Subgroup.mem_map_iff_mem Yp.subtype_injective).symm
  have hmemQ : ∀ g : ↥Yp, (QuotientGroup.mk g : OTwoQuot Yp) = 1 ↔ (g : G) ∈ Q := fun g =>
    (QuotientGroup.eq_one_iff g).trans (hmemQ' g)
  have hlc' : l * c = c * l := hLC l hl c hc
  have hconj : ∀ q ∈ Q, c * q * c⁻¹ ∈ Yp := by
    intro q hq
    obtain ⟨p, hp, d, hd, hpd⟩ :=
      exists_mul_of_mem_sylow_inf hSL hS.2.1 hLC (hQS hq) (hin (hQY hq))
    have hdinv : d⁻¹ ∈ Subgroup.normalizer (Yp : Set G) :=
      (Subgroup.normalizer (Yp : Set G)).inv_mem (hSN hd.1)
    have hy' : d⁻¹ * y * d ∈ Yp := by
      have := (Subgroup.mem_normalizer_iff.mp hdinv y).mp hyY
      simpa using this
    have hpc : p * c = c * p := hLC p hp.2 c hc
    have hecd : c * d * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hd.2) (C.inv_mem hc)
    have hle : l * (c * d * c⁻¹) = c * d * c⁻¹ * l := hLC l hl _ hecd
    have key : c * q * c⁻¹ = q * ((d⁻¹ * y * d) * y⁻¹) := by
      rw [← hpd, ← hlc]
      calc c * (p * d) * c⁻¹ = (c * p) * d * c⁻¹ := by group
        _ = (p * c) * d * c⁻¹ := by rw [hpc]
        _ = p * (c * d * c⁻¹) := by group
        _ = p * (c * d * c⁻¹ * l * l⁻¹) := by group
        _ = p * (l * (c * d * c⁻¹) * l⁻¹) := by rw [hle]
        _ = p * d * (d⁻¹ * (l * c) * d * (l * c)⁻¹) := by group
    rw [key]
    exact Yp.mul_mem (hQY hq) (Yp.mul_mem hy' (Yp.inv_mem hyY))
  have hconjQ : ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro q hq
    have hmemY := hconj q hq
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    have hk' : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hx : (⟨c * q * c⁻¹, hmemY⟩ : ↥Yp) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [conj_pow, hk']
      simp
    have h1 : (QuotientGroup.mk (⟨c * q * c⁻¹, hmemY⟩ : ↥Yp) : OTwoQuot Yp) ^ 2 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
    exact (hmemQ _).mp (eq_one_of_pow_two_pow_of_card_three hcard _ h1)
  have hybar1 : (QuotientGroup.mk (⟨y, hyY⟩ : ↥Yp) : OTwoQuot Yp) ≠ 1 := by
    intro h
    have hyQ : y ∈ Q := (hmemQ ⟨y, hyY⟩).mp h
    obtain ⟨j, hj⟩ := hQ2 ⟨y, hyQ⟩
    have hj' : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have h3o : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hd : 3 ∣ 2 ^ j := h3o ▸ orderOf_dvd_of_pow_eq_one hj'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hgen : Subgroup.zpowers (QuotientGroup.mk (⟨y, hyY⟩ : ↥Yp) : OTwoQuot Yp) = ⊤ :=
    zpowers_eq_top_of_prime_card hcard hybar1
  apply A4.mem_normalizer_of_conj_mem
  intro x hx
  have hxbar : (QuotientGroup.mk (⟨x, hx⟩ : ↥Yp) : OTwoQuot Yp) ∈
      Subgroup.zpowers (QuotientGroup.mk (⟨y, hyY⟩ : ↥Yp) : OTwoQuot Yp) := by
    rw [hgen]
    trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxbar
  have hk' : (QuotientGroup.mk ((⟨y, hyY⟩ : ↥Yp) ^ k) : OTwoQuot Yp) =
      QuotientGroup.mk ⟨x, hx⟩ := by
    rw [QuotientGroup.mk_zpow]
    exact hk
  have hqmem : ((⟨y, hyY⟩ : ↥Yp) ^ k)⁻¹ * ⟨x, hx⟩ ∈ CFSG.Open.pCore 2 ↥Yp :=
    QuotientGroup.eq.mp hk'
  have hq : (y ^ k)⁻¹ * x ∈ Q := by
    have h := (hmemQ' _).mp hqmem
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] using h
  have hcy : c * y ^ k * c⁻¹ = y ^ k := by
    rw [← conj_zpow]
    congr 1
    calc c * y * c⁻¹ = c * (l * c) * c⁻¹ := by rw [hlc]
      _ = c * l := by group
      _ = y := by rw [← hlc', hlc]
  have e : c * x * c⁻¹ = (c * y ^ k * c⁻¹) * (c * ((y ^ k)⁻¹ * x) * c⁻¹) := by group
  rw [e, hcy]
  exact Yp.mul_mem (Yp.zpow_mem hyY k) (hQY (hconjQ _ hq))

end Generic

section Main

theorem input15343Project_holds : Input15343Project := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hopen hin
  set C : Subgroup G := Subgroup.centralizer (L : Set G) with hC
  have hLI : L ∈ cComp I := c.c33.mem
  have hLleI : L ≤ I := le_of_mem_cComp hLI
  have hS : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hLI) hS
  have hYpI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hnorm : I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I := c.facts.norm_eq
  have htheta : Yp = thetaOf (M ⊓ I) := c.facts.theta
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
    intro s hs
    have hsM : s ∈ M ⊓ I := ⟨c.hyp.hyp.T_le hs.1, hSI hs⟩
    rw [← hnorm] at hsM
    exact hsM.2
  have hYpM : Yp ≤ M ⊓ I := by
    rw [← hnorm]
    exact le_inf hYpI Subgroup.le_normalizer
  have hrank : CFSG.Open.pRank 3 Yp ≤ 1 := c.rank.le
  have hcard : Nat.card (OTwoQuot Yp) = 3 := hopen.a_ord
  have hLC : ∀ l ∈ L, ∀ x ∈ C, l * x = x * l := fun l hl x hx =>
    Subgroup.mem_centralizer_iff.mp hx l hl
  have hgenY : ∀ z ∈ M ⊓ I, orderOf z = 3 → z ∈ Yp := fun z hz hzo => by
    rw [htheta]
    exact Subgroup.subset_closure ⟨hz, hzo⟩
  have key : ∀ y ∈ Yp, orderOf y = 3 → y ∈ L ∨ y ∈ C := by
    intro y hy hyo
    have hy3 : y ^ 3 = 1 := hyo ▸ pow_orderOf_eq_one y
    have hy1 : y ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hyo
      omega
    obtain ⟨l, hl, x, hx, hlx⟩ := exists_mul_eq_of_mem_sup_commute hLC (hin hy)
    have hxN := mem_normalizer_of_projection hS hYpI hSN hin hSL hcard hy hy3 hy1 hl hx hlx
    have hlI : l ∈ I := hLleI hl
    have hxI : x ∈ I := by
      have e : x = l⁻¹ * y := by rw [← hlx]; group
      rw [e]
      exact I.mul_mem (I.inv_mem hlI) (hYpI hy)
    have hxM : x ∈ M ⊓ I := by
      rw [← hnorm]
      exact ⟨hxI, hxN⟩
    have hlM : l ∈ M ⊓ I := by
      have e : l = y * x⁻¹ := by rw [← hlx]; group
      rw [e]
      exact (M ⊓ I).mul_mem (hYpM hy) ((M ⊓ I).inv_mem hxM)
    have hlx' : l * x = x * l := hLC l hl x hx
    have hcm : Commute l x := hlx'
    subst hlx
    by_cases h3l : 3 ∣ orderOf l
    · left
      obtain ⟨a, ha⟩ : ∃ a, a = l ^ (orderOf l / 3) := ⟨_, rfl⟩
      have hao : orderOf a = 3 := by
        rw [ha]
        exact orderOf_pow_orderOf_div (orderOf_pos l).ne' h3l
      have haM : a ∈ M ⊓ I := by
        rw [ha]
        exact Subgroup.pow_mem _ hlM _
      have haY : a ∈ Yp := hgenY a haM hao
      have haL : a ∈ L := by
        rw [ha]
        exact Subgroup.pow_mem _ hl _
      have ha1 : a ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hao
        omega
      have ha3 : a ^ 3 = 1 := by
        have := pow_orderOf_eq_one a
        rwa [hao] at this
      have hcomm : a * (l * x) = (l * x) * a := by
        rw [ha]
        exact (((Commute.refl l).mul_right hcm).pow_left (orderOf l / 3)).eq
      exact (Subgroup.zpowers_le.mpr haL) (mem_zpowers_of_commute_of_pRank hrank haY hy ha1 ha3 hy3 hcomm)
    · right
      have hyn : (l * x) ^ orderOf l = x ^ orderOf l := by
        rw [hcm.mul_pow, pow_orderOf_eq_one, one_mul]
      have hxn : x ^ orderOf l ∈ C := C.pow_mem hx _
      have hnn : orderOf l * orderOf l % 3 = 1 := by
        have : orderOf l % 3 = 1 ∨ orderOf l % 3 = 2 := by omega
        rcases this with h | h <;> simp [Nat.mul_mod, h]
      have hyy : l * x = ((l * x) ^ orderOf l) ^ orderOf l := by
        rw [← pow_mul, pow_eq_pow_mod (orderOf l * orderOf l) hy3, hnn, pow_one]
      rw [hyy, hyn]
      exact C.pow_mem hxn _
  by_cases hcon : ∀ x ∈ M ⊓ I, orderOf x = 3 → x ∈ L
  · rw [htheta]
    exact (Subgroup.closure_le L).mpr fun x hx => hcon x hx.1 hx.2
  exfalso
  obtain ⟨x₀, hx₀M, hx₀o, hx₀L⟩ : ∃ x₀ ∈ M ⊓ I, orderOf x₀ = 3 ∧ x₀ ∉ L := by
    by_contra h
    exact hcon fun x hx hxo => by_contra fun hxL => h ⟨x, hx, hxo, hxL⟩
  have hx₀Y : x₀ ∈ Yp := hgenY x₀ hx₀M hx₀o
  have hx₀C : x₀ ∈ C := (key x₀ hx₀Y hx₀o).resolve_left hx₀L
  have hx₀3 : x₀ ^ 3 = 1 := hx₀o ▸ pow_orderOf_eq_one x₀
  have hall : ∀ z ∈ M ⊓ I, orderOf z = 3 → z ∈ C := by
    intro z hzM hzo
    have hzY : z ∈ Yp := hgenY z hzM hzo
    rcases key z hzY hzo with hzL | hzC
    · exfalso
      have hz1 : z ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hzo
        omega
      have hz3 : z ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one z
      have hcomm : z * x₀ = x₀ * z := hLC z hzL x₀ hx₀C
      have hmem := mem_zpowers_of_commute_of_pRank hrank hzY hx₀Y hz1 hz3 hx₀3 hcomm
      exact hx₀L ((Subgroup.zpowers_le.mpr hzL) hmem)
    · exact hzC
  have hYC : Yp ≤ C := by
    rw [htheta]
    exact (Subgroup.closure_le C).mpr fun z hz => hall z hz.1 hz.2
  have hLN : L ≤ Subgroup.normalizer (Yp : Set G) := by
    intro l hl
    refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
    have h := Subgroup.mem_centralizer_iff.mp (hYC hy) l hl
    have e : l * y * l⁻¹ = y := by rw [h]; group
    rw [e]
    exact hy
  have hLM : L ≤ M ⊓ I := by
    rw [← hnorm]
    exact le_inf hLleI hLN
  exact c.c33.not_le (hLM.trans inf_le_left)

end Main

end SBc

end CFSG.Quasithin
