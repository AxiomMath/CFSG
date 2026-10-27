module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.L14324

open CFSG.Open CFSG.Quasithin

section Abstract

variable {Q : Type*} [Group Q] [Finite Q]

theorem false_of_faithful_eight (A E : Subgroup Q) (hAn : ∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ ∈ A)
    (hA9 : Nat.card A = 9) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hE8 : Nat.card E = 8)
    (hEsq : ∀ e ∈ E, e * e = 1) (hfaith : ∀ e ∈ E, (∀ a ∈ A, e * a = a * e) → e = 1) : False := by
  classical
  let act : MulAction ↥E ↥A :=
    { smul := fun e a => ⟨(e : Q) * a * (e : Q)⁻¹, hAn _ e.2 _ a.2⟩
      one_smul := fun a => Subtype.ext (by
        show ((1 : ↥E) : Q) * a * ((1 : ↥E) : Q)⁻¹ = a
        simp)
      mul_smul := fun e f a => Subtype.ext (by
        show ((e * f : ↥E) : Q) * a * ((e * f : ↥E) : Q)⁻¹ =
          (e : Q) * ((f : Q) * a * (f : Q)⁻¹) * (e : Q)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hsmul : ∀ (e : ↥E) (a : ↥A), ((e • a : ↥A) : Q) = (e : Q) * a * (e : Q)⁻¹ :=
    fun _ _ => rfl
  have : Fintype ↥E := Fintype.ofFinite _
  have : Fintype ↥A := Fintype.ofFinite _
  let C : ↥E → Subgroup ↥A := fun e =>
    { carrier := {a | e • a = a}
      mul_mem' := fun {a b} ha hb => by
        show e • (a * b) = a * b
        apply Subtype.ext
        have ha' : (e : Q) * a * (e : Q)⁻¹ = a := congrArg Subtype.val ha
        have hb' : (e : Q) * b * (e : Q)⁻¹ = b := congrArg Subtype.val hb
        rw [hsmul, Subgroup.coe_mul]
        calc (e : Q) * (a * b) * (e : Q)⁻¹
            = ((e : Q) * a * (e : Q)⁻¹) * ((e : Q) * b * (e : Q)⁻¹) := by group
          _ = a * b := by rw [ha', hb']
      one_mem' := Subtype.ext (by rw [hsmul]; simp)
      inv_mem' := fun {a} ha => by
        show e • a⁻¹ = a⁻¹
        apply Subtype.ext
        have ha' : (e : Q) * a * (e : Q)⁻¹ = a := congrArg Subtype.val ha
        rw [hsmul, Subgroup.coe_inv]
        calc (e : Q) * (a : Q)⁻¹ * (e : Q)⁻¹ = ((e : Q) * a * (e : Q)⁻¹)⁻¹ := by group
          _ = (a : Q)⁻¹ := by rw [ha'] }
  have hcardC : ∀ e : ↥E, Fintype.card (MulAction.fixedBy ↥A e) = Nat.card (C e) := by
    intro e
    rw [← Nat.card_eq_fintype_card]
    rfl
  have hdvd : ∀ e : ↥E, Nat.card (C e) ∣ 9 := fun e => hA9 ▸ Subgroup.card_subgroup_dvd_card _
  have hne9 : ∀ e : ↥E, e ≠ 1 → Nat.card (C e) ≠ 9 := by
    intro e he h9
    apply he
    have htop : C e = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h9, hA9])
    have h1 := hfaith _ e.2 fun a ha => by
      have hmem : (⟨a, ha⟩ : ↥A) ∈ C e := htop ▸ Subgroup.mem_top _
      have h2 : (e : Q) * a * (e : Q)⁻¹ = a := congrArg Subtype.val hmem
      calc (e : Q) * a = (e : Q) * a * (e : Q)⁻¹ * e := by group
        _ = a * e := by rw [h2]
    exact Subtype.ext h1
  have hval : ∀ e : ↥E, e ≠ 1 → Nat.card (C e) = 1 ∨ Nat.card (C e) = 3 := by
    intro e he
    have h := hdvd e
    have h9 := hne9 e he
    have : Nat.card (C e) ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hinv : ∀ e : ↥E, Nat.card (C e) = 1 → ∀ a : ↥A, (e • a : ↥A) = a⁻¹ := by
    intro e h1 a
    have hbot : C e = ⊥ := (Subgroup.card_eq_one).mp h1
    have hfix : a * (e • a) ∈ C e := by
      show e • (a * (e • a)) = a * (e • a)
      apply Subtype.ext
      have hee : (e : Q) * e = 1 := hEsq _ e.2
      rw [hsmul, Subgroup.coe_mul, hsmul]
      have hea : (e : Q) * a * (e : Q)⁻¹ ∈ A := hAn _ e.2 _ a.2
      calc (e : Q) * (a * ((e : Q) * a * (e : Q)⁻¹)) * (e : Q)⁻¹
          = ((e : Q) * a * (e : Q)⁻¹) * (((e : Q) * e) * a * ((e : Q) * e)⁻¹) := by group
        _ = ((e : Q) * a * (e : Q)⁻¹) * a := by rw [hee]; group
        _ = a * ((e : Q) * a * (e : Q)⁻¹) := hAab _ hea _ a.2
    rw [hbot, Subgroup.mem_bot] at hfix
    exact (eq_inv_of_mul_eq_one_right hfix)
  have huniq : ∀ e f : ↥E, Nat.card (C e) = 1 → Nat.card (C f) = 1 → e = f := by
    intro e f he hf
    have hef : ∀ a : ↥A, (e : Q) * a * (e : Q)⁻¹ = (f : Q) * a * (f : Q)⁻¹ := by
      intro a
      have h1 := congrArg Subtype.val (hinv e he a)
      have h2 := congrArg Subtype.val (hinv f hf a)
      rw [hsmul] at h1 h2
      rw [h1, h2]
    have hk : (f : Q)⁻¹ * e = 1 := hfaith _ (E.mul_mem (E.inv_mem f.2) e.2) fun a ha => by
      have h := hef ⟨a, ha⟩
      calc (f : Q)⁻¹ * e * a = (f : Q)⁻¹ * ((e : Q) * a * (e : Q)⁻¹) * e := by group
        _ = (f : Q)⁻¹ * ((f : Q) * a * (f : Q)⁻¹) * e := by rw [h]
        _ = a * ((f : Q)⁻¹ * e) := by group
    apply Subtype.ext
    calc (e : Q) = (f : Q) * ((f : Q)⁻¹ * e) := by group
      _ = f := by rw [hk, mul_one]
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥E ↥A
  simp only [hcardC] at hB
  rw [← Nat.card_eq_fintype_card (α := ↥E), hE8] at hB
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥E))] at hB
  have h1 : Nat.card (C 1) = 9 := by
    have htop : C 1 = ⊤ := by
      ext a
      simp only [Subgroup.mem_top, iff_true]
      show (1 : ↥E) • a = a
      exact one_smul _ a
    rw [htop, Subgroup.card_top, hA9]
  rw [h1] at hB
  set s := (Finset.univ : Finset ↥E).erase 1 with hs
  set s1 := s.filter (fun e => Nat.card (C e) = 1) with hs1
  have hs1card : s1.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
    huniq a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hscard : s.card = 7 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hE8]
  have hsum : ∑ e ∈ s, Nat.card (C e) = 3 * s.card - 2 * s1.card := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun e => Nat.card (C e) = 1)]
    have ha : ∑ e ∈ s1, Nat.card (C e) = s1.card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun e he => (Finset.mem_filter.mp he).2
    have hb : ∑ e ∈ s.filter (fun e => ¬ Nat.card (C e) = 1), Nat.card (C e) =
        3 * (s.filter (fun e => ¬ Nat.card (C e) = 1)).card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum, mul_one]
      refine Finset.sum_congr rfl fun e he => ?_
      obtain ⟨hes, hne⟩ := Finset.mem_filter.mp he
      rcases hval e (Finset.ne_of_mem_erase hes) with h | h
      · exact absurd h hne
      · exact h
    have hcard := Finset.card_filter_add_card_filter_not
      (s := s) (fun e => Nat.card (C e) = 1)
    have ha2 : ∑ x ∈ s.filter (fun e => Nat.card (C e) = 1), Nat.card (C x) = s1.card := ha
    rw [ha2, hb]
    rw [← hs1] at hcard
    omega
  rw [hsum, hscard] at hB
  omega

end Abstract


theorem comm_center_left {G' : Type*} [Group G'] {z a b : G'} (hza : z * a = a * z)
    (hzb : z * b = b * z) : z * a * b * (z * a)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc : Commute z (a * b * a⁻¹) :=
    ((Commute.mul_right hza hzb).mul_right (Commute.inv_right hza))
  have e : z * a * b * (z * a)⁻¹ * b⁻¹ = (z * (a * b * a⁻¹)) * z⁻¹ * b⁻¹ := by group
  rw [e, hc.eq]
  group

theorem comm_center_right {G' : Type*} [Group G'] {z a b : G'} (hza : z * a = a * z)
    (hzb : z * b = b * z) : a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc : Commute z (b * a⁻¹) := (Commute.mul_right hzb (Commute.inv_right hza))
  have e : a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * (z * (b * a⁻¹)) * b⁻¹ * z⁻¹ := by group
  rw [e, hc.eq]
  have hzb' : Commute z b⁻¹ := Commute.inv_right hzb
  have e2 : a * (b * a⁻¹ * z) * b⁻¹ * z⁻¹ = a * b * a⁻¹ * (z * b⁻¹) * z⁻¹ := by group
  rw [e2, hzb'.eq]
  group

section Steps

variable {G' : Type*} [Group G'] [Finite G']

theorem eq_bot_of_le_centralizer (hO2 : ∀ N : Subgroup G', N.Normal → IsPGroup 2 N → N = ⊥)
    {P : Subgroup G'} [hPn : P.Normal] (hZ3 : Nat.card (Subgroup.center ↥P) = 3)
    (hidx : P.index ∣ 16) {Y : Subgroup G'} (hY2 : IsPGroup 2 Y)
    (hYC : Y ≤ Subgroup.centralizer (P : Set G')) : Y = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G' := Subgroup.centralizer (P : Set G') with hK
  set Z : Subgroup G' := (Subgroup.center ↥P).map P.subtype with hZdef
  have hZK : Z ≤ K := by
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun p hp =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨p, hp⟩)
  have hPK : P ⊓ K = Z := by
    ext x
    constructor
    · rintro ⟨hxP, hxK⟩
      refine ⟨⟨x, hxP⟩, Subgroup.mem_center_iff.mpr fun p => Subtype.ext ?_, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hxK p p.2)
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hZK ⟨z, hz, rfl⟩⟩
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective P.subtype_injective, hZ3]
  have hrel : P.relIndex K ∣ 16 := (Subgroup.relIndex_dvd_index_of_normal P K).trans hidx
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show P.relIndex K ∣ 2 ^ 4 from hrel)
  have hKcard : Nat.card K = 2 ^ a * 3 := by
    have := Subgroup.relIndex_mul_card P K
    rw [hPK, hZcard, ha] at this
    exact this.symm
  have hYK : IsPGroup 2 (Y.subgroupOf K) := hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYC).symm
  obtain ⟨S, hS⟩ := hYK.exists_le_sylow
  have hScard : Nat.card (S : Subgroup ↥K) = 2 ^ a := by
    rw [Sylow.card_eq_multiplicity, hKcard, Nat.factorization_mul (by positivity) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hnorm : Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K) = ⊤ := by
    set N := Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K)
    have h1 : (S : Subgroup ↥K) ≤ N := Subgroup.le_normalizer
    have h2 : Z.subgroupOf K ≤ N := by
      intro z hz
      have hzZ : (z : G') ∈ Z := Subgroup.mem_subgroupOf.mp hz
      have hzP : (z : G') ∈ P := (hPK ▸ inf_le_left : Z ≤ P) hzZ
      rw [Subgroup.mem_normalizer_iff]
      intro n
      have hc : z * n = n * z := Subtype.ext (Subgroup.mem_centralizer_iff.mp n.2 _ hzP)
      have : z * n * z⁻¹ = n := by rw [hc]; group
      rw [this]
    have hd1 : 2 ^ a ∣ Nat.card N := hScard ▸ Subgroup.card_dvd_of_le h1
    have hZK' : Nat.card (Z.subgroupOf K) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZcard]
    have hd2 : 3 ∣ Nat.card N := hZK' ▸ Subgroup.card_dvd_of_le h2
    have hcop : Nat.Coprime (2 ^ a) 3 := Nat.Coprime.pow_left a (by norm_num)
    have hd : 2 ^ a * 3 ∣ Nat.card N := hcop.mul_dvd_of_dvd_of_dvd hd1 hd2
    have hle : Nat.card N ≤ Nat.card ↥K := Subgroup.card_le_card_group N
    have hK' : Nat.card ↥K = 2 ^ a * 3 := hKcard
    apply Subgroup.eq_top_of_card_eq
    have hpos : 0 < Nat.card N := Nat.card_pos
    have := Nat.le_of_dvd hpos hd
    omega
  have hSn : (S : Subgroup ↥K).Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  have hSc : (S : Subgroup ↥K).Characteristic := Sylow.characteristic_of_normal S hSn
  have hSmap : ((S : Subgroup ↥K).map K.subtype).Normal := inferInstance
  have hS2 : IsPGroup 2 ((S : Subgroup ↥K).map K.subtype) := S.isPGroup'.map K.subtype
  have hbot := hO2 _ hSmap hS2
  rw [eq_bot_iff]
  intro y hy
  have hyS : (⟨y, hYC hy⟩ : ↥K) ∈ (S : Subgroup ↥K) := hS (Subgroup.mem_subgroupOf.mpr hy)
  have : y ∈ (S : Subgroup ↥K).map K.subtype := ⟨_, hyS, rfl⟩
  rwa [hbot] at this

omit [Finite G'] in
theorem commutator_mem_center {P : Subgroup G'} [hP : CFSG.IsExtraspecial 3 ↥P] :
    ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ (Subgroup.center ↥P).map P.subtype := by
    intro p hp q hq
    have hEA := CFSG.IsExtraspecial.quotient_elementary_abelian 3 ↥P
    set y : ↥P := ⟨p, hp⟩ * ⟨q, hq⟩ * (⟨p, hp⟩ : ↥P)⁻¹ * (⟨q, hq⟩ : ↥P)⁻¹ with hy
    have hy1 : (QuotientGroup.mk y : ↥P ⧸ Subgroup.center ↥P) = 1 := by
      rw [hy, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        mul_comm' (QuotientGroup.mk (⟨p, hp⟩ : ↥P) : ↥P ⧸ Subgroup.center ↥P)]
      group
    refine ⟨y, (QuotientGroup.eq_one_iff y).mp hy1, ?_⟩
    rw [hy]
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]

theorem commute_of_conj_mem_center {P : Subgroup G'}
    [hP : CFSG.IsExtraspecial 3 ↥P] {x : G'} (hx : x * x = 1)
    (hxP : ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ (Subgroup.center ↥P).map P.subtype) :
    ∀ p ∈ P, x * p = p * x := by
  classical
  set Z : Subgroup G' := (Subgroup.center ↥P).map P.subtype with hZdef
  have hZ3 : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective P.subtype_injective]
    exact CFSG.IsExtraspecial.center_order_p 3 ↥P
  have hZc : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z := by
    rintro _ ⟨w, hw, rfl⟩ p hp
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨p, hp⟩).symm
  have hZP : Z ≤ P := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Z := commutator_mem_center
  obtain ⟨p₀, hp₀, q₀, hq₀, hne⟩ : ∃ p₀ ∈ P, ∃ q₀ ∈ P, p₀ * q₀ * p₀⁻¹ * q₀⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hnt := CFSG.IsExtraspecial.quotient_nontrivial 3 ↥P
    obtain ⟨u, v, huv⟩ := hnt
    apply huv
    induction u using QuotientGroup.induction_on with | H u => ?_
    induction v using QuotientGroup.induction_on with | H v => ?_
    have hu : u ∈ Subgroup.center ↥P := Subgroup.mem_center_iff.mpr fun r => Subtype.ext (by
      have h0 := hall r r.2 u u.2
      have h1 : (r : G') * u * (r : G')⁻¹ = u := mul_inv_eq_one.mp h0
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mul_inv_eq_iff_eq_mul.mp h1)
    have hv : v ∈ Subgroup.center ↥P := Subgroup.mem_center_iff.mpr fun r => Subtype.ext (by
      have h0 := hall r r.2 v v.2
      have h1 : (r : G') * v * (r : G')⁻¹ = v := mul_inv_eq_one.mp h0
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mul_inv_eq_iff_eq_mul.mp h1)
    rw [(QuotientGroup.eq_one_iff u).mpr hu, (QuotientGroup.eq_one_iff v).mpr hv]
  set c := p₀ * q₀ * p₀⁻¹ * q₀⁻¹ with hc
  have hcZ : c ∈ Z := hcomm p₀ hp₀ q₀ hq₀
  have hzp : ∀ p ∈ P, ∃ z ∈ Z, x * p * x⁻¹ = z * p := fun p hp =>
    ⟨_, hxP p hp, by group⟩
  obtain ⟨z₁, hz₁, h₁⟩ := hzp p₀ hp₀
  obtain ⟨z₂, hz₂, h₂⟩ := hzp q₀ hq₀
  have hxc : x * c * x⁻¹ = c := by
    have e : x * c * x⁻¹ = (x * p₀ * x⁻¹) * (x * q₀ * x⁻¹) * (x * p₀ * x⁻¹)⁻¹ *
        (x * q₀ * x⁻¹)⁻¹ := by rw [hc]; group
    rw [e, h₁, h₂, hc, comm_center_left (hZc z₁ hz₁ p₀ hp₀)
      (hZc z₁ hz₁ (z₂ * q₀) (P.mul_mem (hZP hz₂) hq₀)),
      comm_center_right (hZc z₂ hz₂ p₀ hp₀) (hZc z₂ hz₂ q₀ hq₀)]
  have hZc' : Z = Subgroup.zpowers c := by
    have hle : Subgroup.zpowers c ≤ Z := (Subgroup.zpowers_le).mpr hcZ
    have hc3 : Nat.card (Subgroup.zpowers c) = 3 := by
      have hdvd : Nat.card (Subgroup.zpowers c) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exfalso
        apply hne
        rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
        exact h
      · exact h
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hZ3, hc3])).symm
  have hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z := by
    intro z hz
    rw [hZc'] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hxc]
  intro p hp
  obtain ⟨z, hz, hzx⟩ := hzp p hp
  have hz2 : z * z = 1 := by
    have h1 : x * (x * p * x⁻¹) * x⁻¹ = p := by
      calc x * (x * p * x⁻¹) * x⁻¹ = (x * x) * p * (x * x)⁻¹ := by group
        _ = p := by rw [hx]; group
    rw [hzx] at h1
    have h2 : x * (z * p) * x⁻¹ = (x * z * x⁻¹) * (x * p * x⁻¹) := by group
    rw [h2, hxZ z hz, hzx] at h1
    exact mul_eq_right.mp (by rw [mul_assoc]; exact h1)
  have hz1 : z = 1 := by
    have h3 : z ^ 3 = 1 := by
      have : orderOf z ∣ 3 := by
        have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
        rw [hZ3] at this
        rwa [← Subgroup.orderOf_mk z hz]
      exact orderOf_dvd_iff_pow_eq_one.mp this
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [h3, hz2]; group
  rw [hz1, one_mul] at hzx
  calc x * p = x * p * x⁻¹ * x := by group
    _ = p * x := by rw [hzx]

end Steps


section Concl3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem card_le_four_of_concl3 (hXΓ : X ≤ Γ) (hX : IsElemAbelian 2 X) {k : ℕ}
    (hk : Nat.card X = 2 ^ k) (hO2 : pCoreOf 2 Γ = ⊥) (h3 : G112Concl3 Γ) :
    Nat.card X ≤ 4 := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, P, hPn, hPe, hP27, -, hidx, -⟩ := h3
  have hO2' : ∀ N : Subgroup ↥Γ, N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hN2
    have h1 : N ≤ CFSG.Open.pCore 2 ↥Γ := CFSG.LieType.BorelTits.le_pCore 2 hN hN2
    have h2 : CFSG.Open.pCore 2 ↥Γ = ⊥ := by
      have := hO2
      rw [pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective] at this
      exact this
    exact le_bot_iff.mp (h2 ▸ h1)
  by_contra hgt
  push Not at hgt
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set X' : Subgroup ↥Γ := X.subgroupOf Γ with hX'
  have hX'card : Nat.card X' = 2 ^ k := by
    rw [hX', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXΓ).toEquiv, hk]
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥X') 2 (n := 3)
    (by rw [hX'card]; exact Nat.pow_dvd_pow 2 hk3)
  set E : Subgroup ↥Γ := E₀.map X'.subtype with hE
  have hEcard : Nat.card E = 8 := by
    rw [hE, Subgroup.card_map_of_injective X'.subtype_injective, hE₀]
    norm_num
  have hEX : E ≤ X' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hEsq : ∀ e ∈ E, e * e = 1 := by
    intro e he
    apply Subtype.ext
    have := hX.2 _ (Subgroup.mem_subgroupOf.mp (hEX he))
    simpa [sq] using this
  set Zp : Subgroup ↥Γ := (Subgroup.center ↥P).map P.subtype with hZp
  have hZpP : Zp ≤ P := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hZpn : Zp.Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    have hgw : g * (w : ↥Γ) * g⁻¹ ∈ P := hPn.conj_mem _ w.2 g
    refine ⟨⟨_, hgw⟩, Subgroup.mem_center_iff.mpr fun q => Subtype.ext ?_, rfl⟩
    have hq : g⁻¹ * (q : ↥Γ) * g ∈ P := by
      have := hPn.conj_mem _ q.2 g⁻¹
      simpa using this
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨_, hq⟩)
    simp only [Subgroup.coe_mul] at hc
    show (q : ↥Γ) * (g * w * g⁻¹) = g * w * g⁻¹ * q
    calc (q : ↥Γ) * (g * w * g⁻¹) = g * ((g⁻¹ * q * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
      _ = g * w * g⁻¹ * q := by group
  set f : ↥Γ →* ↥Γ ⧸ Zp := QuotientGroup.mk' Zp with hf
  set A : Subgroup (↥Γ ⧸ Zp) := (f.comp P.subtype).range with hA
  set E' : Subgroup (↥Γ ⧸ Zp) := (f.comp E.subtype).range with hE'
  have hkerP : (f.comp P.subtype).ker = Subgroup.center ↥P := by
    ext p
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨w, hw, hwp⟩
      have : w = p := Subtype.ext hwp
      rwa [← this]
    · intro hp
      exact ⟨p, hp, rfl⟩
  have hA9 : Nat.card A = 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.comp P.subtype).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp P.subtype)).toEquiv,
      hkerP, hP27, CFSG.IsExtraspecial.center_order_p 3 ↥P] at h1
    rw [hA]
    omega
  have hkerE : (f.comp E.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at he
    have h2 : orderOf (e : ↥Γ) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hEsq _ e.2)
    have hZp3 : Nat.card Zp = 3 := by
      rw [hZp, Subgroup.card_map_of_injective P.subtype_injective]
      exact CFSG.IsExtraspecial.center_order_p 3 ↥P
    have h3 : orderOf (e : ↥Γ) ∣ 3 := by
      have := orderOf_dvd_natCard (⟨_, he⟩ : ↥Zp)
      rw [hZp3, Subgroup.orderOf_mk] at this
      exact this
    have h1 : orderOf (e : ↥Γ) = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h3
    rw [orderOf_eq_one_iff] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hE'8 : Nat.card E' = 8 := by
    rw [hE', ← Nat.card_congr (MonoidHom.ofInjective
      ((MonoidHom.ker_eq_bot_iff _).mp hkerE)).toEquiv, hEcard]
  refine false_of_faithful_eight A E' ?_ hA9 ?_ hE'8 ?_ ?_
  ·
    rintro _ ⟨e, rfl⟩ _ ⟨p, rfl⟩
    refine ⟨⟨(e : ↥Γ) * p * (e : ↥Γ)⁻¹, hPn.conj_mem _ p.2 _⟩, ?_⟩
    simp [map_mul, map_inv]
  ·
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    have hc := commutator_mem_center (G' := ↥Γ) (P := P) p p.2 q q.2
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← map_mul, ← map_mul, hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have e1 : ((p : ↥Γ) * q)⁻¹ * (q * p) = (q : ↥Γ)⁻¹ * (p : ↥Γ)⁻¹ * (q : ↥Γ)⁻¹⁻¹ *
        (p : ↥Γ)⁻¹⁻¹ := by group
    rw [e1]
    exact commutator_mem_center (G' := ↥Γ) (P := P) _ (P.inv_mem q.2) _ (P.inv_mem p.2)
  · rintro _ ⟨e, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul]
    show f ((e : ↥Γ) * (e : ↥Γ)) = 1
    rw [hEsq _ e.2, map_one]
  ·
    rintro _ ⟨e, rfl⟩ hcent
    have hxP : ∀ p ∈ P, (e : ↥Γ) * p * (e : ↥Γ)⁻¹ * p⁻¹ ∈ Zp := by
      intro p hp
      have h1 := hcent _ ⟨⟨p, hp⟩, rfl⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
      rw [← map_mul, ← map_mul, hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h1
      have hconj : (e : ↥Γ) * p * (e : ↥Γ)⁻¹ * p⁻¹ =
          ((e : ↥Γ) * p) * (((e : ↥Γ) * p)⁻¹ * (p * e))⁻¹ * ((e : ↥Γ) * p)⁻¹ := by group
      rw [hconj]
      exact hZpn.conj_mem _ (Zp.inv_mem h1) _
    have hcomm := commute_of_conj_mem_center (P := P) (hEsq _ e.2) hxP
    have hY : Subgroup.zpowers (e : ↥Γ) ≤ Subgroup.centralizer (P : Set ↥Γ) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.mpr fun p hp => (hcomm p hp).symm
    have he1 : (e : ↥Γ) = 1 := by
      by_contra hne
      have hord : orderOf (e : ↥Γ) = 2 :=
        orderOf_eq_prime (by rw [sq]; exact hEsq _ e.2) hne
      have hY2 : IsPGroup 2 (Subgroup.zpowers (e : ↥Γ)) := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, hord, pow_one]
      have hbot := eq_bot_of_le_centralizer hO2' (P := P)
        (CFSG.IsExtraspecial.center_order_p 3 ↥P) hidx hY2 hY
      have : (e : ↥Γ) ∈ Subgroup.zpowers (e : ↥Γ) := Subgroup.mem_zpowers _
      rw [hbot, Subgroup.mem_bot] at this
      exact hne this
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, he1, map_one]

end Concl3

end CFSG.Quasithin.H13.L14324
