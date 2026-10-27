module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceTypes
public import CFSG.Quasithin.EmptyFaithful.S152N2Frob
public import CFSG.Quasithin.MS93.ASGroup

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open CFSG.Quasithin.MS93 (oddGen)

variable {G : Type} [Group G] [Finite G]

private theorem two_pow_mul_odd_inj {a b i j : ℕ} (hi : Odd i) (hj : Odd j)
    (h : 2 ^ a * i = 2 ^ b * j) : a = b ∧ i = j := by
  have key : ∀ {a b i j : ℕ}, Odd j → 2 ^ a * i = 2 ^ b * j → a ≤ b := by
    intro a b i j hj h
    have hdvd : 2 ^ a ∣ 2 ^ b * j := h ▸ dvd_mul_right _ _
    have hcop : Nat.Coprime (2 ^ a) j := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hj)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  have hab : a = b := le_antisymm (key hj h) (key hi h.symm)
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

private theorem exists_two_pow_mul_prime {n : ℕ} (hn : n = 6 ∨ n = 10 ∨ n = 20) :
    ∃ e p : ℕ, p.Prime ∧ p ≠ 2 ∧ 2 ^ e < p ∧ n = 2 ^ e * p := by
  rcases hn with rfl | rfl | rfl
  · exact ⟨1, 3, Nat.prime_three, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1, 5, Nat.prime_five, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 5, Nat.prime_five, by norm_num, by norm_num, by norm_num⟩

private theorem exists_card_eq_two_pow_mul_card_oTwoQuot (L : Subgroup G) :
    ∃ a : ℕ, Nat.card ↥L = 2 ^ a * Nat.card (oTwoQuot ↥L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥L)).exists_card_eq
  exact ⟨a, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L), ha, mul_comm]⟩

theorem relIndex_card_of_isSylowTwoOf {T H : Subgroup G} (hT : IsSylowTwoOf T H) {a m : ℕ}
    (hm : Odd m) (hH : Nat.card ↥H = 2 ^ a * m) : T.relIndex H = m ∧ Nat.card ↥T = 2 ^ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hT.2.1.exists_card_eq
  have hmul := Subgroup.relIndex_mul_card T H
  rw [inf_eq_left.mpr hT.1, hj, hH, mul_comm] at hmul
  have hodd : Odd (T.relIndex H) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (F7.isSylowTwoOf_odd_relIndex hT))
  obtain ⟨hja, hrm⟩ := two_pow_mul_odd_inj hodd hm hmul
  exact ⟨hrm, hj.trans (by rw [hja])⟩

theorem isCyclic_of_isPGroup_of_card_eq_two_mul {Q : Type*} [Group Q] [Finite Q] {m : ℕ}
    (hm : Odd m) (hQ : Nat.card Q = 2 * m) (X : Subgroup Q) (hX : IsPGroup 2 ↥X) :
    IsCyclic ↥X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hdvd : Nat.card ↥X ∣ 2 * m := hQ ▸ Subgroup.card_subgroup_dvd_card X
  have hcop : Nat.Coprime (Nat.card ↥X) m :=
    hk ▸ Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  exact isCyclic_of_card_dvd_prime (p := 2) (hcop.dvd_of_dvd_mul_right hdvd)

private theorem forall_isCyclic_of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : ∀ X : Subgroup Q', IsPGroup 2 ↥X → IsCyclic ↥X) :
    ∀ X : Subgroup Q, IsPGroup 2 ↥X → IsCyclic ↥X := by
  intro X hX
  let f : ↥X ≃* ↥(X.map e.toMonoidHom) := X.equivMapOfInjective e.toMonoidHom e.injective
  exact f.isCyclic.mpr (h _ (hX.of_equiv f))

private theorem mem_of_forall_commute {X : Type*} [Group X] {N K : Subgroup X} [N.Normal]
    (hNK : N.IsComplement' K) (hcomm : ∀ n ∈ N, ∀ m ∈ N, n * m = m * n)
    (hf : ∀ k ∈ K, (∀ n ∈ N, k * n = n * k) → k = 1) {x : X} (hx : ∀ n ∈ N, x * n = n * x) :
    x ∈ N := by
  have hxs : x ∈ ((K ⊔ N : Subgroup X) : Set X) := by
    rw [sup_comm, hNK.isCompl.sup_eq_top]
    exact Subgroup.mem_top x
  rw [Subgroup.mul_normal] at hxs
  obtain ⟨k, hkK, n, hnN, rfl⟩ := hxs
  have hk1 : k = 1 := hf k hkK fun m hm => by
    calc k * m = (k * n) * (n⁻¹ * m) := by group
      _ = (k * n) * (m * n⁻¹) := by rw [hcomm _ (N.inv_mem hnN) m hm]
      _ = ((k * n) * m) * n⁻¹ := by group
      _ = (m * (k * n)) * n⁻¹ := by rw [hx m hm]
      _ = m * k := by group
  rw [hk1]
  simpa using hnN

theorem isCyclic_of_isPGroup_of_selfCentralizing {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Nat.card ↥N = 5) (hc : ∀ x : X, (∀ n ∈ N, x * n = n * x) → x ∈ N) (Y : Subgroup X)
    (hY : IsPGroup 2 ↥Y) : IsCyclic ↥Y := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : IsCyclic ↥N := isCyclic_of_prime_card hN
  have hinj : Function.Injective ((MulAut.conjNormal (H := N)).comp Y.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyN : (y : X) ∈ N := hc y fun n hn => by
      have h1 := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : ↥N) : X)) hy
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply] at h1
      calc (y : X) * n = (y * n * (y : X)⁻¹) * y := by group
        _ = n * y := by rw [h1]
    obtain ⟨k, hk⟩ := hY y
    have hk' : (y : X) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf (⟨y, hyN⟩ : ↥N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hk')
    have hord5 : orderOf (⟨y, hyN⟩ : ↥N) ∣ 5 := hN ▸ orderOf_dvd_natCard _
    have h1 : orderOf (⟨y, hyN⟩ : ↥N) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 5)) hord hord5
    exact Subtype.ext (by simpa using congrArg Subtype.val (orderOf_eq_one_iff.mp h1))
  have hcyc : IsCyclic (ZMod (Nat.card ↥N))ˣ := by
    rw [hN]
    exact ZMod.isCyclic_units_prime Nat.prime_five
  haveI : IsCyclic (MulAut ↥N) := (IsCyclic.mulAutMulEquiv ↥N).isCyclic.mpr hcyc
  exact isCyclic_of_injective _ hinj

theorem isCyclic_of_isFrob20 {X : Type} [Group X] (hX : S152N2.IsFrob20 X) (Y : Subgroup X)
    (hY : IsPGroup 2 ↥Y) : IsCyclic ↥Y := by
  obtain ⟨N, K, hNn, hNK, hN, -, hf⟩ := hX
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : IsCyclic ↥N := isCyclic_of_prime_card hN
  haveI : IsMulCommutative ↥N := inferInstance
  exact isCyclic_of_isPGroup_of_selfCentralizing hN
    (fun x hx => mem_of_forall_commute hNK (fun n hn m hm => setLike_mul_comm (s := N) hn hm) hf hx)
    Y hY

theorem card_oTwoQuot_of_vS3 {L : Subgroup G} (h : VS3 L) : Nat.card (oTwoQuot ↥L) = 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm]
  simp [Nat.factorial]

theorem card_oTwoQuot_of_vFD {L : Subgroup G} (h : VFD L) :
    Nat.card (oTwoQuot ↥L) = 10 ∨ Nat.card (oTwoQuot ↥L) = 20 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  · right
    rw [Nat.card_congr e.toEquiv]
    exact card_sz_zero_eq_twenty

theorem isCyclic_of_vS3 {L : Subgroup G} (h : VS3 L) :
    ∀ X : Subgroup (oTwoQuot ↥L), IsPGroup 2 ↥X → IsCyclic ↥X :=
  isCyclic_of_isPGroup_of_card_eq_two_mul (m := 3) (by decide) (by rw [card_oTwoQuot_of_vS3 h])

theorem isCyclic_of_vFD {L : Subgroup G} (h : VFD L) :
    ∀ X : Subgroup (oTwoQuot ↥L), IsPGroup 2 ↥X → IsCyclic ↥X := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact isCyclic_of_isPGroup_of_card_eq_two_mul (m := 5) (by decide)
      (by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card])
  · haveI : Finite ↥(Sz 0) := Nat.finite_of_card_ne_zero (by rw [card_sz_zero_eq_twenty]; norm_num)
    exact forall_isCyclic_of_mulEquiv e fun Y hY => isCyclic_of_isFrob20
      (S152N2.isFrob20_of_pCore card_sz_zero_eq_twenty pCore_two_sz_zero_eq_bot) Y hY

variable {L₁ L₂ S : Subgroup G}

theorem relIndex_borelOf_eq_of_card (h : Hyp111R L₁ L₂ S) {e p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : Nat.card (oTwoQuot ↥L₁) = 2 ^ e * p) :
    (borelOf L₁ S).relIndex L₁ = p ∧ IsPGroup 2 ↥(borelOf L₁ S) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨a, ha⟩ := exists_card_eq_two_pow_mul_card_oTwoQuot L₁
  rw [hc, ← mul_assoc, ← pow_add] at ha
  have hS := relIndex_card_of_isSylowTwoOf h.hyp.h1.sylow hpodd ha
  have hdvd : (borelOf L₁ S).relIndex L₁ ∣ p :=
    hS.1 ▸ Subgroup.relIndex_dvd_of_le_left L₁ (F1.sylow_le_borelOf L₁ S)
  have hne : (borelOf L₁ S).relIndex L₁ ≠ 1 := fun h1 =>
    (F1.lt_borelOf h).not_ge (Subgroup.relIndex_eq_one.mp h1)
  have hrel : (borelOf L₁ S).relIndex L₁ = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hne
  refine ⟨hrel, IsPGroup.of_card (n := a + e) ?_⟩
  have hmul := Subgroup.relIndex_mul_card (borelOf L₁ S) L₁
  rw [inf_eq_left.mpr (F1.borelOf_le L₁ S), hrel, ha] at hmul
  exact Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_comm _ _))

theorem relIndex_borelOf_eq_three (h : Hyp111R L₁ L₂ S) (hc : Nat.card (oTwoQuot ↥L₁) = 6) :
    (borelOf L₁ S).relIndex L₁ = 3 :=
  (relIndex_borelOf_eq_of_card h (e := 1) Nat.prime_three (by norm_num)
    (hc.trans (by norm_num))).1

theorem relIndex_borelOf_eq_five (h : Hyp111R L₁ L₂ S)
    (hc : Nat.card (oTwoQuot ↥L₁) = 10 ∨ Nat.card (oTwoQuot ↥L₁) = 20) :
    (borelOf L₁ S).relIndex L₁ = 5 := by
  rcases hc with hc | hc
  · exact (relIndex_borelOf_eq_of_card h (e := 1) Nat.prime_five (by norm_num)
      (hc.trans (by norm_num))).1
  · exact (relIndex_borelOf_eq_of_card h (e := 2) Nat.prime_five (by norm_num)
      (hc.trans (by norm_num))).1

private theorem card_sylow_of_card {Q : Type*} [Group Q] [Finite Q] {e p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQ : Nat.card Q = 2 ^ e * p) (P : Sylow p Q) :
    Nat.card ↥(P : Subgroup Q) = p ∧ (P : Subgroup Q).index = 2 ^ e := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop2 : Nat.Coprime (2 ^ e) p :=
    Nat.Coprime.pow_left e ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hmul := (P : Subgroup Q).card_mul_index
  have hdvd : p ^ n ∣ p :=
    (Nat.Coprime.pow_left n hcop2.symm).dvd_of_dvd_mul_left
      (hQ ▸ hn ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup Q))
  have hle : n ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (by simpa using hdvd)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with rfl | rfl
  · rw [hn, hQ, pow_zero, one_mul] at hmul
    exact absurd (by rw [hmul]; exact dvd_mul_left _ _) P.not_dvd_index
  · rw [hn, hQ, pow_one] at hmul
    exact ⟨by rw [hn, pow_one], Nat.eq_of_mul_eq_mul_left hp.pos (by rw [hmul, mul_comm])⟩

private theorem subsingleton_sylow_of_card {Q : Type*} [Group Q] [Finite Q] {e p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlt : 2 ^ e < p) (hQ : Nat.card Q = 2 ^ e * p) : Subsingleton (Sylow p Q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p Q) := inferInstance
  have h1 := card_sylow_modEq_one p Q
  have h2 := P.card_dvd_index
  rw [(card_sylow_of_card hp hp2 hQ P).2] at h2
  have hle : Nat.card (Sylow p Q) ≤ 2 ^ e := Nat.le_of_dvd (by positivity) h2
  have hpos : 0 < Nat.card (Sylow p Q) := Nat.card_pos
  unfold Nat.ModEq at h1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hp.one_lt] at h1
  exact (Nat.card_eq_one_iff_unique.mp h1).1

theorem exists_subgroup_of_odd_order {Q : Type*} [Group Q] [Finite Q] {e p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlt : 2 ^ e < p) (hQ : Nat.card Q = 2 ^ e * p) :
    ∃ P : Subgroup Q, (∀ x ∈ P, x ^ p = 1) ∧ ∀ x : Q, Odd (orderOf x) → x ∈ P := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := subsingleton_sylow_of_card hp hp2 hlt hQ
  obtain ⟨P⟩ : Nonempty (Sylow p Q) := inferInstance
  refine ⟨P, fun x hx => ?_, fun x hx => ?_⟩
  · have h1 : orderOf (⟨x, hx⟩ : (P : Subgroup Q)) ∣ Nat.card (P : Subgroup Q) :=
      orderOf_dvd_natCard _
    rw [(card_sylow_of_card hp hp2 hQ P).1] at h1
    simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h1)
  · have hdvdQ : orderOf x ∣ 2 ^ e * p := hQ ▸ orderOf_dvd_natCard x
    have hcop : Nat.Coprime (orderOf x) (2 ^ e) :=
      Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hx)
    have hxp : orderOf x ∣ p := hcop.dvd_of_dvd_mul_left hdvdQ
    have hpg : IsPGroup p (Subgroup.zpowers x) := by
      rcases (Nat.dvd_prime hp).mp hxp with h1 | h1
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; simp)
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; simp)
    obtain ⟨R, hR⟩ := hpg.exists_le_sylow
    rw [Subsingleton.elim R P] at hR
    exact hR (Subgroup.mem_zpowers x)

theorem oddGen_le_map_comap {L : Subgroup G} {P : Subgroup (oTwoQuot ↥L)}
    (hP : ∀ x : oTwoQuot ↥L, Odd (orderOf x) → x ∈ P) :
    oddGen L ≤ (P.comap (QuotientGroup.mk' (pCore 2 ↥L))).map L.subtype := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, hodd⟩
  refine ⟨⟨x, hx⟩, hP _ ?_, rfl⟩
  refine Odd.of_dvd_nat (n := orderOf (⟨x, hx⟩ : ↥L)) ?_ (orderOf_map_dvd _ _)
  rwa [← Subgroup.orderOf_coe]

theorem oddGen_inf_borelOf_le (h : Hyp111R L₁ L₂ S)
    (hc : Nat.card (oTwoQuot ↥L₁) = 6 ∨ Nat.card (oTwoQuot ↥L₁) = 10 ∨
      Nat.card (oTwoQuot ↥L₁) = 20) :
    oddGen L₁ ⊓ borelOf L₁ S ≤ pCoreOf 2 L₁ := by
  obtain ⟨e, p, hp, hp2, hlt, hQ⟩ := exists_two_pow_mul_prime hc
  have hB2 := (relIndex_borelOf_eq_of_card h hp hp2 hQ).2
  obtain ⟨P, hP1, hP2⟩ := exists_subgroup_of_odd_order hp hp2 hlt hQ
  have hD := oddGen_le_map_comap (L := L₁) hP2
  rintro x ⟨hxD, hxB⟩
  obtain ⟨y, hyP, rfl⟩ := hD hxD
  obtain ⟨k, hk⟩ := hB2 ⟨y, hxB⟩
  have hyk : y ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hdvd2 : orderOf (QuotientGroup.mk' (pCore 2 ↥L₁) y) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hyk, map_one])
  have hdvdp : orderOf (QuotientGroup.mk' (pCore 2 ↥L₁) y) ∣ p :=
    orderOf_dvd_of_pow_eq_one (hP1 _ hyP)
  have h1 : orderOf (QuotientGroup.mk' (pCore 2 ↥L₁) y) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k
      ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)) hdvd2 hdvdp
  exact ⟨y, (QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp h1), rfl⟩

end CFSG.Quasithin.F112Crit

end
