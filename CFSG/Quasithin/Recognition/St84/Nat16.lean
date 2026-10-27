module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.M3

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open Certificates.A5GL42 (Mat4 fixSet klein)
open scoped commutatorElement Matrix

theorem eq_sixteen_of_dvd_sixteen_of_modEq_one {n : ℕ} (hdvd : n ∣ 16) (hgt : 1 < n)
    (hmod : n ≡ 1 [MOD 5]) : n = 16 := by
  have hdvd' : n ∣ 2 ^ 4 := by
    norm_num at hdvd ⊢
    exact hdvd
  have hmod' : n % 5 = 1 % 5 := hmod
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd' with ⟨k, hk4, hkEq⟩
  interval_cases k
  · rw [hkEq] at hgt
    norm_num at hgt
  · exfalso
    rw [hkEq] at hmod'
    norm_num at hmod'
  · exfalso
    rw [hkEq] at hmod'
    norm_num at hmod'
  · exfalso
    rw [hkEq] at hmod'
    norm_num at hmod'
  · rw [hkEq]
    norm_num

@[instance_reducible]
noncomputable def conjActOn {G : Type*} [Group G] (X W : Subgroup G)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) : MulDistribMulAction X W :=
  MulDistribMulAction.compHom W (W.normalizerMonoidHom.comp (Subgroup.inclusion hXW))

theorem conjActOn_smul_coe {G : Type*} [Group G] {X W : Subgroup G}
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) (g : X) (w : W) :
    (letI : MulDistribMulAction X W := conjActOn X W hXW
     (((g • w : W)) : G)) = (g : G) * (w : G) * (g : G)⁻¹ := by
  change ((MulAction.compHom W
    (W.normalizerMonoidHom.comp (Subgroup.inclusion hXW))).smul g w : G) = _
  exact Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion hXW g) w

theorem isElemAbelian_of_card_eq_sixteen {G : Type*} [Group G] {Q : Subgroup G} [Finite Q]
    (hQ : Nat.card Q = 16) {x : G} (hxQ : x ∈ Subgroup.normalizer (Q : Set G))
    (hx5 : orderOf x = 5) (hnt : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) :
    IsElemAbelian 2 Q ∧ ∀ q ∈ Q, x * q * x⁻¹ = q → q = 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Nontrivial Q :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 4) (by rw [hQ]; norm_num)
  let X : Subgroup G := Subgroup.zpowers x
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hxQ
  have hX5 : Nat.card X = 5 := by rw [Nat.card_zpowers, hx5]
  have hXp : IsPGroup 5 X := IsPGroup.of_card (n := 1) (by rw [hX5]; norm_num)
  let gX : X := ⟨x, Subgroup.mem_zpowers x⟩
  let Cq : Subgroup Q := (Subgroup.centralizer ({x} : Set G)).subgroupOf Q
  let _ : MulDistribMulAction X Q := conjActOn X Q hXQ
  have hfixed_eq : MulAction.fixedPoints X Q = (Cq : Set Q) := by
    ext q
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      have hg : gX • q = q := h gX
      have hcoe := congrArg Subtype.val hg
      rw [conjActOn_smul_coe hXQ gX q] at hcoe
      have hcomm : x * (q : G) = (q : G) * x := by
        calc x * (q : G) = (x * (q : G) * x⁻¹) * x := by group
          _ = (q : G) * x := by rw [hcoe]
      change (q : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hcomm
    · intro hq
      have hqC : (q : G) ∈ Subgroup.centralizer ({x} : Set G) := hq
      have hcomm : x * (q : G) = (q : G) * x :=
        Subgroup.mem_centralizer_iff.mp hqC x (Set.mem_singleton x)
      have hgen : gX • q = q := by
        apply Subtype.ext
        rw [conjActOn_smul_coe hXQ gX q]
        calc x * (q : G) * x⁻¹ = (x * (q : G)) * x⁻¹ := rfl
          _ = ((q : G) * x) * x⁻¹ := by rw [hcomm]
          _ = (q : G) := by group
      have hs : q ∈ MulAction.fixedBy Q gX := hgen
      intro s
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp s.2
      have hsk : s = gX ^ k := Subtype.ext (by simpa [gX] using hk.symm)
      rw [hsk]
      exact MulAction.mem_fixedBy_zpow hs k
  have hcong := hXp.card_modEq_card_fixedPoints Q
  rw [hfixed_eq, hQ] at hcong
  simp only [SetLike.coe_sort_coe] at hcong
  have hcardC : Nat.card Cq ≡ 1 [MOD 5] :=
    hcong.symm.trans (by norm_num)
  have hdvdC : Nat.card Cq ∣ 16 := by
    rw [← hQ]
    exact Subgroup.card_subgroup_dvd_card Cq
  have hne16 : Nat.card Cq ≠ 16 := by
    intro h16
    have htop : Cq = ⊤ := Subgroup.eq_top_of_card_eq (H := Cq) (by rw [h16, hQ])
    obtain ⟨q, hq, hqne⟩ := hnt
    have hqC : (⟨q, hq⟩ : Q) ∈ Cq := by
      rw [htop]
      exact Subgroup.mem_top _
    have hcomm : x * q = q * x := by
      have hqC' : (q : G) ∈ Subgroup.centralizer ({x} : Set G) := hqC
      exact Subgroup.mem_centralizer_iff.mp hqC' x (Set.mem_singleton x)
    have hconj : x * q * x⁻¹ = q := by
      calc x * q * x⁻¹ = (q * x) * x⁻¹ := by rw [hcomm]
        _ = q := by group
    exact hqne hconj
  have hCcard : Nat.card Cq = 1 := by
    by_contra hne1
    have hgt : 1 < Nat.card Cq := by
      have hpos : 0 < Nat.card Cq := Nat.card_pos
      omega
    exact hne16 (eq_sixteen_of_dvd_sixteen_of_modEq_one hdvdC hgt hcardC)
  have hCbot : Cq = ⊥ := Cq.eq_bot_of_card_eq hCcard
  let Z : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  have hZle : Z ≤ Q := Subgroup.map_subtype_le _
  have hZcard : Nat.card Z = Nat.card (Subgroup.center ↥Q) :=
    Subgroup.card_map_of_injective Q.subtype_injective
  have hZgt1 : 1 < Nat.card Z := by
    rw [hZcard]
    rw [Finite.one_lt_card_iff_nontrivial]
    exact hQp.center_nontrivial
  have hxZ : x ∈ Subgroup.normalizer (Z : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (K := Subgroup.center ↥Q) hxQ
  have hXZ : X ≤ Subgroup.normalizer (Z : Set G) := Subgroup.zpowers_le.mpr hxZ
  haveI : Finite Z := Finite.of_injective
    (fun z : Z => (⟨(z : G), hZle z.2⟩ : Q))
    (fun a b h => Subtype.ext (by simpa using congrArg (fun q : Q => (q : G)) h))
  let _ : MulDistribMulAction X Z := conjActOn X Z hXZ
  have hfixZ : MulAction.fixedPoints X Z = {1} := by
    ext z
    constructor
    · intro hz
      have hzgen : gX • z = z := hz gX
      have hzconj : x * (z : G) * x⁻¹ = (z : G) := by
        have hcoe := congrArg Subtype.val hzgen
        rw [conjActOn_smul_coe hXZ gX z] at hcoe
        simpa [gX] using hcoe
      have hzQ : (z : G) ∈ Q := hZle z.2
      have hzC : (⟨(z : G), hzQ⟩ : Q) ∈ Cq := by
        change (z : G) ∈ Subgroup.centralizer ({x} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        calc x * (z : G) = (x * (z : G) * x⁻¹) * x := by group
          _ = (z : G) * x := by rw [hzconj]
      have hz1 : (⟨(z : G), hzQ⟩ : Q) = 1 := by
        have := hCbot ▸ hzC
        simpa using this
      exact Subtype.ext (by simpa using congrArg (fun q : Q => (q : G)) hz1)
    · rintro rfl
      simp
  have hcongZ := hXp.card_modEq_card_fixedPoints Z
  have hfixZcard : Nat.card (MulAction.fixedPoints X Z) = 1 := by
    rw [hfixZ]
    exact Nat.card_unique
  rw [hfixZcard] at hcongZ
  have hcardZ : Nat.card Z ≡ 1 [MOD 5] := hcongZ
  have hdvdZ : Nat.card Z ∣ 16 := by
    rw [← hQ]
    exact Subgroup.card_dvd_of_le hZle
  have hZcard16 : Nat.card Z = 16 :=
    eq_sixteen_of_dvd_sixteen_of_modEq_one hdvdZ hZgt1 hcardZ
  have hZeq : Z = Q := Subgroup.eq_of_le_of_card_ge hZle (by rw [hZcard16, hQ])
  have hcenter_top : Subgroup.center ↥Q = ⊤ := by
    ext q
    constructor
    · intro _
      exact Subgroup.mem_top _
    · intro _
      have hqZ : (q : G) ∈ Z := by
        rw [hZeq]
        exact q.2
      obtain ⟨z, hz, hzq⟩ := Subgroup.mem_map.mp hqZ
      simpa [show z = q from Subtype.ext hzq] using hz
  have hQcomm : IsMulCommutative ↥Q := (Subgroup.center_eq_top_iff).mp hcenter_top
  let Ω : Subgroup G :=
    { carrier := {q | q ∈ Q ∧ q ^ 2 = 1}
      one_mem' := ⟨Q.one_mem, one_pow 2⟩
      mul_mem' := by
        intro a b ha hb
        refine ⟨Q.mul_mem ha.1 hb.1, ?_⟩
        have hcomm : Commute a b := by
          have h := hQcomm.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩
          exact congrArg Subtype.val h
        rw [hcomm.mul_pow, ha.2, hb.2, one_mul]
      inv_mem' := by
        intro a ha
        exact ⟨Q.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩle : Ω ≤ Q := fun _ h => h.1
  haveI : Finite Ω := Finite.of_injective
    (fun z : Ω => (⟨(z : G), hΩle z.2⟩ : Q))
    (fun a b h => Subtype.ext (by simpa using congrArg (fun q : Q => (q : G)) h))
  have hΩne1 : Nat.card Ω ≠ 1 := by
    intro h1
    have hbot : Ω = ⊥ := Ω.eq_bot_of_card_eq h1
    have h2dvd : 2 ∣ Nat.card ↥Q := by rw [hQ]; norm_num
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have hq2 : (q : G) ^ 2 = 1 := by
      simpa [hq] using congrArg Subtype.val (pow_orderOf_eq_one q)
    have hqne : (q : G) ≠ 1 := by
      intro hq1
      have h1' : orderOf (q : G) = 1 := by rw [hq1, orderOf_one]
      rw [Subgroup.orderOf_coe] at h1'
      omega
    have hqΩ : (q : G) ∈ Ω := ⟨q.2, hq2⟩
    rw [hbot] at hqΩ
    exact hqne (Subgroup.mem_bot.mp hqΩ)
  have hΩgt1 : 1 < Nat.card Ω := by
    have hpos : 0 < Nat.card Ω := Nat.card_pos
    omega
  have hxΩ : x ∈ Subgroup.normalizer (Ω : Set G) := by
    have hconj : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∀ a ∈ Ω, g * a * g⁻¹ ∈ Ω := by
      intro g hg a ha
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg a).mp ha.1, ?_⟩
      calc (g * a * g⁻¹) ^ 2 = g * a ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [ha.2]; group
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hconj x hxQ a ha
    · intro ha
      have h := hconj x⁻¹ (Subgroup.inv_mem _ hxQ) (x * a * x⁻¹) ha
      have h2 : x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a := by group
      rwa [h2] at h
  have hXΩ : X ≤ Subgroup.normalizer (Ω : Set G) := Subgroup.zpowers_le.mpr hxΩ
  let _ : MulDistribMulAction X Ω := conjActOn X Ω hXΩ
  have hfixΩ : MulAction.fixedPoints X Ω = {1} := by
    ext z
    constructor
    · intro hz
      have hzgen : gX • z = z := hz gX
      have hzconj : x * (z : G) * x⁻¹ = (z : G) := by
        have hcoe := congrArg Subtype.val hzgen
        rw [conjActOn_smul_coe hXΩ gX z] at hcoe
        simpa [gX] using hcoe
      have hzQ : (z : G) ∈ Q := hΩle z.2
      have hzC : (⟨(z : G), hzQ⟩ : Q) ∈ Cq := by
        change (z : G) ∈ Subgroup.centralizer ({x} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        calc x * (z : G) = (x * (z : G) * x⁻¹) * x := by group
          _ = (z : G) * x := by rw [hzconj]
      have hz1 : (⟨(z : G), hzQ⟩ : Q) = 1 := by
        have := hCbot ▸ hzC
        simpa using this
      exact Subtype.ext (by simpa using congrArg (fun q : Q => (q : G)) hz1)
    · rintro rfl
      simp
  have hcongΩ := hXp.card_modEq_card_fixedPoints Ω
  have hfixΩcard : Nat.card (MulAction.fixedPoints X Ω) = 1 := by
    rw [hfixΩ]
    exact Nat.card_unique
  rw [hfixΩcard] at hcongΩ
  have hcardΩ : Nat.card Ω ≡ 1 [MOD 5] := hcongΩ
  have hdvdΩ : Nat.card Ω ∣ 16 := by
    rw [← hQ]
    exact Subgroup.card_dvd_of_le hΩle
  have hΩcard16 : Nat.card Ω = 16 :=
    eq_sixteen_of_dvd_sixteen_of_modEq_one hdvdΩ hΩgt1 hcardΩ
  have hΩeq : Ω = Q := Subgroup.eq_of_le_of_card_ge hΩle (by rw [hΩcard16, hQ])
  refine ⟨⟨hQcomm, ?_⟩, ?_⟩
  · intro q hq
    have hqΩ : q ∈ Ω := hΩeq ▸ hq
    exact hqΩ.2
  · intro q hq hqconj
    have hqC : (⟨q, hq⟩ : Q) ∈ Cq := by
      change q ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      calc x * q = (x * q * x⁻¹) * x := by group
        _ = q * x := by rw [hqconj]
    have hq1 : (⟨q, hq⟩ : Q) = 1 := by
      have := hCbot ▸ hqC
      simpa using this
    exact congrArg Subtype.val hq1

theorem exists_order_five_not_centralizing_pCoreOf {G : Type} [Group G] [Finite G]
    {P L : Subgroup G} (hLP : L ≤ P) (hchar : CharTwo P)
    (hquot : IsL2Quot 2 (oTwoQuot ↥L)) :
    ∃ x ∈ L, orderOf x = 5 ∧ ∃ q ∈ pCoreOf 2 P, x * q * x⁻¹ ≠ q := by
  have h5dvd : 5 ∣ Nat.card ↥L := by
    obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hquot
    have h60 : Nat.card (oTwoQuot ↥L) = 60 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.QuasithinUnique.A5.Delta5.a5_card
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L), h60]
    exact dvd_mul_of_dvd_left (by norm_num : 5 ∣ 60) _
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  have hxL : (x : G) ∈ L := x.2
  have hx5 : orderOf (x : G) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hxP : (x : G) ∈ P := hLP hxL
  have hxNQ : (x : G) ∈ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hxP
  by_contra hcon
  push Not at hcon
  have hxcent : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    calc q * (x : G) = (x : G) * q * (x : G)⁻¹ * (x : G) := by
          rw [hcon (x : G) hxL hx5 q hq]
      _ = (x : G) * q := by group
  have hxQ : (x : G) ∈ pCoreOf 2 P := hchar ⟨hxP, hxcent⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQp) ⟨(x : G), hxQ⟩
  rw [Subgroup.orderOf_mk, hx5] at hk
  rcases k with _ | k
  · simp at hk
  · have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    rw [← hk] at h2
    norm_num at h2

theorem a5Pre_pCoreOf {G : Type} [Group G] [Finite G] {P L : Subgroup G}
    (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hchar : CharTwo P)
    (hquot : IsL2Quot 2 (oTwoQuot ↥L)) (hcard : Nat.card (pCoreOf 2 P) = 16) :
    A5Pre P L (pCoreOf 2 P) ⊥ := by
  obtain ⟨x, hxL, hx5, q, hqQ, hqne⟩ :=
    exists_order_five_not_centralizing_pCoreOf hLP hchar hquot
  have hxQ : x ∈ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P (hLP hxL)
  have hElem := isElemAbelian_of_card_eq_sixteen hcard hxQ hx5 ⟨q, hqQ, hqne⟩
  have hcomm : ∀ a ∈ pCoreOf 2 P, ∀ b ∈ pCoreOf 2 P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hElem.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm1 : ∀ a ∈ pCoreOf 2 P, ∀ b ∈ pCoreOf 2 P, ⁅a, b⁆ = 1 := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a ha b hb)
  refine ⟨hLP, hPL, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P, ?_, ?_, ?_, ?_,
    hquot, ?_⟩
  · intro p _
    rw [Subgroup.mem_normalizer_iff]
    intro a
    simp
  · refine ⟨bot_le, ?_, ?_⟩
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot]
      exact hcomm1 a ha b hb
    · intro e he
      rw [Subgroup.mem_bot]
      exact hElem.1.2 e he
  · rw [Subgroup.relIndex_bot_left]
    exact hcard
  · intro q' hq' e he
    rw [Subgroup.mem_bot]
    exact hcomm1 q' hq' e he
  · refine ⟨x, hxL, q, hqQ, ?_⟩
    rw [Subgroup.mem_bot]
    intro h1
    apply hqne
    have hcomm' : x * q = q * x := commutatorElement_eq_one_iff_mul_comm.mp h1
    calc x * q * x⁻¹ = (q * x) * x⁻¹ := by rw [hcomm']
      _ = q := by group

theorem img_inf_centralizer_eq_fixSet {G : Type} [Group G] [Finite G] {P L E : Subgroup G}
    {H : Finset Mat4} (h : A5Pre P L E ⊥) (M : A5Model P L E ⊥ H) {T : Subgroup G}
    (hTP : T ≤ P) (sd : SylowData M T) :
    img M.F (E ⊓ Subgroup.centralizer (T : Set G)) = fixSet (klein sd.x sd.y) := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, rfl⟩ := mem_img.mp hv
    obtain ⟨heE, heC⟩ := Subgroup.mem_inf.mp he
    refine fixes_of_comm_mem h hTP sd heE ?_
    intro t ht
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp heC t ht).symm
  · intro hv
    obtain ⟨e, he⟩ := M.F.surj (Multiplicative.ofAdd v)
    refine mem_img.mpr ⟨e, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨e.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hv' : Multiplicative.toAdd (M.F.φ e) ∈ fixSet (klein sd.x sd.y) := by
        rw [he]
        exact hv
      have hcomm := comm_mem_of_fixes h hTP sd e.2 hv' ht
      exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hcomm)).symm
    · simpa using congrArg Multiplicative.toAdd he

theorem card_inf_centralizer_eq_fixSet_card {G : Type} [Group G] [Finite G]
    {P L E : Subgroup G} {H : Finset Mat4} (h : A5Pre P L E ⊥)
    (M : A5Model P L E ⊥ H) {T : Subgroup G} (hTP : T ≤ P) (sd : SylowData M T) :
    Nat.card ↥(E ⊓ Subgroup.centralizer (T : Set G)) =
      (fixSet (klein sd.x sd.y)).card := by
  have hC : E ⊓ Subgroup.centralizer (T : Set G) ≤ E := inf_le_left
  rw [← Subgroup.relIndex_bot_left, relIndex_eq_card_img M.F bot_le hC,
    img_inf_centralizer_eq_fixSet h M hTP sd]

theorem natSec_iff_card_centralizer {G : Type} [Group G]
    [Finite G] {P L E : Subgroup G} (h : A5Pre P L E ⊥) {T : Subgroup G}
    (hT : IsSylowTwoOf T L) :
    (NatSec L ⊥ E ↔ Nat.card ↥(E ⊓ Subgroup.centralizer (T : Set G)) = 4) ∧
      (¬ NatSec L ⊥ E ↔ Nat.card ↥(E ⊓ Subgroup.centralizer (T : Set G)) = 2) := by
  have hF := a5Facts
  rcases h.exists_model' with ⟨hnat, ⟨M⟩⟩ | ⟨hnot, ⟨M⟩⟩
  · obtain ⟨sd⟩ := M.exists_sylowData hF.groupN h hT
    have h4 : Nat.card ↥(E ⊓ Subgroup.centralizer (T : Set G)) = 4 := by
      rw [card_inf_centralizer_eq_fixSet_card h M (hT.1.trans h.le) sd]
      obtain ⟨-, -, hc, hfix, -⟩ := (hF.kleinN _ sd.mem_kleinGroups).1
      rw [← hfix]
      exact hc
    refine ⟨⟨fun _ => h4, fun _ => hnat⟩, ?_⟩
    constructor
    · intro hn
      exact absurd hnat hn
    · intro h2
      omega
  · obtain ⟨sd⟩ := M.exists_sylowData hF.groupO h hT
    have h2 : Nat.card ↥(E ⊓ Subgroup.centralizer (T : Set G)) = 2 := by
      rw [card_inf_centralizer_eq_fixSet_card h M (hT.1.trans h.le) sd]
      obtain ⟨-, -, -, -, -, hc, hfix⟩ := (hF.kleinO _ sd.mem_kleinGroups).1
      rw [← hfix]
      exact hc
    refine ⟨?_, ⟨fun _ => h2, fun _ => hnot⟩⟩
    constructor
    · intro hnat
      exact absurd hnat hnot
    · intro h4
      omega

theorem natSec_of_four_le_card_centralizer {G : Type}
    [Group G] [Finite G] {P L T : Subgroup G} (hLP : L ≤ P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hchar : CharTwo P)
    (hquot : IsL2Quot 2 (oTwoQuot ↥L)) (hcard : Nat.card (pCoreOf 2 P) = 16)
    (hT : IsSylowTwoOf T L)
    (hC : 4 ≤ Nat.card ↥(pCoreOf 2 P ⊓ Subgroup.centralizer (T : Set G))) :
    IsElemAbelian 2 (pCoreOf 2 P) ∧ NatSec L ⊥ (pCoreOf 2 P) := by
  obtain ⟨x, hxL, hx5, q, hqQ, hqne⟩ :=
    exists_order_five_not_centralizing_pCoreOf hLP hchar hquot
  have hxQ : x ∈ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P (hLP hxL)
  have hElem := isElemAbelian_of_card_eq_sixteen hcard hxQ hx5 ⟨q, hqQ, hqne⟩
  have hpre := a5Pre_pCoreOf hLP hPL hchar hquot hcard
  have hNat : NatSec L ⊥ (pCoreOf 2 P) := by
    by_contra hnot
    have h2 : Nat.card ↥(pCoreOf 2 P ⊓ Subgroup.centralizer (T : Set G)) = 2 :=
      (natSec_iff_card_centralizer hpre hT).2.mp hnot
    omega
  exact ⟨hElem.1, hNat⟩

end CFSG.Quasithin.St84
