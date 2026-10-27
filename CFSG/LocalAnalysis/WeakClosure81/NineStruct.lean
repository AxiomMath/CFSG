module

public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.CGT.Timmesfeld75
open CFSG.LieType.BorelTits Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace TwoPTwo

variable {K S X : Subgroup G} {p : ℕ}

private theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {x : G} {a b : ℕ}
    (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) (hab : a.Coprime b) : x ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab, Nat.cast_one] at h
  have e : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)


private theorem isPSolvable_of_isSolvable {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (hX : Group.IsSolvable X) : CFSG.HallHigman.IsPSolvable p X := by
  intro H _ T _ hs
  have := hX
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  change Nat.card (↥H ⧸ T) = p ∨ Nat.Coprime p (Nat.card (↥H ⧸ T))
  by_cases h : Nat.card (↥H ⧸ T) = p
  · exact Or.inl h
  · exact Or.inr ((Nat.coprime_primes hp hq).mpr fun hp' => h hp'.symm)

private theorem eq_bot_of_isPGroup_of_coprime_card {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {N : Subgroup G} (hN : IsPGroup p N) (hc : Nat.Coprime p (Nat.card N)) : N = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hN.exists_orderOf_eq_pow ⟨x, hx⟩
  have hxord : orderOf x = p ^ k := by
    rw [← Subgroup.orderOf_mk x hx, hk]
  have hcop : Nat.Coprime p (orderOf x) :=
    hc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hx)
  have hnot : ¬ p ∣ orderOf x := (hp.coprime_iff_not_dvd).mp hcop
  have hk0 : k = 0 := by
    by_contra hkne
    exact hnot (hxord ▸ dvd_pow_self p hkne)
  have hone : orderOf x = 1 := by rw [hxord, hk0, pow_zero]
  exact orderOf_eq_one_iff.mp hone

private theorem isSolvable_pCore_two (Q : Type*) [Group Q] [Finite Q] :
    Group.IsSolvable ↥(CFSG.pCore 2 Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 Q) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) 2).isNilpotent
  infer_instance

private theorem isSolvable_comap_mk' {Q : Type*} [Group Q] [Finite Q] {N : Subgroup Q}
    [N.Normal] (hN : Group.IsSolvable ↥N) {H : Subgroup (Q ⧸ N)}
    (hH : Group.IsSolvable ↥H) :
    Group.IsSolvable ↥(H.comap (QuotientGroup.mk' N)) := by
  have hNle : N ≤ H.comap (QuotientGroup.mk' N) := fun x hx => by
    have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [Subgroup.mem_comap, h1]
    exact one_mem _
  set g : H.comap (QuotientGroup.mk' N) →* H :=
    ((QuotientGroup.mk' N).comp (Subgroup.subtype _)).codRestrict H (fun x => x.2) with hg
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNle) g ?_
  intro x hx
  have h1 : QuotientGroup.mk' N (x : Q) = 1 := congrArg Subtype.val hx
  exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩

private theorem oTwoP_quotient_isPGroup {Q : Type*} [Group Q] [Finite Q] (p : ℕ)
    (h : E1.oTwoPTwo Q p = ⊤) : IsPGroup 2 (Q ⧸ E1.oTwoP Q p) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (E1.oTwoP Q p) y
  have hmem : q ∈ E1.oTwoPTwo Q p := by rw [h]; exact Subgroup.mem_top _
  have hq : QuotientGroup.mk' (E1.oTwoP Q p) q ∈
      CFSG.pCore 2 (Q ⧸ E1.oTwoP Q p) := Subgroup.mem_comap.mp hmem
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCore_isPGroup
    (G := Q ⧸ E1.oTwoP Q p) 2 ⟨_, hq⟩
  refine ⟨n, ?_⟩
  have hv := congrArg Subtype.val hn
  simpa [QuotientGroup.mk'_apply, Subgroup.coe_pow] using hv

private theorem pow_two_pow_mem_oTwoP {Q : Type*} [Group Q] [Finite Q] (p : ℕ)
    (h : E1.oTwoPTwo Q p = ⊤) :
    ∀ q : Q, ∃ n : ℕ, q ^ 2 ^ n ∈ E1.oTwoP Q p := by
  intro q
  obtain ⟨n, hn⟩ := oTwoP_quotient_isPGroup p h (QuotientGroup.mk' (E1.oTwoP Q p) q)
  refine ⟨n, ?_⟩
  rw [← QuotientGroup.eq_one_iff]
  simpa [QuotientGroup.mk'_apply] using hn

theorem pCoreOf_le_sylowTwo (h : TwoPTwo K S X p) : pCoreOf 2 K ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsSylowIn.le_of_normal h.sylowTwo (pCoreOf_le 2 K) ?_ (pCoreOf_isPGroup 2 K)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 K)).mpr
    (le_normalizer_pCoreOf 2 K)

theorem sylowP_inf_pCoreOf (h : TwoPTwo K S X p) : X ⊓ pCoreOf 2 K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  exact (IsPGroup.disjoint_of_ne p 2 h.odd X (pCoreOf 2 K)
    h.sylowP.isPGroup (pCoreOf_isPGroup 2 K)).eq_bot

theorem map_oTwoP_eq_sup (h : TwoPTwo K S X p) :
    (E1.oTwoP ↥K p).map K.subtype = pCoreOf 2 K ⊔ X := by
  let Q := ↥K
  let R0 : Subgroup Q := CFSG.pCore 2 Q
  let P0 : Subgroup Q := E1.oTwoP Q p
  let X0 : Subgroup Q := X.subgroupOf K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  have hR0P0 : R0 ≤ P0 := by
    intro x hx
    rw [show P0 = E1.oTwoP Q p from rfl, E1.oTwoP, Subgroup.mem_comap]
    have hx1 : QuotientGroup.mk' R0 x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact Subgroup.one_mem _
  have hpow : ∀ q : Q, ∃ n : ℕ, q ^ 2 ^ n ∈ P0 := by
    intro q
    have hpc : IsPGroup 2 ↥(CFSG.pCore 2 (Q ⧸ P0)) :=
      CFSG.LieType.BorelTits.pCore_isPGroup (G := Q ⧸ P0) 2
    have htop : E1.oTwoPTwo Q p = ⊤ := h.oTwoPTwo
    have hqmem : q ∈ E1.oTwoPTwo Q p := by
      rw [htop]
      exact Subgroup.mem_top _
    have hq : QuotientGroup.mk' P0 q ∈ CFSG.pCore 2 (Q ⧸ P0) :=
      Subgroup.mem_comap.mp hqmem
    obtain ⟨n, hn⟩ := hpc ⟨_, hq⟩
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.eq_one_iff (x := q ^ 2 ^ n)]
    have hv := congrArg Subtype.val hn
    simpa [QuotientGroup.mk'_apply, Subgroup.coe_pow] using hv
  have hX0P0 : X0 ≤ P0 := by
    intro q hq
    obtain ⟨n, hn⟩ := hpow q
    have hqX : IsPGroup p X0 := h.sylowP.isPGroup.comap_subtype
    obtain ⟨b, hb⟩ := hqX.exists_orderOf_eq_pow ⟨q, hq⟩
    have hbq : orderOf q = p ^ b := by
      rw [← Subgroup.orderOf_mk q hq, hb]
    have hcop : Nat.Coprime (2 ^ n) (orderOf q) := by
      rw [hbq]
      exact Nat.coprime_pow_primes n b Nat.prime_two h.prime h.odd.symm
    refine mem_of_pow_mem_of_coprime (G := Q) (H := P0) hn ?_ hcop
    rw [pow_orderOf_eq_one]
    exact P0.one_mem
  have hP0le : P0 ≤ X0 ⊔ R0 := by
    let mk := QuotientGroup.mk' R0
    let Sy : Sylow p (Q ⧸ R0) :=
      h.sylowP.toSylow.mapSurjective (QuotientGroup.mk'_surjective R0)
    have hbar : P0.map mk = CFSG.pCore p (Q ⧸ R0) := by
      show (E1.oTwoP Q p).map mk = _
      rw [E1.oTwoP]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R0) _
    haveI : (P0.map mk).Normal :=
      (E1.instNormalOTwoP (Q := Q) p).map mk (QuotientGroup.mk'_surjective R0)
    have hbarP : IsPGroup p (P0.map mk) := by
      rw [hbar]
      exact CFSG.LieType.BorelTits.pCore_isPGroup (G := Q ⧸ R0) p
    have hle : P0.map mk ≤ (Sy : Subgroup (Q ⧸ R0)) := hbarP.le_sylow_of_normal Sy
    have hSy : (Sy : Subgroup (Q ⧸ R0)) = X0.map mk := by
      simp [Sy, X0, mk, IsSylowIn.coe_toSylow, Sylow.coe_mapSurjective]
    have hmap : P0.map mk ≤ X0.map mk := by rwa [hSy] at hle
    have hle' : P0 ≤ Subgroup.comap mk (X0.map mk) :=
      (Subgroup.map_le_iff_le_comap).mp hmap
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hle'
  have hP0eq : P0 = X0 ⊔ R0 := le_antisymm hP0le (sup_le hX0P0 hR0P0)
  calc
    (E1.oTwoP ↥K p).map K.subtype = P0.map K.subtype := rfl
    _ = (X0 ⊔ R0).map K.subtype := by rw [hP0eq]
    _ = X0.map K.subtype ⊔ R0.map K.subtype := Subgroup.map_sup _ _ _
    _ = X ⊔ pCoreOf 2 K := by
      rw [Subgroup.map_subgroupOf_eq_of_le h.sylowP.le]
      rfl
    _ = pCoreOf 2 K ⊔ X := sup_comm _ _

theorem normal_pCoreOf_sup (h : TwoPTwo K S X p) : ((pCoreOf 2 K ⊔ X).subgroupOf K).Normal := by
  rw [← map_oTwoP_eq_sup h]
  have hN : (E1.oTwoP ↥K p).Normal := E1.instNormalOTwoP (Q := ↥K) p
  rw [← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  exact hN

theorem isSolvable (h : TwoPTwo K S X p) : Group.IsSolvable ↥K := by
  let Q := ↥K
  let R0 : Subgroup Q := CFSG.pCore 2 Q
  let P0 : Subgroup Q := E1.oTwoP Q p
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  haveI : Group.IsSolvable ↥R0 := isSolvable_pCore_two Q
  have hbar : Group.IsSolvable ↥(CFSG.pCore p (Q ⧸ R0)) := by
    have : Group.IsNilpotent ↥(CFSG.pCore p (Q ⧸ R0)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := Q ⧸ R0) p).isNilpotent
    infer_instance
  have hP0 : Group.IsSolvable ↥P0 := by
    show Group.IsSolvable ↥((CFSG.pCore p (Q ⧸ R0)).comap (QuotientGroup.mk' R0))
    exact isSolvable_comap_mk' (N := R0) inferInstance hbar
  have hquot : IsPGroup 2 (Q ⧸ P0) := oTwoP_quotient_isPGroup p h.oTwoPTwo
  have hQ : Group.IsSolvable Q := by
    have : Group.IsNilpotent (Q ⧸ P0) := hquot.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient P0).mpr ⟨hP0, inferInstance⟩
  exact hQ

theorem mem_sup_of_odd_orderOf (h : TwoPTwo K S X p) {k : G} (hk : k ∈ K)
    (hodd : Odd (orderOf k)) : k ∈ pCoreOf 2 K ⊔ X := by
  obtain ⟨n, hn⟩ := pow_two_pow_mem_oTwoP p h.oTwoPTwo ⟨k, hk⟩
  have hmem : k ^ 2 ^ n ∈ pCoreOf 2 K ⊔ X := by
    have hmapmem := Subgroup.mem_map_of_mem K.subtype hn
    rwa [map_oTwoP_eq_sup h] at hmapmem
  have hcop : Nat.Coprime (2 ^ n) (orderOf k) := hodd.coprime_two_left.pow_left n
  refine mem_of_pow_mem_of_coprime hmem ?_ hcop
  rw [pow_orderOf_eq_one]
  exact (pCoreOf 2 K ⊔ X).one_mem

theorem mem_pCoreOf_of_mem_sup (h : TwoPTwo K S X p) {k : G} (hk : k ∈ pCoreOf 2 K ⊔ X)
    {n : ℕ} (hn : k ^ 2 ^ n = 1) : k ∈ pCoreOf 2 K := by
  let Q := ↥K
  let R0 : Subgroup Q := CFSG.pCore 2 Q
  let X0 : Subgroup Q := X.subgroupOf K
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  have hkK : k ∈ K := (show pCoreOf 2 K ⊔ X ≤ K from
    sup_le (pCoreOf_le 2 K) h.sylowP.le) hk
  let q : Q := ⟨k, hkK⟩
  have hqsup : q ∈ R0 ⊔ X0 := by
    have hmap : (R0 ⊔ X0).map K.subtype = pCoreOf 2 K ⊔ X := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le h.sylowP.le]
      rfl
    have hk' : k ∈ (R0 ⊔ X0).map K.subtype := by rwa [hmap]
    obtain ⟨q', hq', hq'k⟩ := Subgroup.mem_map.mp hk'
    have hq'eq : q' = q := Subtype.ext hq'k
    rwa [← hq'eq]
  let π := QuotientGroup.mk' R0
  have hqπ : π q = 1 := by
    change q ∈ ((R0 ⊔ X0 : Subgroup Q) : Set Q) at hqsup
    rw [Subgroup.normal_mul] at hqsup
    obtain ⟨r0, hr0, x0, hx0, hqx⟩ := hqsup
    have hπq : π q = π x0 := by
      rw [← hqx, map_mul]
      have hr1 : π r0 = 1 := (QuotientGroup.eq_one_iff r0).mpr hr0
      rw [hr1, one_mul]
    have hxX : IsPGroup p X0 := h.sylowP.isPGroup.comap_subtype
    obtain ⟨b, hb⟩ := hxX.exists_orderOf_eq_pow ⟨x0, hx0⟩
    have hb' : orderOf x0 = p ^ b := by
      rw [← Subgroup.orderOf_mk x0 hx0, hb]
    have hdivp : orderOf (π x0) ∣ p ^ b := by
      rw [← hb']
      exact orderOf_map_dvd π x0
    have hqpow : q ^ 2 ^ n = 1 := by
      apply Subtype.ext
      change (q : G) ^ 2 ^ n = 1
      change k ^ 2 ^ n = 1
      exact hn
    have hpow2 : (π q) ^ 2 ^ n = 1 := by
      rw [← map_pow, hqpow, map_one]
    have hdiv2 : orderOf (π x0) ∣ 2 ^ n := by
      rw [← hπq]
      exact orderOf_dvd_of_pow_eq_one hpow2
    have hcop : Nat.Coprime (p ^ b) (2 ^ n) :=
      Nat.coprime_pow_primes b n h.prime Nat.prime_two h.odd
    have hone : orderOf (π x0) = 1 :=
      (hcop.coprime_dvd_left hdivp).eq_one_of_dvd hdiv2
    exact hπq.trans (orderOf_eq_one_iff.mp hone)
  have hqmem : q ∈ R0 := (QuotientGroup.eq_one_iff q).mp hqπ
  show k ∈ (CFSG.pCore 2 Q).map K.subtype
  exact Subgroup.mem_map_of_mem K.subtype hqmem

private theorem twoResidual_le_sup_pCoreOf_X (h : TwoPTwo K S X p) :
    twoResidual K ≤ pCoreOf 2 K ⊔ X := by
  have hRK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hXK : X ≤ K := h.sylowP.le
  have hNle : pCoreOf 2 K ⊔ X ≤ K := sup_le hRK hXK
  have hNnorm : K ≤ Subgroup.normalizer ((pCoreOf 2 K ⊔ X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mp (normal_pCoreOf_sup h)
  have h2 : ∀ y ∈ K, ∃ n : ℕ, y ^ 2 ^ n ∈ pCoreOf 2 K ⊔ X := by
    intro y hy
    obtain ⟨n, hn⟩ := pow_two_pow_mem_oTwoP p h.oTwoPTwo ⟨y, hy⟩
    refine ⟨n, ?_⟩
    have hmapmem := Subgroup.mem_map_of_mem K.subtype hn
    rw [map_oTwoP_eq_sup h] at hmapmem
    exact hmapmem
  exact twoResidual_le_of_isTwoQuotient hNle hNnorm h2

private theorem X_le_twoResidual_sup_pCoreOf (h : TwoPTwo K S X p) :
    X ≤ twoResidual K ⊔ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  intro x hxX
  obtain ⟨b, hb⟩ := h.sylowP.isPGroup.exists_orderOf_eq_pow ⟨x, hxX⟩
  have hbx : orderOf x = p ^ b := by
    rw [← Subgroup.orderOf_mk x hxX, hb]
  obtain ⟨n, hn⟩ := twoResidual_isTwoQuotient K x (h.sylowP.le hxX)
  have hcop : Nat.Coprime (2 ^ n) (orderOf x) := by
    rw [hbx]
    exact Nat.coprime_pow_primes n b Nat.prime_two h.prime h.odd.symm
  refine mem_of_pow_mem_of_coprime (H := twoResidual K ⊔ pCoreOf 2 K)
    (show x ^ 2 ^ n ∈ twoResidual K ⊔ pCoreOf 2 K from Subgroup.mem_sup_left hn) ?_ hcop
  rw [pow_orderOf_eq_one]
  exact (twoResidual K ⊔ pCoreOf 2 K).one_mem

theorem twoResidual_sup_pCoreOf (h : TwoPTwo K S X p) :
    twoResidual K ⊔ pCoreOf 2 K = pCoreOf 2 K ⊔ X := by
  apply le_antisymm
  · exact sup_le (twoResidual_le_sup_pCoreOf_X h) le_sup_left
  · exact sup_le le_sup_right (X_le_twoResidual_sup_pCoreOf h)

theorem mul_eq (h : TwoPTwo K S X p) : (K : Set G) = (S : Set G) * (X : Set G) := by
  let C : Subgroup G := pCoreOf 2 K ⊔ X
  let R : Subgroup G := pCoreOf 2 K
  have hRK : R ≤ K := pCoreOf_le 2 K
  have hXK : X ≤ K := h.sylowP.le
  have hCle : C ≤ K := sup_le hRK hXK
  have hCnorm : K ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCle).mp (normal_pCoreOf_sup h)
  have hRnorm : K ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 K
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := hXK.trans hRnorm
  have hSC : S ≤ Subgroup.normalizer (C : Set G) := h.sylowTwo.le.trans hCnorm
  have h2 : ∀ y ∈ K, ∃ n : ℕ, y ^ 2 ^ n ∈ C := by
    intro y hy
    obtain ⟨n, hn⟩ := pow_two_pow_mem_oTwoP p h.oTwoPTwo ⟨y, hy⟩
    refine ⟨n, ?_⟩
    have hmapmem := Subgroup.mem_map_of_mem K.subtype hn
    rw [map_oTwoP_eq_sup h] at hmapmem
    exact hmapmem
  have hsup : C ⊔ S = K :=
    CFSG.Quasithin.B6.sup_eq_of_isTwoQuotient hCle hCnorm h2
      (show IsSylowTwoOf S K from h.sylowTwo)
  have hCS : (K : Set G) = (C : Set G) * (S : Set G) := by
    rw [← hsup]
    exact Subgroup.coe_mul_of_right_le_normalizer_left C S hSC
  have hCR : (C : Set G) = (R : Set G) * (X : Set G) := by
    show ((R ⊔ X : Subgroup G) : Set G) = (R : Set G) * (X : Set G)
    exact Subgroup.coe_mul_of_right_le_normalizer_left R X hXR
  have hprod : (K : Set G) = (X : Set G) * (S : Set G) := by
    rw [hCS, hCR]
    apply Set.Subset.antisymm
    · intro y hy
      rw [Set.mem_mul] at hy
      rw [Set.mem_mul]
      obtain ⟨a, ha, s, hs, rfl⟩ := hy
      rw [Set.mem_mul] at ha
      obtain ⟨r, hr, x, hx, rfl⟩ := ha
      refine ⟨x, hx, x⁻¹ * r * x * s, S.mul_mem ?_ hs, by group⟩
      have hxR : x ∈ Subgroup.normalizer (R : Set G) := hXR hx
      have hxrR : x⁻¹ * r * x ∈ R := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxR) r).mp hr
      exact pCoreOf_le_sylowTwo h hxrR
    · intro y hy
      rw [Set.mem_mul] at hy
      rw [Set.mem_mul]
      obtain ⟨x, hx, s, hs, rfl⟩ := hy
      refine ⟨x, ?_, s, hs, by group⟩
      rw [Set.mem_mul]
      exact ⟨1, R.one_mem, x, hx, by group⟩
  calc (K : Set G) = ((K : Set G))⁻¹ := by rw [inv_coe_set]
    _ = ((X : Set G) * (S : Set G))⁻¹ := by rw [hprod]
    _ = (S : Set G) * (X : Set G) := by
        rw [mul_inv_rev, inv_coe_set, inv_coe_set]

theorem mem_sup_of_commutator_mem (h : TwoPTwo K S X p) {k : G} (hk : k ∈ K)
    (hc : ∀ x ∈ X, ⁅k, x⁆ ∈ pCoreOf 2 K) : k ∈ pCoreOf 2 K ⊔ X := by
  let Q := ↥K
  let R0 : Subgroup Q := CFSG.pCore 2 Q
  let P0 : Subgroup Q := E1.oTwoP Q p
  let X0 : Subgroup Q := X.subgroupOf K
  let Kb := Q ⧸ R0
  let mk := QuotientGroup.mk' R0
  let Pb : Subgroup Kb := P0.map mk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  have hR0P0 : R0 ≤ P0 := by
    intro x hx
    rw [show P0 = E1.oTwoP Q p from rfl, E1.oTwoP, Subgroup.mem_comap]
    have hx1 : QuotientGroup.mk' R0 x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact Subgroup.one_mem _
  have hP0eq : P0 = X0 ⊔ R0 := by
    have hmap : P0.map K.subtype = (X0 ⊔ R0).map K.subtype := by
      rw [map_oTwoP_eq_sup h, Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le h.sylowP.le]
      exact sup_comm _ _
    exact Subgroup.map_injective K.subtype_injective hmap
  have hPb_eq : Pb = CFSG.pCore p Kb := by
    change (E1.oTwoP Q p).map mk = _
    rw [E1.oTwoP]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R0) _
  have hPb_isP : IsPGroup p Pb := hPb_eq ▸ CFSG.LieType.BorelTits.pCore_isPGroup (G := Kb) p
  have hPbX : Pb = X0.map mk := by
    show P0.map mk = _
    rw [hP0eq, Subgroup.map_sup]
    have hRbot : R0.map mk = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hRbot, sup_bot_eq]
  have hKbarSolv : Group.IsSolvable Kb := by
    haveI : Group.IsSolvable Q := isSolvable h
    infer_instance
  have hpsolv : CFSG.HallHigman.IsPSolvable p Kb :=
    isPSolvable_of_isSolvable h.prime hKbarSolv
  have hO2 : CFSG.pCore 2 Kb = ⊥ := by
    let Rbar : Subgroup Kb := CFSG.pCore 2 Kb
    have hRbar2 : IsPGroup 2 Rbar :=
      CFSG.LieType.BorelTits.pCore_isPGroup (G := Kb) 2
    have hker2 : IsPGroup 2 mk.ker := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) 2
    have hM2 : IsPGroup 2 (Rbar.comap mk) := hRbar2.comap_of_ker_isPGroup mk hker2
    haveI : (Rbar.comap mk).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2).comap mk
    have hMle : Rbar.comap mk ≤ R0 := le_pCore 2 inferInstance hM2
    have hmapbot : (Rbar.comap mk).map mk = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hMle
    calc Rbar = (Rbar.comap mk).map mk :=
          (Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective R0) Rbar).symm
      _ = ⊥ := hmapbot
  have hOpp : CFSG.pPrimeCore p Kb = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro N hNnorm hNcop
    let πb := QuotientGroup.mk' Pb
    have hquot2 : IsPGroup 2 (Kb ⧸ Pb) := by
      let e : (Kb ⧸ Pb) ≃* (Q ⧸ P0) :=
        QuotientGroup.quotientQuotientEquivQuotient R0 P0 hR0P0
      exact (oTwoP_quotient_isPGroup p h.oTwoPTwo).of_equiv e.symm
    have hNimg2 : IsPGroup 2 (N.map πb) := hquot2.to_subgroup _
    have hNP : IsPGroup p ↥(N ⊓ Pb) := hPb_isP.to_inf_right (H := N)
    have hNPb_bot : N ⊓ Pb = ⊥ := by
      refine eq_bot_of_isPGroup_of_coprime_card h.prime hNP ?_
      exact hNcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    have hN2 : IsPGroup 2 N := by
      let φ : N →* N.map πb :=
        (πb.comp N.subtype).codRestrict (N.map πb)
          (fun x => Subgroup.mem_map_of_mem πb x.2)
      have hφinj : Function.Injective φ := by
        intro a b hab
        apply Subtype.ext
        have hπeq : πb (a : Kb) = πb (b : Kb) := congrArg Subtype.val hab
        have h1 : πb ((a : Kb) * (b : Kb)⁻¹) = 1 := by
          rw [map_mul, map_inv, hπeq, mul_inv_cancel]
        have h2 : (a : Kb) * (b : Kb)⁻¹ ∈ Pb := (QuotientGroup.eq_one_iff _).mp h1
        have hmem : (a : Kb) * (b : Kb)⁻¹ ∈ N ⊓ Pb :=
          ⟨N.mul_mem a.2 (N.inv_mem b.2), h2⟩
        rw [hNPb_bot, Subgroup.mem_bot] at hmem
        exact mul_inv_eq_one.mp hmem
      exact hNimg2.of_injective φ hφinj
    have hNle : N ≤ CFSG.pCore 2 Kb := le_pCore 2 hNnorm hN2
    rw [hO2] at hNle
    exact le_bot_iff.mp hNle
  have hcent : CFSG.IsCharacteristicP p Kb :=
    CFSG.HallHigman.isCharacteristicP_of_isPSolvable hpsolv hOpp
  let q : Q := ⟨k, hk⟩
  let kb : Kb := mk q
  have hkb_cent : kb ∈ Subgroup.centralizer (CFSG.pCore p Kb : Set Kb) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyPb : y ∈ Pb := by rwa [hPb_eq]
    rw [hPbX] at hyPb
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hyPb
    have hx0X : (x0 : G) ∈ X := hx0
    have hcommQ : ⁅q, x0⁆ ∈ R0 := by
      have hcommG : ⁅k, (x0 : G)⁆ ∈ pCoreOf 2 K := hc (x0 : G) hx0X
      have hmapcomm : ((⁅q, x0⁆ : Q) : G) = ⁅k, (x0 : G)⁆ :=
        map_commutatorElement (f := K.subtype) (g₁ := q) (g₂ := x0)
      have hmem : ((⁅q, x0⁆ : Q) : G) ∈ R0.map K.subtype := by
        rw [hmapcomm]
        exact hcommG
      obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hmem
      have hzq : z = ⁅q, x0⁆ := Subtype.ext hzeq
      rwa [← hzq]
    have hcommQuot : ⁅kb, mk x0⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hcommQ
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommQuot).symm
  have hkb : kb ∈ CFSG.pCore p Kb := hcent hkb_cent
  have hqP : q ∈ P0 := by
    have hqcomap : q ∈ (CFSG.pCore p Kb).comap mk := Subgroup.mem_comap.mpr hkb
    simpa [P0, E1.oTwoP, Kb, mk] using hqcomap
  have hkmap : k ∈ P0.map K.subtype := Subgroup.mem_map_of_mem K.subtype hqP
  rwa [map_oTwoP_eq_sup h] at hkmap

theorem mem_pCoreOf_of_commutator_mem_frattiniR (h : TwoPTwo K S X p) {k : G} (hk : k ∈ K)
    {n : ℕ} (hn : k ^ 2 ^ n = 1) (hc : ∀ x ∈ X, ⁅k, x⁆ ∈ nineFrattiniR K X) :
    k ∈ pCoreOf 2 K := by
  let Q := ↥K
  let R0 : Subgroup Q := CFSG.pCore 2 Q
  let P0 : Subgroup Q := E1.oTwoP Q p
  let X0 : Subgroup Q := X.subgroupOf K
  let Kb := Q ⧸ R0
  let mk := QuotientGroup.mk' R0
  let Pb : Subgroup Kb := P0.map mk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  have hR0P0 : R0 ≤ P0 := by
    intro x hx
    rw [show P0 = E1.oTwoP Q p from rfl, E1.oTwoP, Subgroup.mem_comap]
    have hx1 : QuotientGroup.mk' R0 x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact Subgroup.one_mem _
  have hP0eq : P0 = X0 ⊔ R0 := by
    have hmap : P0.map K.subtype = (X0 ⊔ R0).map K.subtype := by
      rw [map_oTwoP_eq_sup h, Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le h.sylowP.le]
      exact sup_comm _ _
    exact Subgroup.map_injective K.subtype_injective hmap
  have hPbX : Pb = X0.map mk := by
    show P0.map mk = _
    rw [hP0eq, Subgroup.map_sup]
    have hRbot : R0.map mk = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hRbot, sup_bot_eq]
  have hPb_eq : Pb = CFSG.pCore p Kb := by
    change (E1.oTwoP Q p).map mk = _
    rw [E1.oTwoP]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R0) _
  have hPb_isP : IsPGroup p Pb := hPb_eq ▸ CFSG.LieType.BorelTits.pCore_isPGroup (G := Kb) p
  have hPb_normal : Pb.Normal := hPb_eq ▸ (CFSG.LieType.BorelTits.pCore_normal p)
  let Φ : Subgroup Kb := (frattini ↥Pb).map Pb.subtype
  have hΦ_normal : Φ.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    have h1 : (⊤ : Subgroup Kb) ≤ Subgroup.normalizer (Pb : Set Kb) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hPb_normal]
    have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Pb) (K := frattini ↥Pb)
    have h : (⊤ : Subgroup Kb) ≤ Subgroup.normalizer (Φ : Set Kb) := by
      simpa [Φ] using h1.trans h2
    exact top_le_iff.mp h
  have hΦXmap : ((nineFrattini X).subgroupOf K).map mk ≤ Φ := by
    let φ : ↥X →* ↥Pb :=
      { toFun := fun x =>
          let xQ : Q := ⟨(x : G), h.sylowP.le x.2⟩
          let x0 : X0 := ⟨xQ, by
            change (xQ : G) ∈ X
            exact x.2⟩
          ⟨mk xQ, by
            rw [hPbX]
            exact Subgroup.mem_map_of_mem mk x0.2⟩
        map_one' := by
          apply Subtype.ext
          change mk (1 : Q) = 1
          rw [map_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          change mk ((⟨(a : G), h.sylowP.le a.2⟩ : Q) *
            ⟨(b : G), h.sylowP.le b.2⟩) =
            mk ⟨(a : G), h.sylowP.le a.2⟩ * mk ⟨(b : G), h.sylowP.le b.2⟩
          rw [map_mul] }
    have hφsurj : Function.Surjective φ := by
      intro y
      have hy : (y : Kb) ∈ X0.map mk := hPbX ▸ y.2
      obtain ⟨x0, hx0, hx0y⟩ := Subgroup.mem_map.mp hy
      refine ⟨⟨(x0 : G), hx0⟩, ?_⟩
      apply Subtype.ext
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
      change mk x0 = (y : Kb)
      exact hx0y
    have hfr := frattini_le_comap_frattini_of_surjective (φ := φ) hφsurj
    intro z hz
    obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp hz
    have hz0Φ : (z0 : G) ∈ nineFrattini X := hz0
    obtain ⟨xΦ, hxΦ, hxΦz⟩ := Subgroup.mem_map.mp hz0Φ
    have hxmem : φ xΦ ∈ frattini ↥Pb := hfr hxΦ
    refine Subgroup.mem_map.mpr ⟨φ xΦ, hxmem, ?_⟩
    change (φ xΦ : Kb) = mk z0
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
    change mk ⟨(xΦ : G), h.sylowP.le xΦ.2⟩ = mk z0
    rw [show (⟨(xΦ : G), h.sylowP.le xΦ.2⟩ : Q) = z0 from Subtype.ext hxΦz]
  have hNineMap : ((nineFrattiniR K X).subgroupOf K).map mk ≤ Φ := by
    change ((nineFrattini X ⊔ pCoreOf 2 K).subgroupOf K).map mk ≤ Φ
    have hsup : (nineFrattini X ⊔ pCoreOf 2 K).subgroupOf K =
        (nineFrattini X).subgroupOf K ⊔ (pCoreOf 2 K).subgroupOf K :=
      Subgroup.subgroupOf_sup
        ((Subgroup.map_subtype_le _).trans h.sylowP.le) (pCoreOf_le 2 K)
    rw [hsup, Subgroup.map_sup]
    refine sup_le hΦXmap ?_
    have hRsub : (pCoreOf 2 K).subgroupOf K = R0 := by
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective R0
    rw [hRsub]
    have hRbot : R0.map mk = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hRbot]
    exact bot_le
  let q : Q := ⟨k, hk⟩
  let kb : Kb := mk q
  have hqpow : q ^ 2 ^ n = 1 := by
    apply Subtype.ext
    change (q : G) ^ 2 ^ n = 1
    change k ^ 2 ^ n = 1
    exact hn
  have hkbpow : kb ^ 2 ^ n = 1 := by
    change (mk q) ^ 2 ^ n = 1
    rw [← map_pow, hqpow, map_one]
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers kb)) (Nat.card Pb) := by
    obtain ⟨m, hm⟩ := hPb_isP.exists_card_eq
    rw [hm]
    have hdvd : Nat.card (Subgroup.zpowers kb) ∣ 2 ^ n := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hkbpow
    exact Nat.Coprime.coprime_dvd_left hdvd
      (Nat.coprime_pow_primes n m Nat.prime_two h.prime h.odd.symm)
  have hcentPb : kb ∈ Subgroup.centralizer (Pb : Set Kb) := by
    refine CFSG.mem_centralizer_of_quotient_frattini_local (p := p) (H := Pb) (Φ := Φ)
      hPb_isP rfl kb hcop ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hy
    rw [hPbX] at hh'
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hh'
    have hx0X : (x0 : G) ∈ X := hx0
    have hcommQ : ⁅q, x0⁆ ∈ (nineFrattiniR K X).subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      have hmapcomm : ((⁅q, x0⁆ : Q) : G) = ⁅k, (x0 : G)⁆ :=
        map_commutatorElement (f := K.subtype) (g₁ := q) (g₂ := x0)
      rw [hmapcomm]
      exact hc (x0 : G) hx0X
    have hcommPb : ⁅kb, mk x0⁆ ∈ Φ := by
      have h1 : mk ⁅q, x0⁆ ∈ Φ :=
        hNineMap (Subgroup.mem_map_of_mem mk hcommQ)
      have h2 : mk ⁅q, x0⁆ = ⁅kb, mk x0⁆ :=
        map_commutatorElement (f := mk) (g₁ := q) (g₂ := x0)
      rwa [h2] at h1
    have hcommQuot : ⁅QuotientGroup.mk' Φ kb, QuotientGroup.mk' Φ (mk x0)⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hcommPb
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommQuot).symm
  have hcR : ∀ x ∈ X, ⁅k, x⁆ ∈ pCoreOf 2 K := by
    intro x hxX
    have hxK : x ∈ K := h.sylowP.le hxX
    let x0 : Q := ⟨x, hxK⟩
    have hx0 : x0 ∈ X0 := hxX
    have hxPb : mk x0 ∈ Pb := by
      rw [hPbX]
      exact Subgroup.mem_map_of_mem mk hx0
    have hcomm := Subgroup.mem_centralizer_iff.mp hcentPb (mk x0) hxPb
    have h1 : ⁅kb, mk x0⁆ = 1 :=
      (commutatorElement_eq_one_iff_mul_comm).mpr hcomm.symm
    have hqcomm : ⁅q, x0⁆ ∈ R0 := by
      have hker : mk ⁅q, x0⁆ = 1 := by
        rw [map_commutatorElement]
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp hker
    have hmapcomm : ((⁅q, x0⁆ : Q) : G) = ⁅k, x⁆ :=
      map_commutatorElement (f := K.subtype) (g₁ := q) (g₂ := x0)
    have hG : ⁅k, x⁆ ∈ pCoreOf 2 K := by
      rw [← hmapcomm]
      exact Subgroup.mem_map_of_mem K.subtype hqcomm
    exact hG
  have hksup : k ∈ pCoreOf 2 K ⊔ X := mem_sup_of_commutator_mem h hk hcR
  exact mem_pCoreOf_of_mem_sup h hksup hn

theorem subgroupOf_normal_of_le_normalizer (h : TwoPTwo K S X p) {N : Subgroup G} (hNK : N ≤ K)
    (hN₁ : twoResidual K ≤ normalizer (N : Set G)) (hN₂ : S ≤ normalizer (N : Set G)) :
    (N.subgroupOf K).Normal := by
  have hsup : S ⊔ twoResidual K = K :=
    sup_twoResidual_eq (show IsSylowTwoOf S K from h.sylowTwo)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr ?_
  rw [← hsup]
  exact sup_le hN₂ hN₁

theorem twoResidual_le_of_le_sup (h : TwoPTwo K S X p) {N : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) (hX : X ≤ N ⊔ pCoreOf 2 K) : twoResidual K ≤ N := by
  let Q := ↥K
  let N0 : Subgroup Q := N.subgroupOf K
  let R0 : Subgroup Q := CFSG.pCore 2 Q
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  have hKN : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hN
  have hXN : X ≤ N := by
    intro x hxX
    have hxK : x ∈ K := h.sylowP.le hxX
    let q : Q := ⟨x, hxK⟩
    have hqsup : q ∈ N0 ⊔ R0 := by
      have hmap : (N0 ⊔ R0).map K.subtype = N ⊔ pCoreOf 2 K := by
        rw [Subgroup.map_sup, show N0.map K.subtype = N from
          Subgroup.map_subgroupOf_eq_of_le hNK]
        rfl
      have hq' : x ∈ (N0 ⊔ R0).map K.subtype := by
        rw [hmap]
        exact hX hxX
      obtain ⟨q', hq', hq'x⟩ := Subgroup.mem_map.mp hq'
      have hqeq : q' = q := Subtype.ext hq'x
      rwa [← hqeq]
    let π := QuotientGroup.mk' N0
    have hqπ : π q = 1 := by
      change q ∈ ((N0 ⊔ R0 : Subgroup Q) : Set Q) at hqsup
      rw [Subgroup.normal_mul] at hqsup
      obtain ⟨n0, hn0, r0, hr0, hqr⟩ := hqsup
      have hπq : π q = π r0 := by
        rw [← hqr, map_mul]
        have hn1 : π n0 = 1 := (QuotientGroup.eq_one_iff n0).mpr hn0
        rw [hn1, one_mul]
      obtain ⟨c, hc⟩ := h.sylowP.isPGroup.exists_orderOf_eq_pow ⟨x, hxX⟩
      have hcx : orderOf x = p ^ c := by
        rw [← Subgroup.orderOf_mk x hxX, hc]
      have hcq : orderOf q = p ^ c := (Subgroup.orderOf_mk x hxK).trans hcx
      have hR0p : IsPGroup 2 R0 :=
        CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) 2
      obtain ⟨b, hb⟩ := hR0p.exists_orderOf_eq_pow ⟨r0, hr0⟩
      have hbr : orderOf r0 = 2 ^ b := by
        rw [← Subgroup.orderOf_mk r0 hr0, hb]
      have hdivp : orderOf (π q) ∣ p ^ c := by
        rw [← hcq]
        exact orderOf_map_dvd π q
      have hdiv2 : orderOf (π r0) ∣ 2 ^ b := by
        rw [← hbr]
        exact orderOf_map_dvd π r0
      have hdiv2' : orderOf (π q) ∣ 2 ^ b := by rwa [← hπq] at hdiv2
      have hcop : Nat.Coprime (p ^ c) (2 ^ b) :=
        Nat.coprime_pow_primes c b h.prime Nat.prime_two h.odd
      have hone : orderOf (π q) = 1 :=
        (hcop.coprime_dvd_left hdivp).eq_one_of_dvd hdiv2'
      exact orderOf_eq_one_iff.mp hone
    have hqmem : q ∈ N0 := (QuotientGroup.eq_one_iff q).mp hqπ
    show x ∈ N
    exact Subgroup.mem_subgroupOf.mp hqmem
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := h.sylowTwo.le.trans hKN
  have hSsupN : ((S ⊔ N : Subgroup G) : Set G) = (S : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S N hSN
  have hsup : S ⊔ N = K := by
    apply le_antisymm (sup_le h.sylowTwo.le hNK)
    intro k hk
    have hkSX : k ∈ (S : Set G) * (X : Set G) := by
      change k ∈ (K : Set G) at hk
      rwa [mul_eq h] at hk
    change k ∈ ((S ⊔ N : Subgroup G) : Set G)
    rw [hSsupN]
    rw [Set.mem_mul] at hkSX ⊢
    obtain ⟨s, hs, x, hx, rfl⟩ := hkSX
    exact ⟨s, hs, x, hXN hx, rfl⟩
  have h2 : ∀ y ∈ K, ∃ m : ℕ, y ^ 2 ^ m ∈ N :=
    CFSG.Quasithin.B6.isTwoQuotient_of_sup_eq h.sylowTwo.isPGroup hKN hsup
  exact twoResidual_le_of_isTwoQuotient hNK hKN h2

theorem not_le_frattiniR_of_isPGroup (h : TwoPTwo K S X p) {A : Subgroup G} (hAK : A ≤ K)
    (hA : IsPGroup 2 A) (hAR : ¬ A ≤ pCoreOf 2 K) : ¬ A ≤ nineFrattiniR K X := by
  intro hle
  apply hAR
  intro a ha
  have haF : a ∈ nineFrattiniR K X := hle ha
  have hΦX : nineFrattini X ≤ X := Subgroup.map_subtype_le _
  have haXR : a ∈ pCoreOf 2 K ⊔ X :=
    (show nineFrattiniR K X ≤ pCoreOf 2 K ⊔ X from sup_le (hΦX.trans le_sup_right) le_sup_left) haF
  obtain ⟨n, hn⟩ := hA ⟨a, ha⟩
  have hn' : a ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa [Subgroup.coe_pow] using this
  exact mem_pCoreOf_of_mem_sup h haXR hn'

end TwoPTwo

end CFSG.LocalAnalysis.WeakClosure81
