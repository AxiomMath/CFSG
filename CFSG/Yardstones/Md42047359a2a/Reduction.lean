module

public import CFSG.Yardstones.Md42047359a2a.Definitions
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.I19DefCharHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieDC
public import CFSG.CGT.PushingUpLit.CGT6.EmbLayer
public import CFSG.RankThree.PartOne.N143.CaseB1Theta
public import CFSG.RankThree.PartOne.S12.Sec159Fin
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLoc
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor

public section

namespace CFSG.Yardstones.Md42047359a2a

open CFSG.Open Subgroup

theorem inCatalog_center_quotient {Z : Type} [Group Z] (hZ : lBalanceIsKGroup Z)
    (K : Subgroup Z) (hK : CFSG.IsComponent K) : CFSG.Assembly.InCatalog (K ⧸ center K) := by
  let L : Subgroup Z := (center K).map K.subtype
  have hLK : L ≤ K := Subgroup.map_subtype_le _
  have hL : L.subgroupOf K = center K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have : (L.subgroupOf K).Normal := by
    rw [hL]
    infer_instance
  let e : K ⧸ L.subgroupOf K ≃* K ⧸ center K := QuotientGroup.quotientMulEquivOfEq hL
  have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  have hsimple : IsSimpleGroup (K ⧸ L.subgroupOf K) := e.isSimpleGroup
  have hnonab : ∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK.1.2.2
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  obtain ⟨i, ⟨f⟩⟩ := hZ K L hLK hsimple hnonab
  exact ⟨i, ⟨e.symm.trans f⟩⟩

section Normalization

open CFSG CFSG.LocalCores CFSG.ComponentClassification CFSG.ComponentClassification.LBalance

variable {H : Type*} [Group H]

theorem conjugate_eq_self_iff {K : Subgroup H} {g : H} :
    conjugate K g = K ↔ g ∈ normalizer (K : Set H) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h k
    rw [← UnbalancedLayer.mem_conjugate_iff, h]
  · intro h
    ext k
    rw [UnbalancedLayer.mem_conjugate_iff]
    exact (h k).symm

theorem le_normalizer_of_coprime_orbit {p : ℕ} {S : Subgroup H}
    (hS : Nat.Coprime p (Nat.card S)) {x : H} {n : ℕ} (hxn : x ^ p ^ n = 1)
    (hSx : S ≤ centralizer ({x} : Set H)) {K : Subgroup H}
    (horb : ∀ s ∈ S, ∃ i : ℤ, conjugate K s = conjugate K (x ^ i)) :
    S ≤ normalizer (K : Set H) := by
  intro s hs
  obtain ⟨i, hi⟩ := horb s hs
  have hsx : ∀ j : ℤ, s * x ^ j = x ^ j * s := fun j =>
    ((show Commute s x from mem_centralizer_singleton_iff.mp (hSx hs)).zpow_right j).eq
  have hpow : ∀ k : ℕ, conjugate K (s ^ k) = conjugate K (x ^ ((k : ℤ) * i)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc conjugate K (s ^ (k + 1)) = conjugate (conjugate K (s ^ k)) s := by
            rw [pow_succ, UnbalancedLayer.conjugate_conjugate]
        _ = conjugate K (x ^ ((k : ℤ) * i) * s) := by
            rw [ih, UnbalancedLayer.conjugate_conjugate]
        _ = conjugate K (s * x ^ ((k : ℤ) * i)) := by rw [hsx]
        _ = conjugate (conjugate K s) (x ^ ((k : ℤ) * i)) := by
            rw [UnbalancedLayer.conjugate_conjugate]
        _ = conjugate K (x ^ i * x ^ ((k : ℤ) * i)) := by
            rw [hi, UnbalancedLayer.conjugate_conjugate]
        _ = conjugate K (x ^ (((k + 1 : ℕ) : ℤ) * i)) := by
            rw [← zpow_add]
            congr 2
            push_cast
            ring
  have hord : Nat.Coprime p (orderOf s) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard S hs) hS
  have hym : (x ^ i) ^ orderOf s ∈ normalizer (K : Set H) := by
    rw [← conjugate_eq_self_iff]
    have h1 := hpow (orderOf s)
    rw [pow_orderOf_eq_one, UnbalancedLayer.conjugate_one] at h1
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    exact h1.symm
  have hyp : (x ^ i) ^ (p ^ n) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxn, one_zpow]
  have hcop : Nat.Coprime (orderOf s) (p ^ n) := (Nat.Coprime.pow_left n hord).symm
  have hgcd := Nat.gcd_eq_gcd_ab (orderOf s) (p ^ n)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hgcd
  have hy : x ^ i ∈ normalizer (K : Set H) := by
    generalize x ^ i = y at hym hyp ⊢
    have hy_eq : y = (y ^ orderOf s) ^ (Nat.gcdA (orderOf s) (p ^ n)) *
        (y ^ (p ^ n)) ^ (Nat.gcdB (orderOf s) (p ^ n)) := by
      rw [← zpow_natCast y (orderOf s), ← zpow_natCast y (p ^ n), ← zpow_mul, ← zpow_mul,
        ← zpow_add, ← hgcd, zpow_one]
    rw [hy_eq, hyp, one_zpow, mul_one]
    exact zpow_mem hym _
  exact conjugate_eq_self_iff.mp (hi.trans (conjugate_eq_self_iff.mpr hy))

end Normalization

section NormalizationMain

open CFSG CFSG.LocalCores CFSG.ComponentClassification CFSG.ComponentClassification.LBalance

theorem core_normalizes_components {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hcore : lBalancePrimeCore p (⊤ : Subgroup H) = ⊥) {x : H} (hx : ∃ n : ℕ, x ^ p ^ n = 1)
    {K : Subgroup H} (hK : CFSG.IsComponent K) :
    lBalancePrimeCore p (centralizer ({x} : Set H)) ≤ normalizer (K : Set H) := by
  have : Fact p.Prime := ⟨hp⟩
  have hO : pPrimeCore p H = ⊥ := by
    rw [← LBalance.primeCore_top]
    exact hcore
  obtain ⟨n, hxn⟩ := hx
  have hSC : lBalancePrimeCore p (centralizer ({x} : Set H)) ≤ centralizer ({x} : Set H) :=
    LBalance.primeCore_le p _
  have hScop : Nat.Coprime p (Nat.card (lBalancePrimeCore p (centralizer ({x} : Set H)))) :=
    LBalance.primeCore_coprime p _
  have hSn : ((lBalancePrimeCore p (centralizer ({x} : Set H))).subgroupOf
      (centralizer ({x} : Set H))).Normal := LBalance.primeCore_normal p _
  set S := lBalancePrimeCore p (centralizer ({x} : Set H)) with hSdef
  have : (layer H).Characteristic := layer_characteristic
  have hE : (layer H).Normal := inferInstance
  set Z := (center (layer H)).map (layer H).subtype with hZdef
  have hZn : Z.Normal := by
    constructor
    intro z hz h
    obtain ⟨hzE, hzc⟩ := (mem_map_center_iff _).mp hz
    refine (mem_map_center_iff _).mpr ⟨hE.conj_mem z hzE h, ?_⟩
    rw [mem_centralizer_iff]
    intro e he
    have he' : h⁻¹ * e * h ∈ layer H := by simpa using hE.conj_mem e he h⁻¹
    have hez := mem_centralizer_iff.mp hzc _ he'
    calc e * (h * z * h⁻¹) = h * ((h⁻¹ * e * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * e * h)) * h⁻¹ := by rw [hez]
      _ = h * z * h⁻¹ * e := by group
  have hFP : fittingSubgroup H ≤ pCore p H :=
    le_sSup ⟨inferInstance, isPGroup_of_nilpotent_normal _ inferInstance inferInstance hO⟩
  have hZp : IsPGroup p Z :=
    pCore_isPGroup.to_le (UnbalancedLayer.center_layer_le_fittingSubgroup.trans hFP)
  have hxp : IsPGroup p (zpowers x) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hxn)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hZnorm : ∀ L : Subgroup H, L ≤ normalizer (Z : Set H) := fun L =>
    le_top.trans (normalizer_eq_top_iff.mpr hZn).ge
  have hxS : zpowers x ≤ centralizer (S : Set H) :=
    zpowers_le.mpr (mem_centralizer_iff.mpr fun s hs => mem_centralizer_singleton_iff.mp (hSC hs))
  have hSZ : ⁅Z, S⁆ = ⊥ := by
    refine GorensteinWalter.ThompsonPQ.thompson_p_times_q (zpowers x) S Z hxp hZp hScop
      (hZnorm _) (hZnorm _) (commutator_eq_bot_iff_le_centralizer.mpr hxS) ?_
    intro z hz
    obtain ⟨hzZ, hzx⟩ := mem_inf.mp hz
    have hzC : z ∈ centralizer ({x} : Set H) :=
      centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers x)) hzx
    refine mem_centralizer_iff.mpr fun s hs => ?_
    have hcS : s * z * s⁻¹ * z⁻¹ ∈ S := by
      have h1 : z * s⁻¹ * z⁻¹ ∈ S := by
        have := hSn.conj_mem ⟨s⁻¹, hSC (inv_mem hs)⟩ (mem_subgroupOf.mpr (inv_mem hs)) ⟨z, hzC⟩
        simpa only [mem_subgroupOf, coe_mul, coe_inv] using this
      simpa only [mul_assoc] using mul_mem hs h1
    have hcZ : s * z * s⁻¹ * z⁻¹ ∈ Z := mul_mem (hZn.conj_mem z hzZ s) (inv_mem hzZ)
    obtain ⟨a, ha⟩ := hZp ⟨_, hcZ⟩
    have hca : (s * z * s⁻¹ * z⁻¹) ^ p ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this
    have h1 := Core.eq_one_of_mem_of_pow_prime_pow hScop hcS hca
    have h2 : s * z = z * s := by
      have h3 : s * z * s⁻¹ * z⁻¹ * (z * s) = z * s := by rw [h1, one_mul]
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h3
    exact h2
  have hSZc : S ≤ centralizer (Z : Set H) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hSZ
  set C0 := centralizer (Z : Set H) ⊓ centralizer ({x} : Set H) with hC0
  have hSC0 : S ≤ C0 := le_inf hSZc hSC
  set U := UnbalancedLayer.displacementSubgroup Z x with hU
  have hC0U : C0 ≤ U := UnbalancedLayer.centralizer_inf_le_displacementSubgroup Z x
  have hC0n : (C0.subgroupOf U).Normal := UnbalancedLayer.centralizer_inf_normal_displacementSubgroup Z x
  have hconj : ∀ w ∈ U, ∀ c ∈ C0, w * c * w⁻¹ ∈ C0 := by
    intro w hw c hc
    have := hC0n.conj_mem ⟨c, hC0U hc⟩ (mem_subgroupOf.mpr hc) ⟨w, hw⟩
    simpa only [mem_subgroupOf, coe_mul, coe_inv] using this
  have hSnC0 : ∀ c ∈ C0, ∀ s ∈ S, c * s * c⁻¹ ∈ S := by
    intro c hc s hs
    have := hSn.conj_mem ⟨s, hSC hs⟩ (mem_subgroupOf.mpr hs) ⟨c, (mem_inf.mp hc).2⟩
    simpa only [mem_subgroupOf, coe_mul, coe_inv] using this
  set O := lBalancePrimeCore p C0 with hOdef
  have hOcop : Nat.Coprime p (Nat.card O) := LBalance.primeCore_coprime p C0
  have hleO : ∀ T : Subgroup H, T ≤ C0 → (∀ c ∈ C0, ∀ t ∈ T, c * t * c⁻¹ ∈ T) →
      Nat.Coprime p (Nat.card T) → T ≤ O := by
    intro T hTC hTn hTcop
    refine le_sSup ⟨hTC, ?_, hTcop⟩
    refine ⟨fun t ht c => ?_⟩
    exact mem_subgroupOf.mpr (by
      simpa only [coe_mul, coe_inv] using hTn c c.2 t (mem_subgroupOf.mp ht))
  have hSO : S ≤ O := hleO S hSC0 hSnC0 hScop
  obtain ⟨u, huM, ⟨a, hua⟩, ⟨k₀, hk₀, hk₀u⟩, hz⟩ :=
    Core.exists_orbit_witness hxn hK (Core.prime_dvd_card_center_quotient hO hK)
  have huE : u ∈ layer H := Core.orbitJoin_le_layer hK x huM
  have huC : u ∈ centralizer (Z : Set H) := by
    rw [mem_centralizer_iff]
    intro z hzZ
    exact (mem_centralizer_iff.mp ((mem_map_center_iff _).mp hzZ).2 u huE).symm
  have huU : u ∈ U := UnbalancedLayer.mem_displacementSubgroup.mpr ⟨huC, hz⟩
  set T := S.map (MulAut.conj u).toMonoidHom with hT
  have hmemT : ∀ t, t ∈ T ↔ u⁻¹ * t * u ∈ S := by
    intro t
    rw [hT, mem_map_equiv, MulAut.conj_symm_apply]
  have hTC0 : T ≤ C0 := by
    intro t ht
    have h1 := hSC0 ((hmemT t).mp ht)
    have h2 := hconj u huU _ h1
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using h2
  have hTn : ∀ c ∈ C0, ∀ t ∈ T, c * t * c⁻¹ ∈ T := by
    intro c hc t ht
    rw [hmemT] at ht ⊢
    have hc' : u⁻¹ * c * u ∈ C0 := by
      simpa only [inv_inv] using hconj u⁻¹ (inv_mem huU) c hc
    have := hSnC0 _ hc' _ ht
    simpa only [mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left, inv_mul_cancel_left]
      using this
  have hTcop : Nat.Coprime p (Nat.card T) := by
    rw [hT, card_map_of_injective (MulAut.conj u).injective]
    exact hScop
  have hTO : T ≤ O := hleO T hTC0 hTn hTcop
  have hdisp : ∀ s ∈ S, s * u * s⁻¹ * u⁻¹ ∈ O := by
    intro s hs
    have h1 : u * s⁻¹ * u⁻¹ ∈ T := by
      rw [hmemT, show u⁻¹ * (u * s⁻¹ * u⁻¹) * u = s⁻¹ by group]
      exact inv_mem hs
    have h2 := mul_mem (hSO hs) (hTO h1)
    simpa only [mul_assoc] using h2
  have horb := Core.conjugate_mem_orbit hK hSC hOcop huM hua hk₀ hk₀u hdisp
  refine le_normalizer_of_coprime_orbit hScop hxn hSC fun s hs => ?_
  obtain ⟨i, hi⟩ := horb s⁻¹ (inv_mem hs)
  rw [inv_inv] at hi
  exact ⟨i, hi⟩

end NormalizationMain

section NormalizerCase

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.LBalance

theorem kGroup_quotient_of_subgroup {X : Type} [Group X] [Finite X] (hX : lBalanceIsKGroup X)
    (G' : Subgroup X) (N : Subgroup G') [N.Normal] : lBalanceIsKGroup (G' ⧸ N) := by
  have h1 : CFSG.IsKGroup X := HardMathSupport.Solomon.LocalBalance.Lemma27Ns.s1t_isKGroup_of_open hX
  have h2 : CFSG.IsKGroup G' := RankThree.PartOne.N143.isKGroup_subgroup h1 G'
  have h3 : CFSG.IsKGroup (G' ⧸ N) := RankThree.PartOne.Sec159Cfg.isKGroup_of_surjective h2
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  exact CGT.PushingUpLit.CGT6.openIsKGroup_of_isKGroup h3

theorem exists_sup_zpowers_pow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : IsPGroup p P) (hne : P ≠ ⊥) :
    ∃ Q : Subgroup X, Q ≤ P ∧ Nat.card Q < Nat.card P ∧
      ∃ x ∈ P, x ∈ normalizer (Q : Set X) ∧ P ≤ Q ⊔ zpowers x ∧ x ^ p ∈ Q := by
  have hp : p.Prime := Fact.out
  have : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hne
  have : Group.IsNilpotent P := hP.isNilpotent
  have hdvd : p ∣ Nat.card P := hP.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
  obtain ⟨Q, hindex, hQ⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
  obtain ⟨x, hx⟩ : ∃ x : P, x ∉ Q := by
    by_contra! h
    have htop : Q = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, index_top] at hindex
    exact hp.one_lt.ne hindex
  have hsup : Q ⊔ zpowers x = ⊤ := by
    have hmul := relIndex_mul_index (le_sup_left : Q ≤ Q ⊔ zpowers x)
    rw [hindex] at hmul
    rcases hp.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hmul) with h | h
    · exact index_eq_one.mp h
    · rw [h] at hmul
      have hrel : Q.relIndex (Q ⊔ zpowers x) = 1 :=
        Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans (one_mul p).symm)
      exact (hx (relIndex_eq_one.mp hrel (mem_sup_right (mem_zpowers x)))).elim
  have hxp : x ^ p ∈ Q := by
    have hcard : Nat.card (P ⧸ Q) = p := by rw [← index_eq_card]; exact hindex
    have h := pow_card_eq_one' (G := P ⧸ Q) (x := ((x : P) : P ⧸ Q))
    rw [hcard, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    exact h
  refine ⟨Q.map P.subtype, map_subtype_le Q, ?_, x, x.2, ?_, ?_, ?_⟩
  · rw [card_map_of_injective P.subtype_injective]
    have hcard := Q.card_mul_index
    rw [hindex] at hcard
    calc Nat.card Q < Nat.card Q * p := lt_mul_of_one_lt_right Nat.card_pos hp.one_lt
      _ = Nat.card P := hcard
  · have h := le_normalizer_map (H := Q) P.subtype
    rw [normalizer_eq_top Q, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h x.2
  · have h : (Q ⊔ zpowers x).map P.subtype = Q.map P.subtype ⊔ zpowers (x : X) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    refine le_of_eq ?_
    rw [← h, hsup, ← MonoidHom.range_eq_map, range_subtype]
  · exact mem_map.mpr ⟨x ^ p, hxp, by simp⟩

variable {G : Type*} [Group G] [Finite G]

theorem primeCore_conj_mem (p : ℕ) [Fact p.Prime] {Y : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Y : Set G)) {w : G} (hw : w ∈ lBalancePrimeCore p Y) :
    g * w * g⁻¹ ∈ lBalancePrimeCore p Y := by
  set O := lBalancePrimeCore p Y
  have hOY : O ≤ Y := primeCore_le p Y
  have hOn : (O.subgroupOf Y).Normal := primeCore_normal p Y
  have hOcop : Nat.Coprime p (Nat.card O) := primeCore_coprime p Y
  set T := O.map (MulAut.conj g).toMonoidHom with hT
  have hmemT : ∀ t, t ∈ T ↔ g⁻¹ * t * g ∈ O := by
    intro t
    rw [hT, mem_map_equiv, MulAut.conj_symm_apply]
  have hgY : ∀ y, y ∈ Y ↔ g * y * g⁻¹ ∈ Y := mem_normalizer_iff.mp hg
  have hTY : T ≤ Y := by
    intro t ht
    have h1 := hOY ((hmemT t).mp ht)
    have h2 := (hgY _).mp h1
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using h2
  have hTn : (T.subgroupOf Y).Normal := by
    refine ⟨fun t ht y => ?_⟩
    have ht' : (t : G) ∈ T := mem_subgroupOf.mp ht
    rw [mem_subgroupOf, coe_mul, coe_mul, coe_inv, hmemT]
    rw [hmemT] at ht'
    have hy' : g⁻¹ * (y : G) * g ∈ Y := by
      have := (hgY (g⁻¹ * (y : G) * g)).mpr (by simpa only [mul_assoc, mul_inv_cancel,
        mul_one, mul_inv_cancel_left] using y.2)
      exact this
    have := hOn.conj_mem ⟨_, hOY ht'⟩ (mem_subgroupOf.mpr ht') ⟨_, hy'⟩
    rw [mem_subgroupOf] at this
    simpa only [coe_mul, coe_inv, mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left,
      inv_mul_cancel_left] using this
  have hTcop : Nat.Coprime p (Nat.card T) := by
    rw [hT, card_map_of_injective (MulAut.conj g).injective]
    exact hOcop
  have hTO : T ≤ O := le_sSup ⟨hTY, hTn, hTcop⟩
  apply hTO
  rw [hmemT, show g⁻¹ * (g * w * g⁻¹) * g = w by group]
  exact hw

theorem primeCore_normalizer_le (p : ℕ) [Fact p.Prime] (P : Subgroup G) (hP : IsPGroup p P) :
    lBalancePrimeCore p (normalizer (P : Set G)) ≤ lBalancePrimeCore p (centralizer (P : Set G)) := by
  set N := normalizer (P : Set G)
  set O := lBalancePrimeCore p N
  have hON : O ≤ N := primeCore_le p N
  have hOcop : Nat.Coprime p (Nat.card O) := primeCore_coprime p N
  have hconjO : ∀ g ∈ N, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    primeCore_conj_mem p (show g ∈ normalizer (N : Set G) from le_normalizer hg) ho
  have hOC : O ≤ centralizer (P : Set G) := by
    intro o ho
    rw [mem_centralizer_iff]
    intro g hg
    have hgN : g ∈ N := le_normalizer hg
    have hc1 : g * o * g⁻¹ * o⁻¹ ∈ O := mul_mem (hconjO g hgN o ho) (inv_mem ho)
    have hc2 : g * o * g⁻¹ * o⁻¹ ∈ P := by
      have h1 : o * g⁻¹ * o⁻¹ ∈ P := (mem_normalizer_iff.mp (hON ho) _).mp (inv_mem hg)
      have := mul_mem hg h1
      simpa only [mul_assoc] using this
    obtain ⟨a, ha⟩ := hP ⟨_, hc2⟩
    have hca : (g * o * g⁻¹ * o⁻¹) ^ p ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this
    have h1 := Core.eq_one_of_mem_of_pow_prime_pow hOcop hc1 hca
    have h3 : g * o * g⁻¹ * o⁻¹ * (o * g) = o * g := by rw [h1, one_mul]
    have h4 : g * o = o * g := by
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h3
    exact h4
  refine le_sSup ⟨hOC, ⟨fun o ho c => ?_⟩, hOcop⟩
  rw [mem_subgroupOf] at ho ⊢
  exact hconjO c (centralizer_le_normalizer _ c.2) o ho


omit [Finite G] in
theorem mem_normalizer_inf {Y Z : Subgroup G} {c : G} (hY : c ∈ normalizer (Y : Set G))
    (hZ : c ∈ normalizer (Z : Set G)) : c ∈ normalizer ((Y ⊓ Z : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hY hZ ⊢
  intro h
  rw [mem_inf, mem_inf]
  exact and_congr (hY h) (hZ h)

omit [Finite G] in
theorem lBalancePLayer_le_self (p : ℕ) (Y : Subgroup G) : lBalancePLayer p Y ≤ Y :=
  sSup_le fun _ hL => subnormal_le hL.1

theorem commutator_mem_of_elementCase {p : ℕ} [Fact p.Prime]
    (hElt : ∀ (Z : Type) [Group Z] [Finite Z], lBalanceIsKGroup Z →
      lBalancePrimeCore p (⊤ : Subgroup Z) = ⊥ →
      ∀ x : Z, (∃ n : ℕ, x ^ p ^ n = 1) → x ^ p ∈ center Z →
        ∀ a ∈ lBalancePLayer p (centralizer ({x} : Set Z)),
          ∀ b ∈ lBalancePrimeCore p (centralizer ({x} : Set Z)), a * b = b * a)
    {X : Type} [Group X] [Finite X] (hK : lBalanceIsKGroup X) {Y : Subgroup X} {x : X}
    (hxY : x ∈ normalizer (Y : Set X)) (hxn : ∃ n : ℕ, x ^ p ^ n = 1)
    (hxp : x ^ p ∈ centralizer (Y : Set X))
    {a b : X} (ha : a ∈ lBalancePLayer p ((Y ⊔ zpowers x) ⊓ centralizer ({x} : Set X)))
    (hb : b ∈ lBalancePrimeCore p (Y ⊓ centralizer ({x} : Set X))) :
    a * b * a⁻¹ * b⁻¹ ∈ lBalancePrimeCore p Y := by
  set G' := Y ⊔ zpowers x with hG'
  have hYM : Y ≤ G' := le_sup_left
  have hxM : x ∈ G' := mem_sup_right (mem_zpowers x)
  have hMN : G' ≤ normalizer (Y : Set X) := sup_le le_normalizer (zpowers_le.mpr hxY)
  set x' : G' := ⟨x, hxM⟩ with hx'def
  have hx' : ∃ n : ℕ, x' ^ p ^ n = 1 :=
    hxn.imp fun n hn => Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hn)
  have hC : (G' ⊓ centralizer ({x} : Set X)).subgroupOf G' = centralizer ({x'} : Set G') := by
    ext y
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, true_and,
      mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  set C' := centralizer ({x'} : Set G') with hC'def
  set π := QuotientGroup.mk' (pPrimeCore p G') with hπ
  set D := centralizer ({π x'} : Set (G' ⧸ pPrimeCore p G')) with hDdef
  have hD : C'.map π = D := Quot.map_centralizer_eq hx'
  have haM : a ∈ G' := (lBalancePLayer_le_self p _ ha).1
  have hbY : b ∈ Y := (primeCore_le p _ hb).1
  set a' : G' := ⟨a, haM⟩
  set b' : G' := ⟨b, hYM hbY⟩
  have ha' : a' ∈ lBalancePLayer p C' := by
    have h := pLayer_nested_map p (G' ⊓ centralizer ({x} : Set X)) G' inf_le_left
    rw [hC] at h
    rw [← h] at ha
    obtain ⟨c, hc, hca⟩ := mem_map.mp ha
    have : c = a' := Subtype.ext hca
    rwa [← this]
  have hB1 : π a' ∈ lBalancePLayer p D := by
    have hle : (lBalancePLayer p C').map π ≤ lBalancePLayer p D := by
      rw [Asm.lBalancePLayer_eq_map p C', Asm.lBalancePLayer_eq_map p D, map_le_iff_le_comap,
        map_le_iff_le_comap]
      refine sSup_le fun K hK => ?_
      rw [← map_le_iff_le_comap, ← map_le_iff_le_comap]
      have hK' := Quot.isPComponent_map_of_map_eq hD hK
      have hKD : (K.map C'.subtype).map π ≤ D := by
        rw [← hD]
        exact map_mono (map_subtype_le K)
      have h := map_mono (f := D.subtype)
        (show ((K.map C'.subtype).map π).subgroupOf D ≤ pLayer D p from le_sSup hK')
      rwa [map_subgroupOf_eq_of_le hKD] at h
    exact hle (mem_map_of_mem π ha')
  have hB2 : π b' ∈ lBalancePrimeCore p D := by
    set W := lBalancePrimeCore p (Y ⊓ centralizer ({x} : Set X)) with hW
    have hWM : W ≤ G' := (primeCore_le p _).trans (inf_le_left.trans hYM)
    set N := (W.subgroupOf G').map π with hN
    have hWC : W.subgroupOf G' ≤ C' := by
      rw [← hC]
      intro w hw
      rw [mem_subgroupOf] at hw ⊢
      exact ⟨w.2, (primeCore_le p _ hw).2⟩
    have hND : N ≤ D := by
      rw [← hD]
      exact map_mono hWC
    have hNn : (N.subgroupOf D).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨w, hw, hwn⟩ := mem_map.mp hn
      have hg : (g : G' ⧸ pPrimeCore p G') ∈ C'.map π := by
        rw [hD]
        exact g.2
      obtain ⟨c, hc, hcg⟩ := mem_map.mp hg
      have hcC : (c : X) ∈ centralizer ({x} : Set X) := by
        have := mem_centralizer_singleton_iff.mp hc
        exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
      have hcnorm : (c : X) ∈ normalizer ((Y ⊓ centralizer ({x} : Set X) : Subgroup X) : Set X) :=
        mem_normalizer_inf (hMN c.2) (le_normalizer hcC)
      have hcw : (c : X) * (w : X) * (c : X)⁻¹ ∈ W :=
        primeCore_conj_mem p hcnorm (mem_subgroupOf.mp hw)
      have hcw' : c * w * c⁻¹ ∈ W.subgroupOf G' := by
        rw [mem_subgroupOf]
        simpa only [coe_mul, coe_inv] using hcw
      have := mem_map_of_mem π hcw'
      rw [map_mul, map_mul, map_inv, hcg, hwn] at this
      simpa only [coe_mul, coe_inv] using this
    have hNcop : Nat.Coprime p (Nat.card N) := by
      have h1 : Nat.card (W.subgroupOf G') = Nat.card W :=
        Nat.card_congr (subgroupOfEquivOfLe hWM).toEquiv
      exact (primeCore_coprime p _).coprime_dvd_right ((card_map_dvd _ _).trans h1.dvd)
    have hNO : N ≤ lBalancePrimeCore p D := le_sSup ⟨hND, hNn, hNcop⟩
    exact hNO (mem_map_of_mem π (show b' ∈ W.subgroupOf G' from mem_subgroupOf.mpr hb))
  have hKq : lBalanceIsKGroup (G' ⧸ pPrimeCore p G') :=
    kGroup_quotient_of_subgroup hK G' (pPrimeCore p G')
  have hcoreq : lBalancePrimeCore p (⊤ : Subgroup (G' ⧸ pPrimeCore p G')) = ⊥ := by
    rw [primeCore_top]
    exact pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hxq : ∃ n : ℕ, π x' ^ p ^ n = 1 := Quot.exists_mk_pow_eq_one hx'
  have hxpc : x' ^ p ∈ center G' := by
    have hle : G' ≤ centralizer ({x ^ p} : Set X) := by
      refine sup_le (fun y hy => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hxp y hy)) (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr (pow_mul_comm' x p).symm
    rw [mem_center_iff]
    intro g
    have := mem_centralizer_singleton_iff.mp (hle g.2)
    exact Subtype.ext (by simpa only [coe_mul, SubgroupClass.coe_pow] using this)
  have hxqc : π x' ^ p ∈ center (G' ⧸ pPrimeCore p G') := by
    rw [← map_pow, mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore p G') g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hxpc g]
  have hcomm := hElt (G' ⧸ pPrimeCore p G') hKq hcoreq (π x') hxq hxqc (π a') hB1 (π b') hB2
  have hker : a' * b' * a'⁻¹ * b'⁻¹ ∈ pPrimeCore p G' := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore p G'), MonoidHom.mem_ker, map_mul, map_mul, map_mul,
      map_inv, map_inv, ← hπ, hcomm]
    group
  set N₀ := (pPrimeCore p G').map G'.subtype ⊓ Y with hN₀
  have hN₀ : N₀ ≤ lBalancePrimeCore p Y := by
    refine le_sSup ⟨inf_le_right, ⟨fun n hn y => ?_⟩, ?_⟩
    · rw [mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, hn2⟩ := mem_inf.mp hn
      obtain ⟨m, hm, hmn⟩ := mem_map.mp hn1
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have hy : (y : X) ∈ G' := hYM y.2
        have := (inferInstance : (pPrimeCore p G').Normal).conj_mem m hm ⟨y, hy⟩
        refine mem_map.mpr ⟨_, this, ?_⟩
        simp only [coe_subtype, coe_mul, coe_inv] at hmn ⊢
        rw [hmn]
      · exact mul_mem (mul_mem y.2 hn2) (inv_mem y.2)
    · have h1 : Nat.card ((pPrimeCore p G').map G'.subtype) = Nat.card (pPrimeCore p G') :=
        card_map_of_injective G'.subtype_injective
      exact (pPrimeCore_coprime_card (p := p) (G := G')).coprime_dvd_right
        ((card_dvd_of_le inf_le_left).trans h1.dvd)
  apply hN₀
  refine mem_inf.mpr ⟨mem_map.mpr ⟨_, hker, rfl⟩, ?_⟩
  have h1 : a * b * a⁻¹ ∈ Y := (mem_normalizer_iff.mp (hMN haM) b).mp hbY
  exact mul_mem h1 (inv_mem hbY)

theorem centralizer_case (hS : CatalogueRelativeB.CatalogueSchreier) {p : ℕ} [Fact p.Prime]
    (hElt : ∀ (Z : Type) [Group Z] [Finite Z], lBalanceIsKGroup Z →
      lBalancePrimeCore p (⊤ : Subgroup Z) = ⊥ →
      ∀ x : Z, (∃ n : ℕ, x ^ p ^ n = 1) → x ^ p ∈ center Z →
        ∀ a ∈ lBalancePLayer p (centralizer ({x} : Set Z)),
          ∀ b ∈ lBalancePrimeCore p (centralizer ({x} : Set Z)), a * b = b * a)
    {X : Type} [Group X] [Finite X] (hK : lBalanceIsKGroup X)
    (hcore : lBalancePrimeCore p (⊤ : Subgroup X) = ⊥) (P : Subgroup X) (hP : IsPGroup p P) :
    ∀ a ∈ lBalancePLayer p (centralizer (P : Set X)),
      ∀ b ∈ lBalancePrimeCore p (centralizer (P : Set X)), a * b = b * a := by
  have hX : SchreierSections X := schreierSections_of_kGroup hS hK
  induction hn : Nat.card P using Nat.strong_induction_on generalizing P with
  | h n ih =>
  by_cases hbot : P = ⊥
  · subst hbot
    have htop : centralizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (SetLike.coe_subset_coe.mpr bot_le)
    rw [htop, hcore]
    intro a _ b hb
    rw [mem_bot.mp hb, mul_one, one_mul]
  obtain ⟨Q, hQP, hcard, x, hxP, hxQ, hPQ, hxpQ⟩ := exists_sup_zpowers_pow hP hbot
  have IH := ih (Nat.card Q) (hcard.trans_eq hn) Q (hP.to_le hQP) rfl
  have hxY := Asm.mem_normalizer_centralizer hxQ
  have hYM : centralizer (Q : Set X) ≤ centralizer (Q : Set X) ⊔ zpowers x := le_sup_left
  have hxM : x ∈ centralizer (Q : Set X) ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hMN : centralizer (Q : Set X) ⊔ zpowers x ≤ normalizer (centralizer (Q : Set X) : Set X) :=
    sup_le le_normalizer (zpowers_le.mpr hxY)
  have hCP : centralizer (P : Set X) = centralizer (Q : Set X) ⊓ centralizer ({x} : Set X) := by
    refine le_antisymm (le_inf (centralizer_le hQP)
      (centralizer_le (Set.singleton_subset_iff.mpr hxP))) ?_
    rintro z ⟨hzQ, hzx⟩
    have hle : Q ⊔ zpowers x ≤ centralizer ({z} : Set X) := by
      refine sup_le (fun q hq => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hzQ q hq)) (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hzx).symm
    exact mem_centralizer_iff.mpr fun g hg => mem_centralizer_singleton_iff.mp (hle (hPQ hg))
  rw [hCP]
  have hxp : x ^ p ∈ centralizer (centralizer (Q : Set X) : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.mp hy _ hxpQ).symm
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hxn : ∃ n : ℕ, x ^ p ^ n = 1 := ⟨k, by simpa using congrArg Subtype.val hk⟩
  have : ((centralizer (Q : Set X) ⊓ centralizer ({x} : Set X)).subgroupOf
      ((centralizer (Q : Set X) ⊔ zpowers x) ⊓ centralizer ({x} : Set X))).Normal := by
    refine (normal_subgroupOf_iff (inf_le_inf_right _ hYM)).mpr fun z c hz hc =>
      mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hMN (mem_inf.mp hc).1) z).mp (mem_inf.mp hz).1
    · exact mul_mem (mul_mem (mem_inf.mp hc).2 (mem_inf.mp hz).2) (inv_mem (mem_inf.mp hc).2)
  have h1 := pLayer_relative_normal_mono p _ _ (inf_le_inf_right (centralizer ({x} : Set X)) hYM)
  have h2 := lBalancePLayer_inf_centralizer_le (p := p) hX hxM hxn
  have : ((centralizer (Q : Set X)).subgroupOf (centralizer (Q : Set X) ⊔ zpowers x)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYM).mpr hMN
  have h3 : lBalancePLayer p (centralizer (Q : Set X) ⊔ zpowers x) ≤
      lBalancePLayer p (centralizer (Q : Set X)) := by
    refine Asm.pLayer_le_of_pComponents_le p _ _ hYM fun L hL => ?_
    have : Group.IsPerfect L := pComponent_perfect p _ L hL
    exact Asm.le_of_perfect_le_sup_zpowers hxY (subnormal_le hL.1)
  set J := lBalancePLayer p (centralizer (Q : Set X) ⊓ centralizer ({x} : Set X)) with hJ
  set W := lBalancePrimeCore p (centralizer (Q : Set X) ⊓ centralizer ({x} : Set X)) with hW
  set M := lBalancePrimeCore p (centralizer (Q : Set X)) with hM
  have hJY : J ≤ lBalancePLayer p (centralizer (Q : Set X)) := h1.trans (h2.trans h3)
  have hJW : ⁅J, W⁆ ≤ M := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact commutator_mem_of_elementCase hElt hK hxY hxn hxp (h1 ha) hb
  have hJM : ⁅J, M⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [mem_centralizer_iff]
    intro m hm
    exact (IH a (hJY ha) m hm).symm
  have hA : ⁅⁅J, W⁆, J⁆ = ⊥ := by
    refine le_bot_iff.mp ((commutator_mono hJW le_rfl).trans ?_)
    rw [commutator_comm, hJM]
  have hB : ⁅⁅W, J⁆, J⁆ = ⊥ := by rw [commutator_comm W J]; exact hA
  have hC3 : ⁅⁅J, J⁆, W⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hA hB
  have : Group.IsPerfect J := pLayer_perfect p _
  rw [commutator_eq_self] at hC3
  intro a ha b hb
  have := (commutator_eq_bot_iff_le_centralizer.mp hC3) ha
  exact (mem_centralizer_iff.mp this b hb).symm

theorem normalizer_case (hS : CatalogueRelativeB.CatalogueSchreier) {p : ℕ} (hp : p.Prime)
    (hElt : ∀ (Z : Type) [Group Z] [Finite Z], lBalanceIsKGroup Z →
      lBalancePrimeCore p (⊤ : Subgroup Z) = ⊥ →
      ∀ x : Z, (∃ n : ℕ, x ^ p ^ n = 1) → x ^ p ∈ center Z →
        ∀ a ∈ lBalancePLayer p (centralizer ({x} : Set Z)),
          ∀ b ∈ lBalancePrimeCore p (centralizer ({x} : Set Z)), a * b = b * a)
    {X : Type} [Group X] [Finite X] (hK : lBalanceIsKGroup X)
    (hcore : lBalancePrimeCore p (⊤ : Subgroup X) = ⊥) (P : Subgroup X) (hP : IsPGroup p P) :
    ∀ a ∈ lBalancePLayer p (normalizer (P : Set X)),
      ∀ b ∈ lBalancePrimeCore p (normalizer (P : Set X)), a * b = b * a := by
  have : Fact p.Prime := ⟨hp⟩
  intro a ha b hb
  exact centralizer_case hS hElt hK hcore P hP a
    (lBalancePLayer_normalizer_le_centralizer P hP ha) b (primeCore_normalizer_le p P hP hb)

end NormalizerCase

section Catalogue

open CFSG.HardMathSupport.Solomon.Coordinator

theorem catalogueBp_alternating_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (hn : 5 ≤ n) :
    CatalogueBp p (TauCeti.CFSGIndex.alternating n hn) := by
  intro S _ _ _ _ ⟨e⟩ β hβ
  let π : S →* alternatingGroup (Fin n) := e.toMonoidHom
  have hπ : Function.Surjective π := e.surjective
  have hker : π.ker ≤ Subgroup.center S := by
    have : π.ker = ⊥ := (MonoidHom.ker_eq_bot_iff π).2 e.injective
    rw [this]; exact bot_le
  let β' : MulAut (alternatingGroup (Fin n)) := MulAut.congr e β
  have hββ : ∀ k, π (β k) = β' (π k) := fun k => by simp [β', π]
  have hβ' : β' ^ p = 1 := by
    show (MulAut.congr e : MulAut S →* MulAut (alternatingGroup (Fin n))) β ^ p = 1
    rw [← map_pow, hβ, map_one]
  have hB := commutator_layer_eq_bot_A hp hp2 hn β' hβ'
  have hLmap : (GLAPLayer p (fixSubgroup β)).map π ≤ GLAPLayer p (fixSubgroup β') :=
    (map_glaPLayer_fixSubgroup_eq π hker β β' hββ hπ hp).le
  have hOmap := map_glaPPrimeCoreOf_fixSubgroup_le π hker β β' hββ hπ hp
  have hcm : (⁅GLAPLayer p (fixSubgroup β), GLAPPrimeCoreOf p (fixSubgroup β)⁆).map π = ⊥ := by
    rw [Subgroup.map_commutator]
    exact eq_bot_iff.2 (hB ▸ Subgroup.commutator_mono hLmap hOmap)
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hcm

theorem lieSemisimpleCent_of_families (h05 : LieSemisimpleCentLinearUnitary)
    (h06 : LieSemisimpleCentSymplecticOrthogonal) (h07 : LieSemisimpleCentExceptional)
    (h08 : LieSemisimpleCentSuzukiReeTits) : LieSemisimpleCent := by
  intro S _ _ hs hnc idx he p hp hp2 hpq β hβ hβ1
  cases hf : lieFamily idx.1
  · exact h05 S hs hnc idx hf he p hp hp2 hpq β hβ hβ1
  · exact h06 S hs hnc idx hf he p hp hp2 hpq β hβ hβ1
  · exact h07 S hs hnc idx hf he p hp hp2 hpq β hβ hβ1
  · exact h08 S hs hnc idx hf he p hp hp2 hpq β hβ hβ1

end Catalogue

section SporadicTwo

open CFSG.HardMathSupport.Solomon.Coordinator

theorem simpleBp_two_of_oddCore {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a)
    (h : ∀ i : MulAut S, orderOf i = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({i} : Set (MulAut S))) = ⊥) :
    SimpleBp 2 S := by
  intro β hβ
  by_cases h1 : β = 1
  · subst h1
    exact commutator_glaPLayer_eq_bot_of_perfect_le_layer (perfectInLayer_one hnc)
  suffices hO : GLAPPrimeCoreOf 2 (fixSubgroup β) = ⊥ by
    rw [hO, Subgroup.commutator_bot_right]
  have hord : orderOf β = 2 := orderOf_eq_prime hβ h1
  set C := fixSubgroup β with hC
  set O := GLAPPrimeCoreOf 2 C with hOdef
  set κ : S →* MulAut S := MulAut.conj with hκ
  have hinj : Function.Injective κ :=
    CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hnc
  set Cβ := Subgroup.centralizer ({β} : Set (MulAut S)) with hCβ
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hconj : ∀ (γ : MulAut S) (s : S), γ * κ s * γ⁻¹ = κ (γ s) := by
    intro γ s
    ext x
    simp [hκ, MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  have hκC : O.map κ ≤ Cβ := by
    rintro _ ⟨o, ho, rfl⟩
    have hfix : β o = o := hOC ho
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hconj β o
    rw [hfix] at this
    calc κ o * β = β * κ o * β⁻¹ * β := by rw [this]
      _ = β * κ o := by group
  have hγO : ∀ γ : MulAut S, γ ∈ Cβ → ∀ o ∈ O, γ o ∈ O := by
    intro γ hγ o ho
    have hcomm : γ * β = β * γ := Subgroup.mem_centralizer_singleton_iff.mp hγ
    have hCγ : C.map γ.toMonoidHom = C := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hc' : β c = c := hc
        show β (γ c) = γ c
        have := congrArg (fun f : MulAut S => f c) hcomm
        simp only [MulAut.mul_apply] at this
        rw [← this, hc']
      · intro hx
        have hx' : β x = x := hx
        refine ⟨γ⁻¹ x, ?_, by simp⟩
        show β (γ⁻¹ x) = γ⁻¹ x
        have hcomm' : γ⁻¹ * β = β * γ⁻¹ := by
          calc γ⁻¹ * β = γ⁻¹ * (β * γ) * γ⁻¹ := by group
            _ = γ⁻¹ * (γ * β) * γ⁻¹ := by rw [hcomm]
            _ = β * γ⁻¹ := by group
        have := congrArg (fun f : MulAut S => f x) hcomm'
        simp only [MulAut.mul_apply] at this
        rw [← this, hx']
    have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 2
      γ.toMonoidHom γ.injective C
    rw [hCγ] at hmap
    rw [← hOdef] at hmap
    rw [← hmap]
    exact ⟨o, ho, rfl⟩
  set T : Subgroup ↥Cβ := (O.map κ).subgroupOf Cβ with hT
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
    obtain ⟨o, ho, hto⟩ := ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hto, hconj]
    exact ⟨_, hγO g g.2 o ho, rfl⟩
  have hTodd : Odd (Nat.card T) := by
    have h1 : Nat.card T = Nat.card (O.map κ) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hκC).toEquiv
    rw [h1, Subgroup.card_map_of_injective hinj]
    exact Nat.coprime_two_left.mp (i183_coprime_card_glaPPrimeCoreOf Nat.prime_two C)
  have hTbot : T = ⊥ := by
    have hle : T ≤ CFSG.oddCore ↥Cβ := le_sSup ⟨hTn, hTodd⟩
    rw [h β hord] at hle
    exact le_bot_iff.mp hle
  refine eq_bot_iff.mpr fun o ho => ?_
  have hmem : (⟨κ o, hκC ⟨o, ho, rfl⟩⟩ : ↥Cβ) ∈ T := by
    rw [hT, Subgroup.mem_subgroupOf]
    exact ⟨o, ho, rfl⟩
  rw [hTbot, Subgroup.mem_bot] at hmem
  have : κ o = 1 := congrArg Subtype.val hmem
  exact (Subgroup.mem_bot).mpr (hinj (this.trans (map_one κ).symm))

end SporadicTwo

section SporadicTwoCertified

open CFSG.HardMathSupport.Solomon.Coordinator


theorem catalogueBp_two_sporadic (name : TauCeti.SporadicName) (hname : name ≠ .He) :
    CatalogueBp 2 (TauCeti.CFSGIndex.sporadic name) := by
  have hs : CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree name :=
    match name, hname with
    | .M11, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M11
    | .M12, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M12
    | .M22, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M22
    | .M23, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M23
    | .M24, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M24
    | .J1, _ => CFSG.ComponentClassification.Foote5.sporadicOddCoreFree_J1
    | .J2, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_J2
    | .J3, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_J3
    | .J4, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_J4
    | .HS, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_HS
    | .McL, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_McL
    | .Ru, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Ru
    | .Suz, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Suz
    | .ONan, _ => CFSG.Sporadic.ONOddCore.sporadicOddCoreFree_ONan
    | .Co1, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Co1
    | .Co2, _ => CFSG.Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
    | .Co3, _ => CFSG.Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
    | .Fi22, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Fi22
    | .Fi23, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Fi23
    | .Fi24Prime, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Fi24Prime
    | .HN, _ => CFSG.Sporadic.HNOddCore.sporadicOddCoreFree_HN
    | .Ly, _ => CFSG.Sporadic.LySchreier.sporadicOddCoreFree_Ly
    | .Th, _ => CFSG.Sporadic.ThSchreier.sporadicOddCoreFree_Th
    | .B, _ => CFSG.ComponentClassification.BMCase.sporadicOddCoreFree_B
    | .M, _ => CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M
    | .He, h => (h rfl).elim
  intro S _ _ hS hnc ⟨e⟩
  have := hS
  obtain ⟨e'⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group name
  exact simpleBp_two_of_oddCore hnc fun i hi =>
    CFSG.ComponentClassification.CatLeaf.mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hs hnc
      (e.trans e'.symm) i hi

end SporadicTwoCertified

section DefChar

open CFSG.HardMathSupport.Solomon.Coordinator


theorem simpleBp_of_inCatalog (h01 : AlternatingTwoBp) (h02 : SporadicMathieuLeechBp)
    (h03 : SporadicMonsterSectionBp) (h04 : SporadicPariahBp)
    (h05 : LieSemisimpleCentLinearUnitary) (h06 : LieSemisimpleCentSymplecticOrthogonal)
    (h07 : LieSemisimpleCentExceptional) (h08 : LieSemisimpleCentSuzukiReeTits)
    (h09 : LieDefCharOuter) (h10 : LieClassicalOddCharTwoBp) (h11 : LieExceptionalOddCharTwoBp)
    (h12 : LieEvenCharTwoBp) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Assembly.InCatalog S) {p : ℕ}
    (hp : p.Prime) : SimpleBp p S := by
  obtain ⟨i, ⟨e⟩⟩ := hcat
  have hs : IsSimpleGroup S := inferInstance
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn =>
    by_cases hp2 : p = 2
    · subst hp2
      exact h01 n hn S hs hnc ⟨e⟩
    · exact catalogueBp_alternating_odd hp hp2 n hn S hs hnc ⟨e⟩
  | sporadic name =>
    by_cases hp2 : p = 2
    · subst hp2
      by_cases hHe : name = .He
      · subst hHe
        exact h03 2 hp .He (by simp [monsterSectionNames]) (.inr rfl) S hs hnc ⟨e⟩
      · exact catalogueBp_two_sporadic name hHe S hs hnc ⟨e⟩
    have hname : name ∈ mathieuLeechNames ∨ name ∈ monsterSectionNames ∨ name ∈ pariahNames := by
      cases name <;> simp [mathieuLeechNames, monsterSectionNames, pariahNames]
    rcases hname with h | h | h
    · exact h02 p hp hp2 name h S hs hnc ⟨e⟩
    · exact h03 p hp name h (.inl hp2) S hs hnc ⟨e⟩
    · exact h04 p hp hp2 name h S hs hnc ⟨e⟩
  | lie idx =>
    by_cases hp2 : p = 2
    · subst hp2
      by_cases hc : idx.1.characteristic = 2
      · exact h12 idx hc S hs hnc ⟨e⟩
      · cases hf : lieFamily idx.1
        · exact h10 idx (.inl hf) hc S hs hnc ⟨e⟩
        · exact h10 idx (.inr hf) hc S hs hnc ⟨e⟩
        · exact h11 idx (.inl hf) hc S hs hnc ⟨e⟩
        · exact h11 idx (.inr hf) hc S hs hnc ⟨e⟩
    · have hB : BpSimpleLie := bpSimpleLie_of_defChar defCharInnerCoreFree_holds
        (lieSemisimpleCent_of_families h05 h06 h07 h08) h09
      exact hB S hs hnc ⟨idx, ⟨e⟩⟩ p hp hp2

end DefChar

section Schreier


theorem catalogueSchreier_of_certificates :
    CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier :=
  CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog CFSG.RankThree.PartOne.SPOR.schreierFor_catalog

end Schreier

section Certified

open CFSG.HardMathSupport.Solomon.Coordinator


theorem milestone_of_yardstones (h01 : AlternatingTwoBp) (h02 : SporadicMathieuLeechBp)
    (h03 : SporadicMonsterSectionBp) (h04 : SporadicPariahBp)
    (h05 : LieSemisimpleCentLinearUnitary) (h06 : LieSemisimpleCentSymplecticOrthogonal)
    (h07 : LieSemisimpleCentExceptional) (h08 : LieSemisimpleCentSuzukiReeTits)
    (h09 : LieDefCharOuter) (h10 : LieClassicalOddCharTwoBp) (h11 : LieExceptionalOddCharTwoBp)
    (h12 : LieEvenCharTwoBp) (h13 : ElementCaseBp) :
    CFSG.Open.LBalanceStatement := by
  intro X _ _ hK p hp P hP
  have hS := catalogueSchreier_of_certificates
  obtain ⟨h1, h2⟩ := CFSG.ComponentClassification.LBalance.l_balance_clauses hS X hK p hp P hP
  refine ⟨h1, h2, fun hcore => normalizer_case hS hp ?_ hK hcore P hP⟩
  intro Z _ _ hZ hZcore x hx hxc
  have hSZ := CFSG.ComponentClassification.LBalance.schreierSections_of_kGroup hS hZ
  refine h13 Z p hp hZcore (fun K hK => ⟨hSZ.outer_component K hK, ?_⟩) x hx hxc
    (fun K hK => core_normalizes_components hp hZcore hx hK)
  have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  exact simpleBp_of_inCatalog h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 hK.1.2.2
    (inCatalog_center_quotient hZ K hK) hp

end Certified

end CFSG.Yardstones.Md42047359a2a
