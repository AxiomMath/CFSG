module

public import CFSG.Open.QuasithinDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.Quasithin.I4

open CFSG.Open

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {z x : G} (hz : orderOf z = 2)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem conj_eq_of_mem_zpowers {z h y : G} (hh : Commute h z) (hy : y ∈ Subgroup.zpowers z) :
    h * y * h⁻¹ = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [(hh.zpow_right k).eq, mul_inv_cancel_right]

theorem normalizer_zpowers_eq_centralizer {z : G} (hz : orderOf z = 2) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) = Subgroup.centralizer {z} := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hmem : g * z * g⁻¹ ∈ Subgroup.zpowers z := (h z).mp (Subgroup.mem_zpowers z)
    rcases eq_one_or_eq_of_mem_zpowers hz hmem with h1 | h1
    · refine absurd ?_ hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h1]
  · intro hg x
    have hc : Commute g z := hg
    constructor
    · intro hx
      rwa [conj_eq_of_mem_zpowers hc hx]
    · intro hx
      have hx' := conj_eq_of_mem_zpowers hc.inv_left hx
      rw [inv_inv] at hx'
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, hx']
      exact hx

theorem le_centralizer_of_mem_center {T : Subgroup G} {z : T} (hz : z ∈ Subgroup.center T) :
    T ≤ Subgroup.centralizer {(z : G)} := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨t, ht⟩)

theorem isTwoLocal_centralizer {z : G} (hz : orderOf z = 2) :
    IsTwoLocal (Subgroup.centralizer ({z} : Set G)) := by
  refine ⟨Subgroup.zpowers z, ?_, ?_, (normalizer_zpowers_eq_centralizer hz).symm⟩
  · intro h
    have : z ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers z
    rw [Subgroup.mem_bot] at this
    rw [this] at hz
    simp at hz
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])

variable [Finite G]

theorem eq_bot_of_normal_of_coprime_of_le {H N : Subgroup G}
    (hH : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hodd : Nat.Coprime 2 (Nat.card N)) : N = ⊥ := by
  set P := pCoreOf 2 H with hPdef
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hPH : P ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hPn : (P.subgroupOf H).Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_normal 2 H
  have hdisj : N ⊓ P = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_right k hodd.symm
  have hNP : N ≤ P := by
    intro n hn
    apply hH
    refine Subgroup.mem_inf.mpr ⟨hNH hn, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hdisj' : Disjoint (N.subgroupOf H) (P.subgroupOf H) := by
      rw [Subgroup.disjoint_def]
      intro y hyN hyP
      have hy : (y : G) ∈ N ⊓ P := Subgroup.mem_inf.mpr ⟨hyN, hyP⟩
      rw [hdisj, Subgroup.mem_bot] at hy
      exact Subtype.ext hy
    have hcomm := Subgroup.commute_of_normal_of_disjoint (N.subgroupOf H) (P.subgroupOf H) hN
      hPn hdisj' ⟨n, hNH hn⟩ ⟨x, hPH hx⟩ hn hx
    exact (congrArg Subtype.val hcomm.eq).symm
  rw [eq_bot_iff, ← hdisj]
  exact fun n hn => ⟨hn, hNP hn⟩

theorem eq_bot_of_normal_of_coprime (hE : quasithinEvenCharacteristic G) {H N : Subgroup G}
    (hH : IsTwoLocal H) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ H) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hodd : Nat.Coprime 2 (Nat.card N)) : N = ⊥ :=
  eq_bot_of_normal_of_coprime_of_le (hE H hH hS) hNH hN hodd

theorem pPrimeCore_eq_bot_of_le {H : Subgroup G}
    (hH : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H) :
    CFSG.pPrimeCore 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := (CFSG.pPrimeCore 2 H).map H.subtype with hNdef
  have hNH : N ≤ H := Subgroup.map_subtype_le _
  have hNsub : N.subgroupOf H = CFSG.pPrimeCore 2 H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hN : (N.subgroupOf H).Normal := by
    rw [hNsub]
    infer_instance
  have hodd : Nat.Coprime 2 (Nat.card N) := by
    rw [hNdef, Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hbot := eq_bot_of_normal_of_coprime_of_le hH hNH hN hodd
  rwa [hNdef, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot

theorem pPrimeCore_centralizer_eq_bot (hE : quasithinEvenCharacteristic G) {z : G}
    (hz : orderOf z = 2) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer {z}) :
    CFSG.pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) = ⊥ :=
  pPrimeCore_eq_bot_of_le (hE _ (isTwoLocal_centralizer hz) hS)

omit [Finite G] in
theorem orderOf_mul_eq_two {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b)
    (hc : a * b = b * a) : orderOf (a * b) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
    rw [(Commute.mul_pow hc 2), ha2, hb2, one_mul]
  · intro h
    apply hab
    have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
    have hbinv : b⁻¹ = b := by
      rw [inv_eq_iff_mul_eq_one, ← sq, hb2]
    rw [← hbinv]
    exact eq_inv_of_mul_eq_one_left h

theorem eq_bot_of_inf_centralizer_eq_bot {K : Subgroup G} [K.Normal]
    (hK : ∀ u : G, orderOf u = 2 → K ⊓ Subgroup.centralizer {u} = ⊥)
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hc : a * b = b * a) :
    K = ⊥ := by
  have hinv : ∀ u : G, orderOf u = 2 → ∀ k ∈ K, u * k * u⁻¹ = k⁻¹ := by
    intro u hu k hk
    have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
    let φ : MulAut K := MulAut.conjNormal u
    have hφ : ∀ x : K, (φ x : G) = u * x * u⁻¹ := fun x => MulAut.conjNormal_apply u x
    have hfree : MonoidHom.FixedPointFree φ := by
      intro x hx
      have hx' : (x : G) ∈ K ⊓ Subgroup.centralizer {u} := by
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg Subtype.val hx
        rw [hφ] at h
        calc (x : G) * u = u * x * u⁻¹ * u := by rw [h]
          _ = u * x := by group
      rw [hK u hu, Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have huu : u * u = 1 := by rw [← sq]; exact hu2
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    have hinvol : Function.Involutive φ := by
      intro x
      apply Subtype.ext
      rw [hφ, hφ, hui]
      calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [huu, one_mul, mul_one]
    have h := congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨k, hk⟩
    have h' := congrArg Subtype.val h
    rwa [hφ] at h'
  have hab2 := orderOf_mul_eq_two ha hb hab hc
  rw [eq_bot_iff, ← hK (a * b) hab2]
  intro k hk
  refine Subgroup.mem_inf.mpr ⟨hk, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hk' : (a * b) * k * (a * b)⁻¹ = k := by
    have e1 : (a * b) * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
    rw [e1, hinv b hb k hk]
    have e2 : a * k⁻¹ * a⁻¹ = (a * k * a⁻¹)⁻¹ := by group
    rw [e2, hinv a ha k hk, inv_inv]
  calc k * (a * b) = (a * b) * k * (a * b)⁻¹ * (a * b) := by rw [hk']
    _ = (a * b) * k := by group

omit [Finite G] in
theorem inf_centralizer_eq_bot_of_isConj {K : Subgroup G} [K.Normal] {z u : G}
    (hKz : K ⊓ Subgroup.centralizer {z} = ⊥) (hzu : IsConj z u) :
    K ⊓ Subgroup.centralizer {u} = ⊥ := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hzu
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hxC
  have hy : c⁻¹ * x * c ∈ K ⊓ Subgroup.centralizer {z} := by
    refine Subgroup.mem_inf.mpr ⟨by simpa using (inferInstance : K.Normal).conj_mem x hxK c⁻¹, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * x * c * z = c⁻¹ * (x * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * x) * c := by rw [hxC]
      _ = z * (c⁻¹ * x * c) := by group
  rw [hKz, Subgroup.mem_bot] at hy
  rw [Subgroup.mem_bot]
  calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    _ = 1 := by rw [hy]; group

theorem eq_bot_of_isConj_of_inf_centralizer_eq_bot {K : Subgroup G} [K.Normal] {z : G}
    (hKz : K ⊓ Subgroup.centralizer {z} = ⊥) (hinv : ∀ u : G, orderOf u = 2 → IsConj z u)
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hc : a * b = b * a) :
    K = ⊥ :=
  eq_bot_of_inf_centralizer_eq_bot
    (fun u hu => inf_centralizer_eq_bot_of_isConj hKz (hinv u hu)) ha hb hab hc

omit [Finite G] in
theorem map_centralizer_singleton {H : Type*} [Group H] (f : G ≃* H) (z : G) :
    (Subgroup.centralizer ({z} : Set G)).map f.toMonoidHom = Subgroup.centralizer {f z} := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg f h
  · intro h
    apply f.injective
    simpa using h

omit [Finite G] in
theorem card_centralizer_map {H : Type*} [Group H] (f : G ≃* H) (z : G) :
    Nat.card (Subgroup.centralizer ({f z} : Set H)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  rw [← map_centralizer_singleton f z]
  exact (Nat.card_congr ((Subgroup.centralizer {z}).equivMapOfInjective f.toMonoidHom
    f.injective).toEquiv).symm

omit [Finite G] in
theorem mem_of_odd_index {N : Subgroup G} [N.Normal] (hN : Odd N.index) {x : G} {k : ℕ}
    (hx : orderOf x = 2 ^ k) : x ∈ N := by
  rw [← QuotientGroup.eq_one_iff, ← orderOf_eq_one_iff]
  have h1 : orderOf (x : G ⧸ N) ∣ 2 ^ k := hx ▸ orderOf_map_dvd (QuotientGroup.mk' N) x
  have h2 : orderOf (x : G ⧸ N) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hodd : Odd (2 ^ j) := hj ▸ Odd.of_dvd_nat hN h2
  have hj0 : j = 0 := by
    by_contra hj0
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  rw [hj, hj0, pow_zero]

omit [Finite G] in
theorem le_of_odd_index {N P : Subgroup G} [N.Normal] (hN : Odd N.index) (hP : IsPGroup 2 P) :
    P ≤ N := by
  intro x hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  exact mem_of_odd_index hN (k := k) (by rw [← Subgroup.orderOf_mk x hx]; exact hk)

theorem index_centralizer_eq_ncard {z : G} (hz : orderOf z = 2)
    (hinv : ∀ u : G, orderOf u = 2 → IsConj z u) :
    (Subgroup.centralizer ({z} : Set G)).index = {u : G | orderOf u = 2}.ncard := by
  have horb : MulAction.orbit (ConjAct G) z = {u : G | orderOf u = 2} := by
    ext u
    rw [ConjAct.mem_orbit_conjAct]
    constructor
    · intro h
      obtain ⟨c, rfl⟩ := isConj_iff.mp h.symm
      change orderOf (MulAut.conj c z) = 2
      rw [MulEquiv.orderOf_eq, hz]
    · intro hu
      exact (hinv u hu).symm
  have hstab := MulAction.index_stabilizer (ConjAct G) z
  rw [horb] at hstab
  rw [← hstab]
  have h1 := (Subgroup.centralizer ({z} : Set G)).index_mul_card
  have h2 := (MulAction.stabilizer (ConjAct G) z).index_mul_card
  rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h2
  have h3 : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.toConjAct.toEquiv.symm
  rw [h3, ← h1] at h2
  have hpos : 0 < Nat.card (Subgroup.centralizer ({z} : Set G)) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

theorem eq_top_of_involutions {L : Subgroup G} [L.Normal] (hL : Odd L.index) {z : G}
    (hz : orderOf z = 2) (hzL : z ∈ L) (hCL : Subgroup.centralizer ({z} : Set G) ≤ L)
    (hinvG : ∀ u : G, orderOf u = 2 → IsConj z u)
    (hinvL : ∀ u : L, orderOf u = 2 → IsConj (⟨z, hzL⟩ : L) u) : L = ⊤ := by
  set z' : L := ⟨z, hzL⟩ with hz'def
  have hz' : orderOf z' = 2 := by rw [hz'def, Subgroup.orderOf_mk, hz]
  have hG := index_centralizer_eq_ncard hz hinvG
  have hL' := index_centralizer_eq_ncard hz' hinvL
  have hset : {u : G | orderOf u = 2} = Subtype.val '' {u : L | orderOf u = 2} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hu
      have huL : u ∈ L := mem_of_odd_index hL (k := 1) (by rw [hu, pow_one])
      exact ⟨⟨u, huL⟩, by rw [Subgroup.orderOf_mk, hu], rfl⟩
    · rintro ⟨v, hv, rfl⟩
      rwa [Subgroup.orderOf_coe]
  have hncard : {u : G | orderOf u = 2}.ncard = {u : L | orderOf u = 2}.ncard := by
    rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hCsub : Subgroup.centralizer ({z'} : Set L) = (Subgroup.centralizer {z}).subgroupOf L := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hCcard : Nat.card (Subgroup.centralizer ({z'} : Set L)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    rw [hCsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCL).toEquiv
  apply Subgroup.eq_top_of_card_eq
  rw [← (Subgroup.centralizer ({z'} : Set L)).index_mul_card,
    ← (Subgroup.centralizer ({z} : Set G)).index_mul_card, hG, hL', hncard, hCcard]

theorem exists_index_two_of_index_eq_two_mul_odd {N : Subgroup G} [N.Normal] {m : ℕ}
    (hm : Odd m) (hN : N.index = 2 * m) : ∃ M : Subgroup G, M.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : Nat.card (G ⧸ N) = 2 * m := by rw [← Subgroup.index_eq_card, hN]
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 (G ⧸ N)))
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hfac : (2 * m).factorization 2 = 1 := by
    rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm)
        (even_iff_two_dvd.mpr h))]
  have hP : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, hQ, hfac, pow_one]
  have hPc : IsCyclic P := isCyclic_of_prime_card hP
  have hp : (Nat.card (G ⧸ N)).minFac = 2 := by
    rw [Nat.minFac_eq_two_iff, hQ]
    exact dvd_mul_right 2 m
  obtain ⟨K, hK⟩ : ∃ K : Subgroup (G ⧸ N), K.IsComplement' P :=
    ⟨_, IsCyclic.isComplement' hp hPc⟩
  refine ⟨K.comap (QuotientGroup.mk' N), ?_⟩
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N),
    hK.symm.index_eq_card, hP]

omit [Finite G] in
theorem index_ne_two_of_isSimpleGroup [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (M : Subgroup G) : M.index ≠ 2 := by
  intro hM
  have : M.Normal := Subgroup.normal_of_index_eq_two hM
  rcases this.eq_bot_or_eq_top with rfl | rfl
  · rw [Subgroup.index_bot] at hM
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite G := Nat.finite_of_card_ne_zero (by omega)
    have hcyc : IsCyclic G := isCyclic_of_prime_card hM
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (hcyc.commGroup.mul_comm a b)
  · rw [Subgroup.index_top] at hM
    omega

end CFSG.Quasithin.I4
