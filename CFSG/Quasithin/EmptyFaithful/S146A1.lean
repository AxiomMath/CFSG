module

public import CFSG.Quasithin.EmptyFaithful.S146A0
public import CFSG.GroupTheory.BaerSuzuki.Helpers
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.EmptyFaithful.S146Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

section Preim

@[expose] def preimH (H : Subgroup G) (N : Subgroup (OTwoQuot H)) : Subgroup G :=
  (N.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map H.subtype

omit [Finite G] in
theorem mem_preimH {H : Subgroup G} {N : Subgroup (OTwoQuot H)} {x : G} :
    x ∈ preimH H N ↔ ∃ hx : x ∈ H,
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨x, hx⟩ : OTwoQuot H) ∈ N := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite G] in
theorem preimH_le (H : Subgroup G) (N : Subgroup (OTwoQuot H)) : preimH H N ≤ H :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem pCoreOf_le_preimH (H : Subgroup G) (N : Subgroup (OTwoQuot H)) :
    pCoreOf 2 H ≤ preimH H N := by
  rintro x ⟨y, hy, rfl⟩
  refine mem_preimH.mpr ⟨y.2, ?_⟩
  have : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) y ∈ N
  rw [this]
  exact N.one_mem

omit [Finite G] in
theorem normalizer_preimH {H : Subgroup G} {N : Subgroup (OTwoQuot H)} [N.Normal] :
    H ≤ Subgroup.normalizer (preimH H N : Set G) := by
  have h1 : (preimH H N).subgroupOf H = N.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have : ((preimH H N).subgroupOf H).Normal := by
    rw [h1]
    exact Subgroup.Normal.comap inferInstance _
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (preimH_le H N)).mp this

end Preim

omit [Finite G] in
theorem S146A.oTwoUpper_idem (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ?_
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

theorem exists_odd_pCore_ne_bot {H : Subgroup G} (h : ¬ OddCoreModTwoTrivial H) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ CFSG.pCore q (OTwoQuot H) ≠ ⊥ := by
  unfold OddCoreModTwoTrivial at h
  push Not at h
  obtain ⟨N, hNH, hNn, hQN, hodd, hnle⟩ := h
  set π : ↥H →* OTwoQuot H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) with hπ
  set N' : Subgroup (OTwoQuot H) := (N.subgroupOf H).map π with hN'
  have hN'n : N'.Normal := Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)
  have hN'ne : N' ≠ ⊥ := by
    intro hbot
    apply hnle
    intro x hx
    have h1 : π ⟨x, hNH hx⟩ ∈ N' := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot, Subgroup.mem_bot] at h1
    exact ⟨⟨x, hNH hx⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  have hker : (⊥ : Subgroup (OTwoQuot H)).comap π = CFSG.Open.pCore 2 ↥H :=
    QuotientGroup.ker_mk' _
  have hcard : Nat.card N' = (pCoreOf 2 H).relIndex N := by
    have h1 := Subgroup.relIndex_comap (⊥ : Subgroup (OTwoQuot H)) π (N.subgroupOf H)
    rw [hker, Subgroup.relIndex_bot_left] at h1
    have h2 : (pCoreOf 2 H).relIndex N = (CFSG.Open.pCore 2 ↥H).relIndex (N.subgroupOf H) := by
      have e : pCoreOf 2 H = (CFSG.Open.pCore 2 ↥H).map H.subtype := rfl
      have e2 : N = (N.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH).symm
      calc (pCoreOf 2 H).relIndex N
          = ((CFSG.Open.pCore 2 ↥H).map H.subtype).relIndex ((N.subgroupOf H).map H.subtype) := by
            rw [← e, ← e2]
        _ = (CFSG.Open.pCore 2 ↥H).relIndex (N.subgroupOf H) :=
            Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective
    rw [h2, h1]
  have hoddN' : Odd (Nat.card N') := by rw [hcard]; exact hodd
  obtain ⟨M, hMn, hMN', hMne, hMmin⟩ := CFSG.exists_minimal_normal_le N' hN'n hN'ne
  have hoddM : Odd (Nat.card M) := Odd.of_dvd_nat hoddN' (Subgroup.card_dvd_of_le hMN')
  have hMsolv : Group.IsSolvable ↥M := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddM
  have : M.Normal := hMn
  have : CFSG.IsMinimalNormal M := ⟨fun K hK hKM => by
    by_cases hKb : K = ⊥
    · exact Or.inl hKb
    · exact Or.inr (hMmin K hK hKM hKb)⟩
  obtain ⟨q, hq, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
  have : Fact q.Prime := ⟨hq⟩
  have hMp : IsPGroup q ↥M := CFSG.IsElementaryAbelian.isPGroup q ↥M
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨n, hn⟩ := hMp.exists_card_eq
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · apply hMne
      rw [h0, pow_zero] at hn
      exact (Subgroup.card_eq_one).mp hn
    · rw [hn] at hoddM
      exact (Nat.not_even_iff_odd.mpr hoddM) (by
        exact (Nat.even_pow.mpr ⟨even_two, hpos.ne'⟩))
  refine ⟨q, hq, hq2, fun hbot => hMne ?_⟩
  have hle : M ≤ CFSG.pCore q (OTwoQuot H) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hMn hMp
  rw [hbot] at hle
  exact le_bot_iff.mp hle

theorem prime_le_card_of_pCore_ne_bot {H : Subgroup G} {q : ℕ} (hq : q.Prime)
    (h : CFSG.pCore q (OTwoQuot H) ≠ ⊥) : q ≤ Nat.card G := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := q) (G := OTwoQuot H)) ⟨x, hx⟩
  have hk' : x ^ q ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf x ∣ q ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow hq).mp hord
  have hxne : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hxne (orderOf_eq_one_iff.mp (by simpa using hjo))
  have hqx : q ∣ orderOf x := by
    rw [hjo]
    exact dvd_pow_self q hj0
  have h1 : orderOf x ∣ Nat.card (OTwoQuot H) := orderOf_dvd_natCard x
  have h2 : Nat.card (OTwoQuot H) ∣ Nat.card ↥H := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card ↥H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  exact Nat.le_of_dvd Nat.card_pos ((hqx.trans h1).trans (h2.trans h3))

omit [Finite G] in
theorem mem_of_pow_two_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G} {y : G}
    {k a : ℕ} (hy : y ^ 2 ^ a = 1) (hk : y ^ p ^ k ∈ Q) : y ∈ Q := by
  have hd : orderOf y ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hy
  have hcop : Nat.Coprime (p ^ k) (orderOf y) :=
    Nat.Coprime.coprime_dvd_right hd
      (Nat.Coprime.pow k a ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
  exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

theorem exists_redCE (h4 : Stage1461Four) {T M : Subgroup G} (S : Setting146 G T M)
    (hex : ∃ H : Subgroup G, IsHTM T M H ∧ ¬ OddCoreModTwoTrivial H) :
    ∃ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p ∧ PMaximal T M p := by
  classical
  set 𝒬 : Set ℕ := {q | q.Prime ∧ q ≠ 2 ∧ ∃ H₀ : Subgroup G, IsHTM T M H₀ ∧
    CFSG.pCore q (OTwoQuot H₀) ≠ ⊥} with h𝒬
  have hne : 𝒬.Nonempty := by
    obtain ⟨H, hH, hn⟩ := hex
    obtain ⟨q, hq, hq2, hpc⟩ := exists_odd_pCore_ne_bot hn
    exact ⟨q, hq, hq2, H, hH, hpc⟩
  have hbdd : BddAbove 𝒬 :=
    ⟨Nat.card G, fun q ⟨hqp, _, H₀, _, hpc⟩ => prime_le_card_of_pCore_ne_bot hqp hpc⟩
  set p := sSup 𝒬 with hpdef
  have hp𝒬 : p ∈ 𝒬 := Nat.sSup_mem hne hbdd
  have hmax : PMaximal T M p := fun H₀ hH₀ q hq hq2 hpc =>
    le_csSup hbdd ⟨hq, hq2, H₀, hH₀, hpc⟩
  obtain ⟨hpprime, hp2, H₁, hH₁, hpc₁⟩ := hp𝒬
  obtain ⟨H, ⟨hH, hpc⟩, hmin⟩ :=
    (InvImage.wf (fun K : Subgroup G => Nat.card K) wellFounded_lt).has_min
      {K | IsHTM T M K ∧ CFSG.pCore p (OTwoQuot K) ≠ ⊥} ⟨H₁, hH₁, hpc₁⟩
  have : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨N, hNn, hNle, hNbot, hNmin⟩ :=
    CFSG.exists_minimal_normal_le (CFSG.pCore p (OTwoQuot H)) CFSG.pCore_normal hpc
  have : N.Normal := hNn
  set π : ↥H →* OTwoQuot H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) with hπ
  set PQ : Subgroup G := preimH H N with hPQ
  have hPQH : PQ ≤ H := preimH_le H N
  have hQPQ : pCoreOf 2 H ≤ PQ := pCoreOf_le_preimH H N
  have hHPQ : H ≤ Subgroup.normalizer (PQ : Set G) := normalizer_preimH
  have hTH : T ≤ H := hH.1.1
  have hpSec : ∀ x ∈ PQ, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H := by
    intro x hx
    obtain ⟨hxH, hxN⟩ := mem_preimH.mp hx
    have hxpc : π ⟨x, hxH⟩ ∈ CFSG.pCore p (OTwoQuot H) := hNle hxN
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := OTwoQuot H)) ⟨π ⟨x, hxH⟩, hxpc⟩
    refine ⟨k, ?_⟩
    have hk' : (π ⟨x, hxH⟩) ^ p ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at hk'
    exact ⟨_, (QuotientGroup.eq_one_iff _).mp hk', rfl⟩
  have hlt : pCoreOf 2 H < PQ := by
    refine lt_of_le_of_ne hQPQ fun heq => hNbot ?_
    refine eq_bot_iff.mpr fun n hn => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H) n
    have hxPQ : (x : G) ∈ PQ := mem_preimH.mpr ⟨x.2, hn⟩
    rw [← heq] at hxPQ
    obtain ⟨y, hy, hyx⟩ := hxPQ
    have hyx' : y = x := Subtype.ext hyx
    rw [Subgroup.mem_bot, ← hyx']
    exact (QuotientGroup.eq_one_iff _).mpr hy
  have hXne : oTwoUpper PQ ≠ ⊥ := by
    intro hbot
    obtain ⟨y, hyPQ, hyQ⟩ := IsConcreteLE.exists_of_lt hlt
    obtain ⟨a, ha⟩ := exists_pow_mem_oTwoUpper PQ hyPQ
    rw [hbot, Subgroup.mem_bot] at ha
    obtain ⟨k, hk⟩ := hpSec y hyPQ
    exact hyQ (mem_of_pow_two_pow_eq_one hpprime hp2 ha hk)
  set H' : Subgroup G := PQ ⊔ T with hH'
  have hH'H : H' ≤ H := sup_le hPQH hTH
  have hH'N : H' ≤ Subgroup.normalizer (PQ : Set G) :=
    sup_le Subgroup.le_normalizer (hTH.trans hHPQ)
  have hQH' : pCoreOf 2 H ≤ H' := hQPQ.trans le_sup_left
  have hQ'ge : pCoreOf 2 H ≤ pCoreOf 2 H' :=
    le_pCoreOf_of_le_normalizer 2 hQH' (hH'H.trans (le_normalizer_pCoreOf 2 H))
      (pCoreOf_isPGroup 2 H)
  have hH'HTM : IsHTM T M H' := by
    refine ⟨⟨le_sup_right, fun hbot => hH.1.2 (le_bot_iff.mp (hbot ▸ hQ'ge))⟩, ?_⟩
    have hXH : oTwoUpper PQ ≤ H := (oTwoUpper_le PQ).trans hPQH
    have hXnorm : ((oTwoUpper PQ).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr
        (hHPQ.trans (normalizer_le_normalizer_oTwoUpper PQ))
    have h14 := h4 G T M S H hH (oTwoUpper PQ) hXne (S146A.oTwoUpper_idem PQ) hXH hXnorm
    exact fun hM => h14.2 ((sup_le_sup_right (oTwoUpper_le PQ) T).trans hM)
  have hpcH' : CFSG.pCore p (OTwoQuot H') ≠ ⊥ := by
    set π' : ↥H' →* OTwoQuot H' := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H') with hπ'
    have hPQH' : PQ ≤ H' := le_sup_left
    have hWn : ((PQ.subgroupOf H').map π').Normal :=
      Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer hPQH').mpr hH'N) π'
        (QuotientGroup.mk'_surjective _)
    have hWp : IsPGroup p ↥((PQ.subgroupOf H').map π') := by
      intro w
      obtain ⟨z, hz, hzw⟩ := w.2
      obtain ⟨k, hk⟩ := hpSec (z : G) (Subgroup.mem_subgroupOf.mp hz)
      refine ⟨k, Subtype.ext ?_⟩
      obtain ⟨y, hy, hyz⟩ := hQ'ge hk
      have hyz' : y = z ^ p ^ k := Subtype.ext hyz
      have h1 : π' (z ^ p ^ k) = 1 := (QuotientGroup.eq_one_iff _).mpr (hyz' ▸ hy)
      show (w : OTwoQuot H') ^ p ^ k = 1
      rw [← hzw, ← map_pow]
      exact h1
    have hWle : (PQ.subgroupOf H').map π' ≤ CFSG.pCore p (OTwoQuot H') :=
      CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hWn hWp
    obtain ⟨y, hyPQ, hyQ⟩ := IsConcreteLE.exists_of_lt hlt
    have hyQ' : y ∉ pCoreOf 2 H' := by
      intro hyQ'
      obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 H' ⟨y, hyQ'⟩
      obtain ⟨k, hk⟩ := hpSec y hyPQ
      exact hyQ (mem_of_pow_two_pow_eq_one hpprime hp2 (congrArg Subtype.val ha) hk)
    intro hbot
    rw [hbot, le_bot_iff] at hWle
    have h1 : π' ⟨y, hPQH' hyPQ⟩ ∈ (PQ.subgroupOf H').map π' :=
      Subgroup.mem_map_of_mem π' (Subgroup.mem_subgroupOf.mpr hyPQ)
    rw [hWle, Subgroup.mem_bot] at h1
    exact hyQ' ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  have hcard : Nat.card H ≤ Nat.card H' := not_lt.mp (hmin H' ⟨hH'HTM, hpcH'⟩)
  have hHH' : H' = H := Subgroup.eq_of_le_of_card_ge hH'H hcard
  refine ⟨H, PQ, p, ⟨hH, hpprime, hp2, hPQH, hlt, hpSec, hHH'.symm, hHPQ, ?_⟩, hmax⟩
  intro N₀ hQN₀ hN₀PQ hHN₀
  have hN₀H : N₀ ≤ H := hN₀PQ.trans hPQH
  have hN₀n : (N₀.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀H).mpr hHN₀
  set N'' : Subgroup (OTwoQuot H) := (N₀.subgroupOf H).map π with hN''
  have hN''n : N''.Normal := Subgroup.Normal.map hN₀n π (QuotientGroup.mk'_surjective _)
  have hN''le : N'' ≤ N := by
    rintro _ ⟨z, hz, rfl⟩
    have hzPQ : (z : G) ∈ PQ := hN₀PQ (Subgroup.mem_subgroupOf.mp hz)
    exact (mem_preimH.mp hzPQ).2
  by_cases hbot : N'' = ⊥
  · left
    refine le_antisymm (fun x hx => ?_) hQN₀
    have h1 : π ⟨x, hN₀H hx⟩ ∈ N'' := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot, Subgroup.mem_bot] at h1
    exact ⟨⟨x, hN₀H hx⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  · right
    have hNeq : N'' = N := hNmin N'' hN''n hN''le hbot
    refine le_antisymm hN₀PQ (fun y hy => ?_)
    obtain ⟨hyH, hyN⟩ := mem_preimH.mp hy
    have h1 : π ⟨y, hyH⟩ ∈ N'' := by rw [hNeq]; exact hyN
    obtain ⟨z, hz, hzy⟩ := h1
    have hzN₀ : (z : G) ∈ N₀ := Subgroup.mem_subgroupOf.mp hz
    have hyz : (z : G)⁻¹ * y ∈ pCoreOf 2 H := by
      have h2 : (z⁻¹ * ⟨y, hyH⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H := QuotientGroup.eq.mp hzy
      exact ⟨_, h2, rfl⟩
    have hy' : y = (z : G) * ((z : G)⁻¹ * y) := by group
    rw [hy']
    exact N₀.mul_mem hzN₀ (hQN₀ hyz)

end CFSG.Quasithin
