module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.RankThree.PGroups.SolvableTrivialComplementCore
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Fit

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem pCore_quotient_pCore_eq_bot : CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
  set N := CFSG.pCore 2 X with hN
  set Q := CFSG.pCore 2 (X ⧸ N) with hQ
  have hQnorm : Q.Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hpre : (Q.comap (QuotientGroup.mk' N)).Normal := hQnorm.comap _
  have hpre2 : IsPGroup 2 (Q.comap (QuotientGroup.mk' N)) := by
    intro x
    obtain ⟨a, ha⟩ := hQ2 ⟨QuotientGroup.mk' N (x : X), x.2⟩
    have ha' : QuotientGroup.mk' N ((x : X) ^ (2 ^ a)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have hmem : (x : X) ^ (2 ^ a) ∈ N := (QuotientGroup.eq_one_iff _).mp ha'
    obtain ⟨b, hb⟩ := hN2 ⟨(x : X) ^ (2 ^ a), hmem⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((x : X) ^ (2 ^ a)) ^ (2 ^ b) = 1 := congrArg Subtype.val hb
    rw [← pow_mul, ← pow_add] at hb'
    exact hb'
  have hle : Q.comap (QuotientGroup.mk' N) ≤ N := le_sSup ⟨hpre, hpre2⟩
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have : x ∈ N := hle hq
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr this)

theorem odd_card_fitting_quotient :
    Odd (Nat.card (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X)) := by
    rcases Nat.even_or_odd (Nat.card (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X))) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X))) := inferInstance
  have hP : (P : Subgroup (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X))) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card P h2
  have hle := Sylow.map_le_pCore (inferInstance : (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X)).Normal)
    (inferInstance : Group.IsNilpotent ↥(CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X))) 2 P
  rw [pCore_quotient_pCore_eq_bot, le_bot_iff] at hle
  exact hP ((Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hle)

@[expose] def oTwoFSub (X : Type*) [Group X] : Subgroup X :=
  (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.pCore 2 X))

omit [Finite X] in
instance normal_oTwoFSub : (oTwoFSub X).Normal :=
  Subgroup.Normal.comap inferInstance _

omit [Finite X] in
theorem pCore_le_oTwoFSub : CFSG.pCore 2 X ≤ oTwoFSub X := fun x hx => by
  show QuotientGroup.mk' (CFSG.pCore 2 X) x ∈ CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact Subgroup.one_mem _

theorem mem_pCore_of_two_pow_eq_one {x : X} (hx : x ∈ oTwoFSub X) {k : ℕ} (hk : x ^ (2 ^ k) = 1) :
    x ∈ CFSG.pCore 2 X := by
  have hF : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈ CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X) := hx
  set y : ↥(CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X)) := ⟨QuotientGroup.mk' (CFSG.pCore 2 X) x, hF⟩
    with hy
  have h1 : orderOf y ∣ Nat.card (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X)) :=
    orderOf_dvd_natCard y
  have h2 : orderOf y ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    show (QuotientGroup.mk' (CFSG.pCore 2 X) x) ^ (2 ^ k) = 1
    rw [← map_pow, hk, map_one]
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr odd_card_fitting_quotient)
  have h3 : orderOf y ∣ Nat.gcd (2 ^ k) (Nat.card (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X))) :=
    Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one] at h3
  have h4 : y = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have h5 : QuotientGroup.mk' (CFSG.pCore 2 X) x = 1 := congrArg Subtype.val h4
  exact (QuotientGroup.eq_one_iff x).mp h5

theorem isSolvable_oTwoFSub : Group.IsSolvable ↥(oTwoFSub X) := by
  set K₀ := oTwoFSub X with hK₀
  set N := CFSG.pCore 2 X with hN
  have hNK : N ≤ K₀ := pCore_le_oTwoFSub
  let g : ↥K₀ →* ↥(CFSG.fittingSubgroup (X ⧸ N)) :=
    ((QuotientGroup.mk' N).comp K₀.subtype).codRestrict _ (fun x => x.2)
  let f : ↥(N.subgroupOf K₀) →* ↥K₀ := (N.subgroupOf K₀).subtype
  have hN2 : IsPGroup 2 (N.subgroupOf K₀) :=
    (CFSG.pCore_isPGroup : IsPGroup 2 ↥N).of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(N.subgroupOf K₀) := hN2.isNilpotent
  have : Group.IsSolvable ↥(N.subgroupOf K₀) := inferInstance
  have : Group.IsSolvable ↥(CFSG.fittingSubgroup (X ⧸ N)) := inferInstance
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro x hx
  have hx1 : QuotientGroup.mk' N (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hxN : (x : X) ∈ N := (QuotientGroup.eq_one_iff _).mp hx1
  exact ⟨⟨x, hxN⟩, rfl⟩

theorem pPrimeCore_oTwoFSub_eq_bot (hO : fusionOddCore X = ⊥) :
    CFSG.pPrimeCore 2 ↥(oTwoFSub X) = ⊥ := by
  set K₀ := oTwoFSub X with hK₀
  set P := CFSG.pPrimeCore 2 ↥K₀ with hP
  have hnorm : (P.map K₀.subtype).Normal := by
    have hchar := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := K₀) P
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (K₀ : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact (normal_oTwoFSub (X := X)).conj_mem h hh g
      · intro hh
        have := (normal_oTwoFSub (X := X)).conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this
    exact (Subgroup.mem_normalizer_iff.mp (hchar hg) n).mp hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (P.map K₀.subtype)) := by
    rw [Subgroup.card_map_of_injective K₀.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hle : P.map K₀.subtype ≤ fusionOddCore X := le_sSup ⟨hnorm, hodd⟩
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K₀.subtype_injective] at hle
  exact hle

theorem isCharacteristicP_oTwoFSub (hO : fusionOddCore X = ⊥) :
    CFSG.IsCharacteristicP 2 ↥(oTwoFSub X) := by
  have := isSolvable_oTwoFSub (X := X)
  exact CFSG.RankThree.PGroups.solvable_trivial_complement_core Nat.prime_two
    (pPrimeCore_oTwoFSub_eq_bot hO)

theorem odd_card_oTwoFSub_quotient :
    Odd (Nat.card (↥(oTwoFSub X) ⧸ CFSG.pCore 2 ↥(oTwoFSub X))) := by
  by_contra hodd
  set K₀ := oTwoFSub X with hK₀
  have h2 : 2 ∣ Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := by
    rcases Nat.even_or_odd (Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hy2 : y ^ 2 ∈ CFSG.pCore 2 ↥K₀ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have := pow_orderOf_eq_one (QuotientGroup.mk y : ↥K₀ ⧸ CFSG.pCore 2 ↥K₀)
    rwa [hq] at this
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥K₀)) ⟨y ^ 2, hy2⟩
  have hm' : (y ^ 2) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  have hy : (y : X) ^ (2 ^ (m + 1)) = 1 := by
    have h1 : y ^ (2 ^ (m + 1)) = 1 := by
      rw [pow_succ', pow_mul]
      exact hm'
    exact (congrArg Subtype.val h1 : ((y ^ (2 ^ (m + 1)) : ↥K₀) : X) = ((1 : ↥K₀) : X))
  have hyN : (y : X) ∈ CFSG.pCore 2 X := mem_pCore_of_two_pow_eq_one y.2 hy
  have hsub : (CFSG.pCore 2 X).subgroupOf K₀ ≤ CFSG.pCore 2 ↥K₀ := by
    refine le_sSup ⟨Subgroup.normal_subgroupOf, ?_⟩
    exact (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 X)).of_equiv
      (Subgroup.subgroupOfEquivOfLe pCore_le_oTwoFSub).symm
  have hyp : y ∈ CFSG.pCore 2 ↥K₀ := hsub hyN
  have h1 : orderOf (QuotientGroup.mk y : ↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = 1 := by
    rw [(QuotientGroup.eq_one_iff y).mpr hyp, orderOf_one]
  omega

end Fit

section GLevel

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem fusionOddCore_eq_bot_of_oddCoreIn {H : Subgroup G} (hO : oddCoreIn H = ⊥) :
    fusionOddCore ↥H = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hO

omit [Finite G] in
theorem oTwoFIn_eq_map (H : Subgroup G) : oTwoFIn H = (oTwoFSub ↥H).map H.subtype := rfl

omit [Finite G] in
theorem oTwoFIn_le (H : Subgroup G) : oTwoFIn H ≤ H := Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_normalizer_oTwoFIn (H : Subgroup G) : H ≤ Subgroup.normalizer (oTwoFIn H : Set G) := by
  have key : ∀ x ∈ H, ∀ k ∈ oTwoFIn H, x * k * x⁻¹ ∈ oTwoFIn H := by
    intro x hx k hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact ⟨(⟨x, hx⟩ : ↥H) * k' * (⟨x, hx⟩ : ↥H)⁻¹,
      (normal_oTwoFSub (X := ↥H)).conj_mem k' hk' ⟨x, hx⟩, rfl⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact fun hk => key x hx k hk
  · intro hk
    have := key x⁻¹ (H.inv_mem hx) _ hk
    simpa [mul_assoc] using this

theorem charTwo_oTwoFIn {H : Subgroup G} (hO : oddCoreIn H = ⊥) : CharTwo (oTwoFIn H) := by
  have h := isCharacteristicP_oTwoFSub (X := ↥H) (fusionOddCore_eq_bot_of_oddCoreIn hO)
  have h0 : Subgroup.centralizer (CFSG.pCore 2 ↥(oTwoFSub ↥H) : Set ↥(oTwoFSub ↥H)) ≤
      CFSG.pCore 2 ↥(oTwoFSub ↥H) := h
  have h' : Subgroup.centralizer (CFSG.Open.pCore 2 ↥(oTwoFSub ↥H) : Set ↥(oTwoFSub ↥H)) ≤
      CFSG.Open.pCore 2 ↥(oTwoFSub ↥H) := by
    exact h0
  exact charTwo_map_subtype (K := H) (L := oTwoFSub ↥H) h'

theorem odd_card_oTwoFIn_quotient (H : Subgroup G) :
    Odd (Nat.card (↥(oTwoFIn H) ⧸ CFSG.pCore 2 ↥(oTwoFIn H))) := by
  have h := odd_card_oTwoFSub_quotient (X := ↥H)
  set K₀ := oTwoFSub ↥H with hK₀
  let e : ↥K₀ ≃* ↥(K₀.map H.subtype) := K₀.equivMapOfInjective H.subtype H.subtype_injective
  have hcore : (CFSG.pCore 2 ↥K₀).map e.toMonoidHom = CFSG.pCore 2 ↥(K₀.map H.subtype) :=
    CFSG.pCore_map_iso 2 e
  have hidx : (CFSG.pCore 2 ↥(K₀.map H.subtype)).index = (CFSG.pCore 2 ↥K₀).index := by
    rw [← hcore]
    exact Subgroup.index_map_equiv _ e
  have h2 : Odd (CFSG.pCore 2 ↥(K₀.map H.subtype)).index := by
    rw [hidx]
    exact h
  exact h2

theorem oTwoFIn_le_of_two {H M : Subgroup G} (hMH : M ≤ H) (hO : oddCoreIn H = ⊥)
    (h2 : ∀ K : Subgroup G, K ≤ H → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
      M ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ M) : oTwoFIn H ≤ M :=
  h2 _ (oTwoFIn_le H) (odd_card_oTwoFIn_quotient H) (hMH.trans (le_normalizer_oTwoFIn H))
    (charTwo_oTwoFIn hO)

end GLevel

end CFSG.Quasithin
