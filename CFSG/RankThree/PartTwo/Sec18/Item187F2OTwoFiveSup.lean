module

public import CFSG.RankThree.PartTwo.Sec18.Item187F2OTwoFive
public import CFSG.RankThree.PartTwo.Sec18.Item187F1Hall
public import CFSG.RankThree.PartTwo.Sec18.Item187Frattini

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools

section Helpers

variable {T : Type} [Group T]

theorem char_comap_mk (K : Subgroup T) [K.Normal] [K.Characteristic]
    (L : Subgroup (T ⧸ K)) [L.Characteristic] :
    (L.comap (QuotientGroup.mk' K)).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro σ
  have hKσ : K.map σ.toMonoidHom = K :=
    (Subgroup.map_equiv_eq_comap_symm σ K).trans
      (Subgroup.characteristic_iff_comap_eq.mp inferInstance σ.symm)
  set σ' : T ⧸ K ≃* T ⧸ K := QuotientGroup.congr K K σ hKσ with hσ'
  have hcomm : ∀ x : T, QuotientGroup.mk' K (σ x) = σ' (QuotientGroup.mk' K x) :=
    fun x => rfl
  have hL : L.comap σ'.toMonoidHom = L :=
    Subgroup.characteristic_iff_comap_eq.mp inferInstance σ'
  ext x
  change QuotientGroup.mk' K (σ x) ∈ L ↔ QuotientGroup.mk' K x ∈ L
  rw [hcomm]
  conv_rhs => rw [← hL]
  rfl

theorem relIndex_normal_comap_mk (N : Subgroup T) [N.Normal] (L : Subgroup (T ⧸ N)) :
    N.relIndex (L.comap (QuotientGroup.mk' N)) = Nat.card L := by
  have hA : ((⊥ : Subgroup (T ⧸ N)).comap (QuotientGroup.mk' N)).relIndex
      (L.comap (QuotientGroup.mk' N)) = Nat.card L := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective N), top_inf_eq, Subgroup.relIndex_bot_left]
  have hB : (⊥ : Subgroup (T ⧸ N)).comap (QuotientGroup.mk' N) = N := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [hB] at hA
  exact hA

theorem relIndex_comap_mk_comap (N : Subgroup T) [N.Normal] {R W : Subgroup (T ⧸ N)} :
    (R.comap (QuotientGroup.mk' N)).relIndex (W.comap (QuotientGroup.mk' N)) = R.relIndex W := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr
    (QuotientGroup.mk'_surjective N), top_inf_eq]

end Helpers

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

omit [Finite G] in
theorem le_sup_of_two_pow_relIndex {P T V : Subgroup G} (hPV : P ≤ V) (hTV : T ≤ V)
    (hP2 : ∃ k : ℕ, P.relIndex V = 2 ^ k) (hT : ¬ 2 ∣ T.relIndex V) : V ≤ P ⊔ T := by
  obtain ⟨k, hk⟩ := hP2
  have hKV : P ⊔ T ≤ V := sup_le hPV hTV
  have h1 : P.relIndex V = P.relIndex (P ⊔ T) * (P ⊔ T).relIndex V :=
    (Subgroup.relIndex_mul_relIndex P (P ⊔ T) V le_sup_left hKV).symm
  have h2 : T.relIndex V = T.relIndex (P ⊔ T) * (P ⊔ T).relIndex V :=
    (Subgroup.relIndex_mul_relIndex T (P ⊔ T) V le_sup_right hKV).symm
  have hdvd : (P ⊔ T).relIndex V ∣ 2 ^ k := by
    rw [← hk]
    exact Dvd.intro_left _ h1.symm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    apply hT
    rw [h2, hj]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hne) _
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

abbrev ZQuot (X : Subgroup G) : Type := ↥X ⧸ CFSG.pCore 2 ↥X

abbrev YQuot (X : Subgroup G) : Type := ZQuot X ⧸ CFSG.pCore 5 (ZQuot X)

@[expose] noncomputable def oTwoFiveOv (X : Subgroup G) : Subgroup ↥X :=
  ((CFSG.pCore 2 (YQuot X)).comap (QuotientGroup.mk' (CFSG.pCore 5 (ZQuot X)))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X))

theorem oTwoFiveOv_characteristic (X : Subgroup G) : (oTwoFiveOv X).Characteristic := by
  unfold oTwoFiveOv
  haveI : ((CFSG.pCore 2 (YQuot X)).comap
      (QuotientGroup.mk' (CFSG.pCore 5 (ZQuot X)))).Characteristic :=
    char_comap_mk (CFSG.pCore 5 (ZQuot X)) (CFSG.pCore 2 (YQuot X))
  exact char_comap_mk (CFSG.pCore 2 ↥X) _

omit [Finite G] in
theorem oTwoP_le_oTwoFiveOv (X : Subgroup G) : Sec4.oTwoP 5 ↥X ≤ oTwoFiveOv X := by
  intro y hy
  have h1 : QuotientGroup.mk' (CFSG.pCore 5 (ZQuot X))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) = 1 :=
    (QuotientGroup.eq_one_iff (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y)).2 hy
  show QuotientGroup.mk' (CFSG.pCore 5 (ZQuot X))
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ∈ CFSG.pCore 2 (YQuot X)
  rw [h1]
  exact one_mem _

omit [Finite G] in
theorem relIndex_oTwoP_oTwoFiveOv (X : Subgroup G) :
    (Sec4.oTwoP 5 ↥X).relIndex (oTwoFiveOv X) = Nat.card (CFSG.pCore 2 (YQuot X)) := by
  unfold oTwoFiveOv Sec4.oTwoP
  rw [relIndex_comap_mk_comap, relIndex_normal_comap_mk]

omit [Finite G] in
theorem relIndex_oTwoFive_oTwoFiveOv (X : Subgroup G) :
    (oTwoFive X).relIndex ((oTwoFiveOv X).map X.subtype) =
      Nat.card (CFSG.pCore 2 (YQuot X)) := by
  unfold oTwoFive
  rw [Subgroup.relIndex_map_map_of_injective _ _ X.subtype_injective]
  exact relIndex_oTwoP_oTwoFiveOv X

theorem relIndex_oTwoFive_two_pow (X : Subgroup G) :
    ∃ k : ℕ, (oTwoFive X).relIndex ((oTwoFiveOv X).map X.subtype) = 2 ^ k := by
  rw [relIndex_oTwoFive_oTwoFiveOv]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := YQuot X))

theorem normalizer_le_normalizer_oTwoFiveOv (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((oTwoFiveOv X).map X.subtype : Set G) := by
  haveI := oTwoFiveOv_characteristic X
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (oTwoFiveOv X)

theorem mem_pCoreOf_two_of_mem_oTwoFive_of_pow {x : G} (hx : x ∈ oTwoFive X)
    (h2 : ∃ n : ℕ, x ^ 2 ^ n = 1) : x ∈ CFSG.Open.pCoreOf 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨n, hn⟩ := h2
  have hyn : y ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
  have hz2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ^ 2 ^ n = 1 := by
    rw [← map_pow, hyn, map_one]
  have hz5' : QuotientGroup.mk' (CFSG.pCore 2 ↥X) y ∈ CFSG.pCore 5 (ZQuot X) := hy
  obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 5) (G := ZQuot X) ⟨_, hz5'⟩
  have hz5 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ^ 5 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hcop : Nat.Coprime (2 ^ n) (5 ^ m) := Nat.Coprime.pow n m (by norm_num)
  have hz1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ^ (2 ^ n).gcd (5 ^ m) = 1 :=
    pow_gcd_eq_one.mpr ⟨hz2, hz5⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hz1
  have hy2 : y ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff y).1 hz1
  exact Subgroup.mem_map_of_mem X.subtype hy2

theorem MinCex.sup_oTwoFive_eq (h186 : Item186H) (hX : MinCex A M H c X)
    (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X) :
    oTwoFive X ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) = X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hsol
  have hπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = 5 :=
    MinCex.card_primeFactors_subset h186 hX hsol h5
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) X :=
    isSylowOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem
  have hVX : (oTwoFiveOv X).map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hXV : X ≤ Subgroup.normalizer (((oTwoFiveOv X).map X.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoFiveOv X)
  have hAV : A ≤ Subgroup.normalizer (((oTwoFiveOv X).map X.subtype : Subgroup G) : Set G) :=
    (le_sup_left.trans hX.le_normalizer).trans (normalizer_le_normalizer_oTwoFiveOv X)
  have hPV : oTwoFive X ≤ (oTwoFiveOv X).map X.subtype :=
    Subgroup.map_mono (oTwoP_le_oTwoFiveOv X)
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2
      (CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ (oTwoFiveOv X).map X.subtype)
      ((oTwoFiveOv X).map X.subtype) :=
    hS.inf_of_le_normalizer hVX hXV
  have hT : ¬ 2 ∣ (CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ (oTwoFiveOv X).map X.subtype).relIndex
      ((oTwoFiveOv X).map X.subtype) := (isSylowOf_iff.mp hTsyl).2.2
  have hA : (oTwoFiveOv X).map X.subtype ≤ oTwoFive X ⊔
      (CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ (oTwoFiveOv X).map X.subtype) :=
    le_sup_of_two_pow_relIndex hPV inf_le_right (relIndex_oTwoFive_two_pow X) hT
  have hA' : (oTwoFiveOv X).map X.subtype ≤ oTwoFive X ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) :=
    hA.trans (sup_le_sup_left inf_le_left _)
  rcases hX.sup_eq_or_inf_le hS hVX hXV hAV with h | h
  · exact le_antisymm (sup_le (oTwoFive_le X) hS.le)
      (h.symm.le.trans (sup_le hA' le_sup_right))
  · have hTP : CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ (oTwoFiveOv X).map X.subtype ≤ oTwoFive X :=
      (inf_comm _ _).le.trans (h.trans (pCoreOf_le_oTwoFive X))
    have hVP : (oTwoFiveOv X).map X.subtype ≤ oTwoFive X := hA.trans (sup_le le_rfl hTP)
    have hle : oTwoFiveOv X ≤ Sec4.oTwoP 5 ↥X :=
      (Subgroup.map_le_map_iff_of_injective X.subtype_injective).mp hVP
    have h1 : (Sec4.oTwoP 5 ↥X).relIndex (oTwoFiveOv X) = 1 :=
      Subgroup.relIndex_eq_one.mpr hle
    rw [relIndex_oTwoP_oTwoFiveOv] at h1
    have hY2 : CFSG.pCore 2 (YQuot X) = ⊥ := Subgroup.card_eq_one.mp h1
    have hπY : ∀ q : ℕ, q.Prime → q ∣ Nat.card (YQuot X) → q = 2 ∨ q = 5 := fun q hq hqY =>
      hπ q hq (hqY.trans ((Subgroup.card_quotient_dvd_card (CFSG.pCore 5 (ZQuot X))).trans
        (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X))))
    have hchar : CFSG.IsCharacteristicP 5 (YQuot X) :=
      isCharacteristicP_five_of_solvable hπY hY2
    have hY5 : CFSG.pCore 5 (YQuot X) = ⊥ :=
      CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 5)
    have hYtriv : ∀ y : YQuot X, y = 1 := by
      intro y
      have hmem : y ∈ Subgroup.centralizer
          ((CFSG.pCore 5 (YQuot X) : Subgroup (YQuot X)) : Set (YQuot X)) := by
        rw [hY5, Subgroup.mem_centralizer_iff]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
        simp [hg]
      have hy := hchar hmem
      rw [hY5] at hy
      exact Subgroup.mem_bot.mp hy
    have hXle : X ≤ oTwoFive X := by
      intro x hx
      have h2 : (⟨x, hx⟩ : ↥X) ∈ Sec4.oTwoP 5 ↥X :=
        (QuotientGroup.eq_one_iff (QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨x, hx⟩ : ↥X))).1
          (hYtriv _)
      exact Subgroup.mem_map_of_mem X.subtype h2
    exact le_antisymm (sup_le (oTwoFive_le X) hS.le) (hXle.trans le_sup_left)

theorem MinCex.oTwoFive_inf_S (hX : MinCex A M H c X) :
    oTwoFive X ⊓ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ CFSG.Open.pCoreOf 2 X := by
  intro x hx
  obtain ⟨hxP, hxS⟩ := hx
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
  obtain ⟨n, hn⟩ := hS2 ⟨x, hxS⟩
  exact mem_pCoreOf_two_of_mem_oTwoFive_of_pow hxP ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem MinCex.A_le_normalizer_oTwoFive (hX : MinCex A M H c X) :
    A ≤ Subgroup.normalizer (oTwoFive X : Set G) :=
  (le_sup_left.trans hX.le_normalizer).trans (normalizer_le_normalizer_oTwoFive X)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
