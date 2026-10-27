module

public import CFSG.Quasithin.EmptyFaithful.S146zMStep
public import CFSG.Quasithin.EmptyFaithful.S146zMQuo
public import CFSG.Quasithin.EmptyFaithful.S146zMDec
public import CFSG.Quasithin.EmptyFaithful.S146zMComp
public import CFSG.Quasithin.EmptyFaithful.S146zMSolv
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.SectionRank
open scoped Pointwise

section Aux

variable {G : Type} [Group G]

theorem zm_isElemAbelian_subgroupOf {p : ℕ} {X E : Subgroup G} (hEX : E ≤ X)
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.subgroupOf X) ∧ Nat.card (E.subgroupOf X) = Nat.card E := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv⟩
  · apply Subtype.ext
    apply Subtype.ext
    have := zmComm hE (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
    exact this
  · apply Subtype.ext
    exact hE.2 _ (Subgroup.mem_subgroupOf.mp hx)

theorem isSolvable_sup_of_normalizes {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hA : Group.IsSolvable ↥A) (hB : Group.IsSolvable ↥B) : Group.IsSolvable ↥(A ⊔ B) := by
  set Y := A ⊔ B with hY
  have hBY : B ≤ Y := le_sup_right
  have hAY : A ≤ Y := le_sup_left
  have hYn : Y ≤ Subgroup.normalizer (B : Set G) := sup_le hAB Subgroup.le_normalizer
  have hBn : (B.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).mpr hYn
  have hBs : Group.IsSolvable ↥(B.subgroupOf Y) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hBY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hBY).symm.surjective
  have hmul : (↑(A ⊔ B) : Set G) = ↑A * ↑B := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  let ψ : ↥A →* ↥Y ⧸ B.subgroupOf Y :=
    (QuotientGroup.mk' (B.subgroupOf Y)).comp (Subgroup.inclusion hAY)
  have hψ : Function.Surjective ψ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : G) ∈ (↑(A ⊔ B) : Set G) := y.2
      rw [hmul] at hy
      obtain ⟨a, ha, b, hb, hab⟩ := hy
      refine ⟨⟨a, ha⟩, ?_⟩
      show (QuotientGroup.mk (Subgroup.inclusion hAY ⟨a, ha⟩) : ↥Y ⧸ B.subgroupOf Y) = QuotientGroup.mk y
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      show ((Subgroup.inclusion hAY ⟨a, ha⟩ : ↥Y) : G)⁻¹ * (y : G) ∈ B
      have : ((Subgroup.inclusion hAY ⟨a, ha⟩ : ↥Y) : G)⁻¹ * (y : G) = b := by
        show a⁻¹ * (y : G) = b
        rw [← hab]; group
      rw [this]
      exact hb
  have hqs : Group.IsSolvable (↥Y ⧸ B.subgroupOf Y) := Group.isSolvable_of_surjective hψ
  exact Group.isSolvable_of_ker_le_range (B.subgroupOf Y).subtype (QuotientGroup.mk' (B.subgroupOf Y))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Aux

section Dec

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem IsRedCE.exists_mul_oTwoUpper (hred : IsRedCE T M H PQ p) {y : G}
    (hy : y ∈ PQ) : ∃ a ∈ pCoreOf 2 H, ∃ b ∈ oTwoUpper PQ, y = a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hab, -, ⟨e, hae⟩, hb, haz, hbz⟩ := F6.exists_mul_eq_pPart Nat.prime_two y
  have haPQ : a ∈ PQ := (Subgroup.zpowers_le.mpr hy) haz
  have hbPQ : b ∈ PQ := (Subgroup.zpowers_le.mpr hy) hbz
  have hbodd : Odd (orderOf b) := by
    rcases Nat.even_or_odd (orderOf b) with he | ho
    · exfalso
      have := Nat.Coprime.eq_one_of_dvd hb.symm (even_iff_two_dvd.mp he)
      omega
    · exact ho
  refine ⟨a, ?_, b, mem_oTwoUpper_of_odd hbPQ hbodd, hab.symm⟩
  obtain ⟨k, hk⟩ := hred.pSec a haPQ
  have h1 : orderOf a ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hae
  have hcop : Nat.Coprime (orderOf a) (p ^ k) :=
    Nat.Coprime.coprime_dvd_left h1
      (Nat.Coprime.pow e k ((Nat.coprime_primes Nat.prime_two hred.prime).mpr (Ne.symm hred.odd)))
  exact mem_of_pow_mem_of_coprime hcop hk

theorem IsRedCE.exists_mul_of_mem (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) {h : G}
    (hh : h ∈ H) : ∃ p' ∈ oTwoUpper PQ, ∃ t' ∈ T, h = p' * t' := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hH
  have hhPT : h ∈ PQ ⊔ T := by rw [← hred.eq]; exact hh
  have hmul : (↑(PQ ⊔ T) : Set G) = ↑PQ * ↑T :=
    Subgroup.coe_mul_of_right_le_normalizer_left PQ T (hTH.trans hred.normal)
  have hh' : h ∈ (↑(PQ ⊔ T) : Set G) := hhPT
  rw [hmul] at hh'
  obtain ⟨y, hy, t, ht, rfl⟩ := hh'
  obtain ⟨a, ha, b, hb, rfl⟩ := hred.exists_mul_oTwoUpper hy
  have hbH : b ∈ H := hred.le (oTwoUpper_le PQ hb)
  have hconj : b⁻¹ * a * b ∈ pCoreOf 2 H := by
    have := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hbH)) a).mp ha
    simpa using this
  refine ⟨b, hb, (b⁻¹ * a * b) * t, T.mul_mem (hQT hconj) ht, ?_⟩
  group

theorem input14614SolDec_of_list (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (hlist : SQTKList3Dvd) : Input14614SolDec := by
  intro G _ _ T M S H PQ p hred hmax hp3 hdec hK
  classical
  subst hp3
  obtain ⟨H₀, H₁, H₂, t, hdecP⟩ := hdec
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hG₁ : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTG : T ≤ mcOf T := hTH.trans hHG
  by_contra hns
  set X : Subgroup G := mcOf T with hXdef
  set R : Subgroup ↥X := CFSG.pCore 2 ↥X with hRdef
  have hRp : IsPGroup 2 R := CFSG.pCore_isPGroup
  let π : ↥X →* ↥X ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hQns : ¬ Group.IsSolvable (↥X ⧸ R) := fun h =>
    hns (isSolvable_of_quotient_two_group R hRp h)
  have hQ : SQTKHyp (↥X ⧸ R) :=
    sqtkHyp_quotient_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple S.hyp.nonabelian hG₁.1.2
  have : Finite (↥X ⧸ R) := hQ.finite
  have hSQ : CFSG.IsStronglyQuasithin ↥X :=
    isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank S.hyp.qtke.2.2 hG₁.1.2
  have hr3X : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp hSQ) 3 Nat.prime_three (by norm_num)
  have hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥X ⧸ R)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_two_group R hRp Nat.prime_three (by norm_num)]
    exact hr3X
  set K : Subgroup G := oTwoUpper H with hKdef
  have hKH : K ≤ H := oTwoUpper_le H
  have hKX : K ≤ X := hKH.trans hHG
  have hnormK : X ≤ Subgroup.normalizer (K : Set G) := by
    have := le_normalizer_conjClosure K X
    rwa [hK] at this
  have hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hnormK
  set Kb : Subgroup (↥X ⧸ R) := (K.subgroupOf X).map π with hKb
  have hKbn : Kb.Normal := Subgroup.Normal.map hKn π hπ
  have hHs : Group.IsSolvable ↥H := hred.isSolvable S
  have hKs0 : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
      (Subgroup.inclusion_injective hKH)
  have hKs1 : Group.IsSolvable ↥(K.subgroupOf X) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hKX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKX).symm.surjective
  have hKbs : Group.IsSolvable ↥Kb :=
    Group.isSolvable_of_surjective (f := π.subgroupMap (K.subgroupOf X))
      (π.subgroupMap_surjective _)
  have hKb23 : ∀ r : ℕ, r.Prime → r ∣ Nat.card Kb → r = 2 ∨ r = 3 := by
    intro r hr hd
    have h1 : Nat.card Kb ∣ Nat.card ↥(K.subgroupOf X) :=
      Subgroup.card_dvd_of_surjective (π.subgroupMap_surjective (K.subgroupOf X))
    have h2 : Nat.card ↥(K.subgroupOf X) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
    have h3 : Nat.card K ∣ Nat.card H := Subgroup.card_dvd_of_le hKH
    rw [h2] at h1
    exact hred.prime_dvd_card S hr (hd.trans (h1.trans h3))
  obtain ⟨E, hEH, hEK, hEel, hEcard⟩ := hdecP.exists_elemAbelian_sq Nat.prime_three (by norm_num)
  obtain ⟨hE', hE'card⟩ := zm_isElemAbelian_subgroupOf (hEH.trans hHG) hEel
  obtain ⟨hEb, hEbcard⟩ := isElemAbelian_map_quotient R hRp (by norm_num : (3 : ℕ) ≠ 2) hE'
  set Eb : Subgroup (↥X ⧸ R) := (E.subgroupOf X).map π with hEbdef
  have hEbK : Eb ≤ Kb := Subgroup.map_mono (Subgroup.comap_mono hEK)
  have hEbc : Nat.card Eb = 3 ^ 2 := by rw [hEbcard, hE'card, hEcard]
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTi : ¬ 2 ∣ T.index := S.hyp.sylow.2
  have hT'p : IsPGroup 2 (T.subgroupOf X) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTG).symm
  have hT'i : ¬ 2 ∣ (T.subgroupOf X).index := by
    intro hd
    apply hTi
    have h1 : T.relIndex X * X.index = T.index := Subgroup.relIndex_mul_index hTG
    rw [← h1]
    exact hd.trans (dvd_mul_right _ _)
  have hTb : IsSylowTwoOf ((T.subgroupOf X).map π) ⊤ := isSylowTwoOf_map_quotient R hT'p hT'i
  have hA37 := h37 (↥X ⧸ R) hQ
  have hA36 := h36 (↥X ⧸ R) hQ
  have hSz : ∀ L ∈ cComp (⊤ : Subgroup (↥X ⧸ R)),
      ⁅L, Kb⁆ = ⊥ ∧ ∃ f : ℕ, CFSG.Blueprint.SuzukiModel ↥L 2 f := fun L hL => by
    obtain ⟨h1, -, f, -, -, hf⟩ :=
      cComp_simple_suzuki_of_a36 hlist hr3 hL (hA36 L hL) hKbs hKb23 hEbK hEb hEbc
    exact ⟨h1, f, hf⟩
  have hQns' : ¬ Group.IsSolvable ↥(⊤ : Subgroup (↥X ⧸ R)) := fun h =>
    hQns (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥X ⧸ R)) ≃* _).toMonoidHom)
      Subgroup.topEquiv.surjective)
  obtain ⟨J, hJ, -⟩ := exists_cComp_le_of_not_solvable (H := (⊤ : Subgroup (↥X ⧸ R)))
    (X := ⊤) le_top inferInstance hQns'
  set P : Subgroup G := oTwoUpper PQ with hPdef
  have hPK : P ≤ K := oTwoUpper_mono hred.le
  set Pb : Subgroup (↥X ⧸ R) := (P.subgroupOf X).map π with hPbdef
  have hPbK : Pb ≤ Kb := Subgroup.map_mono (Subgroup.comap_mono hPK)
  obtain ⟨B, hBs, hPB, hTB, ℓ, hℓ, h2, h3, hd⟩ :=
    exists_solvable_normalized_of_suzuki hA37 hTb hSz hJ hPbK
  set Hb : Subgroup (↥X ⧸ R) := (H.subgroupOf X).map π with hHbdef
  have hHbN : Hb ≤ Subgroup.normalizer (B : Set (↥X ⧸ R)) := by
    rintro z ⟨h, hh, rfl⟩
    have hhH : (h : G) ∈ H := hh
    obtain ⟨p', hp', t', ht', hpt⟩ := hred.exists_mul_of_mem S hhH
    have hp'X : p' ∈ X := (hHG (hred.le (oTwoUpper_le PQ hp')))
    have ht'X : t' ∈ X := hTG ht'
    have e : h = ⟨p', hp'X⟩ * ⟨t', ht'X⟩ := Subtype.ext hpt
    rw [e, map_mul]
    exact (Subgroup.normalizer (B : Set (↥X ⧸ R))).mul_mem
      (hPB ⟨⟨p', hp'X⟩, Subgroup.mem_subgroupOf.mpr hp', rfl⟩)
      (hTB ⟨⟨t', ht'X⟩, Subgroup.mem_subgroupOf.mpr ht', rfl⟩)
  have hHbs : Group.IsSolvable ↥Hb := by
    have hH's : Group.IsSolvable ↥(H.subgroupOf X) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hHG).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hHG).symm.surjective
    exact Group.isSolvable_of_surjective (f := π.subgroupMap (H.subgroupOf X))
      (π.subgroupMap_surjective _)
  set Y : Subgroup (↥X ⧸ R) := Hb ⊔ B with hYdef
  have hYs : Group.IsSolvable ↥Y := isSolvable_sup_of_normalizes hHbN hHbs hBs
  set Hp : Subgroup G := (Y.comap π).map X.subtype with hHpdef
  have hCs : Group.IsSolvable ↥(Y.comap π) := isSolvable_comap_quotient R hRp hYs
  have hHpsolv : Group.IsSolvable ↥Hp :=
    Group.isSolvable_of_surjective
      (f := ((Y.comap π).equivMapOfInjective X.subtype X.subtype_injective).toMonoidHom)
      ((Y.comap π).equivMapOfInjective X.subtype X.subtype_injective).surjective
  have hHHp : H ≤ Hp := by
    intro h hh
    refine ⟨⟨h, hHG hh⟩, ?_, rfl⟩
    show π ⟨h, hHG hh⟩ ∈ Y
    exact (le_sup_left : Hb ≤ Y) ⟨⟨h, hHG hh⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
  have hHpM : Hp ≤ mcOf T := Subgroup.map_subtype_le _
  have hdvdHp : ℓ ∣ Nat.card ↥Hp := by
    have h1 : Nat.card B ∣ Nat.card Y := Subgroup.card_dvd_of_le le_sup_right
    have h2' : Nat.card Y ∣ Nat.card ↥(Y.comap π) := card_dvd_comap_quotient R Y
    have h3' : Nat.card ↥(Y.comap π) = Nat.card ↥Hp :=
      Nat.card_congr ((Y.comap π).equivMapOfInjective X.subtype X.subtype_injective).toEquiv
    rw [← h3']
    exact hd.trans (h1.trans h2')
  have := (input14614Solv_proved G T M S H PQ 3 hred hmax Hp hHHp hHpM hHpsolv).1 rfl ℓ hℓ hdvdHp
  rcases this with h | h
  · exact h2 h
  · exact h3 h

end Dec

end CFSG.Quasithin
