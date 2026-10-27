module

public import CFSG.Quasithin.EmptyFaithful.S146zMSol
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Sec2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.SectionRank

theorem input14614SolE9_of_list (h35 : Lemma1435)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (hlist : SQTKList3Dvd) :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
      ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsE9Z4Shape T H p →
        conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H → Group.IsSolvable ↥(mcOf T) := by
  intro G _ _ T M S H PQ p hred hmax hshape hK
  classical
  have hp3 : p = 3 := hshape.1
  subst hp3
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
  obtain ⟨E, hEK, hEel, hE9, -⟩ := e9_exists_P h35 S hred hshape
  have hEH : E ≤ H := hEK.trans hKH
  obtain ⟨hE', hE'card⟩ := zm_isElemAbelian_subgroupOf (hEH.trans hHG) hEel
  obtain ⟨hEb, hEbcard⟩ := isElemAbelian_map_quotient R hRp (by norm_num : (3 : ℕ) ≠ 2) hE'
  set Eb : Subgroup (↥X ⧸ R) := (E.subgroupOf X).map π with hEbdef
  have hEbK : Eb ≤ Kb := Subgroup.map_mono (Subgroup.comap_mono hEK)
  have hEbc : Nat.card Eb = 3 ^ 2 := by rw [hEbcard, hE'card, hE9]; norm_num
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
    hQns (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥X ⧸ R)) ≃* _).toMonoidHom)
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

theorem stage14614C1_of_eq_E9 (h35 : Lemma1435)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (hlist : SQTKList3Dvd) {G : Type} [Group G] [Finite G]
    {T M H PQ : Subgroup G} {p : ℕ} (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p)
    (hK : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) : Stage14614C1 T H p := by
  refine ⟨hK, fun hp3 r hr hdvd => ?_⟩
  have hsolv := input14614SolE9_of_list h35 h36 h37 hlist G T M S H PQ p hred hmax hshape hK
  exact (input14614Solv_proved G T M S H PQ p hred hmax (mcOf T) (S.le_mcOf hred.isHTM) le_rfl
    hsolv).1 hp3 r hr hdvd

end CFSG.Quasithin
