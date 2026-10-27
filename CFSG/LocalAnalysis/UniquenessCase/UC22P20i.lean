module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p20i_isSolvable_quotient_sup (L T : Subgroup G) (hTn : T ≤ normalizer (L : Set G))
    (hT : IsPGroup 2 T) [hNn : (L.subgroupOf (L ⊔ T)).Normal] :
    Group.IsSolvable (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) := by
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  haveI : Group.IsSolvable ↥T := inferInstance
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (L.subgroupOf (L ⊔ T))).comp
        (Subgroup.inclusion (le_sup_right : T ≤ L ⊔ T))) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (L ⊔ T)) q
    have hx' : x ∈ ((L ⊔ T : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTn] at hx'
    obtain ⟨l, hl, b, hb, rfl⟩ := hx'
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff''.1 (hTn hb) l).1 hl
  exact Group.isSolvable_of_surjective hsurj

theorem uc22p20i_normalizer_le_M (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    normalizer ((D.T ⊓ L : Subgroup G) : Set G) ⊓ (L ⊔ D.T) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : L ⊔ D.T ∈ hSet D.T D.M := hL.2.2.1
  have hTL : D.T ≤ normalizer (L : Set G) := hL.1
  have hLH : L ≤ L ⊔ D.T := le_sup_left
  have hTH : D.T ≤ L ⊔ D.T := le_sup_right
  set Y : Subgroup G := normalizer ((D.T ⊓ L : Subgroup G) : Set G) ⊓ (L ⊔ D.T) with hY
  have hTN : D.T ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      refine ⟨D.T.mul_mem (D.T.mul_mem ht hxT) (D.T.inv_mem ht), ?_⟩
      exact (Subgroup.mem_normalizer_iff.1 (hTL ht) x).1 hxL
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, ?_⟩
      · have := D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hxT) ht
        simpa [mul_assoc] using this
      · have := (Subgroup.mem_normalizer_iff.1 (hTL (D.T.inv_mem ht)) (t * x * t⁻¹)).1
        simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.1 (hTL ht) x).2 hxL
  have hTY : D.T ≤ Y := le_inf hTN hTH
  refine uc22p20b_le_M_of_solvable D hB h1930 hH hTY inf_le_right ?_
  haveI hNn : (L.subgroupOf (L ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 (sup_le Subgroup.le_normalizer hTL)
  have hsylH : CFSG.ABGLocalTools.IsSylowOf 2 D.T (L ⊔ D.T) := D.sylowG.of_le hTH le_top
  have hT₀ : IsPGroup 2 (D.T.subgroupOf (L ⊔ D.T)) := D.sylowM.isPGroup.comap_subtype
  have hT₀' : ¬ 2 ∣ (D.T.subgroupOf (L ⊔ D.T)).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.1 hsylH).2.2
  have hsolv := uc22p20b_solvable_normalizer (D.T.subgroupOf (L ⊔ D.T)) (L.subgroupOf (L ⊔ D.T)) hT₀ hT₀'
    (uc22p20i_isSolvable_quotient_sup L D.T hTL D.sylowM.isPGroup)
  have hmem : ∀ x : ↥Y, (⟨(x : G), x.2.2⟩ : ↥(L ⊔ D.T)) ∈
      normalizer (((D.T.subgroupOf (L ⊔ D.T) ⊓ L.subgroupOf (L ⊔ D.T) : Subgroup ↥(L ⊔ D.T))) :
        Set ↥(L ⊔ D.T)) := by
    intro x
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h := Subgroup.mem_normalizer_iff.1 x.2.1 (y : G)
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf] at h ⊢
    exact h
  let φ : ↥Y →* ↥(normalizer (((D.T.subgroupOf (L ⊔ D.T) ⊓ L.subgroupOf (L ⊔ D.T) :
      Subgroup ↥(L ⊔ D.T))) : Set ↥(L ⊔ D.T))) :=
    (Subgroup.inclusion (inf_le_right : Y ≤ L ⊔ D.T)).codRestrict _ hmem
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => ((z : ↥(L ⊔ D.T)) : G)) (congrArg Subtype.val hab)
  haveI := hsolv
  exact Group.isSolvable_of_isSolvable_injective (f := φ) hφ

theorem uc22p20i_pCoreOf_le (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    pCoreOf 2 L ≤ D.T ⊓ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : D.T ≤ normalizer (L : Set G) := hL.1
  have hH : L ⊔ D.T ∈ hSet D.T D.M := hL.2.2.1
  have hLH : L ≤ L ⊔ D.T := le_sup_left
  have hP2 : IsPGroup 2 (pCoreOf 2 L) := uc22p20b_isPGroup_pCoreOf L
  have hPL : pCoreOf 2 L ≤ L := uc22p20b_pCoreOf_le L
  have hTP : ∀ t ∈ D.T, ∀ x ∈ pCoreOf 2 L, t * x * t⁻¹ ∈ pCoreOf 2 L := by
    intro t ht x hx
    have hmapL : (pCoreOf 2 L).map (MulAut.conj t).toMonoidHom ≤ L := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hTL ht) y).1 (hPL hy)
    have hmap2 : IsPGroup 2 ((pCoreOf 2 L).map (MulAut.conj t).toMonoidHom) := hP2.map _
    have hmapn : ∀ l ∈ L, ∀ y ∈ (pCoreOf 2 L).map (MulAut.conj t).toMonoidHom,
        l * y * l⁻¹ ∈ (pCoreOf 2 L).map (MulAut.conj t).toMonoidHom := by
      rintro l hl _ ⟨y, hy, rfl⟩
      have hl' : t⁻¹ * l * t ∈ L := by
        simpa using (Subgroup.mem_normalizer_iff.1 (hTL (D.T.inv_mem ht)) l).1 hl
      refine ⟨(t⁻¹ * l * t) * y * (t⁻¹ * l * t)⁻¹, uc22p20b_conj_mem_pCoreOf_self hl' hy, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      group
    exact uc22p20b_le_pCoreOf hmapL hmap2 hmapn ⟨x, hx, rfl⟩
  have hLTn : ∀ k ∈ L ⊔ D.T, ∀ x ∈ pCoreOf 2 L, k * x * k⁻¹ ∈ pCoreOf 2 L := by
    intro k hk x hx
    have hk' : k ∈ ((L ⊔ D.T : Subgroup G) : Set G) := hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L D.T hTL] at hk'
    obtain ⟨l, hl, t, ht, rfl⟩ := hk'
    have h1 := hTP t ht x hx
    have h2 := uc22p20b_conj_mem_pCoreOf_self hl h1
    simpa [mul_assoc] using h2
  have hle : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ D.T) :=
    uc22p20b_le_pCoreOf (hPL.trans hLH) hP2 hLTn
  exact le_inf ((hle.trans (uc22p20b_pCoreOf_le_T D le_sup_right))) hPL

theorem uc22p20i_pRank_bar2_le (D : Data G) {L : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) ≤ CFSG.Open.pRank p (L ⊔ D.T) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hk]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow hp h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) hN,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) L]
  exact CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left

theorem uc22p20i_isSylowOf_inf (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L ≤ L ⊔ D.T := le_sup_left
  have hsylH : CFSG.ABGLocalTools.IsSylowOf 2 D.T (L ⊔ D.T) := D.sylowG.of_le le_sup_right le_top
  exact hsylH.inf_of_le_normalizer hLH (sup_le Subgroup.le_normalizer hL.1)

@[expose] def uc22p20iSylowBar (D : Data G) (L : Subgroup G) : Subgroup (Bar2 L) :=
  ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

theorem uc22p20i_sylowBar_isPGroup (D : Data G) {L : Subgroup G} :
    IsPGroup 2 (uc22p20iSylowBar D L) := by
  unfold uc22p20iSylowBar
  exact (D.sylowM.isPGroup.to_inf_left.comap_subtype).map _

theorem uc22p20i_sylowBar_index (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    ¬ 2 ∣ (uc22p20iSylowBar D L).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ (D.T ⊓ L).subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (uc22p20i_pCoreOf_le D hL this)
  unfold uc22p20iSylowBar
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker]
  exact (CFSG.ABGLocalTools.isSylowOf_iff.1 (uc22p20i_isSylowOf_inf D hL)).2.2

theorem uc22p20i_mem_sylowBar_iff (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) (y : ↥L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥L) y ∈ uc22p20iSylowBar D L ↔ (y : G) ∈ D.T ⊓ L := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : (z⁻¹ * y : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker, map_mul, map_inv, hzy]
      exact inv_mul_cancel _
    have hmem : (((z⁻¹ * y : ↥L)) : G) ∈ pCoreOf 2 L := ⟨_, hzy', rfl⟩
    have h3 := uc22p20i_pCoreOf_le D hL hmem
    have hz' : (z : G) ∈ D.T ⊓ L := Subgroup.mem_subgroupOf.1 hz
    have : (y : G) = (z : G) * (((z⁻¹ * y : ↥L)) : G) := by simp
    rw [this]
    exact (D.T ⊓ L).mul_mem hz' h3
  · intro hy
    exact ⟨y, Subgroup.mem_subgroupOf.2 hy, rfl⟩

theorem uc22p20i_mem_normalizer_of_borel (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (l : ↥L) (hl : QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈
      normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L))) :
    (l : G) ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_normalizer_iff] at hl
  constructor
  · intro hx
    have hxL : x ∈ L := hx.2
    have h3 := (hl (π ⟨x, hxL⟩)).1 ((uc22p20i_mem_sylowBar_iff D hL ⟨x, hxL⟩).2 hx)
    have h4 : π (l * ⟨x, hxL⟩ * l⁻¹) ∈ uc22p20iSylowBar D L := by
      simpa [map_mul, map_inv] using h3
    exact (uc22p20i_mem_sylowBar_iff D hL _).1 h4
  · intro hx
    have hx' : (l : G) * x * (l : G)⁻¹ ∈ L := hx.2
    have hxL : x ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem l.2) hx') l.2
      simpa [mul_assoc] using this
    have h4 : π (l * ⟨x, hxL⟩ * l⁻¹) ∈ uc22p20iSylowBar D L :=
      (uc22p20i_mem_sylowBar_iff D hL _).2 hx
    have h5 : π l * π ⟨x, hxL⟩ * (π l)⁻¹ ∈ uc22p20iSylowBar D L := by
      simpa [map_mul, map_inv] using h4
    exact (uc22p20i_mem_sylowBar_iff D hL ⟨x, hxL⟩).1 ((hl (π ⟨x, hxL⟩)).2 h5)

theorem uc22p20i_borel_le_M (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) (l : ↥L)
    (hl : QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈
      normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L))) : (l : G) ∈ D.M :=
  uc22p20i_normalizer_le_M D hB h1930 hL
    ⟨uc22p20i_mem_normalizer_of_borel D hL l hl, (le_sup_left : L ≤ L ⊔ D.T) l.2⟩

theorem uc22p20i_pRank_borel_le (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L))) ≤
      CFSG.Open.pRank p ((L ⊔ D.T) ⊓ D.M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hk : ¬ p ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact uc22p20c_not_dvd_card_of_isPGroup_two (CFSG.pCore_isPGroup) hp hp2
  set N := normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) with hN
  have h1 : CFSG.Open.pRank p (N.comap π) = CFSG.Open.pRank p N :=
    uc22p20c_pRank_comap_eq π hsurj hp hk N
  have h2 : CFSG.Open.pRank p ((N.comap π).map L.subtype) = CFSG.Open.pRank p (N.comap π) :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp L.subtype L.subtype_injective _
  have hle : (N.comap π).map L.subtype ≤ (L ⊔ D.T) ⊓ D.M := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨(le_sup_left : L ≤ L ⊔ D.T) l.2, uc22p20i_borel_le_M D hB h1930 hL l hl⟩
  rw [← h1, ← h2]
  exact CFSG.SectionRank.pRank_mono hp.one_lt hle

theorem uc22p20i_rank_bounds (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    (h20_1 : S20_1_124 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≤ 3 ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → 3 < CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) →
        CFSG.Open.pRank p (normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) :
          Set (Bar2 L))) ≤ 1 := by
  have hH : L ⊔ D.T ∈ hSet D.T D.M := hL.2.2.1
  obtain ⟨h1, h2, -⟩ := h20_1 h1930 _ hH
  refine ⟨(uc22p20i_pRank_bar2_le D Nat.prime_three (by norm_num)).trans h1, fun p hp hp2 hbig => ?_⟩
  have h3 := uc22p20i_pRank_bar2_le D (L := L) hp hp2
  exact (uc22p20i_pRank_borel_le D hB h1930 hL hp hp2).trans (h2 p hp hp2 (lt_of_lt_of_le hbig h3))

theorem uc22p20i_listB_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Asc1930ListB X) : Asc1930ListB Y := by
  rcases h with ⟨t, m, n, hn, hm⟩ | h | h | h | h | h | h
  · exact Or.inl ⟨t, m, n, hn, CFSG.Blueprint.LieModel.of_mulEquiv e hm⟩
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.Blueprint.LieModel.of_mulEquiv e h))))))
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans e'⟩)))))

theorem uc22p20i_listB (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) : ∃ C ∈ CFSG.Quasithin.cComp L, Asc1930ListB (BarInf C) := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨hTL, -, hH, K, hK, hLK⟩ := hL
  have hKc : K ∈ CFSG.Quasithin.cComp L := uc22p20e_cComp_of_calC hK
  have hLH : L ≤ L ⊔ D.T := le_sup_left
  have hsub : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Open.IsSubnormal.step hLH ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2
      (sup_le Subgroup.le_normalizer hTL)) (CFSG.Open.IsSubnormal.refl _)
  have hKH : K ∈ CFSG.Quasithin.cComp (L ⊔ D.T) := CFSG.Quasithin.cComp_mem_of_subnormal hsub hKc
  have hspan : sSup (CFSG.Quasithin.cComp L) = L := by
    have h := uc22p20b_sSup_cComp_orb hKH (le_sup_right : D.T ≤ L ⊔ D.T)
    have hLo : uc22p20bOrb D.T K = L := hLK.symm
    rwa [hLo] at h
  haveI : Group.IsNilpotent ↥D.T := D.sylowM.isPGroup.isNilpotent
  haveI : Group.IsSolvable ↥D.T := inferInstance
  obtain ⟨Λ, _, hcf, hlistB⟩ := (h1930 _ hH).1
  obtain ⟨a, b, hab⟩ := hB Λ hlistB
  obtain ⟨C, hC, ⟨e⟩⟩ := uc22p20b_compFactorsOfCComp (G := G) L D.T hTL inferInstance hspan Λ hcf
    ⟨a, b, hab⟩
  exact ⟨C, hC, uc22p20i_listB_of_mulEquiv e.symm hlistB⟩

theorem uc22p20i_not_le_M (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) : ¬ L ≤ D.M :=
  fun h => hL.2.2.1.2.1 (sup_le h D.sylowM.le)

theorem uc22p20i_inf_parabolic (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    ParabolicOf L (D.M ⊓ L) ∧ D.T ≤ normalizer ((D.M ⊓ L : Subgroup G) : Set G) ∧ ¬ L ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨(uc22p20i_pCoreOf_le D hL).trans (inf_le_inf_right L D.sylowM.le), inf_le_right, ?_⟩,
    ?_, uc22p20i_not_le_M D hL⟩
  · refine ⟨(uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL), ?_⟩
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
    exact ⟨l, Subgroup.mem_subgroupOf.2 ⟨uc22p20i_borel_le_M D hB h1930 hL l hx, l.2⟩, rfl⟩
  · intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (H := D.M) (D.sylowM.le ht)) x
    have h2 := Subgroup.mem_normalizer_iff.1 (hL.1 ht) x
    simp only [Subgroup.mem_inf]
    exact and_congr h1 h2

end CFSG.LocalAnalysis.UniquenessCase.UC22
