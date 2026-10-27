module

public import CFSG.Quasithin.H13.NQCatRkOneProd
public import CFSG.Quasithin.H13.NQCatE68Borel
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837KG
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin.H13.NQCat.RkOne

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

section Quotient

variable {B : Type*} [Group B]

theorem pCore_subgroupOf_of_normal (p : ℕ) (N : Subgroup B) [N.Normal] :
    (CFSG.pCore p B).subgroupOf N = CFSG.pCore p N := by
  apply le_antisymm
  · exact le_sSup ⟨CFSG.pCore_normal.subgroupOf N,
      CFSG.pCore_isPGroup.comap_of_injective N.subtype N.subtype_injective⟩
  · intro x hx
    rw [mem_subgroupOf]
    have hp : IsPGroup p ((CFSG.pCore p N).map N.subtype) := CFSG.pCore_isPGroup.map _
    exact (le_sSup ⟨inferInstance, hp⟩ : _ ≤ CFSG.pCore p B) ⟨x, hx, rfl⟩

theorem benderType_map_mk {N : Subgroup B} [N.Normal] {Y : Type*} [Group Y] (f : N ≃* Y)
    {n i e : ℕ} (h : BenderType (Y ⧸ CFSG.pCore 2 Y) n i e) :
    BenderType (N.map (QuotientGroup.mk' (CFSG.pCore 2 B))) n i e := by
  set φ := (QuotientGroup.mk' (CFSG.pCore 2 B)).domRestrict N with hφ
  have hker : φ.ker = CFSG.pCore 2 N := by
    rw [hφ, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', pCore_subgroupOf_of_normal]
  have hrange : φ.range = N.map (QuotientGroup.mk' (CFSG.pCore 2 B)) := by
    rw [hφ, MonoidHom.domRestrict_range]
  let e₁ : N ⧸ CFSG.pCore 2 N ≃* Y ⧸ CFSG.pCore 2 Y :=
    QuotientGroup.congr _ _ f (CFSG.pCore_map_iso 2 f)
  let e₂ : N ⧸ CFSG.pCore 2 N ≃* N.map (QuotientGroup.mk' (CFSG.pCore 2 B)) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
  exact h.of_mulEquiv (e₁.symm.trans e₂)

end Quotient

section Components

variable {G : Type} [Group G]

theorem conj_mem_cComp {H K : Subgroup G} {t : G} (ht : t ∈ H) (hK : K ∈ cComp H) :
    K.map (MulAut.conj t).toMonoidHom ∈ cComp H := by
  have h := cComp_map_mulEquiv (MulAut.conj t) hK
  have hH : H.map (MulAut.conj t).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.1 (le_normalizer ht)
  rwa [hH] at h

theorem le_normalizer_pCore (L : Subgroup G) :
    L ≤ normalizer (((CFSG.pCore 2 L).map L.subtype : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, CFSG.pCore_normal.conj_mem y hy ⟨x, hx⟩, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    refine ⟨⟨x, hx⟩⁻¹ * y * ⟨x, hx⟩, ?_, ?_⟩
    · have := CFSG.pCore_normal.conj_mem y hy ⟨x, hx⟩⁻¹
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyg ⊢
      rw [hyg]
      group

theorem eq_of_map_le [Finite G] {H L J J' : Subgroup G} (hJ : J ∈ cComp H) (hJ' : J' ∈ cComp H)
    (hJL : J ≤ L) (hJ'L : J' ≤ L) (hLH : L ≤ H)
    (hle : (J.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) ≤
      (J'.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L))) : J = J' := by
  set QG : Subgroup G := (CFSG.pCore 2 L).map L.subtype with hQG
  have hJle : J ≤ J' ⊔ QG := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := hle ⟨⟨a, hJL ha⟩, ha, rfl⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hba
    have h1 : a = (b : G) * ((b⁻¹ * ⟨a, hJL ha⟩ : L) : G) := by
      simp
    rw [h1]
    exact mul_mem (mem_sup_left hb) (mem_sup_right ⟨_, hba, rfl⟩)
  have hQs : Group.IsSolvable QG := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 QG := CFSG.pCore_isPGroup.map _
    have := hp.isNilpotent
    infer_instance
  have hcore := (cComp_commutator_perfectCore hJ' ((map_subtype_le _).trans hLH) hQs
    (hJ'L.trans (le_normalizer_pCore L))).2
  have hJJ' : J ≤ J' := by
    calc J = perfectCore J := (perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hJ)).symm
      _ ≤ perfectCore (J' ⊔ QG) := perfectCore_mono hJle
      _ = J' := hcore
  by_contra hne
  exact not_subnormal_of_mem_cComp hJ' (lt_of_le_of_ne hJJ' hne) (ne_bot_of_mem_cComp hJ)
    (perfect_of_mem_cComp hJ) (subnormal_of_mem_cComp hJ)

end Components

theorem rankOne_overgroups {G : Type} [Group G] [Finite G]
    {H T K : Subgroup G} (hT : IsSylowTwoOf T H) (hK : K ∈ cComp H)
    (hHT : conjClosure K T ⊔ T = H) {n i e : ℕ}
    (hBK : BenderType (K ⧸ CFSG.pCore 2 K) n i e) :
    Group.IsSolvable ↥(H ⊓ normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G)) ∧
      ∀ Y : Subgroup G, T ≤ Y → Y ≤ H →
        Y = H ∨ Y ≤ normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := conjClosure K T with hLdef
  set S : Subgroup G := T ⊓ L with hSdef
  have hTH : T ≤ H := hT.1
  have hLH : L ≤ H := hHT ▸ le_sup_left
  have hTL : T ≤ normalizer (L : Set G) := le_normalizer_conjClosure K T
  have hHL : H ≤ normalizer (L : Set G) := hHT ▸ sup_le le_normalizer hTL
  have hTS : T ≤ normalizer (S : Set G) := fun t ht =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer ht, hTL ht⟩
  set ι := ↥(Set.range fun t : T => K.map (MulAut.conj (t : G)).toMonoidHom) with hι
  have hJt : ∀ j : ι, ∃ t ∈ T, (j : Subgroup G) = K.map (MulAut.conj t).toMonoidHom := by
    rintro ⟨_, ⟨t, rfl⟩⟩
    exact ⟨t, t.2, rfl⟩
  have hJc : ∀ j : ι, (j : Subgroup G) ∈ cComp H := fun j => by
    obtain ⟨t, ht, hj⟩ := hJt j
    rw [hj]
    exact conj_mem_cComp (hTH ht) hK
  have hJL : ∀ j : ι, (j : Subgroup G) ≤ L := fun j => by
    obtain ⟨t, ht, hj⟩ := hJt j
    rw [hj]
    rintro _ ⟨k, hk, rfl⟩
    exact mem_conjClosure ht hk
  have hLspan : L ≤ cCompSpan H := conjClosure_le fun t ht k hk =>
    le_cCompSpan (conj_mem_cComp (hTH ht) hK) ⟨k, hk, rfl⟩
  have hJn : ∀ j : ι, ((j : Subgroup G).subgroupOf L).Normal := fun j => by
    obtain ⟨hle, hn⟩ := cComp_normal_span_of_le (hJc j)
    rw [normal_subgroupOf_iff_le_normalizer (hJL j)]
    exact hLspan.trans ((normal_subgroupOf_iff_le_normalizer hle).1 hn)
  have hsupJ : ⨆ j : ι, (j : Subgroup G) = L := by
    refine le_antisymm (iSup_le hJL) (conjClosure_le fun t ht k hk => ?_)
    exact mem_iSup_of_mem (⟨K.map (MulAut.conj t).toMonoidHom, ⟨t, ht⟩, rfl⟩ : ι)
      (show t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom from ⟨k, hk, rfl⟩)
  set Q' : Subgroup L := CFSG.pCore 2 L with hQ'
  set φ : L →* L ⧸ Q' := QuotientGroup.mk' Q' with hφ
  set X : ι → Subgroup (L ⧸ Q') := fun j => ((j : Subgroup G).subgroupOf L).map φ with hX
  have hXn : ∀ j, (X j).Normal := fun j => (hJn j).map φ (QuotientGroup.mk'_surjective Q')
  have hXB : ∀ j, BenderType (X j) n i e := fun j => by
    obtain ⟨t, ht, hj⟩ := hJt j
    have := hJn j
    let f : ((j : Subgroup G).subgroupOf L) ≃* K :=
      ((subgroupOfEquivOfLe (hJL j)).trans (MulEquiv.subgroupCongr hj)).trans
        (K.equivMapOfInjective _ (MulAut.conj t).injective).symm
    exact benderType_map_mk f hBK
  have hXsimple : ∀ j, IsSimpleGroup (X j) := fun j => (hXB j).isSimple
  have hcomm : Pairwise fun j j' => ∀ x y : L ⧸ Q', x ∈ X j → y ∈ X j' → Commute x y := by
    intro j j' hjj' x y hx hy
    have := hXn j
    have := hXn j'
    have := hXsimple j
    have hN : ((X j ⊓ X j').subgroupOf (X j)).Normal :=
      (inferInstance : (X j ⊓ X j').Normal).subgroupOf _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X j ⊓ X j').subgroupOf (X j)) with h | h
    · have hc : x * y * x⁻¹ * y⁻¹ ∈ X j ⊓ X j' := by
        rw [mem_inf]
        refine ⟨?_, mul_mem ((hXn j').conj_mem _ hy x) (inv_mem hy)⟩
        have h1 := mul_mem hx ((hXn j).conj_mem _ (inv_mem hx) y)
        simpa [mul_assoc] using h1
      have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := by
        have : (⟨_, hc.1⟩ : X j) ∈ (X j ⊓ X j').subgroupOf (X j) := hc
        rw [h, mem_bot] at this
        exact congrArg Subtype.val this
      exact mul_inv_eq_one.1 (by simpa [mul_assoc] using hc1)
    · exfalso
      apply hjj'
      refine Subtype.ext (eq_of_map_le (hJc j) (hJc j') (hJL j) (hJL j') hLH fun z hz => ?_)
      have : (⟨z, hz⟩ : X j) ∈ (X j ⊓ X j').subgroupOf (X j) := h ▸ mem_top _
      exact this.2
  have hind : iSupIndep X := iSupIndep_of_commute X hcomm fun j x hx hxc => by
    have hz : (⟨x, hx⟩ : X j) ∈ center (X j) := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext ((hxc g g.2).eq.symm)
    have := hXsimple j
    have hnc := (hXB j).isSimpleBenderGroup.not_commutative
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (X j)) with hbot | htop
    · rw [hbot, mem_bot] at hz
      exact congrArg Subtype.val hz
    · exfalso
      apply hnc
      intro a b
      have : a ∈ center (X j) := by rw [htop]; trivial
      exact (mem_center_iff.mp this b).symm
  have htop : ⨆ j, X j = ⊤ := by
    have h1 : ⨆ j : ι, (j : Subgroup G).subgroupOf L = ⊤ := by
      apply map_injective L.subtype_injective
      rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
      simp_rw [map_subgroupOf_eq_of_le (hJL _)]
      exact hsupJ
    rw [hX, ← Subgroup.map_iSup, h1, map_top_of_surjective _ (QuotientGroup.mk'_surjective Q')]
  have hS : IsSylowTwoOf S L := A4.isSylowTwoOf_inf_normal hT hLH hHL
  set S' : Subgroup L := S.subgroupOf L with hS'
  have hS'p : IsPGroup 2 S' := hS.2.1.comap_of_injective L.subtype L.subtype_injective
  have hS'syl : ¬ 2 ∣ S'.index := hS.2.2
  set P : Sylow 2 (L ⧸ Q') := (hS'p.map φ).toSylow fun h =>
    hS'syl (dvd_trans h (index_map_dvd _ (QuotientGroup.mk'_surjective Q'))) with hP
  obtain ⟨hsolP, hZP⟩ := product_sylow X hcomm hind htop
    (fun j P₁ P₂ Y => bender_sylow_eq (hXB j) P₁ P₂) (fun j => bender_isSolvable_normalizer (hXB j))
    P
  have hPS : (P : Subgroup (L ⧸ Q')) = S'.map φ := rfl
  have hQS : Q' ≤ S' := by
    have := CFSG.pCore_isPGroup (p := 2) (G := L)
    exact this.le_sylow_of_normal (hS'p.toSylow hS'syl)
  have hcomapP : (P : Subgroup (L ⧸ Q')).comap φ = S' := by
    rw [hPS, comap_map_eq, hφ, QuotientGroup.ker_mk', sup_eq_left.2 hQS]
  have hnormL : ∀ x : L, x ∈ normalizer (S' : Set L) ↔ (x : G) ∈ normalizer (S : Set G) := by
    intro x
    rw [mem_normalizer_iff, mem_normalizer_iff]
    constructor
    · intro hx g
      by_cases hgL : g ∈ L
      · have := hx ⟨g, hgL⟩
        simpa [hS', mem_subgroupOf] using this
      · constructor
        · intro hg
          exact absurd hg.2 hgL
        · intro hg
          exfalso
          apply hgL
          have := mul_mem (mul_mem (inv_mem x.2) hg.2) x.2
          simpa [mul_assoc] using this
    · intro hx g
      have := hx g
      simpa [hS', mem_subgroupOf] using this
  have hnormφ : ∀ x : L, φ x ∈ normalizer ((P : Subgroup (L ⧸ Q')) : Set (L ⧸ Q')) →
      (x : G) ∈ normalizer (S : Set G) := by
    intro x hx
    rw [← hnormL, ← hcomapP]
    exact le_normalizer_comap φ hx
  refine ⟨?_, fun Y hTY hYH => ?_⟩
  ·
    set M : Subgroup G := (H ⊓ normalizer (S : Set G)) ⊓ L with hM
    have hMeq : H ⊓ normalizer (S : Set G) = T ⊔ M :=
      A3.eq_sup_inf_of_le_sup hTL (le_inf hTH hTS) (hHT ▸ inf_le_left.trans (sup_comm _ _).le)
    have hML : M ≤ L := inf_le_right
    have hψ : ∀ x : M, φ ⟨x, hML x.2⟩ ∈ normalizer ((P : Subgroup (L ⧸ Q')) : Set (L ⧸ Q')) :=
      fun x => by
        rw [hPS]
        exact le_normalizer_map φ ⟨⟨x, hML x.2⟩, (hnormL _).2 x.2.1.2, rfl⟩
    let ψ : M →* normalizer ((P : Subgroup (L ⧸ Q')) : Set (L ⧸ Q')) :=
      (φ.comp (inclusion hML)).codRestrict _ hψ
    have hker : IsPGroup 2 ψ.ker := by
      intro x
      have hx : φ ⟨x, hML x.1.2⟩ = 1 := by
        have h0 : ψ x.1 = 1 := x.2
        exact congrArg Subtype.val h0
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 2) (G := L) ⟨_, hx⟩
      refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun y : CFSG.pCore 2 L => ((y : L) : G)) hm
      simpa using this
    have : Group.IsSolvable ψ.ker := by
      have := hker.isNilpotent
      infer_instance
    have : Group.IsSolvable M := Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by
      rw [range_subtype])
    have hTs : Group.IsSolvable T := by
      have := hT.2.1.isNilpotent
      infer_instance
    have hTM : T ≤ normalizer (M : Set G) := fun t ht =>
      inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
        ⟨le_normalizer (hTH ht), le_normalizer (hTS ht)⟩, hTL ht⟩
    rw [hMeq, sup_comm]
    exact A3.isSolvable_sup_of_le_normalizer hTM
  ·
    by_cases hYN : Y ≤ normalizer (S : Set G)
    · exact Or.inr hYN
    left
    have hYL : ¬ Y ⊓ L ≤ normalizer (S : Set G) := fun h => by
      apply hYN
      rw [A3.eq_sup_inf_of_le_sup hTL hTY (hYH.trans (hHT ▸ (sup_comm _ _).le))]
      exact sup_le hTS h
    set Z : Subgroup (L ⧸ Q') := ((Y ⊓ L).subgroupOf L).map φ with hZ
    have hPZ : (P : Subgroup (L ⧸ Q')) ≤ Z := by
      rw [hPS]
      refine map_mono fun x hx => ?_
      exact ⟨hTY hx.1, hx.2⟩
    have hZN : ¬ Z ≤ normalizer ((P : Subgroup (L ⧸ Q')) : Set (L ⧸ Q')) := fun h => by
      apply hYL
      intro y hy
      exact hnormφ ⟨y, hy.2⟩ (h ⟨⟨y, hy.2⟩, hy, rfl⟩)
    obtain ⟨j, hj⟩ := hZP Z hPZ hZN
    have hJY : (j : Subgroup G) ≤ Y := by
      intro a ha
      obtain ⟨b, hb, hba⟩ := hj ⟨⟨a, hJL j ha⟩, ha, rfl⟩
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hba
      have h1 : a = (b : G) * ((b⁻¹ * ⟨a, hJL j ha⟩ : L) : G) := by
        simp
      rw [h1]
      exact mul_mem hb.1 (hTY (hQS hba).1)
    obtain ⟨t, ht, hjt⟩ := hJt j
    have hKY : K ≤ Y := fun k hk => by
      have h0 : t * k * t⁻¹ ∈ (j : Subgroup G) := by
        rw [hjt]
        exact ⟨k, hk, rfl⟩
      have h1 : t * k * t⁻¹ ∈ Y := hJY h0
      have := mul_mem (mul_mem (inv_mem (hTY ht)) h1) (hTY ht)
      simpa [mul_assoc] using this
    have hLY : L ≤ Y := conjClosure_le fun t' ht' k hk =>
      mul_mem (mul_mem (hTY ht') (hKY hk)) (inv_mem (hTY ht'))
    exact le_antisymm hYH (hHT ▸ sup_le hLY hTY)

theorem kgRankOneOvergroups_holds : H13.KGRankOneOvergroups := by
  intro G _ _ H T K _ _ hT hK hHT hn
  obtain ⟨n, hn⟩ := hn
  obtain ⟨i, e, hB⟩ : ∃ i e, BenderType (K ⧸ CFSG.pCore 2 K) n i e := by
    rcases hn with ⟨hn2, hL⟩ | ⟨hn3, hSz⟩
    · obtain ⟨i, e, h, -⟩ := benderType_of_rank_one hn2 (Or.inl hL)
      exact ⟨i, e, h⟩
    · obtain ⟨i, e, h, -⟩ := benderType_of_rank_one (by omega) (Or.inr (Or.inl hSz))
      exact ⟨i, e, h⟩
  exact rankOne_overgroups hT hK hHT hB

end CFSG.Quasithin.H13.NQCat.RkOne
