module

public import CFSG.Quasithin.H13.NQBlockSinglePrime
public import CFSG.Quasithin.H13.NQTermThompsonFactorization
public import CFSG.Quasithin.SteinbergCCNormalizerFactorization
public import CFSG.Quasithin.SteinbergCDPrimeKernelOvergroups
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement Pointwise

theorem two_core_quotient_image {H : Type*} [Group H] [Finite H] {A Z : Subgroup H}
    (hZA : Z ≤ A) (hAZ : A ≤ normalizer (Z : Set H)) {s : ℕ} [hs : Fact s.Prime]
    (hZs : IsPGroup s (Z ⧸ CFSG.pCore 2 Z)) (hZnt : Nontrivial (Z ⧸ CFSG.pCore 2 Z)) :
    Z ⊓ (CFSG.pCore 2 A).map A.subtype = (CFSG.pCore 2 Z).map Z.subtype ∧
      (∃ φ : Z ⧸ CFSG.pCore 2 Z ≃* ((Z.subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A))),
        ∀ z : Z, (φ (z : Z ⧸ CFSG.pCore 2 Z) : A ⧸ CFSG.pCore 2 A) =
          QuotientGroup.mk' (CFSG.pCore 2 A) ⟨z, hZA z.2⟩) ∧
      (Z.subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A)) ≠ ⊥ ∧
      ((Z.subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A))).Normal ∧
      IsPGroup s ((Z.subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A))) ∧
      (Z.subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A)) ≤
        CFSG.pCore s (A ⧸ CFSG.pCore 2 A) ∧
      CFSG.pCore s (A ⧸ CFSG.pCore 2 A) ≤ CFSG.fittingSubgroup (A ⧸ CFSG.pCore 2 A) ∧
      s ∣ Nat.card (CFSG.fittingSubgroup (A ⧸ CFSG.pCore 2 A)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZn : (Z.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hZA).mpr hAZ
  have hO2Z : ((CFSG.pCore 2 Z).map Z.subtype).subgroupOf A ≤ CFSG.pCore 2 A := by
    refine CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup
      ((normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hZA)).mpr fun g hg =>
        mem_normalizer_map_of_characteristic (CFSG.pCore 2 Z) (hAZ hg)) ?_
    rw [← comap_subtype]
    exact (CFSG.pCore_isPGroup.map _).comap_subtype
  have hNO2A : A ≤ normalizer (((CFSG.pCore 2 A).map A.subtype : Subgroup H) : Set H) :=
    fun g hg => mem_normalizer_map_of_characteristic (CFSG.pCore 2 A) (le_normalizer hg)
  have hO2A : ((CFSG.pCore 2 A).map A.subtype).subgroupOf Z ≤ CFSG.pCore 2 Z := by
    refine CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup ⟨fun x hx g => ?_⟩ ?_
    · rw [mem_subgroupOf] at hx ⊢
      exact (mem_normalizer_iff.mp (hNO2A (hZA g.2)) _).mp hx
    · rw [← comap_subtype]
      exact (CFSG.pCore_isPGroup.map _).comap_subtype
  have hZO2 : Z ⊓ (CFSG.pCore 2 A).map A.subtype = (CFSG.pCore 2 Z).map Z.subtype := by
    apply le_antisymm
    · rintro x ⟨hxZ, hxA⟩
      exact ⟨⟨x, hxZ⟩, hO2A (mem_subgroupOf.mpr hxA), rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine mem_inf.mpr ⟨z.2, ?_⟩
      have h1 := hO2Z (x := ⟨z, hZA z.2⟩) (mem_subgroupOf.mpr ⟨z, hz, rfl⟩)
      exact ⟨_, h1, rfl⟩
  set ψ : Z →* A ⧸ CFSG.pCore 2 A := (QuotientGroup.mk' (CFSG.pCore 2 A)).comp (inclusion hZA)
    with hψ
  have hψker : ψ.ker = CFSG.pCore 2 Z := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have h1 : (x : H) ∈ Z ⊓ (CFSG.pCore 2 A).map A.subtype := mem_inf.mpr ⟨x.2, ⟨_, hx, rfl⟩⟩
      rw [hZO2] at h1
      exact (mem_map_iff_mem Z.subtype_injective).mp h1
    · intro hx
      exact hO2Z (mem_subgroupOf.mpr ⟨x, hx, rfl⟩)
  have hψrange : ψ.range = (Z.subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A)) := by
    rw [hψ, MonoidHom.range_comp, inclusion_range]
  set B := (Z.subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A)) with hB
  set φ : Z ⧸ CFSG.pCore 2 Z ≃* B := (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hψrange)) with hφ
  have hBn : B.Normal := hZn.map _ (QuotientGroup.mk'_surjective _)
  have hBs : IsPGroup s B := hZs.of_equiv φ
  have hBnt : Nontrivial B := φ.symm.toEquiv.nontrivial
  have hBne : B ≠ ⊥ := (nontrivial_iff_ne_bot B).mp hBnt
  have hBQ : B ≤ CFSG.pCore s (A ⧸ CFSG.pCore 2 A) :=
    CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup hBn hBs
  have hQF : CFSG.pCore s (A ⧸ CFSG.pCore 2 A) ≤ CFSG.fittingSubgroup (A ⧸ CFSG.pCore 2 A) :=
    CFSG.pCore_le_fitting _ s
  refine ⟨hZO2, ⟨φ, fun z => rfl⟩, hBne, hBn, hBs, hBQ, hQF, ?_⟩
  rcases hBs.card_eq_or_dvd with h | h
  · exact absurd h Finite.one_lt_card.ne'
  · exact h.trans (card_dvd_of_le (hBQ.trans hQF))

theorem elemThompson_two_ne_bot {R : Type*} [Group R] [Finite R] [Nontrivial R]
    (hR : IsPGroup 2 R) : CFSG.elemThompson R 2 ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2
    (hR.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne')
  have hBcard : Nat.card (zpowers x) = 2 := by rw [Nat.card_zpowers, hx]
  have hB : IsElementaryAbelian 2 (zpowers x) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
        rw [← hBcard]
        exact pow_card_eq_one' }
  have h1 := CFSG.Quasithin.BlueprintB2.card_le_pow_pRank hB
  obtain ⟨A, hA, hAcard⟩ := CFSG.Quasithin.BlueprintB2.exists_card_eq_pow_pRank R 2
  have hAJ := CFSG.Quasithin.BlueprintB2.le_elemThompson (A := A) ⟨hA, hAcard⟩
  intro hJ
  rw [hJ, le_bot_iff] at hAJ
  rw [hAJ, card_bot] at hAcard
  rw [hBcard, ← hAcard] at h1
  omega

theorem le_perfectResidual_map_of_isPerfect {H : Type*} [Group H] [Finite H] {Y A : Subgroup H}
    (hY : Group.IsPerfect Y) (hYA : Y ≤ A) : Y ≤ (CFSG.perfectResidual A).map A.subtype := by
  have hYperf : Group.IsPerfect (Y.subgroupOf A) := by
    rw [isPerfect_iff]
    apply map_injective (subtype_injective A)
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hYA, isPerfect_iff.mp hY]
  have hYD := (CFSG.perfect_residual_transport (MonoidHom.id A)).2.2 _ hYperf
  exact fun y hy => ⟨⟨y, hYA hy⟩, hYD (mem_subgroupOf.mpr hy), rfl⟩

theorem frattiniQuotConj_irreducible_of_ambient {H : Type*} [Group H] [Finite H]
    {L : Subgroup H} [L.Normal] {X : Subgroup L} [X.Characteristic] {Y : Subgroup H}
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ y ∈ Y, ∀ u ∈ U, ambientResidualAction L X y u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ y ∈ Y, ∃ w, ambientResidualAction L X y w ≠ w) :
    (∀ U : Subgroup ((X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype)) ⧸
        frattini (X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype))),
      (∀ y ∈ Y, ∀ u ∈ U, CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype) y u ∈ U) →
        U = ⊥ ∨ U = ⊤) ∧
      ∃ y ∈ Y, ∃ w, CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype) y w ≠ w := by
  classical
  obtain ⟨ι, ιP, ιW, -, -, hιW⟩ := ambient_transport L X
  refine ⟨fun U hU => ?_, ?_⟩
  · have hsurj : Function.Surjective ιW.toMonoidHom := ιW.surjective
    have h1 := hirr (U.comap ιW.toMonoidHom) (fun y hy u hu => by
      rw [mem_comap, MulEquiv.coe_toMonoidHom] at hu ⊢
      rw [hιW]
      exact hU y hy _ hu)
    rcases h1 with h1 | h1
    · left
      rw [← map_comap_eq_self_of_surjective hsurj U, h1, Subgroup.map_bot]
    · right
      rw [← map_comap_eq_self_of_surjective hsurj U, h1, map_top_of_surjective _ hsurj]
  · obtain ⟨y, hy, w, hw⟩ := hnt
    refine ⟨y, hy, ιW w, fun h => hw (ιW.injective ?_)⟩
    rw [hιW, h]

theorem thompson_factorization_in_ambient {H : Type} [Group H] [Finite H] {V R : Subgroup H}
    [Group.IsSolvable V] (hF : CFSG.generalizedFitting V = CFSG.pCore 2 V)
    (h3 : ¬ 3 ∣ Nat.card V) (hR : CFSG.ABGLocalTools.IsSylowOf 2 R V) :
    (V : Set H) = ((V ⊓ normalizer
        (((CFSG.elemThompson R 2).map R.subtype : Subgroup H) : Set H) : Subgroup H) : Set H) *
      ((V ⊓ centralizer (CFSG.Open.quasithinOmegaOneCenter R : Set H) : Subgroup H) : Set H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hR
  have hfact :=
    CFSG.Quasithin.H13.NQTerm.solvable_characteristic_two_three_free_thompson_factorization
      hF h3 S rfl rfl rfl
  obtain ⟨-, -, -, -, -, -, hNZ, -⟩ := hfact
  set J : Subgroup V := (CFSG.elemThompson (S : Subgroup V) 2).map (S : Subgroup V).subtype
    with hJ
  set Z : Subgroup V := CFSG.Open.quasithinOmegaOneCenter (S : Subgroup V) with hZ
  set C₁ := (CFSG.elemThompson R 2).map R.subtype with hC₁
  set C₂ := CFSG.Open.quasithinOmegaOneCenter R with hC₂
  have hJmap : J.map V.subtype = C₁ := by
    set e : (S : Subgroup V) ≃* R := ((S : Subgroup V).equivMapOfInjective V.subtype
      V.subtype_injective).trans (MulEquiv.subgroupCongr hS) with he
    have h1 := CFSG.QuasithinUnique.Setup.Campbell.elemThompson_map_mulEquiv e 2
    rw [hC₁, ← h1, map_map, map_map]
    rfl
  have hRV : R ≤ V := hS ▸ map_subtype_le _
  have hZmap : Z.map V.subtype = C₂ := by
    rw [hZ, hC₂, CFSG.Open.quasithinOmegaOneCenter, CFSG.Open.quasithinOmegaOneCenter,
      MonoidHom.map_closure]
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_ofPred_eq, mem_inf, mem_centralizer_iff, subtype_apply]
    constructor
    · rintro ⟨z, ⟨⟨hzS, hzC⟩, hz2⟩, rfl⟩
      refine ⟨⟨hS ▸ ⟨z, hzS, rfl⟩, ?_⟩, ?_⟩
      · intro r hr
        rw [← hS] at hr
        obtain ⟨s, hs, rfl⟩ := hr
        exact congrArg Subtype.val (hzC s hs)
      · rw [← SubgroupClass.coe_pow, hz2, OneMemClass.coe_one]
    · rintro ⟨⟨hhR, hhC⟩, hh2⟩
      have hhR' := hhR
      rw [← hS] at hhR'
      obtain ⟨s, hs, rfl⟩ := hhR'
      refine ⟨s, ⟨⟨hs, fun s' hs' => Subtype.ext (hhC _ (hS ▸ ⟨s', hs', rfl⟩))⟩,
        Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hh2)⟩, rfl⟩
  have hJsub : C₁.subgroupOf V = J := by
    rw [← hJmap, Subgroup.subgroupOf, comap_map_eq_self_of_injective V.subtype_injective]
  have hNmap : (normalizer (J : Set V)).map V.subtype = V ⊓ normalizer (C₁ : Set H) := by
    have hC₁V : C₁ ≤ V := hJmap ▸ map_subtype_le _
    rw [← hJsub, ← subgroupOf_normalizer_eq hC₁V, subgroupOf_map_subtype, inf_comm]
  have hCmap : (centralizer (Z : Set V)).map V.subtype = V ⊓ centralizer (C₂ : Set H) := by
    ext h
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine mem_inf.mpr ⟨v.2, ?_⟩
      rw [mem_centralizer_iff]
      rw [← hZmap]
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hv z hz)
    · rintro ⟨hhV, hhC⟩
      refine ⟨⟨h, hhV⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro z hz
      apply Subtype.ext
      exact mem_centralizer_iff.mp hhC _ (hZmap ▸ ⟨z, hz, rfl⟩)
  have himg : (V : Set H) = V.subtype '' Set.univ := by
    rw [Set.image_univ, coe_subtype, Subtype.range_coe]
  rw [himg, ← hNZ, Set.image_mul, ← coe_map, ← coe_map, hNmap, hCmap]

theorem two_prime_capture_data
    {H : Type} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hSQT : CFSG.IsStronglyQuasithin L) (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (T : Sylow 2 H) (hLT : L ⊔ (T : Subgroup H) = ⊤)
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    (hF : CFSG.generalizedFitting L = CFSG.pCore 2 L)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {X : Subgroup L} (hX : IsOddResidualWitness p X)
    {q : ℕ} (hqF : q ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors)
    (Q D : Subgroup (L ⧸ CFSG.pCore 2 L)) (E Xq : Subgroup L)
    (hQ : Q = CFSG.pCore q (L ⧸ CFSG.pCore 2 L)) (hD : D = closure {a | a ∈ Q ∧ a ^ q = 1})
    (hE : E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)))
    (hXq : Xq = closure {e | e ∈ E ∧ Odd (orderOf e)}) :
    let R := (CFSG.pCore 2 (X.map L.subtype ⊔ (T : Subgroup H) : Subgroup H)).map
      (X.map L.subtype ⊔ (T : Subgroup H)).subtype
    let Y := (CFSG.perfectResidual (L ⊓ normalizer (R : Set H) : Subgroup H)).map
      (L ⊓ normalizer (R : Set H)).subtype
    5 ≤ q ∧ (CFSG.pCore 2 L).map L.subtype ≠ ⊥ ∧ (CFSG.pCore 2 L).map L.subtype ≤ R ∧
      Group.IsPerfect Y ∧ X.map L.subtype ≤ Y ∧ Y ≤ L ⊓ normalizer (R : Set H) ∧
      ∃ _ : Xq.Characteristic, IsOddResidualWitness q Xq ∧
      (∀ U : Subgroup ((Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)),
        (∀ y ∈ Y, ∀ u ∈ U, ambientResidualAction L Xq y u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      (∃ y ∈ Y, ∃ w, ambientResidualAction L Xq y w ≠ w) ∧
      Group.IsSolvable (Xq.map L.subtype ⊔ R : Subgroup H) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 R (Xq.map L.subtype ⊔ R) ∧
      CFSG.generalizedFitting (Xq.map L.subtype ⊔ R : Subgroup H) =
        CFSG.pCore 2 (Xq.map L.subtype ⊔ R : Subgroup H) ∧
      ¬ 3 ∣ Nat.card (Xq.map L.subtype ⊔ R : Subgroup H) := by
  intro R Y
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXc := hX.characteristic
  have hall := all_canonical_prime_witnesses_retain_original_normalizer_derived_Frattini_actions
    hSQT hLC T hLT hq hp5 hX
  obtain ⟨hNR, hYperf, -, hXY, -, hqall⟩ := hall
  obtain ⟨hq5, hXqc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hYnt, hYirr, -, -, hVs, h2q, -,
    hSyl⟩ := hqall q hqF Q D E Xq hQ hD hE hXq
  have hcw := canonical_prime_witness hSQT hLC hq hqF Q D E Xq hQ hD hE hXq
  obtain ⟨-, -, hWq, -⟩ := hcw
  have hCF := CFSG.centralizer_generalizedFitting_le L
  rw [hF] at hCF
  have hN2 : IsPGroup 2 ((CFSG.pCore 2 L).map L.subtype) := CFSG.pCore_isPGroup.map _
  have hXnt : Nontrivial ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hX.card_W]
    exact Nat.one_lt_pow two_ne_zero hp.out.one_lt
  have hNne : (CFSG.pCore 2 L).map L.subtype ≠ ⊥ := by
    intro h
    have hN : CFSG.pCore 2 L = ⊥ := (map_eq_bot_iff_of_injective _ L.subtype_injective).mp h
    have hL1 : ∀ l : L, l = 1 := by
      intro l
      have h1 : l ∈ centralizer ((CFSG.pCore 2 L : Subgroup L) : Set L) := by
        rw [mem_centralizer_iff]
        intro m hm
        rw [hN, SetLike.mem_coe, mem_bot] at hm
        rw [hm, one_mul, mul_one]
      have h2 := hCF h1
      rwa [hN, mem_bot] at h2
    obtain ⟨w1, w2, hw⟩ := exists_pair_ne ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))
    apply hw
    obtain ⟨u1, rfl⟩ := QuotientGroup.mk_surjective w1
    obtain ⟨u2, rfl⟩ := QuotientGroup.mk_surjective w2
    obtain ⟨x1, rfl⟩ := QuotientGroup.mk_surjective u1
    obtain ⟨x2, rfl⟩ := QuotientGroup.mk_surjective u2
    have h12 : x1 = x2 := Subtype.ext ((hL1 _).trans (hL1 _).symm)
    rw [h12]
  have hCL : L ⊓ centralizer (((CFSG.pCore 2 L).map L.subtype : Subgroup H) : Set H) ≤
      (CFSG.pCore 2 L).map L.subtype := by
    rintro h ⟨hhL, hhC⟩
    have h1 : (⟨h, hhL⟩ : L) ∈ centralizer ((CFSG.pCore 2 L : Subgroup L) : Set L) := by
      rw [mem_centralizer_iff]
      intro m hm
      apply Subtype.ext
      exact mem_centralizer_iff.mp hhC _ ⟨m, hm, rfl⟩
    exact ⟨_, hCF h1, rfl⟩
  have hHL : IsPGroup 2 (H ⧸ L) := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    have hg : g ∈ ((L ⊔ (T : Subgroup H) : Subgroup H) : Set H) := by
      rw [hLT]
      exact (mem_top g : g ∈ (⊤ : Subgroup H))
    rw [normal_mul, Set.mem_mul] at hg
    obtain ⟨l, hl, t, ht, rfl⟩ := hg
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
    refine ⟨k, ?_⟩
    have hk' : t ^ 2 ^ k = 1 := by
      have h1 := congrArg Subtype.val hk
      rwa [SubgroupClass.coe_pow] at h1
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l).mpr hl, one_mul, ← QuotientGroup.mk_pow,
      hk', QuotientGroup.mk_one]
  have hNV : (CFSG.pCore 2 L).map L.subtype ≤ Xq.map L.subtype ⊔ R := hNR.trans le_sup_right
  obtain ⟨-, -, -, -, -, hFV⟩ :=
    CFSG.Quasithin.SteinbergCD.normal_prime_kernel_overgroups_characteristic_prime
      Nat.prime_two L hHL ((CFSG.pCore 2 L).map L.subtype) hN2 hCL _ hNV
  have h3 : ¬ 3 ∣ Nat.card (Xq.map L.subtype ⊔ R : Subgroup H) := fun h => by
    rcases h2q 3 Nat.prime_three h with h' | h' <;> omega
  exact ⟨hq5, hNne, hNR, hYperf, hXY, map_subtype_le _, hXqc, hWq, hYirr, hYnt, hVs, hSyl, hFV,
    h3⟩

theorem thompson_center_subgroups {H : Type*} [Group H] [Finite H] {R : Subgroup H}
    (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    (CFSG.elemThompson R 2).map R.subtype ≠ ⊥ ∧ (CFSG.elemThompson R 2).map R.subtype ≤ R ∧
      (((CFSG.elemThompson R 2).map R.subtype).subgroupOf R).Characteristic ∧
      CFSG.Open.quasithinOmegaOneCenter R ≠ ⊥ ∧ CFSG.Open.quasithinOmegaOneCenter R ≤ R ∧
      ((CFSG.Open.quasithinOmegaOneCenter R).subgroupOf R).Characteristic ∧
      normalizer (R : Set H) ≤
        normalizer (((CFSG.elemThompson R 2).map R.subtype : Subgroup H) : Set H) ∧
      normalizer (R : Set H) ≤ normalizer (CFSG.Open.quasithinOmegaOneCenter R : Set H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hR1
  have hC₁ : (CFSG.elemThompson R 2).map R.subtype ≠ ⊥ := by
    rw [Ne, map_eq_bot_iff_of_injective _ R.subtype_injective]
    exact elemThompson_two_ne_bot hR2
  have hC₁sub : ((CFSG.elemThompson R 2).map R.subtype).subgroupOf R = CFSG.elemThompson R 2 := by
    rw [Subgroup.subgroupOf, comap_map_eq_self_of_injective R.subtype_injective]
  have hC₁c : (((CFSG.elemThompson R 2).map R.subtype).subgroupOf R).Characteristic := by
    rw [hC₁sub]
    exact CFSG.Quasithin.BlueprintB2.elemThompson_characteristic R 2
  have hC₂ : CFSG.Open.quasithinOmegaOneCenter R ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hR2 hR1
  have hC₂le : CFSG.Open.quasithinOmegaOneCenter R ≤ R := by
    rw [CFSG.Open.quasithinOmegaOneCenter, closure_le]
    exact fun z hz => (mem_inf.mp hz.1).1
  have hC₂c : ((CFSG.Open.quasithinOmegaOneCenter R).subgroupOf R).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R
  have hnorm : ∀ C : Subgroup H, C ≤ R → (C.subgroupOf R).Characteristic →
      normalizer (R : Set H) ≤ normalizer (C : Set H) := by
    intro C hCR hCc g hg
    have h1 := mem_normalizer_map_of_characteristic (C.subgroupOf R) hg
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr hCR] at h1
  exact ⟨hC₁, map_subtype_le _, hC₁c, hC₂, hC₂le, hC₂c, hnorm _ (map_subtype_le _) hC₁c,
    hnorm _ hC₂le hC₂c⟩

open CFSG.Quasithin.SteinbergCC
  (characteristic_normalizer_factorization_captures_original_prime_witness_in_perfect_residual) in
theorem original_multiple_prime_radical_captures_two_primes_in_actual_characteristic_normalizer
    {H : Type} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hSQT : CFSG.IsStronglyQuasithin L) (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (T : Sylow 2 H) (hLT : L ⊔ (T : Subgroup H) = ⊤)
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    (hF : CFSG.generalizedFitting L = CFSG.pCore 2 L)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {X : Subgroup L} (hX : IsOddResidualWitness p X)
    {q : ℕ} (hqF : q ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors)
    (hqp : q ≠ p) (Q D : Subgroup (L ⧸ CFSG.pCore 2 L)) (E Xq : Subgroup L)
    (hQ : Q = CFSG.pCore q (L ⧸ CFSG.pCore 2 L)) (hD : D = closure {a | a ∈ Q ∧ a ^ q = 1})
    (hE : E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)))
    (hXq : Xq = closure {e | e ∈ E ∧ Odd (orderOf e)}) :
    let R := (CFSG.pCore 2 (X.map L.subtype ⊔ (T : Subgroup H) : Subgroup H)).map
      (X.map L.subtype ⊔ (T : Subgroup H)).subtype
    let Y := (CFSG.perfectResidual (L ⊓ normalizer (R : Set H) : Subgroup H)).map
      (L ⊓ normalizer (R : Set H)).subtype
    let C₁ := (CFSG.elemThompson R 2).map R.subtype
    let C₂ := CFSG.Open.quasithinOmegaOneCenter R
    let A₁ := (CFSG.perfectResidual (L ⊓ normalizer (C₁ : Set H) : Subgroup H)).map
      (L ⊓ normalizer (C₁ : Set H)).subtype
    let A₂ := (CFSG.perfectResidual (L ⊓ normalizer (C₂ : Set H) : Subgroup H)).map
      (L ⊓ normalizer (C₂ : Set H)).subtype
    let V := Xq.map L.subtype ⊔ R
    5 ≤ q ∧ (CFSG.pCore 2 L).map L.subtype ≠ ⊥ ∧ (CFSG.pCore 2 L).map L.subtype ≤ R ∧
      C₁ ≠ ⊥ ∧ C₁ ≤ R ∧ (C₁.subgroupOf R).Characteristic ∧
      C₂ ≠ ⊥ ∧ C₂ ≤ R ∧ (C₂.subgroupOf R).Characteristic ∧
      Group.IsSolvable V ∧ CFSG.ABGLocalTools.IsSylowOf 2 R V ∧
      CFSG.generalizedFitting V = CFSG.pCore 2 V ∧ ¬ 3 ∣ Nat.card V ∧
      (V : Set H) = ((V ⊓ normalizer (C₁ : Set H) : Subgroup H) : Set H) *
        ((V ⊓ centralizer (C₂ : Set H) : Subgroup H) : Set H) ∧
      (V : Set H) = ((V ⊓ normalizer (C₁ : Set H) : Subgroup H) : Set H) *
        ((V ⊓ normalizer (C₂ : Set H) : Subgroup H) : Set H) ∧
      X.map L.subtype ≤ Y ∧ Y ≤ A₁ ∧ Y ≤ A₂ ∧
      ∃ A : Subgroup H, (A = A₁ ∨ A = A₂) ∧ Xq.map L.subtype ≤ A ∧
        ∀ (s : ℕ) (Xs : Subgroup L), (s = p ∧ Xs = X ∨ s = q ∧ Xs = Xq) →
          ∃ hsA : Xs.map L.subtype ≤ A,
          Xs.map L.subtype ⊓ (CFSG.pCore 2 A).map A.subtype =
              (CFSG.pCore 2 (Xs.map L.subtype)).map (Xs.map L.subtype).subtype ∧
            (∃ φ : Xs.map L.subtype ⧸ CFSG.pCore 2 (Xs.map L.subtype) ≃*
                (((Xs.map L.subtype).subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A))),
              ∀ z : Xs.map L.subtype,
                (φ (z : Xs.map L.subtype ⧸ CFSG.pCore 2 (Xs.map L.subtype)) : A ⧸ CFSG.pCore 2 A) =
                  QuotientGroup.mk' (CFSG.pCore 2 A) ⟨z, hsA z.2⟩) ∧
            ((Xs.map L.subtype).subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A)) ≠ ⊥ ∧
            (((Xs.map L.subtype).subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A))).Normal ∧
            IsPGroup s (((Xs.map L.subtype).subgroupOf A).map
              (QuotientGroup.mk' (CFSG.pCore 2 A))) ∧
            ((Xs.map L.subtype).subgroupOf A).map (QuotientGroup.mk' (CFSG.pCore 2 A)) ≤
              CFSG.pCore s (A ⧸ CFSG.pCore 2 A) ∧
            CFSG.pCore s (A ⧸ CFSG.pCore 2 A) ≤ CFSG.fittingSubgroup (A ⧸ CFSG.pCore 2 A) ∧
            s ∣ Nat.card (CFSG.fittingSubgroup (A ⧸ CFSG.pCore 2 A)) := by
  intro R Y C₁ C₂ A₁ A₂ V
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXc := hX.characteristic
  have hdata := two_prime_capture_data hSQT hLC T hLT hq hF hp5 hX hqF Q D E Xq hQ hD hE hXq
  obtain ⟨hq5, hNne, hNR, hYperf, hXY, hYLR, hXqc, hWq, hYirr, hYnt, hVs, hSyl, hFV, h3⟩ := hdata
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF⟩
  have hq2 : q ≠ 2 := by omega
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup.map _
  have hR1 : R ≠ ⊥ := fun h => hNne (le_bot_iff.mp (h ▸ hNR))
  obtain ⟨hC₁, hC₁R, hC₁c, hC₂, hC₂R, hC₂c, hNC₁, hNC₂⟩ := thompson_center_subgroups hR2 hR1
  have hfact1 := thompson_factorization_in_ambient hFV h3 hSyl
  have hfact2 : (V : Set H) = ((V ⊓ normalizer (C₁ : Set H) : Subgroup H) : Set H) *
      ((V ⊓ normalizer (C₂ : Set H) : Subgroup H) : Set H) := by
    apply le_antisymm
    · intro v hv
      rw [hfact1] at hv
      obtain ⟨a, ha, b, hb, rfl⟩ := hv
      exact ⟨a, ha, b, mem_inf.mpr ⟨(mem_inf.mp hb).1,
        centralizer_le_normalizer _ (mem_inf.mp hb).2⟩, rfl⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact mul_mem (mem_inf.mp ha).1 (mem_inf.mp hb).1
  have hYL : Y ≤ L := hYLR.trans inf_le_left
  have hYR : Y ≤ normalizer (R : Set H) := hYLR.trans inf_le_right
  have hYA₁ : Y ≤ A₁ := le_perfectResidual_map_of_isPerfect hYperf (le_inf hYL (hYR.trans hNC₁))
  have hYA₂ : Y ≤ A₂ := le_perfectResidual_map_of_isPerfect hYperf (le_inf hYL (hYR.trans hNC₂))
  obtain ⟨hX2q, hPq, hWq', -, -, -⟩ := witness_frattiniQuotConj (H := H) hWq
  obtain ⟨hirrq, hntq⟩ := frattiniQuotConj_irreducible_of_ambient hYirr hYnt
  have hO2q : (CFSG.pCore 2 (Xq.map L.subtype)).map (Xq.map L.subtype).subtype ≤ R := by
    refine le_trans ?_ hNR
    intro x hx
    have hxL : x ∈ L := (map_subtype_le _ : _ ≤ Xq.map L.subtype) hx |> fun h =>
      (map_subtype_le Xq) h
    have hn : (((CFSG.pCore 2 (Xq.map L.subtype)).map (Xq.map L.subtype).subtype).subgroupOf
        L).Normal := ⟨fun y hy g => by
      rw [mem_subgroupOf] at hy ⊢
      exact (inferInstance : ((CFSG.pCore 2 (Xq.map L.subtype)).map
        (Xq.map L.subtype).subtype).Normal).conj_mem _ hy g⟩
    have hp2' : IsPGroup 2 (((CFSG.pCore 2 (Xq.map L.subtype)).map
        (Xq.map L.subtype).subtype).subgroupOf L) := by
      rw [← comap_subtype]
      exact (CFSG.pCore_isPGroup.map _).comap_subtype
    have hle := CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup hn hp2'
    exact ⟨⟨x, hxL⟩, hle (mem_subgroupOf.mpr hx), rfl⟩
  have hcap :=
    characteristic_normalizer_factorization_captures_original_prime_witness_in_perfect_residual
      (map_subtype_le Xq) (Nat.prime_of_mem_primeFactors hqF) hq2 hX2q hPq hWq' hR2 hO2q hYL hYperf
      hYR hirrq hntq hC₁R hC₂R hC₁c hC₂c hfact2
  obtain ⟨-, -, -, -, C, hC, -, hXA, -⟩ := hcap
  set A := (CFSG.perfectResidual (L ⊓ normalizer (C : Set H) : Subgroup H)).map
    (L ⊓ normalizer (C : Set H)).subtype with hA
  have hAi : A = A₁ ∨ A = A₂ := by
    rcases hC with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hYA : Y ≤ A := by
    rcases hAi with h | h <;> rw [h]
    · exact hYA₁
    · exact hYA₂
  refine ⟨hq5, hNne, hNR, hC₁, hC₁R, hC₁c, hC₂, hC₂R, hC₂c, hVs, hSyl, hFV, h3, hfact1, hfact2,
    hXY, hYA₁, hYA₂, A, hAi, hXA, ?_⟩
  rintro s Xs hs
  obtain ⟨hXsA, hXsc, hWs, hsp⟩ : ∃ _ : Xs.map L.subtype ≤ A, ∃ _ : Xs.Characteristic,
      ∃ _ : IsOddResidualWitness s Xs, Fact s.Prime := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hXY.trans hYA, hXc, hX, hp⟩
    · exact ⟨hXA, hXqc, hWq, inferInstance⟩
  obtain ⟨-, hPs, hWs', -, -, -⟩ := witness_frattiniQuotConj (H := H) hWs
  have hsnt : Nontrivial (Xs.map L.subtype ⧸ CFSG.pCore 2 (Xs.map L.subtype)) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hWs' (Subsingleton.elim _ _)
  have hAXs : A ≤ normalizer ((Xs.map L.subtype : Subgroup H) : Set H) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  exact ⟨hXsA, two_core_quotient_image hXsA hAXs hPs hsnt⟩

end CFSG.Quasithin.H13.NQBlock
