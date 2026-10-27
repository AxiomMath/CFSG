module

public import CFSG.Quasithin.H13.NQBlockCharNormalizerEscape
public import CFSG.Quasithin.H13.NQBlockTwoPrimeExceptional
public import CFSG.Quasithin.H13.NQBlockTwoPrimeCapture
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAssembly
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Transport

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergCC (frattiniQuotConj normalizerFrattiniConj)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_map_subtype_of_normal {H : Subgroup G} (X : Subgroup H) [hX : X.Normal] :
    H ≤ normalizer ((X.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  have h1 : (⟨h, hh⟩ : H) ∈ normalizer (X : Set H) := by
    rw [normalizer_eq_top_iff.mpr hX]
    exact mem_top _
  have h2 := Subgroup.mem_map_of_mem H.subtype h1
  rw [map_subtype_normalizer_eq] at h2
  exact h2.2

omit [Finite G] in
theorem exists_frattini_map_subtype_equiv {H : Subgroup G} (X : Subgroup H) [X.Normal] :
    ∃ Θ : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃* WPlane (X.map H.subtype),
      ∀ (h : H) (hn : (h : G) ∈ normalizer ((X.map H.subtype : Subgroup G) : Set G)) w,
        Θ (frattiniQuotConj X h w) = normalizerFrattiniConj (X.map H.subtype) ⟨h, hn⟩ (Θ w) := by
  let e₁ : X ≃* X.map H.subtype := X.equivMapOfInjective H.subtype H.subtype_injective
  let e₂ : X ⧸ CFSG.pCore 2 X ≃* X.map H.subtype ⧸ CFSG.pCore 2 (X.map H.subtype) :=
    QuotientGroup.congr _ _ e₁ (CFSG.pCore_map_iso 2 e₁)
  let Θ := QuotientGroup.congr _ _ e₂ (map_frattini_mulEquiv e₂)
  refine ⟨Θ, fun h hn w => ?_⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rfl

theorem odd_residual_witness_map {H : Subgroup G} {L : Subgroup H} [L.Normal] {p : ℕ}
    [Fact p.Prime] {X : Subgroup L} (hX : IsOddResidualWitness p X) :
    let XG := (X.map L.subtype).map H.subtype
    XG ≤ L.map H.subtype ∧ (XG.subgroupOf H).Normal ∧ H ≤ normalizer (XG : Set G) ∧
      NoPQuotient 2 XG ∧ IsPGroup p (XG ⧸ CFSG.pCore 2 XG) ∧
      Monoid.exponent (XG ⧸ CFSG.pCore 2 XG) = p ∧ CFSG.pRank p (XG ⧸ CFSG.pCore 2 XG) = 2 ∧
      Nat.card (WPlane XG) = p ^ 2 ∧
      (∃ l : normalizer (XG : Set G), (l : G) ∈ L.map H.subtype ∧
        normalizerFrattiniConj XG l ≠ 1) ∧
      ∀ V : Subgroup (WPlane XG),
        (∀ l : normalizer (XG : Set G), (l : G) ∈ L.map H.subtype → ∀ w ∈ V,
          normalizerFrattiniConj XG l w ∈ V) → V = ⊥ ∨ V = ⊤ := by
  intro XG
  classical
  have := hX.characteristic
  obtain ⟨hX2H, -, -, hirrH, hntH, -⟩ := witness_frattiniQuotConj (H := H) hX
  have hHX : H ≤ normalizer (XG : Set G) := le_normalizer_map_subtype_of_normal (X.map L.subtype)
  obtain ⟨Θ, hΘ⟩ := exists_frattini_map_subtype_equiv (X.map L.subtype)
  let eXG : X ≃* XG := (X.equivMapOfInjective L.subtype L.subtype_injective).trans
    ((X.map L.subtype).equivMapOfInjective H.subtype H.subtype_injective)
  let e₂ : X ⧸ CFSG.pCore 2 X ≃* XG ⧸ CFSG.pCore 2 XG :=
    QuotientGroup.congr _ _ eXG (CFSG.pCore_map_iso 2 eXG)
  have hXGH : XG.subgroupOf H = X.map L.subtype :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  refine ⟨Subgroup.map_mono (Subgroup.map_subtype_le _), ?_, hHX, ?_, IsPGroup.of_equiv
    hX.isPGroup e₂, (Monoid.exponent_eq_of_mulEquiv e₂.symm).trans hX.exponent,
    (CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv e₂.symm p).trans hX.pRank,
    (Nat.card_congr (QuotientGroup.congr _ _ e₂ (map_frattini_mulEquiv e₂)).toEquiv).symm.trans
      hX.card_W, ?_, ?_⟩
  · rw [hXGH]
    infer_instance
  · let e₁ : X.map L.subtype ≃* XG :=
      (X.map L.subtype).equivMapOfInjective H.subtype H.subtype_injective
    exact CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective e₁.toMonoidHom
      e₁.surjective hX2H
  · obtain ⟨l, hlL, w, hw⟩ := hntH
    refine ⟨⟨(l : G), hHX l.2⟩, Subgroup.mem_map_of_mem H.subtype hlL, fun h1 => hw ?_⟩
    have h2 := hΘ l (hHX l.2) w
    rw [h1, MulAut.one_apply] at h2
    exact Θ.injective h2
  · intro V hV
    rcases hirrH (V.comap Θ.toMonoidHom) (by
        intro l hlL u hu
        change Θ (frattiniQuotConj (X.map L.subtype) l u) ∈ V
        rw [hΘ l (hHX l.2) u]
        exact hV ⟨(l : G), hHX l.2⟩ (Subgroup.mem_map_of_mem H.subtype hlL) _ hu) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro v hv
      have h3 : Θ.symm v ∈ V.comap Θ.toMonoidHom := by
        change Θ (Θ.symm v) ∈ V
        rw [MulEquiv.apply_symm_apply]
        exact hv
      rw [h0, mem_bot] at h3
      rw [mem_bot, ← Θ.apply_symm_apply v, h3, map_one]
    · right
      rw [eq_top_iff]
      intro v _
      have h3 : Θ.symm v ∈ V.comap Θ.toMonoidHom := by
        rw [h1]
        exact mem_top _
      have h4 : Θ (Θ.symm v) ∈ V := h3
      rwa [MulEquiv.apply_symm_apply] at h4

omit [Finite G] in
theorem odd_residual_witness_subgroupOf {X K : Subgroup G} (hXK : X ≤ K) {p : ℕ}
    (hX2 : NoPQuotient 2 X) (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hXr : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) :
    (∀ (N : Subgroup (X.subgroupOf K)) [N.Normal], IsPGroup 2 ((X.subgroupOf K) ⧸ N) → N = ⊤) ∧
      IsPGroup p (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ∧
      CFSG.pRank p (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) = 2 := by
  let e₁ : X.subgroupOf K ≃* X := subgroupOfEquivOfLe hXK
  let e₂ : X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K) ≃* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.congr _ _ e₁ (CFSG.pCore_map_iso 2 e₁)
  exact ⟨CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective e₁.symm.toMonoidHom
    e₁.symm.surjective hX2, IsPGroup.of_equiv hXp e₂.symm,
    (CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv e₂ p).trans hXr⟩

end Transport

section Confine

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergCC (frattiniQuotConj normalizerFrattiniConj)

variable {G : Type} [Group G] [Finite G]

theorem original_two_prime_capture_confines_the_same_characteristic_normalizer_of
    (h39 : SQTKCLayerPerfectResidual) (h2 : StmtQuasisimpleAmbientOneRankTwoPrime)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G)
    {T H : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) {L : Subgroup H} [L.Normal]
    (hLT : L ⊔ T.subgroupOf H = ⊤) (hSQT : CFSG.IsStronglyQuasithin L)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    (hF : CFSG.generalizedFitting L = CFSG.pCore 2 L) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {X : Subgroup L} (hX : IsOddResidualWitness p X) {q : ℕ}
    (hqF : q ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors) (hqp : q ≠ p)
    (Q D : Subgroup (L ⧸ CFSG.pCore 2 L)) (E Xq : Subgroup L)
    (hQ : Q = CFSG.pCore q (L ⧸ CFSG.pCore 2 L)) (hD : D = closure {a | a ∈ Q ∧ a ^ q = 1})
    (hE : E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)))
    (hXq : Xq = closure {e | e ∈ E ∧ Odd (orderOf e)}) :
    let R := (CFSG.pCore 2 (X.map L.subtype ⊔ T.subgroupOf H : Subgroup H)).map
      (X.map L.subtype ⊔ T.subgroupOf H).subtype
    let C₁ := (CFSG.elemThompson R 2).map R.subtype
    let C₂ := CFSG.Open.quasithinOmegaOneCenter R
    let A₁ := (CFSG.perfectResidual (L ⊓ normalizer (C₁ : Set H) : Subgroup H)).map
      (L ⊓ normalizer (C₁ : Set H)).subtype
    let A₂ := (CFSG.perfectResidual (L ⊓ normalizer (C₂ : Set H) : Subgroup H)).map
      (L ⊓ normalizer (C₂ : Set H)).subtype
    (∃ A : Subgroup H, (A = A₁ ∨ A = A₂) ∧ X.map L.subtype ≤ A ∧ Xq.map L.subtype ≤ A) ∧
      ∀ C A : Subgroup H, (C = C₁ ∧ A = A₁ ∨ C = C₂ ∧ A = A₂) → X.map L.subtype ≤ A →
        Xq.map L.subtype ≤ A →
        normalizer ((C.map H.subtype : Subgroup G) : Set G) ≤
          normalizer (((X.map L.subtype).map H.subtype : Subgroup G) : Set G) := by
  intro R C₁ C₂ A₁ A₂
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hT' := quasithinIsSylowTwo_subgroupOf hT hTH
  let T' : Sylow 2 H := hT'.1.toSylow hT'.2
  have hLT' : L ⊔ (T' : Subgroup H) = ⊤ := hLT
  obtain ⟨hq5, -, -, hC₁1, hC₁R, hC₁c, hC₂1, hC₂R, hC₂c, -, -, -, -, -, -, hXY, hYA₁, hYA₂, A,
      hA12, hXqA, -⟩ :=
    original_multiple_prime_radical_captures_two_primes_in_actual_characteristic_normalizer
      hSQT hLC T' hLT' hq hF hp5 hX hqF hqp Q D E Xq hQ hD hE hXq
  obtain ⟨-, -, -, -, -, -, -, hWq, -⟩ :=
    two_prime_capture_data hSQT hLC T' hLT' hq hF hp5 hX hqF Q D E Xq hQ hD hE hXq
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF⟩
  have hqP : q.Prime := Fact.out
  refine ⟨⟨A, hA12, ?_, hXqA⟩, ?_⟩
  · rcases hA12 with rfl | rfl
    · exact hXY.trans hYA₁
    · exact hXY.trans hYA₂
  intro C A' hCA hXA' hXqA'
  obtain ⟨hC1, hCR, hCc, hA'⟩ : C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
      A' = (CFSG.perfectResidual (L ⊓ normalizer (C : Set H) : Subgroup H)).map
        (L ⊓ normalizer (C : Set H)).subtype := by
    rcases hCA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hC₁1, hC₁R, hC₁c, rfl⟩
    · exact ⟨hC₂1, hC₂R, hC₂c, rfl⟩
  by_contra hNX
  obtain ⟨hXL, hXn, hHX, hX2, hXp, hexp, hrank, hW, hLW, hirr⟩ :=
    odd_residual_witness_map (H := H) hX
  obtain ⟨-, -, hHXq, hXq2, hXqp, -, hXqr, -, -, -⟩ := odd_residual_witness_map (H := H) hWq
  have hLH : L.map H.subtype ≤ H := Subgroup.map_subtype_le L
  have hLn : ((L.map H.subtype).subgroupOf H).Normal := by
    have hLGH : (L.map H.subtype).subgroupOf H = L :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
    rw [hLGH]
    infer_instance
  have hHLT : H = L.map H.subtype ⊔ T := by
    have h1 := congrArg (Subgroup.map H.subtype) hLT
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1.symm
  have hLC' : L.map H.subtype ∈ cComp (L.map H.subtype) := by
    have h1 := map_subtype_mem_cComp_of_mem (B := L) (mem_cComp_top_iff_isCComponent.mpr hLC)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact map_subtype_mem_cComp_of_mem h1
  have hRG : R.map H.subtype = pCoreOf 2 ((X.map L.subtype).map H.subtype ⊔ T) := by
    have h1 := pCoreOf_map_subtype (H := H) (X.map L.subtype ⊔ T.subgroupOf H)
    unfold CFSG.Open.pCoreOf at h1
    change ((CFSG.pCore 2 (X.map L.subtype ⊔ T.subgroupOf H : Subgroup H)).map
      (X.map L.subtype ⊔ T.subgroupOf H).subtype).map H.subtype = _
    rw [h1, Subgroup.map_sup, map_subgroupOf_eq_of_le hTH]
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  have hCG1 : C.map H.subtype ≠ ⊥ := fun h =>
    hC1 ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h)
  have hCGR : C.map H.subtype ≤ pCoreOf 2 ((X.map L.subtype).map H.subtype ⊔ T) := by
    have h1 := Subgroup.map_mono (f := H.subtype) hCR
    rwa [hRG] at h1
  have hCGc : ((C.map H.subtype).subgroupOf
      (pCoreOf 2 ((X.map L.subtype).map H.subtype ⊔ T))).Characteristic := by
    let ψR : R ≃* pCoreOf 2 ((X.map L.subtype).map H.subtype ⊔ T) :=
      (R.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hRG)
    have hmap : (C.subgroupOf R).map ψR.toMonoidHom = (C.map H.subtype).subgroupOf
        (pCoreOf 2 ((X.map L.subtype).map H.subtype ⊔ T)) := by
      ext x
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨(r : H), hr, rfl⟩
      · rintro ⟨c, hc, hcx⟩
        refine ⟨ψR.symm x, ?_, ψR.apply_symm_apply x⟩
        have h1 : (((ψR.symm x : R) : H) : G) = (x : G) :=
          congrArg (fun y : pCoreOf 2 ((X.map L.subtype).map H.subtype ⊔ T) => (y : G))
            (ψR.apply_symm_apply x)
        have h2 : ((ψR.symm x : R) : H) = c := Subtype.ext (h1.trans hcx.symm)
        change ((ψR.symm x : R) : H) ∈ C
        rw [h2]
        exact hc
    rw [← hmap]
    exact characteristic_map_mulEquiv ψR hCc
  obtain ⟨-, -, hCO, hTs, -, hAloc, -, KC, ⟨hKC, hAK⟩, -, -, -, -, -, -, -, -, -, -, hesc⟩ :=
    escaping_characteristic_normalizer_has_proper_original_local_of h39 hnab hK hT hTH hLH hLn hHLT
      hLC' hp hp5 hXL hXn hX2 hXp hexp hrank hW hLW hirr (C.map H.subtype) hCG1 hCGR hCGc
  obtain ⟨-, hAq, -, -, -, -⟩ := char_normalizer_residual_in_G hT hTH hLH hLn hHLT hLC' hp hp5 hXL
    hXn hX2 hXp hW hLW hirr (C.map H.subtype) hCG1 hCGR hCGc
  obtain ⟨hKq, -, -⟩ := hesc hNX
  have hAG : A'.map H.subtype = (CFSG.perfectResidual ↥(L.map H.subtype ⊓
      normalizer ((C.map H.subtype : Subgroup G) : Set G))).map
        (L.map H.subtype ⊓ normalizer ((C.map H.subtype : Subgroup G) : Set G)).subtype := by
    rw [hA', CFSG.LieType.SteinbergBR.BlockPar.map_perfectResidual_subgroup]
    apply CFSG.LieType.SteinbergBR.BlockPar.perfectResidual_map_subtype_congr
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, map_subtype_normalizer_eq, ← inf_assoc,
      inf_eq_left.mpr hLH]
  set AG := (CFSG.perfectResidual ↥(L.map H.subtype ⊓
      normalizer ((C.map H.subtype : Subgroup G) : Set G))).map
        (L.map H.subtype ⊓ normalizer ((C.map H.subtype : Subgroup G) : Set G)).subtype with hAGdef
  have hAL : AG ≤ L.map H.subtype := (Subgroup.map_subtype_le _).trans inf_le_left
  have hXAG : (X.map L.subtype).map H.subtype ≤ AG := by
    have h1 := Subgroup.map_mono (f := H.subtype) hXA'
    rwa [hAG] at h1
  have hXqAG : (Xq.map L.subtype).map H.subtype ≤ AG := by
    have h1 := Subgroup.map_mono (f := H.subtype) hXqA'
    rwa [hAG] at h1
  have hO2 : pCoreOf 2 (normalizer ((C.map H.subtype : Subgroup G) : Set G)) ≠ ⊥ := fun hb =>
    hCG1 (le_bot_iff.mp (hb ▸ hCO))
  have hloc : LocalSQTK G := (qtkeCore_of_cat hnab hK).1
  have hKNC : KC ≤ normalizer ((C.map H.subtype : Subgroup G) : Set G) := le_of_mem_cComp hKC
  have hSQTK : CFSG.SectionRank.IsSQTKCat KC :=
    CFSG.QuasithinUnique.Setup.Family.isSQTKCat_of_le hKNC (hloc _ hO2)
  have hTK := CFSG.QuasithinUnique.L246C127.isSylowTwoOf_inf_of_isSubnormal'
    (subnormal_of_mem_cComp hKC) hTs
  have hTKs : quasithinIsSylowTwo (T.subgroupOf KC) := by
    rw [← Subgroup.inf_subgroupOf_right T KC]
    exact ⟨hTK.2.1.of_equiv (subgroupOfEquivOfLe inf_le_right).symm, hTK.2.2⟩
  have hAKc : AG.subgroupOf KC ∈ cComp (AG.subgroupOf KC ⊔ T.subgroupOf KC) := by
    have h1 : AG ∈ cComp (AG ⊔ (T ⊓ KC)) :=
      cComp_mem_of_le hAloc.2.1 le_sup_left (sup_le_sup_left inf_le_left AG)
    have h3 := subgroupOf_mem_cComp_of_le (sup_le hAK inf_le_right) h1
    rwa [Subgroup.subgroupOf_sup hAK inf_le_right, Subgroup.inf_subgroupOf_right] at h3
  have hAqK : ¬ CFSG.IsQuasisimple (↥(AG.subgroupOf KC) ⧸ CFSG.pCore 2 ↥(AG.subgroupOf KC)) := by
    intro hq'
    apply hAq
    let eA : AG.subgroupOf KC ≃* AG := subgroupOfEquivOfLe hAK
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (QuotientGroup.congr _ _ eA (CFSG.pCore_map_iso 2 eA))).1 hq'
  have hXK : (X.map L.subtype).map H.subtype ≤ KC := hXAG.trans hAK
  have hXqK : (Xq.map L.subtype).map H.subtype ≤ KC := hXqAG.trans hAK
  obtain ⟨hXp2', hXpp', hXpr'⟩ := odd_residual_witness_subgroupOf hXK hX2 hXp hrank
  obtain ⟨hXq2', hXqp', hXqr'⟩ := odd_residual_witness_subgroupOf hXqK hXq2 hXqp hXqr
  have hnorm : ∀ Z : Subgroup G, H ≤ normalizer (Z : Set G) → ∀ U : Subgroup KC,
      (∀ u ∈ U, (u : G) ∈ H) → U ≤ normalizer ((Z.subgroupOf KC : Subgroup KC) : Set KC) :=
    fun _ hHZ _ hU u hu => mem_normalizer_subgroupOf_of_mem (hHZ (hU u hu))
  have hAH : ∀ u ∈ AG.subgroupOf KC, (u : G) ∈ H := fun u hu => hLH (hAL hu)
  have hTH' : ∀ u ∈ T.subgroupOf KC, (u : G) ∈ H := fun u hu => hTH hu
  have hXpA : ((X.map L.subtype).map H.subtype).subgroupOf KC ≤ AG.subgroupOf KC :=
    fun x hx => hXAG hx
  have hXqA : ((Xq.map L.subtype).map H.subtype).subgroupOf KC ≤ AG.subgroupOf KC :=
    fun x hx => hXqAG hx
  have hpq := h2 KC hSQTK hKq (T.subgroupOf KC) (AG.subgroupOf KC) hTKs hAKc hAqK p q hp hqP
    hp5 hq5 (((X.map L.subtype).map H.subtype).subgroupOf KC)
    (((Xq.map L.subtype).map H.subtype).subgroupOf KC) hXpA
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXpA).mpr (hnorm _ hHX _ hAH))
    (hnorm _ hHX _ hTH') hXp2' hXpp' hXpr' hXqA
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXqA).mpr (hnorm _ hHXq _ hAH))
    (hnorm _ hHXq _ hTH') hXq2' hXqp' hXqr'
  exact hqp hpq.symm

@[expose] def StmtTwoPrimeCaptureConfinesCharNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    quasithinIsQTKECat G → ∀ T H : Subgroup G, quasithinIsSylowTwo T → T ≤ H →
    ∀ (L : Subgroup H) [L.Normal], L ⊔ T.subgroupOf H = ⊤ → CFSG.IsStronglyQuasithin L →
    CFSG.IsCComponent (⊤ : Subgroup L) → ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.generalizedFitting L = CFSG.pCore 2 L → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ X : Subgroup L, IsOddResidualWitness p X →
    ∀ q : ℕ, q ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors → q ≠ p →
    ∀ (Q D : Subgroup (L ⧸ CFSG.pCore 2 L)) (E Xq : Subgroup L),
    Q = CFSG.pCore q (L ⧸ CFSG.pCore 2 L) → D = closure {a | a ∈ Q ∧ a ^ q = 1} →
    E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)) →
    Xq = closure {e | e ∈ E ∧ Odd (orderOf e)} →
    let R := (CFSG.pCore 2 (X.map L.subtype ⊔ T.subgroupOf H : Subgroup H)).map
      (X.map L.subtype ⊔ T.subgroupOf H).subtype
    let C₁ := (CFSG.elemThompson R 2).map R.subtype
    let C₂ := CFSG.Open.quasithinOmegaOneCenter R
    let A₁ := (CFSG.perfectResidual (L ⊓ normalizer (C₁ : Set H) : Subgroup H)).map
      (L ⊓ normalizer (C₁ : Set H)).subtype
    let A₂ := (CFSG.perfectResidual (L ⊓ normalizer (C₂ : Set H) : Subgroup H)).map
      (L ⊓ normalizer (C₂ : Set H)).subtype
    (∃ A : Subgroup H, (A = A₁ ∨ A = A₂) ∧ X.map L.subtype ≤ A ∧ Xq.map L.subtype ≤ A) ∧
      ∀ C A : Subgroup H, (C = C₁ ∧ A = A₁ ∨ C = C₂ ∧ A = A₂) → X.map L.subtype ≤ A →
        Xq.map L.subtype ≤ A →
        normalizer ((C.map H.subtype : Subgroup G) : Set G) ≤
          normalizer (((X.map L.subtype).map H.subtype : Subgroup G) : Set G)

theorem stmtTwoPrimeCaptureConfinesCharNormalizer_of (h39 : SQTKCLayerPerfectResidual)
    (h2 : StmtQuasisimpleAmbientOneRankTwoPrime)
    : StmtTwoPrimeCaptureConfinesCharNormalizer :=
  fun _ _ _ _ hnab hK _ _ hT hTH _ _ hLT hSQT hLC hq hF p hp hp5 _ hX _ hqF hqp Q D E Xq hQ hD hE
    hXq =>
    haveI : Fact p.Prime := ⟨hp⟩
    original_two_prime_capture_confines_the_same_characteristic_normalizer_of h39 h2 hnab hK hT
      hTH hLT hSQT hLC hq hF hp5 hX hqF hqp Q D E Xq hQ hD hE hXq

end Confine

end CFSG.Quasithin.H13.NQBlock
