module

public import CFSG.Quasithin.Vol2.Ch7Setup
public import CFSG.Quasithin.Background.RonanE338Glue
public import CFSG.Quasithin.H13.E22CHolds

public section

open scoped Pointwise commutatorElement

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.E1 CFSG.Quasithin.A1b

@[expose] def E_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ∀ A : Subgroup (MulAut (IntMod V hV)), A ≤ autI hV ⊤ → A ≠ ⊥ → IsElemAbelian2 A →
      mParam (autI hV ⊤) ≤ rkIdx (fixV A)

set_option linter.unusedVariables false in
theorem as_E_3_2 : E_3_2 := fun G _ _ V hV _ A hA hA1 hAb => E3.e3_2 hA hAb hA1

@[expose] def E_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), IsElemAbelian 2 V → V ≠ ⊥ →
    (∀ (g : G) (B : Subgroup G), B ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) →
        ¬ V ⊓ Subgroup.centralizer (B : Set G) ≤
          Subgroup.normalizer (conjSubgroup V g : Set G) →
        rParam V ≤ (mQuot (conjSubgroup V g) B : ℕ∞)) ∧
    (∀ g : G, ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) →
        rParam V ≤
          (mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) : ℕ∞))

set_option linter.unusedVariables false in
theorem as_E_3_4 : E_3_4 := fun G _ _ V hV hne =>
  ⟨fun g B hB hC => E3.e3_4_one hB hC, fun g h => E3.e3_4_two h⟩

@[expose] def E_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ∀ A B E : Subgroup G, B ≤ A → A ≤ V → mQuot V B < sParam hV → IsPGroup 2 E →
      A ≤ Subgroup.normalizer (E : Set G) →
      E ⊓ Subgroup.centralizer (A : Set G) = E ⊓ Subgroup.centralizer (B : Set G) ∧
        E ⊓ Subgroup.centralizer (B : Set G) = E ⊓ Subgroup.centralizer (V : Set G)

set_option linter.unusedVariables false in
theorem as_E_3_6 : E_3_6 := fun G _ _ V hV _ A B E hBA hAV hs hE _ => E3.e3_6 hV hBA hAV hs hE

@[expose] def E_3_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ∀ (g : G) (B : Subgroup G), B ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) →
      mQuot (conjSubgroup V g) B < sParam hV →
      V ⊓ Subgroup.centralizer (B : Set G) = V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)

set_option linter.unusedVariables false in
theorem as_E_3_7 : E_3_7 := fun G _ _ V hV _ g B hB hs => E3.e3_7 hV hB hs

@[expose] def E_3_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ∀ (g : G) (A : Subgroup G) (b : ℕ), A = conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) →
      b = mQuot (conjSubgroup V g) A → b < sParam hV → ⁅V, conjSubgroup V g⁆ ≠ ⊥ →
      V ⊓ Subgroup.centralizer (A : Set G) = V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) ∧
        autI hV A ∈ aSet (sParam hV - b) (autI hV ⊤) ∧
        sParam hV ≤ aParam (autI hV ⊤) + b ∧ b < sParam hV

set_option linter.unusedVariables false in
theorem as_E_3_10 : E_3_10 := fun G _ _ V hV _ g A b hA hb hbs hnc => by
  subst hA; subst hb
  exact ⟨E3.e3_10_one hV hbs, E3.e3_10_two hV hbs hnc, by
    have := E3.e3_10_three hV hbs hnc; omega, hbs⟩

@[expose] def E_3_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ¬ IsFFModule (autI hV ⊤) → ∀ g : G, conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) →
      ⁅V, conjSubgroup V g⁆ ≠ ⊥ → ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)

set_option linter.unusedVariables false in
theorem as_E_3_11 : E_3_11 := fun G _ _ V hV _ hFF g hg hnc => E3.e3_11 hV hFF hg hnc

@[expose] def E_3_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), IsElemAbelian 2 V → V ≠ ⊥ →
    ∀ H S A K : Subgroup G, IsSylowIn 2 S H → A ≤ V ⊓ S → IsEAny H S A K →
      IsTwoClosed (kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K) ∧
        ¬ A ≤ kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K

set_option linter.unusedVariables false in
theorem as_E_3_12 : E_3_12 := fun G _ _ V hV hne H S A K hS hA hK =>
  ⟨E3.e3_12_isTwoClosed hV hS (hA.trans inf_le_left) (hA.trans inf_le_right) hK,
    E3.e3_12_not_le hV hS (hA.trans inf_le_left) (hA.trans inf_le_right) hK⟩

@[expose] def E_3_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), IsElemAbelian 2 V → V ≠ ⊥ →
    ∀ (X : Subgroup G) (i : ℕ), i < rk ↥V →
      Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (wClos V i X : Set G) ∧
        Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (cClos V i X : Set G)

set_option linter.unusedVariables false in
theorem as_E_3_14 : E_3_14 := fun G _ _ V hV hne X i hi =>
  ⟨E3.normalizer_le_normalizer_wClos X, E3.normalizer_le_normalizer_cClos X⟩

@[expose] def E_3_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), IsElemAbelian 2 V → V ≠ ⊥ →
    ∀ (H S Y : Subgroup G) (i : ℕ), i < rk ↥V → IsSylowIn 2 S H → Y ≤ H → IsPGroup 2 Y →
      wClos V i S ≤ Y →
      wClos V i S = wClos V i Y ∧ IsWeaklyClosedIn (wClos V i S) Y ∧
        Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (wClos V i S : Set G)

set_option linter.unusedVariables false in
theorem as_E_3_15 : E_3_15 := fun G _ _ V hV _ H S Y i hi hS hYH hY hW =>
  ⟨E3.e3_15 hS hYH hY hW, E3.e3_15_weaklyClosed hS hYH hY hW, E3.e3_15_normalizer hS hYH hY hW⟩

@[expose] def E_3_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), IsElemAbelian 2 V → V ≠ ⊥ →
    ∀ (H S Y N : Subgroup G) (i : ℕ), i < rk ↥V → IsSylowIn 2 S H → Y ≤ H → IsPGroup 2 Y →
      wClos V i S ≤ Y → wClos V i S ≠ ⊥ → IsUniqueM (Subgroup.normalizer (Y : Set G)) N →
      (Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (wClos V i S : Set G) ∧
        Subgroup.normalizer (wClos V i S : Set G) ≤ N) ∧
      IsUniqueM (Subgroup.normalizer (wClos V i S : Set G)) N ∧
      Subgroup.centralizer (cClos V i S : Set G) ≤ N

set_option linter.unusedVariables false in
theorem as_E_3_16 : E_3_16 := fun G _ _ V hV _ H S Y N i hi hS hYH hY hW hW1 hN =>
  ⟨E3.e3_16_one hS hYH hY hW hW1 hN, E3.e3_16_two hS hYH hY hW hW1 hN,
    E3.e3_16_three hS hYH hY hW hW1 hN⟩

@[expose] def E_3_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ∀ (H S : Subgroup G) (i j k : ℕ), IsSylowIn 2 S H → i + j ≤ k → (k : ℕ∞) < rParam V →
      k < rk ↥V → ∀ A K : Subgroup G, A ∈ gammaSet V i S → IsE j H S A K →
      ⁅twoResidual K, cClos V k S⁆ ≠ ⊥ →
      (cClos V k S ≤ cClos V k (pCoreOf 2 K) ∧
        ⁅twoResidual K, cClos V k (pCoreOf 2 K)⁆ ≠ ⊥ ∧ ⁅A, cClos V k (pCoreOf 2 K)⁆ ≠ ⊥) ∧
      (A ≤ V → V ⊓ centerOf (wClos V k (pCoreOf 2 K)) ≠ ⊥) ∧
      mParam (autI hV ⊤) ≤ k

set_option linter.unusedVariables false in
theorem as_E_3_17 : E_3_17 := fun G _ _ V hV _ H S i j k hS hijk hkr hkV A K hA hK hne =>
  ⟨E3.e3_17_one hV hS hijk hkr hkV hA hK hne,
    fun hAV => E3.e3_17_two hV hS hijk hkr hkV hA hAV hK hne,
    E3.e3_17_three hV hS hijk hkr hkV hA hK hne⟩

@[expose] def E_3_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ∀ (H S U : Subgroup G) (hU : IsElemAbelian 2 U) (i : ℕ), IsSylowIn 2 S H → U ≤ H →
      H ≤ Subgroup.normalizer (U : Set G) → i + aParam (autI hU H) < sParam hV →
      wClos V i S ≠ ⊥ →
      ⁅U, wClos V i S⁆ = ⊥ ∧
        ((H ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) *
            ((H ⊓ Subgroup.normalizer (wClos V i S : Set G) : Subgroup G) : Set G) = (H : Set G)

set_option linter.unusedVariables false in
theorem as_E_3_18 : E_3_18 := fun G _ _ V hV _ H S U hU i hS hUH hUn hi hW1 =>
  ⟨E3.e3_18_comm hV hS.le hUn hU (Nat.lt_sub_of_add_lt hi), by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨c, hc, n, hn, rfl⟩
      exact H.mul_mem hc.1 hn.1
    · intro h hh
      obtain ⟨c, hc, n, hn, rfl⟩ := E3.e3_18_factor hV hS hUn hU (Nat.lt_sub_of_add_lt hi) h hh
      exact ⟨c, hc, n, hn, rfl⟩⟩

@[expose] def E_3_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ∀ (H S : Subgroup G) (i j : ℕ), IsSylowIn 2 S H → nParam H = (j : ℕ∞) → i + j < sParam hV →
      (H ⊓ Subgroup.centralizer (cClos V (i + j) S : Set G)) ⊔
          (H ⊓ Subgroup.normalizer (wClos V i S : Set G)) = H

set_option linter.unusedVariables false in
theorem as_E_3_19 : E_3_19 := fun G _ _ V hV _ H S i j hS hj hij => E3.e3_19 hV hS hj hij

@[expose] def E_3_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I H : Subgroup G), CFSG.Quasithin.H13.FSU G T L I →
    IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H →
    ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ → ¬ wClos (conjClosure I T) 0 T ≤ pCoreOf 2 H →
    ∃ hV : IsElemAbelian 2 (conjClosure I T), (sParam hV : ℕ∞) ≤ nParam H

@[expose] def E_3_20_partial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I H : Subgroup G), CFSG.Quasithin.H13.FSU G T L I →
    ∀ hV : IsElemAbelian 2 (conjClosure I T),
      IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H →
      ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ → ¬ wClos (conjClosure I T) 0 T ≤ pCoreOf 2 H →
      (sParam hV : ℕ∞) ≤ nParam H

set_option linter.unusedVariables false in
theorem as_E_3_20_partial : E_3_20_partial := fun G _ _ T L I H hF hV hH hZ hW => by
  obtain ⟨S, hS⟩ : ∃ S : Sylow 2 G, (S : Subgroup G) = T :=
    ⟨hF.sylow.1.toSylow hF.sylow.2, rfl⟩
  subst hS
  exact E3.e3_20 hV hH hZ hW

theorem e3_20_fsu_ambient_eq {G : Type} [Group G] (T L : Subgroup G) :
    L ⊔ T = conjClosure L T ⊔ T := by
  refine le_antisymm (sup_le ((le_conjClosure L T).trans le_sup_left) le_sup_right) ?_
  refine sup_le (conjClosure_le fun element hElement generator hGenerator => ?_) le_sup_right
  exact (L ⊔ T).mul_mem
    ((L ⊔ T).mul_mem ((le_sup_right : T ≤ L ⊔ T) hElement) ((le_sup_left : L ≤ L ⊔ T) hGenerator))
    ((L ⊔ T).inv_mem ((le_sup_right : T ≤ L ⊔ T) hElement))

theorem e3_20_fsu_elemAbelian {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hF : CFSG.Quasithin.H13.FSU G T L I) : IsElemAbelian 2 (conjClosure I T) := by
  let ambient := L ⊔ T
  let aggregate := CFSG.Quasithin.primeReducedAggregate ↥ambient 2
  obtain ⟨hNormal, _, hCenter⟩ :=
    CFSG.Quasithin.primeReducedAggregate_normal_elementaryAbelian (E := ↥ambient) 2
  have hMappedNormal : ambient ≤ Subgroup.normalizer
      (CFSG.Quasithin.H13.reducedAggregate ambient : Set G) := by
    have hSubgroup : (CFSG.Quasithin.H13.reducedAggregate ambient).subgroupOf ambient =
        aggregate := Subgroup.comap_map_eq_self_of_injective ambient.subtype_injective _
    have : ((CFSG.Quasithin.H13.reducedAggregate ambient).subgroupOf ambient).Normal := by
      rw [hSubgroup]
      exact hNormal
    exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)
  have hContained : conjClosure I T ≤ CFSG.Quasithin.H13.reducedAggregate ambient := by
    refine conjClosure_le fun element hElement generator hGenerator => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (hMappedNormal ((le_sup_right : T ≤ L ⊔ T) hElement)) generator).mp (hF.irrPlus.1 hGenerator)
  have hMem : ∀ element ∈ CFSG.Quasithin.H13.reducedAggregate ambient,
      ∃ internal : ↥ambient, internal ∈ CFSG.pCore 2 ↥ambient ∧
        (∀ other ∈ CFSG.pCore 2 ↥ambient, other * internal = internal * other) ∧
        internal ^ 2 = 1 ∧ (internal : G) = element := by
    rintro element ⟨internal, hInternal, rfl⟩
    obtain ⟨hCore, hCommute, hPower⟩ :=
      CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mp (hCenter hInternal)
    exact ⟨internal, hCore, hCommute, hPower, rfl⟩
  refine ⟨?_, ?_⟩
  · refine ⟨⟨fun first second => Subtype.ext ?_⟩⟩
    obtain ⟨firstInternal, hCore, _, _, hFirst⟩ := hMem first (hContained first.2)
    obtain ⟨secondInternal, _, hCommute, _, hSecond⟩ := hMem second (hContained second.2)
    change (first : G) * (second : G) = (second : G) * (first : G)
    rw [← hFirst, ← hSecond]
    exact congrArg Subtype.val (hCommute firstInternal hCore)
  · intro element hElement
    obtain ⟨internal, _, _, hPower, rfl⟩ := hMem element (hContained hElement)
    exact congrArg Subtype.val hPower

theorem e3_20_fsu_module : CFSG.Quasithin.H13.StmtFSUModule := by
  intro G _ _ T L I hF
  refine ⟨e3_20_fsu_elemAbelian hF, sup_le ?_ (le_normalizer_conjClosure I T)⟩
  have hNormalizeI := hF.irrPlus.2.2.1
  have hNormalizeL := le_normalizer_conjClosure L T
  have hConjugate : ∀ element ∈ conjClosure L T, ∀ value ∈ conjClosure I T,
      element * value * element⁻¹ ∈ conjClosure I T := by
    intro element hElement value hValue
    induction hValue using Subgroup.closure_induction with
    | mem value hValue =>
      obtain ⟨conjugator, hConjugator, generator, hGenerator, rfl⟩ := hValue
      have hInternal : conjugator⁻¹ * element * conjugator ∈ conjClosure L T := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (hNormalizeL (T.inv_mem hConjugator)) element).mp hElement
        simpa using h
      have hGeneratorImage :
          (conjugator⁻¹ * element * conjugator) * generator *
            (conjugator⁻¹ * element * conjugator)⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (hNormalizeI hInternal) generator).mp hGenerator
      have hImage := mem_conjClosure hConjugator hGeneratorImage
      simpa [mul_assoc] using hImage
    | one => simp
    | mul first second _ _ hFirst hSecond =>
      simpa [mul_assoc] using (conjClosure I T).mul_mem hFirst hSecond
    | inv value _ hValue =>
      simpa [mul_assoc] using (conjClosure I T).inv_mem hValue
  intro element hElement
  rw [Subgroup.mem_normalizer_iff]
  intro value
  refine ⟨hConjugate element hElement value, fun hValue => ?_⟩
  have h := hConjugate element⁻¹ ((conjClosure L T).inv_mem hElement) _ hValue
  simpa [mul_assoc] using h

theorem as_E_3_20 : E_3_20 := fun G _ _ T L I H hF hH hZ hW => by
  have hV := (e3_20_fsu_module G T L I hF).1
  exact ⟨hV, as_E_3_20_partial G T L I H hF hV hH hZ hW⟩

@[expose] def E_3_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    ∀ (H S M : Subgroup G) (i : ℕ), IsSylowIn 2 S H → V ≤ S → S ≤ Subgroup.normalizer (V : Set G) →
      i + aParam (autI hV ⊤) < sParam hV →
      IsUniqueM (Subgroup.normalizer ((S ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
        M →
      (⁅V, wClos V i S⁆ = ⊥ ∧
        wClos V (sParam hV - aParam (autI hV ⊤) - 1) S ≤ S ⊓ Subgroup.centralizer (V : Set G) ∧
        Subgroup.normalizer (wClos V i S : Set G) ≤ M ∧
        Subgroup.centralizer (cClos V i S : Set G) ≤ M) ∧
      (nParam H = (i : ℕ∞) → H ≤ M) ∧
      (1 ≤ i → Group.IsSolvable ↥H → H ≤ M)

set_option linter.unusedVariables false in
theorem as_E_3_21 : E_3_21 := fun G _ _ V hV _ H S M i hS hVS hVN hia hM =>
  ⟨E3.e3_21_one hV hS hVS hVN hia hM, fun hj => E3.e3_21_two hV hS hVS hVN hia hM hj,
    fun hi1 hsol => E3.e3_21_three hV hS hVS hVN hi1 hia hM hsol⟩

@[expose] def E_3_25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G), IsElemAbelian 2 V → V ≠ ⊥ →
    HypE322 T V → 0 < wParam T V → ∀ g : G,
      (conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) ↔
          conjSubgroup V g ≤ Subgroup.centralizer (V : Set G)) ∧
        (conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) ↔
          V ≤ Subgroup.centralizer (conjSubgroup V g : Set G)) ∧
        (V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) ↔
          V ≤ Subgroup.normalizer (conjSubgroup V g : Set G))

set_option linter.unusedVariables false in
theorem as_E_3_25 : E_3_25 := fun G _ _ T V hV _ hT hw g => E3.e3_25 hV hT hw g

@[expose] def E_3_26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE322 T V → HypE324 T V hV → ∀ g : G, conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) →
      ⁅V, conjSubgroup V g⁆ ≠ ⊥ → ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)

set_option linter.unusedVariables false in
theorem as_E_3_26 : E_3_26 := fun G _ _ T V hV _ hT h24 g hg hnc => E3.e3_26 hV hT h24 hg hnc

@[expose] def E_3_28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE322 T V → HypE324 T V hV → ∀ g : G, IsWOffenderAt T V g →
      rParam V ≤ (mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (V : Set G)) :
          ℕ∞) ∧
      (rParam V ≤ wParam T V +
          ((rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) : ℕ) : ℕ∞) ∧
        wParam T V + ((rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) : ℕ) :
            ℕ∞) ≤ wParam T V + ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞)) ∧
      rParam V - wParam T V ≤
        ((rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) : ℕ) : ℕ∞) ∧
      (¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) ∧
        (0 < wParam T V → ¬ conjSubgroup V g ≤ Subgroup.normalizer (V : Set G)))

set_option linter.unusedVariables false in
theorem as_E_3_28 : E_3_28 := fun G _ _ T V hV _ hT h24 g hg =>
  ⟨E3.e3_28_one hV hT h24 hg, ⟨E3.e3_28_two_left hV hT h24 hg, E3.e3_28_two_right hV _⟩,
    E3.e3_28_three hV hT h24 hg,
    ⟨E3.e3_28_four_left hV hT h24 hg, fun hw => E3.e3_28_four_right hV hT hg hw⟩⟩

@[expose] def E_3_29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE322 T V → HypE324 T V hV →
      rParam V ≤ ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T V

set_option linter.unusedVariables false in
theorem as_E_3_29 : E_3_29 := fun G _ _ T V hV hne hT h24 => by
  by_cases hw : E3.wParam T V = ⊤
  · rw [hw]; simp
  · obtain ⟨g, hg⟩ := H13.exists_isWOffenderAt hV hT hw
    exact E3.e3_29 hV hT h24 hg

@[expose] def E_3_31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE322 T V → HypE324 T V hV → ∀ g : G, IsWOffenderAt T V g →
      rParam V = ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T V →
      (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) =
          CFSG.Open.pRank 2 (autI hV ⊤) ∧
        rParam V = (mQuot (conjSubgroup V g)
          (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (V : Set G)) :
            ℕ∞) ∧
        (gammaCheck (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
          (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))).map (valHom hV) ≤
          V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) ∧
      (wParam T V ≤ ((rkIdx (gammaCheck
          (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
          (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) : ℕ) : ℕ∞) ∧
        (∀ hVg : IsElemAbelian 2 (conjSubgroup V g),
          wParam T V = ((rkIdx (gammaCheck
            (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
            (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) : ℕ) : ℕ∞) →
          0 < wParam T V ∧
            (gammaCheck (rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) - 1)
              (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))).map (valHom hV) =
              V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) ∧
            IsWOffenderAt (conjSubgroup T g) (conjSubgroup V g) g⁻¹ ∧
            rk ↥(autI hVg (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G))) =
              CFSG.Open.pRank 2 (autI hV ⊤)))

set_option linter.unusedVariables false in
theorem as_E_3_31 : E_3_31 := fun G _ _ T V hV _ hT h24 g hg hEq =>
  ⟨⟨(E3.e3_31_one_core hV hT h24 hg hEq).1, (E3.e3_31_one_core hV hT h24 hg hEq).2,
      E3.e3_31_one_le hV hT h24 hg hEq⟩,
    ⟨E3.e3_31_two_ge hV hT h24 hg hEq,
      fun hVg hweq => E3.e3_31_two_eq hV hVg hT h24 hg hEq hweq⟩⟩

@[expose] def E_3_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE322 T V → ∀ g : G, wParam T V < rParam V → IsWOffenderAt T V g →
      (gammaCheck (rParam V - wParam T V - 1).toNat
        (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))).map (valHom hV) ≤
        V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)

set_option linter.unusedVariables false in
theorem as_E_3_32 : E_3_32 := fun G _ _ T V hV _ hT g hwr hg => by
  apply E3.e3_32 hV hg
  generalize E3.rParam V = r at *
  generalize E3.wParam T V = w at *
  induction r using ENat.recTopCoe with
  | top => exact le_top
  | coe r =>
    induction w using ENat.recTopCoe with
    | top => exact absurd hwr (by simp)
    | coe w =>
      have hlt : w < r := by exact_mod_cast hwr
      have e : ((r : ℕ∞) - w - 1) = ((r - w - 1 : ℕ) : ℕ∞) := by norm_cast
      rw [e, ENat.toNat_natCast]
      exact_mod_cast (by omega : (r - w - 1) + w + 1 ≤ r)

@[expose] def E_3_33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE322 T V → ∀ g : G, IsWOffenderAt T V g → 0 < wParam T V → wParam T V < (sParam hV : ℕ∞) →
      (V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) :
            Subgroup G) : Set G) = V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) ∧
        V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) < V) ∧
      (V < V ⊔ conjSubgroup V g ∧
        V ⊔ conjSubgroup V g ≤ Subgroup.centralizer
          ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) : Subgroup G) : Set G) ∧
        ¬ Subgroup.centralizer
          ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) : Subgroup G) : Set G) ≤
            Subgroup.normalizer (V : Set G)) ∧
      rParam V ≤ (mQuot V (V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) : ℕ∞) ∧
      (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ∈
          aSet (sParam hV - mQuot (conjSubgroup V g)
            (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) (autI hV ⊤) ∧
        sParam hV - mQuot (conjSubgroup V g)
            (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ≤
          rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) ∧
        1 ≤ sParam hV - mQuot (conjSubgroup V g)
            (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))

set_option linter.unusedVariables false in
theorem as_E_3_33 : E_3_33 := fun G _ _ T V hV _ hT g hg h0w hws =>
  ⟨E3.e3_33_one hV hg hws, E3.e3_33_two hV hT hg h0w, E3.e3_33_three hV hT hg h0w,
    E3.e3_33_four hV hg hws⟩

@[expose] def E_3_34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE322 T V →
      (aParam (autI hV ⊤) < sParam hV →
        ((sParam hV - aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ wParam T V ∧
          0 < sParam hV - aParam (autI hV ⊤)) ∧
      (∀ M : Subgroup G,
        IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
          Set G)) M →
        ∀ i : ℕ, i < rk ↥V → (i : ℕ∞) < wParam T V →
          Subgroup.normalizer (wClos V i T : Set G) ≤ M ∧
            Subgroup.centralizer (cClos V i T : Set G) ≤ M)

set_option linter.unusedVariables false in
theorem as_E_3_34 : E_3_34 := fun G _ _ T V hV _ hT =>
  ⟨fun h => E3.e3_34_one hV hT h, fun M hM i hi hiw => E3.e3_34_two hV hT hM hi hiw⟩

@[expose] def E_3_35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE322 T V → ∀ (H S M : Subgroup G), IsSylowIn 2 S H →
      IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
        M →
      H ⊓ Subgroup.centralizer (V : Set G) ≤ M → T ⊓ Subgroup.centralizer (V : Set G) ≤ S →
      ((nParam H < min (wParam T V) (rParam V) → H ≤ M) ∧
        (Group.IsSolvable ↥H → 1 < min (wParam T V) (rParam V) → H ≤ M)) ∧
      (aParam (autI hV ⊤) < sParam hV → rParam V ≥ wParam T V → ¬ H ≤ M →
        wParam T V ≤ nParam H ∧
          ((sParam hV - aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ wParam T V ∧
          0 < sParam hV - aParam (autI hV ⊤))

set_option linter.unusedVariables false in
theorem as_E_3_35 : E_3_35 := fun G _ _ T V hV hne hT H S M hS hM hCH hQS =>
  ⟨⟨fun hn => E3.e3_35_one hV hne hT hM hS hCH hQS hn,
      fun hsol h1 => E3.e3_35_one_solvable hV hne hT hM hS hCH hQS hsol h1⟩,
    fun has hrw hHM => E3.e3_35_two hV hne hT hM hS hCH hQS has hrw hHM⟩

@[expose] def E_3_37 : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (X : Subgroup M), 1 ≤ nPrime X

set_option linter.unusedVariables false in
theorem as_E_3_37 : E_3_37 := fun M _ _ X => E3.one_le_nPrime X

@[expose] def E_3_38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V M : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE336 T V M → ∀ H : Subgroup G, IsHStar T M H →
      min (wParam T V) (rParam V) ≤ nParam H ∧ nParam H ≤ (nPrime (autI hV ⊤) : ℕ∞)

section E338


theorem as_E_3_38
    : E_3_38 := by
  intro G _ _ T V M hV hV1 hyp H hH
  exact CFSG.Quasithin.RonanE338.e3_38 CFSG.Quasithin.H13.e22StatementC_holds hV hV1 hyp hH

end E338

@[expose] def E_3_39 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V M : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    HypE336 T V M → (nPrime (autI hV ⊤) : ℕ∞) < rParam V → ∀ H : Subgroup G, IsHStar T M H →
      (wParam T V ≤ nParam H ∧ nParam H ≤ (nPrime (autI hV ⊤) : ℕ∞) ∧
        (nPrime (autI hV ⊤) : ℕ∞) < rParam V) ∧
      (aParam (autI hV ⊤) < sParam hV →
        0 < sParam hV - aParam (autI hV ⊤) ∧
          ((sParam hV - aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ wParam T V ∧
          wParam T V ≤ nParam H ∧ nParam H ≤ (nPrime (autI hV ⊤) : ℕ∞) ∧
          (nPrime (autI hV ⊤) : ℕ∞) < rParam V)

section E339


theorem as_E_3_39
    : E_3_39 := by
  intro G _ _ T V M hV hV1 hyp hnr H hH
  exact CFSG.Quasithin.RonanE338.e3_39 CFSG.Quasithin.H13.e22StatementC_holds hV hV1 hyp hnr hH

end E339

@[expose] def E_3_40 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X A : Subgroup (MulAut W), A ∈ aSet 2 X → A ≤ Subgroup.centralizer (CFSG.QuasithinUnique.oddCoreIn X : Set (MulAut W))

set_option linter.unusedVariables false in
theorem as_E_3_40 : E_3_40 := fun W _ _ hW X A hA => E3.e3_40 hW hA

end CFSG.ASVolI
