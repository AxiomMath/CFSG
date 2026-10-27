module

public import CFSG.Quasithin.H13.NQCatSuzukiCatalog
public import CFSG.Quasithin.H13.NQCatSuzukiCComponent
public import CFSG.Quasithin.H13.NQBlockContainingComponent
public import CFSG.Quasithin.SteinbergBMCoreQuotientCenterOdd
public import CFSG.Quasithin.H13.NQRigidWitness

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem nonempty_suzukiGroup_mulEquiv_suzukiMatrixGroup {a : ℕ} (ha : 1 ≤ a) {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2 ^ (2 * a + 1)) :
    Nonempty (Blueprint.suzukiGroup a k ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
  ⟨(MulEquiv.subgroupCongr (LieType.BorelTits.suzukiGroup_eq_glaSzGroup a k)).trans
    ((ShultStronglyClosedTI.glaSzEquivNative a ha hk).trans
      (ShultStronglyClosedTI.suzukiCoverNativeEquiv a))⟩

theorem le_center_of_isSolvable_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) {N : Subgroup Q} [N.Normal] (hN : Group.IsSolvable N) :
    N ≤ center Q := by
  obtain ⟨-, hs, a, b, hab⟩ := hQ
  have hNm : (N.map (QuotientGroup.mk' (center Q))).Normal :=
    Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hsol : Group.IsSolvable (N.map (QuotientGroup.mk' (center Q))) :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (center Q)).subgroupMap_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center Q))) with
    h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have hQs : Group.IsSolvable (Q ⧸ center Q) :=
      Group.isSolvable_of_surjective (f := (N.map (QuotientGroup.mk' (center Q))).subtype)
        fun q => ⟨⟨q, by rw [h]; exact mem_top q⟩, rfl⟩
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hQs a b)

theorem solvableRadical_eq_pCore_of_suzuki {B : Type} [Group B] [Finite B] {a : ℕ} (ha : 1 ≤ a)
    (hQ : CFSG.IsQuasisimple (B ⧸ CFSG.pCore 2 B))
    (η : B ⧸ CFSG.solvableRadical B ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :
    CFSG.solvableRadical B = CFSG.pCore 2 B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hQ
  have hRad : Group.IsSolvable (CFSG.solvableRadical B) :=
    SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have h2 : CFSG.pCore 2 B ≤ CFSG.solvableRadical B := by
    refine SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical inferInstance ?_
    have := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 B)).isNilpotent
    infer_instance
  refine le_antisymm ?_ h2
  have hle : CFSG.pCore 2 B ≤ (QuotientGroup.mk' (CFSG.solvableRadical B)).ker := by
    rw [QuotientGroup.ker_mk']
    exact h2
  set ν : B ⧸ CFSG.pCore 2 B →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    η.toMonoidHom.comp (QuotientGroup.lift _ (QuotientGroup.mk' (CFSG.solvableRadical B)) hle)
    with hν
  have hνmk : ∀ b : B, ν (b : B ⧸ CFSG.pCore 2 B) = η (b : B ⧸ CFSG.solvableRadical B) :=
    fun b => rfl
  have hνs : Function.Surjective ν := by
    intro y
    obtain ⟨z, rfl⟩ := η.surjective y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨(b : B ⧸ CFSG.pCore 2 B), hνmk b⟩
  set R := (CFSG.solvableRadical B).map (QuotientGroup.mk' (CFSG.pCore 2 B)) with hR
  have hνk : ν.ker = R := by
    ext q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 B) q
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, hνmk, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hb
      exact ⟨b, hb, rfl⟩
    · rintro ⟨c, hc, hcb⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hcb
      have h1 := mul_mem hc (h2 hcb)
      rwa [mul_inv_cancel_left] at h1
  have hRn : R.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hRs : Group.IsSolvable R :=
    Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 B)).subgroupMap_surjective (CFSG.solvableRadical B))
  have hRZ : R ≤ center (B ⧸ CFSG.pCore 2 B) := le_center_of_isSolvable_of_isQuasisimple hQ hRs
  have hRodd : Odd (Nat.card ν.ker) := by
    rw [hνk]
    exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hRZ)
  have hbot := SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) ν hνs
    (hνk ▸ hRZ) hRodd
  intro x hx
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 B) x ∈ ν.ker := by
    rw [hνk]
    exact ⟨x, hx, rfl⟩
  rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk
  exact hmk

theorem suzuki_order_ge {a : ℕ} (ha : 1 ≤ a) :
    29120 ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 8 ≤ 2 ^ (2 * a + 1) :=
    (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ 3 ≤ 2 ^ (2 * a + 1))
  have h1 : 64 ≤ (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
  have h2 : 7 ≤ 2 ^ (2 * a + 1) - 1 := by omega
  have h3 : 65 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := by omega
  calc 29120 = 64 * 7 * 65 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

variable {G : Type} [Group G] [Finite G]

theorem isCComponent_top_and_sqt_of_isLocal {T L M D : Subgroup G} (h : QTNQ T L M)
    (hD : quasithinIsLocal T D) :
    CFSG.IsCComponent (⊤ : Subgroup ↥D) ∧ CFSG.IsStronglyQuasithin ↥D := by
  have := h.simple
  have hDc : D ∈ cComp (D ⊔ T) := CFSG.Quasithin.cComp_of_isLocal hD
  have hsqtk := (NQCore.qt_positive_two_core_SQTK h.nonabelian h.qtke hD.2.2.2).2
  refine ⟨?_, NQRigid.isStronglyQuasithin_of_le le_sup_left hsqtk.1⟩
  have hDself : D ∈ cComp D := cComp_mem_of_le hDc le_rfl le_sup_left
  have h3 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hDself)
  rwa [subgroupOf_self] at h3

theorem primeToThreeComplementaryQuasisimple_holds :
    ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
      ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
      ∀ A ∈ cComp H, nqOriginalK T L ≤ A → (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) →
      ∀ B ∈ cComp H, B ≠ A → ¬ 3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) →
        (∃ a : ℕ, 1 ≤ a ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
          Nat.card k = 2 ^ (2 * a + 1) ∧
          Nonempty (↥B ⧸ CFSG.solvableRadical ↥B ≃* CFSG.Blueprint.suzukiGroup a k) ∧
          CFSG.solvableRadical ↥B = CFSG.pCore 2 ↥B ∧
          Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* CFSG.Blueprint.suzukiGroup a k) ∧
          Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) =
            (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) ∧
          29120 ≤ Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)) ∧
        (∀ D : Subgroup G, quasithinIsLocal T D → B ≤ D →
          CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D)) ∧
        (¬ B ≤ M →
          quasithinIsFaithfulLocal T B ∧
          (∀ D : Subgroup G, quasithinIsLocal T D → B ≤ D →
            quasithinIsFaithfulLocal T D ∧ ¬ D ≤ M) ∧
          (∃ B' : Subgroup G, (quasithinIsMaximalLocal T B' ∧ quasithinIsFaithfulLocal T B') ∧
            B ≤ B') ∧
          ∀ B' : Subgroup G, quasithinIsMaximalLocal T B' → B ≤ B' →
            quasithinIsFaithfulLocal T B' ∧ ¬ B' ≤ M ∧
            CFSG.IsQuasisimple (↥B' ⧸ CFSG.pCore 2 ↥B') ∧
            CFSG.pCore 2 (↥B' ⧸ CFSG.pCore 2 ↥B') = ⊥ ∧
            Odd (Nat.card (center (↥B' ⧸ CFSG.pCore 2 ↥B')))) := by
  intro G _ _ T L M h H hH hKTH hHM A hA hKA huniq B hB hBA h3
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2H := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hTs := NQBlock.isSylowTwoOf_of_qtnq h hTH
  have hBloc : quasithinIsLocal T B := Vol2Native.isLocal_of_mem_cComp hO2H hTs hB
  have hBH : B ≤ H := le_of_mem_cComp hB
  obtain ⟨hBtop, -⟩ := isCComponent_top_and_sqt_of_isLocal h hBloc
  obtain ⟨hBs, hBnab⟩ := NQBlock.simple_radical_quotient_of_isCComponent_top hBtop
  have hHsqtk := (NQCore.qt_positive_two_core_SQTK h.nonabelian h.qtke hO2H).2
  have hcat : Blueprint.Catalog (↥B ⧸ CFSG.solvableRadical ↥B) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hHsqtk.2 (B.subgroupOf H)
      ((QuotientGroup.mk' (CFSG.solvableRadical ↥B)).comp
        (subgroupOfEquivOfLe hBH).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe hBH).surjective)
  obtain ⟨a, ha, ⟨k, hk, hkf, hcard, ⟨η⟩⟩, -⟩ :=
    catalog_prime_to_three_simple_groups_are_exact_Suzuki_models _ hBnab hcat h3
  have hBperf : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hB)
  have hpart2 : ∀ D : Subgroup G, quasithinIsLocal T D → B ≤ D →
      CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D) := by
    intro D hD hBD
    obtain ⟨hDtop, hDsqt⟩ := isCComponent_top_and_sqt_of_isLocal h hD
    set e : ↥(B.subgroupOf D) ≃* ↥B := subgroupOfEquivOfLe hBD with he
    have hperf' : Group.IsPerfect ↥(B.subgroupOf D) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    refine (sqt_nonquasisimple_Ccomponent_prime_linear_radical_quotient_and_no_Suzuki_section
      hDsqt hDtop).2 (B.subgroupOf D) hperf' ⟨a, ha, k, hk, hkf, hcard, ⟨?_⟩⟩
    exact (QuotientGroup.congr _ _ e (LieType.SteinbergBR.solvableRadical_map_equiv e)).trans η
  have hQB := hpart2 B hBloc le_rfl
  obtain ⟨ξ⟩ := nonempty_suzukiGroup_mulEquiv_suzukiMatrixGroup ha hcard
  have hRadB : CFSG.solvableRadical ↥B = CFSG.pCore 2 ↥B :=
    solvableRadical_eq_pCore_of_suzuki ha hQB (η.trans ξ)
  have eO2 : (↥B ⧸ CFSG.pCore 2 ↥B) ≃* Blueprint.suzukiGroup a k :=
    (QuotientGroup.quotientMulEquivOfEq hRadB.symm).trans η
  have hord : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr (eO2.trans ξ).toEquiv, SectionRank.card_suzukiMatrixGroup a (by omega)]
    ring
  refine ⟨⟨a, ha, k, hk, hkf, hcard, ⟨η⟩, hRadB, ⟨eO2⟩, hord, hord ▸ suzuki_order_ge ha⟩,
    hpart2, fun hBM => ?_⟩
  obtain ⟨-, -, -, -, -, -, hcl, -⟩ := NQBlock.containing_sylow_closure (A := A) h hH hTH
  obtain ⟨-, -, hBf, B', ⟨hB'm, hB'f⟩, hBB', hB'M⟩ := hcl B hB hBM
  have hup : ∀ D : Subgroup G, quasithinIsLocal T D → B ≤ D → quasithinIsFaithfulLocal T D :=
    fun D hD hBD => local_faithfulness_upward LocDbl.local_double_embedding_exclusion h.simple
      h.nonabelian h.qtke h.sylow hD hBD hBf
  refine ⟨hBf, fun D hD hBD => ⟨hup D hD hBD, fun hDM => hBM (hBD.trans hDM)⟩,
    ⟨B', ⟨hB'm, hB'f⟩, hBB'⟩, fun B'' hB''m hBB'' => ?_⟩
  have hq'' := hpart2 B'' hB''m.1 hBB''
  obtain ⟨-, hO2'', hodd''⟩ := SteinbergBM.five_core_quotient_center_odd hq''
  exact ⟨hup B'' hB''m.1 hBB'', fun hB''M => hBM (hBB''.trans hB''M), hq'', hO2'', hodd''⟩

end CFSG.Quasithin.H13.NQCat
