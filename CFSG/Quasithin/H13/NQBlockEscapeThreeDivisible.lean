module

public import CFSG.Quasithin.H13.NQBlockThreeDivisible
public import CFSG.Quasithin.H13.NQBlockNonquasisimpleConfine
public import CFSG.Quasithin.H13.NQBlockFiveOrders

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem card_quotient_pCore_le {X Y : Subgroup G} (hXY : X ≤ Y) :
    Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ≤ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  set ψ : ↥X →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hXY) with hψdef
  have hψk : ψ.ker ≤ CFSG.pCore 2 ↥X := by
    intro x hx
    rw [MonoidHom.mem_ker, hψdef, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk', mem_pCore_iff_mem_pCoreOf] at hx
    exact mem_pCore_of_mem_pCoreOf hXY x hx
  have hs : Function.Surjective (QuotientGroup.map ψ.ker (CFSG.pCore 2 ↥X) (MonoidHom.id ↥X)
      hψk) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨x, rfl⟩
  calc Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ≤ Nat.card (↥X ⧸ ψ.ker) :=
        Nat.card_le_card_of_surjective _ hs
    _ = Nat.card ψ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    _ ≤ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := Subgroup.card_le_card_group _

theorem maximalLocal_eq_of_original_K_le (h1323 : Stmt13_1_2_three)
    {T L M D : Subgroup G} (h : QTNQ T L M) (hDm : quasithinIsMaximalLocal T D)
    (hKD : nqOriginalK T L ≤ D) : D = L := by
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  have hf := containing_local_facts h hR hDm.1 hKD
  have hDf : quasithinIsFaithfulLocal T D := hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hDM : D ≤ M := by
    by_contra hDM
    have hq : CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D) := by
      by_contra hq
      exact hDM (originalKNonquasisimpleConfinement_holds G T L M h D hDm hDf hKD hq).2.2
    exact not_qt13Five_of_maximalLocal h hDm hKD hf.1
      (h1323 G T D h.simple h.nonabelian h.qtke h.sylow h.not_excluded hDm hDf hq)
  exact eq_of_maximalLocal_le h hDm hf.1 hDM hKD

theorem complementaryEscapeThreeDivisible_of (h1323 : Stmt13_1_2_three)
    :
    ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
      ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
      ∀ A ∈ cComp H, nqOriginalK T L ≤ A → (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) →
        (∀ B ∈ cComp H, B ≠ A → ¬ 3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) → B ≤ M) ∧
        (¬ nqComplementaryLayer H A ≤ M ↔
          ∃ B ∈ cComp H, B ≠ A ∧ ¬ B ≤ M ∧ 3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)) ∧
        (∀ B ∈ cComp H, B ≠ A → ¬ B ≤ M →
          3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) ∧
          (∀ B' ∈ cComp H, B' ≠ A → 3 ∣ Nat.card (↥B' ⧸ CFSG.solvableRadical ↥B') → B' = B) ∧
          (B.subgroupOf H).Normal ∧ T ≤ normalizer (B : Set G) ∧
          ⁅quasithinOmegaOneCenter T, B⁆ ≠ ⊥ ∧ quasithinIsFaithfulLocal T B ∧
          (∃ B' : Subgroup G, (quasithinIsMaximalLocal T B' ∧ quasithinIsFaithfulLocal T B') ∧
            B ≤ B') ∧
          (∀ B' : Subgroup G, quasithinIsMaximalLocal T B' → B ≤ B' →
            quasithinIsFaithfulLocal T B' ∧ T ≤ normalizer (B' : Set G) ∧ ¬ B' ≤ M) ∧
          ∀ C ∈ cComp H, C ≠ A → C ≠ B → C ≤ M) ∧
        A ≤ L ∧ L ≤ M ∧ (nqComplementaryLayer H A ≤ M → ∀ C ∈ cComp H, C ≤ M) := by
  intro G _ _ T L M h H hH hKTH hHM A hA hKA hAu
  classical
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hTs := isSylowTwoOf_of_qtnq h hTH
  have hO2 := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1
  have h3M : ∀ B ∈ cComp H, B ≠ A → ¬ 3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) → B ≤ M := by
    intro B hB hBA h3
    by_contra hBM
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hge⟩, -, hesc⟩ :=
      NQCat.primeToThreeComplementaryQuasisimple_holds G T L M h H hH hKTH hHM A hA hKA hAu B hB
        hBA h3
    obtain ⟨-, -, ⟨B', ⟨hB'm, hB'f⟩, hBB'⟩, hall⟩ := hesc hBM
    obtain ⟨-, -, hq, -, -⟩ := hall B' hB'm hBB'
    have h5 := h1323 G T B' h.simple h.nonabelian h.qtke h.sylow h.not_excluded hB'm hB'f hq
    have h6048 := (fiveQuotientExactOrders_holds (↥B' ⧸ CFSG.pCore 2 ↥B')).2.2.2.2.2 h5
    have hle := card_quotient_pCore_le hBB'
    omega
  have hesc : ∀ B ∈ cComp H, B ≠ A → ¬ B ≤ M → 3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) :=
    fun B hB hBA hBM => by_contra fun h3 => hBM (h3M B hB hBA h3)
  obtain ⟨hu, -, h3n⟩ :=
    complementaryThreeDivisibleUniqueNormal_holds G T L M h H hH hKTH hHM A hA hKA hAu
  obtain ⟨-, -, -, -, -, -, hcl, hY⟩ := containing_sylow_closure (A := A) h hH hTH
  have hAL : A ≤ L := by
    obtain ⟨A', hA'm, hAA'⟩ :=
      exists_maximalLocal_ge (QuasithinUnique.Vol2Native.isLocal_of_mem_cComp hO2 hTs hA)
    exact hAA'.trans (maximalLocal_eq_of_original_K_le h1323 h hA'm (hKA.trans hAA')).le
  refine ⟨h3M, ?_, fun B hB hBA hBM => ?_, hAL, h.l_le, fun hYM C hC => ?_⟩
  · rw [hY]
    exact ⟨fun ⟨B, hB, hBA, hBM⟩ => ⟨B, hB, hBA, hBM, hesc B hB hBA hBM⟩,
      fun ⟨B, hB, hBA, hBM, _⟩ => ⟨B, hB, hBA, hBM⟩⟩
  · have h3 := hesc B hB hBA hBM
    obtain ⟨hBn, hTB, -, hBesc⟩ := h3n B hB hBA h3
    obtain ⟨hBf, -, hex, hall⟩ := hBesc hBM
    obtain ⟨hZB, -⟩ := hcl B hB hBM
    refine ⟨h3, fun B' hB' hB'A h3' => hu B' hB' B hB hB'A hBA h3' h3, hBn, hTB, hZB, hBf, hex,
      fun B' hB'm hBB' => ⟨(hall B' hB'm hBB').1, (hall B' hB'm hBB').2,
        fun hB'M => hBM (hBB'.trans hB'M)⟩, fun C hC hCA hCB => ?_⟩
    by_contra hCM
    exact hCB (hu C hC B hB hCA hBA (hesc C hC hCA hCM) h3)
  · by_cases hCA : C = A
    · rw [hCA]
      exact hAL.trans h.l_le
    · exact (le_sSup ⟨hC, hCA⟩ : C ≤ nqComplementaryLayer H A).trans hYM

end CFSG.Quasithin.H13.NQBlock
