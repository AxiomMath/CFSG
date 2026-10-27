module

public import CFSG.Quasithin.H13.NQRigidInputs
public import CFSG.Quasithin.H13.NQBlockXTPlacement
public import CFSG.Quasithin.H13.NQBlockCharNormalizerEscape

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem cpu_data_subgroupOf {H R K M : Subgroup G} (hRH : R ≤ H) (hR2 : IsPGroup 2 R)
    (hRc : pCoreOf 2 (H ⊓ normalizer (R : Set G)) = R) (hKc : K ∈ cComp H)
    (hKF : quasithinGenFitting K = pCoreOf 2 K) (hKq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hRK : R ≤ normalizer (K : Set G)) (hKM : ¬ K ≤ M)
    (hD : ∀ D : Subgroup G, D ≠ ⊥ → D ≤ R → (D.subgroupOf R).Characteristic →
      H ⊓ normalizer (D : Set G) ≤ M) :
    IsPGroup 2 (R.subgroupOf H) ∧
      R.subgroupOf H = (CFSG.pCore 2 ↥(normalizer ((R.subgroupOf H : Subgroup H) : Set H))).map
        (normalizer ((R.subgroupOf H : Subgroup H) : Set H)).subtype ∧
      CFSG.IsCComponent (K.subgroupOf H) ∧
      CFSG.generalizedFitting ↥(K.subgroupOf H) = CFSG.pCore 2 ↥(K.subgroupOf H) ∧
      CFSG.IsQuasisimple (↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H)) ∧
      R.subgroupOf H ≤ normalizer ((K.subgroupOf H : Subgroup H) : Set H) ∧
      ¬ K.subgroupOf H ≤ M.subgroupOf H ∧
      (∀ D : Subgroup ↥(R.subgroupOf H), D.Characteristic → D ≠ ⊥ →
        normalizer ((D.map (R.subgroupOf H).subtype : Subgroup H) : Set H) ≤ M.subgroupOf H) ∧
      Nonempty (↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H) ≃* ↥K ⧸ CFSG.pCore 2 ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  let e : ↥(K.subgroupOf H) ≃* ↥K := subgroupOfEquivOfLe hKH
  let e₂ : ↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H) ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
    QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
  refine ⟨hR2.comap_subtype, ?_, mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hKc),
    ?_, (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e₂).2 hKq,
    fun r hr => mem_normalizer_subgroupOf_of_mem (hRK hr), ?_, ?_, ⟨e₂⟩⟩
  ·
    apply Subgroup.map_injective H.subtype_injective
    have e1 : (CFSG.pCore 2 ↥(normalizer ((R.subgroupOf H : Subgroup H) : Set H))).map
        (normalizer ((R.subgroupOf H : Subgroup H) : Set H)).subtype =
        pCoreOf 2 (normalizer ((R.subgroupOf H : Subgroup H) : Set H)) := by
      unfold pCoreOf
      try with_reducible rfl
    rw [e1, pCoreOf_map_subtype, map_subtype_normalizer_eq, map_subgroupOf_eq_of_le hRH, hRc]
  ·
    have hc : CFSG.IsCharacteristicP 2 ↥K := by
      have h1 := (centralizer_pCore_le_iff_pCoreOf 2 K).mpr
        ((quasithinGenFitting_eq_pCoreOf_iff K 2).mp hKF)
      change centralizer (CFSG.pCore 2 ↥K : Set ↥K) ≤ CFSG.pCore 2 ↥K
      exact h1
    exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥(K.subgroupOf H) 2).mp
      (CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv e.symm hc)
  ·
    intro hle
    apply hKM
    intro k hk
    exact hle (show (⟨k, hKH hk⟩ : H) ∈ K.subgroupOf H from hk)
  ·
    intro D hDc hD1
    set DH : Subgroup H := D.map (R.subgroupOf H).subtype with hDHdef
    have hDHR : DH ≤ R.subgroupOf H := Subgroup.map_subtype_le D
    have hDR : DH.map H.subtype ≤ R := by
      rw [← map_subgroupOf_eq_of_le hRH]
      exact Subgroup.map_mono hDHR
    have hD1' : DH.map H.subtype ≠ ⊥ := by
      intro hb
      apply hD1
      have hDH : DH = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hb
      exact (Subgroup.map_eq_bot_iff_of_injective _ (R.subgroupOf H).subtype_injective).mp hDH
    have hDc' : ((DH.map H.subtype).subgroupOf R).Characteristic := by
      let eR : ↥(R.subgroupOf H) ≃* ↥R := subgroupOfEquivOfLe hRH
      have h1 := characteristic_map_mulEquiv eR hDc
      have h2 : D.map eR.toMonoidHom = (DH.map H.subtype).subgroupOf R := by
        ext ⟨x, hx⟩
        simp only [Subgroup.mem_map, mem_subgroupOf, hDHdef, Subgroup.coe_subtype]
        constructor
        · rintro ⟨d, hd, hde⟩
          refine ⟨(d : H), ⟨d, hd, rfl⟩, ?_⟩
          have := congrArg Subtype.val hde
          exact this
        · rintro ⟨y, ⟨d, hd, rfl⟩, hyx⟩
          refine ⟨d, hd, Subtype.ext ?_⟩
          exact hyx
      rw [← h2]
      exact h1
    have h1 := hD _ hD1' hDR hDc'
    intro x hx
    have hx' := Subgroup.mem_map_of_mem H.subtype hx
    rw [map_subtype_normalizer_eq] at hx'
    exact h1 hx'

theorem cpuOffenderSection_of (h : NQRigid.StmtCPUOffenderSection) : CPUOffenderSection := by
  intro G _ _ H R K M hRH hR2 hRc hKc hKF hKq hRK _ hKM hD
  obtain ⟨hR2', hRc', hKc', hKF', hKq', hRK', hKM', hD', ⟨e₂⟩⟩ :=
    cpu_data_subgroupOf hRH hR2 hRc hKc hKF hKq hRK hKM hD
  obtain ⟨W, i₁, i₂, i₃, i₄, L₁, B₁, hq, hirr, hB, hB1, hBn, hquad, hcard, ⟨φ⟩⟩ :=
    h H (R.subgroupOf H) hR2' hRc' (K.subgroupOf H) hKc' hKF' hKq' hRK' (M.subgroupOf H) hKM' hD'
  let e₃ := QuotientGroup.congr _ _ e₂ (Subgroup.map_center_eq e₂)
  exact ⟨W, i₁, i₂, i₃, i₄, L₁, B₁, hq, hirr, hBn, hB1, hB, hquad, hcard, ⟨φ.trans e₃⟩⟩

theorem evenLinearCPUShortBlock_of (h : NQRigid.StmtCPUShortBlock) : EvenLinearCPUShortBlock := by
  intro G _ _ H R K M hRH hR2 hRc hKc hKF hKq hRK _ hKM hD n hn F _ _ hF ⟨φ⟩
  obtain ⟨hR2', hRc', hKc', hKF', hKq', hRK', hKM', hD', ⟨e₂⟩⟩ :=
    cpu_data_subgroupOf hRH hR2 hRc hKc hKF hKq hRK hKM hD
  let e₃ := QuotientGroup.congr _ _ e₂ (Subgroup.map_center_eq e₂)
  exact h H (R.subgroupOf H) hR2' hRc' (K.subgroupOf H) hKc' hKF' hKq' hRK' (M.subgroupOf H) hKM'
    hD' n hn F hF ⟨e₃.trans φ⟩

theorem originalXTPlacement_of_groupCPU
    (hO : OriginalXTOrbitPlacement) (hCPU : NQRigid.StmtCPUOffenderSection)
    (hE : NQRigid.StmtCPUShortBlock) : OriginalXTPlacement :=
  originalXTPlacement_of hO (cpuOffenderSection_of hCPU) (evenLinearCPUShortBlock_of hE)

theorem original_characteristic_witness_singleton_of_groupCPU
    (hO : OriginalXTOrbitPlacement) (hCPU : NQRigid.StmtCPUOffenderSection)
    (hE : NQRigid.StmtCPUShortBlock) (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hSp4 : OriginalWitnessExcludesEvenSymplecticFour)
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype) (hXc : (X.subgroupOf L).Characteristic)
    (hX2 : CFSG.pCore 2 X ≠ ⊥) (hXno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧
      CFSG.Quasithin.SteinbergCC.normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V,
        CFSG.Quasithin.SteinbergCC.normalizerFrattiniConj X l w ∈ V) → V = ⊥ ∨ V = ⊤) :
    quasithinIsMaxTwoLocal M ∧ X ⊔ T ≤ M ∧
      ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ⊔ T ≤ M' → M' = M :=
  original_characteristic_witness_singleton_of_orbit hO (cpuOffenderSection_of hCPU)
    (evenLinearCPUShortBlock_of hE) hCat hSp4 h hp hp5 hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr

end CFSG.Quasithin.H13.NQBlock
