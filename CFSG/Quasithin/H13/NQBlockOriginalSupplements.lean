module

public import CFSG.Quasithin.H13.NQBlockOriginalTwoCore
public import CFSG.Quasithin.H13.NQBlockTIWeakClosure
public import CFSG.Quasithin.H13.NQBlockCommonResidual

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_ne_bot_of_faithfulLocal {T L : Subgroup G} (h : quasithinIsFaithfulLocal T L) :
    pCoreOf 2 L ≠ ⊥ := by
  intro h0
  apply h.2.2.2
  unfold quasithinV2
  rw [h0]
  have h1 : closure {z : G | z ∈ (⊥ : Subgroup G) ⊓ centralizer ((⊥ : Subgroup G) : Set G) ∧
      z ^ 2 = 1} = ⊥ := by
    rw [closure_eq_bot_iff]
    rintro z ⟨hz, -⟩
    exact mem_bot.mp (mem_inf.mp hz).1
  rw [h1, commutator_bot_left]

theorem isStronglyQuasithin_L_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) :
    CFSG.IsStronglyQuasithin L :=
  QuasithinUnique.isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank h.qtke.2.2
    (pCoreOf_ne_bot_of_faithfulLocal h.faithful_local)

omit [Finite G] in
theorem map_inf_normalizer_subgroupOf {B X R : Subgroup G} (hXB : X ≤ B) {R' : Subgroup ↥B}
    (hR' : R'.map B.subtype = R) :
    (X.subgroupOf B ⊓ normalizer (R' : Set ↥B)).map B.subtype = X ⊓ normalizer (R : Set G) := by
  rw [map_inf_eq _ _ _ B.subtype_injective, map_subtype_normalizer_eq, hR',
    map_subgroupOf_eq_of_le hXB, ← inf_assoc, inf_eq_left.mpr hXB]

theorem original_common_residual
    {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) :
    nqOriginalK T L ⊓ (CFSG.solvableRadical L).map L.subtype = pCoreOf 2 (nqOriginalK T L) ∧
      (∃ e : nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L) ≃* L ⧸ CFSG.solvableRadical L,
        ∀ (k : nqOriginalK T L) (hk : (k : G) ∈ L),
          e (QuotientGroup.mk k) = QuotientGroup.mk (⟨k, hk⟩ : L)) ∧
      (∃ (s : ℕ) (_ : Fact s.Prime), 5 ≤ s ∧
        Nonempty (L ⧸ CFSG.solvableRadical L ≃* projectiveSL 2 (ZMod s))) ∧
      ∀ L₁ : Subgroup G, L₁ ≤ L → T ≤ normalizer (L₁ : Set G) →
        L = (CFSG.solvableRadical L).map L.subtype ⊔ L₁ →
        L₁ = (L₁ ⊓ (CFSG.solvableRadical L).map L.subtype) ⊔ nqOriginalK T L ∧
          (CFSG.perfectResidual ↥(L₁ ⊓ normalizer (R : Set G))).map
            (L₁ ⊓ normalizer (R : Set G)).subtype = nqOriginalK T L ∧ nqOriginalK T L ≤ L₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLB : L ≤ L ⊔ T := le_sup_left
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  have hL'n := original_subgroupOf_normal hTL
  have hT2 : IsPGroup 2 (T.subgroupOf (L ⊔ T)) := h.sylow.1.comap_subtype
  let T' : Sylow 2 ↥(L ⊔ T) := hT2.toSylow h.maximal_local.1.2.2.1
  have hT' : (T' : Subgroup ↥(L ⊔ T)) = T.subgroupOf (L ⊔ T) := IsPGroup.toSylow_coe _ _
  have hBLT : L.subgroupOf (L ⊔ T) ⊔ (T' : Subgroup ↥(L ⊔ T)) = ⊤ :=
    hT' ▸ original_subgroupOf_sup_eq_top T L
  let eL : L.subgroupOf (L ⊔ T) ≃* L := subgroupOfEquivOfLe hLB
  have hSQT : CFSG.IsStronglyQuasithin (L.subgroupOf (L ⊔ T)) := fun r hr hr2 => by
    rw [CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv eL r]
    exact isStronglyQuasithin_L_of_qtnq h r hr hr2
  have hLC : CFSG.IsCComponent (⊤ : Subgroup (L.subgroupOf (L ⊔ T))) := by
    have hLc' : L.subgroupOf (L ⊔ T) ∈ cComp (⊤ : Subgroup ↥(L ⊔ T)) :=
      subgroupOf_mem_cComp h.maximal_local.1.2.1
    have h1 := subgroupOf_mem_cComp (cComp_mem_of_le hLc' le_rfl le_top)
    rw [subgroupOf_self] at h1
    exact mem_cComp_top_iff_isCComponent.mp h1
  let qO : (L.subgroupOf (L ⊔ T) ⧸ CFSG.pCore 2 (L.subgroupOf (L ⊔ T))) ≃*
      (L ⧸ CFSG.pCore 2 L) :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eL)
  have hq : ¬ CFSG.IsQuasisimple (L.subgroupOf (L ⊔ T) ⧸ CFSG.pCore 2 (L.subgroupOf (L ⊔ T))) :=
    fun hq' => h.not_quasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv qO hq')
  obtain ⟨C', hC'⟩ := exists_quotientCentralizer (L.subgroupOf (L ⊔ T))
    ((CFSG.solvableRadical (L.subgroupOf (L ⊔ T))).map (L.subgroupOf (L ⊔ T)).subtype)
  have hRmap := original_R_map hR hT' hC'
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup ↥(L ⊔ T), K' = (CFSG.perfectResidual ↥(L.subgroupOf (L ⊔ T) ⊓
      normalizer (((T' : Subgroup ↥(L ⊔ T)) ⊓ C' : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T)))).map
    (L.subgroupOf (L ⊔ T) ⊓
      normalizer (((T' : Subgroup ↥(L ⊔ T)) ⊓ C' : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T))).subtype :=
    ⟨_, rfl⟩
  have hKmap : K'.map (L ⊔ T).subtype = nqOriginalK T L := hK' ▸ original_K_map hR hRmap
  have hNmap := map_radical_subgroupOf hLB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hKN, -, -, ⟨e, he⟩, ⟨s, hs, hs5, ⟨eS⟩⟩,
      hL1⟩ :=
    radical_Sylow_normalizer_residual_is_common_simple_two_core_supplement
      (L.subgroupOf (L ⊔ T)) T' hBLT hSQT hLC hq _ C' _ _ K' rfl hC' rfl rfl hK'
  have hKN' : nqOriginalK T L ⊓ (CFSG.solvableRadical L).map L.subtype =
      pCoreOf 2 (nqOriginalK T L) := by
    have h1 := congrArg (Subgroup.map (L ⊔ T).subtype) hKN
    rw [map_inf_eq _ _ _ (L ⊔ T).subtype_injective, hKmap, hNmap] at h1
    rw [h1, ← hKmap]
    exact map_inSubgroup_pCore K' 2
  let eK : K' ≃* nqOriginalK T L :=
    (K'.equivMapOfInjective _ (L ⊔ T).subtype_injective).trans (MulEquiv.subgroupCongr hKmap)
  have heK : ∀ x : K', ((eK x : nqOriginalK T L) : G) = ((x : ↥(L ⊔ T)) : G) := fun _ => rfl
  let qK : (K' ⧸ CFSG.pCore 2 K') ≃* (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L)) :=
    QuotientGroup.congr _ _ eK (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eK)
  let qL : (L.subgroupOf (L ⊔ T) ⧸ CFSG.solvableRadical (L.subgroupOf (L ⊔ T))) ≃*
      (L ⧸ CFSG.solvableRadical L) :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.SteinbergBR.solvableRadical_map_equiv eL)
  have hiso : ∃ e : nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L) ≃*
      L ⧸ CFSG.solvableRadical L, ∀ (k : nqOriginalK T L) (hk : (k : G) ∈ L),
        e (QuotientGroup.mk k) = QuotientGroup.mk (⟨k, hk⟩ : L) := by
    refine ⟨qK.symm.trans (e.trans qL), fun k hk => ?_⟩
    have hk'G : ((eK.symm k : ↥(L ⊔ T)) : G) = (k : G) := by
      rw [← heK, MulEquiv.apply_symm_apply]
    have hk'L : ((eK.symm k : K') : ↥(L ⊔ T)) ∈ L.subgroupOf (L ⊔ T) := by
      rw [mem_subgroupOf, hk'G]
      exact hk
    have h1 : qK.symm (QuotientGroup.mk k) = QuotientGroup.mk (eK.symm k) := by
      rw [MulEquiv.symm_apply_eq]
      exact congrArg QuotientGroup.mk (eK.apply_symm_apply k).symm
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, he _ hk'L]
    exact congrArg QuotientGroup.mk (Subtype.ext hk'G)
  refine ⟨hKN', hiso, ⟨s, hs, hs5, ⟨qL.symm.trans eS⟩⟩, fun L₁ hL₁L hTL₁ hLNL₁ => ?_⟩
  have hL₁B : L₁ ≤ L ⊔ T := hL₁L.trans hLB
  have hL₁'L' : L₁.subgroupOf (L ⊔ T) ≤ L.subgroupOf (L ⊔ T) := fun x hx => hL₁L hx
  have hTL₁' : (T' : Subgroup ↥(L ⊔ T)) ≤
      normalizer ((L₁.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T)) := by
    rw [hT', ← subgroupOf_normalizer_eq hL₁B]
    exact fun x hx => hTL₁ hx
  have hLNL₁' : L.subgroupOf (L ⊔ T) = (CFSG.solvableRadical (L.subgroupOf (L ⊔ T))).map
      (L.subgroupOf (L ⊔ T)).subtype ⊔ L₁.subgroupOf (L ⊔ T) := by
    apply map_injective (L ⊔ T).subtype_injective
    rw [Subgroup.map_sup, hNmap, map_subgroupOf_eq_of_le hLB, map_subgroupOf_eq_of_le hL₁B]
    exact hLNL₁
  obtain ⟨-, h2, h3, h4⟩ := hL1 _ hL₁'L' hTL₁' hLNL₁'
  refine ⟨?_, ?_, ?_⟩
  · have h2' := congrArg (Subgroup.map (L ⊔ T).subtype) h2
    rwa [map_subgroupOf_eq_of_le hL₁B, Subgroup.map_sup,
      map_inf_eq _ _ _ (L ⊔ T).subtype_injective, map_subgroupOf_eq_of_le hL₁B, hNmap,
      hKmap] at h2'
  · have h3' := congrArg (Subgroup.map (L ⊔ T).subtype) h3
    rwa [← perfectCore_eq_map_perfectResidual, map_perfectCore,
      map_inf_normalizer_subgroupOf hL₁B hRmap, perfectCore_eq_map_perfectResidual,
      hKmap] at h3'
  · have h4' := map_mono (f := (L ⊔ T).subtype) h4
    rwa [hKmap, map_subgroupOf_eq_of_le hL₁B] at h4'

theorem commutator_qtnqVc_eq_of_sup {T L M L₁ : Subgroup G} (h : QTNQ T L M) (hL₁L : L₁ ≤ L)
    (hLNL₁ : L = (CFSG.solvableRadical L).map L.subtype ⊔ L₁) :
    ⁅qtnqVc M, L₁⁆ = qtnqU L M := by
  have hchar := (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).1
  have hLN : L ≤ normalizer (((CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G) :=
    le_normalizer.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  refine le_antisymm (commutator_mono le_rfl hL₁L) ?_
  rw [commutator_le]
  intro v hv l hl
  have hl' : l ∈ ((L₁ ⊔ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G) := by
    rw [sup_comm, ← hLNL₁]
    exact hl
  rw [coe_mul_of_left_le_normalizer_right _ _ (hL₁L.trans hLN), Set.mem_mul] at hl'
  obtain ⟨l₁, hl₁, n, hn, rfl⟩ := hl'
  have hnc : n ∈ centralizer (qtnqVc M : Set G) := by
    rw [← h.centralizer_eq_radical] at hn
    exact (mem_inf.mp hn).2
  have hvn : n * v⁻¹ = v⁻¹ * n := (mem_centralizer_iff.mp hnc v⁻¹ (inv_mem hv)).symm
  have e : ⁅v, l₁ * n⁆ = ⁅v, l₁⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc v * (l₁ * n) * v⁻¹ * (l₁ * n)⁻¹ = v * l₁ * (n * v⁻¹) * n⁻¹ * l₁⁻¹ := by group
      _ = v * l₁ * (v⁻¹ * n) * n⁻¹ * l₁⁻¹ := by rw [hvn]
      _ = v * l₁ * v⁻¹ * l₁⁻¹ := by group
  rw [e]
  exact commutator_mem_commutator hv hl₁

theorem original_supplement_clause
    {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) :
    ∀ L₁ : Subgroup G, L₁ ≤ L → T ≤ normalizer (L₁ : Set G) →
      L = (CFSG.solvableRadical L).map L.subtype ⊔ L₁ →
      (CFSG.perfectResidual ↥(L₁ ⊓ normalizer (R : Set G))).map
          (L₁ ⊓ normalizer (R : Set G)).subtype = nqOriginalK T L ∧ nqOriginalK T L ≤ L₁ ∧
        L₁ = (L₁ ⊓ (CFSG.solvableRadical L).map L.subtype) ⊔ nqOriginalK T L ∧
        ⁅qtnqVc M, L₁⁆ = qtnqU L M := fun L₁ hL₁L hTL₁ hLNL₁ => by
  obtain ⟨-, -, -, hL1⟩ := original_common_residual h hR
  obtain ⟨h1, h2, h3⟩ := hL1 L₁ hL₁L hTL₁ hLNL₁
  exact ⟨h2, h3, h1, commutator_qtnqVc_eq_of_sup h hL₁L hLNL₁⟩

theorem original_K_supplement {T L M : Subgroup G} (h : QTNQ T L M) :
    nqOriginalK T L ≤ L ∧ T ≤ normalizer (nqOriginalK T L : Set G) ∧
      L = (CFSG.solvableRadical L).map L.subtype ⊔ nqOriginalK T L := by
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.eq_normalizer ▸ h.t_le)
  obtain ⟨-, -, -, -, -, hLNK, -, -, -, hTK, -, -, -⟩ :=
    original_radical_supplement h.sylow.1 h.maximal_local.1.2.2.1 (h.eq_normalizer ▸ h.t_le)
      h.maximal_local.1.2.1 hR
  exact ⟨le_sup_right.trans hLNK.ge, hTK, hLNK⟩

theorem original_singleton_iff {T L M : Subgroup G} (h : QTNQ T L M) :
    (quasithinIsMaxTwoLocal M ∧ nqOriginalK T L ⊔ T ≤ M ∧
        ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → nqOriginalK T L ⊔ T ≤ M' → M' = M) ↔
      ∀ L₁ : Subgroup G, L₁ ≤ L → T ≤ normalizer (L₁ : Set G) →
        L = (CFSG.solvableRadical L).map L.subtype ⊔ L₁ →
        quasithinIsMaxTwoLocal M ∧ L₁ ⊔ T ≤ M ∧
          ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L₁ ⊔ T ≤ M' → M' = M := by
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.eq_normalizer ▸ h.t_le)
  obtain ⟨hKL, hTK, hLNK⟩ := original_K_supplement h
  constructor
  · rintro ⟨hM, -, huniq⟩ L₁ hL₁L hTL₁ hLNL₁
    have hKL₁ := (original_supplement_clause h hR L₁ hL₁L hTL₁ hLNL₁).2.1
    exact ⟨hM, sup_le (hL₁L.trans h.l_le) h.t_le, fun M' hM' hL₁M' =>
      huniq M' hM' ((sup_le_sup_right hKL₁ T).trans hL₁M')⟩
  · intro hall
    exact hall _ hKL hTK hLNK

theorem original_TI_weak_closure {T L M : Subgroup G} (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M) {W : Subgroup G}
    (hW : W = sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧ X ≤ T}) :
    nqOriginalK T L ≤ (CFSG.perfectResidual ↥(L ⊓ normalizer (W : Set G))).map
        (L ⊓ normalizer (W : Set G)).subtype ∧
      (quasithinIsMaxTwoLocal M ∧ nqOriginalK T L ⊔ T ≤ M ∧
          (∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → nqOriginalK T L ⊔ T ≤ M' → M' = M) →
        normalizer (W : Set G) ≤ M) := by
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.eq_normalizer ▸ h.t_le)
  obtain ⟨-, -, -, -, -, -, -, -, hLNKW, hTKW, -, -, hWM⟩ :=
    nq_TI_weak_closure_local_normalizer_witness h hTI (R := T ⊓ centralizer (qtnqU L M : Set G))
      (A := L ⊓ normalizer (W : Set G)) hW rfl rfl rfl
  have hKWL : (CFSG.perfectResidual ↥(L ⊓ normalizer (W : Set G))).map
      (L ⊓ normalizer (W : Set G)).subtype ≤ L := (map_subtype_le _).trans inf_le_left
  refine ⟨(original_supplement_clause h hR _ hKWL hTKW hLNKW).2.1, fun hS => hWM ?_⟩
  exact ((original_singleton_iff h).mp hS) _ hKWL hTKW hLNKW

theorem original_radical_supplements_share_simple_residual_and_internal_module
    {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) :
    quasithinIsLocal T (nqOriginalK T L) ∧ R = pCoreOf 2 (nqOriginalK T L ⊔ T) ∧ R ≠ ⊥ ∧
      nqOriginalK T L ⊓ (CFSG.solvableRadical L).map L.subtype = pCoreOf 2 (nqOriginalK T L) ∧
      (∃ e : nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L) ≃* L ⧸ CFSG.solvableRadical L,
        ∀ (k : nqOriginalK T L) (hk : (k : G) ∈ L),
          e (QuotientGroup.mk k) = QuotientGroup.mk (⟨k, hk⟩ : L)) ∧
      (∃ (s : ℕ) (_ : Fact s.Prime), 5 ≤ s ∧
        Nonempty (L ⧸ CFSG.solvableRadical L ≃* projectiveSL 2 (ZMod s))) ∧
      ⁅qtnqVc M, nqOriginalK T L⁆ = qtnqU L M ∧ qtnqU L M ≠ ⊥ ∧
      (∀ L₁ : Subgroup G, L₁ ≤ L → T ≤ normalizer (L₁ : Set G) →
        L = (CFSG.solvableRadical L).map L.subtype ⊔ L₁ →
        (CFSG.perfectResidual ↥(L₁ ⊓ normalizer (R : Set G))).map
            (L₁ ⊓ normalizer (R : Set G)).subtype = nqOriginalK T L ∧ nqOriginalK T L ≤ L₁ ∧
          L₁ = (L₁ ⊓ (CFSG.solvableRadical L).map L.subtype) ⊔ nqOriginalK T L ∧
          ⁅qtnqVc M, L₁⁆ = qtnqU L M) ∧
      ((quasithinIsMaxTwoLocal M ∧ nqOriginalK T L ⊔ T ≤ M ∧
          ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → nqOriginalK T L ⊔ T ≤ M' → M' = M) ↔
        ∀ L₁ : Subgroup G, L₁ ≤ L → T ≤ normalizer (L₁ : Set G) →
          L = (CFSG.solvableRadical L).map L.subtype ⊔ L₁ →
          quasithinIsMaxTwoLocal M ∧ L₁ ⊔ T ≤ M ∧
            ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L₁ ⊔ T ≤ M' → M' = M) ∧
      ((∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
          CFSG.conjugate (qtnqU L M) g = qtnqU L M) →
        ∀ W : Subgroup G,
          W = sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧ X ≤ T} →
          nqOriginalK T L ≤ (CFSG.perfectResidual ↥(L ⊓ normalizer (W : Set G))).map
            (L ⊓ normalizer (W : Set G)).subtype ∧
          (quasithinIsMaxTwoLocal M ∧ nqOriginalK T L ⊔ T ≤ M ∧
              (∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → nqOriginalK T L ⊔ T ≤ M' →
                M' = M) →
            normalizer (W : Set G) ≤ M)) := by
  obtain ⟨hRne, -, -, -, -, hloc, -, -⟩ :=
    original_radical_normalizer_local_and_Thompson_failure h hR
  obtain ⟨hKN, hiso, hpsl, -⟩ := original_common_residual h hR
  obtain ⟨-, -, -, -, ⟨hU1, -, -, -⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  obtain ⟨hKL, -, hLNK⟩ := original_K_supplement h
  exact ⟨hloc, (original_radical_normalizer_centralizer_is_two_core h hR).1, hRne, hKN, hiso,
    hpsl, commutator_qtnqVc_eq_of_sup h hKL hLNK, hU1, original_supplement_clause h hR,
    original_singleton_iff h, fun hTI _ hW => original_TI_weak_closure h hTI hW⟩

end CFSG.Quasithin.H13.NQBlock
