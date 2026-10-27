module

public import CFSG.Quasithin.H13.U3Escape
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_maxTwoLocal_le [Finite G] {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ M : Subgroup G, quasithinIsMaxTwoLocal M ∧ H ≤ M := by
  obtain ⟨M, hHM, hM⟩ := Finite.exists_le_maximal (p := IsTwoLocal) hH
  exact ⟨M, ⟨hM.1, fun K hK hMK => le_antisymm (hM.2 hK hMK) hMK⟩, hHM⟩

theorem normalizer_le_of_uniqueMaxTwoLocal [Finite G] {X M P : Subgroup G}
    (huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ≤ M' → M' = M) (hP1 : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hXP : X ≤ normalizer (P : Set G)) :
    normalizer (P : Set G) ≤ M := by
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_le ⟨P, hP1, hP2, rfl⟩
  rw [← huniq M' hM' (hXP.trans hle)]
  exact hle

theorem u3_original_local_maximality_and_unique_normalizer_of_1332 (h1332 : Stmt13_3_2)
    [Finite G] {T L : Subgroup G} (hH : QTH13 G T L) :
    (quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) ∧ T ≤ normalizer (L : Set G) ∧
      normalizer (L : Set G) = normalizer (pCoreOf 2 L : Set G) ∧
      UniqueMaxTwoLocal (L ⊔ T) (normalizer (L : Set G)) ∧
      ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → P ≤ L ⊔ T → L ⊔ T ≤ normalizer (P : Set G) →
        normalizer (P : Set G) ≤ normalizer (L : Set G) ∧
          UniqueMaxTwoLocal (normalizer (P : Set G)) (normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTL, hmax, hMmax, huniq⟩, -, -⟩ := h1332 G T L hH L hH.faithful
  have hLT : L ⊔ T ≤ normalizer (L : Set G) := sup_le le_normalizer hTL
  have hNO : normalizer (L : Set G) ≤ normalizer (pCoreOf 2 L : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hO2 := pCoreOf_ne_bot_of_isFaithfulLocal hH.faithful
  refine ⟨⟨hmax, hH.faithful⟩, hTL, le_antisymm hNO ?_, ⟨hMmax, hLT, huniq⟩,
    fun P hP1 hP2 _ hLTP => ?_⟩
  · exact normalizer_le_of_uniqueMaxTwoLocal huniq hO2 (LieType.BorelTits.pCoreOf_isPGroup 2 L)
      (hLT.trans hNO)
  · have hPM := normalizer_le_of_uniqueMaxTwoLocal huniq hP1 hP2 hLTP
    exact ⟨hPM, hMmax, hPM, fun M' hM' hPM' => huniq M' hM' (hLTP.trans hPM')⟩

theorem u3_selected_local_normalizer_and_TI_of_1332 (h1332 : Stmt13_3_2) [Finite G]
    {T L V : Subgroup G} {z : G} (hH : QTH13 G T L) (hF : SteinbergCB.QTU3InternalFrame T L V z) :
    normalizer (L : Set G) < ⊤ ∧ normalizer (V : Set G) ≤ normalizer (L : Set G) ∧
      (∀ m ∈ normalizer (L : Set G), CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
      (∀ U : Subgroup G, U ≠ ⊥ → U ≤ V → ∀ H : Subgroup G, H ≤ normalizer (U : Set G) →
        H ⊓ normalizer (L : Set G) = H ⊓ normalizer (V : Set G)) ∧
      ∀ v ∈ V, v ≠ 1 →
        normalizer (L : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hNO2, -, h3⟩ := u3_original_local_maximality_and_unique_normalizer_of_1332 h1332 hH
  obtain ⟨hTL, hVT, hVe, hV64, -, -, hLV, hTV, hirr, -, -, -, -⟩ := hF
  set M := normalizer (L : Set G) with hM
  have hMtop : M < ⊤ := by
    have : IsSimpleGroup G := hH.simple
    refine lt_top_iff_ne_top.2 (ne_top_of_pCoreOf_ne_bot_of_simple hH.nonabelian ?_)
    intro hbot
    have hO2 := pCoreOf_ne_bot_of_isFaithfulLocal hH.faithful
    apply hO2
    rw [eq_bot_iff]
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 M := by
      rw [hNO2]
      exact LieType.BorelTits.le_pCoreOf_normalizer 2 (pCoreOf 2 L)
        (LieType.BorelTits.pCoreOf_isPGroup 2 L)
    rw [← hbot]
    exact h1
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  have hVM : normalizer (V : Set G) ≤ M := by
    refine (h3 V hV1 ?_ (hVT.trans le_sup_right) (sup_le hLV hTV)).1
    exact (IsElementaryAbelian.isPGroup 2 V).of_equiv (MulEquiv.refl _)
  have hLM : L ≤ M := le_normalizer
  have hLn : (L.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hLM).2 le_rfl
  obtain ⟨hTI, -, hHM⟩ :=
    SteinbergCB.irreducible_local_module_is_TI_in_local_normalizer hLM hLn hV1 hVe hLV hirr
  have hconj : ∀ m : G, MulAut.conj m⁻¹ • V = CFSG.conjugate V m := fun m => by
    ext x
    rw [SteinbergCB.mem_conj_inv_smul_iff, mem_conjugate_iff']
  refine ⟨hMtop, hVM, fun m hm => ?_, fun U hU1 hUV H hH => hHM hVM U hU1 hUV H hH,
    fun v hv hv1 => ?_⟩
  · rcases hTI m hm with h | h
    · right
      rwa [hconj] at h
    · left
      rwa [hconj] at h
  · have hzp : zpowers v ≠ ⊥ := by
      intro h
      exact hv1 (by rw [← mem_bot, ← h]; exact mem_zpowers v)
    have hcn : centralizer ({v} : Set G) ≤ normalizer ((zpowers v : Subgroup G) : Set G) := by
      have h := Subgroup.centralizer_le_normalizer ((zpowers v : Subgroup G) : Set G)
      rwa [zpowers_eq_closure, centralizer_closure, ← zpowers_eq_closure] at h
    have h1 := hHM hVM (zpowers v) hzp (zpowers_le.2 hv) (centralizer ({v} : Set G)) hcn
    intro x hx
    have hx' : x ∈ centralizer ({v} : Set G) ⊓ M := ⟨hx.2, hx.1⟩
    rw [h1] at hx'
    exact hx'.2

theorem u3_local_uniqueness_and_escape_producer_of_1332 (h1332 : Stmt13_3_2)
    (hconf : U3ConfinedCentralizerOvergroup) (hexcl : ExcludedMinimalOvergroupTwoRankBound) :
    U3LocalUniquenessEscapeProducer := by
  intro G _ _ T L V z hH hU3 hF
  obtain ⟨hMtop, hVM, hTI, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  refine ⟨hMtop, hVM, fun m hm => hTI m hm, fun hz => ?_⟩
  obtain ⟨-, -, -, -, -, -, hZM, -, ⟨H, ⟨hTH, hR, hHM⟩, hleast⟩, hmin⟩ :=
    hconf G T L V z hH hU3 hF hz
  obtain ⟨-, hns, -, -, hTn, huniq, h6⟩ := hmin H hTH hR hHM hleast
  have h4 := hexcl G T _ H hH.simple hH.nonabelian hH.qtke hH.sylow hH.not_excluded hZM hTH hns
    hR hTn hHM huniq
  omega

end CFSG.Quasithin.H13.U3
