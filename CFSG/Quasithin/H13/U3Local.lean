module

public import CFSG.Quasithin.H13.U3LocalSylow
public import CFSG.Quasithin.H13.AssemblyLocal
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.SteinbergCBIrreducibleTI

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def UniqueMaxTwoLocal (X M : Subgroup G) : Prop :=
  quasithinIsMaxTwoLocal M ∧ X ≤ M ∧ ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ≤ M' → M' = M

@[expose] def FiveQuotientExactOrders : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    (Nonempty (Q ≃* alternatingGroup (Fin 5)) → Nat.card Q = 60) ∧
    (LieModel Q .PSL 3 2 1 → Nat.card Q = 168) ∧
    (Nonempty (Q ≃* alternatingGroup (Fin 6)) → Nat.card Q = 360) ∧
    (Group.IsPerfect Q → Nat.card (center Q) = 3 →
      Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 6)) → Nat.card Q = 1080) ∧
    (LieModel Q .PSU 3 3 1 → Nat.card Q = 6048) ∧
    (QT13Five Q → Nat.card Q ≤ 6048)

@[expose] def LocalTwoCoreQuotientStrictGrowth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S L K : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsLocal S L →
    quasithinIsLocal S K → L ≤ K → S ≤ normalizer (L : Set G) →
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≤ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ↔ L = K)

@[expose] def SylowNormalizedMaximalLocalUniqueNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    quasithinIsMaximalLocal T L → T ≤ normalizer (L : Set G) → pCoreOf 2 L ≠ ⊥ →
    normalizer (L : Set G) = normalizer (pCoreOf 2 L : Set G) ∧
      UniqueMaxTwoLocal (L ⊔ T) (normalizer (L : Set G)) ∧
      ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q → Q ≤ L ⊔ T → L ⊔ T ≤ normalizer (Q : Set G) →
        normalizer (Q : Set G) ≤ normalizer (L : Set G) ∧
          UniqueMaxTwoLocal (normalizer (Q : Set G)) (normalizer (L : Set G))

theorem pCoreOf_ne_bot_of_isFaithfulLocal {T L : Subgroup G} (hL : quasithinIsFaithfulLocal T L) :
    pCoreOf 2 L ≠ ⊥ := by
  intro h
  apply hL.2.2.2
  rw [quasithinV2, h]
  have h1 : closure {z : G | z ∈ (⊥ : Subgroup G) ⊓ centralizer ((⊥ : Subgroup G) : Set G) ∧
      z ^ 2 = 1} = ⊥ := by
    rw [eq_bot_iff, closure_le]
    rintro z ⟨⟨hz, -⟩, -⟩
    exact hz
  rw [h1, commutator_bot_left]

theorem u3_original_local_maximality_and_unique_normalizer
    (hD : LocalDoubleEmbeddingExclusion) (h137 : Stmt13_1_7) (h1323 : Stmt13_1_2_three)
    (hord : FiveQuotientExactOrders) (hgrow : LocalTwoCoreQuotientStrictGrowth)
    (hA7 : SylowNormalizedMaximalLocalUniqueNormalizer) [Finite G] {T L : Subgroup G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    (quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) ∧ T ≤ normalizer (L : Set G) ∧
      normalizer (L : Set G) = normalizer (pCoreOf 2 L : Set G) ∧
      UniqueMaxTwoLocal (L ⊔ T) (normalizer (L : Set G)) ∧
      ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → P ≤ L ⊔ T → L ⊔ T ≤ normalizer (P : Set G) →
        normalizer (P : Set G) ≤ normalizer (L : Set G) ∧
          UniqueMaxTwoLocal (normalizer (P : Set G)) (normalizer (L : Set G)) := by
  obtain ⟨hs, hnab, hqtke, hsyl, hLf, hexcl, -⟩ := hH
  have hTL : T ≤ normalizer (L : Set G) :=
    (unitary_three_field_three_local_Sylow_normalization hs hnab hqtke hLf.1 hU3).2.1
  obtain ⟨K, ⟨hKmax, hKf⟩, hLK⟩ := faithful_maximal_local_exists hD hs hnab hqtke hsyl hLf
  have hKq := h137 G T hs hnab hqtke hsyl hexcl K hKf
  have hK5 := h1323 G T K hs hnab hqtke hsyl hexcl hKmax hKf hKq
  have hKcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≤ 6048 := (hord _).2.2.2.2.2 hK5
  have hLcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := (hord _).2.2.2.2.1 hU3
  obtain ⟨hle, heq⟩ := hgrow G T L K hs hnab hqtke hLf.1 hKmax.1 hLK hTL
  have hLKeq : L = K := heq.1 (by omega)
  subst hLKeq
  have hO2 := pCoreOf_ne_bot_of_isFaithfulLocal hLf
  obtain ⟨h1, h2, h3⟩ := hA7 G T L hs hnab hqtke hsyl hKmax hTL hO2
  exact ⟨⟨hKmax, hLf⟩, hTL, h1, h2, h3⟩

theorem u3_selected_local_normalizer_and_TI
    (hD : LocalDoubleEmbeddingExclusion) (h137 : Stmt13_1_7) (h1323 : Stmt13_1_2_three)
    (hord : FiveQuotientExactOrders) (hgrow : LocalTwoCoreQuotientStrictGrowth)
    (hA7 : SylowNormalizedMaximalLocalUniqueNormalizer) [Finite G] {T L V : Subgroup G} {z : G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hF : SteinbergCB.QTU3InternalFrame T L V z) :
    normalizer (L : Set G) < ⊤ ∧ normalizer (V : Set G) ≤ normalizer (L : Set G) ∧
      (∀ m ∈ normalizer (L : Set G), CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
      (∀ U : Subgroup G, U ≠ ⊥ → U ≤ V → ∀ H : Subgroup G, H ≤ normalizer (U : Set G) →
        H ⊓ normalizer (L : Set G) = H ⊓ normalizer (V : Set G)) ∧
      ∀ v ∈ V, v ≠ 1 →
        normalizer (L : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hNO2, -, h3⟩ :=
    u3_original_local_maximality_and_unique_normalizer hD h137 h1323 hord hgrow hA7 hH hU3
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

end CFSG.Quasithin.H13.U3
