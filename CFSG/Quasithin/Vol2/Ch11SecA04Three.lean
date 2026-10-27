module

public import CFSG.Quasithin.Vol2.Ch11SecA04Hyp319
public import CFSG.Quasithin.Vol2.Ch11SecA03Three
public import CFSG.Quasithin.Vol2.Ch11SecCB51
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem oPrimeResidualOf_three_eq_of_a319 (h318 : A318Facts) (h319 : A319Facts)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h331 : Stmt3_3_1) (h : Hyp11 G T L I n)
    {H V' : Subgroup G} (hLT : L ⊔ T ≤ H) (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHV : H ≤ Subgroup.normalizer (V' : Set G)) (hV : IsElemAbelian 2 (V'.subgroupOf H))
    (hHyp : A319Hyp (L.subgroupOf H) (V'.subgroupOf H)) : oPrimeResidualOf 3 H = L := by
  have hLH : L ≤ H := le_sup_left.trans hLT
  have hS := sqtkGroup_of_le_normalizer h331 h hHL
  have hSQ := SQTKHyp.of_sqtkGroup ↥H hS
  have h1 := a319 h318 h319 hS (h36 _ hSQ) (h38 _ hSQ)
    (subgroupOf_mem_cComp (mem_cComp_of_le h hLT hHL))
    (Subgroup.normal_subgroupOf_of_le_normalizer hHV) hV hHyp
  rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hLH]

theorem natOn_fsuV (h16 : ASInputs.AS_I_1_6) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : KindSL3 L (fsuV T I) n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)),
      Nat.card K = 2 ^ n ∧ NatOn L (fsuV T I) K φ := by
  have hLV := L_le_normalizer_fsuV h
  obtain ⟨hcomm, -, -, ⟨e⟩, hcases⟩ := h1102 G T L I n h
  have hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rcases card_cV_le h16 h1102 h with ⟨-, hC⟩ | ⟨hk', -⟩
    · exact hC
    · rcases hk' with hk' | hk'
      · exact (kind_not_SL3_Sp4 (by have := h.one_lt; omega) hk hk').elim
      · exact (kind_not_SL3_G2 hG2 h.one_lt hk hk').elim
  have hC' : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have : (v : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hv⟩
    rw [hC, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [← inf_centralizer_eq_pCoreOf hLV e]
    exact inf_le_right
  rcases hcases with ⟨K, _, _, hK, ⟨eS⟩, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩
  · rw [hC'] at hπ
    have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card ↥(StatedSL 3 K) := by
      rw [Nat.card_congr (e.trans eS).toEquiv,
        Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv]
    obtain ⟨φ, hφ⟩ := natOn_of_realizesVia hLV hπ hO hcard
    exact ⟨K, inferInstance, inferInstance, φ, hK, hφ⟩
  · exact (kind_not_SL3_Sp4 (by have := h.one_lt; omega) hk
      ⟨K, inferInstance, inferInstance, hK, he⟩).elim
  · exact (kind_not_SL3_G2 hG2 h.one_lt hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem natOn_sumTwo (h322 : Ch10.TmpL6_3_2_2_two) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n) (hS : SecC.SumTwoNatural L (VM T L I) n) :
    ∃ (W₁ W₂ : Subgroup G) (K : Type) (_ : Field K) (_ : Finite K)
      (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)),
      Nat.card K = 2 ^ n ∧ L ≤ Subgroup.normalizer (W₁ : Set G) ∧
      L ≤ Subgroup.normalizer (W₂ : Set G) ∧ W₁ ⊔ W₂ = VM T L I ∧ W₁ ⊓ W₂ = ⊥ ∧
      NatOn L W₁ K φ ∧ NatOn L W₂ K φ := by
  obtain ⟨W₁, W₂, hW₁, -, hLW₁, hLW₂, hinf, hsup, ⟨hc₁, K, _, _, hK, π, hπ⟩, -, hiso⟩ := hS
  obtain ⟨hVM, hR⟩ := stmt11_0_3_one h322 h
  have hLsub : IsSubnormal L (Subgroup.normalizer (L : Set G)) :=
    IsSubnormal.step Subgroup.le_normalizer (Subgroup.normal_subgroupOf_of_le_normalizer le_rfl)
      (IsSubnormal.refl _)
  have hO₁ : pCoreOf 2 L ≤ Subgroup.centralizer (W₁ : Set G) :=
    (InternalSec.pCoreOf_le_centralizer_of_isPrimeReduced hVM hR hLsub).trans
      (Subgroup.centralizer_le (show (W₁ : Set G) ⊆ (VM T L I : Set G) from hW₁))
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I n h
  obtain ⟨K₀, _, _, hK₀, ⟨e₀⟩⟩ := hk
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card ↥(StatedSL 3 K) := by
    rw [Nat.card_congr (e.trans e₀).toEquiv, card_SL_three' hK₀,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv, card_SL_three' hK]
  obtain ⟨φ, hφ⟩ := natOn_of_realizesVia hLW₁ hπ hO₁ hcard
  obtain ⟨e₁₂, he₁₂⟩ := exists_equiv_of_isXSectionIso₂ hLW₂ hiso
  exact ⟨W₁, W₂, K, inferInstance, inferInstance, φ, hK, hLW₁, hLW₂, hsup, hinf, hφ,
    natOn_of_equiv hLW₁ hφ e₁₂ (fun l w hw => he₁₂ l l.2 w hw)⟩

theorem stmt11_0_4_two (h318 : A318Facts) (h319 : A319Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (h331 : Stmt3_3_1) (h16 : ASInputs.AS_I_1_6)
    (hG2 : FactG2DerivedOrder) (h51 : AsB51) (h56 : AsB56) (hKF : SecC.KindModuleFacts)
    (h322 : Ch10.TmpL6_3_2_2_two) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    KindSL3 L (fsuV T I) n → Even n →
      ∀ x ∈ Subgroup.normalizer (L : Set G), orderOf x = 3 →
        (x ∈ Subgroup.normalizer (fsuV T I : Set G) ∨ L = ⁅L, thompsonJ T⁆ ∨
          fsuV T I = VM T L I) → x ∈ L := by
  intro hk hn x hxM hx3 hcase
  have key : ∀ {H V' : Subgroup G}, L ⊔ T ≤ H → H ≤ Subgroup.normalizer (L : Set G) →
      H ≤ Subgroup.normalizer (V' : Set G) → IsElemAbelian 2 (V'.subgroupOf H) →
      A319Hyp (L.subgroupOf H) (V'.subgroupOf H) → x ∈ H → x ∈ L := by
    intro H V' hLT hHL hHV hV hHyp hxH
    rw [← oPrimeResidualOf_three_eq_of_a319 h318 h319 h36 h38 h331 h hLT hHL hHV hV hHyp]
    exact Subgroup.subset_closure ⟨hxH, 1, by rw [pow_one]; exact hx3⟩
  have caseA : x ∈ Subgroup.normalizer (fsuV T I : Set G) → x ∈ L := by
    intro hxV
    obtain ⟨K, _, _, φ, hK, hφ⟩ := natOn_fsuV h16 hG2 h1102 h hk
    have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (fsuV T I : Set G) :=
      sup_le (le_inf Subgroup.le_normalizer (L_le_normalizer_fsuV h))
        (le_inf h.normal (T_le_normalizer_fsuV T I))
    exact key hLT inf_le_left inf_le_right (isElemAbelian_subgroupOf (isElemAbelian_fsuV h))
      (a319Hyp_one (le_sup_left.trans hLT) (le_inf (fsuV_le_normalizer_L h) Subgroup.le_normalizer)
        (L_le_normalizer_fsuV h) hn hK hφ) ⟨hxM, hxV⟩
  have hxVM : fsuV T I = VM T L I → x ∈ Subgroup.normalizer (fsuV T I : Set G) := by
    intro hV
    rw [hV]
    exact le_normalizer_conjClosure _ _ hxM
  rcases hcase with hxV | hJ | hV
  · exact caseA hxV
  · rcases SecC.fsuV_eq_VM_or h51 h56 h1102 hKF h322 h hJ with hV | ⟨-, -, hS⟩
    · exact caseA (hxVM hV)
    · obtain ⟨W₁, W₂, K, _, _, φ, hK, hLW₁, hLW₂, hsup, hinf, hφ₁, hφ₂⟩ :=
        natOn_sumTwo h322 h1102 h hk hS
      obtain ⟨hVMM, hR⟩ := stmt11_0_3_one h322 h
      exact key (sup_le Subgroup.le_normalizer h.normal) le_rfl (le_normalizer_conjClosure _ _)
        ((BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr
          hR.isElementaryAbelian)
        (a319Hyp_two Subgroup.le_normalizer hVMM hLW₁ hLW₂ hsup hinf hn hK hφ₁ hφ₂) hxM
  · exact caseA (hxVM hV)

end CFSG.Quasithin.Vol2.Ch11.SecA
