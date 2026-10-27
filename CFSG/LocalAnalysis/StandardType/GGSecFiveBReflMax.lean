module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxStep6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHCRowDefs
import CFSG.LocalAnalysis.StandardType.GGLargeRowCard
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType

private theorem false_of_weylInf_typeB {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixB M)
    {ι' : Type} {M' : CoxeterMatrix ι'} (hB : GGIsWeylMatrixB M')
    (f : M'.Group ≃* ↥(ggAInf p B Bs x L D J))
    (hf : ∀ i : ι', GGIsReflection p
      ((f (M'.simple i) : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs))
    {y : G} {K : Subgroup G} (hN : GGNbr p B x D J y K)
    (hKnot : ¬ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) : False := by
  obtain ⟨m, σ, hm, rfl⟩ := hB
  obtain ⟨n, -, hBs_card, hW_card⟩ := hR.exists_card_eq_of_typeB hTBF hWI e hP hM
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hWeylB : GGWeylOfType p (CoxeterMatrix.B m) (ggAInf p B Bs x L D J) :=
    GGWeylOfType.of_reindex (M := CoxeterMatrix.B m) (e := σ) ⟨f, hf⟩
  have hpm : p ^ m ≤ Nat.card Bs := pow_le_card_of_weylOfType_B hp hp2 hBs hm hWeylB
  have hmn : m ≤ n := by
    refine (Nat.pow_le_pow_iff_right hp.one_lt).mp ?_
    calc p ^ m ≤ Nat.card Bs := hpm
      _ = p ^ n := hBs_card
  have hcardA : Nat.card (ggAInf p B Bs x L D J) = 2 ^ m * m.factorial := by
    rw [← Nat.card_congr f.toEquiv]
    rw [Nat.card_congr ((CoxeterMatrix.B m).reindexGroupEquiv σ).toEquiv,
      ggCoxeterB_card m hm]
  have hcard_le :
      Nat.card (ggAInf p B Bs x L D J) ≤ Nat.card (ggAutomizerJoin L Bs 𝒦) := by
    rw [hcardA, hW_card]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hmn) (Nat.factorial_le hmn)
  have hWeq : ggAutomizerJoin L Bs 𝒦 = ggAInf p B Bs x L D J :=
    Subgroup.eq_of_le_of_card_ge (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1) hcard_le
  exact hKnot (hWeq ▸ ggAutomizer_le_ggAInf_of_nbr hN)

private theorem typeF4_data
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixB M)
    {ι' : Type} {M' : CoxeterMatrix ι'} (hF : GGIsWeylMatrixF4 M')
    (f : M'.Group ≃* ↥(ggAInf p B Bs x L D J))
    (hf : ∀ i : ι', GGIsReflection p
      ((f (M'.simple i) : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs)) :
    Nat.card (ggAInf p B Bs x L D J) = 1152 ∧
      Nat.card (ggAutomizerJoin L Bs 𝒦) = 384 ∧
        ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
          ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
  obtain ⟨σ, rfl⟩ := hF
  obtain ⟨n, hn4, hBs_card, hW_card⟩ := hR.exists_card_eq_of_typeB hTBF hWI e hP hM
  have hcardA : Nat.card (ggAInf p B Bs x L D J) = 1152 := by
    rw [← Nat.card_congr f.toEquiv]
    rw [Nat.card_congr ((CoxeterMatrix.F₄).reindexGroupEquiv σ).toEquiv]
    exact l04fFRC_ord_card_coxeterF4
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  have hW' : GGWeylOfType p CoxeterMatrix.F₄ (ggAInf p B Bs x L D J) :=
    GGWeylOfType.of_reindex (M := CoxeterMatrix.F₄) (e := σ) ⟨f, hf⟩
  have hBs_le : Nat.card Bs ≤ p ^ 4 := by
    have h := hR.card_le_pow_of_weylOfType hTBF hWI
      (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1) (ι' := Fin 4) (M' := CoxeterMatrix.F₄) hW'
    simpa using h
  have hn_eq : n = 4 := by
    refine le_antisymm ?_ hn4
    refine (Nat.pow_le_pow_iff_right hp.one_lt).mp ?_
    calc p ^ n = Nat.card Bs := hBs_card.symm
      _ ≤ p ^ 4 := hBs_le
  have hWcard : Nat.card (ggAutomizerJoin L Bs 𝒦) = 384 := by
    rw [hW_card, hn_eq]
    norm_num
  obtain ⟨y, K, hN, hjoin⟩ := hR.exists_join_eq_of_typeB hTBF hWI e hP hM
  exact ⟨hcardA, hWcard, y, K, hN, hjoin⟩

private theorem card_eq_of_dvd_384_1152 {G : Type} [Group G] [Finite G] {W H : Subgroup G}
    (hW : Nat.card W = 384) (hle : W ≤ H) (hne : H ≠ W)
    (hdvd : Nat.card H ∣ 1152) : Nat.card H = 1152 := by
  have h384 : 384 ∣ Nat.card H := by
    rw [← hW]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨t, ht⟩ := h384
  obtain ⟨u, hu⟩ := hdvd
  have ht_dvd : t ∣ 3 := by
    refine ⟨u, ?_⟩
    have h : 384 * 3 = 384 * (t * u) := by
      calc 384 * 3 = 1152 := by norm_num
        _ = Nat.card H * u := hu
        _ = 384 * t * u := by rw [ht]
        _ = 384 * (t * u) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp ht_dvd with ht1 | ht3
  · exfalso
    apply hne
    have hHcard : Nat.card H = 384 := by rw [ht, ht1, mul_one]
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hHcard, hW]
  · rw [ht, ht3]

private theorem infWitness_of_typeF4_data {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hNbr : GGNbrSet p B x D J 𝒦)
    (hW : GGWeylReflectionGroup p (ggAInf p B Bs x L D J))
    (hcardA : Nat.card (ggAInf p B Bs x L D J) = 1152)
    (hWcard : Nat.card (ggAutomizerJoin L Bs 𝒦) = 384)
    {y0 : G} {K0 : Subgroup G} (hN0 : GGNbr p B x D J y0 K0)
    (hK0 : ggAutomizer L Bs ⊔ ggAutomizer K0 Bs = ggAutomizerJoin L Bs 𝒦)
    {y : G} {K : Subgroup G} (hN : GGNbr p B x D J y K)
    (hKnot : ¬ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    GGSecFiveInfWitness p B Bs x L D J := by
  classical
  let H : Subgroup (MulAut ↥Bs) := ggAutomizerJoin L Bs 𝒦 ⊔ ggAutomizer K Bs
  have hHle : H ≤ ggAInf p B Bs x L D J :=
    sup_le (GGNbrSet.automizerJoin_le_ggAInf hNbr) (ggAutomizer_le_ggAInf_of_nbr hN)
  have hHne : H ≠ ggAutomizerJoin L Bs 𝒦 := by
    intro hEq
    exact hKnot (hEq ▸ (le_sup_right : ggAutomizer K Bs ≤ H))
  have hHdvd : Nat.card H ∣ 1152 := by
    rw [← hcardA]
    exact Subgroup.card_dvd_of_le hHle
  have hHcard : Nat.card H = 1152 :=
    card_eq_of_dvd_384_1152 hWcard le_sup_left hHne hHdvd
  have hH_eq : H = ggAInf p B Bs x L D J :=
    Subgroup.eq_of_le_of_card_ge hHle (by rw [hcardA, hHcard])
  refine ⟨hW, ⟨{K0, K}, ?_, ?_⟩⟩
  · refine ⟨?_, ?_⟩
    · simpa using Finset.card_insert_le K0 ({K} : Finset (Subgroup G))
    · intro K' hK'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hK'
      rcases hK' with rfl | rfl
      · exact ⟨y0, hN0⟩
      · exact ⟨y, hN⟩
  · show ggAutomizerJoin L Bs {K0, K} = ggAInf p B Bs x L D J
    rw [ggAutomizerJoin, Finset.iSup_insert, Finset.iSup_singleton, ← sup_assoc, hK0]
    exact hH_eq

theorem GGSecFiveRouteCfg.infWitness_of_weylInf_B
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixB M)
    (hW : GGWeylReflectionGroup p (ggAInf p B Bs x L D J)) :
    GGSecFiveInfWitness p B Bs x L D J := by
  by_cases hcover : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦
  · have hAInf_le : ggAInf p B Bs x L D J ≤ ggAutomizerJoin L Bs 𝒦 := by
      rw [ggAInf]
      exact sup_le le_sup_left
        (iSup_le fun y => iSup_le fun K => iSup_le fun hN => hcover y K hN)
    have hAeq : ggAInf p B Bs x L D J = ggAutomizerJoin L Bs 𝒦 :=
      le_antisymm hAInf_le (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1)
    exact ⟨hW, ⟨𝒦, hR.2.2.2.1, hAeq.symm⟩⟩
  · push Not at hcover
    obtain ⟨y, K, hN, hKnot⟩ := hcover
    have hW₀ := hW
    obtain ⟨ι', M', hM', f, hf⟩ := hW₀
    rcases hR.weylInf_isWeylMatrixB_or_F4 hTBF hWI e hP (Or.inl hM) hM' f hf with hB | hF
    · exact (false_of_weylInf_typeB hR hTBF hWI e hP hM hB f hf hN hKnot).elim
    · obtain ⟨hcardA, hWcard, y0, K0, hN0, hK0⟩ :=
        typeF4_data hR hTBF hWI e hP hM hF f hf
      exact infWitness_of_typeF4_data hR.2.2.2.1 hW hcardA hWcard hN0 hK0 hN hKnot

theorem ggSecFiveReflMaxAt_B_of_weylInfAt
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hW : GGSecFiveWeylInfAt GGIsWeylMatrixB) : GGSecFiveReflMaxAt GGIsWeylMatrixB := by
  intro G _ _ p B Bs x L D J 𝒦 hR ι M e hP hM
  exact ggRM_of_witness hR.2.2.2
    (hR.infWitness_of_weylInf_B hTBF hWI e hP hM (hW G p B Bs x L D J 𝒦 hR ι M e hP hM))

theorem ggSecFiveRowJoinOffQAt_B_of_reflMaxAt
    (hJ : BMaxJoinInput) (hRM : GGSecFiveReflMaxAt GGIsWeylMatrixB) :
    GGSecFiveRowJoinOffQAt GGIsWeylMatrixB := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ _ ι M e hP hM
  exact hJ G p B Bs x L D J 𝒦 hR ι M e hP hM (hRM G p B Bs x L D J 𝒦 hR ι M e hP hM)

end CFSG.StandardType

end
