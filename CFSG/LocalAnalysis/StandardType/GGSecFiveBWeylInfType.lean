module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylInfDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem GGCoxeterPres.exists_refl_mul_orderOf_eq {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    (hP : GGCoxeterPres p A M e) (i j : ι) :
    ∃ r ∈ A, ∃ s ∈ A, GGIsReflection p r ∧ GGIsReflection p s ∧ orderOf (r * s) = M.M i j := by
  let r : MulAut ↥Bs := ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  let s : MulAut ↥Bs := ((e (M.simple j) : ↥A) : MulAut ↥Bs)
  refine ⟨r, (e (M.simple i)).2, s, (e (M.simple j)).2, hP.2 i, hP.2 j, ?_⟩
  have hord : orderOf (M.simple i * M.simple j) = M.M i j := by
    have h := (CoxeterMatrix.toCoxeterSystem (M := M)).orderOf_simple_mul_simple i j
    rwa [CoxeterMatrix.toCoxeterSystem_simple] at h
  have hkey : r * s = ((e (M.simple i * M.simple j) : ↥A) : MulAut ↥Bs) := by
    simp only [r, s, ← Subgroup.coe_mul, ← map_mul]
  rw [hkey, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact hord

omit [Finite G] in
theorem GGCoxeterPres.exists_refl_mul_orderOf_eq_four {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    (hP : GGCoxeterPres p A M e) (hM : GGIsWeylMatrixB M ∨ GGIsWeylMatrixF4 M) :
    ∃ r ∈ A, ∃ s ∈ A, GGIsReflection p r ∧ GGIsReflection p s ∧ orderOf (r * s) = 4 := by
  rcases hM with ⟨n, e', hn, rfl⟩ | ⟨σ, rfl⟩
  · let i : ι := e' ⟨n - 2, by omega⟩
    let j : ι := e' ⟨n - 1, by omega⟩
    obtain ⟨r, hrA, s, hsA, hrr, hsr, hord⟩ := hP.exists_refl_mul_orderOf_eq i j
    refine ⟨r, hrA, s, hsA, hrr, hsr, ?_⟩
    have hB4 : (CoxeterMatrix.B n).M ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = 4 := by
      simp [CoxeterMatrix.B, Fin.ext_iff]
      omega
    have hM4 : ((CoxeterMatrix.B n).reindex e').M i j = 4 := by
      rw [CoxeterMatrix.reindex_apply]
      simpa [i, j] using hB4
    rw [hord, hM4]
  · let i : ι := σ 1
    let j : ι := σ 2
    obtain ⟨r, hrA, s, hsA, hrr, hsr, hord⟩ := hP.exists_refl_mul_orderOf_eq i j
    refine ⟨r, hrA, s, hsA, hrr, hsr, ?_⟩
    have hF4 : (CoxeterMatrix.F₄).M 1 2 = 4 := by
      simp [CoxeterMatrix.F₄, Matrix.of_apply, Matrix.cons_val']
    have hM4 : ((CoxeterMatrix.F₄).reindex σ).M i j = 4 := by
      rw [CoxeterMatrix.reindex_apply]
      simpa [i, j] using hF4
    rw [hord, hM4]

theorem refl_mul_pow_eq_one_of_le_three {Bs : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)}
    (hA : (A : Set (MulAut ↥Bs)) ⊆ ggInduced ⊤ Bs) {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (f : M.Group ≃* ↥A)
    (hf : ∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)) {r s : MulAut ↥Bs}
    (hr : r ∈ A) (hs : s ∈ A) (hrr : GGIsReflection p r) (hsr : GGIsReflection p s) :
    (r * s) ^ 2 = 1 ∨ (r * s) ^ 3 = 1 := by
  have hG2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨en, rfl⟩
    have hne : en 0 ≠ en 1 := by
      intro hh
      have hv := congrArg Fin.val (en.injective hh)
      norm_num at hv
    have hlab := hle3 (en 0) (en 1) hne
    have h6 : (CoxeterMatrix.G₂.reindex en).M (en 0) (en 1) = 6 := by
      rw [CoxeterMatrix.reindex_apply]
      simp [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']
    rw [h6] at hlab
    omega
  obtain ⟨i, g, hag⟩ :=
    SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hBs hNT A hA ι M hM hG2 f hf
      ⟨r, hr⟩ hrr
  obtain ⟨j, h, hbs⟩ :=
    SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hBs hNT A hA ι M hM hG2 f hf
      ⟨s, hs⟩ hsr
  exact ggCoxRefl_mul_orderOf_le_three hM hle3 ⟨g, i, congrArg Subtype.val hag⟩
    ⟨h, j, congrArg Subtype.val hbs⟩

variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

private theorem ggCoxeterMatrixA_M_le_three (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (CoxeterMatrix.A n).M i j ≤ 3 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij]
  split_ifs <;> omega

theorem GGSecFiveRouteCfg.exists_card_eq_of_typeB (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixB M) :
    ∃ n : ℕ, 4 ≤ n ∧ Nat.card Bs = p ^ n ∧
      Nat.card (ggAutomizerJoin L Bs 𝒦) = 2 ^ n * n.factorial := by
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨n, e', hn, rfl⟩ := hM
  let E : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦) :=
    ((CoxeterMatrix.B n).reindexGroupEquiv e').symm.trans e
  have hP' : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) E :=
    GGCoxeterPres.of_reindex_B (A := ggAutomizerJoin L Bs 𝒦) hn hP
  obtain ⟨h4, eta, -⟩ := hR.exists_bSignedFull_coords hTBF hWI hn E hP'
  refine ⟨n, h4, ?_, ?_⟩
  · calc Nat.card Bs = Nat.card (Fin n → Multiplicative (ZMod p)) := Nat.card_congr eta.toEquiv
      _ = p ^ n := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun]
        simp [ZMod.card]
  · calc Nat.card (ggAutomizerJoin L Bs 𝒦) =
        Nat.card ((CoxeterMatrix.B n).reindex e').Group := (Nat.card_congr e.toEquiv).symm
      _ = Nat.card (CoxeterMatrix.B n).Group :=
        Nat.card_congr ((CoxeterMatrix.B n).reindexGroupEquiv e').toEquiv
      _ = 2 ^ n * n.factorial := ggCoxeterB_card n hn

theorem GGSecFiveRouteCfg.exists_nbr_sup_le (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  by_cases h : 𝒦.card ≤ 1
  · obtain ⟨y, K, hN, hEq⟩ := hR.exists_join_eq_of_card_le_one h
    exact ⟨y, K, hN, hEq.le⟩
  · push Not at h
    obtain ⟨K, hK⟩ := Finset.card_pos.mp (by omega : 0 < 𝒦.card)
    obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
    exact ⟨y, K, hN, sup_le (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
      (ggAutomizer_le_ggAutomizerJoin (Or.inr hK))⟩

theorem GGSecFiveRouteCfg.eq_one_of_forall_join_fix (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (b : ↥Bs)
    (hb : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ b = b) : b = 1 := by
  obtain ⟨y, K, hN, hsup⟩ := hR.exists_nbr_sup_le
  exact GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hR.1 hR.2.1 hN b
    fun φ hφ => hb φ (hsup hφ)

theorem GGSecFiveRouteCfg.card_le_pow_of_weylOfType
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {A : Subgroup (MulAut ↥Bs)} (hA : ggAutomizerJoin L Bs 𝒦 ≤ A)
    {ι' : Type} [Fintype ι'] {M' : CoxeterMatrix ι'}
    (hW' : GGWeylOfType p M' A) : Nat.card Bs ≤ p ^ Fintype.card ι' := by
  exact SpJoinRefl.card_le_pow_of_weylOfType hW' fun b hb =>
    hR.eq_one_of_forall_join_fix hTBF hWI b fun φ hφ => hb φ (hA hφ)

private theorem not_refl_mul_order_four (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hM : GGIsWeylMatrixB M ∨ GGIsWeylMatrixF4 M)
    {ι' : Type} {M' : CoxeterMatrix ι'} (hM' : GGIsWeylMatrix M')
    (hle3 : ∀ i j : ι', i ≠ j → M'.M i j ≤ 3)
    (f : M'.Group ≃* ↥(ggAInf p B Bs x L D J))
    (hf : ∀ i : ι', GGIsReflection p ((f (M'.simple i) : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs)) :
    False := by
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨r, hrA, s, hsA, hrr, hsr, hord⟩ := hP.exists_refl_mul_orderOf_eq_four hM
  have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J :=
    GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1
  have h := refl_mul_pow_eq_one_of_le_three hp hp2 hBs hR.1.2.2.2.1
    (A := ggAInf p B Bs x L D J) ggRM_ainf_le_induced hM' hle3 f hf (hle hrA) (hle hsA) hrr hsr
  rcases h with h2 | h3
  · have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hdvd
    omega
  · have hdvd := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at hdvd
    omega

private theorem weylInf_classical (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hM : GGIsWeylMatrixB M ∨ GGIsWeylMatrixF4 M)
    {ι' : Type} {M' : CoxeterMatrix ι'} (hM' : GGIsWeylMatrix M')
    (hcase : ∃ (n : ℕ) (e' : Fin n ≃ ι'), 1 ≤ n ∧
      (M' = (CoxeterMatrix.A n).reindex e' ∨
        (2 ≤ n ∧ M' = (CoxeterMatrix.B n).reindex e') ∨
        (4 ≤ n ∧ M' = (ggCoxeterMatrixD n).reindex e')))
    (f : M'.Group ≃* ↥(ggAInf p B Bs x L D J))
    (hf : ∀ i : ι', GGIsReflection p ((f (M'.simple i) : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs)) :
    GGIsWeylMatrixB M' ∨ GGIsWeylMatrixF4 M' := by
  obtain ⟨n, e', _, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ := hcase
  · exfalso
    have hle3 : ∀ i j : ι', i ≠ j → M'.M i j ≤ 3 := by
      intro i j hij
      rw [hA, CoxeterMatrix.reindex_apply]
      exact ggCoxeterMatrixA_M_le_three n (e'.symm i) (e'.symm j)
        fun h => hij (e'.symm.injective h)
    exact not_refl_mul_order_four hR e hP hM hM' hle3 f hf
  · left
    exact ⟨n, e', hn2, hB⟩
  · exfalso
    have hle3 : ∀ i j : ι', i ≠ j → M'.M i j ≤ 3 :=
      GGIsWeylMatrixAD.le_three (Or.inr ⟨n, e', hn4, hD⟩)
    exact not_refl_mul_order_four hR e hP hM hM' hle3 f hf

private theorem not_g2_of_weylInf (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {ι' : Type} {M' : CoxeterMatrix ι'} {eG2 : Fin 2 ≃ ι'}
    (f : M'.Group ≃* ↥(ggAInf p B Bs x L D J))
    (hf : ∀ i : ι', GGIsReflection p ((f (M'.simple i) : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs))
    (hG2 : M' = CoxeterMatrix.G₂.reindex eG2) : False := by
  obtain ⟨hp, -, -, -, h4⟩ := hR.1.1.tableB_facts
  have hW2 : GGWeylOfType p CoxeterMatrix.G₂ (ggAInf p B Bs x L D J) := by
    have hW : GGWeylOfType p M' (ggAInf p B Bs x L D J) := ⟨f, hf⟩
    rw [hG2] at hW
    exact GGWeylOfType.of_reindex (e := eG2) hW
  have hle2 : Nat.card Bs ≤ p ^ 2 := by
    simpa using hR.card_le_pow_of_weylOfType hTBF hWI
      (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1) hW2
  have h42 : 4 ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h4.trans hle2)
  omega

theorem GGSecFiveRouteCfg.weylInf_isWeylMatrixB_or_F4 (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hM : GGIsWeylMatrixB M ∨ GGIsWeylMatrixF4 M)
    {ι' : Type} {M' : CoxeterMatrix ι'} (hM' : GGIsWeylMatrix M')
    (f : M'.Group ≃* ↥(ggAInf p B Bs x L D J))
    (hf : ∀ i : ι', GGIsReflection p ((f (M'.simple i) : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs)) :
    GGIsWeylMatrixB M' ∨ GGIsWeylMatrixF4 M' := by
  have hM0 : GGIsWeylMatrix M' := hM'
  have hE : GGIsWeylMatrixE M' → False := fun h =>
    not_refl_mul_order_four hR e hP hM hM0 h.le_three f hf
  rcases hM' with hclassical | h6 | h7 | h8 | hF4 | ⟨eG2, hG2⟩
  · exact weylInf_classical hR e hP hM hM0 hclassical f hf
  · exact (hE (Or.inl h6)).elim
  · exact (hE (Or.inr (Or.inl h7))).elim
  · exact (hE (Or.inr (Or.inr h8))).elim
  · exact Or.inr hF4
  · exact (not_g2_of_weylInf hR hTBF hWI f hf hG2).elim

end CFSG.StandardType

end
