module

public import CFSG.Quasithin.Vol2.Ch11SecD557F
public import CFSG.Quasithin.Vol2.Ch11SecD556B
public import CFSG.Quasithin.Vol2.Ch11SecD557E
public import CFSG.Quasithin.Vol2.Ch11SecDFacts6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem pCoreOf_le_pCoreOf_normalizer {V₁ : Subgroup G}
    (St : L3Setting n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)))
    (hTor : TorusFixSL3Fact) (hComm : CommLOneSL3Fact) (h1102 : Stmt11_0_2)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hSL3 : KindSL3 L (fsuV T I) n) {x y : G} (hx : x ∈ L)
    (hy : y ∈ L) (hV : fsuV T I = V₁ ⊔ rconj V₁ x ⊔ rconj V₁ y)
    (hTG₁ : T ≤ Subgroup.normalizer (V₁ : Set G))
    (hH₁ : InH (LOf L V₁ ⊔ T) (Subgroup.normalizer (V₁ : Set G)))
    (hH₁M : ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G))
    (h5one : conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤
      pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) :
    pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ≤
      pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX⟩ := exists_isCartanX h
  have hXL : X ≤ L := hX.1.trans inf_le_left
  have hXodd : Odd (Nat.card X) := hX.2.1
  obtain ⟨-, -, -, -, h6four, h6five, -⟩ :=
    h1156 G T L I n V₁ X _ h hV₁ hX hH₁ hH₁M le_rfl
  have hset := natSetting11_of h1102 h1141 h hV₁
  have hfix := hTor G T L I n X hset hSL3 hX
  have hL₁V := hComm G T L I n V₁ hset hSL3 hV₁
  obtain ⟨-, hSOLT, hST, hInorm, -⟩ := St.sxFacts
  have hS2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))
  have hS₃2 := hS2.to_le (S₃_le _ (tripleU (conjClosure (fsuV T I)
    (Subgroup.normalizer (V₁ : Set G))) x y))
  have hSG₁ := hST.trans hTG₁
  have hXI := hXL.trans (le_sup_left : L ≤ L ⊔ conjClosure (fsuV T I)
    (Subgroup.normalizer (V₁ : Set G)))
  have hXS : X ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ conjClosure (fsuV T I)
      (Subgroup.normalizer (V₁ : Set G))) : Set G) := fun a ha =>
    A4.mem_normalizer_of_conj_mem fun z hz => hInorm a (hXI ha) z hz
  have hXS₃ := hXI.trans (St.G25_four_inv hx hy hV)
  have hCS : pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ⊓
      Subgroup.centralizer (X : Set G) ≤ TripleGrp.S₂ (tripleU (conjClosure (fsuV T I)
        (Subgroup.normalizer (V₁ : Set G))) x y) := fun z hz =>
    mem_S₂_of_forall_conj_eq St hx hy hV hXL hXodd hfix hz.1 fun a ha => by
      rw [Subgroup.mem_centralizer_iff.mp hz.2 a ha, mul_inv_cancel_right]
  have hb := (le_commutator_sup_centralizer hXS (isSolvable_of_isPGroup_two hS2)
    (coprime_card_of_odd hXodd hS2)).trans (sup_le_sup_left hCS _)
  have hb₃ := (le_commutator_sup_centralizer hXS₃ (isSolvable_of_isPGroup_two hS₃2)
    (coprime_card_of_odd hXodd hS₃2)).trans
    (sup_le_sup_left ((inf_le_inf_right _ (S₃_le _ _)).trans hCS) _)
  have hS₂U : TripleGrp.S₂ (tripleU (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))
      x y) ≤ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) :=
    (inf_le_left.trans inf_le_left).trans (tripleU_zero _ x y).le
  have hKG₁ : KOf L V₁ V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    kOf_le_normalizer (lOf_le_normalizer L V₁)
  have hG₁K := normalizer_le_normalizer_kOf L V₁ V₁
  have hYG₁ : Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) ≤
        Subgroup.normalizer (V₁ : Set G) :=
    inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
  have hG₁Y := normalizer_le_normalizer_Y L V₁
  have hSK : pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ≤
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) :=
    hb.trans (sup_le (((Subgroup.commutator_mono hSOLT le_rfl).trans h6five).trans
      (pCoreOf_le_sectionCentralizer_of_le le_sup_left
        (sup_le Subgroup.le_normalizer (hTG₁.trans hG₁K))))
      (hS₂U.trans (h5one.trans (pCoreOf_le_sectionCentralizer_of_le hKG₁ hG₁K))))
  have hYsc := pCoreOf_le_sectionCentralizer_of_le hYG₁ hG₁Y
  have hKY := le_sectionCentralizer_of_le hKG₁ hYG₁ hG₁K hG₁Y inf_le_right
  have hL₁Y := (le_conjClosure (LOf L V₁) (Subgroup.normalizer (V₁ : Set G))).trans hKY
  have hPS₃ := (Subgroup.le_normalizer_iff_commutator_le_left).mp hXS₃
  have hPsc : ⁅TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure (fsuV T I)
      (Subgroup.normalizer (V₁ : Set G)))) (tripleU (conjClosure (fsuV T I)
        (Subgroup.normalizer (V₁ : Set G))) x y), X⁆ ≤
      sectionCentralizer (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))
        (pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) := by
    have hPT := hPS₃.trans ((S₃_le _ _).trans hST)
    have hPY := h6four _ (commutator_commutator_eq hXS₃ (coprime_card_of_odd hXodd hS₃2)).symm
      hPT ((frattini_le_S₂ St hx hy hV hPS₃).trans (hS₂U.trans h5one))
    intro p hp
    have hpN := hG₁Y (hTG₁ (hPT hp))
    exact ⟨hpN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hpN,
      fun w hw => hPY (Subgroup.commutator_mem_commutator hp hw)⟩
  have hSL₁ := le_commutator_sup_S₃ St hx hy hV ((perfectCore_le _).trans inf_le_left) hL₁V
  have hcommL₁ : ⁅pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))),
      LOf L V₁⁆ ≤ sectionCentralizer (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))
        (pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) := by
    rw [Subgroup.commutator_le]
    intro s hs l hl
    have hsN := hG₁Y (hSG₁ hs)
    have h1 := conj_mem_sectionCentralizer hsN
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hsN) (hL₁Y hl)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hL₁Y hl))
  have hSY := hSL₁.trans (sup_le hcommL₁ (hb₃.trans (sup_le hPsc (hS₂U.trans
    (h5one.trans hYsc)))))
  obtain ⟨z₀, hz₀V₁, hz₀1, hz₀T⟩ := exists_z h hV₁
  have hdec := (h1143 G T L I n V₁ h hV₁ z₀ ⟨SecA.IsVi.le_fsuV hV₁ hz₀V₁, hz₀T⟩ hz₀1).2.2
  rw [inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)] at hdec
  have hMS : Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (L ⊔ conjClosure (fsuV T I)
        (Subgroup.normalizer (V₁ : Set G))) : Set G) := fun m hm =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (mem_normalizer_sup' hm.1 (le_normalizer_conjClosure _ _ hm.2))
  exact le_pCoreOf_of_mul hdec hKG₁ hYG₁ inf_le_right hSG₁ hG₁K hG₁Y hS2 hSK hSY hMS

end CFSG.Quasithin.Vol2.Ch11.SecD
