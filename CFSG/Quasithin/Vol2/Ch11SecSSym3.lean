module

public import CFSG.Quasithin.Vol2.Ch1Nine
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSK0b
public import CFSG.Quasithin.Vol2.Ch11SecSXCard
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem lOf_ne (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) : LOf L V₁ ≠ LOf L V₂ := by
  intro heq
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan
  have hcard := card_cartan cL hXN
    (cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
  have hle : X ≤ X ⊓ LOf L V₁ := by
    have := cL.b
    rwa [← heq, sup_idem] at this
  have := Subgroup.card_le_of_le hle
  rw [hcard, cL.card₁] at this
  omega

theorem le_sup_lOf (hPG : FactParabGen) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X) :
    L ≤ LOf L V₁ ⊔ LOf L V₂ ⊔ pCoreOf 2 L := by
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hSL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer h.hyp.normal)
  have hOL : pCoreOf 2 L ≤ T := (pCoreOf_two_le_of_isSylowTwoOf hSL).trans inf_le_left
  have hQs := isSolvable_pCoreOf_two L
  have hp₁ : ⁅LOf L V₁, LOf L V₁⁆ = LOf L V₁ := perfectCore_perfect _
  have hp₂ : ⁅LOf L V₂, LOf L V₂⁆ = LOf L V₂ := perfectCore_perfect _
  have hne₁ : LOf L V₁ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₁ (Or.inl rfl) le_rfl)
  have hne₂ : LOf L V₂ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₂ (Or.inr rfl) le_rfl)
  have hSL₁ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(modO2Image L (LOf L V₁)) ⧸ CFSG.pCore 2 ↥(modO2Image L (LOf L V₁)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h.hyp (Or.inl rfl) h.v₁
    obtain ⟨e₁⟩ := modO2Image_quotEquiv hL₁L
    exact ⟨F, inferInstance, inferInstance, hF.trans (by norm_num), ⟨e₁.symm.trans e⟩⟩
  have hSL₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(modO2Image L (LOf L V₂)) ⧸ CFSG.pCore 2 ↥(modO2Image L (LOf L V₂)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h.hyp (Or.inr rfl) h.v₂
    obtain ⟨e₁⟩ := modO2Image_quotEquiv hL₂L
    exact ⟨F, inferInstance, inferInstance, hF.trans (by norm_num), ⟨e₁.symm.trans e⟩⟩
  have hne : modO2Image L (LOf L V₁) ≠ modO2Image L (LOf L V₂) := by
    intro heq
    apply h.lOf_ne hN h1102 cL
    have h1 := sup_eq_of_modO2Image_eq hL₁L hL₂L heq
    rw [← perfectCore_sup_eq hp₁ hQs (hOL.trans h.T_le_normalizer_L₁), h1,
      perfectCore_sup_eq hp₂ hQs (hOL.trans h.T_le_normalizer_L₂)]
  have hgen := hPG _ h.hyp.shape _ (isSylowTwoOf_modO2Image hSL) _ _ hne
    (modO2Image_ne_bot hL₁L hp₁ hne₁) (modO2Image_ne_bot hL₂L hp₂ hne₂)
    (modO2Image_perfect hL₁L hp₁) (modO2Image_perfect hL₂L hp₂)
    (modO2Image_le_normalizer (inf_le_left.trans h.T_le_normalizer_L₁))
    (modO2Image_le_normalizer (inf_le_left.trans h.T_le_normalizer_L₂)) hSL₁ hSL₂
  exact le_sup_of_modO2Image_eq_top (sup_le hL₁L hL₂L) (by rw [modO2Image_sup hL₁L hL₂L, hgen])

theorem not_le_normalizer_of_isLocal (hPG : FactParabGen) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X) {J : Subgroup G}
    (hJ : quasithinIsLocal T J) (hTJ : T ≤ Subgroup.normalizer (J : Set G))
    (hL₂J : LOf L V₂ ≤ J) : ¬ K ≤ Subgroup.normalizer (J : Set G) := by
  intro hKJ
  have hSL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer h.hyp.normal)
  have hOL : pCoreOf 2 L ≤ T := (pCoreOf_two_le_of_isSylowTwoOf hSL).trans inf_le_left
  have hLJ : L ≤ Subgroup.normalizer (J : Set G) :=
    (h.le_sup_lOf hPG hN h1102 cL).trans (sup_le (sup_le (h.L₁_le_K.trans hKJ)
      (hL₂J.trans Subgroup.le_normalizer)) (hOL.trans hTJ))
  have hO : pCoreOf 2 J ≠ ⊥ := pCoreOf_ne_bot_of_charTwo
    (charTwo_of_isLocal h.hyp.fsu.qtke h.sylow hJ) hJ.2.1.1
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 J : Set G)) :=
    ⟨pCoreOf 2 J, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hNJ : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    fun _ hx => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hx
  have hU := lemma_1_2_7_three h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian h37 h38 h39
    h.sylow h.hyp.fsu.maximal
  have hcc : conjClosure L T = L :=
    le_antisymm
      (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (h.hyp.normal ht) l).1 hl)
      (le_conjClosure L T)
  rw [hcc] at hU
  have hM := hU.2 M' ⟨hM', (sup_le hLJ hTJ).trans (hNJ.trans hle)⟩
  apply h.not_le
  rw [← hM]
  exact hKJ.trans (hNJ.trans hle)

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
