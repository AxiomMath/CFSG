module

public import CFSG.Quasithin.Background.C124YZOff
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C124YZClass

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G]

theorem jr_facts {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
    (E : Entry X T V L R m hV) {N : ℕ} {Q : Type} [Group Q] [Finite Q]
    {act : Perm (Fin m) →* MulAut Q} (MF : ModelFacts m Q act N)
    (hN : Nat.card ↥(autI hV R) ≤ N)
    (ι : ↥(autI hV X) →* Perm (Fin m)) (hι : Function.Injective ι)
    (β : ↥(commV (autI hV L)) →* Q) (hβs : Function.Surjective β)
    (hβe : ∀ (g : ↥(autI hV X)) (u : ↥(commV (autI hV L)))
      (hu : (g : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV L)),
      β ⟨(g : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ = act (ι g) (β u)) :
    IsSwapGroup (Bmap ι (autI hV (thompsonJ R))) ∧
      IsPGroup 2 ↥(Bmap ι (autI hV (thompsonJ R))) ∧
      Nat.card ↥(Bmap ι (autI hV (thompsonJ R))) ≤ N ∧
      ∀ u : ↥(commV (autI hV L)), β u ∈ fixAct act (Bmap ι (autI hV (thompsonJ R))) →
        (u : IntMod V hV) ∈ fixV (autI hV (thompsonJ R)) := by
  classical
  have hVX : V ≤ X := E.red.1
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := E.red.2.1
  have hLX : L ≤ X := le_of_mem_cComp E.comp
  have hRX : R ≤ X := E.RT.trans E.sylow.1
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hXN
  have hVR : V ≤ R := (le_pCoreOf_of_reduced E.red).trans E.QR
  have hRp : IsPGroup 2 R := E.sylow.2.1.to_le E.RT
  have hLsXs : autI hV L ≤ autI hV X := autI_mono hV hLX
  have hXsN := autI_normalizes hV E.normal
  have hUinv : ∀ g ∈ autI hV X, ∀ u ∈ commV (autI hV L), g u ∈ commV (autI hV L) :=
    fun g hg u hu => apply_mem_commV (hXsN hg) hu
  have hAn : ∀ A : Subgroup G, IsMaxElemAbelian R A → autI hV A ≤ autI hV R :=
    fun A hA => autI_mono hV hA.1
  have hAX : ∀ A : Subgroup G, IsMaxElemAbelian R A → autI hV A ≤ autI hV X :=
    fun A hA => (hAn A hA).trans (autI_mono hV hRX)
  have hfixiff : ∀ A : Subgroup G, IsMaxElemAbelian R A → ∀ u : ↥(commV (autI hV L)),
      (u : IntMod V hV) ∈ fixV (autI hV A) ↔ β u ∈ fixAct act (Bmap ι (autI hV A)) := by
    intro A hA u
    by_cases hbot : autI hV A = ⊥
    · rw [hbot, Bmap_bot]
      constructor
      · intro _ b hb
        rw [Subgroup.mem_bot.1 hb, map_one]
        rfl
      · intro _ x hx
        rw [Subgroup.mem_bot.1 hx]
        rfl
    · have hnc : ¬ A ≤ Subgroup.centralizer (V : Set G) := fun h =>
        hbot (autI_eq_bot_of_le_centralizer hV h)
      have hmem : autI hV A ∈ offenderImages hV R := ⟨A, ⟨hA, hnc⟩, rfl⟩
      have hoffs := offenderImages_isFFStarOffender hV hVR hRN hmem
      have hW : Nat.card (IntMod V hV) ≤ Nat.card (autI hV A) * Nat.card (fixV (autI hV A)) := by
        have := hoffs.card_le (bot_le : (⊥ : Subgroup (MulAut (IntMod V hV))) ≤ autI hV A)
        rwa [B1.card_bot_mul_card_fixV] at this
      have hoff := card_le_card_mul_inf (commV (autI hV L)) (autI hV A) hW
      obtain ⟨hsq, hcomm⟩ := Bmap_elemAbelian (ι := ι) hoffs.2.2.1
      have hcard : Nat.card (Bmap ι (autI hV A)) = Nat.card (autI hV A) :=
        card_Bmap ι hι (hAX A hA)
      have hge := MF.index_ge (Bmap ι (autI hV A)) hsq hcomm
        (by rw [hcard]; exact (Subgroup.card_le_of_le (hAn A hA)).trans hN)
      rw [hcard] at hge
      exact mem_fixV_iff_of_offender hUinv hβs hβe hoff hge u
  set Dx := autI hV (thompsonJ R) with hDx
  set D' := Bmap ι Dx with hD'
  let AF : {A : Subgroup G // IsMaxElemAbelian R A} → Subgroup (MulAut (IntMod V hV)) :=
    fun A => autI hV A.1
  have hAF : ∀ A, AF A ≤ autI hV X := fun A => hAX A.1 A.2
  have hDxeq : Dx = ⨆ A, AF A := by
    have h := autI_iSup₂ hV (P := IsMaxElemAbelian R) (fun A hA => hA.1.trans hRN)
    rw [hDx]
    show autI hV (⨆ (A : Subgroup G) (_ : IsMaxElemAbelian R A), A) = _
    rw [h]
    exact iSup_subtype'
  have hD'eq : D' = ⨆ A, Bmap ι (AF A) := by
    rw [hD', hDxeq]
    exact Bmap_iSup ι AF hAF
  have hDxR : Dx ≤ autI hV R := autI_mono hV (thompsonJ_le R)
  have hcardD : Nat.card D' ≤ N := by
    rw [hD', card_Bmap ι hι (hDxR.trans (autI_mono hV hRX))]
    exact (Subgroup.card_le_of_le hDxR).trans hN
  have hBsw : ∀ A : {A : Subgroup G // IsMaxElemAbelian R A}, IsSwapGroup (Bmap ι (AF A)) := by
    intro A
    by_cases hbot : autI hV A.1 = ⊥
    · have : Bmap ι (AF A) = ⊥ := by
        show Bmap ι (autI hV A.1) = ⊥
        rw [hbot]
        exact Bmap_bot ι
      rw [this]
      intro d hd x
      rw [Subgroup.mem_bot.1 hd]
      exact Or.inl rfl
    · have hnc : ¬ A.1 ≤ Subgroup.centralizer (V : Set G) := fun h =>
        hbot (autI_eq_bot_of_le_centralizer hV h)
      have hmem : autI hV A.1 ∈ offenderImages hV R := ⟨A.1, ⟨A.2, hnc⟩, rfl⟩
      have hoffs := offenderImages_isFFStarOffender hV hVR hRN hmem
      have hW : Nat.card (IntMod V hV) ≤
          Nat.card (autI hV A.1) * Nat.card (fixV (autI hV A.1)) := by
        have := hoffs.card_le (bot_le : (⊥ : Subgroup (MulAut (IntMod V hV))) ≤ autI hV A.1)
        rwa [B1.card_bot_mul_card_fixV] at this
      have hoff := card_le_card_mul_inf (commV (autI hV L)) (autI hV A.1) hW
      obtain ⟨hsq, hcomm⟩ := Bmap_elemAbelian (ι := ι) hoffs.2.2.1
      have hcard : Nat.card (Bmap ι (autI hV A.1)) = Nat.card (autI hV A.1) :=
        card_Bmap ι hι (hAX A.1 A.2)
      have hidx := index_fixAct_le (ι := ι) hUinv hβs hβe hoff
      have hne : Bmap ι (autI hV A.1) ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hcard
        exact hbot (Subgroup.card_eq_one.1 hcard.symm)
      exact MF.isSwapGroup (Bmap ι (autI hV A.1)) hsq hcomm hne
        (by rw [hcard]; exact (Subgroup.card_le_of_le (hAn A.1 A.2)).trans hN)
        (by rw [hcard]; exact hidx)
  have hpD' : IsPGroup 2 ↥D' := Bmap_isPGroup hDxR (isPGroup_autI hV hRp)
  have hSG : IsSwapGroup D' := by
    rw [hD'eq]
    exact isSwapGroup_iSup _ hBsw (by rw [← hD'eq]; exact hpD')
  have hfixD : ∀ u : ↥(commV (autI hV L)), β u ∈ fixAct act D' →
      (u : IntMod V hV) ∈ fixV Dx := by
    intro u hu
    rw [hDxeq]
    refine mem_fixV_iSup AF fun A => ?_
    refine (hfixiff A.1 A.2 u).2 (fixAct_anti ?_ hu)
    rw [hD'eq]
    exact le_iSup (fun A => Bmap ι (AF A)) A
  exact ⟨hSG, hpD', hcardD, hfixD⟩

end CFSG.Quasithin.C124.YZ
