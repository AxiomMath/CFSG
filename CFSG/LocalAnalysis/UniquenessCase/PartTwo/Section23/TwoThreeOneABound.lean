module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneStatement
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundImage
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGF2Rep417
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Fb45b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20za

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem le_centralizer_barSub_of_k417 (hK : K_GF2Rep417) {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hS1 : S ≠ ⊥) (hW : IsElemAbelian 2 (conjClosure c.L0 S)) {K : Subgroup G}
    (hKsub : CFSG.Open.IsSubnormal K (c.L0 ⊔ D.T)) (hKq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hKO : barSub ⊥ (conjClosure c.L0 S) hW (CFSG.Open.pCoreOf 2 K) = ⊥)
    (hgen : barSub ⊥ (conjClosure c.L0 S) hW K ⊔ barSub ⊥ (conjClosure c.L0 S) hW D.T =
      barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T))
    {n : ℕ} (hshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n ∨ IsSU3 (Bar2 K) n ∨
      ((IsSL3 (Bar2 K) n ∨ IsSp4 (Bar2 K) n) ∧ ∃ t ∈ D.T, ActsNontrivOnDiagram K t)) :
    ∀ A ∈ E3.aSet (n + 1) (barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T)),
      A ≤ Subgroup.centralizer (barSub ⊥ (conjClosure c.L0 S) hW K :
        Set (MulAut (Vtil (⊥ : Subgroup G) (conjClosure c.L0 S) hW))) := by
  intro A hA
  have hstab := sup_le_stabTil_conjClosure c hSZ
  have hKstab : K ≤ stabTil ⊥ (conjClosure c.L0 S) :=
    (CFSG.Quasithin.A3.subnormal_le hKsub).trans hstab
  have hTstab : D.T ≤ stabTil ⊥ (conjClosure c.L0 S) := le_sup_right.trans hstab
  by_cases hK1 : barSub ⊥ (conjClosure c.L0 S) hW K = ⊥
  · rw [hK1]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hb
    rw [hb, one_mul, mul_one]
  · exact hK (Vtil (⊥ : Subgroup G) (conjClosure c.L0 S) hW)
      (fun w => by rw [pow_two]; exact s16c1_vTil_mul_self hW w) _ _ _ n
      (isSylowIn_barSub_T c hSZ hW)
      (isComponentOf_barSub_of_isSubnormal hW hKstab hKO hK1 hKsub hKq)
      (pCore_barSub_eq_bot_of_quasisimple hW hKstab hKO hK1 hKq)
      (pCore_barSub_sup_eq_bot c hSZ hW) hgen
      (shape417_barSub hW hKstab hKO hK1 hKq hTstab hshape)
      (fixV_barSub_T_ne_fixV_barSub_sup c hSZ hS1 hW) A hA

theorem barSub_sup_eq_of_conj {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S)) {L₁ L₂ : Subgroup G} (hL : c.L0 = L₁ ⊔ L₂)
    {t : G} (htT : t ∈ D.T) (hL₂ : L₂ = L₁.map (MulAut.conj t).toMonoidHom) :
    barSub ⊥ (conjClosure c.L0 S) hW L₁ ⊔ barSub ⊥ (conjClosure c.L0 S) hW D.T =
      barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T) := by
  have hstab := sup_le_stabTil_conjClosure c hSZ
  have hL₁L0 : L₁ ≤ c.L0 := (le_sup_left : L₁ ≤ L₁ ⊔ L₂).trans hL.symm.le
  have hL₂L0 : L₂ ≤ c.L0 := (le_sup_right : L₂ ≤ L₁ ⊔ L₂).trans hL.symm.le
  have hL₁s : L₁ ≤ stabTil ⊥ (conjClosure c.L0 S) := (hL₁L0.trans le_sup_left).trans hstab
  have hL₂s : L₂ ≤ stabTil ⊥ (conjClosure c.L0 S) := (hL₂L0.trans le_sup_left).trans hstab
  have hTs : D.T ≤ stabTil ⊥ (conjClosure c.L0 S) := le_sup_right.trans hstab
  have hts : t ∈ stabTil ⊥ (conjClosure c.L0 S) := hTs htT
  set Y := barSub ⊥ (conjClosure c.L0 S) hW L₁ ⊔ barSub ⊥ (conjClosure c.L0 S) hW D.T
  have h₁Y : barSub ⊥ (conjClosure c.L0 S) hW L₁ ≤ Y := le_sup_left
  have hTY : barSub ⊥ (conjClosure c.L0 S) hW D.T ≤ Y := le_sup_right
  have htY : actTil ⊥ (conjClosure c.L0 S) hW ⟨t, hts⟩ ∈ Y :=
    hTY (actTil_mem_barSub ⊥ _ hW htT hts)
  have h₂Y : barSub ⊥ (conjClosure c.L0 S) hW L₂ ≤ Y := by
    rw [hL₂, TwelveTwentyThree.barSub_map_conj hW hL₁s hts]
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Y.mul_mem (Y.mul_mem htY (h₁Y hx)) (Y.inv_mem htY)
  apply le_antisymm
  · exact sup_le (barSub_mono ⊥ _ hW (hL₁L0.trans le_sup_left)) (barSub_mono ⊥ _ hW le_sup_right)
  · have hsup : c.L0 ⊔ D.T = L₁ ⊔ L₂ ⊔ D.T := by rw [← hL]
    rw [hsup, barSub_sup hW (sup_le hL₁s hL₂s) hTs, barSub_sup hW hL₁s hL₂s]
    exact sup_le (sup_le h₁Y h₂Y) hTY

end Ctx23L

theorem s23_1ABound_of (hK : K_GF2Rep417) {D : Data G} {Ch : Choice2011 G} (h2010 : S20_10 D) :
    S23_1ABound D Ch := by
  intro h1930 c V _hVc hVN hV1 hW
  have hSZ : V ⊓ D.Z ≤ D.Z := inf_le_right
  have hS1 : V ⊓ D.Z ≠ ⊥ := Ctx23L.inf_Z_ne_bot_of_eq_conjClosure c hVN hV1
  have hL0 : c.L0 ∈ calL D.T D.M := c.hL0.1
  have hstab := Ctx23L.sup_le_stabTil_conjClosure c hSZ
  have hTN : D.T ≤ Subgroup.normalizer (c.L0 : Set G) := hL0.1
  have hL0sub : CFSG.Open.IsSubnormal c.L0 (c.L0 ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hTN))
  have hO2L0 := Ctx23L.barSub_pCoreOf_L0_eq_bot c hSZ hW
  refine Ctx23L.aBar_le_of_forall_mem_aSet_le_centralizer c hSZ hW c.n ?_
  rcases shape417_of D hL0 (s20_10Shape_of h2010 h1930 c.hL0) c.hn with
    hsingle | ⟨L₁, L₂, h₁, h₂, hL, -, ⟨t, htT, hL₂⟩, hsh⟩
  ·
    have hq : CFSG.Open.IsQuasisimple (Bar2 c.L0) := by
      refine uc22pw_isQuasisimple_of_single D hL0 (n := c.n) ?_
      rcases hsingle with h | h | h | ⟨h | h, -⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    exact Ctx23L.le_centralizer_barSub_of_k417 c hK hSZ hS1 hW hL0sub hq hO2L0
      (barSub_sup hW (le_sup_left.trans hstab) (le_sup_right.trans hstab)).symm hsingle
  ·
    have htT' : t⁻¹ ∈ D.T := D.T.inv_mem htT
    have hL₁ : L₁ = L₂.map (MulAut.conj t⁻¹).toMonoidHom := by
      apply le_antisymm
      · intro x hx
        refine ⟨t * x * t⁻¹, ?_, ?_⟩
        · rw [hL₂]
          exact ⟨x, hx, rfl⟩
        · simp [mul_assoc]
      · rintro _ ⟨y, hy, rfl⟩
        rw [hL₂] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        simpa [MulAut.conj_apply, mul_assoc] using hx
    have hshape : ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
        IsL2 (Bar2 L') c.n ∨ IsSz (Bar2 L') c.n ∨ IsSU3 (Bar2 L') c.n ∨
          ((IsSL3 (Bar2 L') c.n ∨ IsSp4 (Bar2 L') c.n) ∧
            ∃ t ∈ D.T, ActsNontrivOnDiagram L' t) := by
      intro L' hL'
      rcases hsh L' hL' with h | h | ⟨h3, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl (h3 ▸ h)))
    have hcen : ∀ {K K' : Subgroup G} {s : G}, K ∈ calC c.L0 → c.L0 = K ⊔ K' → s ∈ D.T →
        K' = K.map (MulAut.conj s).toMonoidHom → K ∈ ({L₁, L₂} : Set (Subgroup G)) →
        ∀ A ∈ E3.aSet (c.n + 1)
            (barSub ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW (c.L0 ⊔ D.T)),
          A ≤ Subgroup.centralizer (barSub ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW K :
            Set (MulAut (Vtil (⊥ : Subgroup G) (conjClosure c.L0 (V ⊓ D.Z)) hW))) := by
      intro K K' s hK₁ hKK' hs hK' hKmem
      exact Ctx23L.le_centralizer_barSub_of_k417 c hK hSZ hS1 hW
        (CFSG.Quasithin.A3.subnormal_trans hK₁.1 hL0sub) hK₁.2.2
        (TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hW hK₁.1 hO2L0)
        (Ctx23L.barSub_sup_eq_of_conj c hSZ hW hKK' hs hK') (hshape K hKmem)
    intro A hA
    have hA₁ := hcen h₁ hL htT hL₂ (by simp) A hA
    have hA₂ := hcen h₂ (hL.trans (sup_comm L₁ L₂)) htT' hL₁ (by simp) A hA
    rw [Subgroup.le_centralizer_iff] at hA₁ hA₂ ⊢
    have hL₁s : L₁ ≤ stabTil ⊥ (conjClosure c.L0 (V ⊓ D.Z)) :=
      (((le_sup_left : L₁ ≤ L₁ ⊔ L₂).trans hL.symm.le).trans le_sup_left).trans hstab
    have hL₂s : L₂ ≤ stabTil ⊥ (conjClosure c.L0 (V ⊓ D.Z)) :=
      (((le_sup_right : L₂ ≤ L₁ ⊔ L₂).trans hL.symm.le).trans le_sup_left).trans hstab
    have hbar : barSub ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW c.L0 =
        barSub ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW L₁ ⊔
          barSub ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW L₂ :=
      (congrArg (barSub ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW) hL).trans (barSub_sup hW hL₁s hL₂s)
    rw [hbar]
    exact sup_le hA₁ hA₂

end CFSG.LocalAnalysis.UniquenessCase.UC22
