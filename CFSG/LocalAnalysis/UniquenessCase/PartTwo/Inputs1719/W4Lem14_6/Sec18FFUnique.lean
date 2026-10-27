module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sp4
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC22.K148
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped commutatorElement

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

@[expose] def FactorBound (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop :=
  ∀ B : Subgroup G, CFSG.IsElementaryAbelian 2 ↥B → B ≤ Subgroup.normalizer (L : Set G) →
    ∀ m : ℕ, 1 ≤ m → Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) →
    ∀ Y Z : Submodule (ZMod 2) V, Z ≤ Y → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z →
    (∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y) →
    (∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y) →
    (∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) → secCost ρ B Y Z ≤ m → m < 2 * secCost ρ B Y Z

theorem ffUnique_of_factorBound [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {L : Subgroup G} (hL : IsComponentOf L ⊤) [IsSimpleGroup ↥L]
    {A : Subgroup G} (hA : A ∈ UC22.Ext.calP ρ) (hne : ⁅L, A⁆ ≠ ⊥) (hFac : FactorBound ρ L) :
    ∃ (B : Subgroup G) (m : ℕ), B ≤ A ∧ CFSG.IsElementaryAbelian 2 ↥B ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧ 1 ≤ m ∧
      Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ∧
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤) ∧
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤ ⊓ fixSub ρ L) ∧
      (∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ commOn ρ L ⊤, ρ b y = y) ∧
      (∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W → commOn ρ L ⊤ ⊓ fixSub ρ L ≤ W →
        W ≤ commOn ρ L ⊤ → W = commOn ρ L ⊤ ⊓ fixSub ρ L ∨ W = commOn ρ L ⊤) ∧
      (∃ l ∈ L, ∃ y ∈ commOn ρ L ⊤, ρ l y - y ∉ commOn ρ L ⊤ ⊓ fixSub ρ L) ∧
      secCost ρ B (commOn ρ L ⊤) (commOn ρ L ⊤ ⊓ fixSub ρ L) ≤ m := by
  classical
  have hAN := le_normalizer_of_mem_calP hρ hL hA
  have hLA := commutator_eq_self_of_mem_calP hρ hL hA hne
  have hAe := isElementaryAbelian_of_mem_calP hA
  have hbest := isBestOffenderOn_of_mem_calP hρ hA
  have hLp : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hLnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro hle
    have hL1 : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      apply hρ
      ext w
      simp [(hle hl).2 w Submodule.mem_top]
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance hL1
  obtain ⟨B, hBA, hBinv, hLU, hBU, hBbest, -, hmov, -⟩ :=
    exists_strictMin_moving L A hAe hAN hLA hLnt hbest
  set U := commOn ρ L ⊤ with hU
  have hBe : CFSG.IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.of_le hAe hBA
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAN
  have hLinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U := fun a ha u hu => hBinv a (Subgroup.mem_sup_left ha) u hu
  have hLnt' : ∃ l ∈ L, ∃ u ∈ U, ρ l u ≠ u := by
    by_contra h
    push Not at h
    exact hLU fun l hl => ⟨hl, fun u hu => h l hl u hu⟩
  have hcenEq : ∀ b ∈ B, (∀ u ∈ U, ρ b u = u) ↔ b ∈ Subgroup.centralizer (L : Set G) :=
    fun b hb => Sp4Aux.fix_iff_mem_centralizer hBN hLinv hLnt' hmov hb
  have hcen : cenOn ρ B U = B ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, (hcenEq x hx.1).1 hx.2⟩, fun hx => ⟨hx.1, (hcenEq x hx.1).2 hx.2⟩⟩
  obtain ⟨m, hm1, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧
      Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
    refine Sp4Aux.exists_card_eq_two_pow_mul (IsElementaryAbelian.isPGroup 2 ↥B) fun hle => hBU ?_
    intro b hb
    exact ⟨hb, (hcenEq b hb).2 (hle hb)⟩
  have hcost0 : secCost ρ B U ⊥ ≤ m := by
    refine Sp4Aux.secCost_bot_le hBbest.isOffenderOn.2 ?_
    rw [hcen]
    exact hm
  have hCBU : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ U, ρ b y = y :=
    fun b hb hc y hy => (hcenEq b hb).2 hc y hy
  have hUne : U ≠ ⊥ := by
    intro h
    obtain ⟨l, -, u, hu, hne'⟩ := hLnt'
    rw [h, Submodule.mem_bot] at hu
    exact hne' (by rw [hu, map_zero])
  obtain ⟨X, hXU, hXinv, hXmax⟩ := exists_maximal_invariant hBinv hUne
  have hXinvB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B X := fun a ha x hx => hXinv a (Subgroup.mem_sup_right ha) x hx
  have hUL : commOn ρ L U = U := commOn_commOn_eq hAe hAN hLA
  have hnt : ∃ l ∈ L, ∃ y ∈ U, ρ l y - y ∉ X := by
    by_contra h
    push Not at h
    have hle : commOn ρ L U ≤ X :=
      Submodule.span_le.2 fun w ⟨a, ha, u, hu, hw⟩ => hw ▸ h a ha u hu
    rw [hUL] at hle
    exact lt_irrefl X (lt_of_lt_of_le hXU hle)
  have hcost1 : secCost ρ B U X + secCost ρ B X ⊥ ≤ secCost ρ B U ⊥ :=
    secCost_superadd bot_le hXU.le hXinvB
  have h2m := hFac B hBe hBN m hm1 hm U X hXU.le hBinv hXinv hCBU hXmax hnt (by omega)
  have hLX : ∀ l ∈ L, ∀ x ∈ X, ρ l x = x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨Y, Z, hZY, hYX, hY, hZ, hirr, hnt'⟩ :=
      exists_irr_section (le_sup_left : L ≤ L ⊔ B) hLp hXinv hcon
    have hYB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B Y := fun a ha y hy => hY a (Subgroup.mem_sup_right ha) y hy
    have hZB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B Z := fun a ha z hz => hZ a (Subgroup.mem_sup_right ha) z hz
    have hsY : secCost ρ B Y Z ≤ secCost ρ B X ⊥ :=
      Sp4Aux.secCost_le_secCost_bot hZY hYX hYB hZB
    have hCBY : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y :=
      fun b hb hc y hy => hCBU b hb hc y (hXU.le (hYX hy))
    have h2m' := hFac B hBe hBN m hm1 hm Y Z hZY hY hZ hCBY hirr hnt' (by omega)
    omega
  have hCinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (U ⊓ fixSub ρ L) := by
    refine CFSG.LocalAnalysis.UniquenessCase.UC22.K148.isInvariant_sup (fun l hl w hw => ?_)
      (fun b hb w hw => ?_)
    · rw [(Submodule.mem_inf.1 hw).2 l hl]
      exact hw
    · exact Submodule.mem_inf.2 ⟨hBinv b (Subgroup.mem_sup_right hb) w (Submodule.mem_inf.1 hw).1,
        apply_mem_fixSub_of_mem_normalizer (hBN hb) (Submodule.mem_inf.1 hw).2⟩
  have hXC : X ≤ U ⊓ fixSub ρ L := fun x hx =>
    Submodule.mem_inf.2 ⟨hXU.le hx, fun l hl => hLX l hl x hx⟩
  have hXeq : X = U ⊓ fixSub ρ L := by
    rcases hXmax _ hCinv hXC inf_le_left with h | h
    · exact h.symm
    · exfalso
      obtain ⟨l, hl, u, hu, hlu⟩ := hLnt'
      have hu' : u ∈ U ⊓ fixSub ρ L := by rw [h]; exact hu
      exact hlu ((Submodule.mem_inf.1 hu').2 l hl)
  rw [← hXeq]
  exact ⟨B, m, hBA, hBe, hBN, hm1, hm, hBinv, hXinv, hCBU, hXmax, hnt, by omega⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
