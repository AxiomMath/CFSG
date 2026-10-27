module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S77Basic
import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
import CFSG.RankThree.GF2n.Tim81.Sec7.Transport
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

omit [Finite G] in
theorem perpRoots_conjSubgroup (Δ : Set (Subgroup G)) (X : Subgroup G) (g : G) :
    conjSubgroup g (perpRoots Δ X) =
      perpRoots (CFSG.Timmesfeld.ARS.conjSet Δ g) (conjSubgroup g X) := by
  change CFSG.Timmesfeld.ARS.conjSub (perpRoots Δ X) g =
    CFSG.Timmesfeld.ARS.gen
      {C : Subgroup G | C ∈ CFSG.Timmesfeld.ARS.conjSet Δ g ∧ C ≤ cenOf (conjSubgroup g X)}
  rw [show perpRoots Δ X =
      CFSG.Timmesfeld.ARS.gen {C : Subgroup G | C ∈ Δ ∧ C ≤ cenOf X} from rfl,
    CFSG.Timmesfeld.ARS.conjSub_gen]
  congr 1
  ext E
  have hiff : E ≤ cenOf (conjSubgroup g X) ↔
      CFSG.Timmesfeld.ARS.conjSub E g⁻¹ ≤ cenOf X := by
    change E ≤ Subgroup.centralizer (conjSubgroup g X : Set G) ↔
      CFSG.Timmesfeld.ARS.conjSub E g⁻¹ ≤ Subgroup.centralizer (X : Set G)
    rw [centralizer_conjSubgroup_eq]
    change E ≤ conjSubgroup g (Subgroup.centralizer (X : Set G)) ↔
      conjSubgroup g⁻¹ E ≤ Subgroup.centralizer (X : Set G)
    simpa only [inv_inv] using
      (conjSubgroup_le_iff (g := g⁻¹) (S := E) (T := Subgroup.centralizer (X : Set G))).symm
  simp only [Set.mem_setOf_eq]
  rw [CFSG.Timmesfeld.ARS.mem_conjSet, CFSG.Timmesfeld.ARS.mem_conjSet]
  simp only [Set.mem_setOf_eq, hiff]

theorem Sec7Hyp.normalizer_perpRoots (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (E : Subgroup G) :
    gammaL V ⊓ cenOf E ≤
      Subgroup.normalizer (perpRoots (gammaAt V) E : Set G) := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxL, hxE⟩ := hx
  have hxY : x ∈ gammaStab V := hS.toSec6Hyp.gammaL_le_gammaStab h75 hxL
  have hxE' : conjSubgroup x E = E :=
    mem_normalizer_iff_conjSubgroup_eq.mp (Subgroup.centralizer_le_normalizer (E : Set G) hxE)
  have hΓ : CFSG.Timmesfeld.ARS.conjSet (gammaAt V) x = gammaAt V :=
    CFSG.Timmesfeld.ARS.mem_stabSet.mp hxY
  rw [mem_normalizer_iff_conjSubgroup_eq, perpRoots_conjSubgroup, hΓ, hxE']

private theorem perpRoots_eq_sylowRoots_aux (hS : Sec7Hyp M V n f)
    (h74 : Sec7.Stmt74 M V) (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f)
    (hRTS : UnitaryRootTypeSylow) (hSR : UnitarySylowRoots) (h76 : Sec7.Stmt76 V)
    {B : Subgroup G} (hB : B ∈ omegaSet V) (hVB : ⁅V, B⁆ = ⊥)
    (hpair : ∀ A₁ ∈ gammaAt V, ∀ A₂ ∈ gammaAt V, IsL2Gen A₁ A₂ →
      ¬ B ≤ cenOf (A₁ ⊔ A₂)) :
    ∃ S : Sylow 2 ↥(gammaL V),
      perpRoots (gammaAt V) B = sylowRoots (gammaL V) (gammaAt V) S ∧
      V ≤ sylowRoots (gammaL V) (gammaAt V) S ∧
      B ≤ sylowRoots (gammaL V) (gammaAt V) S := by
  obtain ⟨S, hBS, hVS⟩ := hS.exists_sylowRoots_of_commute h74 h75 h76U hRTS hB
    hS.toSec6Hyp.mem_gammaAt_self hVB
  have hW := hSR G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
    (by have := hS.four_le; omega) hS.two_le (hS.isSUImage_gammaL h76U) S
  refine ⟨S, le_antisymm ?_ ?_, hVS, hBS⟩
  · change CFSG.Timmesfeld.ARS.gen {A : Subgroup G | A ∈ gammaAt V ∧ A ≤ cenOf B} ≤ _
    refine CFSG.Timmesfeld.ARS.gen_le fun A hA => ?_
    refine hW.2.2.2.2.1 A hA.1 ?_
    rw [Subgroup.le_centralizer_iff]
    change CFSG.Timmesfeld.ARS.gen
      {C : Subgroup G | C ∈ gammaAt V ∧
        C ≤ (S : Subgroup ↥(gammaL V)).map (gammaL V).subtype} ≤ cenOf A
    refine CFSG.Timmesfeld.ARS.gen_le fun C hC => ?_
    rw [Subgroup.le_centralizer_iff]
    by_cases hAC : A = C
    · subst hAC
      obtain ⟨x, -, rfl⟩ := gammaAt_subset_omegaSet V hA.1
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Hyp.commute_of_mem_conj hS.sec5.toRootHyp.toHyp hb ha
    · have hcomm : ⁅A, C⁆ = ⊥ := by
        rcases h76 A hA.1 C hC.1 hAC with h | hL
        · exact h
        · exfalso
          refine hpair A hA.1 C hC.1 hL ?_
          change B ≤ Subgroup.centralizer ((A ⊔ C : Subgroup G) : Set G)
          rw [CFSG.centralizer_sup_eq]
          refine le_inf (Subgroup.le_centralizer_iff.mp hA.2) ?_
          rw [Subgroup.le_centralizer_iff]
          intro c hc
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          exact (hW.1 c ((CFSG.Timmesfeld.ARS.le_gen hC) hc) b (hBS hb)).symm
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  · change sylowRoots (gammaL V) (gammaAt V) S ≤
      CFSG.Timmesfeld.ARS.gen {A : Subgroup G | A ∈ gammaAt V ∧ A ≤ cenOf B}
    refine CFSG.Timmesfeld.ARS.gen_le fun A hA => ?_
    refine CFSG.Timmesfeld.ARS.le_gen ⟨hA.1, ?_⟩
    have hAW : A ≤ sylowRoots (gammaL V) (gammaAt V) S :=
      CFSG.Timmesfeld.ARS.le_gen hA
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hW.1 a (hAW ha) b (hBS hb)).symm

theorem Sec7Hyp.perpRoots_eq_sylowRoots (hS : Sec7Hyp M V n f)
    (h74 : Sec7.Stmt74 M V) (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f)
    (hRTS : UnitaryRootTypeSylow) (hSR : UnitarySylowRoots) (h76 : Sec7.Stmt76 V)
    {B : Subgroup G} (hB : B ∈ omegaSet V) (hVB : ⁅V, B⁆ = ⊥)
    (hpair : ∀ A₁ ∈ gammaAt V, ∀ A₂ ∈ gammaAt V, IsL2Gen A₁ A₂ →
      ¬ B ≤ cenOf (A₁ ⊔ A₂)) :
    ∃ S : Sylow 2 ↥(gammaL V),
      perpRoots (gammaAt V) B = sylowRoots (gammaL V) (gammaAt V) S ∧
      V ≤ sylowRoots (gammaL V) (gammaAt V) S := by
  obtain ⟨S, hE, hV, -⟩ := perpRoots_eq_sylowRoots_aux hS h74 h75 h76U hRTS hSR h76 hB hVB hpair
  exact ⟨S, hE, hV⟩

private theorem isElemAbelian_sylowRoots (hS : Sec7Hyp M V n f)
    (h76U : Sec7.Stmt76U V n f) (hSR : UnitarySylowRoots)
    (S : Sylow 2 ↥(gammaL V)) :
    CFSG.Open.IsElemAbelian 2 (sylowRoots (gammaL V) (gammaAt V) S) := by
  have hW := hSR G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
    (by have := hS.four_le; omega) hS.two_le (hS.isSUImage_gammaL h76U) S
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro x y
    exact Subtype.ext (hW.1 x x.2 y y.2)
  · intro x hx
    simpa [pow_two] using hW.2.1 x hx

private theorem conj_sylowRoots_le_gammaL (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f) (hRTS : UnitaryRootTypeSylow)
    (hSR : UnitarySylowRoots) {S₁ : Sylow 2 ↥(gammaL V)} {g : G}
    (hVg : conjSubgroup g⁻¹ V ≤ sylowRoots (gammaL V) (gammaAt V) S₁) :
    conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁) ≤ gammaL V := by
  have hW := hSR G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
    (by have := hS.four_le; omega) hS.two_le (hS.isSUImage_gammaL h76U) S₁
  change CFSG.Timmesfeld.ARS.conjSub (sylowRoots (gammaL V) (gammaAt V) S₁) g ≤ gammaL V
  rw [show sylowRoots (gammaL V) (gammaAt V) S₁ =
      CFSG.Timmesfeld.ARS.gen {A : Subgroup G | A ∈ gammaAt V ∧
        A ≤ (S₁ : Subgroup ↥(gammaL V)).map (gammaL V).subtype} from rfl,
    CFSG.Timmesfeld.ARS.conjSub_gen]
  refine CFSG.Timmesfeld.ARS.gen_le fun A hA => ?_
  rw [CFSG.Timmesfeld.ARS.conjSet, Set.mem_image] at hA
  obtain ⟨A', hA', hAeq⟩ := hA
  rw [← hAeq]
  have hA'Ω : A' ∈ omegaSet V := gammaAt_subset_omegaSet V hA'.1
  have hEΩ : conjSubgroup g A' ∈ omegaSet V := by
    obtain ⟨x, -, rfl⟩ := hA'Ω
    exact ⟨g * x, Subgroup.mem_top (g * x), by rw [conjSubgroup_mul]⟩
  have hcomm' : ⁅A', conjSubgroup g⁻¹ V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hW.1 a ((CFSG.Timmesfeld.ARS.le_gen hA') ha) b (hVg hb)).symm
  have hEcomm : ⁅V, conjSubgroup g A'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    change V ≤ Subgroup.centralizer (conjSubgroup g A' : Set G)
    rw [centralizer_conjSubgroup_eq]
    change V ≤ conjSubgroup g (Subgroup.centralizer (A' : Set G))
    have h2 : conjSubgroup g⁻¹ V ≤ Subgroup.centralizer (A' : Set G) :=
      Subgroup.le_centralizer_iff.mpr
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm')
    have h3 := (conjSubgroup_le_iff (g := g⁻¹) (S := V)
      (T := Subgroup.centralizer (A' : Set G))).mp h2
    simpa only [inv_inv] using h3
  obtain ⟨S', hA'S', -⟩ := hS.exists_sylowRoots_of_commute h74 h75 h76U hRTS hEΩ
    hS.toSec6Hyp.mem_gammaAt_self hEcomm
  exact hA'S'.trans (sylowRoots_le _ _ S')

private theorem exists_conj_eq_sylowRoots (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f) (hRTS : UnitaryRootTypeSylow)
    (hSR : UnitarySylowRoots) (h76 : Sec7.Stmt76 V) {g : G}
    (hVB : ⁅V, conjSubgroup g V⁆ = ⊥)
    (hpair : ∀ A₁ ∈ gammaAt V, ∀ A₂ ∈ gammaAt V, IsL2Gen A₁ A₂ →
      ¬ conjSubgroup g V ≤ cenOf (A₁ ⊔ A₂)) :
    ∃ S₀ S₁ : Sylow 2 ↥(gammaL V),
      perpRoots (gammaAt V) (conjSubgroup g V) = sylowRoots (gammaL V) (gammaAt V) S₀ ∧
      V ≤ sylowRoots (gammaL V) (gammaAt V) S₀ ∧
      conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁) =
        sylowRoots (gammaL V) (gammaAt V) S₀ ∧
      V ≤ sylowRoots (gammaL V) (gammaAt V) S₁ := by
  have hBΩ : conjSubgroup g V ∈ omegaSet V := ⟨g, Subgroup.mem_top g, rfl⟩
  obtain ⟨S₀, hE₀, hVS₀⟩ := hS.perpRoots_eq_sylowRoots h74 h75 h76U hRTS hSR h76
    hBΩ hVB hpair
  have hcommg : ⁅V, conjSubgroup g⁻¹ V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    change V ≤ Subgroup.centralizer (conjSubgroup g⁻¹ V : Set G)
    rw [centralizer_conjSubgroup_eq]
    change V ≤ conjSubgroup g⁻¹ (Subgroup.centralizer (V : Set G))
    rw [← conjSubgroup_le_iff (g := g) (S := V) (T := Subgroup.centralizer (V : Set G))]
    rw [Subgroup.le_centralizer_iff]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVB
  obtain ⟨S₁, hVgS₁, hVS₁⟩ := hS.exists_sylowRoots_of_commute h74 h75 h76U hRTS
    ⟨g⁻¹, Subgroup.mem_top g⁻¹, rfl⟩ hS.toSec6Hyp.mem_gammaAt_self hcommg
  have hE₁elem : CFSG.Open.IsElemAbelian 2
      (conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁)) :=
    isElemAbelian_conjSubgroup (isElemAbelian_sylowRoots hS h76U hSR S₁) g
  have hE₁L : conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁) ≤ gammaL V :=
    conj_sylowRoots_le_gammaL hS h74 h75 h76U hRTS hSR hVgS₁
  have hBE₁ : conjSubgroup g V ≤ conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁) :=
    conjSubgroup_mono hVS₁
  have hE₁cB : conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁) ≤
      cenOf (conjSubgroup g V) := by
    rw [Subgroup.le_centralizer_iff]
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact elemAbelian_mul_comm hE₁elem hx (hBE₁ hb)
  have hE₁N : conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁) ≤
      Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S₀ : Set G) := by
    have h := (le_inf hE₁L hE₁cB).trans (hS.normalizer_perpRoots h75 (conjSubgroup g V))
    rwa [hE₀] at h
  have hcard : Nat.card (sylowRoots (gammaL V) (gammaAt V) S₀) ≤
      Nat.card (conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁)) := by
    rw [hSR G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
        (by have := hS.four_le; omega) hS.two_le (hS.isSUImage_gammaL h76U) S₀ |>.2.2.1,
      card_conjSubgroup,
      hSR G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
        (by have := hS.four_le; omega) hS.two_le (hS.isSUImage_gammaL h76U) S₁ |>.2.2.1]
  have hE₁eq : conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁) =
      sylowRoots (gammaL V) (gammaAt V) S₀ :=
    (hSR G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
      (by have := hS.four_le; omega) hS.two_le (hS.isSUImage_gammaL h76U) S₀).2.2.2.2.2
      (conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁))
      (le_inf hE₁L hE₁N)
      (fun x hx y hy => elemAbelian_mul_comm hE₁elem hx hy)
      (fun x hx => by simpa [pow_two] using hE₁elem.2 x hx) hcard
  exact ⟨S₀, S₁, hE₀, hVS₀, hE₁eq, hVS₁⟩

private theorem normalizes_sylowRoots (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h76U : Sec7.Stmt76U V n f) (hSR : UnitarySylowRoots) {g : G}
    {S₀ S₁ : Sylow 2 ↥(gammaL V)}
    (hVS₀ : V ≤ sylowRoots (gammaL V) (gammaAt V) S₀)
    (hVS₁ : V ≤ sylowRoots (gammaL V) (gammaAt V) S₁)
    (hE₁eq : conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S₁) =
      sylowRoots (gammaL V) (gammaAt V) S₀) :
    hOf M V g ≤ Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S₀ : Set G) ∧
      V ≤ sylowRoots (gammaL V) (gammaAt V) S₀ ⊓ hOf M V g ∧
      sylowRoots (gammaL V) (gammaAt V) S₀ ⊓ hOf M V g ≤ inSubgroup (pCore 2) (hOf M V g) := by
  have hPN₀ : Pc M V ≤
      Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S₀ : Set G) :=
    hS.Pc_le_normalizer_sylowRoots h74 h76U hSR hVS₀
  have hPN₁ : Pc M V ≤
      Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S₁ : Set G) :=
    hS.Pc_le_normalizer_sylowRoots h74 h76U hSR hVS₁
  have hPgN : conjSubgroup g (Pc M V) ≤
      Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S₀ : Set G) := by
    have h := conjSubgroup_mono (g := g) hPN₁
    rw [show Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S₀ : Set G) =
        conjSubgroup g (Subgroup.normalizer
          (sylowRoots (gammaL V) (gammaAt V) S₁ : Set G)) by
      rw [← hE₁eq, normalizer_conjSubgroup]]
    exact h
  have hHnorm : hOf M V g ≤
      Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S₀ : Set G) :=
    sup_le hPN₀ hPgN
  have hVH : V ≤ sylowRoots (gammaL V) (gammaAt V) S₀ ⊓ hOf M V g :=
    le_inf hVS₀ (hS.sec5.toRootHyp.toHyp.le_Pc.trans le_sup_left)
  have hB2 : IsPGroup 2 ↥(sylowRoots (gammaL V) (gammaAt V) S₀ ⊓ hOf M V g) := by
    have h : CFSG.Open.IsElemAbelian 2
        (sylowRoots (gammaL V) (gammaAt V) S₀ ⊓ hOf M V g) :=
      CFSG.Open.IsElemAbelian.mono (isElemAbelian_sylowRoots hS h76U hSR S₀)
        (fun x hx => hx.1)
    exact h.isPGroup
  have hHN : hOf M V g ≤ Subgroup.normalizer
      (sylowRoots (gammaL V) (gammaAt V) S₀ ⊓ hOf M V g : Set G) := by
    intro h hh
    change h ∈ Subgroup.normalizer
      ((sylowRoots (gammaL V) (gammaAt V) S₀ ⊓ hOf M V g : Subgroup G) : Set G)
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_inf,
      mem_normalizer_iff_conjSubgroup_eq.mp (hHnorm hh),
      mem_normalizer_iff_conjSubgroup_eq.mp (Subgroup.le_normalizer hh)]
  exact ⟨hHnorm, hVH, Tim78.le_inSubgroup_pCore inf_le_right hHN hB2⟩

theorem Sec7Hyp.stmt77b (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h75 : Sec7.Stmt75 V) (h76 : Sec7.Stmt76 V) (h76U : Sec7.Stmt76U V n f)
    (hRTS : UnitaryRootTypeSylow) (hSR : UnitarySylowRoots) : Sec7.Stmt77b V := by
  rintro ⟨B, hBΩ, hBΓ, hVB⟩
  by_contra hno
  have hpair : ∀ A₁ ∈ gammaAt V, ∀ A₂ ∈ gammaAt V, IsL2Gen A₁ A₂ →
      ¬ B ≤ cenOf (A₁ ⊔ A₂) := by
    intro A₁ hA₁ A₂ hA₂ hL hBle
    exact hno ⟨B, hBΩ, hBΓ, hVB, A₁, hA₁, A₂, hA₂, hL, hBle⟩
  obtain ⟨g, -, rfl⟩ := hBΩ
  obtain ⟨S₀, S₁, hE₀, hVS₀, hE₁eq, hVS₁⟩ :=
    exists_conj_eq_sylowRoots hS h74 h75 h76U hRTS hSR h76 hVB hpair
  obtain ⟨hHnorm, hVH, hO2⟩ := normalizes_sylowRoots hS h74 h76U hSR hVS₀ hVS₁ hE₁eq
  have hO2ne : inSubgroup (pCore 2) (hOf M V g) ≠ ⊥ := by
    intro hbot
    exact hS.sec5.toRootHyp.toHyp.ne_bot (le_bot_iff.mp (hVH.trans (hO2.trans_eq hbot)))
  by_cases hHM : hOf M V g ≤ M
  · have hPgM : conjSubgroup g (Pc M V) ≤ M := le_sup_right.trans hHM
    have hPN : Pc M V ≤ Subgroup.normalizer (conjSubgroup g⁻¹ V : Set G) := by
      have h1 : conjSubgroup g (Pc M V) ≤ Subgroup.normalizer (V : Set G) := by
        rw [hS.sec5.toRootHyp.toHyp.normalizer_eq]
        exact hPgM
      have h2 := conjSubgroup_mono (g := g⁻¹) h1
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
        ← normalizer_conjSubgroup] at h2
      exact h2
    have hEeq : conjSubgroup g⁻¹ V = V :=
      hS.sec5.eq_of_Pc_le_normalizer ⟨g⁻¹, Subgroup.mem_top g⁻¹, rfl⟩ hPN
    have hBV : conjSubgroup g V = V := by
      have h := congrArg (conjSubgroup g) hEeq
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h
      exact h.symm
    refine hBΓ ?_
    rw [hBV]
    exact hS.toSec6Hyp.mem_gammaAt_self
  · have hHmem : IsHMember M V (hOf M V g) :=
      ⟨hO2ne, le_sup_left, hHM⟩
    exact hBΓ (hS.toSec6Hyp.sigmaSet_subset_gammaAt
      ((mem_sigmaSet_iff hS.sec5.toRootHyp.toHyp).mpr hHmem))

end CFSG.RankThree.GF2n.Tim81
