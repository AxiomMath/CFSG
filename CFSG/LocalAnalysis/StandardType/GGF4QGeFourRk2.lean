module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
public import CFSG.LocalAnalysis.StandardType.GGF4Rk2Core
public import CFSG.LocalAnalysis.StandardType.GGF4PairRootLeviTransport
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk1
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCPairs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
import CFSG.Timmesfeld.Transvection.PresSp
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.LieType.Universal.Symplectic (rootGroup)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair shortBlock
  longBlock)

private theorem exists_unit_ne_inv_of_charTwo {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) : ∃ a : Fˣ, (a : F) ≠ ((a⁻¹ : Fˣ) : F) := by
  have hcard : 1 < Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  have : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hcard
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  refine ⟨a, fun h => ha ?_⟩
  have h2 : (a : F) * a = 1 := by
    calc (a : F) * a = a * ((a⁻¹ : Fˣ) : F) := by rw [← h]
      _ = 1 := by simp
  have h3 : ((a : F) + 1) * ((a : F) + 1) = 0 := by
    have h22 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h2 + ((a : F) + 1) * h22
  have h4 : (a : F) - 1 = 0 := by
    rw [CharTwo.sub_eq_add]
    exact mul_self_eq_zero.mp h3
  exact Units.ext (sub_eq_zero.mp h4)

private theorem sp6_simplePairs {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) {G : Type} [Group G] (φ : StatedSp 3 F →* G)
    (hφ : φ.ker ≤ Subgroup.center (StatedSp 3 F)) :
    (∀ a ∈ (rankOne (rootGroup 3 F) 0).map φ, ∀ b ∈ (rankOne (rootGroup 3 F) 2).map φ,
      a * b = b * a) ∧
    (∃ W, LinearBlockStandardPair F W ((rankOne (rootGroup 3 F) 0).map φ)
      ((rankOne (rootGroup 3 F) 1).map φ)) ∧
    (∃ W, SymplecticBlockStandardPair F W ((rankOne (rootGroup 3 F) 2).map φ)
      ((rankOne (rootGroup 3 F) 1).map φ)) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have e0 : rankOne (rootGroup 3 F) 0 = (shortBlock F h01).range :=
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.range_shortBlock_eq_rankOne
      (k := (0 : Fin 3)) (by decide)).symm
  have e1 : rankOne (rootGroup 3 F) 1 = (shortBlock F h12).range :=
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.range_shortBlock_eq_rankOne
      (k := (1 : Fin 3)) (by decide)).symm
  have e2 : rankOne (rootGroup 3 F) 2 = (longBlock F 3 2).range :=
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.range_longBlock_eq_rankOne
      (k := (2 : Fin 3)) (by decide)).symm
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hφ.trans (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)).le
  rw [e0, e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩
    have h := CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_shortBlock_longBlock h01
      (k := (2 : Fin 3)) (by decide) (by decide) A B
    rw [← map_mul, ← map_mul, h.eq]
  · exact CFSG.ClassicalInvolution.Models.SymplecticPairs.exists_linearBlockStandardPair_short_map
      h01 h12 h02 (exists_unit_ne_inv_of_charTwo hF) φ hφ (Or.inl rfl) (Or.inl rfl)
  · exact ⟨_, CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_map
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_longShort h12)
      φ hinj⟩

section Inputs

theorem exists_simplePair_of_tableBPos_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 1 ≤ f)
    {ψ : (ggU .PSp 3 f).K →* G} (hpos : GGTableBPos p Bs X .PSp 3 f ψ)
    (w : CoxeterMatrix.F₄.Group) {i j : Fin 4} (hij : i ≠ j)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    ∃ (ν : GGWeyl (ggU .PSp 3 f).D →* (ggU .PSp 3 f).K) (u : GGWeyl (ggU .PSp 3 f).D)
      (c d : Fin 3), GGWeylLift (ggU .PSp 3 f).D ν ∧
      (CoxeterMatrix.F₄ i j = 2 → c = 0 ∧ d = 2 ∨ c = 2 ∧ d = 0) ∧
      (CoxeterMatrix.F₄ i j = 3 → c = 0 ∧ d = 1) ∧
      (CoxeterMatrix.F₄ i j = 4 → c = 2 ∧ d = 1 ∨ c = 1 ∧ d = 2) ∧
      ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) =
        (ggRootLevi (ggU .PSp 3 f).D (Pi.single c 1)).map
          ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) ∧
      ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) =
        (ggRootLevi (ggU .PSp 3 f).D (Pi.single d 1)).map
          ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) := by
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_PSp_three]
    rfl
  have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, hf, by omega, by simp⟩
  obtain ⟨ν, hν⟩ := (ggTagFacts_PSp hadm (by decide)).2.1
  obtain ⟨u, c, d, hSi, hSj, h2, h3, h4⟩ :=
    exists_f4_pair_rootLevi_transport (ggU .PSp 3 f).D hpp hp2 hEl hNT hAind hpres hXA
      ψ ε hεrefl hεlevi (Equiv.refl _) hM ν hν w i j hij hi hj
  exact ⟨ν, u, c, d, hν, h2, h3, h4, hSi, hSj⟩

theorem ggF4QGeFourRk2_of_tableBPos_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .PSp 3 f X) (w : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    (CoxeterMatrix.F₄ i j = 2 →
      ∀ a ∈ ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs),
      ∀ b ∈ ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs),
        a * b = b * a) ∧
    (CoxeterMatrix.F₄ i j = 3 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
        LinearBlockStandardPair F W
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs))) ∧
    (CoxeterMatrix.F₄ i j = 4 →
      GGF4QGeFourBond .S1 f (by omega)
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs)) ∨
        GGF4QGeFourBond .S1 f (by omega)
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))) := by
  by_cases hij : i = j
  · subst hij
    have h1 : CoxeterMatrix.F₄ i i = 1 := CoxeterMatrix.F₄.diagonal i
    exact ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩
  obtain ⟨ψ, hker, -, hpos'⟩ := hpos
  obtain ⟨ν, u, c, d, -, h2, h3, h4, hSi, hSj⟩ :=
    exists_simplePair_of_tableBPos_PSp hpp hp2 hEl hNT hAind hpres hXA (by omega) hpos' w hij hi hj
  set ψ' : (ggU .PSp 3 f).K →* G := (MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ with hψ'
  have hker' : ψ'.ker ≤ Subgroup.center (ggU .PSp 3 f).K := by
    intro z hz
    apply hker
    have hz' := (MonoidHom.mem_ker).mp hz
    rw [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (MulAut.conj (ψ (ν u))).injective] at hz'
    exact hz'
  have hF4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hcomm, hlin, hsymp⟩ := sp6_simplePairs (F := GaloisField 2 f) hF4 ψ' hker'
  refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
  · rw [hSi, hSj]
    rcases h2 hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcomm
    · intro a ha b hb
      exact (hcomm b hb a ha).symm
  · rw [hSi, hSj]
    obtain ⟨rfl, rfl⟩ := h3 hl
    obtain ⟨W, hW⟩ := hlin
    exact ⟨GaloisField 2 f, inferInstance, inferInstance, W, inferInstance, hW⟩
  · rw [hSi, hSj]
    rcases h4 hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hsymp
    · exact Or.inr hsymp

theorem ggF4QGeFourRk2Input_S1_of_kgPos (hKG : GGF4QGeFourKGPosInput .S1) :
    GGF4QGeFourRk2Input .S1 := by
  intro G _ _ p B Bs x L D J y K hcfg e hpres f hf hp hrow X hX w i j hi hj
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hXA : ggAutomizer X Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rcases hX with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hpos := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  have hposX : GGTableBPosImage p Bs .PSp 3 f X := by
    rcases hX with rfl | rfl
    · exact hpos.1
    · exact hpos.2
  exact ggF4QGeFourRk2_of_tableBPos_PSp hpp hp2 hEl hNT hAind hpres hXA hf hposX w i j hi hj

end Inputs

end CFSG.StandardType
