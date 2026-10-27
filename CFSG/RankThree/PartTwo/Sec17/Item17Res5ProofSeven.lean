module

import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofSeven
public import CFSG.RankThree.PartTwo.Sec17.Item17ResProof177

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof
open scoped commutatorElement

@[expose] noncomputable def Step177MainMAny : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G, V ≤ Subgroup.normalizer (Y₀ : Set G) →
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) →
      CFSG.Assembly.IsElemAbelian 2 V →
      ⁅Y₀, V⁆ = ⊥ → ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      (∀ b ∈ A ⊓ L, b ≠ 1 →
        ⁅V, Subgroup.zpowers c⁆ ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥) →
      normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c ≤
        Subgroup.normalizer (Y₀ : Set G)

theorem step177MainM_of_any (h : Step177MainMAny) : Step177MainM := by
  intro G _ _ A c L Y₀ hs h1514 h176 hΩ V hV hYV hcV hUb
  exact h G A c L Y₀ hs h1514 h176 hΩ V hV.prop.1 hV.prop.2.1 hV.prop.2.2 hYV hcV hUb

theorem step177MainB_of_any (h : Step177MainMAny) : Step177MainB :=
  step177MainB_of_M (step177MainM_of_any h)

@[expose] noncomputable def Step177MainMB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G, V ≤ Subgroup.normalizer (Y₀ : Set G) →
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) →
      CFSG.Assembly.IsElemAbelian 2 V →
      ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      (∀ b ∈ A ⊓ L, b ≠ 1 →
        ⁅V, Subgroup.zpowers c⁆ ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥) →
      normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c ≤
        Subgroup.normalizer (Y₀ : Set G)

theorem step177MainMAny_of_MB (h : Step177MainMB) : Step177MainMAny := by
  intro G _ _ A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hYV hcV hUb
  refine h G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab ?_ hcV hUb
  have hYVc : Y₀ ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYV
  have hcM : c ∈ Subgroup.normalizer (Y₀ : Set G) :=
    hs.normalizer_c_le (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  have hUV : ⁅V, Subgroup.zpowers c⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hMV hcM))
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hYVc (hs.le_y0 hx.2)) v (hUV hv)).symm

namespace Proof17Res5

variable {G : Type} [Group G] [Finite G]

theorem false_of_step177MainMB (hM : Step177MainMB) {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (h176 : Item176 A (lB A) c L) (hΩ : omegaA A = {Subgroup.zpowers c}) {V : Subgroup G}
    (hVM : V ≤ Subgroup.normalizer (Y₀ : Set G))
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVab : CFSG.Assembly.IsElemAbelian 2 V)
    (hUC : ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (hcV : ⁅V, Subgroup.zpowers c⁆ ≠ ⊥)
    (hUB : ⁅V, Subgroup.zpowers c⁆ ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set B := A ⊓ L with hBdef
  set X := normalClosureIn (Subgroup.centralizer (B : Set G)) c with hXdef
  set U := ⁅V, Subgroup.zpowers c⁆ with hUdef
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hcM : c ∈ M :=
    h.normalizer_c_le (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  have hcNV : c ∈ Subgroup.normalizer (V : Set G) := hMV hcM
  have hUV : U ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hcNV)
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun a ha =>
    centralizer_singleton_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr
      (h.toSec13Data.commute ha hcA))
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.le_normalizer.trans h.normalizer_le).trans hMV
  have hcU : c ∈ Subgroup.normalizer (U : Set G) := le_normalizer_commutator hAV hAc hcA
  have hUU : U = ⁅U, Subgroup.zpowers c⁆ :=
    eq_commutator_of_le_commutator (pow_three_of_std h hcA) hV2 hVcomm hcNV hcU le_rfl
  have hUb : ∀ b ∈ B, b ≠ 1 → U ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥ :=
    fun b hb _ => by
      rw [eq_bot_iff, ← hUB]
      exact Proof17Res.inf_pPrimeCoreOf_le hb hUC
  have hXM := hM G A c L Y₀ h h1514 h176 hΩ V hVM hMV hVab hUC (by rwa [← hUdef]) hUb
  have hcX : c ∈ X := Subgroup.subset_closure ⟨1, one_mem _, by group⟩
  have hUX : U ≤ X := by
    rw [hUU, Subgroup.commutator_le]
    intro u hu y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have huc : u * c * u⁻¹ ∈ X := Subgroup.subset_closure ⟨u, hUC hu, rfl⟩
    rw [commutatorElement_def, show u * c ^ k * u⁻¹ = (u * c * u⁻¹) ^ k by rw [conj_zpow]]
    exact mul_mem (zpow_mem huc k) (inv_mem (zpow_mem hcX k))
  have hVO : V ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVM hMV hV2
  have hle : X ⊓ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer
        (hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)
  have hUO : U ≤ CFSG.Open.pCoreOf 2 X := fun u hu => hle ⟨hUX hu, hVO (hUV hu)⟩
  have hcB : c ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (h.toSec13Data.commute (h.toSec13Data.mem_A) hx.1).symm
  apply hcV
  rw [eq_bot_iff, ← hUB]
  exact le_inf le_rfl (hUO.trans (Proof17Res.pCoreOf_le_pPrimeCoreOf_centralizer hcB))

end Proof17Res5

theorem step1712SevenY0_of_MB (hM : Step177MainMB) (h1514 : Item1514S17) (h176 : Item176R)
    (h9 : CardInfNineS17) : Step1712SevenY0 := by
  intro G _ _ A c L Y₀ h V hV hΩ hVY hVc hVcY
  have hA : IsE27 A := isE27_of_std h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set W := ⁅V, Subgroup.zpowers c⁆ with hWdef
  have hAM : A ≤ M := Subgroup.le_normalizer.trans h.normalizer_le
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun a ha =>
    centralizer_singleton_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr
      (h.toSec13Data.commute ha hcA))
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := le_normalizer_commutator hAV hAc
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.toSec13Data.mem_lA.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := (h.le_y0.trans Subgroup.le_normalizer).trans hMV
  have hLzc : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun l hl =>
    centralizer_singleton_le_normalizer_zpowers c (hLc hl)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_normalizer_commutator hLV hLzc
  have hWL : ⁅W, L⁆ = ⊥ := by
    have h1 : ⁅W, L⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hLW
    have h2 : ⁅W, L⁆ ≤ Y₀ := by
      have hWV : W ≤ V :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hAV hcA))
      exact (Subgroup.commutator_mono hWV h.le_y0).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hVM)
    exact le_bot_iff.mp (hVcY ▸ le_inf h1 h2)
  have hWC : W ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (W : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact hWL)) hx.2
    exact (Subgroup.mem_centralizer_iff.mp hxC w hw).symm
  have hB : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by rw [hA.2, h9 G A c L Y₀ h]⟩
  have hOQ : pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ∈
      scriptQ A (lB A) := Proof17Res.pPrimeCoreOf_centralizer_hyperplane_mem_scriptQ hA hB
  by_cases hU : W ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥
  · exact (Proof17Res5.false_of_step177MainMB hM h (h1514 G A c L Y₀ h)
      (h176 G A c L h.toSec15R) hΩ hVM hMV hVab hWC hVc hU).elim
  · obtain ⟨U, hU', hUW, -⟩ := Proof1712.exists_fourGroupsMinus_le_of_le_commutator hA hcA
      hVab hAV (le_normalizer_inf hAW hOQ.1.2.2) inf_le_left hU
    exact ⟨U, hU'.1, hUW.trans inf_le_left,
      mem_scriptQ_of_le (mem_scriptQ_of_le hOQ inf_le_right (le_normalizer_inf hAW hOQ.1.2.2))
        hUW hU'.1.1.2.2⟩

end CFSG.RankThree.PartTwo.Sec17
