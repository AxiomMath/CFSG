module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res8ProofSeven
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

@[expose] noncomputable def Step177Contra : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G, V ≤ Subgroup.normalizer (Y₀ : Set G) →
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) →
      CFSG.Assembly.IsElemAbelian 2 V →
      ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      ⁅V, Subgroup.zpowers c⁆ ⊓
          pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥ →
        False

namespace Proof17Res10

variable {G : Type} [Group G] [Finite G]

theorem inf_pPrimeCoreOf_hyperplane_eq_bot (hbal : Step143Balance) (h9 : CardInfNineS17)
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c}) {V : Subgroup G}
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVab : CFSG.Assembly.IsElemAbelian 2 V)
    (hUb : ∀ b ∈ A ⊓ L, b ≠ 1 →
      ⁅V, Subgroup.zpowers c⁆ ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥) :
    ⁅V, Subgroup.zpowers c⁆ ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := isE27_of_std h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  set B := A ⊓ L with hBdef
  set U := ⁅V, Subgroup.zpowers c⁆ with hUdef
  set O := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hO
  have h9' : Nat.card B = 9 := h9 G A c L Y₀ h
  have hB : IsHyperplane A B := ⟨inf_le_left, by rw [hA.2, h9']⟩
  have hBc : ¬ B ≤ Subgroup.zpowers c := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers c) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (pow_three_of_std h hcA))
    omega
  obtain ⟨b, hbB, hbc⟩ := IsConcreteLE.not_le_iff_exists.mp hBc
  have hb1 : b ≠ 1 := fun h1 => hbc (h1 ▸ Subgroup.one_mem _)
  have hbΩ : Subgroup.zpowers b ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    intro hbc'
    exact hbc (hbc' ▸ Subgroup.mem_zpowers b)
  have hAM : A ≤ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer.trans h.normalizer_le
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun a ha =>
    centralizer_singleton_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr
      (h.toSec13Data.commute ha hcA))
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := le_normalizer_commutator hAV hAc
  have hACB : A ≤ Subgroup.centralizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h.toSec13Data.commute hx.1 ha
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hACB.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hAW : A ≤ Subgroup.normalizer ((U ⊓ O : Subgroup G) : Set G) := le_normalizer_inf hAU hAO
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hWW : U ⊓ O = ⁅U ⊓ O, Subgroup.zpowers c⁆ :=
    eq_commutator_of_le_commutator (pow_three_of_std h hcA) hV2 hVcomm (hAV hcA) (hAW hcA)
      inf_le_left
  have hWO : U ⊓ O ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    rw [hWW]
    exact (Subgroup.commutator_mono inf_le_right (Subgroup.zpowers_le.mpr hcA)).trans
      (Sec14.commutator_pPrimeCoreOf_le hbal h.toSec14Std (hB.1 hbB) hb1 hbΩ hB hbB)
  rw [eq_bot_iff, ← hUb b hbB hb1]
  exact le_inf inf_le_left hWO

end Proof17Res10

theorem step177MainMB_of_contra (hC : Step177Contra) (hbal : Step143Balance)
    (h9 : CardInfNineS17) : Step177MainMB := by
  intro G _ _ A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb
  exact (hC G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV
    (Proof17Res10.inf_pPrimeCoreOf_hyperplane_eq_bot hbal h9 hs hΩ hMV hVab hUb)).elim

theorem step177XbB_of_contra (hC : Step177Contra) (hbal : Step143Balance)
    (h9 : CardInfNineS17) : Step177XbB := by
  intro G _ _ A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb b _ _
  exact (hC G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV
    (Proof17Res10.inf_pPrimeCoreOf_hyperplane_eq_bot hbal h9 hs hΩ hMV hVab hUb)).elim

theorem step177XbQuasi_of_contra (hC : Step177Contra) (hbal : Step143Balance)
    (h9 : CardInfNineS17) : Step177XbQuasi := by
  intro G _ _ A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb b _ _
  exact (hC G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV
    (Proof17Res10.inf_pPrimeCoreOf_hyperplane_eq_bot hbal h9 hs hΩ hMV hVab hUb)).elim

theorem step177NRes_of_contra (hC : Step177Contra) (hbal : Step143Balance)
    (h9 : CardInfNineS17) : Step177NRes := by
  intro G _ _ A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb
  exact (hC G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV
    (Proof17Res10.inf_pPrimeCoreOf_hyperplane_eq_bot hbal h9 hs hΩ hMV hVab hUb)).elim

end CFSG.RankThree.PartTwo.Sec17
