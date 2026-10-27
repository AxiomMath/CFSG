module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsTools
public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.Item146General

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1520Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        ∀ X ∈ scriptY2 A, P ≤ X → P ≤ pPrimeCoreOf 3 (delta A (lB A) X)

@[expose] noncomputable def Step1520Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P → P = ⁅P, A⁆

@[expose] noncomputable def Step1521U : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        ∀ X ∈ scriptY2 A, P ≤ X →
          P ≤ inSubgroup CFSG.solvableRadical (pPrimeCoreOf 3 (delta A (lB A) X)) →
          ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G) ∧
            P ≤ Subgroup.normalizer (U : Set G) ∧ Y ≤ Subgroup.normalizer (U : Set G)

@[expose] noncomputable def Step1521Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        P ≤ Subgroup.normalizer (Y : Set G) → L ≤ P ⊔ (Y ⊓ L)

variable {G : Type} [Group G] [Finite G]

theorem rank3II_15_20_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1423 : Item14_23 A L) (hcore : Step1520Core) (hcomm : Step1520Comm) :
    Step1520 A (lB A) c L := by
  intro Y hctx p P hP X hX hPX
  have hP0 := hcore G A c L h Y hctx p P hP X hX hPX
  set X₀ := pPrimeCoreOf 3 (delta A (lB A) X) with hX₀def
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX₀ : X₀ ∈ invariantPiSubgroups ⊤ A (piCompl 3) := by
    refine ⟨le_top, fun q hq => ?_, ?_⟩
    · have hcop := coprime_card_pPrimeCoreOf 3 (delta A (lB A) X)
      intro hq3
      rw [← hX₀def] at hcop
      have h3 : (3 : ℕ) ∣ Nat.card X₀ := by
        have : (q : ℕ) = 3 := hq3
        rw [← this]
        exact hq
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3
    · exact (le_normalizer_delta X).trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)
  have hPne : P ≠ ⊥ := by
    intro h0
    have hc := hP.2.2.2.2.1
    rw [h0, Subgroup.card_bot] at hc
    have h1 := hP.1.one_lt
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) h1
    omega
  have hsol := h1423 p hP.1 hP.2.1 P hPne hP.2.2.2.1 (hcomm G A c L h Y hctx p P hP)
    hP.2.2.2.2.2.1.1.2 X₀ hX₀ hP0
  set N := Subgroup.normalClosure ((P.subgroupOf X₀ : Subgroup ↥X₀) : Set ↥X₀) with hN
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hNs : Group.IsSolvable N := by
    have e : N ≃* N.map X₀.subtype := N.equivMapOfInjective _ X₀.subtype_injective
    have : Group.IsSolvable (N.map X₀.subtype) := hsol
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hNR : N ≤ CFSG.solvableRadical ↥X₀ := le_sSup ⟨hNn, hNs⟩
  intro x hx
  exact ⟨⟨x, hP0 hx⟩, hNR (Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr hx)), rfl⟩

theorem rank3II_15_21_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1520 : Step1520 A (lB A) c L) (hU : Step1521U) (hnorm : Claim153Normal A (lB A))
    (hgen : Step1521Gen) : Step1521 A (lB A) c L := by
  intro Y hctx p P hP X hX hPX
  obtain ⟨U, hU1, hU2, hAU, hPU, hYU⟩ :=
    hU G A c L h Y hctx p P hP X hX hPX (h1520 Y hctx p P hP X hX hPX)
  have hloc : IsPLocal 2 (Subgroup.normalizer (U : Set G)) := ⟨U, hU1, hU2, rfl⟩
  obtain ⟨M, hUM, hM⟩ := Finite.exists_le_maximal (p := IsPLocal 2) hloc
  have hMmax : IsMaximalTwoLocal M :=
    ⟨hM.prop, fun H hMH hH => (not_le_of_gt hMH) (hM.2 hH hMH.le)⟩
  have hMYA : M ∈ maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hMmax, fun x hx => hUM (sup_le hYU hAU hx)⟩
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) :=
    hPU.trans (hUM.trans (hnorm Y hctx.mem_y0Star M hMYA))
  have hLN : L ≤ Subgroup.normalizer (Y : Set G) :=
    (hgen G A c L h Y hctx p P hP hPY).trans
      (sup_le hPY (inf_le_left.trans Subgroup.le_normalizer))
  exact hctx.not_le_normalizer h.mem_thetaComponentsAt hLN

end CFSG.RankThree.PartTwo.Sec15
