module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwelveRest
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTenJFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThirteenAbelian
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEighteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwelveWC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyEightCorrected
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenGlueSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10 (LieAutVocab10)
open CFSG.LocalAnalysis.RankThreeTheoremC (KFactCentralOmega)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certificates

theorem r19_A12 (D : Data G) {V₀ V : Subgroup G}
    (h1 : ∀ (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L), R19_1At D V₀ V p L h)
    (h42 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (h8107 : F08.R8107 D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h := by
  intro p L A t B h
  refine nineteen_twelve_at D h (fun _ => rfl) h42 h8107 ?_
  intro hj
  obtain ⟨K₁, K₂, hK₁, hK₂, hne, hI, hL1, hL2, hpow, hgt, -, -⟩ :=
    jM_four_structure D h.hyp (h1 p L h.hyp) h42 h641 h642 h643 hj
  exact ⟨K₁, K₂, hK₁, hK₂, hne, hI, hL1, hL2, hpow, hgt⟩

theorem r19_A13 (D : Data G) {V₀ V : Subgroup G}
    (h42 : S17.R17_42At D V₀ V) (hK13 : K_19_13_autOmega)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_13At D V₀ V p L A t B 3 h := by
  intro p L A t B h
  exact nineteen_thirteen_of_autOmega D h (h12 p L A t B h) h42 hK13

theorem r19_C12 (D : Data G) {V₀ V : Subgroup G}
    (hodd : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), Odd (S17.nOf L))
    (h1 : ∀ (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L), R19_1At D V₀ V p L h)
    (h42 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (h8107 : F08.R8107 D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_12At D V₀ V p L A t B r h := by
  intro p L A t B r h
  refine nineteen_twelve_at D h
    (fun h3 => (r_ne_three h.hAcard h3 (hodd p L A t B r h) rfl).elim)
    h42 h8107 ?_
  intro hj
  obtain ⟨K₁, K₂, hK₁, hK₂, hne, hI, hL1, hL2, hpow, hgt, -, -⟩ :=
    jM_four_structure D h.hyp (h1 p L h.hyp) h42 h641 h642 h643 hj
  exact ⟨K₁, K₂, hK₁, hK₂, hne, hI, hL1, hL2, hpow, hgt⟩

theorem r19_C13 (D : Data G) {V₀ V : Subgroup G}
    (hodd : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), Odd (S17.nOf L)) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_13At D V₀ V p L A t B r h := by
  intro p L A t B r h h3 P hP
  exact (r_ne_three h.hAcard h3 (hodd p L A t B r h) rfl).elim

theorem r19_A17 (D : Data G) {V₀ V : Subgroup G}
    (h16 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_16At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h13 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_13At D V₀ V p L A t B 3 h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_17At D V₀ V p L A t B 3 Y N Dsub H S h := by
  intro p L A t B Y N Dsub H S h
  exact nineteen_seventeen_of D h (h16 p L A t B Y N Dsub H S h) (h13 p L A t B h.ctx)

theorem r19_C17 (D : Data G) {V₀ V : Subgroup G}
    (h16 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_16At D V₀ V p L A t B r Y N Dsub H S h)
    (h13 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_13At D V₀ V p L A t B r h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_17At D V₀ V p L A t B r Y N Dsub H S h := by
  intro p L A t B r Y N Dsub H S h
  exact nineteen_seventeen_of D h (h16 p L A t B r Y N Dsub H S h) (h13 p L A t B r h.ctx)

theorem nineteen_eighteen_at (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h15 : R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx)
    (hodd : K_19_20_oddAut) (h20b : Gap19_20b D)
    (hW1 : W7_9_1_4) (hW4 : W7_9_4c) (hmin : K_19_18_minNormal)
    (hgap : Gap19_18_5 D) :
    R19_18At D V₀ V p L A t B r Y N Dsub H S h := by
  refine nineteen_eighteen D h h11 h15 h17 hW1 hW4 hmin hgap ?_
  intro h3
  exact false_of_A7_or_L32 D h h17 h12 hodd h20b
    (Or.inr ⟨h3.1, by
      rw [index_barOfInter (M := D.M) (L := Dsub) h.hO2]
      exact h3.2⟩)

theorem r19_A18 (D : Data G) {V₀ V : Subgroup G}
    (h11 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_11At D V₀ V p L A t B r h)
    (h15 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (h17 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_17At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h)
    (hodd : K_19_20_oddAut) (h20b : Gap19_20b D)
    (hW1 : W7_9_1_4) (hW4 : W7_9_4c) (hmin : K_19_18_minNormal)
    (hgap : Gap19_18_5 D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_18At D V₀ V p L A t B 3 Y N Dsub H S h := by
  intro p L A t B Y N Dsub H S h
  exact nineteen_eighteen_at D h (h11 p L A t B 3 h.ctx) (h15 p L A t B 3 Y N Dsub H S h)
    (h17 p L A t B Y N Dsub H S h) (h12 p L A t B h.ctx) hodd h20b hW1 hW4 hmin hgap

theorem r19_C18 (D : Data G) {V₀ V : Subgroup G}
    (h11 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_11At D V₀ V p L A t B r h)
    (h15 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (h17 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_12At D V₀ V p L A t B r h)
    (hodd : K_19_20_oddAut) (h20b : Gap19_20b D)
    (hW1 : W7_9_1_4) (hW4 : W7_9_4c) (hmin : K_19_18_minNormal)
    (hgap : Gap19_18_5 D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_18At D V₀ V p L A t B r Y N Dsub H S h := by
  intro p L A t B r Y N Dsub H S h
  exact nineteen_eighteen_at D h (h11 p L A t B r h.ctx) (h15 p L A t B r Y N Dsub H S h)
    (h17 p L A t B r Y N Dsub H S h) (h12 p L A t B r h.ctx) hodd h20b hW1 hW4 hmin hgap

theorem r19_A201 (D : Data G) {V₀ V : Subgroup G}
    (h16 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_16At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h17 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_17At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h18 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_18At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h19 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_19At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h)
    (h13 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_13At D V₀ V p L A t B 3 h)
    (hodd : K_19_20_oddAut) (hJ0 : K_19_20_J0shape) (hforce : K_19_20_force)
    (h20b : Gap19_20b D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_20_1At D V₀ V p L A t B 3 Y N Dsub H S h := by
  intro p L A t B Y N Dsub H S h
  exact nineteen_twenty_one D h (h16 p L A t B Y N Dsub H S h)
    (h17 p L A t B Y N Dsub H S h) (h18 p L A t B Y N Dsub H S h)
    (h19 p L A t B Y N Dsub H S h) (h12 p L A t B h.ctx)
    (fun _ => h12 p L A t B h.ctx) (h13 p L A t B h.ctx) hodd hJ0 hforce h20b

theorem r19_C201 (D : Data G) {V₀ V : Subgroup G}
    (h16 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_16At D V₀ V p L A t B r Y N Dsub H S h)
    (h17 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h18 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_18At D V₀ V p L A t B r Y N Dsub H S h)
    (h19 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_19At D V₀ V p L A t B r Y N Dsub H S h)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_12At D V₀ V p L A t B r h)
    (h13 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_13At D V₀ V p L A t B r h)
    (hodd : K_19_20_oddAut) (hJ0 : K_19_20_J0shape) (hforce : K_19_20_force)
    (h20b : Gap19_20b D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_20_1At D V₀ V p L A t B r Y N Dsub H S h := by
  intro p L A t B r Y N Dsub H S h
  exact nineteen_twenty_one D h (h16 p L A t B r Y N Dsub H S h)
    (h17 p L A t B r Y N Dsub H S h) (h18 p L A t B r Y N Dsub H S h)
    (h19 p L A t B r Y N Dsub H S h) (h12 p L A t B r h.ctx)
    (fun h3 => h12 p L A t B 3 { h.ctx with hr := h3, hr5 := by decide })
    (h13 p L A t B r h.ctx) hodd hJ0 hforce h20b

theorem r19_A202 (D : Data G) {V₀ V : Subgroup G}
    (h17 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_17At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h19 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_19At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h201 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_20_1At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h)
    (h13 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_13At D V₀ V p L A t B 3 h)
    (hodd : K_19_20_oddAut) (hforce : K_19_20_force) (h20b : Gap19_20b D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_20_2At D V₀ V p L A t B 3 Y N Dsub H S h := by
  intro p L A t B Y N Dsub H S h
  exact nineteen_twenty_two D h (h17 p L A t B Y N Dsub H S h)
    (h19 p L A t B Y N Dsub H S h) (h201 p L A t B Y N Dsub H S h)
    (h12 p L A t B h.ctx) (fun _ => h12 p L A t B h.ctx) (h13 p L A t B h.ctx)
    hodd hforce h20b

theorem r19_C202 (D : Data G) {V₀ V : Subgroup G}
    (h17 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h19 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_19At D V₀ V p L A t B r Y N Dsub H S h)
    (h201 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_20_1At D V₀ V p L A t B r Y N Dsub H S h)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_12At D V₀ V p L A t B r h)
    (h13 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_13At D V₀ V p L A t B r h)
    (hodd : K_19_20_oddAut) (hforce : K_19_20_force) (h20b : Gap19_20b D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_20_2At D V₀ V p L A t B r Y N Dsub H S h := by
  intro p L A t B r Y N Dsub H S h
  exact nineteen_twenty_two D h (h17 p L A t B r Y N Dsub H S h)
    (h19 p L A t B r Y N Dsub H S h) (h201 p L A t B r Y N Dsub H S h)
    (h12 p L A t B r h.ctx) (fun h3 => h12 p L A t B 3 { h.ctx with hr := h3, hr5 := by decide })
    (h13 p L A t B r h.ctx) hodd hforce h20b

theorem r19_A14 (D : Data G) {V₀ V : Subgroup G}
    (hglue : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3) (Y N : Subgroup G)
      (hY : Y ∈ muStarSet D B) (hN : N ∈ calMOf Y ∧ N ≠ D.M),
      R19_glue_5At D V₀ V p L A t B 3 h Y N hY hN)
    (h18 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_18At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h20 : (∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
        (Y N Dsub H S : Subgroup G)
        (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
        R19_20_1At D V₀ V p L A t B 3 Y N Dsub H S h) ∧
      (∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
        (Y N Dsub H S : Subgroup G)
        (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
        R19_20_2At D V₀ V p L A t B 3 Y N Dsub H S h))
    (h21 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_21At D V₀ V p L A t B 3 Y N Dsub H S h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_14At D V₀ V p L A t B 3 h := by
  intro p L A t B h
  exact nineteen_fourteen D h (hglue p L A t B h) (h18 p L A t B)
    ⟨h20.1 p L A t B, h20.2 p L A t B⟩ (h21 p L A t B)

theorem r19_C14 (D : Data G) {V₀ V : Subgroup G}
    (hglue : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r) (Y N : Subgroup G)
      (hY : Y ∈ muStarSet D B) (hN : N ∈ calMOf Y ∧ N ≠ D.M),
      R19_glue_5At D V₀ V p L A t B r h Y N hY hN)
    (h18 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_18At D V₀ V p L A t B r Y N Dsub H S h)
    (h20 : (∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
        (Y N Dsub H S : Subgroup G)
        (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
        R19_20_1At D V₀ V p L A t B r Y N Dsub H S h) ∧
      (∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
        (Y N Dsub H S : Subgroup G)
        (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
        R19_20_2At D V₀ V p L A t B r Y N Dsub H S h))
    (h21 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_21At D V₀ V p L A t B r Y N Dsub H S h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_14At D V₀ V p L A t B r h := by
  intro p L A t B r h
  exact nineteen_fourteen D h (hglue p L A t B r h) (h18 p L A t B r)
    ⟨h20.1 p L A t B r, h20.2 p L A t B r⟩ (h21 p L A t B r)

theorem r19_A22 (D : Data G) {V₀ V : Subgroup G}
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h171 : ∀ (hV : Hyp125 D V₀ V), (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_1At D V₀ V hV)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h42 : S17.R17_42At D V₀ V) (hK : K_BorelOvergroup)
    (h661 : S17.R17_66_1At D V₀ V) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_22At D V₀ V p L A t B 3 h := by
  intro p L A t B h
  exact nineteen_twentytwo_b D h h61 h127 (h171 h.hyp.hyp125 h1669)
    (h12 p L A t B h) h42 hK (gap19_22_holds D h h61 h127 h42 h661)

theorem r19_C22 (D : Data G) {V₀ V : Subgroup G}
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_12At D V₀ V p L A t B r h)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h171 : ∀ (hV : Hyp125 D V₀ V), (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_1At D V₀ V hV)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h42 : S17.R17_42At D V₀ V) (hK : K_BorelOvergroup)
    (h661 : S17.R17_66_1At D V₀ V) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_22At D V₀ V p L A t B r h := by
  intro p L A t B r h
  exact nineteen_twentytwo_b D h h61 h127 (h171 h.hyp.hyp125 h1669)
    (h12 p L A t B r h) h42 hK (gap19_22_holds D h h61 h127 h42 h661)

theorem r19_A23 (D : Data G) {V₀ V : Subgroup G}
    (h14 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_14At D V₀ V p L A t B 3 h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (A₀ : Subgroup G)
      (h : Ctx19_22 D V₀ V p L A t B 3 A₀),
      R19_23At D V₀ V p L A t B 3 A₀ h := by
  intro p L A t B A₀ h
  exact nineteen_twentythree D h (h14 p L A t B h.ctx)

theorem r19_C23 (D : Data G) {V₀ V : Subgroup G}
    (h14 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_14At D V₀ V p L A t B r h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ) (A₀ : Subgroup G)
      (h : Ctx19_22 D V₀ V p L A t B r A₀),
      R19_23At D V₀ V p L A t B r A₀ h := by
  intro p L A t B r A₀ h
  exact nineteen_twentythree D h (h14 p L A t B r h.ctx)

theorem r19_A12wc (D : Data G) {V₀ V : Subgroup G}
    (h1 : ∀ (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L), R19_1At D V₀ V p L h)
    (h42 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (_h : Ctx19_10 D V₀ V p L A t B 3), Concl19_12wc A := by
  intro p L A t B h
  refine nineteen_twelve_wc_at D h (h12 p L A t B h) h42 ?_
  intro hj
  obtain ⟨K₁, K₂, hK₁, hK₂, hne, hI, hL1, hL2, hpow, hgt, -, -⟩ :=
    jM_four_structure D h.hyp (h1 p L h.hyp) h42 h641 h642 h643 hj
  exact ⟨K₁, K₂, hK₁, hK₂, hne, hI, hL1, hL2, hpow, hgt⟩

theorem r19_A26 (D : Data G) {V₀ V : Subgroup G}
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h)
    (h12wc : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (_h : Ctx19_10 D V₀ V p L A t B 3), Concl19_12wc A)
    (h13 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_13At D V₀ V p L A t B 3 h)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h42 : S17.R17_42At D V₀ V) (h661 : S17.R17_66_1At D V₀ V)
    (h332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hCO : KFactCentralOmega)
    (hK1 : K_19_26_rankOne) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (A₀ H : Subgroup G)
      (h : Ctx19_23 D V₀ V p L A t B 3 A₀ H),
      R19_26At D V₀ V p L A t B 3 A₀ H h := by
  intro p L A t B A₀ H h
  exact nineteen_twentysix D h (fun _ => rfl) (h12 p L A t B h.ctx22.ctx)
    (h12wc p L A t B h.ctx22.ctx) (h13 p L A t B h.ctx22.ctx)
    (A_le_centralizer_V0 D h.ctx22.ctx h61 h127 h42 h661) h332 hCO hK1

theorem r19_C26 (D : Data G) {V₀ V : Subgroup G}
    (hodd : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), Odd (S17.nOf L)) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ V p L A t B r A₀ H),
      R19_26At D V₀ V p L A t B r A₀ H h :=
  fun p L A t B r _ _ h => hodd p L A t B r h.ctx22.ctx

theorem r19_odd_any (D : Data G) {V₀ V : Subgroup G}
    (h22 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_22At D V₀ V p L A t B 3 h)
    (h23 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (A₀ : Subgroup G)
      (h : Ctx19_22 D V₀ V p L A t B 3 A₀), R19_23At D V₀ V p L A t B 3 A₀ h)
    (h26 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (A₀ H : Subgroup G)
      (h : Ctx19_23 D V₀ V p L A t B 3 A₀ H), R19_26At D V₀ V p L A t B 3 A₀ H h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), Odd (S17.nOf L) := by
  intro p L A t B r h
  rcases Nat.even_or_odd (S17.nOf L) with heven | hodd
  · exfalso
    have hcardA : Nat.card A = (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) :=
      card_eq_of_isZModSq h.hAcard
    have h3dvd : 3 ∣ 2 ^ S17.nOf L - 1 := by
      have h2 : 2 ∣ S17.nOf L := even_iff_two_dvd.mp heven
      have h := Nat.pow_sub_one_dvd_pow_sub_one 2 h2
      norm_num at h ⊢
      exact h
    have h3dvdA : 3 ∣ Nat.card A := by
      rw [hcardA]
      exact h3dvd.mul_right _
    have h3mem : 3 ∈ piSet A := ⟨Nat.prime_three, h3dvdA⟩
    let h3 : Ctx19_10 D V₀ V p L A t B 3 := { h with hr := h3mem, hr5 := by norm_num }
    obtain ⟨A₀, hctx22⟩ := h22 p L A t B h3
    let H : Subgroup G := centralizer (A₀ : Set G)
    have hO2 : pCoreOf 2 H = ⊥ := h23 p L A t B A₀ hctx22
    let hctx23 : Ctx19_23 D V₀ V p L A t B 3 A₀ H := ⟨hctx22, rfl, hO2⟩
    have hodd' := h26 p L A t B A₀ H hctx23
    exact (Nat.not_odd_iff_even.mpr heven) hodd'
  · exact hodd

theorem r19_C27 (D : Data G) {V₀ V : Subgroup G}
    (h26 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ V p L A t B r A₀ H),
      R19_26At D V₀ V p L A t B r A₀ H h) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ V p L A t B r A₀ H),
      R19_27At D V₀ V p L A t B r A₀ H h := by
  intro p L A t B r A₀ H h
  exact nineteen_twentyseven D h (h26 p L A t B r A₀ H h)

theorem r19_C28 (D : Data G) {V₀ V : Subgroup G}
    (h26 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ V p L A t B r A₀ H),
      R19_26At D V₀ V p L A t B r A₀ H h)
    (h14 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_14At D V₀ V p L A t B r h)
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_12At D V₀ V p L A t B r h)
    (h3 : S17.R17_3At D V₀ V) (h42 : S17.R17_42At D V₀ V)
    (h638 : UC6.R6_38 D) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h71 : F07.R71 D) (h72 : F07.R72 D)
    (hK25 : K_19_25_torusCent) (hKf : K_19_25_noL2SzSection) (hK28 : K_19_28_torusAutomizer) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ V p L A t B r A₀ H),
      R19_28At D V₀ V p L A t B r A₀ H h := by
  intro p L A t B r A₀ H h
  exact nineteen_twentyeight_of_K D h (h26 p L A t B r A₀ H h)
    (h14 p L A t B r h.ctx22.ctx) (h12 p L A t B r h.ctx22.ctx) h3 h42 h638 hSg h71 h72
    hK25 hKf hK28

theorem r19_C29 (V : LieAutVocab10) (D : Data G) {V₀ Vsub : Subgroup G}
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ Vsub p L A t B r), R19_12At D V₀ Vsub p L A t B r h)
    (h26 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H),
      R19_26At D V₀ Vsub p L A t B r A₀ H h)
    (h27 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H),
      R19_27At D V₀ Vsub p L A t B r A₀ H h)
    (h28 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H),
      R19_28At D V₀ Vsub p L A t B r A₀ H h)
    (hK101 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K101)
    (hK104 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K104 V)
    (hK105 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K105)
    (hcat : K_CatalogModels) (hTits : K_TitsOddPrimes) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H E K S : Subgroup G) (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H),
      R19_29At V D V₀ Vsub p L A t B r A₀ H E K S h := by
  intro p L A t B r A₀ H E K S h
  exact nineteen_twentynine V D h (h12 p L A t B r h.ctx22.ctx)
    (h26 p L A t B r A₀ H h) (h27 p L A t B r A₀ H h) (h28 p L A t B r A₀ H h)
    hK101 hK104 hK105 hcat hTits

theorem r19_Cglue7 (V : LieAutVocab10) (D : Data G) {V₀ Vsub : Subgroup G}
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ Vsub p L A t B r), R19_12At D V₀ Vsub p L A t B r h)
    (h26 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H),
      R19_26At D V₀ Vsub p L A t B r A₀ H h)
    (h27 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H),
      R19_27At D V₀ Vsub p L A t B r A₀ H h)
    (h28 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H : Subgroup G) (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H),
      R19_28At D V₀ Vsub p L A t B r A₀ H h)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h42 : S17.R17_42At D V₀ Vsub) (h661 : S17.R17_66_1At D V₀ Vsub)
    (h49 : W10_4_9) (hsmall : K_19_glue7_L2small)
    (hJR : K_19_JRgen) (hCh2 : Chev2StarGen) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (A₀ H E K S : Subgroup G) (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H)
      (hE : E ≤ A) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
      (hK : K ≤ H) (hKcomp : CFSG.IsComponent (K.subgroupOf H))
      (hfaith : ActsFaithfullyOn V₀ K)
      (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
      (h29 : P19_29 V K E A₀ S),
      R19_glue_7At V D V₀ Vsub p L A t B r A₀ H E K S h hE hEel hEcard hK hKcomp hfaith hS
        h29 := by
  intro p L A t B r A₀ H E K S h hE hEel hEcard hK hKcomp hfaith hS h29
  exact nineteen_glue_seven V D h (h12 p L A t B r h.ctx22.ctx)
    (h26 p L A t B r A₀ H h) (h27 p L A t B r A₀ H h) (h28 p L A t B r A₀ H h)
    (A_le_centralizer_V0 D h.ctx22.ctx h61 h127 h42 h661)
    h49 hsmall hJR hCh2 hE hEel hEcard hK hKcomp hfaith hS h29

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
