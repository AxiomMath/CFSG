module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

@[expose] def K_BorelTorusAbelianAt (t : StatedLieTag) (m f : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], LieModel (K ⧸ Subgroup.center K) t m 2 f →
    CFSG.Open.IsQuasisimple K → ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
      IsMulCommutative (normalizerQuotient S)

@[expose] def K_BorelTorusAbelianOn (P : StatedLieTag → ℕ → ℕ → Prop) : Prop :=
  ∀ (t : StatedLieTag) (m f : ℕ), P t m f → K_BorelTorusAbelianAt t m f

@[expose] def K_BorelTorusAbelianRankTwoNotL34 : Prop :=
  K_BorelTorusAbelianOn fun t m f =>
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m ≤ 2 ∧
      ¬ (t = .PSL ∧ m = 3 ∧ f = 2)

@[expose] def K_BorelTorusAbelianRankTwo : Prop :=
  K_BorelTorusAbelianOn fun t m _ =>
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m ≤ 2

@[expose] def K_BorelTorusAbelianRankThreeNotU62 : Prop :=
  K_BorelTorusAbelianOn fun t m f =>
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m = 3 ∧
      ¬ (t = .PSU ∧ m = 6 ∧ f = 1)

@[expose] def K_BorelTorusAbelianRankGeFour : Prop :=
  K_BorelTorusAbelianOn fun t m _ =>
    4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m

@[expose] def K_BorelTorusAbelian_OmegaMinusEight : Prop :=
  ∀ f : ℕ, K_BorelTorusAbelianAt .POmegaMinus 4 f

@[expose] def BorelChevOver (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (t : StatedLieTag) (m : ℕ), LieModel X t m 2 n ∧ K_BorelTorusAbelianAt t m n

theorem K_BorelTorusAbelian.at (h : K_BorelTorusAbelian) (t : StatedLieTag) (m f : ℕ) :
    K_BorelTorusAbelianAt t m f :=
  fun K _ _ hLM hq S hS => h K t m f hLM.admissible hLM hq S hS

theorem K_BorelTorusAbelian.toOn (h : K_BorelTorusAbelian) (P : StatedLieTag → ℕ → ℕ → Prop) :
    K_BorelTorusAbelianOn P :=
  fun t m f _ => h.at t m f

theorem K_BorelTorusAbelianOn.mono {P Q : StatedLieTag → ℕ → ℕ → Prop}
    (h : K_BorelTorusAbelianOn Q) (hPQ : ∀ t m f, P t m f → Q t m f) :
    K_BorelTorusAbelianOn P :=
  fun t m f hP => h t m f (hPQ t m f hP)

theorem K_BorelTorusAbelianRankTwo.notL34 (h : K_BorelTorusAbelianRankTwo) :
    K_BorelTorusAbelianRankTwoNotL34 :=
  K_BorelTorusAbelianOn.mono h fun _ _ _ h => h.1

theorem K_BorelTorusAbelian.rankGeFour (h : K_BorelTorusAbelian) :
    K_BorelTorusAbelianRankGeFour :=
  h.toOn _

theorem BorelChevOver.of_chev {X : Type} [Group X] {n : ℕ} (hK3 : K_BorelTorusAbelian)
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CIsChevOver X n) :
    BorelChevOver X n := by
  obtain ⟨t, m, -, hLM⟩ := h
  exact ⟨t, m, hLM, hK3.at t m n⟩

theorem BorelChevOver.of_on {P : StatedLieTag → ℕ → ℕ → Prop} (hK3 : K_BorelTorusAbelianOn P)
    {X : Type} [Group X] {t : StatedLieTag} {m n : ℕ} (hLM : LieModel X t m 2 n)
    (hP : P t m n) : BorelChevOver X n :=
  ⟨t, m, hLM, hK3 t m n hP⟩

@[expose] def K_CartanRankAt (t : StatedLieTag) (m f : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], LieModel (K ⧸ Subgroup.center K) t m 2 f →
    CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
    ∀ S : Subgroup K, IsSylowTwoOf S ⊤ → ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ f - 1 →
      (t = .PSL → ¬ r ∣ m) → (t = .E6 → r ≠ 3) →
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m ≤
          CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S))

@[expose] def K_CartanRankOn (P : StatedLieTag → ℕ → ℕ → Prop) : Prop :=
  ∀ (t : StatedLieTag) (m f : ℕ), P t m f → K_CartanRankAt t m f

@[expose] def K_CartanRankLeThree : Prop :=
  K_CartanRankOn fun t m _ => CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m ≤ 3

theorem K_CartanRank.at (h : K_CartanRank) (t : StatedLieTag) (m f : ℕ) :
    K_CartanRankAt t m f :=
  fun K _ _ hLM hq hodd S hS r hr hr2 hrd hPSL hE6 =>
    h K t m f hLM.admissible hLM hq hodd S hS r hr hr2 hrd hPSL hE6

theorem K_CartanRank.leThree (h : K_CartanRank) : K_CartanRankLeThree :=
  fun t m f _ => h.at t m f

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem Ctx17_42.borelChevOver {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    {P : StatedLieTag → ℕ → ℕ → Prop} (hK3 : Inputs1719.K_BorelTorusAbelianOn P)
    (hP : ∀ t m, CS17LieRank t m = l → P t m n) :
    Inputs1719.BorelChevOver (BarInf L) n := by
  obtain ⟨t, m, -, hmodel, hrank⟩ := ctx.rank
  exact Inputs1719.BorelChevOver.of_on hK3 hmodel (hP t m hrank)

@[expose] def R17_44_1AtB (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → ∀ f : ℕ, Inputs1719.BorelChevOver (BarInf L) f →
      ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r Dc ≤ 3

@[expose] def R17_44_2AtB (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → ∀ f : ℕ, Inputs1719.BorelChevOver (BarInf L) f →
      ∀ r : ℕ, r.Prime → 5 < r →
        (evenRank G = 3 ∨ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M) →
          CFSG.Open.pRank r Dc ≤ 2

@[expose] def R17_44_3AtB (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l : ℕ) (C Dc : Subgroup G) (Gamma : Set G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma → ∀ f : ℕ, Inputs1719.BorelChevOver (BarInf L) f →
      CFSG.Open.pRank 3 Dc ≤ 2 ∧
        ((D.k = 1 ∨ 2 < CFSG.Open.pRank 3 X) → CFSG.Open.pRank 3 Dc ≤ 1)

theorem R17_44_1At.toB {D : Data G} {V₀ V : Subgroup G} (h : R17_44_1At D V₀ V) :
    R17_44_1AtB D V₀ V :=
  fun L X p n l C Dc Gamma ctx _ _ => h L X p n l C Dc Gamma ctx

theorem R17_44_2At.toB {D : Data G} {V₀ V : Subgroup G} (h : R17_44_2At D V₀ V) :
    R17_44_2AtB D V₀ V :=
  fun L X p n l C Dc Gamma ctx _ _ => h L X p n l C Dc Gamma ctx

theorem R17_44_3At.toB {D : Data G} {V₀ V : Subgroup G} (h : R17_44_3At D V₀ V) :
    R17_44_3AtB D V₀ V :=
  fun L X p n l C Dc Gamma ctx _ _ => h L X p n l C Dc Gamma ctx

theorem R17_44_1AtB.toAt {D : Data G} {V₀ V : Subgroup G} (h : R17_44_1AtB D V₀ V)
    (hK3 : Inputs1719.K_BorelTorusAbelian) : R17_44_1At D V₀ V :=
  fun L X p n l C Dc Gamma ctx =>
    h L X p n l C Dc Gamma ctx n (Inputs1719.BorelChevOver.of_chev hK3 ctx.chev)

theorem R17_44_2AtB.toAt {D : Data G} {V₀ V : Subgroup G} (h : R17_44_2AtB D V₀ V)
    (hK3 : Inputs1719.K_BorelTorusAbelian) : R17_44_2At D V₀ V :=
  fun L X p n l C Dc Gamma ctx =>
    h L X p n l C Dc Gamma ctx n (Inputs1719.BorelChevOver.of_chev hK3 ctx.chev)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
