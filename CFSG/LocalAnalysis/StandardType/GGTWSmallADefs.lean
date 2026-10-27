module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallAClose
public import CFSG.LocalAnalysis.StandardType.GGTWSmallAKClose
public import CFSG.LocalAnalysis.StandardType.GGTWSmallCarried
public import CFSG.LocalAnalysis.StandardType.GGTWSmallRowdata
public import CFSG.LocalAnalysis.StandardType.GGTWSmallRowdataK
public import CFSG.LocalAnalysis.StandardType.GGTWSmallRowdataLrow
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Defs
public import CFSG.LocalAnalysis.StandardType.GGPZMultA
public import CFSG.LocalAnalysis.StandardType.GGPZMultTwA
public import CFSG.LocalAnalysis.StandardType.GGPZMultD4
public import CFSG.LocalAnalysis.StandardType.GGTWAlignOne
public import CFSG.LocalAnalysis.StandardType.GGTWAlignTwo
public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithG1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithF2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResTwoNodeDepSmallAInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmallJA p J L ∧ x ∉ L) ∨ (GGResRowAt ggRowTwoNodeSmallJA p J K ∧ y ∉ K)

@[expose] def GGResTwoNodeDepSmallEInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmallJD p J L ∧ x ∉ L) ∨ (GGResRowAt ggRowTwoNodeSmallJD p J K ∧ y ∉ K)

theorem GGResRowAt.smallA_or_E {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowTwoNodeSmall p J X) :
    GGResRowAt ggRowTwoNodeSmallJA p J X ∨ GGResRowAt ggRowTwoNodeSmallJD p J X := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := h
  have hcases : (labJ.tag = .A ∨ labJ.tag = .twA) ∨ labJ.tag = .D := by
    obtain ⟨hrow, -⟩ := hr
    rcases hrow with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (by rw [h1])
    · exact Or.inr (by rw [h1])
  rcases hcases with hA | hD
  · exact Or.inl ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr, hA⟩
  · exact Or.inr ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr, hD⟩

theorem ggResTwoNodeDepSmallInput_of_A_E (hA : GGResTwoNodeDepSmallAInput)
    (hE : GGResTwoNodeDepSmallEInput) : GGResTwoNodeDepSmallInput := by
  intro G _ _ p B Bs x L D J y K hH hp hF hS hE' hP
  rcases hP with ⟨hrowL, hxL⟩ | ⟨hrowK, hyK⟩
  · rcases GGResRowAt.smallA_or_E hrowL with h | h
    · exact hA G p B Bs x L D J y K hH hF hS hE' (Or.inl ⟨h, hxL⟩)
    · exact hE G p B Bs x L D J y K hH hF hS hE' (Or.inl ⟨h, hxL⟩)
  · rcases GGResRowAt.smallA_or_E hrowK with h | h
    · exact hA G p B Bs x L D J y K hH hF hS hE' (Or.inr ⟨h, hyK⟩)
    · exact hE G p B Bs x L D J y K hH hF hS hE' (Or.inr ⟨h, hyK⟩)

@[expose] def GGTWMultLeaves : Prop :=
  ∀ (Y : Type) [Group Y] (p : ℕ) [Fact p.Prime] (lab : LargeEvenLabel), p ≠ 2 →
    LargeEvenInLambda2 lab → commutator Y = ⊤ → GGHasLabel lab (Y ⧸ Subgroup.center Y) →
    ((lab.tag = .A ∧ ¬ p ∣ lab.rank + 1) ∨
      (lab.tag = .twA ∧ ¬ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1) ∨
      (p = 3 ∧ lab.tag = .D ∧ lab.rank = 4)) → ¬ p ∣ Nat.card ↥(Subgroup.center Y)

theorem ggTWMultLeaves_holds :
    GGTWMultLeaves := by
  intro Y _ p _ lab hp2 hΛ hperf hlab hcov
  obtain ⟨tag, l, n⟩ := lab
  rcases hcov with ⟨h1, hpl⟩ | ⟨h1, hpl, hpq⟩ | ⟨hp3, h1, h2⟩
  · simp only at h1 hpl
    subst h1
    exact ggPZMult_A hp2 hΛ hperf hlab hpl
  · simp only at h1 hpl hpq
    subst h1
    exact ggPZMult_twA hp2 hΛ hperf hlab hpq hpl
  · simp only at h1 h2
    subst h1 h2 hp3
    exact ggPZMult_D4 hΛ hperf hlab

theorem ggTWSmallA_rank_ge {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {labJ labX : LargeEvenLabel}
    (hJΛ : LargeEvenInLambda2 labJ) (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hrow : ggRowTwoNode p labJ labX) : 4 ≤ labX.rank := by
  rcases hrow with ⟨hA, -, hdvd, hXeq⟩ | ⟨hT, -, hdvd, hXeq⟩ | ⟨hJeq, -, -, -⟩ |
    ⟨hJeq, -, -, -⟩
  · rw [hXeq]
    change 4 ≤ labJ.rank + 2
    have hle1 : 1 ≤ labJ.rank := (CFSG.LocalAnalysis.GLTheoremA.inLambda2_A hJΛ hA).2.1
    have hne1 : labJ.rank ≠ 1 := by
      intro h1
      have h4 : p ∣ 2 ^ 2 := by rw [h1] at hdvd; simpa using hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
    omega
  · rw [hXeq]
    change 4 ≤ labJ.rank + 2
    have hle2 : 2 ≤ labJ.rank := (CFSG.LocalAnalysis.GLTheoremA.inLambda2_twA hJΛ hT).2.1
    omega
  · rw [hJeq] at hJtag
    exact absurd hJtag (by simp)
  · rw [hJeq] at hJtag
    exact absurd hJtag (by simp)

theorem ggTWSmallA_row_narrow {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {J L : Subgroup G} (hrow : GGResRowAt ggRowTwoNodeSmallJA p J L) :
    GGResRowAt (fun p J X => ggRowTwoNode p J X ∧ 4 ≤ X.rank ∧ X.rank ≤ 9) p J L := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨⟨hrow2, hle9⟩, hJtag⟩⟩ := hrow
  exact ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrow2,
    ggTWSmallA_rank_ge (Fact.out : p.Prime) hp2 hJΛ hJtag hrow2, hle9⟩

@[expose] def GGTWHKSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N k : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → x ∉ L → y ∉ K →
    (k = 1 ∨ k = 2) → 3 ≤ p → p ∣ N → (N = 5 ∨ N = 6 ∨ N = 9) →
    Nat.card ↥Bs = p ^ (N - 1) → GGTWAligned p N k Bs L J K → GGTWHLAt p Bs K y

@[expose] def GGTWHLSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → y ∉ K →
    3 ≤ p → p ∣ N → (N = 5 ∨ N = 6 ∨ N = 9) → Nat.card ↥Bs = p ^ (N - 1) →
    GGTWAligned p N 1 Bs K J L → GGTWHLAt p Bs L x

theorem ggTWSmall_nonLevi_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTwo : GGResRowAt ggRowTwoNode p J K → GGResTwoNodeSideDatum p Bs K J)
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) (hH : GGResHyp p B Bs x L D J y K)
    (hF : ¬ GGCoxeterForkDatum p Bs L K) (hS : ¬ GGCoxeterStdDatum p Bs L K)
    (hE : ¬ GGE6DepPerpCfg p Bs L K) (h : GGResRowAt ggRowNonLevi p J K) :
    (GGResRowAt ggRowTwoNode p J K ∧ GGResTwoNodeSideDatum p Bs K J) ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases h.cases with h2 | h2 | h2 | h2 | h2 | h2
  · exact Or.inl ⟨h2, hTwo h2⟩
  · exact Or.inr (h6c G p B Bs x L D J y K hH hF hS hE (Or.inr h2))
  · exact Or.inr (h6d G p B Bs x L D J y K hH hF hS hE (Or.inr h2))
  · exact Or.inr (h6e G p B Bs x L D J y K hH hF hS hE (Or.inr h2))
  · exact Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inr h2))
  · exact Or.inr (h6g G p B Bs x L D J y K hH hF hS hE (Or.inr h2))

theorem ggTWSmall_nonLevi_L {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTwo : GGResRowAt ggRowTwoNode p J L → GGResTwoNodeSideDatum p Bs L J)
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) (hH : GGResHyp p B Bs x L D J y K)
    (hF : ¬ GGCoxeterForkDatum p Bs L K) (hS : ¬ GGCoxeterStdDatum p Bs L K)
    (hE : ¬ GGE6DepPerpCfg p Bs L K) (h : GGResRowAt ggRowNonLevi p J L) :
    (GGResRowAt ggRowTwoNode p J L ∧ GGResTwoNodeSideDatum p Bs L J) ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases h.cases with h2 | h2 | h2 | h2 | h2 | h2
  · exact Or.inl ⟨h2, hTwo h2⟩
  · exact Or.inr (h6c G p B Bs x L D J y K hH hF hS hE (Or.inl h2))
  · exact Or.inr (h6d G p B Bs x L D J y K hH hF hS hE (Or.inl h2))
  · exact Or.inr (h6e G p B Bs x L D J y K hH hF hS hE (Or.inl h2))
  · exact Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inl h2))
  · exact Or.inr (h6g G p B Bs x L D J y K hH hF hS hE (Or.inl h2))

theorem ggTWSmall_shapeRow_K (hJ : GGTBJInputR) (hJ2S : GGTBJTwoNodeSmallInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hKs : GGResRowAt ggRowTwoNode p J K → GGResRowAt ggRowTwoNodeSmallJA p J K)
    (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J ∨
      (GGResRowAt ggRowTwoNode p J K ∧ GGResTwoNodeSideDatum p Bs K J) ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
  · rcases (hJ G p B Bs x L D J y K hH).2 hXK with hK | hK3 | hNK
    · exact Or.inl hK
    · exact Or.inr (Or.inl hK3)
    · rcases ggTWSmall_nonLevi_K
          (fun h2 => (hJ2S G p B Bs x L D J y K hH).2 hXK (hKs h2))
          h6c h6d h6e h6f h6g hH hF hS hE hNK with htwo | hweyl
      · exact Or.inr (Or.inr (Or.inl htwo))
      · exact Or.inr (Or.inr (Or.inr hweyl))
  · exact Or.inr (Or.inr (Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inr hSK))))

theorem ggTWSmall_shapeRow_L (hJ : GGTBJInputR) (hJ2S : GGTBJTwoNodeSmallInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hLs : GGResRowAt ggRowTwoNode p J L → GGResRowAt ggRowTwoNodeSmallJA p J L)
    (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J ∨
      (GGResRowAt ggRowTwoNode p J L ∧ GGResTwoNodeSideDatum p Bs L J) ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases (hX G p B Bs x L D J y K hH).1 with hXL | hSL
  · rcases (hJ G p B Bs x L D J y K hH).1 hXL with hL | hL3 | hNL
    · exact Or.inl hL
    · exact Or.inr (Or.inl hL3)
    · rcases ggTWSmall_nonLevi_L
          (fun h2 => (hJ2S G p B Bs x L D J y K hH).1 hXL (hLs h2))
          h6c h6d h6e h6f h6g hH hF hS hE hNL with htwo | hweyl
      · exact Or.inr (Or.inr (Or.inl htwo))
      · exact Or.inr (Or.inr (Or.inr hweyl))
  · exact Or.inr (Or.inr (Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inl hSL))))

end CFSG.StandardType

end
