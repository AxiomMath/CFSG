module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FClassB
public import CFSG.RankThree.PartTwo.Sec8.Hering88FSmall
public import CFSG.RankThree.PartTwo.Sec8.Hering88FRee
public import CFSG.RankThree.PartTwo.Sec8.Hering88EClass

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


@[expose] def ClassBCovered {G : Type} [Group G] [Finite G] (c _b x : G) (_L Y : Subgroup G)
    (n m : ℕ) : Prop :=
  x = c ∧ 2 ≤ n ∧
    (IsoGTwoEven (barCentralizer (Subgroup.zpowers x) Y) m ∨
      (m = 1 ∧ IsoPGUThree (barCentralizer (Subgroup.zpowers x) Y) (2 ^ m)))

namespace Hering88F


theorem classB_covered (h45 : Sec4.Item4_5) (hF : KF84Field) (hG2Two : G2TwoCentThreeSolvable)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hxY : KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField)
    {A₀ : Subgroup G} {d' : G} {m : ℕ} (hodd : Odd m) (hc1 : Case83One Y c A₀ d' m)
    (hcov : ClassBCovered c b c L Y n m)
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdc : d ∉ Subgroup.zpowers c)
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * m))) := by
  obtain ⟨-, hn2, hclause⟩ := hcov
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) :=
    hxY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hZ := center_eq_bot_of_case1 hc1.1
  rcases hclause with hG2 | ⟨hm1, hP⟩
  · rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by have := hodd.pos; omega
      exact (false_of_small h45 hF hG2Two h hn2 hIJ hcN hZ (Or.inl hG2) hdcl hdA hd3 hdN hin
        hne).elim
    · obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
      rcases hcases with ⟨hRee, -⟩ | ⟨-, hKL2⟩
      · exact (false_of_isGammaTypeRee h hn2 hRee hY hIJ hcN hodd hm2 hG2).elim
      · exact classB_x_eq_c h45 hF Hering88C.inputs47ClassesD4_holds h hn2 hKL2 hY hIJ hxY hodd
          hm2 hc1 hG2 hdcl hdc hdA hd3 hdN hin hne
  · subst hm1
    exact (false_of_small h45 hF hG2Two h hn2 hIJ hcN hZ (Or.inr hP) hdcl hdA hd3 hdN hin
      hne).elim

end Hering88F

@[expose] def KF88Case1ClassBSwap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, x = b → x ≠ c →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∀ (A₀ : Subgroup G) (d' : G) (m : ℕ), Odd m → Case83One Y x A₀ d' m →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          Nonempty (imageModTheta Y
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
              projSL 2 (GaloisField 2 (3 * m)))

@[expose] def KF88Case1ClassBOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G), Sec8Pair G A c L a b X 1 →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, x = c →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∀ (A₀ : Subgroup G) (d' : G) (m : ℕ), Odd m → Case83One Y x A₀ d' m →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          Nonempty (imageModTheta Y
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
              projSL 2 (GaloisField 2 (3 * m)))

@[expose] def KF88Case1ClassBPGU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n → 2 ≤ n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, x = c →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∀ (A₀ : Subgroup G) (d' : G) (m : ℕ), Odd m → 2 ≤ m → Case83One Y x A₀ d' m →
      IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) m →
      IsoPGUThree (barCentralizer (Subgroup.zpowers x) Y) (2 ^ m) →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          Nonempty (imageModTheta Y
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
              projSL 2 (GaloisField 2 (3 * m)))

namespace Hering88F


theorem kF88Case1ClassB_of_three (h45 : Sec4.Item4_5) (hF : KF84Field)
    (hG2Two : G2TwoCentThreeSolvable) (hSwap : KF88Case1ClassBSwap) (hOne : KF88Case1ClassBOne)
    (hPGU : KF88Case1ClassBPGU) : KF88Case1ClassB := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY A₀ d' m hodd hc1 d hdcl hdx hdA hd3 hdN hin hne hE
  by_cases hxc : x = c
  · subst hxc
    rcases Nat.lt_or_ge n 2 with hn | hn2
    · obtain rfl : n = 1 := by
        obtain ⟨-, -, hn1, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
        omega
      exact hOne G A x L a b X h Y hY hIJ x rfl hxY A₀ d' m hodd hc1 d hdcl hdx hdA hd3 hdN hin
        hne hE
    · by_cases hcov : ClassBCovered x b x L Y n m
      · exact classB_covered h45 hF hG2Two h hY hIJ hxY hodd hc1 hcov hdcl hdx hdA hd3 hdN hin hne
      · have h3 := hc1.2.2
        rcases h3 with hG2 | ⟨hD4, hP, -⟩
        · exact (hcov ⟨rfl, hn2, Or.inl hG2⟩).elim
        · have hm2 : 2 ≤ m := by
            by_contra hm
            have hm1 : m = 1 := by have := hodd.pos; omega
            exact hcov ⟨rfl, hn2, Or.inr ⟨hm1, hP⟩⟩
          exact hPGU G A x L a b X n h hn2 Y hY hIJ x rfl hxY A₀ d' m hodd hm2 hc1 hD4 hP d hdcl
            hdx hdA hd3 hdN hin hne hE
  · exact hSwap G A c L a b X n h Y hY hIJ x (hx.resolve_left hxc) hxc hxY A₀ d' m hodd hc1 d
      hdcl hdx hdA hd3 hdN hin hne hE

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
