module

public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterDispatch
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTypeA
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

@[expose]
def TypeALane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hA : 1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i)

@[expose]
def InnerLane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hnA : ¬ (1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i)

@[expose]
def OuterDHighLane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hD : 5 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        2 * compRank (componentRoots (famCharHom a) i) *
          (compRank (componentRoots (famCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i)

@[expose]
def OuterDFourLane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) = 4)
    (hc : (componentRoots (famCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i)

@[expose]
def OuterELane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hE : 6 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (famCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i)

@[expose]
def LangFamRatCompFieldLenSL :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (ι : Type) (a : ι → Fin τ.rank → Lˣ),
      (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) → (∀ u j, a u j ^ p = 1) →
      (∃ u, rootDiagUnit τ (a u) ≠ 1) → ∀ i : KernelComponent (famCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) →
        CFSG.StandardType.GGCompFieldAtSL
          (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
          (rationalComponentM S.ρ S.Γ (famCharHom a) i)

inductive FamLaneCase
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) (i : KernelComponent (famCharHom a)) : Prop where
  | typeA (hA : 1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)) : FamLaneCase S a i
  | inner (hnA : ¬ (1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) : FamLaneCase S a i
  | outerDHigh (hD : 5 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        2 * compRank (componentRoots (famCharHom a) i) *
          (compRank (componentRoots (famCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) : FamLaneCase S a i
  | outerDFour (hr : compRank (componentRoots (famCharHom a) i) = 4)
    (hc : (componentRoots (famCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) : FamLaneCase S a i
  | outerE (hτ : τ = .E7 ∨ τ = .E8)
    (hE : 6 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (famCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) : FamLaneCase S a i

theorem fam_lane_cases
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a)) :
    FamLaneCase S a i := by
  classical
  by_cases hA : 1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)
  · exact .typeA hA
  by_cases hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])
  · exact .inner hA hinner
  have hD : 4 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        2 * compRank (componentRoots (famCharHom a) i) *
          (compRank (componentRoots (famCharHom a) i) - 1) →
      FamLaneCase S a i := fun hD => by
    by_cases h5 : 5 ≤ compRank (componentRoots (famCharHom a) i)
    · exact .outerDHigh ⟨h5, hD.2⟩ hinner
    · have hr4 : compRank (componentRoots (famCharHom a) i) = 4 := by
        have := hD.1; omega
      exact .outerDFour hr4 (by rw [hD.2, hr4]) hinner
  obtain ⟨N, b, j, hN, hN2, hbN, hsel⟩ :=
    exists_isolating_element hτ a hp hp2 hap i
  have hpN : (N : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hN (by rw [ringChar.eq L 2]; exact Ne.symm hN2)
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hN hpN hbN j
    rw [hsel] at hroots hrank hncard
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD'
    · obtain ⟨u, hu⟩ := h1
      have hrk : Tag.E6.rank = 6 := rfl
      have hc6 : c.length = 6 := by
        have h6 := hE'.1
        rw [hrank] at h6
        omega
      have h72 : kacCount Tag.E6 kacE6.θ
          ((c.map (idxNode (r := Tag.E6.rank))).toFinset) = 72 := by
        rw [← hncard, hE'.2, hrank, hc6]
        rfl
      have hCp : ∃ y, y ∉ (c.map (idxNode (r := Tag.E6.rank))).toFinset := by
        by_contra hcon
        push Not at hcon
        have h1' : (c.map (idxNode (r := Tag.E6.rank))).toFinset = Finset.univ :=
          Finset.eq_univ_of_forall hcon
        have h2 := e6_card c hc
        rw [h1', Finset.card_univ, Fintype.card_option, Fintype.card_fin, hc6] at h2
        omega
      have hsimple : ∀ k, (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈
          componentRoots (famCharHom a) i := by
        intro k
        rw [hroots]
        refine ⟨v⁻¹ • Pi.single k 1, ?_, smul_inv_smul v _⟩
        exact mem_rootsOf_of_kacTest_all kacE6 facts_E6 hCp
          (e6_allRoots c hc hc6 h72) (IsRoot.smul (isRoot_single _ k) v⁻¹)
      obtain ⟨iu, hiu⟩ := exists_componentRoots_superset (χ := famCharHom a)
        (χ' := rootCharHom (a u)) i (fun γ hγ => by
          obtain ⟨h1γ, h2γ⟩ := (mem_kernelRoots_famChar a).1 hγ.1
          rw [kernelRoots_rootCharHom]
          exact ⟨h1γ, h2γ u⟩)
      exact (hu (eq_one_of_simple_mem_class iu (fun k => hiu (hsimple k)))).elim
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hN hpN hbN j
    rw [hsel] at hrank hncard
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD'
    · exact .outerE (Or.inl rfl) hE' hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hN hpN hbN j
    rw [hsel] at hrank hncard
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD'
    · exact .outerE (Or.inr rfl) hE' hinner

theorem langFamRatCompFieldLenSL_of_lanes
    (hTypeA : TypeALane) (hInner : InnerLane) (hDHigh : OuterDHighLane)
    (hDFour : OuterDFourLane) (hE : OuterELane) :
    LangFamRatCompFieldLenSL := by
  intro τ L _ _ _ p₀ S hτ p hp hp2 ι a hT hap h1 i hq
  rcases fam_lane_cases hτ S hp hp2 hT hap h1 i with
    ⟨hA⟩ | ⟨hnA, hinner⟩ | ⟨hD, hout⟩ | ⟨hr, hc, hout⟩ | ⟨hτ', hE', hout⟩
  · exact hTypeA hτ S hp hT hap h1 i hA hq
  · exact hInner hτ S hp hT hap h1 i hnA hinner hq
  · exact hDHigh hτ S hp hT hap h1 i hD hout hq
  · exact hDFour hτ S hp hp2 hT hap i hr hc hout hq
  · exact hE hτ' S hp hp2 hT hap i hE' hout hq

end CFSG.StandardType.TableCRes
