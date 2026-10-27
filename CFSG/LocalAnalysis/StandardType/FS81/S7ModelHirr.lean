module

public import CFSG.LocalAnalysis.SeitzReduction.EnKLHeis
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

section Shift

variable (K : Type) [Field K]

@[expose] def shiftRoot (γ : Fin Tag.E8.rank → ℤ) (f : (Fin Tag.E8.rank → ℤ) → K) :
    (Fin Tag.E8.rank → ℤ) → K :=
  fun ν => if ν ∈ rootFinset .E8 then f (ν - γ) else 0

variable {K}

@[expose] def SupportedDeg1 (g : (Fin Tag.E8.rank → ℤ) → K) : Prop :=
  ∀ ν, g ν ≠ 0 → ν ∈ rootFinset .E8 ∧ ν 7 = 1

theorem shiftRoot_single {γ μ : Fin Tag.E8.rank → ℤ} (h : μ + γ ∈ rootFinset .E8) :
    shiftRoot K γ (Pi.single μ (1 : K)) = Pi.single (μ + γ) 1 := by
  funext ν
  simp only [shiftRoot, Pi.single_apply]
  by_cases hν : ν = μ + γ
  · subst hν
    simp [h]
  · have h' : ν - γ ≠ μ := fun e => hν (by rw [← e]; abel)
    simp [hν, h']

theorem pos_sum_of_deg_one : ∀ ν ∈ rootFinset .E8, ν 7 = 1 → 0 < ∑ i, ν i := by decide +kernel

open Classical in
noncomputable def hgt (g : (Fin Tag.E8.rank → ℤ) → K) : ℕ :=
  ((rootFinset .E8).filter fun ν => g ν ≠ 0).sup fun ν => (∑ i, ν i).toNat

open Classical in
theorem le_hgt {g : (Fin Tag.E8.rank → ℤ) → K} {ν : Fin Tag.E8.rank → ℤ}
    (hν : ν ∈ rootFinset .E8) (h : g ν ≠ 0) : (∑ i, ν i).toNat ≤ hgt g :=
  Finset.le_sup (f := fun ν => (∑ i, ν i).toNat) (Finset.mem_filter.2 ⟨hν, h⟩)

open Classical in
theorem hgt_lt_of_forall {g : (Fin Tag.E8.rank → ℤ) → K} {n : ℕ} (hn : 0 < n)
    (h : ∀ ν ∈ rootFinset .E8, g ν ≠ 0 → (∑ i, ν i).toNat < n) : hgt g < n :=
  (Finset.sup_lt_iff hn).2 fun ν hν => h ν (Finset.mem_filter.1 hν).1 (Finset.mem_filter.1 hν).2

theorem supportedDeg1_shift_neg {j : Fin Tag.E8.rank} (hj : j ≠ 7)
    {g : (Fin Tag.E8.rank → ℤ) → K} (hg : SupportedDeg1 g) :
    SupportedDeg1 (shiftRoot K (-Pi.single j 1) g) := by
  intro ν hν
  simp only [shiftRoot] at hν
  by_cases hΦ : ν ∈ rootFinset .E8
  · rw [if_pos hΦ] at hν
    obtain ⟨-, h7⟩ := hg _ hν
    refine ⟨hΦ, ?_⟩
    simpa [Pi.single_apply, hj] using h7
  · rw [if_neg hΦ] at hν
    exact absurd rfl hν

theorem single_mem_of_lowering (hK : Nat.card K = 2)
    (hroot : ∀ μ ∈ rootFinset .E8, μ 7 = 1 → μ ≠ Pi.single 7 1 →
      ∃ j : Fin Tag.E8.rank, j ≠ 7 ∧ μ - Pi.single j 1 ∈ rootFinset .E8)
    (W : AddSubgroup ((Fin Tag.E8.rank → ℤ) → K))
    (hlow : ∀ j : Fin Tag.E8.rank, j ≠ 7 → ∀ f ∈ W, shiftRoot K (-Pi.single j 1) f ∈ W)
    {f : (Fin Tag.E8.rank → ℤ) → K} (hf : f ∈ W) (hf0 : f ≠ 0) (hs : SupportedDeg1 f) :
    Pi.single (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (1 : K) ∈ W := by
  classical
  have hK01 : ∀ c : K, c ≠ 0 → c = 1 := fun c hc =>
    ((Nat.card_eq_two_iff' (0 : K)).1 hK).unique hc one_ne_zero
  suffices H : ∀ n : ℕ, ∀ g ∈ W, g ≠ 0 → SupportedDeg1 g → hgt g = n →
      Pi.single (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (1 : K) ∈ W from
    H _ f hf hf0 hs rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg hg0 hgs hn
    by_cases hall : ∀ j : Fin Tag.E8.rank, j ≠ 7 → shiftRoot K (-Pi.single j 1) g = 0
    ·
      have hsupp : ∀ ν, g ν ≠ 0 → ν = Pi.single 7 1 := by
        intro ν hν
        by_contra hne
        obtain ⟨hνΦ, hν7⟩ := hgs ν hν
        obtain ⟨j, hj, hjΦ⟩ := hroot ν hνΦ hν7 hne
        have h0 := congrFun (hall j hj) (ν - Pi.single j 1)
        simp only [shiftRoot, if_pos hjΦ, Pi.zero_apply] at h0
        have : ν - Pi.single j 1 - -Pi.single j 1 = ν := by abel
        rw [this] at h0
        exact hν h0
      obtain ⟨ν₀, hν₀⟩ : ∃ ν, g ν ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hg0 (funext hcon)
      have h0 := hsupp ν₀ hν₀
      subst h0
      have hone : g (Pi.single 7 1) = 1 := hK01 _ hν₀
      have : g = Pi.single (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (1 : K) := by
        funext ν
        by_cases hν : ν = Pi.single 7 1
        · subst hν; simp [hone]
        · rw [Pi.single_apply, if_neg hν]
          by_contra hne
          exact hν (hsupp ν hne)
      rw [← this]
      exact hg
    · push Not at hall
      obtain ⟨j, hj, hne⟩ := hall
      refine ih _ ?_ _ (hlow j hj g hg) hne (supportedDeg1_shift_neg hj hgs) rfl
      rw [← hn]
      obtain ⟨ν₀, hν₀⟩ : ∃ ν, g ν ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hg0 (funext hcon)
      obtain ⟨hν₀Φ, hν₀7⟩ := hgs ν₀ hν₀
      have hpos0 : 0 < hgt g :=
        lt_of_lt_of_le (by have := pos_sum_of_deg_one ν₀ hν₀Φ hν₀7; omega) (le_hgt hν₀Φ hν₀)
      refine hgt_lt_of_forall hpos0 fun ν hν hSν => ?_
      have hSν' : g (ν + (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) ≠ 0 := by
        simpa [shiftRoot, hν] using hSν
      obtain ⟨hμΦ, hμ7⟩ := hgs _ hSν'
      have hν7 : ν 7 = 1 := by
        have : (ν + (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) 7 = ν 7 := by
          simp [hj]
        omega
      have hp := pos_sum_of_deg_one ν hν hν7
      have hle := le_hgt hμΦ hSν'
      have hsum : ∑ i, (ν + (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) i = ∑ i, ν i + 1 := by
        simp [Finset.sum_add_distrib, Pi.single_apply]
      rw [hsum] at hle
      omega

theorem single_mem_of_raising
    (hroot : ∀ μ ∈ rootFinset .E8, μ 7 = 1 → μ ≠ Pi.single 7 1 →
      ∃ j : Fin Tag.E8.rank, j ≠ 7 ∧ μ - Pi.single j 1 ∈ rootFinset .E8)
    (W : AddSubgroup ((Fin Tag.E8.rank → ℤ) → K))
    (hhigh : ∀ j : Fin Tag.E8.rank, j ≠ 7 → ∀ f ∈ W, shiftRoot K (Pi.single j 1) f ∈ W)
    (hbot : Pi.single (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (1 : K) ∈ W) :
    ∀ ν ∈ rootFinset .E8, ν 7 = 1 → Pi.single ν (1 : K) ∈ W := by
  suffices H : ∀ n : ℕ, ∀ ν ∈ rootFinset .E8, ν 7 = 1 → (∑ i, ν i).toNat = n →
      Pi.single ν (1 : K) ∈ W from fun ν hν h7 => H _ ν hν h7 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ν hν h7 hn
    by_cases hα : ν = Pi.single 7 1
    · rw [hα]; exact hbot
    · obtain ⟨j, hj, hjΦ⟩ := hroot ν hν h7 hα
      have hμ7 : (ν - (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) 7 = 1 := by
        simp [hj, h7]
      have hp := pos_sum_of_deg_one ν hν h7
      have hsum : ∑ i, (ν - (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) i = ∑ i, ν i - 1 := by
        simp [Finset.sum_sub_distrib, Pi.single_apply]
      have hlt : (∑ i, (ν - (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) i).toNat < n := by
        rw [hsum, ← hn]
        omega
      have h1 := ih _ hlt (ν - (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) hjΦ hμ7 rfl
      have h2 := hhigh j hj _ h1
      rw [shiftRoot_single (by simpa using hν), sub_add_cancel] at h2
      exact h2

end Shift

section Coord

variable {K : Type} [Field K]

theorem mem_Qθ_of_mem_highRadical_E8 {x : adjointGroup .E8 K} (hx : x ∈ EPilot.highRadical .E8 K) :
    (x : ModGL .E8 K) ∈ Qθ .E8 K := hx

noncomputable def coordGroup (V : Subgroup (adjointGroup .E8 K))
    (hV : V ≤ EPilot.highRadical .E8 K) : AddSubgroup ((Fin Tag.E8.rank → ℤ) → K) where
  carrier := {f | ∃ v ∈ V, heisCoord .E8 K (v : ModGL .E8 K) = f}
  zero_mem' := ⟨1, one_mem V, heisCoord_one⟩
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v * w, mul_mem hv hw,
      (heisCoord_spec .E8 K).mul _ (mem_Qθ_of_mem_highRadical_E8 (hV hv)) _
        (mem_Qθ_of_mem_highRadical_E8 (hV hw))⟩
  neg_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v⁻¹, inv_mem hv, heisCoord_inv (mem_Qθ_of_mem_highRadical_E8 (hV hv))⟩

theorem supportedDeg1_heisCoord {q : ModGL .E8 K} (hq : q ∈ Qθ .E8 K) :
    SupportedDeg1 (heisCoord .E8 K q) := by
  intro ν hν
  by_contra hcon
  refine hν ((heisCoord_spec .E8 K).support q hq ν ?_)
  intro hD
  exact hcon ⟨mem_rootFinset.2 hD.1, hD.2⟩

variable [CharP K 2]

theorem shiftRoot_mem_coordGroup {V : Subgroup (adjointGroup .E8 K)}
    {hV : V ≤ EPilot.highRadical .E8 K}
    (hN : EPilot.perpLevi .E8 K ≤ Subgroup.normalizer (V : Set (adjointGroup .E8 K)))
    {γ : Fin Tag.E8.rank → ℤ} (hD : γ ∈ EPilot.perpRoots .E8)
    {f : (Fin Tag.E8.rank → ℤ) → K} (hf : f ∈ coordGroup V hV) :
    shiftRoot K γ f ∈ coordGroup V hV := by
  obtain ⟨v, hv, rfl⟩ := hf
  have hd := hN (EPilot.pinnedElt_mem_perpLevi (K := K) hD 1)
  have hu : EPilot.pinnedElt .E8 γ (1 : K) * v * (EPilot.pinnedElt .E8 γ (1 : K))⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hd v).1 hv
  have key := (EPilot.heisCoord_conj_pinnedX_of_deg_zero (Or.inr (Or.inr rfl)) hD.1 hD.2 (1 : K)
    (mem_Qθ_of_mem_highRadical_E8 (hV hv))).2
  have hshift : shiftRoot K γ (heisCoord .E8 K (v : ModGL .E8 K)) =
      heisCoord .E8 K ((EPilot.pinnedElt .E8 γ (1 : K) * v *
        (EPilot.pinnedElt .E8 γ (1 : K))⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) -
        heisCoord .E8 K (v : ModGL .E8 K) := by
    funext ν
    rw [Pi.sub_apply, show ((EPilot.pinnedElt .E8 γ (1 : K) * v *
        (EPilot.pinnedElt .E8 γ (1 : K))⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) =
        pinnedX .E8 K γ 1 * (v : ModGL .E8 K) * (pinnedX .E8 K γ 1)⁻¹ from rfl, key ν]
    simp [shiftRoot]
  rw [hshift]
  exact sub_mem ⟨_, hu, rfl⟩ ⟨v, hv, rfl⟩

omit [CharP K 2] in
theorem mem_zpowers_of_heisCoord_eq_zero (hK : Nat.card K = 2) {q : adjointGroup .E8 K}
    (hq : q ∈ EPilot.highRadical .E8 K) (h : heisCoord .E8 K (q : ModGL .E8 K) = 0) :
    q ∈ Subgroup.zpowers (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)) := by
  have hU : (q : ModGL .E8 K) ∈ Uθ .E8 K :=
    ((heisCoord_spec .E8 K).eq_zero_iff _ (mem_Qθ_of_mem_highRadical_E8 hq)).1 h
  obtain ⟨c, hc⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.1 hU
  by_cases hc0 : c = 0
  · subst hc0
    rw [pinnedX_zero] at hc
    have hq1 : q = 1 := Subtype.ext hc.symm
    rw [hq1]
    exact one_mem _
  · have hc1 : c = 1 := ((Nat.card_eq_two_iff' (0 : K)).1 hK).unique hc0 one_ne_zero
    subst hc1
    have hqt : EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) = q := Subtype.ext hc
    rw [← hqt]
    exact Subgroup.mem_zpowers _

theorem eq_zpowers_or_eq_highRadical (hK : Nat.card K = 2) {V : Subgroup (adjointGroup .E8 K)}
    (h1 : Subgroup.zpowers (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)) ≤ V)
    (h2 : V ≤ EPilot.highRadical .E8 K)
    (hN : EPilot.perpLevi .E8 K ≤ Subgroup.normalizer (V : Set (adjointGroup .E8 K))) :
    V = Subgroup.zpowers (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)) ∨
      V = EPilot.highRadical .E8 K := by
  classical
  have hK01 : ∀ c : K, c ≠ 0 → c = 1 := fun c hc =>
    ((Nat.card_eq_two_iff' (0 : K)).1 hK).unique hc one_ne_zero
  have hroot := EPilot.exists_sub_single_mem_rootFinset_of_deg_one (τ := .E8) (Or.inr (Or.inr rfl))
  by_cases hV : ∀ v ∈ V, heisCoord .E8 K (v : ModGL .E8 K) = 0
  · exact Or.inl (le_antisymm
      (fun v hv => mem_zpowers_of_heisCoord_eq_zero hK (h2 hv) (hV v hv)) h1)
  · right
    push Not at hV
    obtain ⟨v₀, hv₀, hne⟩ := hV
    have hW₀ : heisCoord .E8 K (v₀ : ModGL .E8 K) ∈ coordGroup V h2 := ⟨v₀, hv₀, rfl⟩
    have hlow : ∀ j : Fin Tag.E8.rank, j ≠ 7 → ∀ f ∈ coordGroup V h2,
        shiftRoot K (-Pi.single j 1) f ∈ coordGroup V h2 := fun j hj f hf =>
      shiftRoot_mem_coordGroup hN (EPilot.neg_single_mem_perpRoots hj) hf
    have hhigh : ∀ j : Fin Tag.E8.rank, j ≠ 7 → ∀ f ∈ coordGroup V h2,
        shiftRoot K (Pi.single j 1) f ∈ coordGroup V h2 := fun j hj f hf =>
      shiftRoot_mem_coordGroup hN (EPilot.single_mem_perpRoots hj) hf
    have hbot := single_mem_of_lowering hK hroot (coordGroup V h2) hlow hW₀ hne
      (supportedDeg1_heisCoord (mem_Qθ_of_mem_highRadical_E8 (h2 hv₀)))
    have hall := single_mem_of_raising hroot (coordGroup V h2) hhigh hbot
    refine le_antisymm h2 (fun q hq => ?_)
    set c := heisCoord .E8 K (q : ModGL .E8 K) with hcdef
    have hcs : SupportedDeg1 c := supportedDeg1_heisCoord (mem_Qθ_of_mem_highRadical_E8 hq)
    have hcW : c ∈ coordGroup V h2 := by
      have hc : c = ∑ ν ∈ (rootFinset .E8).filter (fun ν => c ν ≠ 0),
          (Pi.single ν (1 : K) : (Fin Tag.E8.rank → ℤ) → K) := by
        funext μ
        rw [Finset.sum_apply]
        simp only [Pi.single_apply]
        rw [Finset.sum_ite_eq]
        by_cases hμ : c μ = 0
        · have hnm : μ ∉ (rootFinset .E8).filter (fun ν => c ν ≠ 0) := fun h =>
            (Finset.mem_filter.1 h).2 hμ
          rw [if_neg hnm, hμ]
        · rw [if_pos (Finset.mem_filter.2 ⟨(hcs μ hμ).1, hμ⟩), hK01 _ hμ]
      rw [hc]
      refine AddSubgroup.sum_mem _ fun ν hν => ?_
      obtain ⟨hνΦ, hμ⟩ := Finset.mem_filter.1 hν
      exact hall ν hνΦ (hcs ν hμ).2
    obtain ⟨v, hv, hvq⟩ := hcW
    have hqv : heisCoord .E8 K ((q * v⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) = 0 := by
      have hmul := (heisCoord_spec .E8 K).mul _ (mem_Qθ_of_mem_highRadical_E8 hq) _
        (inv_mem (mem_Qθ_of_mem_highRadical_E8 (h2 hv)))
      rw [show ((q * v⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) = (q : ModGL .E8 K) * (v : ModGL .E8 K)⁻¹
        from rfl, hmul, heisCoord_inv (mem_Qθ_of_mem_highRadical_E8 (h2 hv)), hvq, ← hcdef]
      exact add_neg_cancel _
    have hmem : q * v⁻¹ ∈ Subgroup.zpowers (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)) :=
      mem_zpowers_of_heisCoord_eq_zero hK (mul_mem hq (inv_mem (h2 hv))) hqv
    have hqeq : q = (q * v⁻¹) * v := by group
    rw [hqeq]
    exact mul_mem (h1 hmem) hv

end Coord

end CFSG.StandardType.FrameRoute.FS81
