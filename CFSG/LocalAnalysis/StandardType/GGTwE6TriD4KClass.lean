module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KCompLabel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj

public section

namespace CFSG.StandardType.TwE6TriD4K

open CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.RankThree.PartOne.KE (d4Nodes)
open scoped MatrixGroups

theorem d4Perp_check : ((List.range e6Certificate.roots.length).all fun k =>
    ([1, 2, 3, 4] : List (Fin Tag.E6.rank)).any fun j =>
      iform (e6Certificate.root k) (Pi.single j 1) != 0) = true := by
  decide +kernel

theorem kernelRoots_subset_of_d4
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i := by
  intro γ hγ
  by_cases hi : (⟦⟨γ, hγ⟩⟧ : KernelComponent (rootCharHom a)) = i
  · exact ⟨hγ, hi⟩
  exfalso
  have horth : ∀ j ∈ ([1, 2, 3, 4] : List (Fin Tag.E6.rank)),
      iform (v⁻¹ • γ) (Pi.single j 1) = 0 := by
    intro j hj
    have hjJ : j ∈ d4Nodes Tag.E6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
    have hmem : v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      refine ⟨_, ⟨IsRoot.basis j, fun k hk => ?_⟩, rfl⟩
      rw [Pi.single_apply, if_neg (show k ≠ j from fun e => hk (e ▸ hjJ))]
    obtain ⟨hβ, hβi⟩ := hmem
    have h0 : iform γ (v • Pi.single j 1) = 0 := by
      by_contra hne
      exact hi ((mk_eq_of_iform_ne_zero (α := ⟨γ, hγ⟩) (β := ⟨_, hβ⟩) hne).trans hβi)
    rw [← iform_smul v, smul_inv_smul]
    exact h0
  obtain ⟨k, hk, hkb⟩ := RootCertificate.exists_root_eq e6Certificate_check (IsRoot.smul hγ.1 v⁻¹)
  have hc := d4Perp_check
  rw [List.all_eq_true] at hc
  have hck := hc k (List.mem_range.2 hk)
  rw [hkb, List.any_eq_true] at hck
  obtain ⟨j, hj, hne⟩ := hck
  exact (bne_iff_ne.1 hne) (horth j hj)

theorem exists_theta_of_component_triD4
    {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3n : 3 ∣ 2 ^ n + 1) (S : LangSetup Tag.E6 (AlgebraicClosure K) 5) (hSq : S.D.q = 2 ^ n)
    (hΦ : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (2 ^ n)) ∧
      S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hinj : Function.Injective ι) (hrange : ι.range = S.Γ) (h : ↥(twistedE6InndiagGL K σ))
    (hconj : ∀ c, ι (twistedE6InndiagConj K σ h c) =
      rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (J : Subgroup ↥(twistedE6RootGroup K σ))
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (twistedE6InndiagConj K σ h)))
    (hlab : GGHasLabel (⟨.triD4, 0, n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    ∃ (v u : WeylGroup Tag.E6) (π : Equiv.Perm (Fin Tag.E6.rank)),
      u ∈ parabolicWeylGroup Tag.E6 (d4Set Tag.E6) ∧
      (π = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
        π = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2]) ∧
      ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), v⁻¹ • S.ρ (v • α) = u • permLattice π α := by
  classical
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne
      Nat.prime_three (by rw [ringChar.eq (AlgebraicClosure K) 2]; norm_num)
  obtain ⟨i, hQS, hlab'⟩ :=
    CFSG.StandardType.TwE6TwA2K.exists_rationalComponent_label_of_langSetup hK S ι hinj hrange h
      hconj hT hap h1 J hJ hlab
  obtain ⟨-, hr, hc, hnin⟩ :=
    CFSG.StandardType.TablePThreeKG.tableZ_classTriD4 S hn hSq hT hap h1 i hQS hlab'
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have e1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)).map_pow a 3
    have e2 : a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply]
    rw [← e1, e2, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3L facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  have hall := kernelRoots_subset_of_d4 i v hv
  obtain ⟨Fr, hFr, hΦFr⟩ := hΦ
  have hS : ∃ (t : TwistTag) (ht : t.tag = .E6) (Fr' : AlgebraicClosure K →+* AlgebraicClosure K),
      (∀ c, Fr' c = c ^ S.D.q) ∧ ∀ g, S.D.Φ g = diagramAt .E6 (AlgebraicClosure K) t ht *
        Units.map (entrywiseHom Fr') g * (diagramAt .E6 (AlgebraicClosure K) t ht)⁻¹ :=
    ⟨TwistTag.E6, rfl, Fr, fun c => by rw [hFr, hSq], fun g => by rw [hΦFr]; rfl⟩
  obtain ⟨-, u, -, π, -, hu, -, -, hπ, hθ⟩ :=
    d4t2out_theta_cycle S hS (by rw [hSq]; exact h3n) hT hap i v hv hall hρ hnin
  exact ⟨v, u, π, hu, hπ, hθ⟩

end CFSG.StandardType.TwE6TriD4K

end
