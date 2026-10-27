module

public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aPairOuterTwoSU
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aPairOuterTwoD

public import CFSG.LocalAnalysis.StandardType.GGFamRatCompE6Outer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGJ4dKernel24
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxCore
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.Blueprint.ChevalleyRoots


public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.AlgebraicGroups
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.StandardType.GGFinModel



private theorem u1aO2_e6Layer_mem {τ : Tag} [M27Ok τ] [E6Sub τ]
    (hτne : ∀ t : TwistTag, t.tag ≠ τ)
    (Δ : LangDatum τ GGL) (hq : Δ.q = 2) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap Δ ρ) (hfin : Finite Δ.model) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a₁ a₂ : Fin τ.rank → GGLˣ} (ha₁ : rootDiagUnit τ a₁ ∈ Δ.torus)
    (ha₂ : rootDiagUnit τ a₂ ∈ Δ.torus) (hap₁ : ∀ j, a₁ j ^ p = 1)
    (hap₂ : ∀ j, a₂ j ^ p = 1) (iJ : KernelComponent (LieCore.jointChar a₁ a₂))
    (hb : componentOrbitLength ρ (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 1)
    (hrk : compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 6)
    (hnc : (componentRoots (LieCore.jointChar a₁ a₂) iJ).ncard = 72)
    {K : KacData τ} (hK : K.Facts)
    {E6C : Finset (Option (Fin τ.rank))}
    (hpin : ∀ C : Finset (Option (Fin τ.rank)), C.card = 6 → kacCount τ K.θ C = 72 → C = E6C)
    (hJ : ∀ k : Fin τ.rank, some k ∈ E6C ↔ k.val ≤ 5) (hnone : none ∉ E6C)
    {g : ModGL τ GGL}
    (hg : g ∈ rootSpan τ GGL (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ Δ.model) :
    g ∈ LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by
  classical
  obtain ⟨S, hSD, hSρ⟩ := LieCore.exists_langSetup_of_datum Δ ρ hρ hfin (f := 1)
    (by norm_num) (by rw [hq, pow_one])
  subst hSD
  subst hSρ
  set Ψ := componentRoots (LieCore.jointChar a₁ a₂) iJ with hΨdef
  have himg : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ :=
    CFSG.StandardType.LangRat.j4d_image_eq_of_componentOrbitLength_eq_one hb
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := by
    intro γ hγ
    have hmem : S.ρ γ ∈ S.ρ '' Ψ := ⟨γ, hγ, rfl⟩
    rwa [himg] at hmem
  let a : Fin 2 → Fin τ.rank → GGLˣ := ![a₁, a₂]
  have hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus := by
    intro u
    fin_cases u
    · simpa [a] using ha₁
    · simpa [a] using ha₂
  have hap : ∀ u j, a u j ^ p = 1 := by
    intro u j
    fin_cases u
    · simpa [a] using hap₁ j
    · simpa [a] using hap₂ j
  obtain ⟨i, hi⟩ := LieCore.exists_famComponent_of_jointChar a₁ a₂ iJ
  obtain ⟨N, b, j, hN, hN2, hbN, hbj⟩ :=
    TableCRes.exists_isolating_element (Or.inr (M27Ok.isE7E8)) a hp hp2 hap i
  have hbΨ : componentRoots (rootCharHom b) j = Ψ := by
    rw [hbj, ← hi]
  have hNL : (N : GGL) ≠ 0 := by
    intro h
    have hdvd : 2 ∣ N := (CharP.cast_eq_zero_iff GGL 2 N).1 h
    exact hN2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hN).1 hdvd).symm
  have hrb : compRank (componentRoots (rootCharHom b) j) = 6 := by
    rw [hbΨ]; exact hrk
  have hcb : (componentRoots (rootCharHom b) j).ncard = 72 := by
    rw [hbΨ]; exact hnc
  obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime (K := K) (E6C := E6C)
    hN hNL hK hpin hJ hnone hbN j hrb hcb
  have hvΨ : Ψ = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := by
    rw [← hbΨ, hv]
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hw : ∀ γ ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ),
      w • γ ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := by
    intro γ hγ
    rw [← hvΨ] at hγ ⊢
    rw [← S.rho_eq_smul hτne hn hγ.1.1]
    exact hρΨ γ hγ
  have hqs : CFSG.IsQuasisimple ↥(rootSpan τ GGL Ψ ⊓ S.D.model) := by
    rw [hvΨ]
    exact (rootSpan_inf_model_quasisimple hτne S hn v hw).2
  have heq := TableCRes.rationalComponentM_eq_of_layer S iJ hρΨ hqs
  rw [LieCore.ratComp_eq_rationalComponentM]
  change g ∈ TableCRes.rationalComponentM S.ρ S.Γ (LieCore.jointChar a₁ a₂) iJ
  rw [heq]
  exact hg

theorem outerTwo_mem_ratComp {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (Δ : LangDatum τ GGL) (hq : Δ.q = 2) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap Δ ρ) (hfin : Finite Δ.model) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a₁ a₂ : Fin τ.rank → GGLˣ} (ha₁ : rootDiagUnit τ a₁ ∈ Δ.torus)
    (ha₂ : rootDiagUnit τ a₂ ∈ Δ.torus) (hap₁ : ∀ j, a₁ j ^ p = 1)
    (hap₂ : ∀ j, a₂ j ^ p = 1) (hne : rootDiagUnit τ a₁ ≠ 1 ∨ rootDiagUnit τ a₂ ≠ 1)
    (iJ : KernelComponent (LieCore.jointChar a₁ a₂))
    (hb : componentOrbitLength ρ (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 1)
    (houter : ¬ twistInner (componentRoots (LieCore.jointChar a₁ a₂) iJ) ρ)
    (hqs : CFSG.Assembly.IsQuasisimple
      ↥(LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ)))
    {g : ModGL τ GGL}
    (hg : g ∈ rootSpan τ GGL (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ Δ.model)
    (hg2 : g * g = 1) :
    g ∈ LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by
  classical
  set Ψ := componentRoots (LieCore.jointChar a₁ a₂) iJ with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots iJ
  have himg : (ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ :=
    CFSG.StandardType.LangRat.j4d_image_eq_of_componentOrbitLength_eq_one hb
  have hbij : Set.BijOn ρ Ψ Ψ := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [← himg]
      exact Set.mem_image_of_mem ρ hx
    · intro x hx y hy hxy
      exact ρ.injective hxy
    · intro y hy
      rw [← himg] at hy
      exact hy
  have hiform : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, CFSG.LieType.Steinberg.Adjoint.iform (ρ γ) (ρ δ) =
      CFSG.LieType.Steinberg.Adjoint.iform γ δ := by
    intro γ _ δ _
    exact hρ.iform_eq γ δ
  have hneg : ∀ γ ∈ Ψ, ρ (-γ) = -ρ γ := by
    intro γ _
    exact hρ.neg_eq γ
  have hsym : HasDiagramSymmetryType Ψ := by
    by_contra hnot
    exact houter (CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds
      τ Ψ hΨ hnot ρ hbij hiform hneg)
  rcases hsym with hA | hD | hE6
  · exact outerTwo_mem_ratComp_suN hτ Δ hq hρ hfin hp hp2 ha₁ ha₂ hap₁ hap₂ iJ hb houter hA hqs
      hg hg2
  · exact outerTwo_mem_ratComp_typeD hτ Δ hq hρ hfin hp hp2 ha₁ ha₂ hap₁ hap₂ iJ hb houter hD
      hg hg2
  · obtain ⟨hrk, hnc⟩ := hE6
    rcases hτ with rfl | rfl | rfl
    ·
      exfalso
      have hsub : Ψ ⊆ (rootFinset Tag.E6 : Set (Fin Tag.E6.rank → ℤ)) := by
        intro γ hγ
        exact Finset.mem_coe.mpr (mem_rootFinset.mpr hγ.1.1)
      have hall : Ψ = (rootFinset Tag.E6 : Set (Fin Tag.E6.rank → ℤ)) := by
        apply Set.eq_of_subset_of_ncard_le hsub
        rw [Set.ncard_coe_finset,
          CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux.card_rootFinset_E6,
          hnc]
      have hsingle : ∀ j : Fin Tag.E6.rank,
          (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ Ψ := by
        intro j
        rw [hall]
        exact Finset.mem_coe.mpr (mem_rootFinset.mpr (isRoot_single Tag.E6 j))
      have hjoint : ∀ j : Fin Tag.E6.rank,
          LieCore.jointChar a₁ a₂ (Pi.single j 1) = 1 := by
        intro j
        exact (hsingle j).1.2
      have ha1 : a₁ = 1 := by
        funext j
        have h := congrArg Prod.fst (hjoint j)
        change rootChar a₁ (Pi.single j 1) = 1 at h
        rw [CFSG.ClassicalInvolution.Balance.rootChar_single_eq] at h
        exact h
      have ha2 : a₂ = 1 := by
        funext j
        have h := congrArg Prod.snd (hjoint j)
        change rootChar a₂ (Pi.single j 1) = 1 at h
        rw [CFSG.ClassicalInvolution.Balance.rootChar_single_eq] at h
        exact h
      have hd1 : rootDiagUnit Tag.E6 a₁ = 1 := by
        rw [ha1, rootDiagUnit_one]
      have hd2 : rootDiagUnit Tag.E6 a₂ = 1 := by
        rw [ha2, rootDiagUnit_one]
      rcases hne with h | h
      · exact h hd1
      · exact h hd2
    ·
      exact u1aO2_e6Layer_mem twistTag_tag_ne_E7 Δ hq hρ hfin hp hp2 ha₁ ha₂ hap₁ hap₂ iJ
        hb hrk hnc facts_E7 kacCount_E7_six (by decide) (by decide) hg
    ·
      exact u1aO2_e6Layer_mem twistTag_tag_ne_E8 Δ hq hρ hfin hp hp2 ha₁ ha₂ hap₁ hap₂ iJ
        hb hrk hnc facts_E8 kacCount_E8_six (by decide) (by decide) hg

end CFSG.StandardType.LieKnownR2.ExcPos
