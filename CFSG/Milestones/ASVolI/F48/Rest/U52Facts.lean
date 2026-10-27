module

public import Certificates.Certificate7767
public import Certificates.Certificate7768
public import Certificates.Certificate7769
public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs
public import CFSG.Milestones.ASVolI.F48.Rest.Perm
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.ClassicalGroups
public import CFSG.GH74.Statements
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Milestones.ASVolI.F48.Rest.Eng
public import CFSG.Milestones.ASVolI.F48.Small.Base
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootRel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
public import CFSG.Sporadic.Schreier.J4SSylow
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr

theorem burnsideF48t_u52_nodupX : burnsideF48t_u52BaseX.Nodup := by decide
theorem burnsideF48t_u52_nodupP1 : burnsideF48t_u52BaseP1.Nodup := by decide
theorem burnsideF48t_u52_nodupP2 : burnsideF48t_u52BaseP2.Nodup := by decide
theorem burnsideF48t_u52_nodupB : burnsideF48t_u52BaseB.Nodup := by decide
theorem burnsideF48t_u52_nodupS0 : burnsideF48t_u52BaseS0.Nodup := by decide
theorem burnsideF48t_u52_nodupK : burnsideF48t_u52BaseK.Nodup := by decide

@[expose] def burnsideF48t_u52X : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 (burnsideF48t_u52Gens ())

@[expose] def burnsideF48t_u52P1' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 burnsideF48t_u52P1Arr

@[expose] def burnsideF48t_u52P2' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 burnsideF48t_u52P2Arr

@[expose] def burnsideF48t_u52B' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 burnsideF48t_u52BArr

@[expose] def burnsideF48t_u52S0' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 (burnsideF48t_u52S0Arr ())

@[expose] def burnsideF48t_u52K' : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 (burnsideF48t_u52KArr ())

section Chains

theorem burnsideF48t_u52_chains : burnsideF48t_u52ChainXOK () = true ∧
    burnsideF48t_u52ChainP1OK () = true ∧ burnsideF48t_u52ChainP2OK () = true ∧
    burnsideF48t_u52ChainBOK () = true ∧ burnsideF48t_u52ChainS0OK () = true ∧
    burnsideF48t_u52ChainKOK () = true :=
  Certificates.certificate7767

theorem burnsideF48t_u52_card_X : Nat.card ↥burnsideF48t_u52X = 13685760 := by
  rw [burnsideF48t_u52X, card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupX
    burnsideF48t_u52_chains.1]
  rfl

theorem burnsideF48t_u52_card_P1' : Nat.card ↥burnsideF48t_u52P1' = 82944 := by
  rw [burnsideF48t_u52P1', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupP1
    burnsideF48t_u52_chains.2.1]
  rfl

theorem burnsideF48t_u52_card_P2' : Nat.card ↥burnsideF48t_u52P2' = 46080 := by
  rw [burnsideF48t_u52P2', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupP2
    burnsideF48t_u52_chains.2.2.1]
  rfl

theorem burnsideF48t_u52_card_B' : Nat.card ↥burnsideF48t_u52B' = 9216 := by
  rw [burnsideF48t_u52B', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupB
    burnsideF48t_u52_chains.2.2.2.1]
  rfl

theorem burnsideF48t_u52_card_S0' : Nat.card ↥burnsideF48t_u52S0' = 1024 := by
  rw [burnsideF48t_u52S0', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupS0
    burnsideF48t_u52_chains.2.2.2.2.1]
  rfl

theorem burnsideF48t_u52_card_K' : Nat.card ↥burnsideF48t_u52K' = 9 := by
  rw [burnsideF48t_u52K', card_arrGen_of_chainCheck (by norm_num) burnsideF48t_u52_nodupK
    burnsideF48t_u52_chains.2.2.2.2.2]
  rfl

theorem burnsideF48t_u52_mem_X_of_sift {t : Array ℕ} {g : Equiv.Perm (Fin 462)}
    (ht : PRep 462 t g)
    (hs : burnsideF48t_sift 462 (burnsideF48t_u52LevX ()) burnsideF48t_u52BaseX t = true) :
    g ∈ burnsideF48t_u52X :=
  burnsideF48t_mem_of_sift (by norm_num) burnsideF48t_u52_nodupX burnsideF48t_u52_chains.1 ht hs

theorem burnsideF48t_u52_mem_S0_of_sift {t : Array ℕ} {g : Equiv.Perm (Fin 462)}
    (ht : PRep 462 t g)
    (hs : burnsideF48t_sift 462 (burnsideF48t_u52LevS0 ()) burnsideF48t_u52BaseS0 t = true) :
    g ∈ burnsideF48t_u52S0' :=
  burnsideF48t_mem_of_sift (by norm_num) burnsideF48t_u52_nodupS0
    burnsideF48t_u52_chains.2.2.2.2.1 ht hs

end Chains

section Letters

theorem burnsideF48t_u52_mem : burnsideF48t_u52InvOK () = true ∧
    burnsideF48t_u52LMemOK () = true ∧ burnsideF48t_u52RelOK () = true ∧
    burnsideF48t_u52CandOK () = true ∧ burnsideF48t_u52FixOK () = true :=
  Certificates.certificate7768

theorem burnsideF48t_u52_inv :
    burnsideF48t_u52LArr.size = 4 ∧ (burnsideF48t_u52LInv ()).size = 4 ∧
    (burnsideF48t_u52Gens ()).size = 6 ∧ (burnsideF48t_u52GensInv ()).size = 6 ∧
    (∀ i < 4, pisInv 462 burnsideF48t_u52LArr[i]! (burnsideF48t_u52LInv ())[i]! = true) ∧
    (∀ i < 6, pisInv 462 (burnsideF48t_u52Gens ())[i]! (burnsideF48t_u52GensInv ())[i]! = true) := by
  have h := burnsideF48t_u52_mem.1
  simp only [burnsideF48t_u52InvOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, fun i hi => allBelowN_spec h5 hi, fun i hi => allBelowN_spec h6 hi⟩

@[expose] noncomputable def burnsideF48t_u52σ (i : ℕ) : Equiv.Perm (Fin 462) :=
  CFSG.ONSchreier.permOfArr 462 burnsideF48t_u52LArr[i]!

theorem burnsideF48t_u52_prep_σ {i : ℕ} (hi : i < 4) :
    PRep 462 burnsideF48t_u52LArr[i]! (burnsideF48t_u52σ i) ∧
      PRep 462 (burnsideF48t_u52LInv ())[i]! (burnsideF48t_u52σ i)⁻¹ :=
  prep_permOfArr (burnsideF48t_u52_inv.2.2.2.2.1 i hi)

@[expose] noncomputable def burnsideF48t_u52γ (i : ℕ) : Equiv.Perm (Fin 462) :=
  CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52Gens ())[i]!

theorem burnsideF48t_u52_prep_γ {i : ℕ} (hi : i < 6) :
    PRep 462 (burnsideF48t_u52Gens ())[i]! (burnsideF48t_u52γ i) ∧
      PRep 462 (burnsideF48t_u52GensInv ())[i]! (burnsideF48t_u52γ i)⁻¹ :=
  prep_permOfArr (burnsideF48t_u52_inv.2.2.2.2.2 i hi)

theorem burnsideF48t_u52_X_eq : burnsideF48t_u52X =
    Subgroup.closure (Set.range fun k : Fin (burnsideF48t_u52Gens ()).size => burnsideF48t_u52γ k) :=
  arrGen_eq fun k hk => (burnsideF48t_u52_prep_γ (burnsideF48t_u52_inv.2.2.1 ▸ hk)).1

theorem burnsideF48t_u52_γ_mem {i : ℕ} (hi : i < 6) : burnsideF48t_u52γ i ∈ burnsideF48t_u52X := by
  rw [burnsideF48t_u52_X_eq]
  exact Subgroup.subset_closure ⟨⟨i, by rw [burnsideF48t_u52_inv.2.2.1]; exact hi⟩, rfl⟩

theorem burnsideF48t_u52_σ_mem {i : ℕ} (hi : i < 4) :
    burnsideF48t_u52σ i ∈ burnsideF48t_u52X := by
  have h := burnsideF48t_u52_mem.2.1
  unfold burnsideF48t_u52LMemOK at h
  exact burnsideF48t_u52_mem_X_of_sift (burnsideF48t_u52_prep_σ hi).1 (allBelowN_spec h hi)

theorem burnsideF48t_u52_recL :
    burnsideF48t_RecL 462 burnsideF48t_u52LArr (burnsideF48t_u52LInv ())
      (fun i : Fin 4 => burnsideF48t_u52σ i) :=
  fun i => burnsideF48t_u52_prep_σ i.2

theorem burnsideF48t_u52_P1Arr : burnsideF48t_u52P1Arr.size = 3 ∧
    burnsideF48t_u52P1Arr[0]! = burnsideF48t_u52LArr[0]! ∧
    burnsideF48t_u52P1Arr[1]! = burnsideF48t_u52LArr[1]! ∧
    burnsideF48t_u52P1Arr[2]! = burnsideF48t_u52LArr[2]! :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem burnsideF48t_u52_P2Arr : burnsideF48t_u52P2Arr.size = 3 ∧
    burnsideF48t_u52P2Arr[0]! = burnsideF48t_u52LArr[0]! ∧
    burnsideF48t_u52P2Arr[1]! = burnsideF48t_u52LArr[1]! ∧
    burnsideF48t_u52P2Arr[2]! = burnsideF48t_u52LArr[3]! :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem burnsideF48t_u52_BArr : burnsideF48t_u52BArr.size = 2 ∧
    burnsideF48t_u52BArr[0]! = burnsideF48t_u52LArr[0]! ∧
    burnsideF48t_u52BArr[1]! = burnsideF48t_u52LArr[1]! :=
  ⟨rfl, rfl, rfl⟩

@[expose] def burnsideF48t_u52P1Idx (k : ℕ) : ℕ := k

@[expose] def burnsideF48t_u52P2Idx (k : ℕ) : ℕ := k + k / 2

theorem burnsideF48t_u52_P1'_eq_closure : burnsideF48t_u52P1' =
    Subgroup.closure (Set.range fun k : Fin burnsideF48t_u52P1Arr.size =>
      burnsideF48t_u52σ (burnsideF48t_u52P1Idx k)) := by
  obtain ⟨hs, h0, h1, h2⟩ := burnsideF48t_u52_P1Arr
  rw [burnsideF48t_u52P1']
  refine arrGen_eq (n := 462) (O := burnsideF48t_u52P1Arr)
    (σ := fun k => burnsideF48t_u52σ (burnsideF48t_u52P1Idx k)) fun k hk => ?_
  rw [hs] at hk
  interval_cases k
  · rw [h0]; exact (burnsideF48t_u52_prep_σ (by decide)).1
  · rw [h1]; exact (burnsideF48t_u52_prep_σ (by decide)).1
  · rw [h2]; exact (burnsideF48t_u52_prep_σ (by decide)).1

theorem burnsideF48t_u52_P2'_eq_closure : burnsideF48t_u52P2' =
    Subgroup.closure (Set.range fun k : Fin burnsideF48t_u52P2Arr.size =>
      burnsideF48t_u52σ (burnsideF48t_u52P2Idx k)) := by
  obtain ⟨hs, h0, h1, h2⟩ := burnsideF48t_u52_P2Arr
  rw [burnsideF48t_u52P2']
  refine arrGen_eq (n := 462) (O := burnsideF48t_u52P2Arr)
    (σ := fun k => burnsideF48t_u52σ (burnsideF48t_u52P2Idx k)) fun k hk => ?_
  rw [hs] at hk
  interval_cases k
  · rw [h0]; exact (burnsideF48t_u52_prep_σ (by decide)).1
  · rw [h1]; exact (burnsideF48t_u52_prep_σ (by decide)).1
  · rw [h2]; exact (burnsideF48t_u52_prep_σ (by decide)).1

theorem burnsideF48t_u52_B'_eq_closure : burnsideF48t_u52B' =
    Subgroup.closure (Set.range fun k : Fin burnsideF48t_u52BArr.size =>
      burnsideF48t_u52σ (burnsideF48t_u52P1Idx k)) := by
  obtain ⟨hs, h0, h1⟩ := burnsideF48t_u52_BArr
  rw [burnsideF48t_u52B']
  refine arrGen_eq (n := 462) (O := burnsideF48t_u52BArr)
    (σ := fun k => burnsideF48t_u52σ (burnsideF48t_u52P1Idx k)) fun k hk => ?_
  rw [hs] at hk
  interval_cases k
  · rw [h0]; exact (burnsideF48t_u52_prep_σ (by decide)).1
  · rw [h1]; exact (burnsideF48t_u52_prep_σ (by decide)).1

end Letters

section Stab

theorem burnsideF48t_u52_orbX :
    (∀ p : Fin 462, p ∈ MulAction.orbit burnsideF48t_u52X (0 : Fin 462) ↔ (p : ℕ) < 165) ∧
    ∀ p : Fin 462, p ∈ MulAction.orbit burnsideF48t_u52X (165 : Fin 462) ↔ 165 ≤ (p : ℕ) :=
  ⟨Certificates.certificate7769.1, Certificates.certificate7769.2.1⟩

theorem burnsideF48t_u52_s0Norm : burnsideF48t_u52S0NormOK () = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := Certificates.certificate7769
  exact h

theorem burnsideF48t_u52_fix :
    (burnsideF48t_u52LArr[0]!)[0]! = 0 ∧ (burnsideF48t_u52LArr[0]!)[165]! = 165 ∧
    (burnsideF48t_u52LArr[1]!)[0]! = 0 ∧ (burnsideF48t_u52LArr[1]!)[165]! = 165 ∧
    (burnsideF48t_u52LArr[2]!)[0]! = 0 ∧ (burnsideF48t_u52LArr[3]!)[165]! = 165 ∧
    (burnsideF48t_u52LArr[3]!)[0]! ≠ 0 ∧ (burnsideF48t_u52LArr[2]!)[165]! ≠ 165 ∧
    (∀ s ∈ burnsideF48t_u52S0Arr (), s[0]! = 0 ∧ s[165]! = 165) ∧
    (∀ p < 462, p ≠ 0 → p ≠ 165 → ∃ s ∈ burnsideF48t_u52S0Arr (), s[p]! ≠ p) := by
  have h := burnsideF48t_u52_mem.2.2.2.2
  simp only [burnsideF48t_u52FixOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_⟩
  · intro s hs
    have := Array.all_eq_true_iff_forall_mem.1 h9 s hs
    simpa using this
  · intro p hp h0 h165
    have := allBelowN_spec h10 hp
    simp only [Bool.or_eq_true, beq_iff_eq, Array.any_eq_true', bne_iff_ne, ne_eq] at this
    rcases this with (h | h) | ⟨s, hs, hsp⟩
    · exact absurd h h0
    · exact absurd h h165
    · exact ⟨s, hs, hsp⟩

end Stab

end CFSG.ASVolI
