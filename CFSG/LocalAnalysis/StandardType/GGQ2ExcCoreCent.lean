module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreCentRaw
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientRefl
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
open scoped commutatorElement


section Helpers


private theorem cent_rootSL2_mem_rootSpan {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {S : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h1 : β ∈ S) (h2 : -β ∈ S) (A : SL2 L) :
    rootSL2 τ L β A ∈ rootSpan τ L S := by
  have h : rootSL2 τ L β A ∈ (rootSL2 τ L β).range := ⟨A, rfl⟩
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ] at h
  exact sup_le (rootSubgroup_le_rootSpan h1) (rootSubgroup_le_rootSpan h2) h

end Helpers

section HelpersConj


private theorem cent_conj_rootWeylSL2 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup τ L p} {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} (d : ExcCoordDatum S T₀ m)
    (k : ExcRaw.Root m) (s : ↥T₀) :
    ∃ s' : ↥T₀,
      (s' : ModGL τ L) =
        rootSL2 τ L (d.γ k) WSL * (s : ModGL τ L) * (rootSL2 τ L (d.γ k) WSL)⁻¹ ∧
      d.coord (Additive.ofMul s') = ExcRaw.reflection m k (d.coord (Additive.ofMul s)) := by
  obtain ⟨b, hb⟩ := d.exists_rootDiagUnit s
  have hbT : rootDiagUnit τ b ∈ T₀ := hb ▸ s.2
  obtain ⟨hmem, hcoord⟩ := d.weylTuple_reflection_mem (b := b) k hbT
  refine ⟨⟨rootDiagUnit τ (weylTuple (rootReflection (d.γ k)) b), hmem⟩, ?_, ?_⟩
  · rw [hb, rootWeylSL2_conj_rootDiagUnit S (d.isRoot k) b]
  · rw [hcoord, show (⟨rootDiagUnit τ b, hbT⟩ : ↥T₀) = s from Subtype.ext hb.symm]

end HelpersConj

private theorem cent_exists_adj {m : Fin 6} {U : Submodule (ZMod 3) (ExcRaw.V m)}
    {c : Finset (ExcRaw.Root m)} (hU : ExcRaw.IsComp m (ExcRaw.Vanish m U) c)
    (hlam : LargeEvenInLambda2 (ExcRaw.label m c))
    (h1 : ∀ i : ExcRaw.Root m, ¬ LargeEvenInLambda2 (ExcRaw.label m {i})) :
    ∀ i ∈ c, ∃ j ∈ c, j ≠ i ∧ ExcRaw.Adj m i j := by
  intro i hi
  obtain ⟨-, -, -, hmin⟩ := hU
  by_contra h
  have hsingle : ({i} : Finset (ExcRaw.Root m)) = c := by
    refine hmin {i} ?_ ⟨i, Finset.mem_singleton_self i⟩ ?_
    · intro x hx
      rw [Finset.mem_singleton] at hx
      exact hx ▸ hi
    · intro x hx y hy hxy
      rw [Finset.mem_singleton] at hx
      subst hx
      rw [Finset.mem_singleton]
      by_contra hyi
      exact h ⟨y, hy, hyi, hxy⟩
  rw [← hsingle] at hlam
  exact h1 i hlam

theorem excCoreCent_of_adjIndep
    {m : Fin 6} {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hA : ExcRaw.AdjIndep m)
    (h1 : ∀ i : ExcRaw.Root m, ¬ LargeEvenInLambda2 (ExcRaw.label m {i})) :
    ExcCoreCent m τ := by
  intro L _ _ p S hS T₀ d c hc
  ext u
  rw [mem_ggLinImage]
  have hq : S.D.q = 2 ^ 1 := by rw [hS.1, pow_one]
  have hcent : u ∈ ExcRaw.cent m c ↔ ∀ i ∈ c, ExcRaw.root m i u = 0 := by
    simp only [ExcRaw.cent, Submodule.mem_iInf, LinearMap.mem_ker]
  have hchar : ((2 : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rwa [hS.1] at h
  constructor
  ·
    intro hu
    rw [hcent]
    intro i hi
    obtain ⟨j, hj, hji, hadj⟩ := cent_exists_adj hc.1.choose_spec hc.2 h1 i hi
    have : CharP L 2 :=
      CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by simpa using hchar)
    have hwiΓ : rootSL2 τ L (d.γ i) WSL ∈ S.Γ :=
      rootWeylSL2_mem_Γ_of_rho_neg S hτ hq hS.2.1 (d.isRoot i) (hS.2.2 _ (d.isRoot i))
    have hwjΓ : rootSL2 τ L (d.γ j) WSL ∈ S.Γ :=
      rootWeylSL2_mem_Γ_of_rho_neg S hτ hq hS.2.1 (d.isRoot j) (hS.2.2 _ (d.isRoot j))
    have hwi2 : rootSL2 τ L (d.γ i) WSL * rootSL2 τ L (d.γ i) WSL = 1 :=
      rootWeylSL2_mul_self_of_charTwo (d.γ i)
    have hwj2 : rootSL2 τ L (d.γ j) WSL * rootSL2 τ L (d.γ j) WSL = 1 :=
      rootWeylSL2_mul_self_of_charTwo (d.γ j)
    have hwi_inv : (rootSL2 τ L (d.γ i) WSL)⁻¹ = rootSL2 τ L (d.γ i) WSL :=
      inv_eq_of_mul_eq_one_right hwi2
    have hwj_inv : (rootSL2 τ L (d.γ j) WSL)⁻¹ = rootSL2 τ L (d.γ j) WSL :=
      inv_eq_of_mul_eq_one_right hwj2
    have hwiMem : d.γ i ∈ codeRoots d.γ c := ⟨i, hi, Or.inl rfl⟩
    have hwiNeg : -(d.γ i) ∈ codeRoots d.γ c := ⟨i, hi, Or.inr rfl⟩
    have hwjMem : d.γ j ∈ codeRoots d.γ c := ⟨j, hj, Or.inl rfl⟩
    have hwjNeg : -(d.γ j) ∈ codeRoots d.γ c := ⟨j, hj, Or.inr rfl⟩
    have hwiSpan : rootSL2 τ L (d.γ i) WSL ∈ rootSpan τ L (codeRoots d.γ c) :=
      cent_rootSL2_mem_rootSpan (d.isRoot i) hwiMem hwiNeg WSL
    have hwjSpan : rootSL2 τ L (d.γ j) WSL ∈ rootSpan τ L (codeRoots d.γ c) :=
      cent_rootSL2_mem_rootSpan (d.isRoot j) hwjMem hwjNeg WSL
    have hwiH : rootSL2 τ L (d.γ i) WSL ∈ rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ :=
      ⟨hwiSpan, hwiΓ⟩
    have hwjH : rootSL2 τ L (d.γ j) WSL ∈ rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ :=
      ⟨hwjSpan, hwjΓ⟩
    have hn : ⁅rootSL2 τ L (d.γ i) WSL, rootSL2 τ L (d.γ j) WSL⁆ ∈ codeComponent S d.γ c :=
      Subgroup.commutator_mem_commutator hwiH hwjH
    set t : ↥T₀ := Additive.toMul (d.coord.symm u) with ht_def
    have htu : d.coord (Additive.ofMul t) = u := by
      rw [ht_def, ofMul_toMul, AddEquiv.apply_symm_apply]
    have hncomm : ⁅rootSL2 τ L (d.γ i) WSL, rootSL2 τ L (d.γ j) WSL⁆ * (t : ModGL τ L) =
        (t : ModGL τ L) * ⁅rootSL2 τ L (d.γ i) WSL, rootSL2 τ L (d.γ j) WSL⁆ :=
      (Subgroup.mem_centralizer_iff.mp hu) _ hn
    have hnt : ⁅rootSL2 τ L (d.γ i) WSL, rootSL2 τ L (d.γ j) WSL⁆ * (t : ModGL τ L) *
        ⁅rootSL2 τ L (d.γ i) WSL, rootSL2 τ L (d.γ j) WSL⁆⁻¹ = (t : ModGL τ L) := by
      rw [hncomm, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨s1, hs1val, hs1coord⟩ := cent_conj_rootWeylSL2 d j t
    obtain ⟨s2, hs2val, hs2coord⟩ := cent_conj_rootWeylSL2 d i s1
    obtain ⟨s3, hs3val, hs3coord⟩ := cent_conj_rootWeylSL2 d j s2
    obtain ⟨s4, hs4val, hs4coord⟩ := cent_conj_rootWeylSL2 d i s3
    have hs4eq : (s4 : ModGL τ L) =
        ⁅rootSL2 τ L (d.γ i) WSL, rootSL2 τ L (d.γ j) WSL⁆ * (t : ModGL τ L) *
          ⁅rootSL2 τ L (d.γ i) WSL, rootSL2 τ L (d.γ j) WSL⁆⁻¹ := by
      rw [hs4val, hs3val, hs2val, hs1val, commutatorElement_def]
      simp only [mul_inv_rev, hwi_inv, hwj_inv]
      group
    have hs4t : s4 = t := Subtype.ext (by rw [hs4eq, hnt])
    have hfix : ExcRaw.reflection m i (ExcRaw.reflection m j (ExcRaw.reflection m i
        (ExcRaw.reflection m j u))) = u := by
      rw [hs3coord, hs2coord, hs1coord] at hs4coord
      rw [hs4t, htu] at hs4coord
      exact hs4coord.symm
    exact ExcRaw.root_eq_zero_of_reflection_fix (m := m) hA (Ne.symm hji) hadj hfix
  ·
    intro hu
    rw [hcent] at hu
    set t : ↥T₀ := Additive.toMul (d.coord.symm u) with ht_def
    have htu : d.coord (Additive.ofMul t) = u := by
      rw [ht_def, ofMul_toMul, AddEquiv.apply_symm_apply]
    obtain ⟨b, hb⟩ := d.exists_rootDiagUnit t
    have hχ : ∀ i ∈ c, rootChar b (d.γ i) = 1 := by
      intro i hi
      rw [d.rootChar_eq t b hb i, htu, hu i hi]
      simp
    have hspan : rootSpan τ L (codeRoots d.γ c) ≤
        Subgroup.centralizer ({(t : ModGL τ L)} : Set (ModGL τ L)) := by
      refine iSup₂_le ?_
      intro α hα
      obtain ⟨k, hk, hα | hα⟩ := hα
      · subst hα
        rw [rootSubgroup, Subgroup.closure_le]
        rintro g ⟨x, rfl⟩
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have hconj : (t : ModGL τ L) * pinnedX τ L (d.γ k) x * (t : ModGL τ L)⁻¹ =
            pinnedX τ L (d.γ k) ((rootChar b (d.γ k) : L) * x) := by
          rw [hb]
          exact rootDiagUnit_conj_pinnedX (K := L) b (d.isRoot k) x
        have hfin : (t : ModGL τ L) * pinnedX τ L (d.γ k) x * (t : ModGL τ L)⁻¹ =
            pinnedX τ L (d.γ k) x := by
          rw [hconj, hχ k hk]
          simp
        have hcomm : (t : ModGL τ L) * pinnedX τ L (d.γ k) x =
            pinnedX τ L (d.γ k) x * (t : ModGL τ L) := by
          simpa [mul_assoc] using congrArg (· * (t : ModGL τ L)) hfin
        exact hcomm.symm
      · subst hα
        have hχneg : rootChar b (-(d.γ k)) = 1 := by
          have hneg := rootChar_sub b (0 : Fin τ.rank → ℤ) (d.γ k)
          rw [zero_sub, rootChar_zero, one_mul] at hneg
          rw [hneg, hχ k hk, inv_one]
        rw [rootSubgroup, Subgroup.closure_le]
        rintro g ⟨x, rfl⟩
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have hconj : (t : ModGL τ L) * pinnedX τ L (-(d.γ k)) x * (t : ModGL τ L)⁻¹ =
            pinnedX τ L (-(d.γ k)) ((rootChar b (-(d.γ k)) : L) * x) := by
          rw [hb]
          exact rootDiagUnit_conj_pinnedX (K := L) b (IsRoot.neg (d.isRoot k)) x
        have hfin : (t : ModGL τ L) * pinnedX τ L (-(d.γ k)) x * (t : ModGL τ L)⁻¹ =
            pinnedX τ L (-(d.γ k)) x := by
          rw [hconj, hχneg]
          simp
        have hcomm : (t : ModGL τ L) * pinnedX τ L (-(d.γ k)) x =
            pinnedX τ L (-(d.γ k)) x * (t : ModGL τ L) := by
          simpa [mul_assoc] using congrArg (· * (t : ModGL τ L)) hfin
        exact hcomm.symm
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hyH : y ∈ rootSpan τ L (codeRoots d.γ c) := by
      have hyR : y ∈ ⁅rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ,
          rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ⁆ := hy
      have hy1 : y ∈ rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ :=
        Subgroup.commutator_le_self (rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ) hyR
      exact (Subgroup.mem_inf.mp hy1).1
    exact Subgroup.mem_centralizer_singleton_iff.mp (hspan hyH)

theorem excCoreCent_E6_two :
    ExcCoreCent 2 .E6 :=
  excCoreCent_of_adjIndep (m := 2) (τ := .E6) (Or.inr (Or.inl rfl)) ExcRaw.adjIndep_two
    (ExcRaw.not_largeEvenInLambda2_label_singleton (by decide))

theorem excCoreCent_E6_three :
    ExcCoreCent 3 .E6 :=
  excCoreCent_of_adjIndep (m := 3) (τ := .E6) (Or.inr (Or.inl rfl)) ExcRaw.adjIndep_three
    (ExcRaw.not_largeEvenInLambda2_label_singleton (by decide))

theorem excCoreCent_F4 :
    ExcCoreCent 0 .F4 :=
  excCoreCent_of_adjIndep (m := 0) (τ := .F4) (Or.inl rfl) ExcRaw.adjIndep_zero
    (ExcRaw.not_largeEvenInLambda2_label_singleton (by decide))

theorem excCoreCent_E7 :
    ExcCoreCent 4 .E7 :=
  excCoreCent_of_adjIndep (m := 4) (τ := .E7) (Or.inr (Or.inr (Or.inl rfl))) ExcRaw.adjIndep_four
    (ExcRaw.not_largeEvenInLambda2_label_singleton (by decide))

theorem excCoreCent_E8 :
    ExcCoreCent 5 .E8 :=
  excCoreCent_of_adjIndep (m := 5) (τ := .E8) (Or.inr (Or.inr (Or.inr rfl))) ExcRaw.adjIndep_five
    (ExcRaw.not_largeEvenInLambda2_label_singleton (by decide))

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
