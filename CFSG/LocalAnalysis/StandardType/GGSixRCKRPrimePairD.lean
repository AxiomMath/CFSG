module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeLabelledD
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairPinD
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpinPlusModel

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement

theorem rckPairDInner_holds
    : RCKPairDInner := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq hshape hquasi
  classical
  obtain ⟨hkind, h4, hn⟩ := hshape
  have hτ := rckSpin_tag S hT i h4 hn
  have hinner := rckD_twistInner hkind h4 hn
  have hpL := rckA4_cast_ne_zero hp hp2
  obtain ⟨n, β, l, hnr, hβroot, hΨβ, hgram, hframe⟩ :=
    rckD_labelled hτ S hp hpL hTp i h4 hn
  obtain ⟨σ, -, hfin, hcard, f, hf1, hf2, hf3, hz⟩ := rckInnerCoverExplicit S hT i hinner
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hs
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · have := S.hqpow.1
      rw [hq, h0, pow_zero] at this
      exact absurd this not_isPrimePow_one
    · exact h0
  have hg : 0 < h * s := Nat.mul_pos hh hs0
  have hn4 : 4 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinK : Finite ↥(fixSubfield σ) := hfin
  have hKcard : Nat.card ↥(fixSubfield σ) = 2 ^ (h * s) := by rw [hcard, hq, pow_mul]
  obtain ⟨Ψ, hΨrange, hΨker, hpin⟩ :=
    innerRecogPinned_D (K := ↥(fixSubfield σ)) (p := 2) (f := h * s) hτ hg hKcard β hβroot
      hn4 l hgram (fun i j hij => hframe (F := ↥(fixSubfield σ)) i j hij)
  have hadm : StatedLieAdmissible .POmegaPlus n 2 (h * s) :=
    ⟨Nat.prime_two, Nat.one_le_of_lt hg, hn4⟩
  let M : LieUniversal :=
    ⟨spinGroup (Spin.quadPlus n (GaloisField 2 (h * s))),
      Spin.plusDatum n (GaloisField 2 (h * s)) h3⟩
  have hMggU : M = ggU .POmegaPlus n (h * s) := (ggU_pOmegaPlus (f := h * s) h3).symm
  have hMmodel : modelUniv .POmegaPlus n 2 (h * s) Nat.prime_two = M := by
    rw [modelUniv_POmegaPlus (n := n) (p := 2) (f := h * s) h3]
  have hbruhat : HasBruhatDatum M.D := by
    have h := hasBruhatDatum .POmegaPlus n 2 (h * s) Nat.prime_two trivial hadm
    rw [hMmodel] at h
    exact h
  have hcartan : CartanOK M.D := by
    have h := cartanOK .POmegaPlus n 2 (h * s) Nat.prime_two trivial hadm
    rw [hMmodel] at h
    exact h
  have hlongsingle : ∀ k : Fin M.D.rank, IsLongNode .POmegaPlus n k.val →
      IsLongestRoot M.D (Pi.single k 1) := by
    have h := isLongestRoot_single .POmegaPlus n 2 (h * s) Nat.prime_two trivial hadm
    rw [hMmodel] at h
    exact h
  obtain ⟨-, hfinG, hperfG, hsplitG, -⟩ :=
    rckSpin_ggU_facts (n := n) (g := h * s) hn4 hg
  have hfinM : Finite M.K := by
    rw [← hMggU] at hfinG
    exact hfinG
  have hperfM : Group.IsPerfect M.K := by
    rw [← hMggU] at hperfG
    exact hperfG
  have hsplitM : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit M.K := by
    rw [← hMggU] at hsplitG
    exact hsplitG
  have hcommM : commutator M.K = ⊤ := Group.isPerfect_def.1 hperfM
  have hC : componentRootSpan (fixSubfield σ) (rootCharHom a) i = Ψ.range := by
    rw [hΨrange]
    show rootSpan τ ↥(fixSubfield σ) (componentRoots (rootCharHom a) i) =
      rootSpan τ ↥(fixSubfield σ) (rootsOfFam β (Set.range l))
    rw [hΨβ]
  have hmem : ∀ x, Ψ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i := fun x => by
    rw [hC]
    exact ⟨x, rfl⟩
  let Ψ' : M.K →* ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    (show M.K →* ModGL τ ↥(fixSubfield σ) from Ψ).codRestrict _ hmem
  have hΨ'surj : Function.Surjective Ψ' := by
    rintro ⟨c, hc⟩
    have hc' : c ∈ Ψ.range := hC ▸ hc
    obtain ⟨x, rfl⟩ := hc'
    exact ⟨x, rfl⟩
  let φ : M.K →* ModGL τ GGL := f.comp Ψ'
  have hperfC : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
      componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
    apply Subgroup.isPerfect_iff.1
    refine Group.isPerfect_def.2 ?_
    have h1 := congrArg (Subgroup.map Ψ') hcommM
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective Ψ' hΨ'surj] at h1
    rw [commutator_def]
    exact h1
  have hrangeφ : φ.range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΨ'surj, Subgroup.map_top]
  have hR : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf3 hperfC) hf1
  have hkerφ : φ.ker ≤ Subgroup.center M.K := by
    intro x hx
    have h2 : Ψ' x ∈ Subgroup.center _ := hf2 (show Ψ' x ∈ f.ker from hx)
    exact rckA4_preimage_center Ψ' hcommM (fun y hy => hΨker
      (show Ψ y = 1 from congrArg Subtype.val hy)) h2
  unfold RCKFrameCoverPair
  refine ⟨M, φ, ?_, ?_, hrangeφ.trans hR, hkerφ, hfinM,
    Group.isPerfect_def.2 hcommM, hsplitM, ?_⟩
  · rw [← hnr]
    exact hMggU
  · exact Or.inl ⟨.POmegaPlus, n, Or.inr (Or.inr (Or.inl rfl)), hadm, hMggU⟩
  · intro hs1 β' hβ' _
    obtain ⟨z, -, hzstep, hfz, hzZ, -⟩ := hz hs1
    have hφx : ∀ x, φ x = z * baseChangeGL (fixSubfield σ).subtype (Ψ x) * z⁻¹ := fun x =>
      hfz (Ψ' x)
    have hmap : ∀ (Y : Subgroup M.K) (V : Subgroup (ModGL τ ↥(fixSubfield σ))),
        Y.map (show M.K →* ModGL τ ↥(fixSubfield σ) from Ψ) = V →
        Y.map φ = (V.map (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj z).toMonoidHom := by
      intro Y V hYV
      rw [← hYV, Subgroup.map_map, Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun x => hφx x
    obtain ⟨hp0, hm0⟩ := hpin ⟨0, by omega⟩
    have hX := hmap _ _ hp0
    have hX' := hmap _ _ hm0
    have hφmodel : φ.range ≤ S.D.model := by
      rw [hrangeφ, hR]
      exact (Subgroup.commutator_le_self _).trans
        ((inf_le_right : _ ≤ S.Γ).trans (Subgroup.commutator_le_self _))
    have hφC : φ.range ≤ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) := by
      rw [hrangeφ, hR]
      exact rationalComponent_le_torusGroup_sup_rootSpan_kernelRoots S i hs1
    have hmemβ := rckPin_mem_rootsOfFam β hβroot l ⟨0, by omega⟩
    have hmem0 : β (l ⟨0, by omega⟩) ∈ componentRoots (rootCharHom a) i := by
      rw [hΨβ]; exact hmemβ.1
    have hmem0' : -β (l ⟨0, by omega⟩) ∈ componentRoots (rootCharHom a) i := by
      rw [hΨβ]; exact hmemβ.2
    obtain ⟨_, _, hct, -⟩ := hbruhat
    obtain ⟨hirr, hratio⟩ := hcartan
    have hl0 := hlongsingle ⟨0, by show 0 < n; omega⟩ trivial
    have hlβ := isLongestRoot_of_mem_roots_of_forall_single M.D rfl
      (fun k => hlongsingle k trivial) hβ'
    obtain ⟨u, hu1, hu2⟩ := exists_map_conj_rankOne_of_isLongest hct hirr hratio hl0 hlβ
    obtain ⟨z', hz'mem, hst1, hst2, hfx1, hfx2⟩ := rckPair_assemble S σ z hzZ hzstep
      (H := torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
      (X := M.D.rootGroup) φ hφmodel hφC (hβroot (l ⟨0, by omega⟩)) hmem0 hmem0'
      hX hX' u hu1 hu2
    exact ⟨β (l ⟨0, by omega⟩), hmem0, z', hz'mem, hst1, hst2, hfx1, hfx2⟩

end CFSG.StandardType.RCKRP

end
